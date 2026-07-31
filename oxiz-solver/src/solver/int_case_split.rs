//! Non-convex LIA integer case-splitting refinement.
//!
//! ## The problem
//!
//! A QF_UFLIA formula is *non-convex* in the arithmetic sense when an integer
//! term `t` is pinned to a small finite domain by arithmetic bounds (e.g.
//! `(>= t 0)` ∧ `(<= t 1)` ⟹ `t ∈ {0, 1}`) and that same `t` is used directly
//! as an argument to an uninterpreted function.  Whether the formula is
//! satisfiable can then depend on *which* concrete value `t` takes, because
//! each value triggers a different congruence in EUF (`f(0)` vs `f(1)`).
//!
//! Nelson–Oppen equality sharing between the arithmetic and EUF solvers can
//! only propagate *entailed* equalities.  `t = 0` is **not** entailed while
//! `t = 1` is still possible, so the disjunction `t ∈ {0,1}` is never resolved
//! and the CDCL core has no Boolean atom to branch on `t`'s value.  The
//! result is a spurious `sat` on an `unsat` instance — a classic false-SAT of
//! non-convex theory combination.
//!
//! Canonical minimal repro:
//! ```text
//!   (declare-fun d () Int) (declare-fun f (Int) Int)
//!   (assert (>= d 0)) (assert (<= d 1))
//!   (assert (= (f 0) 0)) (assert (= (f 1) 1))
//!   (assert (= (f d) (+ d 1)))        ; unsat: d=0 ⇒ 0=1, d=1 ⇒ 1=2
//! ```
//!
//! ## The fix
//!
//! After the CDCL(T) core reports a candidate `sat`, we look for
//! *user-declared* integer variables that (a) appear directly as uninterpreted
//! function arguments and (b) are tightly bounded to a small finite domain by
//! the formula, then assert an explicit disjunction
//! `(or (= t lo) … (= t hi))` as a lemma.  Each disjunct is a fresh equality
//! atom that is shared by both theories (it is a `Constraint::Eq` over an Int
//! term with a *proper SAT-level reason*), so once CDCL picks a value the EUF
//! congruence `f(t) = f(k)` fires and the arithmetic solver detects the
//! conflict through the normal EUF→Arith propagation — exactly reproducing
//! what a hand-written `(assert (or (= d 0) (= d 1)))` achieves.
//!
//! ## Soundness
//!
//! The disjunction is a *theorem* of the formula (it only restates that `t`
//! must lie in `[lo, hi]`), so adding it can never change satisfiability.  Two
//! properties guarantee this:
//!
//!   1. **Bounds come only from decision-level-0 atoms.**  An atom forced at
//!      level 0 holds in *every* model (it is unit-propagated from the formula
//!      alone), so any bound derived from such atoms is a logical consequence
//!      of the formula.  Atoms that merely happen to be true in the current
//!      candidate model are *not* used.
//!   2. **A model-consistency guard.**  As a defensive backstop, we additionally
//!      require that the candidate model's actual value for `t` lies within
//!      `[lo, hi]`; if the derived bounds ever disagreed with the model the
//!      theory solvers just accepted, we skip the term.
//!
//! ## Scope limitation (compound UF arguments)
//!
//! Only *user-declared* integer variables are split.  Compound UF arguments
//! such as `f(fmt1 - 2)` are abstracted to fresh internal proxies during
//! preprocessing; case-splitting those proxies exposes a separate, pre-existing
//! soundness gap in the theory combination (conflict explanations for
//! theory-derived equalities miss their decision-level reasons), so they are
//! deliberately excluded here via [`Solver::is_internal_var`].  Closing that
//! gap is left to a dedicated theory-combination fix.
//!
//! Reference: this is the standard "integer case splitting" used by Z3 / cvc5
//! for non-convex LIA theory combination (see Barrett et al.,
//! "Decision Procedures", ch. 10).

use num_rational::Rational64;
use num_traits::ToPrimitive;
use oxiz_core::ast::{collect_subterms, TermId, TermKind, TermManager};
use oxiz_sat::Lit;
use rustc_hash::{FxHashMap, FxHashSet};
use smallvec::SmallVec;

use super::types::{ArithConstraintType, Constraint};
use super::Solver;

/// Maximum integer range `hi - lo` for which we emit an explicit case split.
const MAX_INT_CASE_RANGE: i64 = 8;

/// Hard cap on the number of reset-and-re-solve refinement rounds.  Each round
/// is expensive (the whole problem is re-solved from scratch); the
/// `case_split_terms` deduplication guarantees saturation well within this.
const MAX_CASE_SPLIT_ROUNDS: u32 = 16;

/// Maximum number of *new* terms split in a single refinement round.
const PER_ROUND_CAP: usize = 8;

/// Whether a constraint's effect on a variable is to pin a lower bound, an
/// upper bound, or both (equality).  Strict `<` / `>` are normalised to `<=` /
/// `>=` with an off-by-one constant (valid over the integers) at collection
/// time, so the propagation core only handles these three cases.
#[derive(Clone, Copy)]
enum Dir {
    Le,
    Ge,
    Eq,
}

/// One normalized arithmetic fact for the interval fixpoint:
/// `sum(coef_i * x_i) <dir-op> constant`.
struct Fact {
    terms: SmallVec<[(TermId, Rational64); 4]>,
    constant: Rational64,
    dir: Dir,
}

impl Solver {
    /// Lazy integer case-split refinement entry point.
    ///
    /// Returns `true` iff at least one new case-split lemma was asserted, in
    /// which case the caller must reset the theory state and re-solve (mirrors
    /// the array-axiom refinement loop in [`Solver::check`]).  Returns `false`
    /// when there is nothing more to split — the candidate `sat` then stands.
    pub(super) fn refine_int_case_split(&mut self, manager: &mut TermManager) -> bool {
        // The whole technique is integer-specific: real (LRA) arithmetic is
        // convex, and the strict-inequality normalisation assumes integers.
        if !self.arith.is_integer() {
            return false;
        }
        if self.case_split_rounds >= MAX_CASE_SPLIT_ROUNDS {
            return false;
        }

        let uf_args = self.collect_int_uf_args(manager);
        let bounds = self.compute_int_bounds();

        let mut candidates: Vec<(TermId, i64, i64)> = Vec::new();
        for t in &uf_args {
            if self.case_split_terms.contains(t) {
                continue;
            }
            let Some(&(Some(lo), Some(hi))) = bounds.get(t) else {
                continue;
            };
            if hi < lo || hi - lo > MAX_INT_CASE_RANGE {
                continue;
            }
            if let Some(val) = self.arith.value(*t).and_then(|r| r.to_i64()) {
                if val < lo || val > hi {
                    // Derived range excludes the model the theory just built —
                    // our bounds are wrong for this term; do not prune.
                    continue;
                }
            }
            candidates.push((*t, lo, hi));
        }
        if candidates.is_empty() {
            return false;
        }

        // Prefer the tightest ranges first (a range-1 split enumerates two).
        candidates.sort_by_key(|&(_, lo, hi)| (hi - lo, lo));
        candidates.truncate(PER_ROUND_CAP);

        for &(term, lo, hi) in &candidates {
            let mut lits: Vec<Lit> = Vec::new();
            for k in lo..=hi {
                let int_k = manager.mk_int(i64::from(k));
                let eq = manager.mk_eq(term, int_k);
                lits.push(self.encode_depth(eq, manager, 0));
            }
            self.sat.add_clause(lits);
            self.case_split_terms.insert(term);
        }

        self.case_split_rounds += 1;
        true
    }

    /// Collect every *user-declared* term that appears directly as an argument
    /// of an uninterpreted function application and has an integer or real
    /// sort.
    ///
    /// Internal preprocessing proxies (`__oxiz_aritharg_*`, `__oxiz_ite_*`,
    /// purification constants `$p*`) are excluded: case-splitting them exposes
    /// a separate theory-combination soundness gap (see the module docs).
    fn collect_int_uf_args(&self, manager: &TermManager) -> Vec<TermId> {
        let int_sort = manager.sorts.int_sort;
        let real_sort = manager.sorts.real_sort;
        let mut seen: FxHashSet<TermId> = FxHashSet::default();
        let mut out: Vec<TermId> = Vec::new();
        for &assertion in &self.assertions {
            for st in collect_subterms(assertion, manager) {
                let Some(t) = manager.get(st) else {
                    continue;
                };
                let TermKind::Apply { args, .. } = &t.kind else {
                    continue;
                };
                for &arg in args {
                    let Some(at) = manager.get(arg) else {
                        continue;
                    };
                    if at.sort != int_sort && at.sort != real_sort {
                        continue;
                    }
                    if self.is_internal_var(arg, manager) {
                        continue;
                    }
                    if seen.insert(arg) {
                        out.push(arg);
                    }
                }
            }
        }
        out
    }

    /// `true` iff `term` is a variable introduced by an internal preprocessing
    /// pass (compound-argument abstraction, `ite` elimination, or arithmetic
    /// purification), identified by its generated name prefix.  Such variables
    /// are not safe targets for case-splitting (see the module docs).
    fn is_internal_var(&self, term: TermId, manager: &TermManager) -> bool {
        let Some(t) = manager.get(term) else {
            return false;
        };
        let TermKind::Var(spur) = &t.kind else {
            return false;
        };
        let name = manager.resolve_str(*spur);
        name.starts_with("__oxiz") || name.starts_with("$p")
    }

    /// Compute sound inclusive integer bounds `[lo, hi]` for arithmetic terms
    /// via a fixpoint of interval propagation over the decision-level-0
    /// arithmetic atoms.
    ///
    /// Only atoms unit-propagated to `true` at level 0 are considered, so every
    /// derived bound holds in all models of the formula.  Equalities propagate
    /// both bounds and drive bound *transfer* between linked variables.
    fn compute_int_bounds(&self) -> FxHashMap<TermId, (Option<i64>, Option<i64>)> {
        let mut facts: Vec<Fact> = Vec::new();
        for (&var, parsed) in &self.var_to_parsed_arith {
            if !self.atom_is_level0_true(var) {
                continue;
            }
            // Coefficients must be integer for our i64 interval arithmetic.
            if parsed.constant.denom() != &1 {
                continue;
            }
            if parsed.terms.iter().any(|(_, c)| c.denom() != &1) {
                continue;
            }
            let dir = match self.var_to_constraint.get(&var) {
                Some(Constraint::Eq(_, _)) => Dir::Eq,
                _ => match parsed.constraint_type {
                    ArithConstraintType::Lt => Dir::Le,
                    ArithConstraintType::Le => Dir::Le,
                    ArithConstraintType::Gt => Dir::Ge,
                    ArithConstraintType::Ge => Dir::Ge,
                },
            };
            // Strict inequalities tighten by one over the integers.
            let constant = match parsed.constraint_type {
                ArithConstraintType::Lt => parsed.constant - Rational64::from_integer(1),
                ArithConstraintType::Gt => parsed.constant + Rational64::from_integer(1),
                _ => parsed.constant,
            };
            facts.push(Fact {
                terms: parsed.terms.clone(),
                constant,
                dir,
            });
        }
        if facts.is_empty() {
            return FxHashMap::default();
        }

        let mut bounds: FxHashMap<TermId, (Option<i64>, Option<i64>)> = FxHashMap::default();
        let mut changed = true;
        while changed {
            changed = false;
            for fact in &facts {
                propagate_fact(fact, &mut bounds, &mut changed);
            }
        }
        bounds
    }

    /// `true` iff the SAT atom `var` is forced to its positive polarity at
    /// decision level 0 — i.e. it is unit-propagated from the formula alone and
    /// therefore holds in every model.  This is the soundness criterion for
    /// using the atom's constraint in bound derivation.
    fn atom_is_level0_true(&self, var: oxiz_sat::Var) -> bool {
        let trail = self.sat.trail();
        trail.level(var) == 0 && trail.value(var).is_true()
    }
}

/// Apply one normalized fact `sum(coef_i·x_i) <dir> constant` to tighten the
/// bounds map.  For every variable, derive the bound implied by the *other*
/// variables' current intervals and intersect.
fn propagate_fact(
    fact: &Fact,
    bounds: &mut FxHashMap<TermId, (Option<i64>, Option<i64>)>,
    changed: &mut bool,
) {
    let Some(c) = fact.constant.to_i64() else {
        return;
    };
    for k in 0..fact.terms.len() {
        let (xk, ak_rat) = &fact.terms[k];
        let Some(ak) = ak_rat.to_i64() else {
            return;
        };
        if ak == 0 {
            continue;
        }
        let (tlo, thi) = sum_excluding(&fact.terms, k, bounds);
        match fact.dir {
            Dir::Eq => {
                // a_k·x_k = c - T  ∈ [c - thi, c - tlo]  (needs T fully bounded)
                let (Some(thi), Some(tlo)) = (thi, tlo) else {
                    continue;
                };
                let Some(klo) = c.checked_sub(thi) else {
                    continue;
                };
                let Some(khi) = c.checked_sub(tlo) else {
                    continue;
                };
                let (lo_b, hi_b) = div_interval(ak, klo, khi);
                tighten(*xk, lo_b, hi_b, bounds, changed);
            }
            Dir::Le => {
                // a_k·x_k <= c - T   (needs T bounded below)
                let Some(tlo) = tlo else {
                    continue;
                };
                let Some(uhi) = c.checked_sub(tlo) else {
                    continue;
                };
                let (lo_b, hi_b) = div_le_ge(ak, uhi, true);
                tighten(*xk, lo_b, hi_b, bounds, changed);
            }
            Dir::Ge => {
                // a_k·x_k >= c - T   (needs T bounded above)
                let Some(thi) = thi else {
                    continue;
                };
                let Some(llo) = c.checked_sub(thi) else {
                    continue;
                };
                let (lo_b, hi_b) = div_le_ge(ak, llo, false);
                tighten(*xk, lo_b, hi_b, bounds, changed);
            }
        }
    }
}

/// Interval of `sum_{i != k} a_i · x_i` from the current bounds.
///
/// Returns `(lo, hi)` as `Option<i64>` where `None` denotes an unbounded side.
/// Any arithmetic overflow is treated as unbounded (forgoes a derivation
/// rather than risk an unsound bound).
fn sum_excluding(
    terms: &[(TermId, Rational64)],
    k: usize,
    bounds: &FxHashMap<TermId, (Option<i64>, Option<i64>)>,
) -> (Option<i64>, Option<i64>) {
    let mut lo: Option<i64> = Some(0);
    let mut hi: Option<i64> = Some(0);
    for (j, (x, a_rat)) in terms.iter().enumerate() {
        if j == k {
            continue;
        }
        let Some(a) = a_rat.to_i64() else {
            return (None, None);
        };
        if a == 0 {
            continue;
        }
        let (xlo, xhi) = bounds.get(x).copied().unwrap_or((None, None));
        // Lower contribution: a>0 ⇒ a·xlo ; a<0 ⇒ a·xhi.
        // Upper contribution: a>0 ⇒ a·xhi ; a<0 ⇒ a·xlo.
        let lo_src = if a > 0 { xlo } else { xhi };
        let hi_src = if a > 0 { xhi } else { xlo };
        lo = match (lo, lo_src.and_then(|v| a.checked_mul(v))) {
            (Some(s), Some(t)) => s.checked_add(t),
            _ => None,
        };
        hi = match (hi, hi_src.and_then(|v| a.checked_mul(v))) {
            (Some(s), Some(t)) => s.checked_add(t),
            _ => None,
        };
    }
    (lo, hi)
}

/// Given `a·x ∈ [klo, khi]`, return the implied inclusive integer `[lo, hi]`
/// of `x` (ceiling on the lower edge, floor on the upper).
fn div_interval(a: i64, klo: i64, khi: i64) -> (Option<i64>, Option<i64>) {
    if a > 0 {
        (ceil_div(klo, a), floor_div(khi, a))
    } else if a < 0 {
        (ceil_div(khi, a), floor_div(klo, a))
    } else {
        (None, None)
    }
}

/// Given a one-sided relation `a·x <= rhs` (`upper = true`) or `a·x >= rhs`,
/// return the implied inclusive integer bound on `x`.
fn div_le_ge(a: i64, rhs: i64, upper: bool) -> (Option<i64>, Option<i64>) {
    if a > 0 {
        if upper {
            (None, floor_div(rhs, a))
        } else {
            (ceil_div(rhs, a), None)
        }
    } else if a < 0 {
        if upper {
            (ceil_div(rhs, a), None)
        } else {
            (None, floor_div(rhs, a))
        }
    } else {
        (None, None)
    }
}

/// Tighten the stored `[lo, hi]` for `x` by intersecting with the new bounds.
fn tighten(
    x: TermId,
    new_lo: Option<i64>,
    new_hi: Option<i64>,
    bounds: &mut FxHashMap<TermId, (Option<i64>, Option<i64>)>,
    changed: &mut bool,
) {
    if new_lo.is_none() && new_hi.is_none() {
        return;
    }
    let entry = bounds.entry(x).or_insert((None, None));
    if let Some(nl) = new_lo {
        let updated = match entry.0 {
            Some(cur) => Some(cur.max(nl)),
            None => Some(nl),
        };
        if updated != entry.0 {
            entry.0 = updated;
            *changed = true;
        }
    }
    if let Some(nh) = new_hi {
        let updated = match entry.1 {
            Some(cur) => Some(cur.min(nh)),
            None => Some(nh),
        };
        if updated != entry.1 {
            entry.1 = updated;
            *changed = true;
        }
    }
}

/// Floor division `num / den` (rounds toward −∞).  `den` must be non-zero.
fn floor_div(num: i64, den: i64) -> Option<i64> {
    if den == 0 {
        return None;
    }
    if den < 0 {
        floor_div(-num, -den)
    } else {
        Some(num.div_euclid(den))
    }
}

/// Ceiling division `num / den` (rounds toward +∞).  `den` must be non-zero.
fn ceil_div(num: i64, den: i64) -> Option<i64> {
    if den == 0 {
        return None;
    }
    if den < 0 {
        ceil_div(-num, -den)
    } else {
        Some(-((-num).div_euclid(den)))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn floor_and_ceil_div_signs() {
        assert_eq!(floor_div(7, 2), Some(3));
        assert_eq!(floor_div(-7, 2), Some(-4));
        assert_eq!(floor_div(7, -2), Some(-4));
        assert_eq!(floor_div(-7, -2), Some(3));
        assert_eq!(ceil_div(7, 2), Some(4));
        assert_eq!(ceil_div(-7, 2), Some(-3));
        assert_eq!(ceil_div(7, -2), Some(-3));
        assert_eq!(ceil_div(-7, -2), Some(4));
        assert_eq!(floor_div(6, 2), Some(3));
        assert_eq!(ceil_div(6, 2), Some(3));
    }

    #[test]
    fn div_interval_positive_coef() {
        // 2·x ∈ [3, 7] ⇒ x ∈ [ceil(3/2), floor(7/2)] = [2, 3]
        assert_eq!(div_interval(2, 3, 7), (Some(2), Some(3)));
    }

    #[test]
    fn div_interval_negative_coef() {
        // -2·x ∈ [3, 7] ⇒ x ∈ [-3.5, -1.5] ⇒ integer [-3, -2]
        assert_eq!(div_interval(-2, 3, 7), (Some(-3), Some(-2)));
    }

    #[test]
    fn div_le_ge_positive_coef() {
        // 2·x <= 7 ⇒ x <= 3
        assert_eq!(div_le_ge(2, 7, true), (None, Some(3)));
        // 2·x >= 3 ⇒ x >= 2
        assert_eq!(div_le_ge(2, 3, false), (Some(2), None));
    }

    #[test]
    fn div_le_ge_negative_coef() {
        // -2·x <= 7 ⇒ x >= -3.5 ⇒ integer x >= -3
        assert_eq!(div_le_ge(-2, 7, true), (Some(-3), None));
        // -2·x >= 3 ⇒ x <= -1.5 ⇒ integer x <= -2
        assert_eq!(div_le_ge(-2, 3, false), (None, Some(-2)));
    }

    #[test]
    fn tighten_intersects() {
        let mut bounds: FxHashMap<TermId, (Option<i64>, Option<i64>)> = FxHashMap::default();
        let mut changed = false;
        tighten(TermId(0), Some(2), None, &mut bounds, &mut changed);
        assert!(changed);
        assert_eq!(bounds.get(&TermId(0)), Some(&(Some(2), None)));
        changed = false;
        // A less-restrictive lower bound (1 < 2) must NOT relax the stored one.
        tighten(TermId(0), Some(1), None, &mut bounds, &mut changed);
        assert!(!changed);
        // A more-restrictive lower bound (5 > 2) tightens it.
        tighten(TermId(0), Some(5), None, &mut bounds, &mut changed);
        assert!(changed);
        assert_eq!(bounds.get(&TermId(0)), Some(&(Some(5), None)));
        changed = false;
        tighten(TermId(0), None, Some(4), &mut bounds, &mut changed);
        assert!(changed);
        assert_eq!(bounds.get(&TermId(0)), Some(&(Some(5), Some(4))));
    }
}
