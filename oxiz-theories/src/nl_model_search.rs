//! Model-based nonlinear integer search — the portable essence of z3's
//! `theory_arith` nonlinear plugin (`src/smt/theory_arith_nl.h`,
//! `process_non_linear`).
//!
//! z3 solves QF_NIA fast not with CAD but with a Simplex tableau over a
//! *linearised* system (each nonlinear monomial is a fresh variable) plus a
//! model-based loop: find a feasible rational model, check that every monomial
//! variable actually equals the product of its factors, and when it does not,
//! branch on an integer variable appearing in a violated monomial. CAD's
//! doubly-exponential projection never runs.
//!
//! This module is a self-contained, sound port of that idea:
//!   * Linearise the top-level comparison conjuncts (monomials → fresh Simplex
//!     variables) and solve the relaxation. The linearisation is a *relaxation*
//!     (monomial variables are unconstrained), so **linear-relaxation-infeasible
//!     ⇒ the original is UNSAT** — a sound `Unsat`.
//!   * Otherwise branch-and-bound toward an integer model, applying local
//!     monomial repair, and **concretely verify** the full original formula
//!     before reporting `Sat` (so a spurious relaxed model can never yield a
//!     wrong `Sat`).
//!
//! Two extensions over the bare relaxation close the gap that defeated it on
//! the VeryMax family (industrial termination VCs):
//!   * **In-tableau monomial repair** (`repair_monomials_via_simplex`): pin each
//!     inconsistent monomial `m` to `∏ value(factors)` and re-run Simplex —
//!     turning `m ≠ x·y` into an explainable infeasibility (a real conflict)
//!     instead of a silent concrete-fail.
//!   * **Disjunctive case-split** (`bool_split`): the relaxation only sees
//!     flat arithmetic conjuncts, so a feasible integer model can still fail a
//!     structural `or`/Boolean conjunct the tableau never encoded. When the
//!     integer/monomial search dead-ends, we case-split a falsified `or`
//!     conjunct, asserting each disjunct (linearised, or split as a two-way
//!     integer disequality) into the relaxation in turn — DPLL-style Boolean
//!     search inlined into the model-based search. This is what solves
//!     `896.smt2` (z3-sat) and the rest of the VeryMax SAT cluster.
//!
//! The whole search runs on a dedicated large-stack worker thread so the
//! recursion (integer B&B → disjunctive split → B&B …) is safe up to the node
//! bound regardless of the caller's stack size.
//!
//! Reference: `theory_arith_nl.h::process_non_linear`, `check_monomial_assignments`,
//! `find_nl_var_for_branching`.

use num_bigint::BigInt;
use num_rational::{BigRational, Rational64};
use num_traits::{ToPrimitive, Zero};

use crate::arithmetic::simplex::{LinExpr, Simplex, VarId};
use oxiz_core::ast::{TermId, TermKind, TermManager};

use crate::ania_ground::{ArrayInterp, eval_bool, eval_int};
use crate::nlsat::NlDispatchResult;
use rustc_hash::FxHashMap;
use std::collections::HashMap;

/// Bound on branch-and-bound nodes (each node re-runs Simplex).
const MAX_BB_NODES: usize = 4_000;
/// Bound on branch-and-bound *recursion depth* — kept equal to the node
/// bound so the real limit is total work, not stack depth. The search runs on
/// a dedicated large-stack worker thread (see `nia_search_core`), so deep
/// recursion is safe; this only guards against pathological unbounded chains
/// (sound to bail — returns `None` → unknown, never a wrong answer).
const MAX_BB_DEPTH: usize = MAX_BB_NODES;
/// Bound on monomial-repair fixpoint iterations per node.
const MAX_REPAIR_ITERS: usize = 32;
/// Bound on the in-tableau monomial value-repair loop (`m := ∏ factors`,
/// re-Simplex) per branch-and-bound node. Each iteration re-pins every
/// inconsistent monomial to the product of the current integer factor values
/// and re-checks feasibility; the loop ends when every monomial is
/// self-consistent (→ concrete verify) or re-Simplex is infeasible (→ a real
/// monomial conflict → branch). See `repair_monomials_via_simplex`.
const MAX_MONO_REPAIR_ITERS: usize = 64;
const REASON: u32 = 0;

/// Upper bound on the number of *free* Boolean variables (after grounding the
/// `(= spur φ)` interface equalities) to exhaustively case-split before the
/// model-based search. Each free Boolean doubles the number of cases, so this
/// is capped to keep the split tractable. (Industrial QF_NIA rarely carries
/// more than a handful after grounding.)
const MAX_FREE_BOOL_CASESPLIT: usize = 8;

/// Entry point. Returns `Some(Sat)` on a concretely-verified integer model,
/// `Some(Unsat)` when the linear relaxation is infeasible (or, when free
/// Boolean variables are case-split, when every case is provably unsat), or
/// `None` to fall through to the CAD-based dispatch.
pub fn try_model_based_nia_search(
    assertions: &[TermId],
    manager: &mut TermManager,
) -> Option<NlDispatchResult> {
    // Ground Boolean interface equalities `(= spur φ)` introduced by
    // purification / Tseitin preprocessing: substitute each Boolean spur
    // variable by its defining formula throughout, so the residual formula
    // contains only evaluable Boolean connectives over arithmetic atoms (no
    // free Boolean leaves). Without this, `fully_evaluable` rejects any
    // formula carrying a Boolean spur (the dominant VeryMax shape) and the
    // search never runs. Substitution is semantics-preserving; the concrete
    // verification at the end remains the soundness backstop.
    let grounded = ground_bool_interface_eqs(assertions, manager);
    let free_bools = free_bool_vars_in(&grounded, manager);
    // Shared branch-and-bound node budget across every case so the total work
    // of the (potentially 2^k-sized) Boolean split stays bounded.
    let mut nodes = 0usize;

    // No free Boolean variables: search the grounded assertions directly.
    if free_bools.is_empty() {
        return nia_search_core(&grounded, manager, &mut nodes);
    }
    // Too many free Booleans to enumerate: fall through (CAD / other paths).
    if free_bools.len() > MAX_FREE_BOOL_CASESPLIT {
        return None;
    }
    // A handful of free Booleans: enumerate their 2^k truth assignments and
    // run the core search on each substituted case. The original formula is
    // SAT iff some case is SAT, and UNSAT iff every case is provably UNSAT
    // (here: every case's linear relaxation is infeasible), so this is sound
    // in both directions. Each reported `Sat` is concretely verified.
    let n = free_bools.len();
    let mut all_unsat = true;
    for bits in 0u32..(1u32 << n) {
        let mut sub: FxHashMap<TermId, TermId> = FxHashMap::default();
        for (i, &v) in free_bools.iter().enumerate() {
            sub.insert(
                v,
                if (bits >> i) & 1 == 1 {
                    manager.mk_true()
                } else {
                    manager.mk_false()
                },
            );
        }
        let cased: Vec<TermId> = grounded
            .iter()
            .map(|&a| manager.substitute(a, &sub))
            .collect();
        match nia_search_core(&cased, manager, &mut nodes) {
            r @ Some(NlDispatchResult::Sat(_)) => return r,
            Some(NlDispatchResult::Unsat) => {}
            None => all_unsat = false,
        }
    }
    if all_unsat {
        Some(NlDispatchResult::Unsat)
    } else {
        None
    }
}

/// Core model-based search on a single, already Boolean-grounded (and
/// case-split) assertion set. Linearise the comparison conjuncts, solve the
/// relaxation (infeasible ⇒ sound `Unsat`), then bounded concrete enumeration
/// and integer branch-and-bound with monomial repair — each returning `Sat`
/// only on a concretely verified witness.
fn nia_search_core(
    assertions: &[TermId],
    manager: &TermManager,
    nodes: &mut usize,
) -> Option<NlDispatchResult> {
    let mut atom_conjuncts: Vec<(TermId, TermId, Cmp)> = Vec::new();
    let mut has_other = false;
    for &a in assertions {
        flatten_collect(a, manager, &mut atom_conjuncts, &mut has_other);
    }
    let _ = has_other; // non-comparison conjuncts are covered by the concrete check
    if atom_conjuncts.is_empty() {
        return None;
    }
    if !fully_evaluable(assertions, manager) {
        return None;
    }
    let int_vars = free_int_vars(assertions, manager);
    if int_vars.is_empty() {
        return None;
    }
    let mut s = Relaxation::build(&atom_conjuncts, &int_vars, manager)?;
    // Linear-relaxation-infeasible ⇒ original UNSAT.
    if s.simplex.check().is_err() {
        return Some(NlDispatchResult::Unsat);
    }
    // Bounded concrete enumeration over a heuristic box: many industrial QF_NIA
    // SAT instances (termination VCs) have small models, so enumerating a small
    // integer box and concretely verifying the full formula is a cheap, sound,
    // and surprisingly effective model finder. Sound for Sat (verified); cannot
    // prove Unsat (a model may live outside the box), so it only short-circuits
    // Sat and otherwise falls through.
    if let Some(witness) = bounded_concrete_search(&int_vars, &atom_conjuncts, assertions, manager)
    {
        return Some(NlDispatchResult::sat_with(
            witness
                .into_iter()
                .map(|(t, v)| (t, BigRational::from_integer(v)))
                .collect(),
        ));
    }
    // Run the (potentially deep) branch-and-bound search on a worker thread
    // with a large stack. Value-exclusion of *unbounded* monomial factors
    // (see `pick_branch`) is productive on VeryMax SAT instances but ascends
    // on UNSAT ones (e.g. `x*x = 2`), recursing up to `MAX_BB_NODES` deep; that
    // overflows the default (test-)thread stack. A dedicated large stack makes
    // the recursion safe regardless of caller stack size, while `MAX_BB_NODES`
    // bounds total work so a doomed ascent still terminates quickly (a tiny
    // relaxation turns over thousands of nodes in milliseconds).

    std::thread::scope(|scope| {
        std::thread::Builder::new()
            .stack_size(512 * 1024 * 1024)
            .spawn_scoped(scope, move || s.search(assertions, manager, nodes, 0))
            .expect("spawn nia search thread")
            .join()
            .expect("nia search thread panicked")
    })
}

/// Free Boolean-sorted variables referenced anywhere in `assertions`.
fn free_bool_vars_in(assertions: &[TermId], manager: &TermManager) -> Vec<TermId> {
    let bool_sort = manager.sorts.bool_sort;
    let mut out = Vec::new();
    let mut visited = std::collections::HashSet::new();
    let mut stack: Vec<TermId> = assertions.to_vec();
    while let Some(id) = stack.pop() {
        if !visited.insert(id) {
            continue;
        }
        let Some(n) = manager.get(id) else { continue };
        if let TermKind::Var(_) = &n.kind
            && n.sort == bool_sort
        {
            out.push(id);
        }
        push_children(&n.kind, &mut stack);
    }
    out
}

/// Substitute Boolean spur variables by their defining formulas.
///
/// Scans every assertion for equalities `(= v φ)` (in either direction)
/// where `v` is a Boolean-sorted `Var` and `φ` is any Boolean-sorted term,
/// recording `v ↦ φ`. Chains (`v₁ ↦ (… v₂ …)`, `v₂ ↦ ψ`) are resolved by a
/// bounded fixpoint over the map itself. Every assertion is then rewritten
/// with the resolved map, so the residual formula references no free
/// Boolean leaf that would otherwise defeat concrete evaluation
/// (`eval_bool` returns `None` for an unassigned Boolean `Var`).
///
/// Semantics-preserving: replacing a variable by an equal term cannot change
/// satisfiability, and the concrete verification at the end of the search
/// remains the soundness backstop. A pure relay (cloned inputs) when no such
/// definitions exist.
fn ground_bool_interface_eqs(assertions: &[TermId], manager: &mut TermManager) -> Vec<TermId> {
    let bool_sort = manager.sorts.bool_sort;
    let is_bool_var = |t: TermId| -> bool {
        manager
            .get(t)
            .is_some_and(|n| n.sort == bool_sort && matches!(n.kind, TermKind::Var(_)))
    };
    let is_bool_sorted =
        |t: TermId| -> bool { manager.get(t).is_some_and(|n| n.sort == bool_sort) };

    let mut defs: FxHashMap<TermId, TermId> = FxHashMap::default();
    {
        let mut stack: Vec<TermId> = assertions.to_vec();
        let mut seen = std::collections::HashSet::new();
        while let Some(id) = stack.pop() {
            if !seen.insert(id) {
                continue;
            }
            let Some(n) = manager.get(id) else { continue };
            if let TermKind::Eq(a, b) = &n.kind {
                let (va, vb) = (is_bool_var(*a), is_bool_var(*b));
                if va && is_bool_sorted(*b) {
                    defs.entry(*a).or_insert(*b);
                } else if vb && is_bool_sorted(*a) {
                    defs.entry(*b).or_insert(*a);
                }
            }
            push_children(&n.kind, &mut stack);
        }
    }

    if defs.is_empty() {
        return assertions.to_vec();
    }

    // Resolve chains: substitute the map into each definition until it is
    // stable (bounded — `substitute` does not recurse into replacements, so a
    // single pass resolves one level of nesting). Any pathological cycle just
    // stops after the cap, leaving a free variable that `fully_evaluable`
    // catches downstream (no correctness impact).
    for _ in 0..16 {
        let mut changed = false;
        for v in defs.keys().copied().collect::<Vec<_>>() {
            let phi = defs[&v];
            let resolved = manager.substitute(phi, &defs);
            if resolved != phi {
                defs.insert(v, resolved);
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }

    let out: Vec<TermId> = assertions
        .iter()
        .map(|&a| manager.substitute(a, &defs))
        .collect();
    out
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Cmp {
    Ge,
    Le,
    Eq,
}

/// Flatten a top-level `and`; record arithmetic comparison conjuncts.
fn flatten_collect(
    term: TermId,
    manager: &TermManager,
    out: &mut Vec<(TermId, TermId, Cmp)>,
    has_other: &mut bool,
) {
    let Some(t) = manager.get(term) else {
        *has_other = true;
        return;
    };
    match &t.kind {
        TermKind::And(args) => {
            for &a in args {
                flatten_collect(a, manager, out, has_other);
            }
        }
        TermKind::Ge(a, b) | TermKind::Gt(a, b) => out.push((*a, *b, Cmp::Ge)), // relax > to ≥
        TermKind::Le(a, b) | TermKind::Lt(a, b) => out.push((*a, *b, Cmp::Le)), // relax < to ≤
        TermKind::Eq(a, b) => {
            if manager
                .get(*a)
                .is_some_and(|n| n.sort == manager.sorts.bool_sort)
            {
                *has_other = true;
            } else {
                out.push((*a, *b, Cmp::Eq));
            }
        }
        _ => *has_other = true,
    }
}

fn fully_evaluable(assertions: &[TermId], manager: &TermManager) -> bool {
    let mut stack: Vec<TermId> = assertions.to_vec();
    let mut seen = std::collections::HashSet::new();
    while let Some(id) = stack.pop() {
        if !seen.insert(id) {
            continue;
        }
        let Some(n) = manager.get(id) else {
            return false;
        };
        match &n.kind {
            TermKind::IntConst(_) | TermKind::True | TermKind::False => {}
            TermKind::Var(_) => {
                if n.sort != manager.sorts.int_sort {
                    return false;
                }
            }
            TermKind::Neg(a) | TermKind::Not(a) => stack.push(*a),
            TermKind::Add(xs) | TermKind::Mul(xs) | TermKind::And(xs) | TermKind::Or(xs) => {
                stack.extend(xs.iter().copied());
            }
            TermKind::Distinct(xs) => stack.extend(xs.iter().copied()),
            TermKind::Sub(a, b)
            | TermKind::Eq(a, b)
            | TermKind::Le(a, b)
            | TermKind::Lt(a, b)
            | TermKind::Ge(a, b)
            | TermKind::Gt(a, b)
            | TermKind::Implies(a, b)
            | TermKind::Xor(a, b) => {
                stack.push(*a);
                stack.push(*b);
            }
            TermKind::Ite(c, a, b) => {
                stack.push(*c);
                stack.push(*a);
                stack.push(*b);
            }
            TermKind::Let { bindings, body } => {
                for &(_, v) in bindings.iter() {
                    stack.push(v);
                }
                stack.push(*body);
            }
            _ => return false,
        }
    }
    true
}

fn free_int_vars(assertions: &[TermId], manager: &TermManager) -> Vec<TermId> {
    let mut out = Vec::new();
    let mut visited = std::collections::HashSet::new();
    let mut stack: Vec<TermId> = assertions.to_vec();
    while let Some(id) = stack.pop() {
        if !visited.insert(id) {
            continue;
        }
        let Some(n) = manager.get(id) else {
            continue;
        };
        if let TermKind::Var(_) = &n.kind {
            if n.sort == manager.sorts.int_sort {
                out.push(id);
            }
            continue;
        }
        push_children(&n.kind, &mut stack);
    }
    out
}

fn push_children(kind: &TermKind, stack: &mut Vec<TermId>) {
    match kind {
        TermKind::Not(a) | TermKind::Neg(a) => stack.push(*a),
        TermKind::Add(xs) | TermKind::Mul(xs) | TermKind::And(xs) | TermKind::Or(xs) => {
            stack.extend(xs.iter().copied());
        }
        TermKind::Distinct(xs) => stack.extend(xs.iter().copied()),
        TermKind::Sub(a, b)
        | TermKind::Eq(a, b)
        | TermKind::Le(a, b)
        | TermKind::Lt(a, b)
        | TermKind::Ge(a, b)
        | TermKind::Gt(a, b)
        | TermKind::Implies(a, b)
        | TermKind::Xor(a, b) => {
            stack.push(*a);
            stack.push(*b);
        }
        TermKind::Ite(c, a, b) => {
            stack.push(*c);
            stack.push(*a);
            stack.push(*b);
        }
        TermKind::Let { bindings, body } => {
            for &(_, v) in bindings.iter() {
                stack.push(v);
            }
            stack.push(*body);
        }
        _ => {}
    }
}

type MonoKey = Vec<(TermId, u32)>;

/// A branch-and-bound decision. `FloorCeil` is the classic integer
/// integrality split on a *non-integral* variable (`v ≤ floor` / `v ≥ ceil`).
/// `Exclude` is z3's `branch_nl_int_var` shape for a variable that is already
/// integral but sits inside an *inconsistent* monomial (`m ≠ ∏ factors`): the
/// current integer value `k` cannot be part of a monomial-consistent model, so
/// the split `v ≤ k−1` / `v ≥ k+1` removes it from both children. Without
/// `Exclude` the search dead-ends whenever every variable is integral yet some
/// product is wrong — exactly the VeryMax shape that defeated the relaxation.
enum Branch {
    /// `var` is non-integral at `val`; split `var ≤ floor` | `var ≥ ceil`.
    FloorCeil {
        var: TermId,
        floor: Rational64,
        ceil: Rational64,
    },
    /// `var` is integral at `value` but is a factor of an inconsistent
    /// monomial; split `var ≤ value−1` | `var ≥ value+1`.
    Exclude { var: TermId, value: Rational64 },
}

/// Outcome of trying to force a Boolean term to a given polarity by adding
/// linear constraints to the relaxation. Used by the disjunctive case-split
/// ([`Relaxation::bool_split`]) to translate each `or` disjunct (or its
/// negation, via `not`) into relaxation work.
enum AssertPlan {
    /// The term was fully asserted as linear constraint(s) under the current
    /// push scope; proceed to re-check + recurse.
    Done,
    /// The term is trivially false under this polarity — this disjunct cannot
    /// contribute; skip it.
    Infeasible,
    /// The term forces a disequality `expr ≠ 0` (e.g. `(not (= v 0))`);
    /// the caller must split it into `expr ≤ −1` | `expr ≥ +1` (a two-way
    /// integer branch), since Simplex has no native disequality.
    SplitExpr(LinExpr),
    /// The term is not a linearizable Boolean shape we handle (nested `or` in
    /// a conjunction, Boolean disequalities, `ite`, …); skip it. Skipping only
    /// loses completeness — never soundness — because every reported `Sat` is
    /// still concretely verified.
    Skip,
}

/// Comparison direction for [`Relaxation::assert_cmp`]. Distinct from the
/// top-level [`Cmp`] (which is the *relaxed* direction used while building the
/// relaxation) because here we assert the *exact* integer semantics of each
/// SMT comparison, including strict ones.
#[derive(Clone, Copy)]
enum CmpDir {
    Le,
    Ge,
    Eq,
    Lt,
    Gt,
}

struct Relaxation<'a> {
    manager: &'a TermManager,
    simplex: Simplex,
    var: HashMap<TermId, VarId>,
    mono: HashMap<MonoKey, VarId>,
    mono_def: Vec<(VarId, MonoKey)>,
    int_vars: Vec<TermId>,
    /// Equality conjuncts (lhs, rhs) used for model repair (solve-for-variable).
    eq_atoms: Vec<(TermId, TermId)>,
}

impl<'a> Relaxation<'a> {
    fn build(
        atoms: &[(TermId, TermId, Cmp)],
        int_vars: &[TermId],
        manager: &'a TermManager,
    ) -> Option<Self> {
        let mut s = Self {
            manager,
            simplex: Simplex::new(),
            var: HashMap::new(),
            mono: HashMap::new(),
            mono_def: Vec::new(),
            int_vars: int_vars.to_vec(),
            eq_atoms: atoms
                .iter()
                .filter(|(_, _, c)| *c == Cmp::Eq)
                .map(|&(l, r, _)| (l, r))
                .collect(),
        };
        for &v in int_vars {
            s.var.insert(v, s.simplex.new_var());
        }
        for &(lhs, rhs, cmp) in atoms {
            let mut e = s.translate(lhs)?;
            let r = s.translate(rhs)?;
            add_expr_scaled(&mut e, &r, Rational64::from_integer(-1));
            match cmp {
                Cmp::Ge => s.simplex.add_ge(e, REASON),
                Cmp::Le => s.simplex.add_le(e, REASON),
                Cmp::Eq => s.simplex.add_eq(e, REASON),
            }
        }
        Some(s)
    }

    fn translate(&mut self, term: TermId) -> Option<LinExpr> {
        let n = self.manager.get(term)?;
        match &n.kind {
            TermKind::IntConst(k) => Some(LinExpr::constant(big_to_r64(k)?)),
            TermKind::Var(_) => Some(LinExpr::var(*self.var.get(&term)?)),
            TermKind::Neg(x) => {
                let mut e = self.translate(*x)?;
                e.negate();
                Some(e)
            }
            TermKind::Add(args) => {
                let mut acc = LinExpr::constant(Rational64::zero());
                for &a in args {
                    add_expr_scaled(&mut acc, &self.translate(a)?, Rational64::from_integer(1));
                }
                Some(acc)
            }
            TermKind::Sub(a, b) => {
                let mut e = self.translate(*a)?;
                add_expr_scaled(&mut e, &self.translate(*b)?, Rational64::from_integer(-1));
                Some(e)
            }
            TermKind::Mul(args) => self.translate_mul(args),
            _ => None,
        }
    }

    fn translate_mul(&mut self, args: &[TermId]) -> Option<LinExpr> {
        let mut coeff = Rational64::from_integer(1);
        let mut powers: HashMap<TermId, u32> = HashMap::new();
        let mut stack: Vec<TermId> = args.to_vec();
        while let Some(id) = stack.pop() {
            let n = self.manager.get(id)?;
            match &n.kind {
                TermKind::IntConst(k) => coeff *= big_to_r64(k)?,
                TermKind::Neg(x) => {
                    coeff *= Rational64::from_integer(-1);
                    stack.push(*x);
                }
                TermKind::Mul(inner) => stack.extend(inner.iter().copied()),
                TermKind::Var(_) => *powers.entry(id).or_insert(0) += 1,
                // Compound factor (e.g. `(- 0 1)` = -1): translate it and fold
                // if it is a pure constant; a variable-bearing compound factor
                // (e.g. `(x+1)*y`) is not a single monomial — bail honestly.
                _ => {
                    let e = self.translate(id)?;
                    if e.terms.is_empty() {
                        coeff *= e.constant;
                    } else {
                        return None;
                    }
                }
            }
        }
        let mut distinct: Vec<(TermId, u32)> = powers.into_iter().collect();
        distinct.sort_by_key(|(t, _)| t.0);
        if distinct.is_empty() {
            Some(LinExpr::constant(coeff))
        } else if distinct.len() == 1 && distinct[0].1 == 1 {
            let v = *self.var.get(&distinct[0].0)?;
            let mut e = LinExpr::var(v);
            e.scale(coeff);
            Some(e)
        } else {
            let mvar = if let Some(&mv) = self.mono.get(&distinct) {
                mv
            } else {
                let mv = self.simplex.new_var();
                self.mono.insert(distinct.clone(), mv);
                self.mono_def.push((mv, distinct));
                mv
            };
            let mut e = LinExpr::var(mvar);
            e.scale(coeff);
            Some(e)
        }
    }

    /// Wrap a concrete integer witness as a dispatch `Sat` result.
    fn sat_result(witness: HashMap<TermId, BigInt>) -> NlDispatchResult {
        NlDispatchResult::sat_with(
            witness
                .into_iter()
                .map(|(t, v)| (t, BigRational::from_integer(v)))
                .collect(),
        )
    }

    /// Recursive branch-and-bound. `nodes` counts explored nodes across the
    /// whole search; `depth` bounds the recursion stack. Returns `Some(Sat)` on
    /// a verified witness, else `None`.
    fn search(
        &mut self,
        assertions: &[TermId],
        manager: &TermManager,
        nodes: &mut usize,
        depth: usize,
    ) -> Option<NlDispatchResult> {
        *nodes += 1;
        if *nodes > MAX_BB_NODES || depth > MAX_BB_DEPTH {
            return None;
        }
        // Current rational model is feasible (caller ensured check() ok).
        if let Some(witness) = self.repair_and_verify(assertions, manager) {
            return Some(Self::sat_result(witness));
        }
        // In-tableau monomial value-repair (z3 `process_non_linear`, step 2):
        // pin each inconsistent monomial variable to the product of its
        // integer factors and re-run Simplex. If the system stays feasible,
        // the monomials become honest and we re-round + concretely verify. If
        // it goes infeasible, the current integer factor assignment is
        // incompatible with `m = x·y` — a real conflict the relaxation alone
        // could never surface. Either outcome only prunes or verifies; never
        // produces a wrong answer.
        if let Some(witness) = self.repair_monomials_via_simplex(assertions, manager) {
            return Some(Self::sat_result(witness));
        }
        let branch = match self.pick_branch() {
            Some(b) => b,
            None => {
                // No integer/monomial branch exists, yet the concrete check
                // fails: the culprit must be the Boolean *structure* (a
                // disjunction the relaxation cannot see — the dominant VeryMax
                // shape, e.g. `(or (not (= inv 0)) …)` forcing a nonzero
                // invariant). Case-split a falsified disjunctive conjunct,
                // asserting each disjunct into the relaxation in turn. This is
                // DPLL-style Boolean search inlined into the model-based
                // search; bounded by `nodes` and sound (Sat only on concrete
                // verify).
                let env = self.round_int_model();
                if let Some(or_term) = self.find_falsified_disjunction(assertions, &env) {
                    return self.bool_split(or_term, assertions, manager, nodes, depth);
                }
                return None;
            }
        };
        match branch {
            Branch::FloorCeil { var, floor, ceil } => {
                let vid = self.var[&var];
                // floor branch: x ≤ floor
                self.simplex.push();
                self.simplex.set_upper(vid, floor, REASON);
                let r = if self.simplex.check().is_ok() {
                    self.search(assertions, manager, nodes, depth + 1)
                } else {
                    None
                };
                self.simplex.pop();
                if r.is_some() {
                    return r;
                }
                // ceil branch: x ≥ ceil
                self.simplex.push();
                self.simplex.set_lower(vid, ceil, REASON);
                let r = if self.simplex.check().is_ok() {
                    self.search(assertions, manager, nodes, depth + 1)
                } else {
                    None
                };
                self.simplex.pop();
                r
            }
            Branch::Exclude { var, value } => {
                let vid = self.var[&var];
                let one = Rational64::from_integer(1);
                // lower child: var ≤ value − 1 (drop the current integer value)
                self.simplex.push();
                self.simplex.set_upper(vid, value - one, REASON);
                let r = if self.simplex.check().is_ok() {
                    self.search(assertions, manager, nodes, depth + 1)
                } else {
                    None
                };
                self.simplex.pop();
                if r.is_some() {
                    return r;
                }
                // upper child: var ≥ value + 1
                self.simplex.push();
                self.simplex.set_lower(vid, value + one, REASON);
                let r = if self.simplex.check().is_ok() {
                    self.search(assertions, manager, nodes, depth + 1)
                } else {
                    None
                };
                self.simplex.pop();
                r
            }
        }
    }

    /// Find a top-level conjunct of `assertions` that is a falsified `or`
    /// (descending through `and`). The relaxation cannot see disjunctions, so
    /// when the integer/monomial search dead-ends, a falsified `or` is the
    /// natural Boolean split point. Returns the first such `or` term.
    fn find_falsified_disjunction(
        &self,
        assertions: &[TermId],
        env: &HashMap<TermId, BigInt>,
    ) -> Option<TermId> {
        let arrays: HashMap<TermId, ArrayInterp> = HashMap::new();
        let mut stack: Vec<TermId> = assertions.to_vec();
        while let Some(t) = stack.pop() {
            let Some(n) = self.manager.get(t) else {
                continue;
            };
            match &n.kind {
                TermKind::And(xs) => stack.extend(xs.iter().copied()),
                TermKind::Or(_) if !eval_bool(t, self.manager, &arrays, env).unwrap_or(false) => {
                    return Some(t);
                }
                _ => {}
            }
        }
        None
    }

    /// Case-split a falsified `or` conjunct: try each disjunct in turn, asserting
    /// it into the relaxation (under a push scope) and recursing. The first
    /// disjunct that yields a concretely-verified model wins. Sound (Sat only
    /// on concrete verify); bounded by `nodes`.
    fn bool_split(
        &mut self,
        or_term: TermId,
        assertions: &[TermId],
        manager: &TermManager,
        nodes: &mut usize,
        depth: usize,
    ) -> Option<NlDispatchResult> {
        let disjuncts: Vec<TermId> = self
            .manager
            .get(or_term)
            .and_then(|n| match &n.kind {
                TermKind::Or(xs) => Some(xs.iter().copied().collect()),
                _ => None,
            })
            .unwrap_or_default();
        for d in disjuncts {
            self.simplex.push();
            let r = self.exec_disjunct(d, assertions, manager, nodes, depth);
            self.simplex.pop();
            if r.is_some() {
                return r;
            }
        }
        None
    }

    /// Assert disjunct `d` true under the current (already-pushed) scope and
    /// recurse. Handles a linearizable disjunct directly; a disequality
    /// disjunct (e.g. `(not (= v 0))`) via a two-way integer split; anything
    /// else is skipped.
    fn exec_disjunct(
        &mut self,
        d: TermId,
        assertions: &[TermId],
        manager: &TermManager,
        nodes: &mut usize,
        depth: usize,
    ) -> Option<NlDispatchResult> {
        let plan = self.plan_assert_true(d);
        match plan {
            AssertPlan::Done => {
                if self.simplex.check().is_ok() {
                    self.search(assertions, manager, nodes, depth + 1)
                } else {
                    None
                }
            }
            AssertPlan::SplitExpr(e) => {
                // child 1: expr ≤ −1  (i.e. expr + 1 ≤ 0)
                self.simplex.push();
                let mut lo = e.clone();
                lo.add_constant(Rational64::from_integer(1));
                self.simplex.add_le(lo, REASON);
                let r = if self.simplex.check().is_ok() {
                    self.search(assertions, manager, nodes, depth + 1)
                } else {
                    None
                };
                self.simplex.pop();
                if r.is_some() {
                    return r;
                }
                // child 2: expr ≥ +1  (i.e. expr − 1 ≥ 0)
                self.simplex.push();
                let mut hi = e;
                hi.add_constant(Rational64::from_integer(-1));
                self.simplex.add_ge(hi, REASON);
                let r = if self.simplex.check().is_ok() {
                    self.search(assertions, manager, nodes, depth + 1)
                } else {
                    None
                };
                self.simplex.pop();
                r
            }
            AssertPlan::Infeasible | AssertPlan::Skip => None,
        }
    }

    /// Plan how to make `term` TRUE in the relaxation. Adds the implied linear
    /// constraints for `Done`; returns `SplitExpr` for a disequality the caller
    /// must branch on; `Skip` for unhandled shapes.
    fn plan_assert_true(&mut self, term: TermId) -> AssertPlan {
        let Some(n) = self.manager.get(term) else {
            return AssertPlan::Skip;
        };
        match &n.kind {
            TermKind::True => AssertPlan::Done,
            TermKind::False => AssertPlan::Infeasible,
            TermKind::Not(x) => self.plan_assert_false(*x),
            TermKind::And(xs) => {
                for &x in xs {
                    match self.plan_assert_true(x) {
                        AssertPlan::Done => {}
                        other => return other,
                    }
                }
                AssertPlan::Done
            }
            // Arithmetic comparisons: translate lhs − rhs and bound it.
            TermKind::Le(a, b) => self.assert_cmp(*a, *b, CmpDir::Le),
            TermKind::Ge(a, b) => self.assert_cmp(*a, *b, CmpDir::Ge),
            TermKind::Lt(a, b) => self.assert_cmp(*a, *b, CmpDir::Lt),
            TermKind::Gt(a, b) => self.assert_cmp(*a, *b, CmpDir::Gt),
            TermKind::Eq(a, b) => {
                if Self::term_is_bool(self.manager, *a) {
                    AssertPlan::Skip
                } else {
                    self.assert_cmp(*a, *b, CmpDir::Eq)
                }
            }
            _ => AssertPlan::Skip,
        }
    }

    /// Plan how to make `term` FALSE in the relaxation (the polarity under
    /// `not`). Mirrors [`Self::plan_assert_true`] with negated comparisons;
    /// a negated equality becomes a disequality split.
    fn plan_assert_false(&mut self, term: TermId) -> AssertPlan {
        let Some(n) = self.manager.get(term) else {
            return AssertPlan::Skip;
        };
        match &n.kind {
            TermKind::True => AssertPlan::Infeasible,
            TermKind::False => AssertPlan::Done,
            TermKind::Not(x) => self.plan_assert_true(*x),
            // ¬(∨ xs) = ∧(¬ xs): assert every disjunct false.
            TermKind::Or(xs) => {
                for &x in xs {
                    match self.plan_assert_false(x) {
                        AssertPlan::Done => {}
                        other => return other,
                    }
                }
                AssertPlan::Done
            }
            TermKind::Le(a, b) => self.assert_cmp(*a, *b, CmpDir::Gt),
            TermKind::Ge(a, b) => self.assert_cmp(*a, *b, CmpDir::Lt),
            TermKind::Lt(a, b) => self.assert_cmp(*a, *b, CmpDir::Ge),
            TermKind::Gt(a, b) => self.assert_cmp(*a, *b, CmpDir::Le),
            TermKind::Eq(a, b) => {
                if Self::term_is_bool(self.manager, *a) {
                    AssertPlan::Skip
                } else {
                    // a ≠ b  ⇒  (a−b) ≠ 0  ⇒  split ≤ −1 | ≥ +1
                    match self.diff_expr(*a, *b) {
                        Some(e) => AssertPlan::SplitExpr(e),
                        None => AssertPlan::Skip,
                    }
                }
            }
            _ => AssertPlan::Skip,
        }
    }

    /// Whether a term is Boolean-sorted (so its equality is a Boolean, not
    /// arithmetic, equality — handled by substitution, not the relaxation).
    fn term_is_bool(manager: &TermManager, t: TermId) -> bool {
        manager
            .get(t)
            .is_some_and(|n| n.sort == manager.sorts.bool_sort)
    }

    /// Translate `a − b` to a `LinExpr`, or `None` if not linearizable.
    fn diff_expr(&mut self, a: TermId, b: TermId) -> Option<LinExpr> {
        let mut e = self.translate(a)?;
        let r = self.translate(b)?;
        add_expr_scaled(&mut e, &r, Rational64::from_integer(-1));
        Some(e)
    }

    /// Assert `a (cmp) b` into the relaxation as `Done`, where the comparison
    /// direction is what must hold. Integer-strict semantics: `Lt` ⇒ `a−b ≤ −1`,
    /// `Gt` ⇒ `a−b ≥ +1` (valid because every variable is integer-sorted).
    fn assert_cmp(&mut self, a: TermId, b: TermId, dir: CmpDir) -> AssertPlan {
        let Some(mut e) = self.diff_expr(a, b) else {
            return AssertPlan::Skip;
        };
        match dir {
            CmpDir::Le => self.simplex.add_le(e, REASON),
            CmpDir::Ge => self.simplex.add_ge(e, REASON),
            CmpDir::Eq => self.simplex.add_eq(e, REASON),
            CmpDir::Lt => {
                // a < b  ⇒  a − b ≤ −1  ⇒  (a − b) + 1 ≤ 0
                e.add_constant(Rational64::from_integer(1));
                self.simplex.add_le(e, REASON);
            }
            CmpDir::Gt => {
                // a > b  ⇒  a − b ≥ +1  ⇒  (a − b) − 1 ≥ 0
                e.add_constant(Rational64::from_integer(-1));
                self.simplex.add_ge(e, REASON);
            }
        }
        AssertPlan::Done
    }

    /// Round the Simplex model to integers, run a bounded monomial-repair
    /// fixpoint, and concretely verify the full formula. Returns a witness
    /// iff verification succeeds.
    fn repair_and_verify(
        &self,
        assertions: &[TermId],
        manager: &TermManager,
    ) -> Option<HashMap<TermId, BigInt>> {
        let mut env: HashMap<TermId, BigInt> = HashMap::new();
        for v in &self.int_vars {
            let r = self.simplex.value(self.var[v]);
            let rounded = if r.is_integer() {
                r64_to_big(r)
            } else {
                r64_to_big(r.floor())
            };
            env.insert(*v, rounded);
        }
        if self.concrete_sat(&env, assertions, manager) {
            return Some(env);
        }
        for _ in 0..MAX_REPAIR_ITERS {
            if !self.repair_step(&mut env) {
                break;
            }
            if self.concrete_sat(&env, assertions, manager) {
                return Some(env);
            }
        }
        None
    }

    fn concrete_sat(
        &self,
        env: &HashMap<TermId, BigInt>,
        assertions: &[TermId],
        manager: &TermManager,
    ) -> bool {
        let arrays: HashMap<TermId, ArrayInterp> = HashMap::new();
        for &a in assertions {
            if !eval_bool(a, manager, &arrays, env).unwrap_or(false) {
                return false;
            }
        }
        true
    }

    /// Equality-based model repair (z3 `theory_arith` style): for each
    /// violated equality conjunct `lhs = rhs`, view the polynomial as linear in
    /// one of its variables and solve for that variable (`v = -rest/coeff`),
    /// preferring an integer result. This is what lets a product equality such
    /// as `b9·a2 - a2 = 0` collapse to `b9 = 1` once `a2` is fixed.
    fn repair_step(&self, env: &mut HashMap<TermId, BigInt>) -> bool {
        let arrays: HashMap<TermId, ArrayInterp> = HashMap::new();
        for &(lhs, rhs) in &self.eq_atoms {
            let l = eval_int(lhs, self.manager, &arrays, env);
            let r = eval_int(rhs, self.manager, &arrays, env);
            let (Some(l), Some(r)) = (l, r) else { continue };
            if l == r {
                continue; // equality already satisfied
            }
            // Try to solve `lhs - rhs = 0` for one variable, linearly.
            if let Some((v, new_val)) = solve_eq_for_var(lhs, rhs, self.manager, env) {
                env.insert(v, new_val);
                return true;
            }
        }
        false
    }

    /// In-tableau monomial value-repair (z3 `process_non_linear`, the
    /// repair-recheck-conflict loop). Under a fresh push scope, repeatedly
    /// round the integer factors and pin every monomial variable `m` whose
    /// relaxation value disagrees with `∏ value(factors)` to that product, then
    /// re-run Simplex. If every monomial becomes self-consistent, concretely
    /// verify and return a witness. If re-Simplex is infeasible, the current
    /// integer factor assignment is incompatible with `m = x·y` under the
    /// asserted atoms — return `None` so the caller branches away from it.
    /// Sound: a witness is returned only after [`Self::concrete_sat`]; `None`
    /// only declines to decide, so the worst a bug can do is miss a model.
    fn repair_monomials_via_simplex(
        &mut self,
        assertions: &[TermId],
        manager: &TermManager,
    ) -> Option<HashMap<TermId, BigInt>> {
        if self.mono_def.is_empty() {
            return None;
        }
        self.simplex.push();
        let outcome = self.mono_repair_loop(assertions, manager);
        self.simplex.pop();
        outcome
    }

    /// The bounded fixpoint body of [`Self::repair_monomials_via_simplex`],
    /// run under a push scope so every pin is undone by the caller's `pop`.
    fn mono_repair_loop(
        &mut self,
        assertions: &[TermId],
        manager: &TermManager,
    ) -> Option<HashMap<TermId, BigInt>> {
        for _ in 0..MAX_MONO_REPAIR_ITERS {
            let env = self.round_int_model();
            if self.concrete_sat(&env, assertions, manager) {
                return Some(env);
            }
            // Pin each monomial whose relaxation value ≠ ∏ factors to the
            // product of the current integer factor values.
            let mut pins: Vec<(VarId, Rational64)> = Vec::new();
            for &(mvar, ref factors) in &self.mono_def {
                let (prod_big, ok) = eval_product(factors, &env);
                if !ok {
                    continue;
                }
                let Some(prod) = big_to_r64(&prod_big) else {
                    continue;
                };
                if self.simplex.value(mvar) != prod {
                    pins.push((mvar, prod));
                }
            }
            if pins.is_empty() {
                // Every monomial is consistent with the integer factors, yet the
                // concrete check failed (a strict inequality or a linear
                // constraint the rounding broke). No further tableau repair can
                // help — hand back to branching.
                return None;
            }
            for (mvar, prod) in &pins {
                self.simplex.set_lower(*mvar, *prod, REASON);
                self.simplex.set_upper(*mvar, *prod, REASON);
            }
            if self.simplex.check().is_err() {
                // Infeasible: the integer factor assignment is incompatible
                // with `m = x·y` under the linear constraints — a real
                // conflict the relaxation alone could never surface.
                return None;
            }
            // Feasible: the monomials are now honest at the pins. Loop to
            // re-round the moved factor model and re-check consistency.
        }
        None
    }

    /// Round the current Simplex rational model of the integer variables to a
    /// `BigInt` environment (floor on non-integrals), matching
    /// [`Self::repair_and_verify`]'s rounding so both paths explore the same
    /// integer candidates.
    fn round_int_model(&self) -> HashMap<TermId, BigInt> {
        let mut env: HashMap<TermId, BigInt> = HashMap::new();
        for v in &self.int_vars {
            let r = self.simplex.value(self.var[v]);
            let rounded = if r.is_integer() {
                r64_to_big(r)
            } else {
                r64_to_big(r.floor())
            };
            env.insert(*v, rounded);
        }
        env
    }

    /// Pick the next branch-and-bound decision (z3 `find_nl_var_for_branching` /
    /// `branch_nl_int_var`): split a non-integral integer var (preferably a
    /// monomial factor) floor/ceil; if all are integral, exclude the value of
    /// an inconsistent monomial's factor so an all-integral-but-monomially-
    /// wrong model does not dead-end the search.
    fn pick_branch(&self) -> Option<Branch> {
        let mono_var_ids: std::collections::HashSet<TermId> = self
            .mono_def
            .iter()
            .flat_map(|(_, f)| f.iter().map(|(v, _)| *v))
            .collect();
        let mut mono_nonint: Option<TermId> = None;
        let mut any_nonint: Option<TermId> = None;
        for &v in &self.int_vars {
            let val = self.simplex.value(self.var[&v]);
            if val.is_integer() {
                continue;
            }
            if mono_var_ids.contains(&v) && mono_nonint.is_none() {
                mono_nonint = Some(v);
            }
            if any_nonint.is_none() {
                any_nonint = Some(v);
            }
        }
        if let Some(v) = mono_nonint.or(any_nonint) {
            let val = self.simplex.value(self.var[&v]);
            return Some(Branch::FloorCeil {
                var: v,
                floor: val.floor(),
                ceil: val.ceil(),
            });
        }
        // All integer variables are integral, yet the concrete check fails and
        // (typically) some monomial is inconsistent (`m ≠ ∏ factors`). Branch
        // on a factor of an inconsistent monomial by excluding its current
        // value (`v ≤ k−1` | `v ≥ k+1`) — z3's `branch_nl_int_var` shape.
        // Prefer the bounded factor with the smallest range (shallowest tree),
        // but fall back to an unbounded factor: many VeryMax models are only
        // reachable by excluding a variable that is unbounded in the relaxation.
        // (Unbounded exclusion can ascend on UNSAT instances, so the search runs
        // on a large-stack worker thread and is bounded by `MAX_BB_NODES`.)
        let env = self.round_int_model();
        // (var, current value, range if bounded)
        let mut best: Option<(TermId, Rational64, Option<Rational64>)> = None;
        for (_, factors) in &self.mono_def {
            let (prod_big, ok) = eval_product(factors, &env);
            if !ok {
                continue;
            }
            let Some(prod) = big_to_r64(&prod_big) else {
                continue;
            };
            let mvar = self.mono.get(factors).copied();
            let Some(mvar) = mvar else { continue };
            if self.simplex.value(mvar) == prod {
                continue; // monomial already consistent
            }
            for &(fvar, _p) in factors {
                let vid = match self.var.get(&fvar) {
                    Some(&vid) => vid,
                    None => continue,
                };
                let fval = self.simplex.value(vid);
                let range = match (self.simplex.get_lower(vid), self.simplex.get_upper(vid)) {
                    (Some(lo), Some(hi)) => Some(hi.value.real - lo.value.real),
                    _ => None,
                };
                let take = match (&best, range) {
                    (None, _) => true,
                    (Some((_, _, Some(br))), Some(r)) => r < *br,
                    (Some((_, _, None)), Some(_)) => true,
                    (_, None) => best.is_none(),
                };
                if take {
                    best = Some((fvar, fval, range));
                }
            }
        }
        let (var, value, _) = best?;
        Some(Branch::Exclude { var, value })
    }
}

fn add_expr_scaled(acc: &mut LinExpr, other: &LinExpr, scale: Rational64) {
    for &(v, c) in &other.terms {
        acc.add_term(v, c * scale);
    }
    acc.add_constant(other.constant * scale);
}

const ENUM_BUDGET: u64 = 1_000_000;

/// Derive tight integer lower/upper bounds for `var` from unit comparison
/// conjuncts of the shape `var OP const` / `const OP var`.
fn unit_bounds_for_var(
    var: TermId,
    atoms: &[(TermId, TermId, Cmp)],
    manager: &TermManager,
) -> (Option<i64>, Option<i64>) {
    let mut lo: Option<i64> = None;
    let mut hi: Option<i64> = None;
    let is_var = |t: TermId| {
        manager
            .get(t)
            .is_some_and(|n| matches!(n.kind, TermKind::Var(_)) && t == var)
    };
    let const_of = |t: TermId| -> Option<i64> {
        manager.get(t).and_then(|n| match &n.kind {
            TermKind::IntConst(k) => k.to_i64(),
            _ => None,
        })
    };
    for &(lhs, rhs, cmp) in atoms {
        let (lv, lc, rv, rc) = (is_var(lhs), const_of(lhs), is_var(rhs), const_of(rhs));
        match (cmp, lv, rv, lc, rc) {
            // var ≥ c  (or var > c → var ≥ c+1)
            (Cmp::Ge, true, false, _, Some(c)) => lo = Some(lo.map_or(c, |x| x.max(c))),
            // c ≤ var  ⇔ var ≥ c  comes in as (Le, lhs=c, rhs=var)
            (Cmp::Le, false, true, Some(c), _) => lo = Some(lo.map_or(c, |x| x.max(c))),
            // var ≤ c
            (Cmp::Le, true, false, _, Some(c)) => hi = Some(hi.map_or(c, |x| x.min(c))),
            // c ≥ var  ⇔ var ≤ c  comes in as (Ge, lhs=c, rhs=var)
            (Cmp::Ge, false, true, Some(c), _) => hi = Some(hi.map_or(c, |x| x.min(c))),
            // var = c
            (Cmp::Eq, true, false, _, Some(c)) => {
                lo = Some(lo.map_or(c, |x| x.max(c)));
                hi = Some(hi.map_or(c, |x| x.min(c)));
            }
            (Cmp::Eq, false, true, Some(c), _) => {
                lo = Some(lo.map_or(c, |x| x.max(c)));
                hi = Some(hi.map_or(c, |x| x.min(c)));
            }
            _ => {}
        }
    }
    (lo, hi)
}

/// Enumerate a bounded integer box and return the first assignment that
/// satisfies the full assertion set (concretely verified). Returns `None` if
/// the box is too large or contains no model. The box width for unbounded
/// variables is chosen *adaptively* so the total cartesian product fits
/// `ENUM_BUDGET`: `width = floor((budget / tight_product) ^ (1/n_unbound))`.
/// This makes the search scale with variable count (small-n instances get a
/// wide box, large-n ones a narrow one) instead of a fixed width that either
/// skips large-n instances or starves small-n ones.
fn bounded_concrete_search(
    int_vars: &[TermId],
    atom_conjuncts: &[(TermId, TermId, Cmp)],
    assertions: &[TermId],
    manager: &TermManager,
) -> Option<HashMap<TermId, BigInt>> {
    // Per-variable tight bounds from unit comparison conjuncts.
    let mut tight: Vec<(TermId, i64, Option<i64>)> = Vec::with_capacity(int_vars.len());
    let mut tight_product: u64 = 1;
    for &v in int_vars {
        let (lo, hi) = unit_bounds_for_var(v, atom_conjuncts, manager);
        let lo = lo.unwrap_or(0);
        if let Some(hi) = hi {
            if hi < lo {
                return None; // contradictory unit bounds
            }
            tight_product = tight_product.saturating_mul((hi - lo + 1) as u64);
            if tight_product > ENUM_BUDGET {
                return None;
            }
            tight.push((v, lo, Some(hi)));
        } else {
            tight.push((v, lo, None));
        }
    }
    if tight.is_empty() {
        return None;
    }
    // Adaptive width for the unbounded variables.
    let n_unbound = tight.iter().filter(|(_, _, h)| h.is_none()).count() as u64;
    let width = if n_unbound == 0 {
        1u64
    } else {
        let remaining = (ENUM_BUDGET / tight_product.max(1)) as f64;
        let mut w = (remaining.powf(1.0 / n_unbound as f64)).floor() as u64;
        // Guard against f64 rounding: shrink until the product fits.
        while w > 1
            && w.saturating_pow(n_unbound as u32)
                .saturating_mul(tight_product)
                > ENUM_BUDGET
        {
            w -= 1;
        }
        w.max(1)
    };
    // Build the final domains.
    let mut domains: Vec<(TermId, i64, i64)> = Vec::with_capacity(tight.len());
    for (v, lo, h) in tight {
        let hi = match h {
            Some(hi) => hi,
            None => lo + (width as i64) - 1,
        };
        domains.push((v, lo, hi));
    }
    let arrays: HashMap<TermId, ArrayInterp> = HashMap::new();
    let mut idx: Vec<i64> = domains.iter().map(|(_, lo, _)| *lo).collect();
    loop {
        let env: HashMap<TermId, BigInt> = domains
            .iter()
            .zip(idx.iter())
            .map(|((v, _, _), &val)| (*v, BigInt::from(val)))
            .collect();
        if assertions
            .iter()
            .all(|a| eval_bool(*a, manager, &arrays, &env).unwrap_or(false))
        {
            return Some(env);
        }
        // odometer increment
        let mut pos = 0;
        loop {
            if pos >= domains.len() {
                return None;
            }
            idx[pos] += 1;
            if idx[pos] <= domains[pos].2 {
                break;
            }
            idx[pos] = domains[pos].1;
            pos += 1;
        }
    }
}

fn eval_product(factors: &MonoKey, env: &HashMap<TermId, BigInt>) -> (BigInt, bool) {
    let mut product = BigInt::from(1);
    for &(v, p) in factors {
        let Some(val) = env.get(&v) else {
            return (BigInt::zero(), false);
        };
        let mut acc = BigInt::from(1);
        for _ in 0..p {
            acc *= val;
        }
        product *= &acc;
    }
    (product, true)
}

/// Solve the equality `lhs = rhs` for one variable under `env`, returning
/// `(var, new_value)` when the polynomial is linear in some variable `var`
/// with a nonzero (evaluated) coefficient and the solution `-rest/coeff` is an
/// integer. This is the model-repair step that collapses product equalities
/// such as `b9·a2 - a2 = 0` to `b9 = 1` once `a2` is fixed.
fn solve_eq_for_var(
    lhs: TermId,
    rhs: TermId,
    manager: &TermManager,
    env: &HashMap<TermId, BigInt>,
) -> Option<(TermId, BigInt)> {
    let mut terms: Vec<(BigInt, MonoKey)> = Vec::new();
    collect_terms(lhs, BigInt::from(1), manager, &mut terms);
    collect_terms(rhs, BigInt::from(-1), manager, &mut terms);
    // Merge like monomials.
    terms = merge_like(terms);
    // Variables appearing.
    let mut all_vars: std::collections::HashSet<TermId> = std::collections::HashSet::new();
    for (_, m) in &terms {
        for (v, _) in m {
            all_vars.insert(*v);
        }
    }
    for v in all_vars {
        // Reject if not linear in v (some term has v^≥2).
        let nonlinear = terms
            .iter()
            .any(|(_, m)| m.iter().any(|(u, p)| *u == v && *p >= 2));
        if nonlinear {
            continue;
        }
        // coeff_v = Σ (term.coeff · eval(mono without v)) over terms containing v^1
        // rest    = Σ (term.coeff · eval(mono))            over terms without v
        let mut coeff_v = BigInt::zero();
        let mut rest = BigInt::zero();
        let mut ok = true;
        for (c, m) in &terms {
            if m.iter().any(|(u, p)| *u == v && *p == 1) {
                let mut m_without: MonoKey = m.iter().filter(|(u, _)| *u != v).copied().collect();
                m_without.sort_by_key(|(t, _)| t.0);
                match eval_product(&m_without, env) {
                    (val, true) => coeff_v += c * &val,
                    _ => {
                        ok = false;
                        break;
                    }
                }
            } else {
                match eval_product(m, env) {
                    (val, true) => rest += c * &val,
                    _ => {
                        ok = false;
                        break;
                    }
                }
            }
        }
        if !ok || coeff_v.is_zero() {
            continue;
        }
        // v = -rest / coeff_v (exact integer division)
        let neg_rest = -rest;
        let q = &neg_rest / &coeff_v;
        let rem = &neg_rest - &(&q * &coeff_v);
        if rem.is_zero() {
            return Some((v, q));
        }
    }
    None
}

/// Flatten an arithmetic term into `(coefficient, monomial)` pairs with the
/// given overall sign. `Mul` of multi-term factors expands via the cartesian
/// product. Non-polynomial sub-terms are silently dropped (the caller treats a
/// missing variable solution as "no repair").
fn collect_terms(
    term: TermId,
    sign: BigInt,
    manager: &TermManager,
    out: &mut Vec<(BigInt, MonoKey)>,
) {
    let Some(n) = manager.get(term) else {
        return;
    };
    match &n.kind {
        TermKind::IntConst(k) => out.push((sign * k, Vec::new())),
        TermKind::Var(_) => out.push((sign, vec![(term, 1)])),
        TermKind::Neg(x) => collect_terms(*x, -sign, manager, out),
        TermKind::Add(args) => {
            for &a in args {
                collect_terms(a, sign.clone(), manager, out);
            }
        }
        TermKind::Sub(a, b) => {
            collect_terms(*a, sign.clone(), manager, out);
            collect_terms(*b, -sign, manager, out);
        }
        TermKind::Mul(args) => {
            // Start with the single constant term 1, then multiply in each factor.
            let mut acc: Vec<(BigInt, MonoKey)> = vec![(sign, Vec::new())];
            for &a in args {
                let mut factor_terms: Vec<(BigInt, MonoKey)> = Vec::new();
                collect_terms(a, BigInt::from(1), manager, &mut factor_terms);
                if factor_terms.is_empty() {
                    return; // non-polynomial factor → drop
                }
                let mut next: Vec<(BigInt, MonoKey)> = Vec::new();
                for (c1, m1) in &acc {
                    for (c2, m2) in &factor_terms {
                        let mut m: MonoKey = m1.iter().chain(m2.iter()).copied().collect();
                        // combine powers of the same variable
                        m.sort_by_key(|(t, _)| t.0);
                        let mut merged: MonoKey = Vec::new();
                        for (t, p) in m {
                            if let Some(last) = merged.last_mut()
                                && last.0 == t
                            {
                                last.1 += p;
                                continue;
                            }
                            merged.push((t, p));
                        }
                        next.push((c1 * c2, merged));
                    }
                }
                acc = next;
            }
            out.extend(acc);
        }
        _ => {}
    }
}

fn merge_like(terms: Vec<(BigInt, MonoKey)>) -> Vec<(BigInt, MonoKey)> {
    let mut map: std::collections::BTreeMap<MonoKey, BigInt> = std::collections::BTreeMap::new();
    for (c, mut m) in terms {
        m.sort_by_key(|(t, _)| t.0);
        *map.entry(m).or_insert_with(BigInt::zero) += c;
    }
    map.into_iter()
        .map(|(m, c)| (c, m))
        .filter(|(c, _)| !c.is_zero())
        .collect()
}

fn big_to_r64(b: &BigInt) -> Option<Rational64> {
    Some(Rational64::from_integer(b.to_i64()?))
}

fn r64_to_big(r: Rational64) -> BigInt {
    BigInt::from(*r.numer())
}

// Re-exports used by the public signature live in crate::nlsat; nothing else
// needs to leave this module.
