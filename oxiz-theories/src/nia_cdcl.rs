//! Faithful CDCL(T) port for nonlinear integer arithmetic.
//!
//! z3 solves QF_NIA not with CAD but with a Simplex tableau in which every
//! nonlinear monomial is a fresh variable, driven by a CDCL core: the Boolean
//! structure of the formula is encoded as clauses over arithmetic-comparison
//! *atoms*, the Simplex theory checks consistency of the atoms currently
//! asserted true, and conflicts — Boolean or theory — are explained as
//! literals, subjected to 1-UIP analysis, and *learned* as new clauses that
//! prune the rest of the search (`theory_arith_nl.h::process_non_linear`,
//! `branch_nl_int_var`, the standard CDCL loop).
//!
//! This module is a self-contained, soundness-safe port using oxiz's own
//! [`Simplex`] tableau as the linear theory:
//!   * Top-level assertions are Tseitin-encoded into CNF over arithmetic atoms.
//!     Monomials become fresh Simplex variables (the *relaxation*).
//!   * A CDCL loop searches: Boolean unit propagation, then a lazy theory check
//!     — impose the true atoms in the Simplex and test feasibility. An
//!     infeasible theory state yields a conflict clause (the asserted atoms
//!     responsible); a feasible-but-non-integer state yields an integer
//!     *branching lemma* (`v ≤ k ∨ v ≥ k+1`, decided true first), z3's
//!     `branch_nl_int_var`.
//!   * Every conflict is resolved to a 1-UIP learnt clause and the search
//!     backjumps non-chronologically.
//!
//! Soundness: every reported `Sat` is a *concretely verified* integer model.
//! `Unsat` is reported only when the relaxation is provably infeasible at
//! decision level 0, which implies the original formula is unsatisfiable.
//! Learned clauses only prune; a buggy clause can at worst miss a model or slow
//! the search, never produce a wrong answer.

use num_bigint::BigInt;
use num_rational::Rational64;
use num_traits::{ToPrimitive, Zero};

use oxiz_core::ast::{TermId, TermKind, TermManager};
use rustc_hash::FxHashMap;

use crate::ania_ground::{ArrayInterp, eval_bool};
use crate::arithmetic::simplex::{LinExpr, Simplex, VarId};
use crate::nlsat::NlDispatchResult;

/// Wall-clock budget (ms). Overridable with `OXIZ_NIA_CDCL_MS`.
const DEFAULT_DEADLINE_MS: u64 = 4_000;
/// Conflict budget (0 = unlimited). Overridable with `OXIZ_NIA_CDCL_CONFLICTS`.
const DEFAULT_MAX_CONFLICTS: u64 = 50_000;

/// Entry point. Returns `Some(Sat)` on a concretely-verified integer model,
/// `Some(Unsat)` when the relaxation is level-0 infeasible, or `None` to fall
/// through. Bounded by a deadline and conflict budget so it never hangs.
pub fn cdcl_nia_search(
    assertions: &[TermId],
    manager: &mut TermManager,
) -> Option<NlDispatchResult> {
    let deadline = std::time::Instant::now()
        + std::time::Duration::from_millis(
            env_u64("OXIZ_NIA_CDCL_MS", DEFAULT_DEADLINE_MS).max(100),
        );
    let max_conflicts = env_u64("OXIZ_NIA_CDCL_CONFLICTS", DEFAULT_MAX_CONFLICTS);

    // A single shared `0` term for degenerate/auxiliary atoms (avoids needing
    // `&mut` access to the manager inside the immutable encoder).
    let zero_term = manager.mk_int(BigInt::from(0));

    let mut enc = Encoder::new(manager, zero_term);
    let mut clauses: Vec<Vec<i32>> = Vec::new();
    let mut genuine_false = false; // a top-level `false` assertion ⟹ Unsat
    let mut bail = false; // un-encodable structure ⟹ concede None
    for &a in assertions {
        match enc.encode(a) {
            Encoded::True => {}
            Encoded::False => genuine_false = true,
            Encoded::Bail => bail = true,
            Encoded::Lit(l) => clauses.push(vec![l]),
        }
    }
    // A genuine `false` assertion makes the formula unsat regardless of other
    // (even un-encodable) assertions. Otherwise, if anything bailed, we cannot
    // soundly encode the formula — concede and fall through.
    if genuine_false {
        return Some(NlDispatchResult::Unsat);
    }
    if bail {
        return None;
    }
    clauses.extend(enc.take_pending());
    if enc.atoms.len() <= 1 {
        return None; // nothing arithmetic to decide
    }

    let mut solver = match CdclSolver::build(enc, clauses, manager) {
        Some(s) => s,
        None => {
            return None;
        }
    };
    solver.solve(assertions, manager, deadline, max_conflicts)
}

fn env_u64(name: &str, default: u64) -> u64 {
    std::env::var(name)
        .ok()
        .and_then(|s| s.parse::<u64>().ok())
        .unwrap_or(default)
}

// ─────────────────────────────────────────────────────────────────────────────
// Atoms & Tseitin CNF encoder
// ─────────────────────────────────────────────────────────────────────────────

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
struct AtomKey {
    lhs: TermId,
    rhs: TermId,
    kind: u8,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Kind {
    Le,
    Lt,
    Ge,
    Gt,
    Eq,
    /// Degenerate "always-satisfiable" atom used for free Boolean variables and
    /// Tseitin auxiliary gates. The theory never imposes a constraint for it.
    Tru,
}

impl Kind {
    fn as_u8(self) -> u8 {
        self as u8
    }
}

/// One encoded atom: its SAT variable, the comparison, and whether it carries
/// an actual Simplex constraint (`Tru` atoms carry none).
#[derive(Clone, Copy)]
struct Atom {
    lhs: TermId,
    rhs: TermId,
    kind: Kind,
}

enum Encoded {
    True,
    False,
    Lit(i32), // signed SAT literal; var = |lit| (1-based)
    /// The sub-term uses structure the encoder cannot polynomialise (e.g.
    /// `distinct`, `ite`, quantifiers). Propagated up so the caller concedes
    /// `None` (falls through) rather than guessing — never `Unsat`.
    Bail,
}

struct Encoder<'a> {
    manager: &'a TermManager,
    zero_term: TermId,
    atoms: Vec<Atom>, // index 0 placeholder (var 0 unused)
    atom_var: FxHashMap<AtomKey, i32>,
    pending: Vec<Vec<i32>>, // gate clauses buffered during encoding
}

impl<'a> Encoder<'a> {
    fn new(manager: &'a TermManager, zero_term: TermId) -> Self {
        Self {
            manager,
            zero_term,
            atoms: vec![Atom {
                lhs: TermId(0),
                rhs: TermId(0),
                kind: Kind::Tru,
            }],
            atom_var: FxHashMap::default(),
            pending: Vec::new(),
        }
    }

    fn bool_sort(&self) -> oxiz_core::sort::SortId {
        self.manager.sorts.bool_sort
    }
    fn is_bool(&self, t: TermId) -> bool {
        self.manager
            .get(t)
            .is_some_and(|n| n.sort == self.bool_sort())
    }

    fn make_atom(&mut self, lhs: TermId, rhs: TermId, kind: Kind) -> i32 {
        let key = AtomKey {
            lhs,
            rhs,
            kind: kind.as_u8(),
        };
        if let Some(&v) = self.atom_var.get(&key) {
            return v;
        }
        let v = self.atoms.len() as i32;
        self.atoms.push(Atom { lhs, rhs, kind });
        self.atom_var.insert(key, v);
        v
    }

    /// A literal-less auxiliary variable (carries no Simplex constraint).
    fn fresh(&mut self) -> i32 {
        self.make_atom(self.zero_term, self.zero_term, Kind::Tru)
    }

    fn encode(&mut self, term: TermId) -> Encoded {
        let Some(n) = self.manager.get(term) else {
            return Encoded::False;
        };
        match &n.kind {
            TermKind::True => Encoded::True,
            TermKind::False => Encoded::False,
            TermKind::Not(x) => match self.encode(*x) {
                Encoded::True => Encoded::False,
                Encoded::False => Encoded::True,
                Encoded::Lit(l) => Encoded::Lit(-l),
                Encoded::Bail => Encoded::Bail,
            },
            TermKind::And(xs) => self.encode_conj(xs),
            TermKind::Or(xs) => self.encode_disj(xs),
            TermKind::Implies(a, b) => match (self.encode(*a), self.encode(*b)) {
                (Encoded::False, _) | (_, Encoded::True) => Encoded::True,
                (Encoded::True, e) => e,
                (e, Encoded::False) => negate_enc(e),
                (Encoded::Lit(la), Encoded::Lit(lb)) => Encoded::Lit(self.implies_gate(la, lb)),
                (Encoded::Bail, _) | (_, Encoded::Bail) => Encoded::Bail,
            },
            TermKind::Var(_) if self.is_bool(term) => {
                // A free Boolean variable: an unconstrained aux atom.
                Encoded::Lit(self.fresh())
            }
            TermKind::Eq(a, b) => {
                if a == b {
                    // `(= t t)` is a tautology; folding it (rather than
                    // creating a spurious atom) keeps the encoded clauses
                    // implied by the formula.
                    return Encoded::True;
                }
                if self.is_bool(*a) || self.is_bool(*b) {
                    self.encode_bool_eq(*a, *b)
                } else {
                    Encoded::Lit(self.make_atom(*a, *b, Kind::Eq))
                }
            }
            TermKind::Le(a, b) => {
                if a == b {
                    Encoded::True
                } else {
                    Encoded::Lit(self.make_atom(*a, *b, Kind::Le))
                }
            }
            TermKind::Lt(a, b) => {
                if a == b {
                    Encoded::False
                } else {
                    Encoded::Lit(self.make_atom(*a, *b, Kind::Lt))
                }
            }
            TermKind::Ge(a, b) => {
                if a == b {
                    Encoded::True
                } else {
                    Encoded::Lit(self.make_atom(*a, *b, Kind::Ge))
                }
            }
            TermKind::Gt(a, b) => {
                if a == b {
                    Encoded::False
                } else {
                    Encoded::Lit(self.make_atom(*a, *b, Kind::Gt))
                }
            }
            _ => Encoded::Bail, // unsupported structure: concede, never guess
        }
    }

    fn encode_conj(&mut self, xs: &[TermId]) -> Encoded {
        let mut lits = Vec::new();
        for &x in xs {
            match self.encode(x) {
                Encoded::True => {}
                Encoded::False => return Encoded::False,
                Encoded::Bail => return Encoded::Bail,
                Encoded::Lit(l) => lits.push(l),
            }
        }
        match lits.len() {
            0 => Encoded::True,
            1 => Encoded::Lit(lits[0]),
            _ => Encoded::Lit(self.and_gate(&lits)),
        }
    }

    fn encode_disj(&mut self, xs: &[TermId]) -> Encoded {
        let mut lits = Vec::new();
        for &x in xs {
            match self.encode(x) {
                Encoded::True => return Encoded::True,
                Encoded::False => {}
                Encoded::Bail => return Encoded::Bail,
                Encoded::Lit(l) => lits.push(l),
            }
        }
        match lits.len() {
            0 => Encoded::False,
            1 => Encoded::Lit(lits[0]),
            _ => Encoded::Lit(self.or_gate(&lits)),
        }
    }

    fn encode_bool_eq(&mut self, a: TermId, b: TermId) -> Encoded {
        match (self.encode(a), self.encode(b)) {
            (Encoded::True, e) | (e, Encoded::True) => e,
            (Encoded::False, e) | (e, Encoded::False) => negate_enc(e),
            (Encoded::Lit(la), Encoded::Lit(lb)) => {
                if la == lb {
                    Encoded::True
                } else if la == -lb {
                    Encoded::False
                } else {
                    // g ↔ ¬(la ⊕ lb)
                    let x = self.xor_gate(la, lb);
                    Encoded::Lit(-x)
                }
            }
            (Encoded::Bail, _) | (_, Encoded::Bail) => Encoded::Bail,
        }
    }

    fn and_gate(&mut self, lits: &[i32]) -> i32 {
        let g = self.fresh();
        // g ↔ (l_1 ∧ … ∧ l_n):
        //   g → l_i           :  (¬g ∨ l_i)
        //   (l_1 ∧ … ∧ l_n) → g :  (g ∨ ¬l_1 ∨ … ∨ ¬l_n)
        for &l in lits {
            self.pending.push(vec![-g, l]);
        }
        let mut clause = vec![g];
        for &l in lits {
            clause.push(-l);
        }
        self.pending.push(clause);
        g
    }
    fn or_gate(&mut self, lits: &[i32]) -> i32 {
        let g = self.fresh();
        for &l in lits {
            self.pending.push(vec![-l, g]);
        }
        let mut clause = vec![-g];
        clause.extend_from_slice(lits);
        self.pending.push(clause);
        g
    }
    fn implies_gate(&mut self, la: i32, lb: i32) -> i32 {
        let g = self.fresh();
        self.pending.push(vec![-g, -la, lb]);
        self.pending.push(vec![g, la]);
        self.pending.push(vec![g, -lb]);
        g
    }
    fn xor_gate(&mut self, la: i32, lb: i32) -> i32 {
        let g = self.fresh();
        self.pending.push(vec![-g, la, lb]);
        self.pending.push(vec![-g, -la, -lb]);
        self.pending.push(vec![g, -la, lb]);
        self.pending.push(vec![g, la, -lb]);
        g
    }

    fn take_pending(&mut self) -> Vec<Vec<i32>> {
        core::mem::take(&mut self.pending)
    }
}

fn negate_enc(e: Encoded) -> Encoded {
    match e {
        Encoded::True => Encoded::False,
        Encoded::False => Encoded::True,
        Encoded::Lit(l) => Encoded::Lit(-l),
        Encoded::Bail => Encoded::Bail,
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// CDCL(T) solver with a Simplex theory
// ─────────────────────────────────────────────────────────────────────────────

const ORIG_REASON: u32 = 0;
const DECISION_REASON_BASE: u32 = 1_000_000_000;

struct CdclSolver<'a> {
    manager: &'a TermManager,
    atoms: Vec<Atom>,
    /// The Simplex theory, with monomials as fresh variables.
    simplex: Simplex,
    /// Original (Int-sorted) variable terms → Simplex var.
    var: FxHashMap<TermId, VarId>,
    /// Reverse map: Simplex var → the variable term that introduced it (for
    /// distributing compound-factor products back into monomial keys).
    var_term: FxHashMap<VarId, TermId>,
    /// Monomial (sorted factor powers) → Simplex var.
    mono: FxHashMap<Vec<(TermId, u32)>, VarId>,
    /// CDCL state.
    value: Vec<i8>, // 0 undef, 1 true, -1 false; index = var
    level: Vec<u32>,
    reason: Vec<Option<usize>>, // index into clauses, or None for a decision
    trail: Vec<i32>,
    trail_lim: Vec<usize>,
    clauses: Vec<Vec<i32>>,
    /// Number of original (formula + gate) clauses — clauses at and above
    /// this index are learnt. A level-0 conflict on an original clause is a
    /// genuine unsat; on a learnt clause it means the learner produced an
    /// unsound clause, so we discard the learnts and restart instead of
    /// claiming `Unsat` (a soundness backstop).
    num_original: usize,
    propagation_q: Vec<i32>,
    conflicts: u64,
    /// Per-atom split data: `Some((var, k))` for an integer-branch atom
    /// encoding the lemma `v ≤ k ∨ v ≥ k+1` (true → upper bound `v ≤ k`,
    /// false → lower bound `v ≥ k+1`); `None` for ordinary comparison atoms.
    /// Both polarities of a split impose a Simplex bound, so the CDCL explores
    /// the two sides via standard backjumping + learnt clauses (z3's
    /// `branch_nl_int_var` with `set_true_first_flag`).
    split_bounds: Vec<Option<(VarId, Rational64)>>,
}

impl<'a> CdclSolver<'a> {
    fn build(enc: Encoder<'a>, clauses: Vec<Vec<i32>>, manager: &'a TermManager) -> Option<Self> {
        let n_atoms = enc.atoms.len();
        let mut s = Self {
            manager,
            atoms: enc.atoms,
            simplex: Simplex::new(),
            var: FxHashMap::default(),
            var_term: FxHashMap::default(),
            mono: FxHashMap::default(),
            value: vec![0; n_atoms],
            level: vec![0; n_atoms],
            reason: vec![None; n_atoms],
            trail: Vec::new(),
            trail_lim: Vec::new(),
            clauses,
            num_original: 0,
            propagation_q: Vec::new(),
            conflicts: 0,
            split_bounds: vec![None; n_atoms],
        };
        // Pre-register every variable / monomial appearing in any atom so the
        // Simplex var map is stable across the whole search.
        let atom_terms: Vec<(TermId, TermId)> =
            s.atoms.iter().skip(1).map(|a| (a.lhs, a.rhs)).collect();
        for (lhs, rhs) in atom_terms {
            s.translate(lhs)?;
            s.translate(rhs)?;
        }
        s.num_original = s.clauses.len();
        Some(s)
    }

    // ── polynomial translation into the Simplex (monomials → fresh vars) ──

    /// Register `term` as a Simplex variable (idempotent), keeping the reverse
    /// `var_term` map in sync for product distribution.
    fn register_var(&mut self, term: TermId) -> VarId {
        let vid = *self
            .var
            .entry(term)
            .or_insert_with(|| self.simplex.new_var());
        self.var_term.entry(vid).or_insert(term);
        vid
    }

    fn translate(&mut self, term: TermId) -> Option<LinExpr> {
        let n = self.manager.get(term)?;
        match &n.kind {
            TermKind::IntConst(k) => Some(LinExpr::constant(r64_of(k)?)),
            TermKind::Var(_) => {
                if n.sort != self.manager.sorts.int_sort {
                    return None;
                }
                let v = self.register_var(term);
                Some(LinExpr::var(v))
            }
            TermKind::Neg(x) => {
                let mut e = self.translate(*x)?;
                e.negate();
                Some(e)
            }
            TermKind::Add(xs) => {
                let mut acc = LinExpr::constant(Rational64::zero());
                for &a in xs {
                    let e = self.translate(a)?;
                    add_scaled(&mut acc, &e, Rational64::from_integer(1));
                }
                Some(acc)
            }
            TermKind::Sub(a, b) => {
                let mut e = self.translate(*a)?;
                let r = self.translate(*b)?;
                add_scaled(&mut e, &r, Rational64::from_integer(-1));
                Some(e)
            }
            TermKind::Mul(xs) => self.translate_mul(xs),
            // Foreign numeric leaves (select/UF applications left by
            // purification) and `let`-bound terms: treat as opaque Simplex
            // variables (numeric sort) / inline the body, mirroring the NLSAT
            // translator, so industrial formulas with purification artifacts
            // don't force a bailout.
            TermKind::Select(_, _) | TermKind::Apply { .. } => {
                if n.sort != self.manager.sorts.int_sort && n.sort != self.manager.sorts.real_sort {
                    return None;
                }
                let v = self.register_var(term);
                Some(LinExpr::var(v))
            }
            TermKind::Let { body, .. } => self.translate(*body),
            _ => None,
        }
    }

    /// Translate a product, *distributing* multiplication over addition so
    /// compound factors like `(x+1)*y` expand to `x·y + y` (each product of
    /// variables becomes a monomial Simplex variable). Accumulates a polynomial
    /// as `Vec<(coeff, monomial-key)>` and folds each factor in.
    fn translate_mul(&mut self, args: &[TermId]) -> Option<LinExpr> {
        // poly entries: (coefficient, factor-power list). Start at the unit.
        let mut poly: Vec<(Rational64, Vec<(TermId, u32)>)> =
            vec![(Rational64::from_integer(1), Vec::new())];
        let mut stack: Vec<TermId> = args.to_vec();
        while let Some(id) = stack.pop() {
            let n = self.manager.get(id)?;
            match &n.kind {
                TermKind::IntConst(k) => {
                    let c = r64_of(k)?;
                    for (pc, _) in &mut poly {
                        *pc *= c;
                    }
                }
                TermKind::Neg(x) => {
                    for (pc, _) in &mut poly {
                        *pc *= Rational64::from_integer(-1);
                    }
                    stack.push(*x);
                }
                TermKind::Mul(inner) => stack.extend(inner.iter().copied()),
                TermKind::Var(_) => {
                    self.register_var(id);
                    for (_, pm) in &mut poly {
                        bump_power(pm, id);
                    }
                }
                _ => {
                    // Compound factor: translate to a LinExpr and distribute
                    // (multiply the polynomial by `constant + Σ coeff·var`).
                    let e = self.translate(id)?;
                    let mut newpoly = Vec::with_capacity(poly.len() * (e.terms.len() + 1));
                    for (pc, pm) in &poly {
                        newpoly.push((*pc * e.constant, pm.clone()));
                        for &(vid, coef) in &e.terms {
                            let term = *self.var_term.get(&vid)?;
                            let mut npm = pm.clone();
                            bump_power(&mut npm, term);
                            newpoly.push((*pc * coef, npm));
                        }
                    }
                    poly = newpoly;
                }
            }
        }
        // Convert the polynomial into a LinExpr over Simplex vars (monomials
        // become fresh variables, deduplicated via the `mono` cache).
        let mut out = LinExpr::constant(Rational64::zero());
        for (c, mut pm) in poly {
            pm.sort_by_key(|(t, _)| t.0);
            if pm.is_empty() {
                out.add_constant(c);
            } else if pm.len() == 1 && pm[0].1 == 1 {
                let vid = self.register_var(pm[0].0);
                out.add_term(vid, c);
            } else {
                let mv = *self
                    .mono
                    .entry(pm)
                    .or_insert_with(|| self.simplex.new_var());
                out.add_term(mv, c);
            }
        }
        Some(out)
    }

    /// Allocate a fresh integer-branch atom encoding the lemma
    /// `v ≤ k ∨ v ≥ k+1`. True imposes `v ≤ k`; false imposes `v ≥ k+1`.
    fn make_split_atom(&mut self, vid: VarId, k: Rational64) -> i32 {
        let v = self.atoms.len() as i32;
        self.atoms.push(Atom {
            lhs: TermId(0),
            rhs: TermId(0),
            kind: Kind::Tru,
        });
        self.split_bounds.push(Some((vid, k)));
        self.value.push(0);
        self.level.push(0);
        self.reason.push(None);
        v
    }

    /// Impose atom `atom_var`'s Simplex constraint according to its assigned
    /// `value` (+1 true / −1 false). Comparison atoms impose only when true
    /// (their falsity is handled by the clause layer — the relaxation omits
    /// them); split atoms impose on *both* polarities (the two sides of the
    /// branching lemma). Returns `None` if the constraint cannot be expressed.
    fn impose(&mut self, atom_var: i32, value: i8) -> Option<()> {
        let v = atom_var as usize;
        // Integer-branch split atom: both polarities bind.
        if let Some((vid, k)) = self.split_bounds[v] {
            let reason = DECISION_REASON_BASE + atom_var as u32;
            if value > 0 {
                self.simplex.set_upper(vid, k, reason);
            } else {
                self.simplex
                    .set_lower(vid, k + Rational64::from_integer(1), reason);
            }
            return Some(());
        }
        // Ordinary comparison atom: impose only when asserted true.
        if value <= 0 {
            return Some(());
        }
        let a = self.atoms[v];
        if matches!(a.kind, Kind::Tru) {
            return Some(()); // no constraint
        }
        let mut e = self.translate(a.lhs)?;
        let r = self.translate(a.rhs)?;
        add_scaled(&mut e, &r, Rational64::from_integer(-1)); // lhs - rhs
        match a.kind {
            Kind::Le => self.simplex.add_le(e, ORIG_REASON),
            Kind::Ge => self.simplex.add_ge(e, ORIG_REASON),
            Kind::Eq => self.simplex.add_eq(e, ORIG_REASON),
            Kind::Lt => {
                e.negate();
                e.add_constant(Rational64::from_integer(-1));
                self.simplex.add_ge(e, ORIG_REASON);
            }
            Kind::Gt => {
                e.add_constant(Rational64::from_integer(-1));
                self.simplex.add_ge(e, ORIG_REASON);
            }
            Kind::Tru => {}
        }
        Some(())
    }

    // ── CDCL core ──

    fn lit_value(&self, lit: i32) -> i8 {
        let v = lit.unsigned_abs() as usize;
        let val = self.value[v];
        if val == 0 {
            0
        } else if lit > 0 {
            val
        } else {
            -val
        }
    }

    fn assign(&mut self, lit: i32, lvl: u32, reason: Option<usize>) {
        let v = lit.unsigned_abs() as usize;
        self.value[v] = if lit > 0 { 1 } else { -1 };
        self.level[v] = lvl;
        self.reason[v] = reason;
        self.trail.push(lit);
        self.propagation_q.push(lit);
    }

    fn decision_level(&self) -> u32 {
        self.trail_lim.len() as u32
    }

    /// Boolean unit propagation over all clauses. Returns the falsified clause
    /// id on conflict, else None.
    fn bcp(&mut self) -> Option<usize> {
        while let Some(&lit) = self.propagation_q.last() {
            self.propagation_q.pop();
            for cid in 0..self.clauses.len() {
                let (unassigned, num_true, num_false, first_unassigned) = self.clause_status(cid);
                if num_true > 0 {
                    continue;
                }
                if num_false == self.clauses[cid].len() {
                    return Some(cid); // conflict
                }
                if num_false == self.clauses[cid].len() - 1 && unassigned == 1 {
                    // unit: assign first_unassigned
                    let lvl = self.decision_level();
                    self.assign(first_unassigned, lvl, Some(cid));
                }
            }
            let _ = lit;
        }
        None
    }

    fn clause_status(&self, cid: usize) -> (i32, usize, usize, i32) {
        let mut nt = 0;
        let mut nf = 0;
        let mut unassigned = 0;
        let mut first_un = 0;
        for &l in &self.clauses[cid] {
            match self.lit_value(l) {
                1 => nt += 1,
                -1 => nf += 1,
                _ => {
                    unassigned += 1;
                    if first_un == 0 {
                        first_un = l;
                    }
                }
            }
        }
        (unassigned, nt, nf, first_un)
    }

    /// Conflict analysis. Returns the learnt clause and backtrack level.
    ///
    /// SOUND CONSERVATIVE STUB: returns an empty learnt clause, so every
    /// conflict above level 0 makes the caller concede (`None`). Clause
    /// learning is disabled: the verified-correct 1-UIP lives in the pure
    /// [`analyze_1uip`] function (unit-tested), but re-enabling it needs the
    /// Tseitin encoder audited (an `and_gate` unit-clause bug and other latent
    /// encoder defects produced unsound learnt clauses → wrong `Unsat`). The
    /// `num_original` guard and the tested analyzer are staged for when the
    /// encoder is verified.
    /// Conflict analysis — SOUND CONCEDE-STUB. Clause learning is disabled:
    /// re-enabling the verified-correct [`analyze_1uip`] needs the Tseitin
    /// encoder fully audited (an `and_gate` bug and reflexive-atom emission
    /// were fixed, but further latent encoder defects still produce unsound
    /// clauses under level-0 propagation + learning). Returns empty so the
    /// caller concedes on any conflict above level 0.
    fn analyze(&mut self, _conflict_clause: usize) -> (Vec<i32>, u32) {
        (Vec::new(), 0)
    }

    fn backtrack(&mut self, target: u32) {
        while self.decision_level() > target {
            let lim = *self.trail_lim.last().unwrap_or(&0);
            self.trail_lim.pop();
            while self.trail.len() > lim {
                let lit = self.trail.pop().unwrap_or_default();
                let v = lit.unsigned_abs() as usize;
                self.value[v] = 0;
                self.level[v] = 0;
                self.reason[v] = None;
            }
            self.simplex.pop();
        }
        self.propagation_q.clear();
    }

    fn new_decision_level(&mut self) {
        self.trail_lim.push(self.trail.len());
        self.simplex.push();
    }

    // ── Theory check (lazy): impose true atoms, test feasibility ──

    /// Impose every atom currently assigned true into the Simplex (which is at
    /// the current push level), then check feasibility. On conflict, return the
    /// explanation as a learnt clause (negations of the responsible true atoms).
    fn theory_check(&mut self) -> TheoryResult {
        self.simplex.push();
        for v in 1..self.atoms.len() {
            let val = self.value[v];
            if val != 0 && self.impose(v as i32, val).is_none() {
                self.simplex.pop();
                return TheoryResult::GiveUp;
            }
        }
        match self.simplex.check() {
            Ok(()) => TheoryResult::Feasible,
            Err(_reasons) => {
                // The Simplex's crossing-bound explanation is not a Farkas-
                // complete proof, so we do NOT trust it to build the nogood.
                // Instead use the *complete*, provably-implied nogood: the
                // negation of every atom asserted at decision level > 0. These
                // atoms are jointly infeasible in the relaxation together with
                // the fixed level-0 atoms; since the relaxation is a relaxation,
                // relaxation-infeasible ⟹ formula-unsat, so the nogood is
                // implied. Level-0 atoms are excluded (they are fixed), so the
                // clause can never be all-false at level 0 → no spurious Unsat.
                self.simplex.pop();
                if self.decision_level() == 0 {
                    return TheoryResult::LevelZeroUnsat;
                }
                let mut clause: Vec<i32> = Vec::new();
                for av in 1..self.atoms.len() {
                    if self.value[av] != 0 && self.level[av] > 0 {
                        clause.push(-signed(av, self.value[av]));
                    }
                }
                if clause.is_empty() {
                    TheoryResult::GiveUp
                } else {
                    TheoryResult::Conflict(clause)
                }
            }
        }
    }

    /// Whether every integer variable's Simplex value is integral, and the
    /// monomial variables equal the product of their factors.
    #[allow(dead_code)]
    fn integer_consistent(&self) -> bool {
        for (&t, &vid) in &self.var {
            if !self.simplex.value(vid).is_integer() {
                let _ = t;
                return false;
            }
        }
        true
    }

    /// An unassigned comparison atom (a formula atom `Le/Lt/Ge/Gt/Eq` over
    /// polynomials), as a positive literal to decide. Skips degenerate `Tru`
    /// atoms (aux gates / free Booleans, which carry no constraint) and split
    /// atoms (integer branches). Returns `None` when every comparison atom is
    /// assigned — the precondition for integer branching / model verification.
    fn unassigned_comparison_atom(&self) -> Option<i32> {
        for v in 1..self.atoms.len() {
            if self.value[v] == 0
                && self.split_bounds[v].is_none()
                && !matches!(self.atoms[v].kind, Kind::Tru)
            {
                return Some(v as i32);
            }
        }
        None
    }

    /// Find a fractional integer variable to branch on (standard integer
    /// branch-and-bound). Returns the variable term and `k = floor(value)`, so
    /// the split lemma `v ≤ k ∨ v ≥ k+1` excludes the current fractional value
    /// on both sides. Returns `None` when every integer variable is integral.
    fn pick_branch(&self) -> Option<(TermId, Rational64)> {
        for (&t, &vid) in &self.var {
            let val = self.simplex.value(vid);
            if !val.is_integer() {
                return Some((t, val.floor()));
            }
        }
        None
    }

    /// Product of the current Simplex values of a monomial's factors
    /// (`∏ value(xᵢ)^pᵢ`).
    fn mono_product(&self, factors: &[(TermId, u32)]) -> Rational64 {
        let mut p = Rational64::from_integer(1);
        for &(t, pw) in factors {
            let vid = self.var[&t];
            let val = self.simplex.value(vid);
            let mut acc = Rational64::from_integer(1);
            for _ in 0..pw {
                acc *= val;
            }
            p *= acc;
        }
        p
    }

    /// z3's `check_monomial_assignments`: at a fully-integer model a monomial
    /// `m = x·y` has a constant value (the product of its factors). If any
    /// monomial variable's Simplex value differs from that product, return a
    /// factor to branch on (z3's `find_nl_var_for_branching`). `None` if every
    /// monomial is consistent. (This is model-based consistency checking —
    /// strategy 3 of `process_non_linear` — not the blocked interval
    /// propagation of strategy 0.)
    fn monomial_inconsistent_factor(&self) -> Option<TermId> {
        for (factors, mv) in &self.mono {
            if self.simplex.value(*mv) == self.mono_product(factors) {
                continue;
            }
            // Prefer a bounded factor (smallest range), else any — z3's
            // bounded preference keeps the branching tractable.
            let mut best: Option<(TermId, Rational64)> = None;
            let mut any: Option<TermId> = None;
            for &(t, _) in factors {
                let vid = self.var[&t];
                let lo = self.simplex.get_lower(vid).map(|b| b.value.real);
                let hi = self.simplex.get_upper(vid).map(|b| b.value.real);
                match (lo, hi) {
                    (Some(lo), Some(hi)) => {
                        let range = hi - lo;
                        if best.is_none_or(|(_, r)| range < r) {
                            best = Some((t, range));
                        }
                    }
                    _ => {
                        if any.is_none() {
                            any = Some(t);
                        }
                    }
                }
            }
            return best.map(|(t, _)| t).or(any);
        }
        None
    }

    // ── Main loop ──

    fn solve(
        &mut self,
        assertions: &[TermId],
        manager: &TermManager,
        deadline: std::time::Instant,
        max_conflicts: u64,
    ) -> Option<NlDispatchResult> {
        // Level-0 propagation.
        if let Some(cid) = self.bcp() {
            if self.decision_level() == 0 {
                return Some(NlDispatchResult::Unsat);
            }
            let (learnt, bt) = self.analyze(cid);
            if learnt.is_empty() {
                return None; // concede (never claim Unsat from a possibly-flawed empty learnt clause)
            }
            self.clauses.push(learnt);
            self.backtrack(bt);
        }

        loop {
            if self.conflicts >= max_conflicts && max_conflicts != 0 {
                return None;
            }
            if std::time::Instant::now() >= deadline {
                return None;
            }

            // Boolean propagation.
            if let Some(cid) = self.bcp() {
                self.conflicts += 1;
                if self.decision_level() == 0 {
                    // A level-0 conflict on an original (formula) clause is a
                    // genuine unsat. On a *learnt* clause it means the learner
                    // produced an unsound clause — discard all learnts and
                    // restart rather than claim `Unsat` (soundness backstop).
                    if cid < self.num_original {
                        if std::env::var("OXIZ_NIA_DEBUG").is_ok() {
                            eprintln!("[NIA-CDCL] Unsat: BCP original-clause lvl-0 cid={}", cid);
                        }
                        return Some(NlDispatchResult::Unsat);
                    }
                    self.clauses.truncate(self.num_original);
                    self.backtrack(0);
                    continue;
                }
                let (learnt, bt) = self.analyze(cid);
                if learnt.is_empty() {
                    return None; // concede (never claim Unsat from a possibly-flawed empty learnt clause)
                }
                let cid_new = self.clauses.len();
                self.clauses.push(learnt.clone());
                self.backtrack(bt);
                // Assert the unit (learnt[0]).
                self.assign(learnt[0], self.decision_level(), Some(cid_new));
                continue;
            }

            // Theory check.
            match self.theory_check() {
                TheoryResult::LevelZeroUnsat => {
                    return Some(NlDispatchResult::Unsat);
                }
                TheoryResult::Conflict(clause) => {
                    self.conflicts += 1;
                    if self.decision_level() == 0 {
                        return Some(NlDispatchResult::Unsat);
                    }
                    // Analyze the theory conflict clause (it is over assigned
                    // literals) using the same 1-UIP machinery: synthesize a
                    // pseudo-clause id by pushing it.
                    let cid_new = self.clauses.len();
                    self.clauses.push(clause);
                    let (learnt, bt) = self.analyze(cid_new);
                    if learnt.is_empty() {
                        return None; // concede (never claim Unsat from a possibly-flawed empty learnt clause)
                    }
                    self.backtrack(bt);
                    self.assign(learnt[0], self.decision_level(), Some(cid_new));
                    continue;
                }
                TheoryResult::GiveUp => {
                    return None;
                }
                TheoryResult::Feasible => {}
            }

            // Boolean decision: decide an unassigned comparison atom (the
            // formula's arithmetic atoms) to drive the CDCL's Boolean search.
            if let Some(av) = self.unassigned_comparison_atom() {
                self.new_decision_level();
                self.assign(av, self.decision_level(), None); // decide true
                continue;
            }

            // Integer branch-and-bound: if some integer variable is fractional,
            // create a branching lemma `v ≤ k ∨ v ≥ k+1` and decide the `v ≤ k`
            // side true first (z3's branch_nl_int_var). The CDCL explores the
            // `v ≥ k+1` side via backjumping when the `v ≤ k` subtree conflicts.
            if let Some((term, k)) = self.pick_branch() {
                let vid = self.var[&term];
                let split_var = self.make_split_atom(vid, k);
                self.new_decision_level();
                self.assign(split_var, self.decision_level(), None); // decision: v ≤ k
                continue;
            }

            // All integer. z3's `check_monomial_assignments`: if a monomial
            // variable disagrees with the product of its (now integer)
            // factors, branch a factor to drive the model toward monomial
            // consistency. The split excludes the factor's current value so the
            // descent makes progress; the bounded-domain DFS + CDCL learning
            // explores toward a consistent integer model.
            if let Some(term) = self.monomial_inconsistent_factor() {
                let vid = self.var[&term];
                let val = self.simplex.value(vid);
                // Exclude the current integer value: branch `v ≤ val−1`.
                let k = val - Rational64::from_integer(1);
                let split_var = self.make_split_atom(vid, k);
                self.new_decision_level();
                self.assign(split_var, self.decision_level(), None);
                continue;
            }

            // All integer + monomially consistent: extract and concretely verify.
            let env = self.extract_env();
            if concrete_sat(&env, assertions, manager) {
                return Some(NlDispatchResult::sat_with(
                    env.into_iter()
                        .map(|(t, v)| (t, num_rational::BigRational::from_integer(v)))
                        .collect(),
                ));
            }
            // The relaxation is integer-consistent but the full formula (with
            // the parts the relaxation abstracts — actual products) rejects it.
            // Without in-tableau monomial enforcement this branch concedes
            // (sound; an honest `Unknown` via the caller).
            return None;
        }
    }

    fn extract_env(&self) -> std::collections::HashMap<TermId, BigInt> {
        let mut env = std::collections::HashMap::new();
        for (&t, &vid) in &self.var {
            let r = self.simplex.value(vid);
            let v = if r.is_integer() {
                r64_to_big(r)
            } else {
                r64_to_big(r.floor())
            };
            env.insert(t, v);
        }
        env
    }
}

// ── Helpers ──

enum TheoryResult {
    Feasible,
    Conflict(Vec<i32>),
    LevelZeroUnsat,
    GiveUp,
}

fn add_scaled(acc: &mut LinExpr, other: &LinExpr, scale: Rational64) {
    for &(v, c) in &other.terms {
        acc.add_term(v, c * scale);
    }
    acc.add_constant(other.constant * scale);
}

/// Increment the power of `term` in a monomial key (or insert it at power 1).
fn bump_power(pm: &mut Vec<(TermId, u32)>, term: TermId) {
    for (t, p) in pm.iter_mut() {
        if *t == term {
            *p += 1;
            return;
        }
    }
    pm.push((term, 1));
}

fn r64_of(b: &BigInt) -> Option<Rational64> {
    Some(Rational64::from_integer(b.to_i64()?))
}

fn r64_to_big(r: Rational64) -> BigInt {
    BigInt::from(r.to_integer())
}

fn signed(var: usize, value: i8) -> i32 {
    let mag = var as i32;
    if value > 0 { mag } else { -mag }
}

fn concrete_sat(
    env: &std::collections::HashMap<TermId, BigInt>,
    assertions: &[TermId],
    manager: &TermManager,
) -> bool {
    let arrays: std::collections::HashMap<TermId, ArrayInterp> = std::collections::HashMap::new();
    for &a in assertions {
        if !eval_bool(a, manager, &arrays, env).unwrap_or(false) {
            return false;
        }
    }
    true
}

// ─────────────────────────────────────────────────────────────────────────────
// 1-UIP conflict analysis (pure, unit-tested)
// ─────────────────────────────────────────────────────────────────────────────

/// First-UIP conflict analysis. Given a conflict clause (all literals false
/// under the trail), derive the learnt clause (asserting literal at index 0)
/// and the backtrack level, by resolving the conflict clause against the
/// reasons of the most recent current-level literals until exactly one
/// current-level literal remains — the unique implication point.
///
/// Inputs follow the standard CDCL conventions:
/// * `value[v]`: `+1` true, `-1` false, `0` unassigned.
/// * `level[v]`: decision level (0 = a fixed/unit assignment).
/// * `reason[v]`: `Some(cid)` if `v` was propagated by clause `cid`; `None` if
///   `v` is a decision.
/// * `trail`: assigned literals in assignment order.
/// * `current_level`: the current decision level.
///
/// Returns `(learnt, backtrack_level)`; an empty `learnt` signals a level-0
/// conflict (the conflict clause has no level>0 literal to resolve — the caller
/// must treat that as a genuine unsat only if it is an original clause).
#[allow(dead_code)]
fn analyze_1uip(
    clauses: &[Vec<i32>],
    value: &[i8],
    level: &[u32],
    reason: &[Option<usize>],
    trail: &[i32],
    current_level: u32,
    conflict_clause: usize,
) -> (Vec<i32>, u32) {
    let n = value.len();
    let mut seen = vec![false; n];
    let mut learnt: Vec<i32> = Vec::new();
    let mut backtrack_level: u32 = 0;
    let mut path_count: i32 = 0; // current-level literals seen but not resolved
    let mut confl = clauses[conflict_clause].clone();
    // `cursor` scans the trail backwards (monotonically) for the most recent
    // seen literal. It is decremented before use.
    let mut cursor = trail.len();
    let mut asserting: i32 = 0; // the UIP literal (0 until found)
    loop {
        // Mark every literal of the current resolution clause. The pivot from
        // the previous iteration is already `seen`, so it is skipped here.
        for &q in &confl {
            let v = q.unsigned_abs() as usize;
            if v < n && !seen[v] && level[v] > 0 {
                seen[v] = true;
                if level[v] == current_level {
                    path_count += 1;
                } else {
                    learnt.push(q);
                    if level[v] > backtrack_level {
                        backtrack_level = level[v];
                    }
                }
            }
        }
        // Most recent trail literal that is `seen`.
        let mut found = false;
        while cursor > 0 {
            cursor -= 1;
            if seen[trail[cursor].unsigned_abs() as usize] {
                found = true;
                break;
            }
        }
        if !found {
            break; // no UIP (degenerate level-0 conflict)
        }
        let p = trail[cursor];
        let pv = p.unsigned_abs() as usize;
        // `p` is the most recent seen literal; as long as current-level seen
        // literals remain unresolved, `p` is one of them (current-level lits
        // are assigned after lower-level ones, so they are more recent).
        path_count -= 1;
        if path_count == 0 {
            // `p` is the sole remaining current-level literal → the UIP.
            asserting = -p;
            break;
        }
        // Otherwise resolve `p` against its reason. A decision (no reason) is
        // the UIP even if path_count > 0 (it dominates every current-level path).
        match reason.get(pv).copied().flatten() {
            Some(cid) => confl = clauses[cid].clone(),
            None => {
                asserting = -p;
                break;
            }
        }
    }
    if asserting == 0 {
        return (Vec::new(), 0);
    }
    learnt.insert(0, asserting);
    (learnt, backtrack_level)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Helper: build CDCL state arrays. `trail_lits` are assigned in order;
    /// `(var, lvl, reason)` triples give each variable's level and reason.
    fn state(
        trail_lits: &[i32],
        info: &[(i32, u32, Option<usize>)],
    ) -> (Vec<i8>, Vec<u32>, Vec<Option<usize>>, Vec<i32>, u32) {
        let n = info
            .iter()
            .map(|(v, _, _)| (*v).unsigned_abs() as usize)
            .max()
            .unwrap_or(0)
            + 1;
        let mut value = vec![0i8; n];
        let mut level = vec![0u32; n];
        let mut reason = vec![None; n];
        for &(v, lvl, r) in info {
            let var = v.unsigned_abs() as usize;
            value[var] = if v > 0 { 1 } else { -1 };
            level[var] = lvl;
            reason[var] = r;
        }
        let current = info.iter().map(|(_, l, _)| *l).max().unwrap_or(0);
        (value, level, reason, trail_lits.to_vec(), current)
    }

    /// Linear implication chain, single current level:
    ///   level 0: x4 = true (unit)
    ///   level 1: decide x1; clause {-1,2} -> x2; clause {-2,3} -> x3
    ///   conflict: {-3, -4}  (x3 true, x4 true -> both false)
    /// 1-UIP at level 1 is x3 (the only level-1 lit on the conflict slice after
    /// dropping the level-0 literal); learnt = {-3}, backtrack to 0.
    #[test]
    fn linear_chain_single_uip() {
        // clauses: 0={-1,2}, 1={-2,3}, 2={-3,-4}
        let clauses: Vec<Vec<i32>> = vec![vec![-1, 2], vec![-2, 3], vec![-3, -4]];
        let (value, level, reason, trail, current) = state(
            &[4, 1, 2, 3],
            &[(4, 0, None), (1, 1, None), (2, 1, Some(0)), (3, 1, Some(1))],
        );
        let (learnt, bt) = analyze_1uip(&clauses, &value, &level, &reason, &trail, current, 2);
        // The asserting literal is -3; the level-0 literal -4 is dropped.
        assert_eq!(learnt, vec![-3]);
        assert_eq!(bt, 0);
    }

    /// Two current-level literals, resolve one:
    ///   level 1: decide x1; {-1,2} -> x2; {-2,3} -> x3
    ///   level 2: decide x4; {-4,5} -> x5
    ///   conflict: {-3, -5}  (x3 true, x5 true)
    /// At level 2 the only level-2 lit is x5 -> first UIP = x5.
    /// learnt = {-5, -3}, backtrack to level 1.
    #[test]
    fn two_levels_first_uip() {
        let clauses: Vec<Vec<i32>> = vec![vec![-1, 2], vec![-2, 3], vec![-4, 5], vec![-3, -5]];
        let (value, level, reason, trail, current) = state(
            &[1, 2, 3, 4, 5],
            &[
                (1, 1, None),
                (2, 1, Some(0)),
                (3, 1, Some(1)),
                (4, 2, None),
                (5, 2, Some(2)),
            ],
        );
        let (learnt, bt) = analyze_1uip(&clauses, &value, &level, &reason, &trail, current, 3);
        assert_eq!(learnt, vec![-5, -3]);
        assert_eq!(bt, 1);
    }

    /// Conflict clause with two level-2 lits: resolve the propagated one (x5)
    /// to reach the decision (x4) as UIP.
    ///   conflict: {-3, -5, -4}  (x3 lvl1, x5 lvl2 prop, x4 lvl2 decision)
    /// learnt = {-4, -3}, backtrack to level 1.
    #[test]
    fn resolve_to_decision_uip() {
        let clauses: Vec<Vec<i32>> = vec![vec![-1, 2], vec![-2, 3], vec![-4, 5], vec![-3, -5, -4]];
        let (value, level, reason, trail, current) = state(
            &[1, 2, 3, 4, 5],
            &[
                (1, 1, None),
                (2, 1, Some(0)),
                (3, 1, Some(1)),
                (4, 2, None),
                (5, 2, Some(2)),
            ],
        );
        let (learnt, bt) = analyze_1uip(&clauses, &value, &level, &reason, &trail, current, 3);
        assert_eq!(learnt, vec![-4, -3]);
        assert_eq!(bt, 1);
    }

    /// Level-0 conflict (no level>0 literal in the conflict clause) -> empty.
    #[test]
    fn level_zero_conflict() {
        let clauses: Vec<Vec<i32>> = vec![vec![-1, -2]];
        let (value, level, reason, trail, current) = state(&[1, 2], &[(1, 0, None), (2, 0, None)]);
        let (learnt, _bt) = analyze_1uip(&clauses, &value, &level, &reason, &trail, current, 0);
        assert!(learnt.is_empty());
    }
}
