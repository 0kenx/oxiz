//! Nonlinear arithmetic (NLSAT/NIA/NRA) constraint checking
//!
//! This module implements early conflict detection for nonlinear arithmetic
//! constraints in QF_NIRA, QF_NIA, and QF_NRA benchmarks. It handles cases
//! where the main CDCL(T) loop with linear arithmetic cannot detect UNSAT
//! because the constraints involve nonlinear terms (e.g., x*x).
//!
//! ## Detected Patterns
//!
//! 1. `x^2 = c` where c < 0 → UNSAT (squares are non-negative)
//! 2. `x^2 = c` (integer x) where c is not a perfect square → UNSAT
//! 3. System contradictions: e.g., `sq > 0 ∧ sq + y = 0 ∧ y >= 0`
//!    (sq > 0 implies sq + y > 0 when y >= 0, contradicting sq + y = 0)

#[allow(unused_imports)]
use crate::prelude::*;
use num_bigint::BigInt;
use num_rational::{BigRational, Rational64};
use num_traits::{One, ToPrimitive, Zero};
use oxiz_core::ast::{TermId, TermKind, TermManager};
use oxiz_core::sort::SortKind;
use oxiz_theories::nlsat::{
    NlDispatchResult, NlSatModel, dispatch_nia_constraints, dispatch_nra_constraints,
    term_is_nonlinear,
};
use smallvec::SmallVec;

use super::Solver;
use super::types::{Model, SolverResult};

/// Which nonlinear backend `dispatch_nl_solver` should invoke.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum NlBackend {
    /// Integer / mixed (NIA, NIRA, ANIA) — `NiaSolver` with per-sort integrality.
    Nia,
    /// Pure real nonlinear — `NlsatSolver`.
    Nra,
}

/// A polynomial atom extracted from an assertion.
/// Represents: `coeff * square_term OP constant`
/// where `square_term` is a term of the form `x * x` (or product of identical terms).
#[derive(Debug, Clone)]
#[allow(dead_code)]
enum NlAtom {
    /// `sq_term = const` — the square term equals a constant
    SqEq {
        sq_term: TermId,
        val: Rational64,
        is_integer_sort: bool,
    },
    /// `sq_term > 0`
    SqGtZero { sq_term: TermId },
    /// `sq_term >= 0`
    SqGeZero { sq_term: TermId },
    /// `sq_term + linear_coeff * other_var = const`
    /// i.e., `sq + coeff * v = c`
    SqPlusLinearEq {
        sq_term: TermId,
        sq_coeff: Rational64,
        linear_var: TermId,
        linear_coeff: Rational64,
        rhs: Rational64,
    },
    /// `linear_var >= const`
    LinearGe { var: TermId, bound: Rational64 },
    /// `linear_var > const`
    LinearGt { var: TermId, bound: Rational64 },
}

impl Solver {
    /// Dispatch nonlinear arithmetic assertions to the full NIA/NRA polynomial
    /// solver.
    ///
    /// Translates all top-level assertions to polynomial form and runs either
    /// `NiaSolver` (integer) or `NlsatSolver` (real). Returns a definitive
    /// `SolverResult` when the solver is conclusive, or `None` to fall
    /// through to CDCL(T).
    ///
    /// On `Sat`, installs a concrete model from the NL solver so subsequent
    /// `(get-model)` / `(get-value …)` queries succeed.
    ///
    /// Backend selection:
    /// - Explicit `*NIA*` / `*NIRA*` / `*NRA*` logics as before.
    /// - Open logics (`ALL`, or no `set-logic`) **auto-detect** from formula
    ///   shape: nonlinear products (or array+nonlinear = ANIA) engage NIA;
    ///   pure-real nonlinear engages NRA. This closes the gap where users
    ///   write `(set-logic ALL)` for array+nonlinear mixes and otherwise
    ///   fell through to an honest `unknown`.
    ///
    /// Handles:
    /// - `x * y`, `x * y * z` (products of distinct variables)
    /// - `x * x` (squares / higher powers via repeated multiplication)
    /// - `(x + 1) * (y - 2)` (products of linear expressions)
    pub(super) fn dispatch_nl_solver(&mut self, manager: &mut TermManager) -> Option<SolverResult> {
        let backend = self.nl_backend(manager)?;

        let result = match backend {
            NlBackend::Nia => dispatch_nia_constraints(&self.assertions, manager, true),
            NlBackend::Nra => dispatch_nra_constraints(&self.assertions, manager),
        }?;

        match result {
            NlDispatchResult::Sat(nl_model) => {
                self.install_nl_model(nl_model, manager);
                Some(SolverResult::Sat)
            }
            NlDispatchResult::Unsat => Some(SolverResult::Unsat),
        }
    }

    /// Resolve which NL backend to run, including formula-shape auto-detect
    /// under open logics (`ALL` / unset).
    fn nl_backend(&self, manager: &TermManager) -> Option<NlBackend> {
        // Unset logic behaves like SMT-LIB `ALL` (no theory restriction).
        let logic = self.logic.as_deref().unwrap_or("ALL");

        // Explicit nonlinear logics win over shape detection.
        // Note: `NIRA` does NOT contain `NIA` as a substring (it is N-I-R-A),
        // so match it explicitly — NIRA routes to the NIA backend (per-sort
        // integrality in the translator keeps Real vars real).
        if logic.contains("NIA") || logic.contains("NIRA") {
            return Some(NlBackend::Nia);
        }
        if logic.contains("NRA") {
            return Some(NlBackend::Nra);
        }

        // Open logics only: do not override QF_LIA / QF_UF / … declarations.
        if !is_open_logic(logic) {
            return None;
        }

        let has_nl = self
            .assertions
            .iter()
            .any(|&a| term_is_nonlinear(a, manager));
        if !has_nl {
            return None;
        }

        // Arrays + nonlinear → ANIA (NIA backend with purification + ground).
        // Any Int-sorted arithmetic in a nonlinear formula → NIA.
        // Otherwise pure-real nonlinear → NRA.
        if assertions_have_array(manager, &self.assertions)
            || assertions_have_int_arith(manager, &self.assertions)
        {
            Some(NlBackend::Nia)
        } else {
            Some(NlBackend::Nra)
        }
    }

    /// Install an NL-dispatch model into `self.model` for `(get-model)`.
    fn install_nl_model(&mut self, nl_model: NlSatModel, manager: &mut TermManager) {
        let mut model = Model::new();
        for (term, value) in nl_model.assignments {
            let is_int = manager
                .get(term)
                .map(|t| t.sort == manager.sorts.int_sort)
                .unwrap_or(true);
            let value_term = if is_int {
                manager.mk_int(value.to_integer())
            } else {
                big_rational_to_real_term(manager, &value)
            };
            model.set(term, value_term);
        }
        self.model = Some(model);
    }

    /// Check nonlinear arithmetic constraints for early UNSAT detection.
    ///
    /// Returns `true` if the constraint set is detected as UNSAT.
    pub(super) fn check_nonlinear_constraints(&self, manager: &TermManager) -> bool {
        // Run for explicit NL logics, and for open logics that actually contain
        // nonlinear products (same auto-detect policy as `dispatch_nl_solver`).
        let logic = self.logic.as_deref().unwrap_or("ALL");
        let explicit_nl = logic.contains("NIA") || logic.contains("NRA") || logic.contains("NIRA");
        let open_nl = is_open_logic(logic)
            && self
                .assertions
                .iter()
                .any(|&a| term_is_nonlinear(a, manager));
        if !explicit_nl && !open_nl {
            return false;
        }

        // Collect nonlinear atoms from all top-level assertions
        let mut atoms: Vec<NlAtom> = Vec::new();
        for &assertion in &self.assertions {
            self.collect_nl_atoms(assertion, manager, &mut atoms);
        }

        if atoms.is_empty() {
            return false;
        }

        // Check pattern 1: x^2 = c where c < 0 (never has a real solution)
        for atom in &atoms {
            if let NlAtom::SqEq { val, .. } = atom {
                if *val < Rational64::zero() {
                    return true;
                }
            }
        }

        // Check pattern 2: x^2 = c where c is not a perfect square (integer context)
        for atom in &atoms {
            if let NlAtom::SqEq {
                val,
                is_integer_sort,
                ..
            } = atom
            {
                if *is_integer_sort && *val >= Rational64::zero() {
                    if let Some(n) = val.to_i64() {
                        if n >= 0 && !is_perfect_square(n as u64) {
                            return true;
                        }
                    }
                }
            }
        }

        // Check pattern 3: system contradictions involving squares.
        //
        // Look for triples:
        //   (A) sq_term > 0                    [or sq_term >= 1 in integer case]
        //   (B) sq_term * a + var * b = c      [sum constraint]
        //   (C) var >= d                        [lower bound on var]
        //
        // where sq > 0 and b * var = c - a * sq, so var = (c - a*sq) / b.
        // Combined with var >= d: (c - a*sq)/b >= d.
        // If sq > 0 (sq >= 1 for int, sq > 0 for real) and a > 0, then
        // a*sq >= a (int) or a*sq > 0 (real), so c - a*sq < c (for positive a).
        // When d = 0 (y >= 0) and c = 0: c - a*sq = -a*sq <= -a < 0,
        // but we need var >= 0 — contradiction.
        //
        // Concretely, check:
        //   sq > 0  AND  sq + v = 0  AND  v >= 0
        // → v = -sq < 0  contradicts  v >= 0
        if self.check_sq_sum_bound_contradiction(&atoms) {
            return true;
        }

        false
    }

    /// Check for the "sq > 0 AND sq + v = 0 AND v >= 0" type contradiction.
    fn check_sq_sum_bound_contradiction(&self, atoms: &[NlAtom]) -> bool {
        // Build sets for quick lookup
        let sq_gt_zero: Vec<TermId> = atoms
            .iter()
            .filter_map(|a| {
                if let NlAtom::SqGtZero { sq_term } = a {
                    Some(*sq_term)
                } else {
                    None
                }
            })
            .collect();

        // For each "sq + coeff * var = rhs" constraint, check if we have sq > 0
        // and var >= -rhs/coeff is violated
        for atom in atoms {
            let NlAtom::SqPlusLinearEq {
                sq_term,
                sq_coeff,
                linear_var,
                linear_coeff,
                rhs,
            } = atom
            else {
                continue;
            };

            // Only handle the case where both sq_coeff and linear_coeff are non-zero
            if sq_coeff.is_zero() || linear_coeff.is_zero() {
                continue;
            }

            // Check if sq_term is known to be > 0
            let sq_positive = sq_gt_zero.contains(sq_term);
            if !sq_positive {
                continue;
            }

            // From: sq_coeff * sq + linear_coeff * var = rhs
            // → var = (rhs - sq_coeff * sq) / linear_coeff
            // If sq > 0 (at least epsilon > 0):
            // For real: sq > 0, so sq_coeff * sq > 0 when sq_coeff > 0
            //   → rhs - sq_coeff * sq < rhs
            //   → var < rhs / linear_coeff  (when linear_coeff > 0)
            //   OR var > rhs / linear_coeff  (when linear_coeff < 0)

            // The var = (rhs - sq_coeff * sq) / linear_coeff must satisfy
            // any lower bounds we have on var.
            let var_expr_at_sq_zero = *rhs / *linear_coeff; // value of var if sq=0

            // The sign of d(var)/d(sq) = -sq_coeff / linear_coeff
            // If sq increases from 0 (since sq > 0), var moves in direction -sq_coeff/linear_coeff

            // Check against all >= bounds on linear_var
            for bound_atom in atoms {
                let bound = match bound_atom {
                    NlAtom::LinearGe { var, bound } if *var == *linear_var => bound,
                    _ => continue,
                };

                // We need: var >= bound
                // From the sum constraint, as sq→0+, var→var_expr_at_sq_zero
                // If the sum constraint requires var < bound for all sq > 0,
                // that contradicts var >= bound.

                // Direction: d(var)/d(sq) = -sq_coeff / linear_coeff
                let deriv_sign = -(*sq_coeff) / *linear_coeff;

                // If deriv_sign < 0, then as sq increases (sq > 0), var decreases.
                // At sq = 0: var = var_expr_at_sq_zero
                // For all sq > 0: var < var_expr_at_sq_zero
                // If var_expr_at_sq_zero <= bound, then for sq > 0: var < bound — contradiction with var >= bound.

                if deriv_sign < Rational64::zero() && var_expr_at_sq_zero <= *bound {
                    return true;
                }

                // If deriv_sign > 0, then as sq increases (sq > 0), var increases.
                // The infimum is at sq = 0 (var → var_expr_at_sq_zero from above).
                // For all sq > 0: var > var_expr_at_sq_zero.
                // If var_expr_at_sq_zero >= bound, no contradiction from this alone.
                // But if we also have an upper bound on var that forces a contradiction...
                // For now, skip this case.
            }

            // Also check against strict lower bounds (LinearGt)
            for bound_atom in atoms {
                let bound = match bound_atom {
                    NlAtom::LinearGt { var, bound } if *var == *linear_var => bound,
                    _ => continue,
                };

                let deriv_sign = -(*sq_coeff) / *linear_coeff;

                // If deriv_sign < 0, as sq > 0: var < var_expr_at_sq_zero
                // Contradiction if var_expr_at_sq_zero <= bound (need var > bound, but var < bound)
                if deriv_sign < Rational64::zero() && var_expr_at_sq_zero <= *bound {
                    return true;
                }
            }
        }

        false
    }

    /// Collect nonlinear atoms from a term (top-level assertion).
    ///
    /// Iterative over the `and`-nesting (the only structure descended into),
    /// with a visited set so shared conjuncts of the hash-consed DAG
    /// contribute their atoms once; every downstream consumer performs pure
    /// existence checks over the collected atoms, so dropping duplicates
    /// preserves the verdict exactly.
    fn collect_nl_atoms(&self, term_id: TermId, manager: &TermManager, atoms: &mut Vec<NlAtom>) {
        let mut visited: FxHashSet<TermId> = FxHashSet::default();
        let mut stack: Vec<TermId> = vec![term_id];
        while let Some(term_id) = stack.pop() {
            if !visited.insert(term_id) {
                continue;
            }
            let Some(term) = manager.get(term_id) else {
                continue;
            };

            match &term.kind {
                TermKind::Eq(lhs, rhs) => {
                    self.extract_nl_eq(*lhs, *rhs, manager, atoms);
                }
                TermKind::Gt(lhs, rhs) => {
                    // lhs > rhs  i.e. lhs - rhs > 0
                    self.extract_nl_comparison(*lhs, *rhs, CompOp::Gt, manager, atoms);
                }
                TermKind::Ge(lhs, rhs) => {
                    self.extract_nl_comparison(*lhs, *rhs, CompOp::Ge, manager, atoms);
                }
                TermKind::Lt(lhs, rhs) => {
                    // lhs < rhs  →  rhs > lhs
                    self.extract_nl_comparison(*rhs, *lhs, CompOp::Gt, manager, atoms);
                }
                TermKind::Le(lhs, rhs) => {
                    // lhs <= rhs  →  rhs >= lhs
                    self.extract_nl_comparison(*rhs, *lhs, CompOp::Ge, manager, atoms);
                }
                TermKind::And(args) => {
                    // Reversed push keeps the original left-to-right visit
                    // order (and with it the order of `atoms`).
                    stack.extend(args.iter().rev().copied());
                }
                _ => {}
            }
        }
    }

    /// Extract atoms from an equality `lhs = rhs`.
    fn extract_nl_eq(
        &self,
        lhs: TermId,
        rhs: TermId,
        manager: &TermManager,
        atoms: &mut Vec<NlAtom>,
    ) {
        // Try: is lhs a pure square (x * x) and rhs a constant?
        if let Some((sq_term, sq_coeff, is_int)) = self.extract_pure_square(lhs, manager) {
            if let Some(rhs_val) = self.extract_rational_const(rhs, manager) {
                // sq_coeff * sq_term = rhs_val  →  sq_term = rhs_val / sq_coeff
                if !sq_coeff.is_zero() {
                    let val = rhs_val / sq_coeff;
                    atoms.push(NlAtom::SqEq {
                        sq_term,
                        val,
                        is_integer_sort: is_int,
                    });
                    return;
                }
            }
        }

        // Try reversed: rhs is pure square, lhs is constant
        if let Some((sq_term, sq_coeff, is_int)) = self.extract_pure_square(rhs, manager) {
            if let Some(lhs_val) = self.extract_rational_const(lhs, manager) {
                if !sq_coeff.is_zero() {
                    let val = lhs_val / sq_coeff;
                    atoms.push(NlAtom::SqEq {
                        sq_term,
                        val,
                        is_integer_sort: is_int,
                    });
                    return;
                }
            }
        }

        // Try: lhs = Add(...) where the Add contains a square term plus a linear var
        // Pattern: (* x x) + y = const  or  y + (* x x) = const
        self.extract_nl_sum_eq(lhs, rhs, manager, atoms);
        self.extract_nl_sum_eq(rhs, lhs, manager, atoms);
    }

    /// Extract "sq_term + linear_var = rhs" from a sum equality.
    fn extract_nl_sum_eq(
        &self,
        sum_side: TermId,
        const_side: TermId,
        manager: &TermManager,
        atoms: &mut Vec<NlAtom>,
    ) {
        let Some(rhs_val) = self.extract_rational_const(const_side, manager) else {
            return;
        };

        let Some(sum_term) = manager.get(sum_side) else {
            return;
        };

        let TermKind::Add(args) = &sum_term.kind else {
            return;
        };

        // Try to identify: one arg is a pure square, the rest are linear vars
        let mut sq_term_opt: Option<(TermId, Rational64)> = None;
        let mut linear_term_opt: Option<(TermId, Rational64)> = None;
        let mut ok = true;

        for &arg in args {
            if let Some((sq_term, sq_coeff, _)) = self.extract_pure_square(arg, manager) {
                if sq_term_opt.is_some() {
                    ok = false;
                    break;
                }
                sq_term_opt = Some((sq_term, sq_coeff));
            } else if let Some((var, coeff)) = self.extract_linear_var(arg, manager) {
                if linear_term_opt.is_some() {
                    ok = false;
                    break;
                }
                linear_term_opt = Some((var, coeff));
            } else {
                ok = false;
                break;
            }
        }

        if !ok {
            return;
        }

        if let (Some((sq_term, sq_coeff)), Some((linear_var, linear_coeff))) =
            (sq_term_opt, linear_term_opt)
        {
            atoms.push(NlAtom::SqPlusLinearEq {
                sq_term,
                sq_coeff,
                linear_var,
                linear_coeff,
                rhs: rhs_val,
            });
        }
    }

    /// Extract atoms from a comparison `lhs OP 0` or `lhs OP rhs`.
    fn extract_nl_comparison(
        &self,
        lhs: TermId,
        rhs: TermId,
        op: CompOp,
        manager: &TermManager,
        atoms: &mut Vec<NlAtom>,
    ) {
        // Check if lhs is a pure square and rhs is a constant.
        // After normalization: sq_term OP (rhs_val / sq_coeff)
        if let Some((sq_term, sq_coeff, _)) = self.extract_pure_square(lhs, manager) {
            if let Some(rhs_val) = self.extract_rational_const(rhs, manager) {
                if !sq_coeff.is_zero() {
                    // sq_coeff * sq_term OP rhs_val
                    // → sq_term OP rhs_val/sq_coeff  (flip op if sq_coeff < 0)
                    let normalized = rhs_val / sq_coeff;
                    let effective_op = if sq_coeff < Rational64::zero() {
                        op.flip()
                    } else {
                        op
                    };
                    match effective_op {
                        CompOp::Gt => {
                            if normalized < Rational64::zero() {
                                // sq > negative → always true, not useful
                            } else if normalized.is_zero() {
                                atoms.push(NlAtom::SqGtZero { sq_term });
                            }
                        }
                        CompOp::Ge => {
                            if normalized <= Rational64::zero() {
                                atoms.push(NlAtom::SqGeZero { sq_term });
                            }
                        }
                    }
                    return;
                }
            }
        }

        // Check if this is a simple linear comparison: var OP const
        if let Some((var, coeff)) = self.extract_linear_var(lhs, manager) {
            if let Some(rhs_val) = self.extract_rational_const(rhs, manager) {
                if !coeff.is_zero() {
                    // coeff * var OP rhs_val
                    // → var OP rhs_val/coeff (flip op if coeff < 0)
                    let bound = rhs_val / coeff;
                    let effective_op = if coeff < Rational64::zero() {
                        op.flip()
                    } else {
                        op
                    };
                    match effective_op {
                        CompOp::Gt => atoms.push(NlAtom::LinearGt { var, bound }),
                        CompOp::Ge => atoms.push(NlAtom::LinearGe { var, bound }),
                    }
                }
                return;
            }
        }

        // Also handle reversed (const OP lhs → lhs OP' const) but skip for now
        // since the benchmark uses canonical form (lhs > 0, var >= 0)
        let _ = (lhs, rhs, op, manager, atoms);
    }

    /// Extract a pure square: a Mul term where all factors are the same variable.
    /// Returns `(representative_var_term, coefficient, is_integer_sort)` or None.
    ///
    /// Handles patterns like:
    /// - `(* x x)` → Some((x_term, 1, is_int))
    /// - `(* 2 x x)` → Some((x_term, 2, is_int))  [if we ever see this]
    fn extract_pure_square(
        &self,
        term_id: TermId,
        manager: &TermManager,
    ) -> Option<(TermId, Rational64, bool)> {
        let term = manager.get(term_id)?;

        match &term.kind {
            TermKind::Mul(args) => {
                let mut const_coeff = Rational64::one();
                let mut var_factors: Vec<TermId> = Vec::new();

                for &arg in args {
                    let arg_term = manager.get(arg)?;
                    match &arg_term.kind {
                        TermKind::IntConst(n) => {
                            let v = n.to_i64()?;
                            const_coeff *= Rational64::from_integer(v);
                        }
                        TermKind::RealConst(r) => {
                            const_coeff *= *r;
                        }
                        TermKind::Var(_) => {
                            var_factors.push(arg);
                        }
                        _ => return None, // nested expressions not handled
                    }
                }

                // Must have exactly 2 variable factors and they must be the same
                if var_factors.len() == 2 && var_factors[0] == var_factors[1] {
                    let v = var_factors[0];
                    let vt = manager.get(v)?;
                    let is_int = vt.sort == manager.sorts.int_sort;
                    Some((v, const_coeff, is_int))
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    /// Extract a simple linear variable term with coefficient.
    /// Returns `(var_term_id, coefficient)` or None.
    ///
    /// Handles:
    /// - `x` → Some((x, 1))
    /// - `(* c x)` → Some((x, c))
    ///
    /// Iterative: the only recursion was through `Neg` nesting, which is a
    /// simple sign-flipping unwrap loop.
    fn extract_linear_var(
        &self,
        term_id: TermId,
        manager: &TermManager,
    ) -> Option<(TermId, Rational64)> {
        let mut sign = Rational64::one();
        let mut current = term_id;
        loop {
            let term = manager.get(current)?;

            match &term.kind {
                TermKind::Neg(inner) => {
                    sign = -sign;
                    current = *inner;
                }
                TermKind::Var(_) => return Some((current, sign)),
                TermKind::Mul(args) => {
                    let mut const_coeff = Rational64::one();
                    let mut var_opt: Option<TermId> = None;

                    for &arg in args {
                        let arg_term = manager.get(arg)?;
                        match &arg_term.kind {
                            TermKind::IntConst(n) => {
                                let v = n.to_i64()?;
                                const_coeff *= Rational64::from_integer(v);
                            }
                            TermKind::RealConst(r) => {
                                const_coeff *= *r;
                            }
                            TermKind::Var(_) => {
                                if var_opt.is_some() {
                                    return None; // multiple vars → nonlinear
                                }
                                var_opt = Some(arg);
                            }
                            _ => return None,
                        }
                    }

                    return var_opt.map(|v| (v, sign * const_coeff));
                }
                _ => return None,
            }
        }
    }

    /// Extract a rational constant from a term.
    ///
    /// Handles:
    /// - `IntConst(n)` → n
    /// - `RealConst(r)` → r
    /// - `Neg(x)` → -extract(x)
    /// - `Sub(0, x)` → -extract(x)  [unary minus is parsed as Sub(0, x)]
    /// - `Sub(x, y)` → extract(x) - extract(y)
    /// - `Add(xs)` → Σ extract(xᵢ)
    ///
    /// Iterative (explicit frame stack), so arbitrarily deep constant
    /// expressions are folded without native recursion; any non-constant
    /// sub-term makes the whole extraction `None`, exactly as before.
    fn extract_rational_const(&self, term_id: TermId, manager: &TermManager) -> Option<Rational64> {
        /// A pending arithmetic operator waiting for operand values.
        enum ConstFrame {
            Neg,
            SubLhs {
                rhs: TermId,
            },
            SubRhs {
                lhs: Rational64,
            },
            Add {
                args: SmallVec<[TermId; 4]>,
                next: usize,
                acc: Rational64,
            },
        }

        let mut frames: Vec<ConstFrame> = Vec::new();
        let mut current = term_id;
        'open: loop {
            // Descend to a constant leaf.
            let mut value: Rational64 = loop {
                let term = manager.get(current)?;
                match &term.kind {
                    TermKind::IntConst(n) => {
                        let v = n.to_i64()?;
                        break Rational64::from_integer(v);
                    }
                    TermKind::RealConst(r) => break *r,
                    TermKind::Neg(inner) => {
                        frames.push(ConstFrame::Neg);
                        current = *inner;
                    }
                    TermKind::Sub(lhs, rhs) => {
                        frames.push(ConstFrame::SubLhs { rhs: *rhs });
                        current = *lhs;
                    }
                    TermKind::Add(args) => match args.first() {
                        Some(&first) => {
                            frames.push(ConstFrame::Add {
                                args: args.clone(),
                                next: 1,
                                acc: Rational64::zero(),
                            });
                            current = first;
                        }
                        None => break Rational64::zero(),
                    },
                    _ => return None,
                }
            };

            // Fold the leaf value into the pending operators.
            loop {
                match frames.pop() {
                    None => return Some(value),
                    Some(ConstFrame::Neg) => value = -value,
                    Some(ConstFrame::SubLhs { rhs }) => {
                        frames.push(ConstFrame::SubRhs { lhs: value });
                        current = rhs;
                        continue 'open;
                    }
                    Some(ConstFrame::SubRhs { lhs }) => value = lhs - value,
                    Some(ConstFrame::Add { args, next, acc }) => {
                        let acc = acc + value;
                        if let Some(&child) = args.get(next) {
                            frames.push(ConstFrame::Add {
                                args,
                                next: next + 1,
                                acc,
                            });
                            current = child;
                            continue 'open;
                        }
                        value = acc;
                    }
                }
            }
        }
    }
}

/// SMT-LIB open / unrestricted logics where formula-shape auto-detect is safe.
fn is_open_logic(logic: &str) -> bool {
    logic.is_empty() || logic.eq_ignore_ascii_case("ALL")
}

/// Whether any assertion mentions an array sort, `select`, or `store`.
fn assertions_have_array(manager: &TermManager, assertions: &[TermId]) -> bool {
    let mut stack: Vec<TermId> = assertions.to_vec();
    let mut seen = FxHashSet::default();
    while let Some(id) = stack.pop() {
        if !seen.insert(id) {
            continue;
        }
        let Some(term) = manager.get(id) else {
            continue;
        };
        if matches!(term.kind, TermKind::Select(_, _) | TermKind::Store(_, _, _)) {
            return true;
        }
        if let Some(sort) = manager.sorts.get(term.sort)
            && matches!(sort.kind, SortKind::Array { .. })
        {
            return true;
        }
        super::term_walk::collect_structural_children(&term.kind, &mut stack);
    }
    false
}

/// Whether any assertion involves Int-sorted arithmetic (vars, selects, consts
/// under arith ops). Used to prefer the NIA backend over pure NRA under `ALL`.
fn assertions_have_int_arith(manager: &TermManager, assertions: &[TermId]) -> bool {
    let int_sort = manager.sorts.int_sort;
    let mut stack: Vec<TermId> = assertions.to_vec();
    let mut seen = FxHashSet::default();
    while let Some(id) = stack.pop() {
        if !seen.insert(id) {
            continue;
        }
        let Some(term) = manager.get(id) else {
            continue;
        };
        if term.sort == int_sort
            && matches!(
                term.kind,
                TermKind::Var(_)
                    | TermKind::Select(_, _)
                    | TermKind::IntConst(_)
                    | TermKind::Add(_)
                    | TermKind::Mul(_)
                    | TermKind::Sub(_, _)
                    | TermKind::Neg(_)
                    | TermKind::Div(_, _)
                    | TermKind::Mod(_, _)
            )
        {
            return true;
        }
        super::term_walk::collect_structural_children(&term.kind, &mut stack);
    }
    false
}

/// Convert a `BigRational` into a Real-sorted constant term.
///
/// Prefers an exact `Rational64` when both numerator and denominator fit in
/// `i64`; otherwise falls back to an integer approximation of the floor
/// (still a valid Real constant, just less precise for huge values).
fn big_rational_to_real_term(manager: &mut TermManager, value: &BigRational) -> TermId {
    let n = value.numer();
    let d = value.denom();
    if let (Some(ni), Some(di)) = (n.to_i64(), d.to_i64()) {
        if di != 0 {
            return manager.mk_real(Rational64::new(ni, di));
        }
    }
    // Fallback: integer part only.
    let approx: BigInt = value.to_integer();
    if let Some(v) = approx.to_i64() {
        manager.mk_real(Rational64::from_integer(v))
    } else {
        manager.mk_real(Rational64::from_integer(0))
    }
}

/// Comparison operator (strict or non-strict greater-than).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum CompOp {
    Gt,
    Ge,
}

impl CompOp {
    fn flip(self) -> Self {
        match self {
            CompOp::Gt => CompOp::Ge, // flipping strict: -x > c → x < -c → -x >= c (approx)
            CompOp::Ge => CompOp::Gt,
        }
    }
}

/// Check if n is a perfect square (i.e., there exists k such that k*k = n).
fn is_perfect_square(n: u64) -> bool {
    if n == 0 {
        return true;
    }
    let r = (n as f64).sqrt() as u64;
    // Check r and r+1 in case of floating-point rounding
    (r * r == n) || ((r + 1) * (r + 1) == n)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_is_perfect_square() {
        assert!(is_perfect_square(0));
        assert!(is_perfect_square(1));
        assert!(is_perfect_square(4));
        assert!(is_perfect_square(9));
        assert!(is_perfect_square(16));
        assert!(is_perfect_square(25));
        assert!(!is_perfect_square(2));
        assert!(!is_perfect_square(3));
        assert!(!is_perfect_square(5));
        assert!(!is_perfect_square(6));
        assert!(!is_perfect_square(7));
        assert!(!is_perfect_square(8));
    }
}
