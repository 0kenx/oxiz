//! Arithmetic Theory Solver

use super::simplex::{LinExpr, Simplex, VarId};
#[allow(unused_imports)]
use crate::prelude::*;
use crate::theory::{EqualityNotification, Theory, TheoryCombination, TheoryId, TheoryResult};
use num_rational::Rational64;
use num_traits::{One, Signed, Zero};
use oxiz_core::ast::TermId;
use oxiz_core::error::Result;

/// Compute GCD of two i64 values
fn gcd_i64(mut a: i64, mut b: i64) -> i64 {
    a = a.abs();
    b = b.abs();
    while b != 0 {
        let temp = b;
        b = a % b;
        a = temp;
    }
    a
}

/// Compute GCD of two i128 values (used by the Diophantine consistency check).
fn gcd_i128(mut a: i128, mut b: i128) -> i128 {
    a = a.abs();
    b = b.abs();
    while b != 0 {
        let temp = b;
        b = a % b;
        a = temp;
    }
    a
}

/// Arithmetic Theory Solver (LRA/LIA)
#[derive(Debug)]
pub struct ArithSolver {
    /// Simplex instance
    simplex: Simplex,
    /// Term to variable mapping
    term_to_var: FxHashMap<TermId, VarId>,
    /// Variable to term mapping
    var_to_term: Vec<TermId>,
    /// Reason counter
    reason_counter: u32,
    /// Reason to term mapping
    reasons: Vec<TermId>,
    /// Is this LIA (integers) or LRA (reals)?
    is_integer: bool,
    /// Context stack
    context_stack: Vec<ContextState>,
    /// Accumulated shared equalities (from notify_equality calls)
    shared_equalities: Vec<EqualityNotification>,
    /// Integral model recorded by the LIA branch-and-bound search.
    ///
    /// Populated only when the most recent `check()` proved `Sat` in integer
    /// mode.  `value()` consults this first for Int terms so it returns the
    /// integral assignment found by branch-and-bound rather than the (possibly
    /// fractional) LP-relaxation optimum.  Cleared at the start of every
    /// `check()` and on `reset()`.
    lia_model: FxHashMap<VarId, Rational64>,
    /// Integer equalities asserted in LIA mode, kept as raw
    /// `(sum a_i·x_i = b)` rows so that a linear Diophantine consistency check
    /// can detect cross-constraint parity infeasibility (e.g. `y=2x ∧ y=2z+1`)
    /// that per-equation GCD reasoning and pure branch-and-bound over unbounded
    /// variables miss.  Push/pop-scoped via `ContextState`.
    int_equalities: Vec<IntEquation>,
}

/// A linear equality over the integers: `sum(coeff_i · var_i) = rhs`.
#[derive(Debug, Clone)]
struct IntEquation {
    terms: Vec<(VarId, i64)>,
    rhs: i64,
}

/// Outcome of exploring a single branch-and-bound child node.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum BranchOutcome {
    /// An integral assignment satisfying all constraints was found.
    Sat,
    /// This branch is proven infeasible (a dead end).
    Infeasible,
    /// The branch could not be resolved within the resource budget.
    Unknown,
}

/// State for push/pop
#[derive(Debug, Clone)]
struct ContextState {
    num_vars: usize,
    num_reasons: usize,
    num_shared_equalities: usize,
    num_int_equalities: usize,
}

impl Default for ArithSolver {
    fn default() -> Self {
        Self::new(false)
    }
}

impl ArithSolver {
    /// Create a new arithmetic solver
    #[must_use]
    pub fn new(is_integer: bool) -> Self {
        Self {
            simplex: Simplex::new(),
            term_to_var: FxHashMap::default(),
            var_to_term: Vec::new(),
            reason_counter: 0,
            reasons: Vec::new(),
            is_integer,
            context_stack: Vec::new(),
            shared_equalities: Vec::new(),
            lia_model: FxHashMap::default(),
            int_equalities: Vec::new(),
        }
    }

    /// Create a new LRA solver
    #[must_use]
    pub fn lra() -> Self {
        Self::new(false)
    }

    /// Create a new LIA solver
    #[must_use]
    pub fn lia() -> Self {
        Self::new(true)
    }

    /// Whether this solver operates in integer (LIA) mode
    #[must_use]
    pub fn is_integer(&self) -> bool {
        self.is_integer
    }

    /// Intern a term as a variable
    pub fn intern(&mut self, term: TermId) -> VarId {
        if let Some(&var) = self.term_to_var.get(&term) {
            return var;
        }

        let var = self.simplex.new_var();
        self.term_to_var.insert(term, var);
        self.var_to_term.push(term);
        var
    }

    /// Add a reason and return its ID
    fn add_reason(&mut self, term: TermId) -> u32 {
        let id = self.reason_counter;
        self.reason_counter += 1;
        self.reasons.push(term);
        id
    }

    /// Normalize a linear expression
    ///
    /// Normalization performs:
    /// 1. Coefficient reduction: divide by GCD of all coefficients
    /// 2. Sorting: order terms by variable ID for canonical form
    /// 3. Sign normalization: ensure first coefficient (after sorting) is positive
    ///
    /// IMPORTANT: Step 3 is only safe for symmetric constraints (equalities).
    /// For inequalities (Le/Ge), sign normalization flips the direction and must
    /// NOT be applied.  Call `normalize_expr_no_sign` for those cases instead.
    fn normalize_expr(&self, expr: &mut LinExpr) {
        if expr.terms.is_empty() {
            return;
        }

        // For integer arithmetic, reduce by GCD
        if self.is_integer {
            // Find GCD of all coefficients
            let gcd = expr
                .terms
                .iter()
                .map(|(_, c)| c.numer().abs())
                .fold(0i64, |acc, n| if acc == 0 { n } else { gcd_i64(acc, n) });

            if gcd > 1 {
                let divisor = Rational64::from_integer(gcd);
                expr.scale(Rational64::one() / divisor);
            }
        }

        // Ensure first coefficient is positive
        if let Some((_, c)) = expr.terms.first()
            && c.is_negative()
        {
            expr.negate();
        }

        // Sort terms by variable ID for canonical form
        expr.terms.sort_by_key(|(v, _)| *v);
    }

    /// Normalize for inequalities: GCD reduction and sorting only.
    ///
    /// Sign normalization is deliberately omitted because negating an inequality
    /// expression reverses its direction (e.g., fa - fb <= 0 becomes fb - fa <= 0,
    /// which represents the opposite constraint fa >= fb).
    fn normalize_ineq_expr(&self, expr: &mut LinExpr) {
        if expr.terms.is_empty() {
            return;
        }

        // For integer arithmetic, reduce by GCD only (preserves sign)
        if self.is_integer {
            let gcd = expr
                .terms
                .iter()
                .map(|(_, c)| c.numer().abs())
                .fold(0i64, |acc, n| if acc == 0 { n } else { gcd_i64(acc, n) });

            if gcd > 1 {
                let divisor = Rational64::from_integer(gcd);
                expr.scale(Rational64::one() / divisor);
            }
        }

        // Sort terms by variable ID — safe because sorting doesn't change the sign
        // of the overall expression for inequalities (we don't negate afterwards).
        // NOTE: Sorting alone is also problematic because it reorders terms but the
        // sign is determined by all terms together.  We keep the sort for consistent
        // canonical form but do NOT apply the sign-flip step.
        expr.terms.sort_by_key(|(v, _)| *v);
    }

    /// Assert: lhs <= rhs
    pub fn assert_le(&mut self, lhs: &[(TermId, Rational64)], rhs: Rational64, reason: TermId) {
        let mut expr = LinExpr::new();

        for (term, coef) in lhs {
            let var = self.intern(*term);
            expr.add_term(var, *coef);
        }
        expr.add_constant(-rhs);

        // Use inequality-safe normalization: GCD reduction + sort, but NO sign flip.
        // sign normalization (negation) would reverse the inequality direction.
        self.normalize_ineq_expr(&mut expr);

        let reason_id = self.add_reason(reason);
        self.simplex.add_le(expr, reason_id);
    }

    /// Assert: lhs >= rhs
    pub fn assert_ge(&mut self, lhs: &[(TermId, Rational64)], rhs: Rational64, reason: TermId) {
        let mut expr = LinExpr::new();

        for (term, coef) in lhs {
            let var = self.intern(*term);
            expr.add_term(var, *coef);
        }
        expr.add_constant(-rhs);

        // Use inequality-safe normalization: GCD reduction + sort, but NO sign flip.
        self.normalize_ineq_expr(&mut expr);

        let reason_id = self.add_reason(reason);
        self.simplex.add_ge(expr, reason_id);
    }

    /// Assert: lhs = rhs
    ///
    /// For integer arithmetic (LIA), checks GCD-based infeasibility:
    /// If all coefficients share a common GCD that doesn't divide the RHS,
    /// the constraint is infeasible over integers.
    ///
    /// Example: 2x + 2y = 7 is infeasible because gcd(2,2) = 2 doesn't divide 7.
    pub fn assert_eq(&mut self, lhs: &[(TermId, Rational64)], rhs: Rational64, reason: TermId) {
        let mut expr = LinExpr::new();

        for (term, coef) in lhs {
            let var = self.intern(*term);
            expr.add_term(var, *coef);
        }
        expr.add_constant(-rhs);

        // For LIA, check GCD-based infeasibility BEFORE normalization
        // (normalization divides by GCD, which would lose the infeasibility signal)
        if self.is_integer {
            // Extract integer coefficients
            let coeffs: Vec<i64> = expr
                .terms
                .iter()
                .filter_map(|(_, c)| {
                    if c.denom() == &1 {
                        Some(*c.numer())
                    } else {
                        None
                    }
                })
                .collect();

            // Extract the constant (which is -rhs in expr = 0 form)
            let const_term = if expr.constant.denom() == &1 {
                -*expr.constant.numer()
            } else {
                // Non-integer constant in equality - infeasible for integers.
                // Attribute the contradiction to the actual assertion that
                // caused it (not a hardcoded/arbitrary reason id), so the
                // resulting unsat core cites the real culprit.
                let reason_id = self.add_reason(reason);
                if let Some(&(var, _)) = expr.terms.first() {
                    self.simplex
                        .set_lower(var, Rational64::from_integer(1), reason_id);
                    self.simplex
                        .set_upper(var, Rational64::from_integer(0), reason_id);
                }
                return;
            };

            // Check GCD infeasibility if all coefficients are integers
            if !coeffs.is_empty() && coeffs.len() == expr.terms.len() {
                // Record the integer equality (sum a_i·x_i = const_term) so the
                // cross-constraint Diophantine consistency check can see it.
                let eq_terms: Vec<(VarId, i64)> =
                    expr.terms.iter().map(|(v, c)| (*v, *c.numer())).collect();
                self.int_equalities.push(IntEquation {
                    terms: eq_terms,
                    rhs: const_term,
                });

                // Compute GCD of all coefficients
                let g = coeffs.iter().fold(0i64, |acc, &c| gcd_i64(acc, c.abs()));

                if g > 0 && const_term % g != 0 {
                    // GCD infeasibility detected!
                    // Add contradictory constraints: x >= 1 and x <= 0,
                    // attributed to the actual equality assertion that
                    // caused the contradiction (not a hardcoded reason id)
                    // so `check()`'s unsat core cites the real culprit
                    // instead of whatever the first reason ever added
                    // happened to be.
                    let reason_id = self.add_reason(reason);
                    if let Some(&(var, _)) = expr.terms.first() {
                        self.simplex
                            .set_lower(var, Rational64::from_integer(1), reason_id);
                        self.simplex
                            .set_upper(var, Rational64::from_integer(0), reason_id);
                    }
                    return;
                }
            }
        }

        // Normalize the expression
        self.normalize_expr(&mut expr);

        let reason_id = self.add_reason(reason);
        self.simplex.add_eq(expr, reason_id);
    }

    /// Assert: lhs < rhs (strict inequality)
    /// For LRA, uses infinitesimals: lhs <= rhs - δ
    /// For LIA, transforms to: lhs <= rhs - 1 (since no integer exists between k and k+1)
    pub fn assert_lt(&mut self, lhs: &[(TermId, Rational64)], rhs: Rational64, reason: TermId) {
        // For integer arithmetic, x < k is equivalent to x <= k - 1
        // because there's no integer strictly between k-1 and k
        if self.is_integer {
            // Transform: lhs < rhs becomes lhs <= rhs - 1
            self.assert_le(lhs, rhs - Rational64::one(), reason);
            return;
        }

        // For reals, use delta-rationals
        // lhs < rhs is equivalent to lhs - rhs < 0
        let mut expr = LinExpr::new();

        for (term, coef) in lhs {
            let var = self.intern(*term);
            expr.add_term(var, *coef);
        }
        expr.add_constant(-rhs);

        // Note: We do NOT normalize here because normalize_expr may negate
        // the expression to make the first coefficient positive, which would
        // flip the inequality direction for strict inequalities.

        let reason_id = self.add_reason(reason);
        self.simplex.add_strict_lt(expr, reason_id);
    }

    /// Assert: lhs > rhs (strict inequality)
    /// For LRA, uses infinitesimals: lhs >= rhs + δ
    /// For LIA, transforms to: lhs >= rhs + 1 (since no integer exists between k and k+1)
    pub fn assert_gt(&mut self, lhs: &[(TermId, Rational64)], rhs: Rational64, reason: TermId) {
        // For integer arithmetic, x > k is equivalent to x >= k + 1
        // because there's no integer strictly between k and k+1
        if self.is_integer {
            // Transform: lhs > rhs becomes lhs >= rhs + 1
            self.assert_ge(lhs, rhs + Rational64::one(), reason);
            return;
        }

        // For reals, use delta-rationals
        // lhs > rhs is equivalent to rhs - lhs < 0
        // We build rhs - lhs directly instead of negating lhs - rhs
        // This avoids issues with normalize_expr which ensures positive first coefficient
        let mut expr = LinExpr::new();

        for (term, coef) in lhs {
            let var = self.intern(*term);
            // Add negative coefficient since we want rhs - lhs
            expr.add_term(var, -(*coef));
        }
        // Add +rhs (since we want rhs - lhs, not lhs - rhs)
        expr.add_constant(rhs);

        // Note: We do NOT normalize here because:
        // 1. normalize_expr may negate to make first coefficient positive
        // 2. This would flip the inequality direction
        // 3. For strict inequalities, the sign matters

        let reason_id = self.add_reason(reason);
        self.simplex.add_strict_lt(expr, reason_id);
    }

    /// Get the current value of a variable
    ///
    /// For integer arithmetic (LIA), this properly rounds values that have
    /// infinitesimal components from strict inequalities:
    /// - If value is `r + δ` (positive delta), return `ceil(r)` for integers
    /// - If value is `r - δ` (negative delta), return `floor(r)` for integers
    #[must_use]
    pub fn value(&self, term: TermId) -> Option<Rational64> {
        self.term_to_var.get(&term).map(|&var| {
            if self.is_integer {
                // Prefer the integral assignment found by branch-and-bound when
                // the last check() proved Sat — the raw LP optimum may be
                // fractional for Int variables.
                if let Some(v) = self.lia_model.get(&var) {
                    return *v;
                }
                // Get the full delta-rational value
                let dval = self.simplex.delta_value(var);

                // For integer arithmetic, round based on delta:
                // - Positive delta means we have a strict lower bound (x > r)
                //   so round up to the next integer
                // - Negative delta means we have a strict upper bound (x < r)
                //   so round down to the previous integer
                // - Zero delta means exact value, round to nearest integer
                if dval.delta.is_positive() {
                    // x > r implies x >= ceil(r) for integers
                    // If r is already an integer, we need r + 1
                    let real_val = dval.real;
                    if real_val.is_integer() {
                        Rational64::from_integer(real_val.to_integer() + 1)
                    } else {
                        Rational64::from_integer(real_val.ceil().to_integer())
                    }
                } else if dval.delta.is_negative() {
                    // x < r implies x <= floor(r) for integers
                    // If r is already an integer, we need r - 1
                    let real_val = dval.real;
                    if real_val.is_integer() {
                        Rational64::from_integer(real_val.to_integer() - 1)
                    } else {
                        Rational64::from_integer(real_val.floor().to_integer())
                    }
                } else {
                    // No strict bound, just return the value
                    // Round to nearest integer for consistency
                    dval.real
                }
            } else {
                // For reals, the raw real part is NOT a model: a variable
                // sitting at a strict bound is stored as `r ± δ`, so returning
                // `r` alone reports a witness that violates the very constraint
                // that created it (e.g. `x > 0` would report `x = 0`).
                // Substitute a concrete positive δ₀ that keeps every bound
                // satisfied (see `Simplex::delta_instantiation`).
                let dval = self.simplex.delta_value(var);
                if dval.delta.is_zero() {
                    dval.real
                } else {
                    dval.real + dval.delta * self.simplex.delta_instantiation()
                }
            }
        })
    }

    
    /// Every term the arithmetic solver has internalised (interface / shared).
    pub fn interface_terms(&self) -> &[TermId] {
        &self.var_to_term
    }
/// Soundly determine whether `term = const_value` is *entailed* by the
    /// current arithmetic assignment, and if so return an all-atom reason
    /// (the SAT atoms whose assertion forces the equality).
    ///
    /// Implemented as two infeasibility probes on a scratch simplex scope:
    /// `term >= const_value` holds iff `term < const_value` is infeasible, and
    /// `term <= const_value` holds iff `term > const_value` is infeasible.  The
    /// reason is the union of the two Farkas certificates, with the probe's own
    /// marker reason excluded.  When both hold with no collected reasons, the
    /// equality is entailed by the empty set (level-0 facts) and the full
    /// unsat-core is returned instead.
    ///
    /// Used by the z3-style `final_check` theory propagation to justify the
    /// triangle `le`/`ge` atoms deterministically.
    pub fn fixed_to_const_reason(&mut self, term: TermId, const_value: i64) -> Option<Vec<TermId>> {
        let Some(&var) = self.term_to_var.get(&term) else {
            return None;
        };
        let cv = Rational64::from_integer(const_value);
        let base = self.reasons.len();
        let mut collected: Vec<TermId> = Vec::new();
        // term < const_value infeasible  ⟺  term >= const_value entailed.
        let ge_entailed = {
            self.simplex.push();
            let marker = self.add_reason(term);
            let mut e = LinExpr::new();
            e.add_term(var, Rational64::one());
            e.add_constant(-cv);
            self.simplex.add_strict_lt(e, marker);
            let r = match self.simplex.check() {
                Ok(()) => false,
                Err(reasons) => {
                    for &rid in &reasons {
                        if rid != marker {
                            if let Some(&t) = self.reasons.get(rid as usize) {
                                collected.push(t);
                            }
                        }
                    }
                    true
                }
            };
            self.simplex.pop();
            r
        };
        if !ge_entailed {
            self.reasons.truncate(base);
            self.reason_counter = base as u32;
            return None;
        }
        // term > const_value infeasible  ⟺  term <= const_value entailed.
        let le_entailed = {
            self.simplex.push();
            let marker = self.add_reason(term);
            let mut e = LinExpr::new();
            e.add_term(var, -Rational64::one());
            e.add_constant(cv);
            self.simplex.add_strict_lt(e, marker);
            let r = match self.simplex.check() {
                Ok(()) => false,
                Err(reasons) => {
                    for &rid in &reasons {
                        if rid != marker {
                            if let Some(&t) = self.reasons.get(rid as usize) {
                                collected.push(t);
                            }
                        }
                    }
                    true
                }
            };
            self.simplex.pop();
            r
        };
        self.reasons.truncate(base);
        self.reason_counter = base as u32;
        if !le_entailed {
            return None;
        }
        collected.sort_unstable();
        collected.dedup();
        if collected.is_empty() {
            return Some(self.full_unsat_core());
        }
        Some(collected)
    }

    /// Tighten a rational bound for integer variables
    ///
    /// For integer variables:
    /// - x <= 5.7 becomes x <= 5
    /// - x >= 2.3 becomes x >= 3
    /// - x < 5.0 becomes x <= 4
    /// - x > 2.0 becomes x >= 3
    #[allow(dead_code)]
    fn tighten_bound(&self, bound: Rational64, is_upper: bool) -> Rational64 {
        if !self.is_integer {
            return bound;
        }

        // For upper bounds (<=), floor the value
        // For lower bounds (>=), ceiling the value
        if bound.is_integer() {
            bound
        } else if is_upper {
            // x <= 5.7 becomes x <= 5
            Rational64::from_integer(bound.floor().to_integer())
        } else {
            // x >= 2.3 becomes x >= 3
            Rational64::from_integer(bound.ceil().to_integer())
        }
    }

    /// Maximum branch-and-bound tree depth for the LIA integrality search.
    const LIA_MAX_DEPTH: usize = 512;
    /// Maximum number of branch-and-bound nodes explored before giving up
    /// (returning `Unknown`).  Bounds worst-case exponential search.
    const LIA_MAX_NODES: usize = 20_000;

    /// Collect the simplex variable ids of all interned (Int) terms, sorted for
    /// deterministic branching order.  Slack variables are excluded — we only
    /// branch on the original integer-sorted variables.
    fn interned_int_vars(&self) -> Vec<VarId> {
        let mut vars: Vec<VarId> = self
            .var_to_term
            .iter()
            .filter_map(|term| self.term_to_var.get(term).copied())
            .collect();
        vars.sort_unstable();
        vars.dedup();
        vars
    }

    /// Find the first interned Int variable whose current LP value is fractional.
    fn find_fractional_int_var(&self, int_vars: &[VarId]) -> Option<(VarId, Rational64)> {
        for &var in int_vars {
            let val = self.simplex.value(var);
            if !val.is_integer() {
                return Some((var, val));
            }
        }
        None
    }

    /// Build a sound (over-approximate) unsat core: every assertion reason known
    /// to the solver.  When branch-and-bound proves integer-infeasibility, the
    /// full conjunction of asserted constraints is genuinely inconsistent, so
    /// returning all of them is a valid (if imprecise) conflict explanation.
    fn full_unsat_core(&self) -> Vec<TermId> {
        let mut terms = self.reasons.clone();
        terms.sort_unstable();
        terms.dedup();
        terms
    }

    /// Snapshot the current (integral) LP assignment of every interned Int
    /// variable into `lia_model`.  Called at an integer-feasible leaf so that
    /// `value()` reports the integral model after branch-and-bound unwinds.
    fn snapshot_lia_model(&mut self, int_vars: &[VarId]) {
        self.lia_model.clear();
        for &var in int_vars {
            self.lia_model.insert(var, self.simplex.value(var));
        }
    }

    /// Decide whether the accumulated system of integer equalities has NO
    /// integer solution (a sound, one-sided UNSAT detector).
    ///
    /// Every equality `sum a_i·x_i = b` is an exact integer row.  We run integer
    /// (fraction-free) Gaussian elimination: reducing rows with the identity
    /// `row := (a/g)·row − (b/g)·pivot` (g = gcd of the two pivot-column
    /// entries) produces rows that are integer linear combinations of the
    /// originals, hence consequences that every integer solution must satisfy.
    /// For any resulting row `sum c_j·x_j = d`, an integer solution requires
    /// `gcd(c_j) | d`; if that fails — or a row reduces to `0 = d` with `d ≠ 0` —
    /// the whole system is integer-infeasible.
    ///
    /// This catches cross-constraint parity infeasibility such as
    /// `y = 2x ∧ y = 2z + 1` (⇒ `2x − 2z = 1`, and `gcd(2,2) = 2 ∤ 1`), which
    /// per-equation GCD reasoning and unbounded branch-and-bound cannot.
    ///
    /// The check is *sound but incomplete*: it only ever concludes UNSAT.  If an
    /// intermediate value would overflow `i128`, or the system is too large, it
    /// conservatively returns `false` (defer to branch-and-bound).
    fn int_equalities_infeasible(&self) -> bool {
        if self.int_equalities.is_empty() {
            return false;
        }

        // Assign a dense column index to every variable that appears.
        let mut col_of: FxHashMap<VarId, usize> = FxHashMap::default();
        for eq in &self.int_equalities {
            for &(v, _) in &eq.terms {
                let next = col_of.len();
                col_of.entry(v).or_insert(next);
            }
        }
        let cols = col_of.len();
        let rows = self.int_equalities.len();

        // Bound the work: skip very large systems (defer to branch-and-bound).
        if cols == 0 || rows.saturating_mul(cols) > 200_000 {
            return false;
        }

        // Dense augmented matrix: last entry of each row is the RHS.
        let mut mat: Vec<Vec<i128>> = vec![vec![0i128; cols + 1]; rows];
        for (r, eq) in self.int_equalities.iter().enumerate() {
            for &(v, c) in &eq.terms {
                if let Some(&col) = col_of.get(&v) {
                    mat[r][col] += c as i128;
                }
            }
            mat[r][cols] = eq.rhs as i128;
        }

        // Fraction-free Gaussian elimination.
        let mut pivot_row = 0usize;
        for col in 0..cols {
            // Find a pivot at or below `pivot_row` with a nonzero entry.
            let Some(sel) = (pivot_row..rows).find(|&r| mat[r][col] != 0) else {
                continue;
            };
            mat.swap(pivot_row, sel);

            // Snapshot the pivot row to avoid aliasing two rows of `mat`.
            let pivot = mat[pivot_row].clone();
            let a = pivot[col];

            // Eliminate this column from every other row.
            for (r, row) in mat.iter_mut().enumerate() {
                if r == pivot_row || row[col] == 0 {
                    continue;
                }
                let b = row[col];
                let g = gcd_i128(a, b);
                let fa = a / g; // scale for row r
                let fb = b / g; // scale for pivot
                for (k, &pv) in pivot.iter().enumerate().skip(col) {
                    let lhs = match row[k].checked_mul(fa) {
                        Some(v) => v,
                        None => return false, // overflow → cannot decide
                    };
                    let rhs = match pv.checked_mul(fb) {
                        Some(v) => v,
                        None => return false,
                    };
                    row[k] = match lhs.checked_sub(rhs) {
                        Some(v) => v,
                        None => return false,
                    };
                }
            }

            pivot_row += 1;
            if pivot_row == rows {
                break;
            }
        }

        // Consequence check: each row must be integer-satisfiable on its own.
        for row in &mat {
            let mut g = 0i128;
            for &c in &row[..cols] {
                g = gcd_i128(g, c);
            }
            let d = row[cols];
            if g == 0 {
                // 0 = d with d ≠ 0 is inconsistent (even over the rationals).
                if d != 0 {
                    return true;
                }
            } else if d % g != 0 {
                // gcd of coefficients does not divide the constant ⇒ no integer
                // solution to this consequence ⇒ system integer-infeasible.
                return true;
            }
        }

        false
    }

    /// Entry point for the LIA integrality search (branch-and-bound).
    ///
    /// Precondition: the LP relaxation is feasible and not resource-limited.
    fn lia_branch_and_bound(&mut self) -> Result<TheoryResult> {
        // Cheap, sound integer-equality consistency check first — resolves
        // cross-constraint parity infeasibility that branch-and-bound over
        // unbounded variables would otherwise only be able to report as Unknown.
        if self.int_equalities_infeasible() {
            return Ok(TheoryResult::Unsat(self.full_unsat_core()));
        }
        let int_vars = self.interned_int_vars();
        let mut nodes: usize = 0;
        self.bnb_recurse(&int_vars, 0, &mut nodes)
    }

    /// Recursive branch-and-bound over integer variables.
    ///
    /// Uses balanced simplex push/pop so no branch constraint leaks into the
    /// caller's decision level.  The satisfying integral assignment is captured
    /// into `lia_model` at the feasible leaf (before the pushes unwind), so
    /// `value()` can report it afterwards.
    ///
    /// Returns:
    /// - `Sat` if an integral assignment is found;
    /// - `Unsat(core)` if BOTH branches on the fractional variable are
    ///   infeasible (integer-infeasible);
    /// - `Unknown` if the depth/node budget is exhausted, or a sub-solve hit the
    ///   simplex pivot limit — never a fabricated Sat/Unsat.
    fn bnb_recurse(
        &mut self,
        int_vars: &[VarId],
        depth: usize,
        nodes: &mut usize,
    ) -> Result<TheoryResult> {
        if depth > Self::LIA_MAX_DEPTH || *nodes > Self::LIA_MAX_NODES {
            return Ok(TheoryResult::Unknown);
        }
        *nodes += 1;

        // Find a fractional Int variable at the current LP optimum.
        let (var, value) = match self.find_fractional_int_var(int_vars) {
            None => {
                // Fully integral leaf: record the model, then report Sat.
                self.snapshot_lia_model(int_vars);
                return Ok(TheoryResult::Sat);
            }
            Some(vv) => vv,
        };

        let floor_v = value.floor();
        let ceil_v = value.ceil();

        // Track whether any explored branch was left unresolved (Unknown) so we
        // never collapse an Unknown into a spurious Unsat.
        let mut saw_unknown = false;

        // Branch down: var <= floor(value).
        self.simplex.push();
        self.simplex.set_upper(var, floor_v, 0);
        let down = self.explore_branch(int_vars, depth, nodes)?;
        self.simplex.pop();
        match down {
            BranchOutcome::Sat => return Ok(TheoryResult::Sat),
            BranchOutcome::Unknown => saw_unknown = true,
            BranchOutcome::Infeasible => {}
        }

        // Branch up: var >= ceil(value).
        self.simplex.push();
        self.simplex.set_lower(var, ceil_v, 0);
        let up = self.explore_branch(int_vars, depth, nodes)?;
        self.simplex.pop();
        match up {
            BranchOutcome::Sat => return Ok(TheoryResult::Sat),
            BranchOutcome::Unknown => saw_unknown = true,
            BranchOutcome::Infeasible => {}
        }

        // Neither branch produced Sat.  If any branch was left unresolved we must
        // answer Unknown; only when both branches are proven infeasible may we
        // conclude integer-infeasibility (Unsat).
        if saw_unknown {
            Ok(TheoryResult::Unknown)
        } else {
            Ok(TheoryResult::Unsat(self.full_unsat_core()))
        }
    }

    /// Explore the current (already-constrained) branch: re-solve the LP and, if
    /// feasible and not resource-limited, recurse into branch-and-bound.
    ///
    /// The caller is responsible for the surrounding `push`/`pop`.
    fn explore_branch(
        &mut self,
        int_vars: &[VarId],
        depth: usize,
        nodes: &mut usize,
    ) -> Result<BranchOutcome> {
        match self.simplex.check() {
            Ok(()) => {
                if self.simplex.resource_limit_reached() {
                    // LP unresolved within the pivot budget — Unknown, not Sat.
                    Ok(BranchOutcome::Unknown)
                } else {
                    Ok(match self.bnb_recurse(int_vars, depth + 1, nodes)? {
                        TheoryResult::Sat => BranchOutcome::Sat,
                        TheoryResult::Unsat(_) => BranchOutcome::Infeasible,
                        _ => BranchOutcome::Unknown,
                    })
                }
            }
            // LP infeasible on this branch: a proven dead end.
            Err(_) => Ok(BranchOutcome::Infeasible),
        }
    }

    /// Tighten constraints for integer arithmetic
    ///
    /// Returns true if any tightening was performed
    pub fn tighten_constraints(&mut self) -> bool {
        if !self.is_integer {
            return false;
        }

        // In a full implementation, we would:
        // 1. Iterate through all bounds
        // 2. Apply tightening rules
        // 3. Propagate tightened bounds
        //
        // For now, tightening is applied during assertion
        false
    }
}

impl Theory for ArithSolver {
    fn id(&self) -> TheoryId {
        if self.is_integer {
            TheoryId::LIA
        } else {
            TheoryId::LRA
        }
    }

    fn name(&self) -> &str {
        if self.is_integer { "LIA" } else { "LRA" }
    }

    fn can_handle(&self, _term: TermId) -> bool {
        // In a full implementation, check if term is arithmetic
        true
    }

    fn assert_true(&mut self, term: TermId) -> Result<TheoryResult> {
        // In a full implementation, parse the term and add constraints
        let _ = self.intern(term);
        Ok(TheoryResult::Sat)
    }

    fn assert_false(&mut self, term: TermId) -> Result<TheoryResult> {
        let _ = self.intern(term);
        Ok(TheoryResult::Sat)
    }

    fn check(&mut self) -> Result<TheoryResult> {
        // Any previously recorded integral model is stale for this fresh check.
        self.lia_model.clear();

        // Step 1: solve the LP (real) relaxation.
        match self.simplex.check() {
            Ok(()) => {
                // The pivot budget may have been exhausted without a definitive
                // answer.  In that case the assignment is NOT a model — report
                // Unknown rather than a fabricated Sat.
                if self.simplex.resource_limit_reached() {
                    return Ok(TheoryResult::Unknown);
                }
            }
            Err(reasons) => {
                // `reasons` and the simplex constraints that carry these ids are
                // pushed and popped together, so every id must resolve.  A miss
                // would silently shrink the core — and a conflict explanation
                // that loses one of its causes is not weaker, it is wrong — so
                // assert it loudly and, in release, fall back to the full set of
                // known reasons rather than a truncated one.
                let mut terms: Vec<TermId> = Vec::with_capacity(reasons.len());
                for &r in &reasons {
                    match self.reasons.get(r as usize).copied() {
                        Some(term) => terms.push(term),
                        None => {
                            debug_assert!(
                                false,
                                "simplex reported reason id {r} with no recorded term \
                                 (only {} known): the conflict core would lose a cause",
                                self.reasons.len()
                            );
                            return Ok(TheoryResult::Unsat(self.full_unsat_core()));
                        }
                    }
                }
                return Ok(TheoryResult::Unsat(terms));
            }
        }

        // Step 2 (LRA): the LP relaxation is exact — feasible LP ⇒ Sat.
        if !self.is_integer {
            return Ok(TheoryResult::Sat);
        }

        // Step 3 (LIA): the LP relaxation being feasible is NOT sufficient — a
        // fractional assignment over Int variables must be resolved by
        // branch-and-bound before we may answer Sat.  Otherwise integer-
        // infeasible-but-LP-feasible systems (e.g. y = 2x ∧ y = 2z+1) would be
        // wrongly reported Sat with fractional values for Int terms.
        self.lia_branch_and_bound()
    }

    fn push(&mut self) {
        self.context_stack.push(ContextState {
            num_vars: self.var_to_term.len(),
            num_reasons: self.reasons.len(),
            num_shared_equalities: self.shared_equalities.len(),
            num_int_equalities: self.int_equalities.len(),
        });
        self.simplex.push();
    }

    fn pop(&mut self) {
        if let Some(state) = self.context_stack.pop() {
            // Roll back the term→var interning done since the matching push.
            //
            // `var_to_term` is the intern trail: `intern` appends exactly one
            // entry per fresh variable and the pushed index equals the VarId
            // (`simplex.new_var()` returns the current array length). So the
            // terms interned inside this scope are precisely the tail beyond
            // `state.num_vars`. Draining that tail and removing each term from
            // `term_to_var` keeps the two maps consistent in O(delta).
            //
            // This is load-bearing for correctness: `simplex.pop()` recycles
            // VarIds (it shrinks its per-variable arrays), so a `term_to_var`
            // entry left dangling here would make `intern` replay a stale index
            // that now belongs to a different (or not-yet-created) variable.
            let cut = state.num_vars.min(self.var_to_term.len());
            let removed: Vec<TermId> = self.var_to_term.drain(cut..).collect();
            for term in removed {
                self.term_to_var.remove(&term);
            }
            self.reasons.truncate(state.num_reasons);
            self.reason_counter = state.num_reasons as u32;
            self.shared_equalities.truncate(state.num_shared_equalities);
            self.int_equalities.truncate(state.num_int_equalities);
            // The LIA branch-and-bound model is a snapshot of the *last* check's
            // integral assignment, keyed by VarId. Because VarIds are recycled
            // across this pop, a leftover entry could be misread by `value()`
            // for a freshly interned term that reuses the index before the next
            // `check()` repopulates it. It is only valid immediately after a
            // successful `check()`, so drop it on backtrack.
            self.lia_model.clear();
            self.simplex.pop();
        }
    }

    fn reset(&mut self) {
        self.simplex.reset();
        self.term_to_var.clear();
        self.var_to_term.clear();
        self.reason_counter = 0;
        self.reasons.clear();
        self.context_stack.clear();
        self.shared_equalities.clear();
        self.lia_model.clear();
        self.int_equalities.clear();
    }

    fn get_model(&self) -> Vec<(TermId, TermId)> {
        // Return variable -> value pairs
        // In a full implementation, we'd create value terms
        Vec::new()
    }
}

impl TheoryCombination for ArithSolver {
    fn notify_equality(&mut self, eq: EqualityNotification) -> bool {
        // Check if both terms are relevant to arithmetic
        let lhs_var = self.term_to_var.get(&eq.lhs).copied();
        let rhs_var = self.term_to_var.get(&eq.rhs).copied();

        if let (Some(lhs), Some(rhs)) = (lhs_var, rhs_var) {
            // Enforce lhs = rhs in the simplex by asserting lhs - rhs <= 0 and rhs - lhs <= 0.
            // This is equivalent to lhs - rhs = 0, i.e., add_eq(lhs - rhs, 0).
            let reason_id = if let Some(r) = eq.reason {
                self.add_reason(r)
            } else {
                self.add_reason(eq.lhs)
            };

            // Build expression: lhs - rhs
            let mut expr_le = LinExpr::new();
            expr_le.add_term(lhs, Rational64::one());
            expr_le.add_term(rhs, -Rational64::one());
            // lhs - rhs <= 0
            self.simplex.add_le(expr_le, reason_id);

            // Build expression: rhs - lhs
            let mut expr_ge = LinExpr::new();
            expr_ge.add_term(rhs, Rational64::one());
            expr_ge.add_term(lhs, -Rational64::one());
            // rhs - lhs <= 0  (i.e., lhs - rhs >= 0)
            self.simplex.add_le(expr_ge, reason_id);

            // Record so that get_shared_equalities can return it
            self.shared_equalities.push(eq);

            true
        } else {
            // Terms not relevant to this arithmetic solver
            false
        }
    }

    fn get_shared_equalities(&self) -> Vec<EqualityNotification> {
        // Sound Nelson-Oppen propagation (model-based + entailment verification).
        //
        // Algorithm:
        // a) Collect interface variables (those mapped from interned terms).
        // b) Group by current delta_value in the simplex model — same-valued vars
        //    are candidates for equality.
        // c) For each adjacent same-bucket pair (x, y):
        //    i)  Probe: push, add x - y < 0 (strict), check → if UNSAT then
        //        "x < y" is infeasible → entailed_ge holds.
        //    ii) Probe: push, add y - x < 0 (strict), check → if UNSAT then
        //        "x > y" is infeasible → entailed_le holds.
        //    iii) Emit equality only if BOTH probes are UNSAT.
        // d) Also include equalities accumulated via notify_equality.

        // We need a mutable borrow on the simplex for probing, so we collect
        // results in a separate step.  Use an immutable reference for reading
        // variable assignments first, then do mutable probing.

        // Need &mut self for probing; but the trait signature is &self.
        // We work around this by cloning the accumulated `shared_equalities` and
        // returning them — the model-based probing path requires &mut self, so we
        // use an internal helper that takes &mut ArithSolver.
        self.shared_equalities.clone()
    }

    fn is_relevant(&self, term: TermId) -> bool {
        // Check if this term has been interned in the arithmetic solver
        self.term_to_var.contains_key(&term)
    }
}

impl ArithSolver {
    /// Sound Nelson-Oppen equality propagation.
    ///
    /// Returns entailed equalities between interface terms that are shared between
    /// this arithmetic theory and other theories in the Nelson-Oppen combination.
    ///
    /// Only emits `x = y` if BOTH `x < y` and `x > y` are infeasible in the
    /// current simplex state — this guarantees soundness: no false equality is
    /// ever propagated.
    ///
    /// Uses probe-and-pop to avoid permanently modifying the simplex state.
    pub fn derive_shared_equalities(&mut self) -> Vec<EqualityNotification> {
        let num_interface_terms = self.var_to_term.len();
        if num_interface_terms < 2 {
            return self.shared_equalities.clone();
        }

        // Collect (delta_value, VarId, TermId) for all interned variables.
        let mut candidates: Vec<(super::delta::DeltaRational, VarId, TermId)> = self
            .var_to_term
            .iter()
            .enumerate()
            .filter_map(|(idx, &term)| {
                // term_to_var maps TermId → VarId; we stored in var_to_term in order
                let var = self.term_to_var.get(&term).copied()?;
                let _ = idx; // suppress warning
                let dval = self.simplex.delta_value(var);
                Some((dval, var, term))
            })
            .collect();

        if candidates.len() < 2 {
            return self.shared_equalities.clone();
        }

        // Sort by current assignment value so same-valued pairs are adjacent.
        candidates.sort_by_key(|a| a.0);

        let mut result = self.shared_equalities.clone();

        // Check adjacent same-bucket pairs.
        let mut i = 0;
        while i < candidates.len() {
            // Find end of this bucket (same delta_value)
            let bucket_start = i;
            while i < candidates.len() && candidates[i].0 == candidates[bucket_start].0 {
                i += 1;
            }
            let bucket = &candidates[bucket_start..i];

            // For each adjacent pair in the bucket, probe for entailment.
            for pair_idx in 0..bucket.len().saturating_sub(1) {
                let (_, var_x, term_x) = bucket[pair_idx];
                let (_, var_y, term_y) = bucket[pair_idx + 1];

                // Probe 1: Can x < y? (i.e., x - y < 0)
                // If UNSAT → x >= y is entailed (x cannot be strictly less than y).
                let entailed_ge = {
                    self.simplex.push();
                    // Add strict x - y < 0
                    let mut expr = LinExpr::new();
                    expr.add_term(var_x, Rational64::one());
                    expr.add_term(var_y, -Rational64::one());
                    self.simplex.add_strict_lt(expr, 0);
                    let infeasible = self.simplex.check().is_err();
                    self.simplex.pop();
                    infeasible
                };

                // Probe 2: Can x > y? (i.e., y - x < 0)
                // If UNSAT → x <= y is entailed (x cannot be strictly greater than y).
                let entailed_le = {
                    self.simplex.push();
                    // Add strict y - x < 0
                    let mut expr = LinExpr::new();
                    expr.add_term(var_y, Rational64::one());
                    expr.add_term(var_x, -Rational64::one());
                    self.simplex.add_strict_lt(expr, 0);
                    let infeasible = self.simplex.check().is_err();
                    self.simplex.pop();
                    infeasible
                };

                // Both strict directions infeasible → x = y is entailed.
                if entailed_ge && entailed_le {
                    // Avoid duplicates from shared_equalities.
                    let already_known = result.iter().any(|eq| {
                        (eq.lhs == term_x && eq.rhs == term_y)
                            || (eq.lhs == term_y && eq.rhs == term_x)
                    });
                    if !already_known {
                        result.push(EqualityNotification {
                            lhs: term_x,
                            rhs: term_y,
                            reason: None,
                        });
                    }
                }
            }
        }

        result
    }

    /// Group the interface (arith-interned) terms by their current simplex
    /// model value, returning every group of size >= 2 (terms the arithmetic
    /// model currently holds *equal*).  Cheap -- no feasibility probe, just a
    /// value read and a sort.  These groups are the candidate set for
    /// [`Self::entailed_equal_reason`]; the caller (which knows the EUF class
    /// structure) filters out pairs already equal in EUF before paying for a
    /// probe, which is what keeps theory combination affordable on large
    /// interfaces.
    pub fn interface_value_buckets(&self) -> Vec<Vec<TermId>> {
        if self.var_to_term.len() < 2 {
            return Vec::new();
        }
        let mut candidates: Vec<(super::delta::DeltaRational, TermId)> = self
            .var_to_term
            .iter()
            .filter_map(|&term| {
                let var = self.term_to_var.get(&term).copied()?;
                Some((self.simplex.delta_value(var), term))
            })
            .collect();
        if candidates.len() < 2 {
            return Vec::new();
        }
        candidates.sort_by(|a, b| a.0.cmp(&b.0));
        let mut buckets: Vec<Vec<TermId>> = Vec::new();
        let mut i = 0;
        while i < candidates.len() {
            let start = i;
            while i < candidates.len() && candidates[i].0 == candidates[start].0 {
                i += 1;
            }
            if i - start >= 2 {
                buckets.push(candidates[start..i].iter().map(|(_, t)| *t).collect());
            }
        }
        buckets
    }

    /// Sound single-pair equality-entailment probe with Farkas reason.
    ///
    /// Returns `Some(reason)` iff arithmetic *entails* `x = y` -- both `x < y`
    /// and `x > y` are infeasible in the current simplex state -- where `reason`
    /// is the set of already-asserted comparison atoms whose conjunction forces
    /// the equality (the union of the two infeasibility certificates).  The
    /// equality is therefore a *deduction*: propagating it to another theory
    /// (merging in EUF) is sound as long as `reason` is carried into any
    /// conflict explanation.  `None` means arithmetic does not entail the
    /// equality (the model merely happened to assign the same value).
    ///
    /// Two `push`/probe/`pop` rounds so the solver's incremental state is
    /// untouched regardless of the outcome.
    /// Sound comparison-entailment probe (bound propagation core).
    ///
    /// For a comparison atom `sum(coef_i·x_i) <op> constant`, returns
    /// `Some((truth, reason))` iff arithmetic *forces* the atom to `truth`
    /// (true or false) — implemented as two push/check/pop probes: assert the
    /// atom (if infeasible, FALSE is forced) and assert its negation (if
    /// infeasible, TRUE is forced).  `reason` is the Farkas certificate.
    /// Sound by construction: the probes are on a scratch simplex scope.
    ///
    /// `less`: `sum ≤/< c` (Le/Lt) vs `sum ≥/> c` (Ge/Gt).
    /// `strict`: strict inequality (Lt/Gt) vs non-strict (Le/Ge).
    #[allow(clippy::too_many_arguments)]
    pub fn comparison_entailed_reason(
        &mut self,
        terms: &[(TermId, Rational64)],
        constant: Rational64,
        less: bool,
        strict: bool,
    ) -> Option<(bool, Vec<TermId>)> {
        let mut e = LinExpr::constant(-constant);
        for &(term, coef) in terms {
            let Some(&var) = self.term_to_var.get(&term) else { return None; };
            e.add_term(var, coef);
        }
        let mut neg_e = LinExpr::constant(constant);
        for &(term, coef) in terms {
            if let Some(&var) = self.term_to_var.get(&term) {
                neg_e.add_term(var, -coef);
            }
        }
        let base = self.reasons.len();
        let probe = |simplex: &mut Simplex, expr: LinExpr, is_strict: bool| -> Option<Vec<u32>> {
            simplex.push();
            if is_strict { simplex.add_strict_lt(expr, 0); } else { simplex.add_le(expr, 0); }
            let r = simplex.check().err();
            simplex.pop();
            r
        };
        let (atom_expr, atom_strict, neg_expr, neg_strict) = match (less, strict) {
            (true, false) => (e.clone(), false, neg_e.clone(), true),
            (true, true) => (e.clone(), true, neg_e.clone(), false),
            (false, false) => (neg_e.clone(), false, e.clone(), true),
            (false, true) => (neg_e.clone(), true, e.clone(), false),
        };
        if let Some(reasons) = probe(&mut self.simplex, neg_expr, neg_strict) {
            return Some((true, self.reasons_from_ids(&reasons, base)));
        }
        if let Some(reasons) = probe(&mut self.simplex, atom_expr, atom_strict) {
            return Some((false, self.reasons_from_ids(&reasons, base)));
        }
        None
    }

    /// Collect reason terms from simplex Farkas IDs, truncate scratch buffer.
    fn reasons_from_ids(&mut self, ids: &[u32], base: usize) -> Vec<TermId> {
        let mut out: Vec<TermId> = Vec::new();
        for &rid in ids {
            if let Some(&t) = self.reasons.get(rid as usize) { out.push(t); }
        }
        self.reasons.truncate(base);
        self.reason_counter = base as u32;
        out.sort_unstable();
        out.dedup();
        if out.is_empty() { out = self.full_unsat_core(); }
        out
    }

    /// Sound disequality-entailment probe.  Returns `Some(reason)` iff
    /// arithmetic forces `x ≠ y` (i.e. `x = y` is infeasible).  cvc5's
    /// `watchedVariableCannotBeZero` analogue.
    pub fn entailed_disequal_reason(&mut self, x: TermId, y: TermId) -> Option<Vec<TermId>> {
        let (Some(var_x), Some(var_y)) =
            (self.term_to_var.get(&x).copied(), self.term_to_var.get(&y).copied())
        else { return None; };
        let base = self.reasons.len();
        self.simplex.push();
        let mut e1 = LinExpr::new();
        e1.add_term(var_x, Rational64::one());
        e1.add_term(var_y, -Rational64::one());
        self.simplex.add_le(e1, 0);
        let mut e2 = LinExpr::new();
        e2.add_term(var_y, Rational64::one());
        e2.add_term(var_x, -Rational64::one());
        self.simplex.add_le(e2, 0);
        let conflict = self.simplex.check().err();
        self.simplex.pop();
        let reasons = conflict?;
        Some(self.reasons_from_ids(&reasons, base))
    }

    pub fn entailed_equal_reason(
        &mut self,
        x: TermId,
        y: TermId,
    ) -> Option<Vec<TermId>> {
        let (Some(var_x), Some(var_y)) =
            (self.term_to_var.get(&x).copied(), self.term_to_var.get(&y).copied())
        else {
            return None;
        };
        let base = self.reasons.len();
        // x < y infeasible  <=>  x >= y entailed.
        let ge_reasons = {
            self.simplex.push();
            let mut e = LinExpr::new();
            e.add_term(var_x, Rational64::one());
            e.add_term(var_y, -Rational64::one());
            self.simplex.add_strict_lt(e, 0);
            let r = self.simplex.check().err();
            self.simplex.pop();
            r
        };
        let ge_reasons = ge_reasons?;
        // x > y infeasible  <=>  x <= y entailed.
        let le_reasons = {
            self.simplex.push();
            let mut e = LinExpr::new();
            e.add_term(var_y, Rational64::one());
            e.add_term(var_x, -Rational64::one());
            self.simplex.add_strict_lt(e, 0);
            let r = self.simplex.check().err();
            self.simplex.pop();
            r
        };
        let le_reasons = le_reasons?;
        let mut reason_terms: Vec<TermId> = Vec::new();
        for &rid in ge_reasons.iter().chain(le_reasons.iter()) {
            if let Some(&t) = self.reasons.get(rid as usize) {
                reason_terms.push(t);
            }
        }
        self.reasons.truncate(base);
        self.reason_counter = base as u32;
        reason_terms.sort_unstable();
        reason_terms.dedup();
        if reason_terms.is_empty() {
            // Entailed at decision level 0 (no atom reason): justify with the
            // full unsat-core so a conflict citing this merge is explainable.
            reason_terms = self.full_unsat_core();
        }
        Some(reason_terms)
    }

}

#[cfg(test)]
mod tests {
    use super::*;
    use num_traits::{One, Zero};

    #[test]
    fn test_arith_basic() {
        let mut solver = ArithSolver::lra();

        let x = TermId::new(1);
        let y = TermId::new(2);
        let reason = TermId::new(100);

        // x >= 0
        solver.assert_ge(
            &[(x, Rational64::one())],
            Rational64::from_integer(0),
            reason,
        );

        // y >= 0
        solver.assert_ge(
            &[(y, Rational64::one())],
            Rational64::from_integer(0),
            reason,
        );

        // x + y <= 10
        solver.assert_le(
            &[(x, Rational64::one()), (y, Rational64::one())],
            Rational64::from_integer(10),
            reason,
        );

        let result = solver.check().expect("test operation should succeed");
        assert!(matches!(result, TheoryResult::Sat));
    }

    #[test]
    fn test_arith_unsat() {
        let mut solver = ArithSolver::lra();

        let x = TermId::new(1);
        let reason = TermId::new(100);

        // x >= 10
        solver.assert_ge(
            &[(x, Rational64::one())],
            Rational64::from_integer(10),
            reason,
        );

        // x <= 5
        solver.assert_le(
            &[(x, Rational64::one())],
            Rational64::from_integer(5),
            reason,
        );

        let result = solver.check().expect("test operation should succeed");
        assert!(matches!(result, TheoryResult::Unsat(_)));
    }

    #[test]
    fn test_arith_strict_inequality() {
        let mut solver = ArithSolver::lra();

        let x = TermId::new(1);
        let reason = TermId::new(100);

        // x > 0 (strict)
        solver.assert_gt(
            &[(x, Rational64::one())],
            Rational64::from_integer(0),
            reason,
        );

        // x < 10 (strict)
        solver.assert_lt(
            &[(x, Rational64::one())],
            Rational64::from_integer(10),
            reason,
        );

        let result = solver.check().expect("test operation should succeed");
        assert!(matches!(result, TheoryResult::Sat));
    }

    #[test]
    fn test_arith_strict_unsat() {
        let mut solver = ArithSolver::lra();

        let x = TermId::new(1);
        let reason = TermId::new(100);

        // x >= 5
        solver.assert_ge(
            &[(x, Rational64::one())],
            Rational64::from_integer(5),
            reason,
        );

        // x < 5 (strict) - should be unsatisfiable with x >= 5
        solver.assert_lt(
            &[(x, Rational64::one())],
            Rational64::from_integer(5),
            reason,
        );

        let result = solver.check().expect("test operation should succeed");
        assert!(matches!(result, TheoryResult::Unsat(_)));
    }

    #[test]
    fn test_coefficient_normalization_lia() {
        let mut solver = ArithSolver::lia();

        let x = TermId::new(1);
        let y = TermId::new(2);
        let reason = TermId::new(100);

        // 2x + 4y <= 10 should be normalized to x + 2y <= 5 (GCD = 2)
        solver.assert_le(
            &[
                (x, Rational64::from_integer(2)),
                (y, Rational64::from_integer(4)),
            ],
            Rational64::from_integer(10),
            reason,
        );

        // The solver should handle this correctly
        let result = solver.check().expect("test operation should succeed");
        assert!(matches!(result, TheoryResult::Sat));
    }

    #[test]
    fn test_coefficient_normalization_sign() {
        let solver = ArithSolver::lra();

        let _x = TermId::new(1);
        let _y = TermId::new(2);

        // Test normalization ensures first coefficient is positive
        let mut expr = LinExpr::new();
        expr.add_term(0, Rational64::from_integer(-3));
        expr.add_term(1, Rational64::from_integer(2));

        solver.normalize_expr(&mut expr);

        // After normalization, first coefficient should be positive
        if let Some((_, c)) = expr.terms.first() {
            assert!(c > &Rational64::zero());
        }
    }

    #[test]
    fn test_gcd_computation() {
        assert_eq!(gcd_i64(12, 8), 4);
        assert_eq!(gcd_i64(15, 25), 5);
        assert_eq!(gcd_i64(7, 13), 1);
        assert_eq!(gcd_i64(0, 5), 5);
        assert_eq!(gcd_i64(5, 0), 5);
        assert_eq!(gcd_i64(-12, 8), 4);
        assert_eq!(gcd_i64(12, -8), 4);
    }

    // Audit regression (theories-arith): the GCD-infeasibility path in
    // `assert_eq` used to fabricate its contradictory bounds with a
    // hardcoded `reason` id of `0`, so the resulting UNSAT conflict always
    // cited whatever the FIRST reason ever added happened to be, instead of
    // the actual assertion that caused the contradiction. Assert an
    // unrelated, satisfiable constraint first (populating reason id `0`
    // with an unrelated term), then a GCD-infeasible equality with a
    // DIFFERENT reason term, and confirm the conflict cites the real
    // culprit.
    #[test]
    fn audit_gcd_infeasibility_conflict_cites_real_reason() {
        let mut solver = ArithSolver::lia();

        let x = TermId::new(10);
        let y = TermId::new(20);
        let unrelated_reason = TermId::new(1);
        let real_reason = TermId::new(2);

        // x >= 0: satisfiable, unrelated to the GCD conflict. If the old
        // hardcoded-reason-0 bug were still present, this becomes
        // `self.reasons[0]`, and the GCD conflict below would wrongly cite
        // it instead of `real_reason`.
        solver.assert_ge(
            &[(x, Rational64::one())],
            Rational64::zero(),
            unrelated_reason,
        );

        // 2y = 7 has no integer solution: gcd(2) = 2 does not divide 7.
        solver.assert_eq(
            &[(y, Rational64::from_integer(2))],
            Rational64::from_integer(7),
            real_reason,
        );

        let result = solver.check().expect("check should succeed");
        match result {
            TheoryResult::Unsat(conflict) => {
                assert!(
                    conflict.contains(&real_reason),
                    "GCD-infeasibility conflict must cite the actual violating \
                     assertion {real_reason:?}, got {conflict:?}"
                );
            }
            other => panic!("expected Unsat (2y=7 is GCD-infeasible over integers), got {other:?}"),
        }
    }

    #[test]
    fn test_bound_tightening_lia() {
        let solver = ArithSolver::lia();

        // Upper bound tightening: x <= 5.7 -> x <= 5
        let tightened = solver.tighten_bound(Rational64::new(57, 10), true);
        assert_eq!(tightened, Rational64::from_integer(5));

        // Lower bound tightening: x >= 2.3 -> x >= 3
        let tightened = solver.tighten_bound(Rational64::new(23, 10), false);
        assert_eq!(tightened, Rational64::from_integer(3));

        // Integer bounds don't change
        let tightened = solver.tighten_bound(Rational64::from_integer(5), true);
        assert_eq!(tightened, Rational64::from_integer(5));
    }

    #[test]
    fn test_bound_tightening_lra() {
        let solver = ArithSolver::lra();

        // No tightening for real arithmetic
        let bound = Rational64::new(57, 10);
        let tightened = solver.tighten_bound(bound, true);
        assert_eq!(tightened, bound);
    }

    #[test]
    fn test_tighten_constraints() {
        let mut solver_lia = ArithSolver::lia();
        let mut solver_lra = ArithSolver::lra();

        // For now, this always returns false (tightening happens during assertion)
        assert!(!solver_lia.tighten_constraints());
        assert!(!solver_lra.tighten_constraints());
    }

    /// Test that x > 5 AND x < 6 is UNSAT for integers (no integer in open interval (5,6))
    /// This is the bug report test case: strict inequalities must be transformed for LIA
    #[test]
    fn test_lia_strict_inequality_empty_interval() {
        let mut solver = ArithSolver::lia();

        let x = TermId::new(1);
        let reason = TermId::new(100);

        // x > 5 (for integers, this becomes x >= 6)
        solver.assert_gt(
            &[(x, Rational64::one())],
            Rational64::from_integer(5),
            reason,
        );

        // x < 6 (for integers, this becomes x <= 5)
        solver.assert_lt(
            &[(x, Rational64::one())],
            Rational64::from_integer(6),
            reason,
        );

        // Should be UNSAT: x >= 6 AND x <= 5 is impossible
        let result = solver.check().expect("test operation should succeed");
        assert!(
            matches!(result, TheoryResult::Unsat(_)),
            "Expected UNSAT for x > 5 AND x < 6 in LIA, got {:?}",
            result
        );
    }

    /// Test that x > 5 AND x < 6 is SAT for reals (5.5 is a valid solution)
    #[test]
    fn test_lra_strict_inequality_has_solution() {
        let mut solver = ArithSolver::lra();

        let x = TermId::new(1);
        let reason = TermId::new(100);

        // x > 5
        solver.assert_gt(
            &[(x, Rational64::one())],
            Rational64::from_integer(5),
            reason,
        );

        // x < 6
        solver.assert_lt(
            &[(x, Rational64::one())],
            Rational64::from_integer(6),
            reason,
        );

        // Should be SAT for reals: x = 5.5 is a valid solution
        let result = solver.check().expect("test operation should succeed");
        assert!(
            matches!(result, TheoryResult::Sat),
            "Expected SAT for x > 5 AND x < 6 in LRA, got {:?}",
            result
        );
    }

    /// Test x >= 5 AND x <= 5 with strict bounds in LIA
    #[test]
    fn test_lia_strict_at_boundary() {
        let mut solver = ArithSolver::lia();

        let x = TermId::new(1);
        let reason = TermId::new(100);

        // x >= 5
        solver.assert_ge(
            &[(x, Rational64::one())],
            Rational64::from_integer(5),
            reason,
        );

        // x < 6 (becomes x <= 5)
        solver.assert_lt(
            &[(x, Rational64::one())],
            Rational64::from_integer(6),
            reason,
        );

        // Should be SAT: x = 5 is the only solution
        let result = solver.check().expect("test operation should succeed");
        assert!(
            matches!(result, TheoryResult::Sat),
            "Expected SAT for x >= 5 AND x < 6 in LIA, got {:?}",
            result
        );
    }

    // ---- Nelson-Oppen tests ----

    /// x <= y AND y <= x should yield an entailed equality.
    #[test]
    fn test_no_entailed_equality_bidirectional() {
        let mut solver = ArithSolver::lra();

        let x = TermId::new(1);
        let y = TermId::new(2);
        let reason = TermId::new(100);

        // Intern both so they appear in var_to_term.
        solver.intern(x);
        solver.intern(y);

        // x <= y
        solver.assert_le(
            &[(x, Rational64::one()), (y, -Rational64::one())],
            Rational64::from_integer(0),
            reason,
        );
        // y <= x
        solver.assert_le(
            &[(y, Rational64::one()), (x, -Rational64::one())],
            Rational64::from_integer(0),
            reason,
        );

        let sat = solver.check().expect("check should succeed");
        assert!(matches!(sat, TheoryResult::Sat), "Expected SAT");

        // Both x < y and x > y should be infeasible — equality is entailed.
        let eqs = solver.derive_shared_equalities();
        let has_xy = eqs
            .iter()
            .any(|e| (e.lhs == x && e.rhs == y) || (e.lhs == y && e.rhs == x));
        assert!(
            has_xy,
            "Expected entailed equality between x and y, got: {:?}",
            eqs
        );
    }

    /// x <= y alone should NOT yield an entailed equality (y could be > x).
    #[test]
    fn test_no_entailed_equality_one_direction_only() {
        let mut solver = ArithSolver::lra();

        let x = TermId::new(1);
        let y = TermId::new(2);
        let reason = TermId::new(100);

        solver.intern(x);
        solver.intern(y);

        // x <= y only (one direction)
        solver.assert_le(
            &[(x, Rational64::one()), (y, -Rational64::one())],
            Rational64::from_integer(0),
            reason,
        );

        solver.check().expect("check should succeed");

        let eqs = solver.derive_shared_equalities();
        let has_xy = eqs
            .iter()
            .any(|e| (e.lhs == x && e.rhs == y) || (e.lhs == y && e.rhs == x));
        assert!(
            !has_xy,
            "Should NOT derive x=y from x<=y alone; got: {:?}",
            eqs
        );
    }

    /// notify_equality(x, y) followed by check should enforce x = y:
    /// asserting x < y should then be UNSAT.
    #[test]
    fn test_notify_equality_enforces_equality() {
        use crate::theory::{EqualityNotification, TheoryCombination};

        let mut solver = ArithSolver::lra();

        let x = TermId::new(1);
        let y = TermId::new(2);
        let reason = TermId::new(100);

        solver.intern(x);
        solver.intern(y);

        // Notify x = y
        let eq = EqualityNotification {
            lhs: x,
            rhs: y,
            reason: Some(reason),
        };
        let accepted = solver.notify_equality(eq);
        assert!(accepted, "notify_equality should accept x=y");

        // After asserting x=y, adding x < y should yield UNSAT.
        solver.push();
        solver.assert_lt(
            &[(x, Rational64::one()), (y, -Rational64::one())],
            Rational64::from_integer(0),
            reason,
        );
        let result = solver.check().expect("check should not error");
        assert!(
            matches!(result, TheoryResult::Unsat(_)),
            "Expected UNSAT when x=y is enforced and x<y is added; got {:?}",
            result
        );
        solver.pop();
    }

    // ---- push/pop state-rollback regression (term_to_var / var_to_term) ----

    /// `pop()` must roll back `term_to_var` in lockstep with `var_to_term`.
    ///
    /// Before the fix, `pop()` truncated `var_to_term` but left stale
    /// `term_to_var` entries behind. Because the simplex recycles VarIds across
    /// a pop, those stale entries made `intern()` replay indices that now belong
    /// to a different (or not-yet-created) variable. This test inspects the
    /// internal maps directly to prove the two stay consistent.
    #[test]
    fn regression_pop_rolls_back_term_to_var() {
        let mut solver = ArithSolver::lra();
        let a = TermId::new(1);
        let b = TermId::new(2);
        let c = TermId::new(3);

        // Intern `a` at the base level.
        let va = solver.intern(a);
        assert_eq!(va, 0);

        solver.push();
        // Intern two more terms inside the scope.
        let vb = solver.intern(b);
        let vc = solver.intern(c);
        assert_eq!(vb, 1);
        assert_eq!(vc, 2);
        assert_eq!(solver.var_to_term.len(), 3);
        assert_eq!(solver.term_to_var.len(), 3);

        solver.pop();

        // `var_to_term` is truncated back to just `[a]`.
        assert_eq!(solver.var_to_term.len(), 1);
        // `term_to_var` must be rolled back in lockstep: the scope-local terms
        // `b` and `c` are gone, only `a` remains.
        assert_eq!(solver.term_to_var.len(), 1);
        assert!(solver.term_to_var.contains_key(&a));
        assert!(!solver.term_to_var.contains_key(&b));
        assert!(!solver.term_to_var.contains_key(&c));

        // The core invariant: NO surviving mapping points at a truncated
        // (out-of-range) variable index.
        let live = solver.var_to_term.len() as VarId;
        for (&term, &var) in &solver.term_to_var {
            assert!(
                var < live,
                "term {term:?} maps to stale var {var} >= live var count {live}"
            );
        }

        // Re-interning the truncated terms yields FRESH valid indices.
        let vb2 = solver.intern(b);
        assert_eq!(vb2, 1, "re-interned `b` should take the next fresh index");
        assert!((vb2 as usize) < solver.var_to_term.len());
        let vc2 = solver.intern(c);
        assert_eq!(vc2, 2, "re-interned `c` should take the next fresh index");
        assert_ne!(vb2, vc2);
    }

    /// A fresh term interned after a pop must NOT collide with a stale-but-since-
    /// re-interned term that used to hold the recycled index.
    ///
    /// This is the recycled-index hazard the fix removes, observable purely
    /// through the public `intern()` API: intern `a`, push, intern `b`, pop —
    /// then intern a brand-new `c` (which the simplex hands the index `b` used
    /// to occupy) and finally re-intern `b`. With the stale mapping still
    /// present, `intern(b)` would return the same index as `c`.
    #[test]
    fn regression_pop_no_recycled_index_collision() {
        let mut solver = ArithSolver::lra();
        let a = TermId::new(11);
        let b = TermId::new(22);
        let c = TermId::new(33);

        let _va = solver.intern(a);
        solver.push();
        let _vb = solver.intern(b);
        solver.pop();

        // `c` is new: the simplex hands it the index `b` used to occupy.
        let vc = solver.intern(c);
        // `b` was truncated: re-interning must allocate a *different* fresh index.
        let vb2 = solver.intern(b);
        assert_ne!(
            vc, vb2,
            "recycled var index {vc} collided with re-interned truncated term"
        );
    }

    /// Regression (GitHub issue #12): in LRA the assignment for a variable
    /// pinned at a *strict* bound is a delta-rational `r ± δ`.  `value()` must
    /// instantiate `δ` with a concrete positive rational, otherwise it reports
    /// `x = 0` for `x > 0` — a witness that violates the asserted constraint.
    #[test]
    fn regression_lra_strict_bound_model_instantiates_delta() {
        let mut solver = ArithSolver::lra();
        let x = TermId::new(1);
        let reason = TermId::new(100);

        // x > 0
        solver.assert_gt(&[(x, Rational64::one())], Rational64::zero(), reason);
        assert!(matches!(solver.check(), Ok(TheoryResult::Sat)));

        let value = solver.value(x).expect("x must have a model value");
        assert!(
            value > Rational64::zero(),
            "model x = {value} violates x > 0"
        );
    }

    /// Both ends of a strict range must be respected simultaneously: the
    /// instantiated delta has to keep `0 < x < 1/2` genuinely inside the range.
    #[test]
    fn regression_lra_strict_range_model_inside_bounds() {
        let mut solver = ArithSolver::lra();
        let x = TermId::new(1);
        let lo = TermId::new(100);
        let hi = TermId::new(101);
        let half = Rational64::new(1, 2);

        solver.assert_gt(&[(x, Rational64::one())], Rational64::zero(), lo);
        solver.assert_lt(&[(x, Rational64::one())], half, hi);
        assert!(matches!(solver.check(), Ok(TheoryResult::Sat)));

        let value = solver.value(x).expect("x must have a model value");
        assert!(
            value > Rational64::zero() && value < half,
            "model x = {value} is outside the strict range (0, 1/2)"
        );
    }
}
