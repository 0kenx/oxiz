//! Model and unsat core building

#[allow(unused_imports)]
use crate::prelude::*;
use num_bigint::BigInt;
use num_traits::{Signed, ToPrimitive, Zero};
use oxiz_core::ast::{TermId, TermKind, TermManager};

use super::Solver;
use super::types::Constraint;
use super::types::{Model, UnsatCore};

/// Reduce an integer to the canonical unsigned representative in `[0, 2^w)`.
///
/// Defends model output against a stale arith assignment outside the BV domain
/// (historically `x = -1` → malformed `#x-1`).
fn bv_model_u_bits(value: impl Into<BigInt>, width: u32) -> BigInt {
    if width == 0 {
        return BigInt::zero();
    }
    let modulus = BigInt::from(1) << width as usize;
    let mut v = value.into() % &modulus;
    if v.is_negative() {
        v += &modulus;
    }
    v
}

impl Solver {
    pub(super) fn build_model(&mut self, manager: &mut TermManager) {
        let mut model = Model::new();
        let sat_model = self.sat.model();

        // Get boolean values from SAT model
        for (&term, &var) in &self.term_to_var {
            let val = sat_model.get(var.index()).copied();
            if let Some(v) = val {
                let bool_val = if v.is_true() {
                    manager.mk_true()
                } else if v.is_false() {
                    manager.mk_false()
                } else {
                    continue;
                };
                model.set(term, bool_val);
            }
        }

        // Extract values from equality constraints (e.g., x = 5)
        // This handles cases where a variable is equated to a constant
        for (&var, constraint) in &self.var_to_constraint {
            // Check if the equality is assigned true in the SAT model
            let is_true = sat_model
                .get(var.index())
                .copied()
                .is_some_and(|v| v.is_true());

            if !is_true {
                continue;
            }

            if let Constraint::Eq(lhs, rhs) = constraint {
                // Check if one side is a tracked variable and the other is a constant.
                // Also handle Apply terms (uninterpreted function applications) that are
                // not in arith_terms due to the restriction on Apply terms with arith args.
                let lhs_is_apply = manager
                    .get(*lhs)
                    .is_some_and(|t| matches!(t.kind, TermKind::Apply { .. }));
                let rhs_is_apply = manager
                    .get(*rhs)
                    .is_some_and(|t| matches!(t.kind, TermKind::Apply { .. }));
                let is_str_var = |tid: TermId| -> bool {
                    manager.get(tid).is_some_and(|t| {
                        matches!(t.kind, TermKind::Var(_))
                            && manager
                                .sorts
                                .get(t.sort)
                                .is_some_and(|s| matches!(s.kind, oxiz_core::sort::SortKind::String))
                    })
                };
                let lhs_is_str_var = is_str_var(*lhs);
                let rhs_is_str_var = is_str_var(*rhs);

                let (var_term, const_term) = if self.arith_terms.contains(lhs)
                    || self.bv_terms.contains(lhs)
                    || lhs_is_apply
                    || lhs_is_str_var
                {
                    (*lhs, *rhs)
                } else if self.arith_terms.contains(rhs)
                    || self.bv_terms.contains(rhs)
                    || rhs_is_apply
                    || rhs_is_str_var
                {
                    (*rhs, *lhs)
                } else {
                    continue;
                };

                // Check if const_term is actually a constant
                let Some(const_term_data) = manager.get(const_term) else {
                    continue;
                };

                match &const_term_data.kind {
                    TermKind::IntConst(n) => {
                        if let Some(val) = n.to_i64() {
                            let value_term = manager.mk_int(val);
                            model.set(var_term, value_term);
                        }
                    }
                    TermKind::RealConst(r) => {
                        let value_term = manager.mk_real(*r);
                        model.set(var_term, value_term);
                    }
                    TermKind::BitVecConst { value, width } => {
                        if let Some(val) = value.to_u64() {
                            let value_term = manager.mk_bitvec(val, *width);
                            model.set(var_term, value_term);
                        }
                    }
                    TermKind::StringLit(s) => {
                        let s = s.clone();
                        let value_term = manager.mk_string_lit(&s);
                        model.set(var_term, value_term);
                    }
                    _ => {}
                }
            }
        }

        // Get arithmetic values from theory solver
        // Iterate over tracked arithmetic terms
        for &term in &self.arith_terms {
            // Don't overwrite if already set (e.g., from equality extraction above)
            if model.get(term).is_some() {
                continue;
            }

            if let Some(value) = self.arith.value(term) {
                // Determine whether the term has Int or Real sort, and create the
                // matching constant kind.  Using the term sort (rather than the
                // denominator of the rational value) is essential: a Real-sorted
                // term whose arith model value happens to be an integer ratio (e.g.
                // 2/1) must be represented as RealConst(2), not IntConst(2).  If
                // stored as IntConst, mixed-type comparisons like (f(c) <= 1.0)
                // become symbolic because eval_le requires both sides to be the
                // same constant kind, preventing counterexample detection.
                let is_int_sort = manager
                    .get(term)
                    .map(|t| t.sort == manager.sorts.int_sort)
                    .unwrap_or(true);
                let value_term = if is_int_sort {
                    // Integer-sorted term: convert to BigInt
                    manager.mk_int(*value.numer())
                } else {
                    // Real-sorted term: always use RealConst regardless of denominator
                    manager.mk_real(value)
                };
                model.set(term, value_term);
            } else {
                // If no value from ArithSolver (e.g., unconstrained variable), use default
                // Get the sort to determine if it's Int or Real
                let is_int = manager
                    .get(term)
                    .map(|t| t.sort == manager.sorts.int_sort)
                    .unwrap_or(true);

                let value_term = if is_int {
                    manager.mk_int(0i64)
                } else {
                    manager.mk_real(num_rational::Rational64::from_integer(0))
                };
                model.set(term, value_term);
            }
        }

        // Get bitvector values.  Which theory owns a BV variable's value depends
        // on how it was actually constrained (see `bv_solver_is_authoritative`):
        //
        //   * BV structure (arithmetic, bitwise, shifts, concat/extract) and BV
        //     (dis)equalities are genuinely bit-blasted — with constant operands
        //     pinned to their concrete bits — so `BvSolver::get_value` is a real
        //     witness (e.g. `a != b` in `not(bvadd a b = bvsub a b)`).
        //   * BV *comparisons* (`bvult`/`bvule`/…) are routed through the linear
        //     `ArithSolver` as bounded integers.  The BV comparison path allocates
        //     *unpinned* bits (`new_bv`) for the constant operands, so
        //     `BvSolver::get_value` for a comparison-only variable is arbitrary and
        //     may violate the very bound that made the query SAT (historically
        //     `x = 122` for `5 <u x <u 10`).  There the ArithSolver holds the real
        //     bounds and its value is authoritative.
        //
        // Establishing a single owning theory per problem keeps the extracted
        // model self-consistent instead of reading a stale value from the wrong
        // solver.
        let bv_authoritative = self.bv_solver_is_authoritative(manager);
        for &term in &self.bv_terms {
            // Don't overwrite if already set (shouldn't happen, but be safe)
            if model.get(term).is_some() {
                continue;
            }

            // Get the bitvector width from the term's sort
            let width = manager
                .get(term)
                .and_then(|t| manager.sorts.get(t.sort))
                .and_then(|s| s.bitvec_width())
                .unwrap_or(64);

            let bv_value = self.bv.get_value(term);
            let arith_value = self.arith.value(term);

            let value_term = if bv_authoritative {
                // BV theory owns the model: prefer its bit-blasted witness, then
                // fall back to any bounded-integer value, then a default of 0.
                if let Some(bv_value) = bv_value {
                    manager.mk_bitvec(bv_value, width)
                } else if let Some(arith_value) = arith_value {
                    manager.mk_bitvec(bv_model_u_bits(arith_value.to_integer(), width), width)
                } else {
                    manager.mk_bitvec(0i64, width)
                }
            } else {
                // Comparison-only problem: the ArithSolver holds the genuine
                // bounds, so prefer its value; only fall back to the (unpinned)
                // BV bits or a default when arith has nothing.
                if let Some(arith_value) = arith_value {
                    manager.mk_bitvec(bv_model_u_bits(arith_value.to_integer(), width), width)
                } else if let Some(bv_value) = bv_value {
                    manager.mk_bitvec(bv_value, width)
                } else {
                    manager.mk_bitvec(0i64, width)
                }
            };
            model.set(term, value_term);
        }

        self.model = Some(model);
    }

    /// Decide whether the `BvSolver`'s bit-blasted model is authoritative for
    /// BV terms in the current problem.
    ///
    /// It is authoritative when the problem contains genuine BV *structure* —
    /// any BV arithmetic/bitwise/shift/concat/extract operation — or any BV
    /// (dis)equality constraint.  Those paths bit-blast their operands with
    /// constant bits pinned to concrete values, so `BvSolver::get_value` is a
    /// faithful witness.
    ///
    /// When the only BV atoms are comparisons (`bvult`/`bvule`/`bvslt`/`bvsle`),
    /// the constraints are solved as bounded integers in the `ArithSolver` and
    /// the BV comparison path leaves constant operands' bits unpinned; the BV
    /// model is then arbitrary, so the arithmetic value is used instead.
    fn bv_solver_is_authoritative(&self, manager: &TermManager) -> bool {
        // Any structural BV operation implies real bit-blasting.
        for &term in &self.bv_terms {
            if let Some(t) = manager.get(term)
                && Self::is_structural_bv_op(&t.kind)
            {
                return true;
            }
        }

        // Any BV (dis)equality also bit-blasts both operands with pinned
        // constants.  A disequality `a != b` is stored as an `Eq` atom whose
        // SAT variable is assigned false, so both cases surface here as `Eq`.
        let is_bv = |tid: TermId| -> bool {
            manager
                .get(tid)
                .and_then(|t| manager.sorts.get(t.sort))
                .is_some_and(|s| s.is_bitvec())
        };
        for constraint in self.var_to_constraint.values() {
            if let Constraint::Eq(lhs, rhs) = constraint
                && (is_bv(*lhs) || is_bv(*rhs))
            {
                return true;
            }
        }

        false
    }

    /// Whether a `TermKind` is a structural BV operation (arithmetic, bitwise,
    /// shift, concat, or extract) — as opposed to a comparison, constant, or
    /// variable.  Structural ops are the ones the BV solver genuinely
    /// bit-blasts, making its model authoritative.
    fn is_structural_bv_op(kind: &TermKind) -> bool {
        matches!(
            kind,
            TermKind::BvNot(_)
                | TermKind::BvAnd(_, _)
                | TermKind::BvOr(_, _)
                | TermKind::BvXor(_, _)
                | TermKind::BvAdd(_, _)
                | TermKind::BvSub(_, _)
                | TermKind::BvMul(_, _)
                | TermKind::BvUdiv(_, _)
                | TermKind::BvSdiv(_, _)
                | TermKind::BvUrem(_, _)
                | TermKind::BvSrem(_, _)
                | TermKind::BvShl(_, _)
                | TermKind::BvLshr(_, _)
                | TermKind::BvAshr(_, _)
                | TermKind::BvConcat(_, _)
                | TermKind::BvExtract { .. }
        )
    }

    /// Canonical EUF congruence-class representative node for `term`.
    ///
    /// Returns `None` when the term was never interned into the congruence
    /// closure (it took part in no (dis)equality), so distinct such terms are
    /// treated as distinct.  Model output uses this to give uninterpreted-sort
    /// constants proven equal a *shared* abstract witness while keeping
    /// distinct constants distinct.
    pub(crate) fn euf_class_representative(&self, term: TermId) -> Option<u32> {
        let node = self.euf.term_to_node(term)?;
        Some(self.euf.find_immutable(node))
    }

    /// Build unsat core for trivial conflicts (assertion of false)
    pub(super) fn build_unsat_core_trivial_false(&mut self) {
        if !self.produce_unsat_cores {
            self.unsat_core = None;
            return;
        }

        // Find all assertions that are trivially false
        let mut core = UnsatCore::new();

        for (i, &term) in self.assertions.iter().enumerate() {
            if term == TermId::new(1) {
                // This is a false assertion
                core.indices.push(i as u32);

                // Find the name if there is one
                if let Some(named) = self.named_assertions.iter().find(|na| na.index == i as u32)
                    && let Some(ref name) = named.name
                {
                    core.names.push(name.clone());
                }
            }
        }

        self.unsat_core = Some(core);
    }

    /// Build the initial (conservative) unsat core after `check()` returned
    /// `Unsat`.
    ///
    /// This records every tracked assertion — a *valid* unsatisfiable set (a
    /// superset of any minimal core is still unsatisfiable), but not minimal on
    /// its own.  Minimization is deliberately left to query time: the SMT-LIB
    /// `(get-unsat-core)` path drives greedy deletion-based minimization via
    /// [`Solver::minimize_unsat_core`], which needs the `TermManager` to
    /// re-solve subsets (unavailable here).  Doing it eagerly for every `Unsat`
    /// solve — including the many that never issue `(get-unsat-core)` — would
    /// pay the re-solve cost unconditionally, so the split is intentional.
    ///
    /// True assumption-literal-based extraction (one selector per assertion,
    /// reading the SAT layer's failed-assumption set) would make this minimal
    /// without re-solving, but requires the encoder to gate each assertion
    /// behind a fresh selector variable — a larger change than this method.
    pub(super) fn build_unsat_core(&mut self) {
        if !self.produce_unsat_cores {
            self.unsat_core = None;
            return;
        }

        let mut core = UnsatCore::new();
        for na in &self.named_assertions {
            core.indices.push(na.index);
            if let Some(ref name) = na.name {
                core.names.push(name.clone());
            }
        }

        self.unsat_core = Some(core);
    }
}
