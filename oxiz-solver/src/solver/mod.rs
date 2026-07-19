//! Main CDCL(T) SMT Solver module

pub(super) mod candidates;
pub(super) mod check_array;
pub(super) mod check_bv;
pub(super) mod check_dt;
pub(super) mod check_fp;
pub(super) mod check_nlsat;
pub(super) mod check_string;
pub(super) mod config;
pub(super) mod encode;
pub(super) mod encode_guards;
pub(super) mod model_builder;
pub(super) mod pigeonhole;
pub(super) mod term_walk;
pub(super) mod theory_bv_encode;
pub(super) mod theory_manager;
pub(super) mod trail;
pub(super) mod types;

pub use types::{
    FpConstraintData, Model, NamedAssertion, Proof, ProofStep, SolverConfig, SolverResult,
    Statistics, TheoryMode, UnsatCore,
};

use crate::mbqi::{MBQIIntegration, MBQIResult};
#[allow(unused_imports)]
use crate::prelude::*;
use crate::simplify::Simplifier;
use num_traits::ToPrimitive;
use oxiz_core::ast::{TermId, TermKind, TermManager};
use oxiz_core::ematching::{EmatchingConfig, EmatchingEngine};
use oxiz_core::sort::SortId;
#[cfg(test)]
use oxiz_sat::RestartStrategy;
use oxiz_sat::{
    Lit, Solver as SatSolver, SolverConfig as SatConfig, SolverResult as SatResult, Var,
};
use oxiz_theories::Theory;
use oxiz_theories::arithmetic::ArithSolver;
use oxiz_theories::bv::BvSolver;
use oxiz_theories::euf::EufSolver;

use theory_manager::TheoryManager;
use trail::{ContextState, TrailOp};
use types::{Constraint, ParsedArithConstraint, Polarity};

/// Main CDCL(T) SMT Solver
#[derive(Debug)]
pub struct Solver {
    /// Configuration
    pub(super) config: SolverConfig,
    /// SAT solver core
    pub(super) sat: SatSolver,
    /// EUF theory solver
    pub(super) euf: EufSolver,
    /// Arithmetic theory solver
    pub(super) arith: ArithSolver,
    /// Bitvector theory solver
    pub(super) bv: BvSolver,
    /// NLSAT solver for nonlinear arithmetic (QF_NIA/QF_NRA)
    #[cfg(feature = "std")]
    pub(super) nlsat: Option<oxiz_theories::nlsat::NlsatTheory>,
    /// MBQI solver for quantified formulas
    pub(super) mbqi: MBQIIntegration,
    /// E-matching engine for quantifier instantiation via trigger patterns
    pub(super) ematch_engine: EmatchingEngine,
    /// Whether the formula contains quantifiers
    pub(super) has_quantifiers: bool,
    /// Term to SAT variable mapping
    pub(super) term_to_var: FxHashMap<TermId, Var>,
    /// SAT variable to term mapping
    pub(super) var_to_term: Vec<TermId>,
    /// SAT variable to theory constraint mapping
    pub(super) var_to_constraint: FxHashMap<Var, Constraint>,
    /// SAT variable to parsed arithmetic constraint mapping
    pub(super) var_to_parsed_arith: FxHashMap<Var, ParsedArithConstraint>,
    /// Current logic
    pub(super) logic: Option<String>,
    /// Assertions
    pub(super) assertions: Vec<TermId>,
    /// Named assertions for unsat core tracking
    pub(super) named_assertions: Vec<NamedAssertion>,
    /// Assumption literals for unsat core tracking (maps assertion index to assumption var)
    /// Reserved for future use with assumption-based unsat core extraction
    #[allow(dead_code)]
    pub(super) assumption_vars: FxHashMap<u32, Var>,
    /// Model (if sat)
    pub(super) model: Option<Model>,
    /// Unsat core (if unsat)
    pub(super) unsat_core: Option<UnsatCore>,
    /// Context stack for push/pop
    pub(super) context_stack: Vec<ContextState>,
    /// Trail of operations for efficient undo
    pub(super) trail: Vec<TrailOp>,
    /// Tracking which literals have been processed by theories
    pub(super) theory_processed_up_to: usize,
    /// Whether to produce unsat cores
    pub(super) produce_unsat_cores: bool,
    /// Track if we've asserted False (for immediate unsat)
    pub(super) has_false_assertion: bool,
    /// Polarity tracking for optimization
    pub(super) polarities: FxHashMap<TermId, Polarity>,
    /// Whether polarity-aware encoding is enabled
    pub(super) polarity_aware: bool,
    /// Whether theory-aware branching is enabled
    pub(super) theory_aware_branching: bool,
    /// Proof of unsatisfiability (if proof generation is enabled)
    pub(super) proof: Option<Proof>,
    /// Formula simplifier
    pub(super) simplifier: Simplifier,
    /// Solver statistics
    pub(super) statistics: Statistics,
    /// Bitvector terms (for model extraction)
    pub(super) bv_terms: FxHashSet<TermId>,
    /// Whether we've seen arithmetic BV operations (division/remainder)
    /// Used to decide when to run eager BV checking
    pub(super) has_bv_arith_ops: bool,
    /// Arithmetic terms (Int/Real variables for model extraction)
    pub(super) arith_terms: FxHashSet<TermId>,
    /// Datatype constructor constraints: variable -> constructor name
    /// Used to detect mutual exclusivity conflicts (var = C1 AND var = C2 where C1 != C2)
    pub(super) dt_var_constructors: FxHashMap<TermId, oxiz_core::interner::Spur>,
    /// Cache for parsed arithmetic constraints, keyed by the comparison term id.
    /// `ParsedArithConstraint` is purely structural (depends only on the term graph),
    /// so it is safe to reuse across CDCL backtracks.
    pub(super) arith_parse_cache: FxHashMap<TermId, Option<ParsedArithConstraint>>,
    /// Set of compound term ids whose theory-variable sub-graph has been fully
    /// traversed by `track_theory_vars`.  Avoids redundant O(depth) re-walks
    /// when the same sub-expression appears in multiple parent constraints.
    pub(super) tracked_compound_terms: FxHashSet<TermId>,
    /// Cache for FP constraint checking results.
    pub(super) fp_constraint_cache: FxHashMap<TermId, FpConstraintData>,
    /// Set to `true` when `encode` aborted a branch because the term nesting
    /// depth exceeded [`ENCODE_DEPTH_LIMIT`].  A truncated encoding leaves the
    /// affected sub-formula under-constrained, so the solver must answer
    /// `Unknown` rather than trust a model built over an incomplete encoding.
    pub(super) encode_depth_exceeded: bool,
}

/// Maximum term-nesting depth the recursive Tseitin encoder will descend
/// before bailing out.  Adversarially deep formulas would otherwise overflow
/// the native call stack (a hard crash / DoS); instead we stop, flag
/// [`Solver::encode_depth_exceeded`], and let `check` answer `Unknown`.
///
/// The limit is chosen well below the point at which the encoder's stack
/// frames exhaust a typical worker-thread stack, yet far above the depth of
/// any realistic hand- or tool-generated formula.
pub(super) const ENCODE_DEPTH_LIMIT: u32 = 2000;

/// A fully-evaluated ground value used by the model-verification soundness gate
/// ([`Solver::model_refutes_assertions`]).  Integers and reals are unified as an
/// exact rational so mixed Int/Real arithmetic and comparisons fold without loss.
#[derive(Debug, Clone, Copy, PartialEq)]
enum EvalVal {
    Bool(bool),
    Num(num_rational::Rational64),
}

impl Default for Solver {
    fn default() -> Self {
        Self::new()
    }
}

impl Solver {
    /// Create a new solver
    #[must_use]
    pub fn new() -> Self {
        Self::with_config(SolverConfig::default())
    }

    /// Create a new solver with configuration
    #[must_use]
    pub fn with_config(config: SolverConfig) -> Self {
        let proof_enabled = config.proof;

        // Build SAT solver configuration from our config
        let sat_config = SatConfig {
            restart_strategy: config.restart_strategy,
            enable_inprocessing: config.enable_inprocessing,
            inprocessing_interval: config.inprocessing_interval,
            ..SatConfig::default()
        };

        // Note: The following features are controlled by the SAT solver's preprocessor
        // and clause management systems. We pass the configuration but the actual
        // implementation is in oxiz-sat:
        // - Clause minimization (via RecursiveMinimizer)
        // - Clause subsumption (via SubsumptionChecker)
        // - Variable elimination (via Preprocessor::variable_elimination)
        // - Blocked clause elimination (via Preprocessor::blocked_clause_elimination)
        // - Symmetry breaking (via SymmetryBreaker)

        Self {
            config,
            sat: SatSolver::with_config(sat_config),
            euf: EufSolver::new(),
            arith: ArithSolver::lra(),
            bv: BvSolver::new(),
            #[cfg(feature = "std")]
            nlsat: None,
            mbqi: MBQIIntegration::new(),
            ematch_engine: EmatchingEngine::new(EmatchingConfig::default()),
            has_quantifiers: false,
            term_to_var: FxHashMap::default(),
            var_to_term: Vec::new(),
            var_to_constraint: FxHashMap::default(),
            var_to_parsed_arith: FxHashMap::default(),
            logic: None,
            assertions: Vec::new(),
            named_assertions: Vec::new(),
            assumption_vars: FxHashMap::default(),
            model: None,
            unsat_core: None,
            context_stack: Vec::new(),
            trail: Vec::new(),
            theory_processed_up_to: 0,
            produce_unsat_cores: false,
            has_false_assertion: false,
            polarities: FxHashMap::default(),
            polarity_aware: true, // Enable polarity-aware encoding by default
            theory_aware_branching: true, // Enable theory-aware branching by default
            proof: if proof_enabled {
                Some(Proof::new())
            } else {
                None
            },
            simplifier: Simplifier::new(),
            statistics: Statistics::new(),
            bv_terms: FxHashSet::default(),
            has_bv_arith_ops: false,
            arith_terms: FxHashSet::default(),
            dt_var_constructors: FxHashMap::default(),
            arith_parse_cache: FxHashMap::default(),
            tracked_compound_terms: FxHashSet::default(),
            fp_constraint_cache: FxHashMap::default(),
            encode_depth_exceeded: false,
        }
    }

    /// Get the proof (if proof generation is enabled and the result is unsat)
    #[must_use]
    pub fn get_proof(&self) -> Option<&Proof> {
        self.proof.as_ref()
    }

    /// Get the solver statistics
    #[must_use]
    pub fn get_statistics(&self) -> &Statistics {
        &self.statistics
    }

    /// Reset the solver statistics
    pub fn reset_statistics(&mut self) {
        self.statistics.reset();
    }

    /// Enable or disable theory-aware branching
    pub fn set_theory_aware_branching(&mut self, enabled: bool) {
        self.theory_aware_branching = enabled;
    }

    /// Check if theory-aware branching is enabled
    #[must_use]
    pub fn theory_aware_branching(&self) -> bool {
        self.theory_aware_branching
    }

    /// Enable or disable unsat core production
    pub fn set_produce_unsat_cores(&mut self, produce: bool) {
        self.produce_unsat_cores = produce;
    }

    /// Register a declared constant as an MBQI ground instantiation candidate.
    ///
    /// This must be called from the context layer whenever a `declare-const`
    /// command is processed, so that trigger-free quantifiers can be
    /// instantiated with constants that exist in scope.
    pub fn register_declared_const(&mut self, term: TermId, sort: SortId) {
        self.mbqi.register_declared_const(term, sort);
    }

    /// Soundness gate: does the freshly built model *provably* violate a
    /// top-level assertion?  Returns `true` only when an assertion evaluates to a
    /// concrete `false` under the model.
    ///
    /// The key to soundness is where leaf numeric values come from: an
    /// Int/Real variable is read from the *arithmetic solver* (`arith.value`),
    /// which reports `None` for a variable it does not actually constrain.  A
    /// `None` propagates to an inconclusive (`None`) result and never triggers a
    /// downgrade — so a `distinct`/comparison over variables that `build_model`
    /// merely *defaulted* to 0 (a genuinely satisfiable formula) is never
    /// mistaken for a violation.  Combined with the strict-inequality boundary
    /// softening (see `cmp_strict`), the gate only fires on a witness the theory
    /// genuinely determined yet the assignment falsifies — the signature of the
    /// SAT core committing an inconsistent trail (e.g. a clause reported
    /// satisfied whose every disjunct is false).  In that case the reported
    /// `Sat` is spurious and the solver answers `Unknown` instead.
    fn model_refutes_assertions(&self, manager: &TermManager) -> bool {
        let Some(model) = self.model.as_ref() else {
            return false;
        };
        for &assertion in &self.assertions {
            if matches!(
                self.eval_in_model(assertion, model, manager, 0),
                Some(EvalVal::Bool(false))
            ) {
                return true;
            }
        }
        false
    }

    /// Recursively evaluate `term` under `model`.  Returns `None` for any term
    /// whose value cannot be fully determined (unsupported operator, unassigned
    /// leaf, mixed/ill-typed operands), so callers only ever act on a concrete
    /// `Some`.  `depth` guards against pathological nesting.
    fn eval_in_model(
        &self,
        term: TermId,
        model: &Model,
        manager: &TermManager,
        depth: u32,
    ) -> Option<EvalVal> {
        if depth > ENCODE_DEPTH_LIMIT {
            return None;
        }
        // IMPORTANT: consult `model.get` only for *leaf* / opaque terms (handled
        // in the `Var`/`_` arms below).  Operator terms (And/Or/Eq/Add/…) are
        // ALWAYS recomputed structurally from their children — never read back
        // from the model cache.  `build_model` records the SAT core's Boolean
        // value for every atom and gate, and when that core commits an
        // inconsistent trail those cached values are exactly what we must not
        // trust (e.g. an `or` gate cached `true` while both disjuncts are
        // `false`).  Recomputing from leaves is what makes this gate sound.
        let t = manager.get(term)?;
        let sort = t.sort;
        let kind = &t.kind;
        let rec = |t: TermId| self.eval_in_model(t, model, manager, depth + 1);
        match kind {
            TermKind::True => Some(EvalVal::Bool(true)),
            TermKind::False => Some(EvalVal::Bool(false)),
            TermKind::IntConst(_) | TermKind::RealConst(_) => Self::parse_value_term(term, manager),
            TermKind::Var(_) => {
                // For a numeric variable, take the value from the ARITHMETIC
                // solver, not the built model.  `arith.value` returns `None` for
                // a variable the solver does not actually constrain, which makes
                // the whole evaluation inconclusive (never a false downgrade) —
                // exactly the variables `build_model` would have defaulted to 0.
                if sort == manager.sorts.int_sort || sort == manager.sorts.real_sort {
                    self.arith.value(term).map(EvalVal::Num)
                } else {
                    // Boolean / bit-vector / other: the model witness is fine
                    // (Booleans are exactly determined by the SAT assignment).
                    let value_term = model.get(term)?;
                    Self::parse_value_term(value_term, manager)
                }
            }
            TermKind::Not(a) => match rec(*a)? {
                EvalVal::Bool(b) => Some(EvalVal::Bool(!b)),
                _ => None,
            },
            TermKind::And(args) => {
                let mut all_true = true;
                for &a in args {
                    match rec(a) {
                        Some(EvalVal::Bool(false)) => return Some(EvalVal::Bool(false)),
                        Some(EvalVal::Bool(true)) => {}
                        _ => all_true = false,
                    }
                }
                all_true.then_some(EvalVal::Bool(true))
            }
            TermKind::Or(args) => {
                let mut all_false = true;
                for &a in args {
                    match rec(a) {
                        Some(EvalVal::Bool(true)) => return Some(EvalVal::Bool(true)),
                        Some(EvalVal::Bool(false)) => {}
                        _ => all_false = false,
                    }
                }
                all_false.then_some(EvalVal::Bool(false))
            }
            TermKind::Implies(a, b) => {
                // false ⇒ _ is true; _ ⇒ true is true.
                match rec(*a) {
                    Some(EvalVal::Bool(false)) => return Some(EvalVal::Bool(true)),
                    Some(EvalVal::Bool(true)) => {}
                    _ => {
                        return match rec(*b) {
                            Some(EvalVal::Bool(true)) => Some(EvalVal::Bool(true)),
                            _ => None,
                        };
                    }
                }
                match rec(*b)? {
                    EvalVal::Bool(b) => Some(EvalVal::Bool(b)),
                    _ => None,
                }
            }
            TermKind::Ite(c, t, e) => match rec(*c)? {
                EvalVal::Bool(true) => rec(*t),
                EvalVal::Bool(false) => rec(*e),
                _ => None,
            },
            TermKind::Eq(a, b) => {
                let (va, vb) = (rec(*a)?, rec(*b)?);
                match (va, vb) {
                    // Booleans come straight from the SAT assignment — reliable.
                    (EvalVal::Bool(x), EvalVal::Bool(y)) => Some(EvalVal::Bool(x == y)),
                    // Numeric equality is trustworthy only in the NEGATIVE
                    // direction: distinct arithmetic values genuinely falsify the
                    // equality.  A *collision* (equal values) is not reliable —
                    // the LP model can assign two variables the same value even
                    // when they were never asserted equal — so we report it as
                    // inconclusive (`None`) rather than a definitive `true`.  This
                    // also makes a negated equality (`distinct`/`not (= ..)`)
                    // inconclusive at a collision instead of a false violation.
                    (EvalVal::Num(x), EvalVal::Num(y)) => {
                        if x == y {
                            None
                        } else {
                            Some(EvalVal::Bool(false))
                        }
                    }
                    _ => None,
                }
            }
            // `distinct` is deliberately INCONCLUSIVE for the gate.  A model in
            // which two operands share a value does NOT reliably indicate a real
            // violation: the linear-arithmetic solver enforces disequalities by
            // case-splitting, not by pinning distinct witnesses in its LP model,
            // so `arith.value` routinely reports colliding integer values for a
            // genuinely satisfiable `distinct`.  Downgrading on that would turn
            // correct `Sat`s into spurious `Unknown`s; the gate targets violated
            // POSITIVE structure (a falsified equality or an all-false clause)
            // instead, which the arithmetic model represents faithfully.
            TermKind::Distinct(_) => None,
            TermKind::Add(args) => {
                let mut sum = num_rational::Rational64::from_integer(0);
                for &a in args {
                    match rec(a)? {
                        EvalVal::Num(n) => sum += n,
                        _ => return None,
                    }
                }
                Some(EvalVal::Num(sum))
            }
            TermKind::Sub(a, b) => match (rec(*a)?, rec(*b)?) {
                (EvalVal::Num(x), EvalVal::Num(y)) => Some(EvalVal::Num(x - y)),
                _ => None,
            },
            TermKind::Mul(args) => {
                let mut prod = num_rational::Rational64::from_integer(1);
                for &a in args {
                    match rec(a)? {
                        EvalVal::Num(n) => prod *= n,
                        _ => return None,
                    }
                }
                Some(EvalVal::Num(prod))
            }
            TermKind::Neg(a) => match rec(*a)? {
                EvalVal::Num(n) => Some(EvalVal::Num(-n)),
                _ => None,
            },
            // STRICT comparisons are softened AT THE BOUNDARY: the arithmetic
            // solver represents `x > c` internally with a delta above `c` but
            // `value()` reports the boundary `c` itself, so a model value equal
            // to the bound cannot distinguish `x > c` (satisfiable) from a real
            // violation.  Returning `None` there keeps the gate from falsely
            // refuting a genuine strict-inequality model; away from the boundary
            // the comparison is concrete and trustworthy.  Non-strict `<=`/`>=`
            // have no such ambiguity.
            TermKind::Lt(a, b) => Self::cmp_strict(rec(*a)?, rec(*b)?, true),
            TermKind::Gt(a, b) => Self::cmp_strict(rec(*a)?, rec(*b)?, false),
            TermKind::Le(a, b) => Self::cmp_nums(rec(*a)?, rec(*b)?, |x, y| x <= y),
            TermKind::Ge(a, b) => Self::cmp_nums(rec(*a)?, rec(*b)?, |x, y| x >= y),
            // Opaque leaves (uninterpreted applications, selects, …): the model
            // may pin a concrete value; otherwise inconclusive.
            _ => model
                .get(term)
                .and_then(|vt| Self::parse_value_term(vt, manager)),
        }
    }

    /// Compare two numeric [`EvalVal`]s; `None` if either is not numeric.
    fn cmp_nums(
        a: EvalVal,
        b: EvalVal,
        op: impl Fn(num_rational::Rational64, num_rational::Rational64) -> bool,
    ) -> Option<EvalVal> {
        match (a, b) {
            (EvalVal::Num(x), EvalVal::Num(y)) => Some(EvalVal::Bool(op(x, y))),
            _ => None,
        }
    }

    /// Evaluate a STRICT comparison (`less` selects `<` vs `>`), returning `None`
    /// when the two numeric sides are equal (the strict-inequality boundary the
    /// arithmetic model cannot resolve — see the `Lt`/`Gt` arms).
    fn cmp_strict(a: EvalVal, b: EvalVal, less: bool) -> Option<EvalVal> {
        match (a, b) {
            (EvalVal::Num(x), EvalVal::Num(y)) => {
                if x == y {
                    None
                } else if less {
                    Some(EvalVal::Bool(x < y))
                } else {
                    Some(EvalVal::Bool(x > y))
                }
            }
            _ => None,
        }
    }

    /// Parse a constant value term (`IntConst`/`RealConst`/`True`/`False`) into
    /// an [`EvalVal`].  Returns `None` for non-constant or out-of-i64 terms.
    fn parse_value_term(term: TermId, manager: &TermManager) -> Option<EvalVal> {
        match &manager.get(term)?.kind {
            TermKind::True => Some(EvalVal::Bool(true)),
            TermKind::False => Some(EvalVal::Bool(false)),
            TermKind::IntConst(n) => n
                .to_i64()
                .map(|v| EvalVal::Num(num_rational::Rational64::from_integer(v))),
            TermKind::RealConst(r) => Some(EvalVal::Num(*r)),
            _ => None,
        }
    }

    /// Get a SAT variable for a term, then check satisfiability
    pub fn check(&mut self, manager: &mut TermManager) -> SolverResult {
        // Check for trivial unsat (false assertion)
        if self.has_false_assertion {
            self.build_unsat_core_trivial_false();
            return SolverResult::Unsat;
        }

        if self.assertions.is_empty() {
            return SolverResult::Sat;
        }

        // Check string constraints for early conflict detection
        if self.check_string_constraints(manager) {
            return SolverResult::Unsat;
        }

        // Check floating-point constraints for early conflict detection
        if self.check_fp_constraints(manager) {
            return SolverResult::Unsat;
        }

        // Check datatype constraints for early conflict detection
        if self.check_dt_constraints(manager) {
            return SolverResult::Unsat;
        }

        // Check array constraints for early conflict detection
        if self.check_array_constraints(manager) {
            return SolverResult::Unsat;
        }

        // Check bitvector constraints for early conflict detection
        if self.check_bv_constraints(manager) {
            return SolverResult::Unsat;
        }

        // For NIA/NRA logics: dispatch all assertions to the full polynomial
        // solver first (NiaSolver or NlsatSolver). This gives a definitive
        // SAT/UNSAT for most benchmark problems without the CDCL(T) loop.
        if let Some(nl_result) = self.dispatch_nl_solver(manager) {
            match nl_result {
                SolverResult::Sat => return SolverResult::Sat,
                SolverResult::Unsat => return SolverResult::Unsat,
                SolverResult::Unknown => {}
            }
        }

        // Check nonlinear arithmetic constraints for early conflict detection
        // (static pattern matching, complementary to the dispatch above).
        if self.check_nonlinear_constraints(manager) {
            return SolverResult::Unsat;
        }

        // Honesty gate (soundness): there is no complete String / FP theory
        // wired into the CDCL(T) core — `encode.rs` maps string and FP atoms to
        // fresh SAT variables, and the checks above only detect a fixed set of
        // definite conflicts.  If any such atom survives without a proven
        // conflict, we must answer `Unknown` instead of letting the SAT core
        // treat it as a free Boolean, which would report a spurious `Sat` for
        // formulas like `(= s "abc") ∧ (str.contains s "xyz")` or
        // `fp.lt x y ∧ fp.lt y x`.
        if self.string_atoms_need_theory(manager) || self.fp_atoms_need_theory(manager) {
            return SolverResult::Unknown;
        }

        // Honesty gate (soundness): an arithmetic comparison / equality atom that
        // could not be turned into a linear constraint (it contains Div/Mod, a
        // nonlinear product, or an out-of-range constant) has no theory
        // constraint attached — `encode.rs` left it as a free Boolean.  Trusting
        // the SAT layer to guess a truth value for such an atom yields a
        // spurious Sat/Unsat.  If the nonlinear dispatch above could not decide
        // the problem and such an atom survives, answer `Unknown`.
        if self.arith_atoms_need_theory(manager) {
            return SolverResult::Unknown;
        }

        // Honesty gate (soundness): if the Tseitin encoder truncated any
        // sub-formula because it was pathologically deep, the encoding is
        // incomplete and any model built over it is untrustworthy.
        if self.encode_depth_exceeded {
            return SolverResult::Unknown;
        }

        // Check resource limits before starting
        if self.config.max_conflicts > 0 && self.statistics.conflicts >= self.config.max_conflicts {
            return SolverResult::Unknown;
        }
        if self.config.max_decisions > 0 && self.statistics.decisions >= self.config.max_decisions {
            return SolverResult::Unknown;
        }

        // Rebuild the bit-vector solver state from scratch for this check.
        //
        // BV constraints are fully re-driven from the live assertion set on
        // every check: `TheoryManager::process_constraint` re-asserts each
        // active BV comparison/equality (via `assert_eq`, `assert_slt`, ...)
        // as the embedded SAT solver assigns the corresponding literals.
        // The BvSolver, however, is *not* wired into `Solver::push`/`pop` and
        // its internal `assertions` vector accumulates unit facts committed at
        // its base level (e.g. `assert_const` pinning `x = 5`).  Those facts
        // outlive both the end of `check()` and a user `pop()`, so a later
        // `(= x 6)` would spuriously conflict with the stale `x = 5` and yield
        // a wrong UNSAT in incremental use.  Resetting here guarantees no
        // cross-scope / cross-check BV leakage: the solver is repopulated only
        // from constraints that are actually active in the current context.
        self.bv.reset();

        // Wall-clock deadline for the CDCL(T)/MBQI search.  `timeout_ms == 0`
        // means "no timeout".  The deadline is enforced (a) between MBQI
        // rounds here and (b) mid-search inside the theory callbacks, so a
        // single long `solve_with_theory` call cannot run past the budget.
        #[cfg(feature = "std")]
        let deadline: Option<std::time::Instant> = if self.config.timeout_ms > 0 {
            std::time::Instant::now()
                .checked_add(core::time::Duration::from_millis(self.config.timeout_ms))
        } else {
            None
        };

        // Run SAT solver with theory integration
        let mut theory_manager = TheoryManager::new(
            manager,
            &mut self.euf,
            &mut self.arith,
            &mut self.bv,
            &self.bv_terms,
            &self.var_to_constraint,
            &self.var_to_parsed_arith,
            &self.term_to_var,
            &self.var_to_term,
            self.config.theory_mode,
            &mut self.statistics,
            self.config.max_conflicts,
            self.config.max_decisions,
            self.has_bv_arith_ops,
            self.config.timeout_ms,
        );

        // MBQI loop for quantified formulas
        let max_mbqi_iterations = 100;
        let mut mbqi_iteration = 0;

        loop {
            // Enforce the wall-clock timeout between MBQI rounds.  Mid-`solve`
            // enforcement lives in the theory callbacks (see TheoryManager).
            #[cfg(feature = "std")]
            if let Some(d) = deadline {
                if std::time::Instant::now() >= d {
                    return SolverResult::Unknown;
                }
            }
            let sat_result = self.sat.solve_with_theory(&mut theory_manager);
            // If a genuine theory conflict was suppressed because the conflict
            // limit was hit, the theory manager reported `Sat` to the SAT solver
            // to force it to stop searching.  That `Sat` is a resource-exhaustion
            // signal, NOT a proof of satisfiability: the model on the table may
            // violate a theory constraint whose conflict we refused to report.
            // We must answer `Unknown` rather than trust such a `Sat`.
            let resource_exhausted = theory_manager.resource_exhausted();
            match sat_result {
                SatResult::Unsat => {
                    self.build_unsat_core();
                    return SolverResult::Unsat;
                }
                SatResult::Unknown => {
                    return SolverResult::Unknown;
                }
                SatResult::Sat => {
                    if resource_exhausted {
                        // A real theory conflict was dropped at the conflict
                        // limit; never fabricate Sat over a suppressed conflict.
                        self.unsat_core = None;
                        return SolverResult::Unknown;
                    }
                    // If no quantifiers, we're done
                    if !self.has_quantifiers {
                        self.build_model(manager);
                        // Soundness gate: never return `Sat` for a model that
                        // provably violates an assertion (see
                        // `model_refutes_assertions`).  This backstops the SAT
                        // core: if it commits an inconsistent trail and reports a
                        // full assignment that falsifies a Boolean clause the
                        // theory layer cannot observe, we answer `Unknown`
                        // instead of a wrong `Sat`.
                        if self.model_refutes_assertions(manager) {
                            self.model = None;
                            self.unsat_core = None;
                            return SolverResult::Unknown;
                        }
                        self.unsat_core = None;
                        return SolverResult::Sat;
                    }

                    // Build partial model for MBQI
                    self.build_model(manager);

                    // Run MBQI to check quantified formulas
                    let model_assignments = self
                        .model
                        .as_ref()
                        .map(|m| m.assignments().clone())
                        .unwrap_or_default();

                    let mbqi_result = self.mbqi.check_with_model(&model_assignments, manager);
                    match mbqi_result {
                        MBQIResult::NoQuantifiers => {
                            self.unsat_core = None;
                            return SolverResult::Sat;
                        }
                        MBQIResult::Satisfied => {
                            // All quantifiers satisfied by the current model.
                            self.unsat_core = None;
                            return SolverResult::Sat;
                        }
                        MBQIResult::InstantiationLimit => {
                            // Too many instantiations - return unknown
                            return SolverResult::Unknown;
                        }
                        MBQIResult::Conflict {
                            quantifier: _,
                            reason,
                        } => {
                            // Add conflict clause
                            let lits: Vec<Lit> = reason
                                .iter()
                                .filter_map(|&t| self.term_to_var.get(&t).map(|&v| Lit::neg(v)))
                                .collect();
                            if !lits.is_empty() {
                                self.sat.add_clause(lits);
                            }
                            // Continue loop
                        }
                        MBQIResult::NewInstantiations(instantiations) => {
                            // Collect ground sub-terms (especially Skolem
                            // applications) from instantiation results so they
                            // become MBQI candidates in subsequent rounds.
                            for inst in &instantiations {
                                self.collect_ground_candidates_from_term(inst.result, manager);
                            }

                            // Collect domain/disequality info for pigeonhole
                            let mut ph_domains: FxHashMap<TermId, (i64, i64)> =
                                FxHashMap::default();
                            let mut ph_diseqs: Vec<(TermId, TermId)> = Vec::new();

                            // Add instantiation lemmas
                            for inst in instantiations {
                                // If the instantiation result is definitively False
                                // (e.g., a nested Exists with no valid witness), add an
                                // empty clause to signal immediate UNSAT.
                                let is_false_result = manager
                                    .get(inst.result)
                                    .is_some_and(|t| matches!(t.kind, TermKind::False));
                                if is_false_result {
                                    self.sat.add_clause([] as [Lit; 0]);
                                    break;
                                }
                                // Scan for pigeonhole patterns (recurses into Implies)
                                self.scan_for_pigeonhole(
                                    inst.result,
                                    manager,
                                    &mut ph_domains,
                                    &mut ph_diseqs,
                                );
                                let lit = self.encode(inst.result, manager);
                                let ok = self.sat.add_clause([lit]);
                                let _ = ok;
                                self.add_arith_diseq_split(inst.result, manager);
                                self.add_arith_eq_trichotomy(inst.result, manager);
                                self.add_int_domain_clauses(inst.result, manager);
                            }
                            // Add pigeonhole exclusion clauses
                            if !ph_diseqs.is_empty() && !ph_domains.is_empty() {
                                self.add_pigeonhole_exclusions_from(
                                    &ph_domains,
                                    &ph_diseqs,
                                    manager,
                                );
                            }

                            // E-matching phase: find additional instantiations via trigger patterns
                            let ematch_lemmas =
                                self.ematch_engine.match_round(manager).unwrap_or_default();
                            let mut new_clauses_added = 0usize;
                            let mut ematch_unsat = false;
                            for lemma in ematch_lemmas {
                                let lit = self.encode(lemma, manager);
                                if self.sat.add_clause([lit]) {
                                    new_clauses_added += 1;
                                } else {
                                    ematch_unsat = true;
                                    break;
                                }
                            }
                            if ematch_unsat || new_clauses_added > 0 {
                                // SAT solver will process newly added clauses on next iteration
                            }
                            // Continue loop
                        }
                        MBQIResult::Unknown => {
                            // Some evaluations produced symbolic residuals.
                            // Generate blind instantiations (simplified) once
                            // to seed the solver with ground lemmas for array
                            // theory reasoning (pigeonhole, bounds, etc.).
                            if !self.mbqi.blind_tried() {
                                self.mbqi.mark_blind_tried();
                                // Clear dedup cache so that blind instantiations with
                                // corrected substitution results are not filtered out
                                // as duplicates of earlier (broken) engine results.
                                self.mbqi.clear_dedup_cache();
                                let blind = self.mbqi.generate_blind_instantiations(manager);
                                let mut ph_domains: FxHashMap<TermId, (i64, i64)> =
                                    FxHashMap::default();
                                let mut ph_diseqs: Vec<(TermId, TermId)> = Vec::new();
                                for inst in blind {
                                    let is_false = manager
                                        .get(inst.result)
                                        .is_some_and(|t| matches!(t.kind, TermKind::False));
                                    if is_false {
                                        self.sat.add_clause([] as [Lit; 0]);
                                        break;
                                    }
                                    // Track domains and disequalities for pigeonhole
                                    let _ = manager.get(inst.result);
                                    self.scan_for_pigeonhole(
                                        inst.result,
                                        manager,
                                        &mut ph_domains,
                                        &mut ph_diseqs,
                                    );
                                    let lit = self.encode(inst.result, manager);
                                    let _ = self.sat.add_clause([lit]);
                                    self.add_arith_diseq_split(inst.result, manager);
                                    self.add_arith_eq_trichotomy(inst.result, manager);
                                    self.add_int_domain_clauses(inst.result, manager);
                                }
                                // Add pigeonhole exclusion clauses directly
                                // from the collected domains and disequalities.
                                self.add_pigeonhole_exclusions_from(
                                    &ph_domains,
                                    &ph_diseqs,
                                    manager,
                                );
                            }
                            // After 2 Unknown rounds, try finite instantiation:
                            // for quantifiers with bounded integer guards like
                            // (i >= 0 && i <= 3), enumerate all values and add
                            // ground instances directly.
                            if mbqi_iteration == 2 {
                                let finite_insts =
                                    self.mbqi.generate_finite_domain_instantiations(manager);
                                if !finite_insts.is_empty() {
                                    let mut ph_d: FxHashMap<TermId, (i64, i64)> =
                                        FxHashMap::default();
                                    let mut ph_q: Vec<(TermId, TermId)> = Vec::new();
                                    for inst in &finite_insts {
                                        let simplified =
                                            self.mbqi.deep_simplify(inst.result, manager);
                                        // Skip tautologies
                                        if manager
                                            .get(simplified)
                                            .is_some_and(|t| matches!(t.kind, TermKind::True))
                                        {
                                            continue;
                                        }
                                        self.scan_for_pigeonhole(
                                            simplified, manager, &mut ph_d, &mut ph_q,
                                        );
                                        let lit = self.encode(simplified, manager);
                                        let _ = self.sat.add_clause([lit]);
                                        self.add_arith_diseq_split(simplified, manager);
                                        self.add_int_domain_clauses(simplified, manager);
                                    }
                                    if !ph_q.is_empty() && !ph_d.is_empty() {
                                        self.add_pigeonhole_exclusions_from(&ph_d, &ph_q, manager);
                                    }
                                }
                            }
                            if mbqi_iteration >= 10 {
                                // After exhausting blind and finite domain
                                // instantiation attempts, MBQI still could not
                                // *verify* that the candidate model satisfies
                                // every quantifier (each round returned
                                // `Unknown`, i.e. symbolic residuals remained).
                                //
                                // Blindly returning Sat here would be unsound:
                                // any UNSAT quantified formula whose refutation
                                // needs an instantiation outside the enumerated
                                // candidates would be wrongly declared
                                // satisfiable.  Z3 returns `unknown` in exactly
                                // this situation.
                                //
                                // We may still soundly answer Sat in one case:
                                // when every quantifier is *trivially valid* —
                                // its body simplifies to `True` in every model
                                // (e.g. `forall x. f(x) = f(x)`).  Such
                                // quantifiers add no constraint, so the model the
                                // SAT/theory layer already found satisfies the
                                // whole formula.  Otherwise the honest answer is
                                // Unknown — never fabricate Sat for an unverified
                                // quantifier.
                                self.unsat_core = None;
                                if self.quantifiers_trivially_valid(manager) {
                                    self.build_model(manager);
                                    return SolverResult::Sat;
                                }
                                return SolverResult::Unknown;
                            }
                            // Continue MBQI loop
                        }
                    }

                    mbqi_iteration += 1;
                    if mbqi_iteration >= max_mbqi_iterations {
                        return SolverResult::Unknown;
                    }

                    // Recreate theory manager for next iteration.
                    // Do NOT reset theory solvers here - resetting EUF/Arith/BV
                    // state causes spurious conflicts when accumulated lemmas from
                    // MBQI instantiations interact with theory state that was cleared.
                    // The theory state accumulates correctly across iterations.
                    theory_manager = TheoryManager::new(
                        manager,
                        &mut self.euf,
                        &mut self.arith,
                        &mut self.bv,
                        &self.bv_terms,
                        &self.var_to_constraint,
                        &self.var_to_parsed_arith,
                        &self.term_to_var,
                        &self.var_to_term,
                        self.config.theory_mode,
                        &mut self.statistics,
                        self.config.max_conflicts,
                        self.config.max_decisions,
                        self.has_bv_arith_ops,
                        self.config.timeout_ms,
                    );
                }
            }
        }
    }

    /// Check satisfiability under assumptions
    /// Assumptions are temporary constraints that don't modify the assertion stack
    pub fn check_with_assumptions(
        &mut self,
        assumptions: &[TermId],
        manager: &mut TermManager,
    ) -> SolverResult {
        // Save current state
        self.push();

        // Assert all assumptions
        for &assumption in assumptions {
            self.assert(assumption, manager);
        }

        // Check satisfiability
        let result = self.check(manager);

        // Restore state
        self.pop();

        result
    }

    /// Sound sufficient check used only at the MBQI incompleteness fallback.
    ///
    /// Returns `true` iff every assertion that carries a quantifier is
    /// *trivially valid* — i.e. it simplifies to `True` in every model.  In
    /// that case the quantifiers add no constraint and the model already found
    /// by the SAT/theory layer satisfies the whole formula, so answering `Sat`
    /// is sound.  Any quantified assertion we cannot prove trivially valid
    /// makes this return `false`, so the solver conservatively answers
    /// `Unknown` instead of fabricating an unverified `Sat`.
    fn quantifiers_trivially_valid(&mut self, manager: &mut TermManager) -> bool {
        let assertions = self.assertions.clone();
        for assertion in assertions {
            // Quantifier-free assertions are already satisfied by the model the
            // SAT/theory search produced (that is why we reached the Sat
            // branch); only quantified assertions need a validity proof.
            if oxiz_core::tactic::contains_quantifier(assertion, manager)
                && !self.term_is_valid(assertion, manager)
            {
                return false;
            }
        }
        true
    }

    /// Returns `true` only when `term` is *valid* (True in every model).
    ///
    /// This is a sound (never over-claiming) syntactic check: a term is valid
    /// when it simplifies to `True`, when it is `forall x. body` with a valid
    /// body, or when it is a conjunction of valid terms.  Every other shape —
    /// including a universal whose body is merely satisfiable — yields `false`.
    fn term_is_valid(&mut self, term: TermId, manager: &mut TermManager) -> bool {
        let simplified = self.mbqi.deep_simplify(term, manager);
        match manager.get(simplified).map(|t| t.kind.clone()) {
            Some(TermKind::True) => true,
            Some(TermKind::Forall { body, .. }) => self.term_is_valid(body, manager),
            Some(TermKind::And(args)) => args.iter().all(|&conj| self.term_is_valid(conj, manager)),
            _ => false,
        }
    }

    /// Check satisfiability (pure SAT, no theory integration)
    /// Useful for benchmarking or when theories are not needed
    pub fn check_sat_only(&mut self, manager: &mut TermManager) -> SolverResult {
        if self.assertions.is_empty() {
            return SolverResult::Sat;
        }

        match self.sat.solve() {
            SatResult::Sat => {
                self.build_model(manager);
                SolverResult::Sat
            }
            SatResult::Unsat => SolverResult::Unsat,
            SatResult::Unknown => SolverResult::Unknown,
        }
    }

    /// Build the model after SAT solving, which can be used to efficiently extract minimal unsat cores
    pub fn enable_assumption_based_cores(&mut self) {
        self.produce_unsat_cores = true;
        // Assumption variables would be created during assertion
        // to enable fine-grained core extraction
    }

    /// Minimize an unsat core using greedy deletion
    /// This creates a minimal (but not necessarily minimum) unsatisfiable subset
    pub fn minimize_unsat_core(&mut self, manager: &mut TermManager) -> Option<UnsatCore> {
        if !self.produce_unsat_cores {
            return None;
        }

        // Get the current unsat core
        let core = self.unsat_core.as_ref()?;
        if core.is_empty() {
            return Some(core.clone());
        }

        // Extract the assertions in the core
        let mut core_assertions: Vec<_> = core
            .indices
            .iter()
            .map(|&idx| {
                let assertion = self.assertions[idx as usize];
                let name = self
                    .named_assertions
                    .iter()
                    .find(|na| na.index == idx)
                    .and_then(|na| na.name.clone());
                (idx, assertion, name)
            })
            .collect();

        // Try to remove each assertion one by one
        let mut i = 0;
        while i < core_assertions.len() {
            // Create a temporary solver with all assertions except the i-th one
            let mut temp_solver = Solver::new();
            temp_solver.set_logic(self.logic.as_deref().unwrap_or("ALL"));

            // Add all assertions except the i-th one
            for (j, &(_, assertion, _)) in core_assertions.iter().enumerate() {
                if i != j {
                    temp_solver.assert(assertion, manager);
                }
            }

            // Check if still unsat
            if temp_solver.check(manager) == SolverResult::Unsat {
                // Still unsat without this assertion - remove it
                core_assertions.remove(i);
                // Don't increment i, check the next element which is now at position i
            } else {
                // This assertion is needed
                i += 1;
            }
        }

        // Build the minimized core
        let mut minimized = UnsatCore::new();
        for (idx, _, name) in core_assertions {
            minimized.indices.push(idx);
            if let Some(n) = name {
                minimized.names.push(n);
            }
        }

        Some(minimized)
    }

    /// Get the model (if sat)
    #[must_use]
    pub fn model(&self) -> Option<&Model> {
        self.model.as_ref()
    }

    /// Congruence-closed function-application entries from the EUF solver for
    /// the given function symbol id (crate-internal use only).
    ///
    /// Each entry's argument and result classes have already been canonicalized
    /// through the union-find, so callers building a `FuncInterp` get congruence
    /// applied for free (e.g. `f(a)` and `f(b)` collapse when `a = b`).  The
    /// `func_id` is the EUF function symbol id, which for an `Apply` term is the
    /// underlying value of the function-name `Spur` (`spur.into_inner().get()`).
    #[must_use]
    pub(crate) fn euf_function_entries(
        &self,
        func_id: u32,
    ) -> Vec<oxiz_theories::euf::FuncAppEntry> {
        self.euf.function_application_entries(func_id)
    }

    /// Check satisfiability with resource limits.
    pub fn check_with_limits(
        &mut self,
        manager: &mut TermManager,
        limits: &crate::resource_limits::ResourceLimits,
    ) -> core::result::Result<SolverResult, crate::resource_limits::ResourceExhausted> {
        use crate::resource_limits::ResourceMonitor;
        let mut monitor = ResourceMonitor::new(limits.clone());
        if let Some(reason) = monitor.check() {
            return Err(reason);
        }
        let orig_max_conflicts = self.config.max_conflicts;
        let orig_max_decisions = self.config.max_decisions;
        if let Some(max_c) = limits.max_conflicts {
            if self.config.max_conflicts == 0 || max_c < self.config.max_conflicts {
                self.config.max_conflicts = max_c;
            }
        }
        if let Some(max_d) = limits.max_decisions {
            if self.config.max_decisions == 0 || max_d < self.config.max_decisions {
                self.config.max_decisions = max_d;
            }
        }
        let result = self.check(manager);
        self.config.max_conflicts = orig_max_conflicts;
        self.config.max_decisions = orig_max_decisions;
        monitor.conflicts = self.statistics.conflicts;
        monitor.decisions = self.statistics.decisions;
        monitor.restarts = self.statistics.restarts;
        monitor.theory_checks =
            self.statistics.theory_propagations + self.statistics.theory_conflicts;
        if result == SolverResult::Unknown {
            if let Some(reason) = monitor.check() {
                return Err(reason);
            }
        }
        Ok(result)
    }
    /// Set a wall-clock timeout.
    pub fn set_timeout(&mut self, timeout: core::time::Duration) {
        self.config.timeout_ms = timeout.as_millis() as u64;
    }
    /// Set the maximum number of SAT conflicts.
    pub fn set_conflict_limit(&mut self, max_conflicts: u64) {
        self.config.max_conflicts = max_conflicts;
    }
    /// Set the maximum number of SAT decisions.
    pub fn set_decision_limit(&mut self, max_decisions: u64) {
        self.config.max_decisions = max_decisions;
    }

    /// Assert multiple terms at once
    /// This is more efficient than calling assert() multiple times
    pub fn assert_many(&mut self, terms: &[TermId], manager: &mut TermManager) {
        for &term in terms {
            self.assert(term, manager);
        }
    }

    /// Simplify a term using the solver's pre-encoding simplifier (with the
    /// FP/String constant folder wired in). Exposed so [`crate::Context`] can
    /// pre-simplify assertion terms during the constant-substitution pass.
    #[must_use]
    pub fn simplify_term(&mut self, term: TermId, manager: &mut TermManager) -> TermId {
        self.simplifier.simplify(term, manager)
    }

    /// Get the number of assertions in the solver
    #[must_use]
    pub fn num_assertions(&self) -> usize {
        self.assertions.len()
    }

    /// Get the number of variables in the SAT solver
    #[must_use]
    pub fn num_variables(&self) -> usize {
        self.term_to_var.len()
    }

    /// Check if the solver has any assertions
    #[must_use]
    pub fn has_assertions(&self) -> bool {
        !self.assertions.is_empty()
    }

    /// Get the current context level (push/pop depth)
    #[must_use]
    pub fn context_level(&self) -> usize {
        self.context_stack.len()
    }

    /// Push a context level
    pub fn push(&mut self) {
        self.context_stack.push(ContextState {
            num_assertions: self.assertions.len(),
            num_vars: self.var_to_term.len(),
            has_false_assertion: self.has_false_assertion,
            trail_position: self.trail.len(),
        });
        self.sat.push();
        self.euf.push();
        self.arith.push();
        #[cfg(feature = "std")]
        if let Some(nlsat) = &mut self.nlsat {
            nlsat.push();
        }
    }

    /// Pop a context level using trail-based undo
    pub fn pop(&mut self) {
        if let Some(state) = self.context_stack.pop() {
            // Undo all operations in the trail since the push
            while self.trail.len() > state.trail_position {
                if let Some(op) = self.trail.pop() {
                    match op {
                        TrailOp::AssertionAdded { index } => {
                            if self.assertions.len() > index {
                                self.assertions.truncate(index);
                            }
                        }
                        TrailOp::VarCreated { var: _, term } => {
                            // Remove the term-to-var mapping
                            self.term_to_var.remove(&term);
                        }
                        TrailOp::ConstraintAdded { var } => {
                            // Remove the constraint
                            self.var_to_constraint.remove(&var);
                        }
                        TrailOp::FalseAssertionSet => {
                            // Reset the flag
                            self.has_false_assertion = false;
                        }
                        TrailOp::NamedAssertionAdded { index } => {
                            // Remove the named assertion
                            if self.named_assertions.len() > index {
                                self.named_assertions.truncate(index);
                            }
                        }
                        TrailOp::BvTermAdded { term } => {
                            // Remove the bitvector term
                            self.bv_terms.remove(&term);
                        }
                        TrailOp::ArithTermAdded { term } => {
                            // Remove the arithmetic term
                            self.arith_terms.remove(&term);
                        }
                    }
                }
            }

            // Use state to restore other fields
            self.assertions.truncate(state.num_assertions);
            self.var_to_term.truncate(state.num_vars);
            self.has_false_assertion = state.has_false_assertion;

            self.sat.pop();
            self.euf.pop();
            self.arith.pop();
            #[cfg(feature = "std")]
            if let Some(nlsat) = &mut self.nlsat {
                nlsat.pop();
            }
        }
    }

    /// Reset the solver
    pub fn reset(&mut self) {
        self.sat.reset();
        self.euf.reset();
        self.arith.reset();
        self.bv.reset();
        // Quantifier reasoning state must be cleared too: leaving the previous
        // problem's quantifiers, e-matching triggers, Skolem candidates, and the
        // `has_quantifiers` flag in place would make a subsequent `check` apply
        // stale quantifiers (and take the MBQI path) for a brand-new formula —
        // a correctness defect.  Rebuild the engines from scratch.
        self.mbqi = MBQIIntegration::new();
        self.ematch_engine = EmatchingEngine::new(EmatchingConfig::default());
        self.has_quantifiers = false;
        #[cfg(feature = "std")]
        {
            self.nlsat = None;
        }
        self.term_to_var.clear();
        self.var_to_term.clear();
        self.var_to_constraint.clear();
        self.var_to_parsed_arith.clear();
        self.assertions.clear();
        self.named_assertions.clear();
        self.model = None;
        self.unsat_core = None;
        self.context_stack.clear();
        self.trail.clear();
        self.logic = None;
        self.theory_processed_up_to = 0;
        self.has_false_assertion = false;
        self.has_bv_arith_ops = false;
        self.polarities.clear();
        self.bv_terms.clear();
        self.arith_terms.clear();
        self.dt_var_constructors.clear();
        self.arith_parse_cache.clear();
        self.tracked_compound_terms.clear();
        self.fp_constraint_cache.clear();
        self.encode_depth_exceeded = false;
    }

    /// Get the configuration
    #[must_use]
    pub fn config(&self) -> &SolverConfig {
        &self.config
    }

    /// Set configuration
    pub fn set_config(&mut self, config: SolverConfig) {
        self.config = config;
    }

    /// Seed the embedded SAT engine's phase-randomization PRNG.
    ///
    /// This realises the SMT-LIB `:random-seed` option: the SAT solver samples a
    /// random phase with probability `random_polarity_prob` (nonzero by default),
    /// so the seed genuinely perturbs the decision order and hence which model is
    /// returned for a satisfiable problem — while never affecting the sat/unsat
    /// verdict (soundness is seed-independent).  A seed of `0` reproduces the
    /// default out-of-the-box behaviour.
    pub fn set_random_seed(&mut self, seed: u64) {
        self.sat.set_random_seed(seed);
    }

    /// Get solver statistics
    #[must_use]
    pub fn stats(&self) -> &oxiz_sat::SolverStats {
        self.sat.stats()
    }
}

#[cfg(test)]
mod tests;
