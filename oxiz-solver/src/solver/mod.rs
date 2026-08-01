//! Main CDCL(T) SMT Solver module

pub(super) mod arith_axioms;
pub(super) mod array_axioms;
pub(super) mod candidates;
pub(super) mod check_array;
pub(super) mod check_bv;
pub(super) mod check_dt;
pub(super) mod check_fp;
pub(super) mod check_fp_model;
pub(super) mod check_nlsat;
pub(super) mod check_string;
pub(super) mod config;
pub(super) mod dt_axioms;
pub(super) mod encode;
pub(super) mod encode_guards;
pub(super) mod int_case_split;
pub(super) mod model_builder;
pub(super) mod model_eval;
pub(super) mod pigeonhole;
pub(super) mod term_walk;
pub(super) mod theory_bv_encode;
pub(super) mod theory_manager;
pub(super) mod trail;
pub(super) mod types;
pub(super) mod verdict_cache;

pub use types::{
    FpConstraintData, Model, NamedAssertion, Proof, ProofStep, SolverConfig, SolverResult,
    Statistics, TheoryMode, UnsatCore,
};

use crate::mbqi::{MBQIIntegration, MBQIResult};
#[allow(unused_imports)]
use crate::prelude::*;
use crate::simplify::Simplifier;
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
use verdict_cache::GoalFingerprint;

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
    /// Explanations for theory assertions tagged with a *derived* equality.
    ///
    /// Owned here rather than by the `TheoryManager` because the theory solvers
    /// above are: a fresh manager is built for every MBQI round while their
    /// state is deliberately kept, so an explanation stored in the manager would
    /// vanish in front of the assertion it explains.  See
    /// [`DerivedReasons`](theory_manager::DerivedReasons).
    pub(super) derived_reasons: theory_manager::DerivedReasons,
    /// NLSAT solver for nonlinear arithmetic (QF_NIA/QF_NRA)
    #[cfg(feature = "std")]
    pub(super) nlsat: Option<oxiz_theories::nlsat::NlsatTheory>,
    /// MBQI solver for quantified formulas
    pub(super) mbqi: MBQIIntegration,
    /// E-matching engine for quantifier instantiation via trigger patterns
    pub(super) ematch_engine: EmatchingEngine,
    /// Whether the formula contains quantifiers
    pub(super) has_quantifiers: bool,
    /// Next unused Skolem symbol id.
    ///
    /// Skolem symbols are named positionally (`sk!N` / `skf!N`) and names are
    /// interned, so two [`SkolemizationContext`](crate::skolemization::SkolemizationContext)s
    /// that both start at zero mint the *same* symbols.  Reusing one witness
    /// symbol for two unrelated existentials strengthens the assertion set and
    /// can turn a satisfiable problem unsatisfiable, so every Skolemization the
    /// solver performs threads this monotone counter (never reset by `pop`: a
    /// popped symbol's name must not come back attached to a different
    /// existential).
    pub(super) next_skolem_id: u64,
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
    /// Fresh constants introduced by `eliminate_nonbool_ite` to stand for
    /// non-Bool `ite` subterms (named `__oxiz_ite_*`).  These are the terms
    /// whose value is fixed by an `ite` side-condition equality and that must
    /// merge with their constant value in EUF for congruence closure to reduce
    /// nested UF chains (the EufLaArithmetic/hard family).  Tracked so the
    /// z3-style triangle axiomatization can target exactly them, keeping the
    /// added boolean structure small.
    pub(super) ite_result_terms: FxHashSet<TermId>,
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
    /// Tseitin-encoding memo: term id -> (literal returned by `encode_depth`,
    /// polarity the term's clauses were emitted under).
    ///
    /// `get_or_create_var` caches only the SAT *variable*; without this map the
    /// encoder re-descends into every occurrence of a shared sub-term, which is
    /// exponential on a hash-consed DAG (each level referencing the previous
    /// twice gives `2^n` re-encodes and `2^n` duplicate clauses).
    ///
    /// The polarity component exists because `And`/`Or` are the only arms whose
    /// emitted clauses depend on more than the term itself: under
    /// `polarity_aware` they emit just one implication direction.  A hit is
    /// therefore only valid when the cached polarity covers the one the arm
    /// would use now (`Both` covers everything).  `collect_polarities` only
    /// ever *widens* a term's polarity, so on a widening miss the term is
    /// re-encoded — emitting the missing direction (plus harmless duplicates
    /// of the old one) — and the entry settles at `Both`.  Every other arm's
    /// clause set is polarity-independent, so those entries are stored as
    /// `Both` directly.
    ///
    /// Lifetime: every write is journalled as
    /// [`TrailOp::EncodedTermAdded`](super::solver::trail::TrailOp), so `pop`
    /// retracts exactly the entries whose clauses the matching `sat.pop()`
    /// retracts and keeps the ones written at an outer level (whose clauses
    /// survive).  Cleared wholesale only by `reset`.
    pub(super) encoded_terms: FxHashMap<TermId, (Lit, Polarity)>,
    /// Cache for FP constraint checking results.
    pub(super) fp_constraint_cache: FxHashMap<TermId, FpConstraintData>,
    /// Set to `true` when `encode` aborted a branch because the term nesting
    /// depth exceeded [`ENCODE_DEPTH_LIMIT`].  A truncated encoding leaves the
    /// affected sub-formula under-constrained, so the solver must answer
    /// `Unknown` rather than trust a model built over an incomplete encoding.
    pub(super) encode_depth_exceeded: bool,
    /// Set to `true` when any array `select`/`store` operation is encoded.  Gates
    /// the lazy array-axiom instantiation refinement (see
    /// [`Solver::instantiate_array_axioms`]) so non-array problems pay no cost.
    pub(super) has_array_ops: bool,
    /// Ground array-axiom instances (read-over-write / extensionality /
    /// select-congruence) already added to the SAT core as lemmas, keyed by the
    /// interned lemma term id.  Guarantees each valid instance is asserted at
    /// most once, which makes the in-loop refinement in `check` terminate: every
    /// refinement round either adds a strictly new instance or reports `Sat`.
    pub(super) array_axiom_instances: FxHashSet<TermId>,
    /// `div` / `mod` / numeric-`ite` terms whose defining axioms have already
    /// been asserted (see [`Solver::instantiate_arith_axioms`]).  The linear
    /// solver treats those terms as opaque atoms, so this set is what tells the
    /// honesty gate whether an atom's meaning is actually present: an atom
    /// mentioning a term that is *not* in here has no theory semantics and
    /// `check` must answer `Unknown`.
    pub(super) arith_defined_terms: FxHashSet<TermId>,
    /// z3-style triangle-axiom pairs `(ite-result term, const)` already
    /// asserted (see [`Solver::axiomatize_arith_constant_equalities`]).
    /// Trailed so the axiomatization is idempotent across repeated `check`s on
    /// an unchanged goal yet re-runs for a pair whose clauses a `pop` retracted.
    pub(super) arith_const_axiom_pairs: FxHashSet<(TermId, i64)>,
    /// Ground datatype-axiom instances (exhaustiveness, exclusivity,
    /// reconstruction, selector-over-constructor, congruence, acyclicity)
    /// already added to the SAT core as lemmas, keyed by the interned lemma
    /// term id.  See [`Solver::instantiate_dt_axioms`].
    pub(super) dt_axiom_instances: FxHashSet<TermId>,
    /// Set to `true` when the datatype axiom budget ran out before every
    /// instance had been asserted.  The remaining axiomatisation is then a
    /// strict subset of the theory, so `Unsat` is still trustworthy but a `Sat`
    /// must be reported as `Unknown`.
    pub(super) dt_axioms_incomplete: bool,
    /// Terms that the *current* assertion stack pins to a concrete integer,
    /// i.e. `t` appears in some top-level `(assert (= t <literal>))`.
    ///
    /// Consumed by [`Solver::finite_expand_assertion`] so that a quantifier
    /// guard such as `(< i n)` counts as a concrete bound once `(= n 5)` has
    /// been asserted.  Every entry is a consequence of the live assertion set,
    /// so substituting it preserves both `sat` and `unsat`.
    ///
    /// Folded in incrementally (see `entailed_int_consts_upto`) to keep the
    /// scan linear in the number of assertions over a whole run instead of
    /// quadratic, and dropped wholesale by `pop` — an entry justified by a
    /// retracted assertion must never survive it.
    pub(super) entailed_int_consts: FxHashMap<TermId, num_bigint::BigInt>,
    /// How many entries of `assertions` have been folded into
    /// `entailed_int_consts`.  Reset to `0` by `pop`, which invalidates the
    /// whole map.
    pub(super) entailed_int_consts_upto: usize,
    /// Test-only: the SAT clause count sampled at each MBQI **round boundary**
    /// this solver has crossed since it was created, cumulative over every
    /// `check`.
    ///
    /// A round boundary is the one place the quantifier loop re-enters the
    /// search: it encodes the round's instantiation / e-matching lemmas, calls
    /// [`Self::rebase_theory_state`] and builds a fresh `TheoryManager`.  Both
    /// facts a "repeated `check-sat` costs no clauses" claim needs are in this
    /// one vector — `len()` says how many boundaries were crossed (a plateau
    /// measured over calls that cross none measures nothing), and the values say
    /// what each crossing cost.  See `solver::scope_rebase_tests`.
    #[cfg(test)]
    pub(crate) mbqi_round_clauses: Vec<usize>,
    /// The most recent [`Self::check`]'s verdict, with the goal fingerprint it
    /// was computed from; see [`verdict_cache`].  Dropped by
    /// [`Self::invalidate_results`], the same hook that drops `model`.
    pub(super) last_check: Option<(GoalFingerprint, SolverResult)>,
    /// Monotone counter of *settings* changes — see [`Self::settings_changed`].
    ///
    /// Bumped by every mutator of something a [`Self::check`] reads that is not
    /// the assertion stack (the logic, the SAT engine's random seed, the
    /// configuration, the unsat-core and branching switches), and carried in the
    /// goal fingerprint so a cached verdict cannot survive one of them.
    pub(super) settings_epoch: u64,
    /// Terms already given an explicit integer case-split lemma during the
    /// current `check`, so we never re-split the same term.  Deduplication
    /// makes the in-loop non-convex-LIA refinement terminate (see
    /// [`Solver::refine_int_case_split`]).
    pub(super) case_split_terms: FxHashSet<TermId>,
    /// Number of reset-and-re-solve refinement rounds spent on integer
    /// case-splitting within the current `check`.  Capped by
    /// [`MAX_CASE_SPLIT_ROUNDS`] in `int_case_split`.
    pub(super) case_split_rounds: u32,
}

/// Maximum term-nesting depth the recursive Tseitin encoder will descend
/// before bailing out.  Adversarially deep formulas would otherwise overflow
/// the native call stack (a hard crash / DoS); instead we stop, flag
/// [`Solver::encode_depth_exceeded`], and let `check` answer `Unknown`.
///
/// # Measured, not guessed
///
/// The historical value 2000 was refuted by measurement: an at-cap
/// `encode` descent on a 1 MiB worker thread (the smallest stack an embedder
/// plausibly hands us) **aborted the process before the cap could fire**, so
/// the guard protected nothing there.  Measured on this workspace's dev
/// profile (`opt-level = 1`, the profile the regression test runs under),
/// with an `Implies` chain exactly at the cap
/// (`encode_at_cap_depth_survives_a_one_mib_stack` in `encode/tests.rs`):
///
/// | cap  | thread stack | outcome |
/// |------|--------------|---------|
/// | 2000 | 1 MiB        | SIGABRT (stack overflow) |
/// | 512  | 256 KiB      | SIGABRT (stack overflow) |
/// | 512  | 384 KiB      | returns |
/// | 512  | 1 MiB        | returns |
///
/// i.e. the encoder costs 512-768 bytes of native stack per nesting level at
/// `opt-level = 1`, so 512 levels fit in 384 KiB and the committed 1 MiB
/// test carries a measured >= 2.7x head-room (release `opt-level = "z"`
/// frames are smaller still; unoptimised `opt-level = 0` frames of other
/// walks in this crate measured ~2.8x larger, which this margin also
/// absorbs).
///
/// Lowering the cap is *honest*: the flag routes to `Unknown`, never to a
/// wrong answer.  The completeness cost is confined to formulas nested
/// deeper than 512 — the SMT-LIB parser already refuses raw nesting past
/// 1024 (`MAX_PARSE_DEPTH`), so only the 513..=1024 band of parseable
/// scripts (and arbitrarily deep API-built terms) moves from "encoded" to
/// "honest `Unknown`", whereas the old 2000 admitted terms whose encoding
/// died on the native stack.  Every other recursive pass that runs behind
/// the assert-time gate (`simplify`, `collect_polarities`, Skolemization,
/// `eval_in_model`) inherits the same tightened bound.
pub(super) const ENCODE_DEPTH_LIMIT: u32 = 512;

/// A fully-evaluated ground value used by the model-verification soundness gate
/// ([`Solver::model_refutes_assertions`]).  Integers and reals are unified as an
/// exact rational so mixed Int/Real arithmetic and comparisons fold without loss.
#[derive(Debug, Clone, Copy, PartialEq)]
pub(super) enum EvalVal {
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
            derived_reasons: theory_manager::DerivedReasons::default(),
            #[cfg(feature = "std")]
            nlsat: None,
            mbqi: MBQIIntegration::new(),
            ematch_engine: EmatchingEngine::new(EmatchingConfig::default()),
            has_quantifiers: false,
            next_skolem_id: 0,
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
            ite_result_terms: FxHashSet::default(),
            dt_var_constructors: FxHashMap::default(),
            arith_parse_cache: FxHashMap::default(),
            tracked_compound_terms: FxHashSet::default(),
            encoded_terms: FxHashMap::default(),
            fp_constraint_cache: FxHashMap::default(),
            encode_depth_exceeded: false,
            has_array_ops: false,
            array_axiom_instances: FxHashSet::default(),
            arith_defined_terms: FxHashSet::default(),
            arith_const_axiom_pairs: FxHashSet::default(),
            dt_axiom_instances: FxHashSet::default(),
            dt_axioms_incomplete: false,
            entailed_int_consts: FxHashMap::default(),
            entailed_int_consts_upto: 0,
            #[cfg(test)]
            mbqi_round_clauses: Vec::new(),
            last_check: None,
            settings_epoch: 0,
            case_split_terms: FxHashSet::default(),
            case_split_rounds: 0,
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

    /// Check if theory-aware branching is enabled
    #[must_use]
    pub fn theory_aware_branching(&self) -> bool {
        self.theory_aware_branching
    }

    /// Register a declared constant as an MBQI ground instantiation candidate.
    ///
    /// This must be called from the context layer whenever a `declare-const`
    /// command is processed, so that trigger-free quantifiers can be
    /// instantiated with constants that exist in scope.
    pub fn register_declared_const(&mut self, term: TermId, sort: SortId) {
        self.mbqi.register_declared_const(term, sort);
    }

    /// Check satisfiability of the asserted formulas.
    ///
    /// Wraps the private `Solver::check_core` with the arithmetic-definition
    /// fixpoint.
    /// `div`/`mod`/numeric-`ite` terms are opaque atoms to the linear solver and
    /// only carry meaning once `Solver::instantiate_arith_axioms` has asserted
    /// their defining axioms.  `check_core` axiomatises everything reachable
    /// from the assertions up front, but a lemma generated *during* the search
    /// can internalise a fresh such term afterwards — an MBQI instantiation, or
    /// an array read-over-write lemma whose `ite` is Int-sorted.  Each round
    /// here supplies the missing definitions and re-solves; when no definition
    /// can be supplied (a symbolic divisor) the verdict degrades to `Unknown`
    /// rather than trusting an atom the SAT core treated as a free Boolean.
    ///
    /// # Repeating a check on an unchanged goal costs nothing
    ///
    /// One `check` is one MBQI search, and it leaves no trace of itself behind:
    /// the candidate pool, dedup filter, blind-instantiation guard and round
    /// budget are snapshotted on entry and restored on exit — see
    /// [`MBQIIntegration::restore_search_state`] for the field-by-field split
    /// between goal state and search state.
    ///
    /// Above that, a repeated query on a goal the caller has not touched is
    /// answered from the previous verdict rather than run again.  Re-running is
    /// not idempotent — the SAT solver keeps what it learned, so the second
    /// search ends on a different model, and a model-based instantiator handed a
    /// different model emits lemmas over ground terms that did not exist before
    /// — and those clauses can never be retracted, because the assertion stack
    /// never moved (task #28).  The cache is dropped by
    /// `Solver::invalidate_results`, the same hook that drops the model and
    /// unsat core beside it, and is additionally gated on a structural
    /// fingerprint of the goal; the `solver::verdict_cache` module carries the
    /// full argument for why it cannot go stale.  Everything the caller is
    /// entitled to keep across
    /// checks is kept: the asserted and lemma clauses, the Tseitin memo, the
    /// registered quantifiers, and any candidate registered outside a check.
    pub fn check(&mut self, manager: &mut TermManager) -> SolverResult {
        let fingerprint = self.goal_fingerprint();
        if let Some(cached) = self.cached_verdict(&fingerprint) {
            return cached;
        }

        let mbqi_checkpoint = self.mbqi.search_checkpoint();
        let result = self.check_with_arith_refinement(manager);
        self.mbqi.restore_search_state(&mbqi_checkpoint);
        self.remember_verdict(result);
        result
    }

    /// The body of [`Self::check`], minus the caching and the MBQI search-state
    /// restore that wrap it.  Split out so both cover every exit, including the
    /// honesty gates' early returns.
    fn check_with_arith_refinement(&mut self, manager: &mut TermManager) -> SolverResult {
        /// Refinement rounds allowed before conceding.  Each round strictly
        /// grows `arith_defined_terms`, and the loop exits as soon as it stops
        /// growing, so this is only a guard against pathological growth.
        const MAX_ARITH_DEFINITION_ROUNDS: usize = 4;

        self.debug_check_invariants("check: entry");
        let mut result = self.check_core(manager);
        for _ in 0..MAX_ARITH_DEFINITION_ROUNDS {
            // Nothing left to refine.  `break` rather than `return`: the gates
            // below are the single exit for a `Sat` verdict, and returning here
            // would skip them.
            if result != SolverResult::Sat || !self.arith_defs_incomplete(manager) {
                break;
            }
            let defined_before = self.arith_defined_terms.len();
            self.instantiate_arith_axioms(manager);
            if self.arith_defined_terms.len() == defined_before {
                // Nothing new could be defined: the offending term has no linear
                // axiomatisation (a symbolic divisor).  Fall through to the gate.
                break;
            }
            result = self.check_core(manager);
        }
        // Honesty gate (soundness): the Tseitin encoder can refuse a sub-term
        // *during* the search as well.  MBQI instantiation results and
        // E-matching lemmas are encoded mid-loop, never pass the assert-time
        // depth pre-check, and `encode_depth`'s own cap then fires *after*
        // `check_core` consulted `encode_depth_exceeded` at its top.  A
        // truncated encoding only ever drops clauses, so an `Unsat` stays
        // sound, but a `Sat` may rest on constraints the truncation lost and
        // must degrade to `Unknown`.
        if result == SolverResult::Sat && self.encode_depth_exceeded {
            self.model = None;
            self.unsat_core = None;
            return SolverResult::Unknown;
        }
        if result == SolverResult::Sat && self.arith_defs_incomplete(manager) {
            self.model = None;
            self.unsat_core = None;
            return SolverResult::Unknown;
        }
        // Honesty gate (soundness): the datatype axiom budget ran out, so the
        // formula was solved against a strict subset of the datatype theory.
        // `Unsat` from a subset of the axioms is still `Unsat`; a `Sat` is a
        // guess and is reported as `Unknown`.
        if result == SolverResult::Sat && self.dt_axioms_incomplete {
            self.model = None;
            self.unsat_core = None;
            return SolverResult::Unknown;
        }
        self.debug_check_invariants("check: exit");
        result
    }

    /// Return the incremental theory solvers to their base scope, keeping every
    /// fact the next search round is entitled to and dropping every fact that
    /// belonged to a search *branch*.
    ///
    /// # The leak this closes
    ///
    /// [`TheoryManager`] opens exactly one theory scope per SAT decision level
    /// (`push_theory_scope`) and unwinds them from its own `level_stack` on
    /// backtrack.  A CDCL(T) search that ends `Sat` **never backtracks**, so it
    /// returns with the EUF / arithmetic / bit-vector solvers several scopes
    /// deep, holding every assertion the winning branch made.  A fresh manager —
    /// built for the next MBQI round, or for the next `check` — starts with
    /// `level_stack == vec![0]`, and from that instant those scopes are
    /// *unreachable*: `on_backtrack(l)` pops only while `level_stack.len() > l +
    /// 1`, which is already false.  The branch's facts are committed for the
    /// lifetime of the `Solver`.
    ///
    /// That is a soundness hazard, not merely a leak.  The MBQI round that
    /// follows exists precisely to *retract* the branch the previous round chose:
    /// it adds an instantiation lemma such as `f(1) = 100 ⇒ x ≠ 1`, whose unit
    /// form drops the SAT trail to the root.  The next round then asserts `x ≠ 1`
    /// into a tableau that still contains the leaked `x = 1`, the arithmetic
    /// solver refutes it at decision level 0, and `solve_with_theory` answers
    /// `Unsat` on a satisfiable goal — before conflict analysis runs, so no
    /// honesty net is even consulted.
    ///
    /// # What the next round is entitled to
    ///
    /// Exactly the facts implied by the **root-level** SAT trail: the original
    /// ground assertions, plus every quantifier instance / e-matching lemma MBQI
    /// chose to keep.  The kept lemmas are universally justified instantiations,
    /// so they are sound at the base scope — and they are not stored in the
    /// theory solvers at all.  They live in the SAT clause database, where
    /// [`Self::encode`] put them and `oxiz_sat::Solver::add_clause` committed
    /// their unit consequences at the root.  What must *not* survive is the
    /// third category: assertions that were merely a search-branch decision.
    ///
    /// # Why reset-and-replay rather than popping the leaked scopes
    ///
    /// Popping down to the base scope looks more surgical, and it was tried: it
    /// makes the MBQI loop diverge on `tests/mbqi_sat_certification.rs`.  The
    /// reason is that popping addresses only half of the desynchronisation.  The
    /// SAT trail and the theory scope stack must be re-aligned *together*, and
    /// the SAT side is already at the root (`add_clause` calls
    /// `backtrack_to_root` for a unit lemma without notifying the theory layer).
    /// Unwinding the theory scopes alone leaves the next round replaying the
    /// whole trail — decisions included — into what it believes is the base
    /// scope, which commits the *new* branch's facts permanently instead of the
    /// old one's: the same defect, one round later, and now unrecoverable.
    ///
    /// Dropping the trail to the root and re-deriving the theory state from it is
    /// the alignment that actually holds.  `solve_with_theory` restarts with
    /// `theory_processed == 0` and replays the entire trail through
    /// `TheoryManager::on_assignment`, so the three solvers are repopulated —
    /// through the ordinary assert path, re-interning terms and re-registering
    /// theory variables as they go — from exactly the constraints that are active
    /// now.  Nothing is re-encoded, so the clause database and the
    /// [`Self::encoded_terms`] memo are untouched and the clause count plateaus
    /// across rounds (`scope_rebase_tests::clause_count_plateaus_across_rounds`).
    ///
    /// This is the same reset-and-replay strategy the array-axiom refinement
    /// rounds and [`TheoryManager::resync_theory_state`] already rely on; the
    /// solvers support only level-scoped `pop`, never point removal of a single
    /// mid-scope assertion, so it is also the only available way to retract a
    /// fact that a leaked scope has put out of reach.
    ///
    /// # The one seam for theory-state teardown
    ///
    /// Four sites need the theory solvers returned to a state that reflects only
    /// what is currently asserted, and all four call this function: `check`'s
    /// entry, the array-axiom refinement boundary, the MBQI round boundary, and
    /// [`Self::pop`].  They are deliberately *not* allowed to hand-roll the set
    /// — see the comment in `pop`, where an open-coded copy of it drifted (it
    /// omitted `bv.reset()`).  [`Self::reset`] is the one exception: it performs
    /// a strictly larger teardown that also drops the quantifier engines, the
    /// term/variable tables and every side cache, so it does not reduce to this.
    ///
    /// # Invariant: theory-variable registrations are re-derived, never carried
    ///
    /// The encoder registers theory variables directly into these long-lived
    /// solvers as it internalises a term — `Solver::register_arith_atom` calls
    /// `ArithSolver::intern`, the `Var` arm of `encode_depth` calls it and
    /// `BvSolver::new_bv`.  Those registrations are wiped by the resets here, so
    /// the invariant this function relies on is:
    ///
    /// > every theory-variable registration a later round needs is re-performed
    /// > by the trail replay, not inherited from before the rebase.
    ///
    /// It holds because the theory solvers are told about a term only through
    /// an assertion, and every assertion path re-registers what it mentions:
    /// `ArithSolver::assert_{eq,le,ge,lt,gt}` call `intern` on each term of the
    /// linear expression they are given, `TheoryManager::process_constraint`
    /// re-interns EUF nodes through `intern_term_for_congruence` (plus
    /// `intern_arith_shared_terms` for the arithmetic operands), and
    /// `bit_blast_bv_pair` re-blasts both operands — falling back to
    /// `BvSolver::new_bv` for a leaf — before every BV check.  The replay runs
    /// `on_assignment` over the *whole* trail, so each of those paths is taken
    /// again for every atom that is still asserted.
    ///
    /// The encoder-side memos (`Solver::arith_terms`, `Solver::bv_terms`,
    /// `Solver::tracked_compound_terms`) are *not* cleared, and deliberately so:
    /// they gate assert-time work — journalling a `TrailOp`, walking a compound
    /// term — and not the theory-solver registration, which the replay owns.
    /// Clearing them would re-journal trail operations for assertions that are
    /// already on the trail.  The consequence to be aware of is the converse: a
    /// term in `arith_terms` that appears in *no* asserted constraint (so the
    /// replay never re-interns it) loses its `ArithSolver` variable and hence
    /// its model value.  That is a model-completeness matter, not a soundness
    /// one — such a term is unconstrained by construction, so any value
    /// satisfies it, `Model` completion supplies one, and the candidate model is
    /// still put through `Solver::model_refutes_assertions` before any `Sat`.
    fn rebase_theory_state(&mut self) {
        // Root-level facts stay on the trail; only the decisions go.
        self.sat.backtrack_to_root();
        self.euf.reset();
        self.arith.reset();
        // The bit-vector solver additionally accumulates unit facts at its own
        // base level (`assert_const` pinning `x = 5`), which are not wired into
        // `Solver::push` / `pop` at all and would otherwise outlive both the
        // check and a user `pop` — a stale `x = 5` refuting a later `(= x 6)`.
        self.bv.reset();
        // The tableau these explanations were read out of is gone, and so are
        // the equalities they justified; keeping them would let a later conflict
        // cite literals belonging to a retracted scope.  This also returns the
        // absolute scope-depth counter to zero, matching the solvers.
        self.derived_reasons.clear();
    }

    /// Get a SAT variable for a term, then check satisfiability
    fn check_core(&mut self, manager: &mut TermManager) -> SolverResult {
        // Per-search case-split bookkeeping: each CDCL search starts with a
        // fresh dedup set and round counter.  The case-split lemmas are added
        // at the current SAT assertion scope, so they are retracted by `pop`;
        // resetting here (rather than only on full `reset`) keeps the dedup set
        // consistent with the live clauses across a `push`/`check`/`pop` and a
        // later `check`, so a term a popped scope already split is re-split if
        // the live formula still needs it.  See [`int_case_split`].
        self.case_split_terms.clear();
        self.case_split_rounds = 0;
        // Check for trivial unsat (false assertion)
        if self.has_false_assertion {
            self.build_unsat_core_trivial_false();
            return SolverResult::Unsat;
        }

        if self.assertions.is_empty() {
            return SolverResult::Sat;
        }

        // Honesty gate (soundness): if the Tseitin encoder refused a
        // sub-formula because it was pathologically deep, the encoding is
        // incomplete and any model built over it is untrustworthy.
        //
        // This gate is deliberately the *first* thing after the two trivial
        // verdicts above.  `assert` sets the flag by skipping the deep term
        // entirely (see `encode.rs`), and every stage between here and the
        // CDCL(T) loop — the axiom instantiators, the five early-conflict
        // collectors, and the nonlinear/FP/string model attempts — walks those
        // same assertion terms.  Several of those walks recurse natively, so
        // running any of them on a term already known to exceed the encoder's
        // safe depth crashes the process instead of reaching this answer: a
        // flat `(str.++ x1 … x5000)` aborted here via
        // `check_string_constraints` -> `eval_ground_bool`, on a 1 MiB stack,
        // long before the gate was consulted.
        //
        // Cost of the earlier position: one of those collectors could have
        // refuted the assertion set outright, and an `Unsat` derived from a
        // partial encoding is still sound.  That precision is given up
        // knowingly — it only applies to inputs that carry an assertion deeper
        // than `ENCODE_DEPTH_LIMIT`, which the gate was already going to
        // answer `Unknown` for unless a collector happened to refute them
        // first, and "answers `Unknown`" beats "aborts the process".
        if self.encode_depth_exceeded {
            return SolverResult::Unknown;
        }

        // Supply the defining axioms of every internalised `div` / `mod` /
        // numeric-`ite` term before any stage inspects the arithmetic atoms:
        // without them those terms are free variables and both the honesty gate
        // and the CDCL(T) loop below would reason about a formula that has lost
        // the terms' semantics.
        self.instantiate_arith_axioms(manager);

        // Supply the defining axioms of every datatype term as well.  Without
        // them a selector, a tester and a constructor application are three
        // unrelated free symbols to the CDCL(T) core, and even
        // `(= (head l) 10) ∧ (= (head l) 11)` came back `sat`.
        self.instantiate_dt_axioms(manager);

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

        // Positive FP path (completeness without sacrificing soundness): before
        // conceding `Unknown` on FP atoms below, try to construct and *verify* a
        // concrete floating-point model.  `try_fp_model_sat` pins every FP-sorted
        // term to a bit-exact IEEE-754 value and only reports success when every
        // assertion evaluates to `true` under it, so the resulting `Sat` is a
        // genuine model witness rather than a guess.
        if self.fp_atoms_need_theory(manager) && self.try_fp_model_sat(manager) {
            return SolverResult::Sat;
        }

        // Honesty gate (soundness): there is no complete String / FP theory
        // wired into the CDCL(T) core — `encode.rs` maps string and FP atoms to
        // fresh SAT variables, and the checks above only detect a fixed set of
        // definite conflicts.  If any such atom survives without a proven
        // conflict, we must answer `Unknown` instead of letting the SAT core
        // treat it as a free Boolean, which would report a spurious `Sat` for
        // formulas like `(= s "abc") ∧ (str.contains s "xyz")` or
        // `fp.lt x y ∧ fp.lt y x`.
        if self.string_atoms_need_theory(manager) {
            // Before conceding, try to construct and verify a concrete string
            // model. A verified witness is a sound `Sat` certificate; otherwise
            // keep the honest `Unknown`.
            if self.ground_string_model_sat(manager) {
                return SolverResult::Sat;
            }
            return SolverResult::Unknown;
        }
        if self.fp_atoms_need_theory(manager) {
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

        // Check resource limits before starting
        if self.config.max_conflicts > 0 && self.statistics.conflicts >= self.config.max_conflicts {
            return SolverResult::Unknown;
        }
        if self.config.max_decisions > 0 && self.statistics.decisions >= self.config.max_decisions {
            return SolverResult::Unknown;
        }

        // Seam 1 of 2: rebuild all three incremental theory solvers from the
        // live assertion set before this check starts searching.
        //
        // The previous `check` on this solver ended either `Sat` — in which case
        // it never backtracked and left the theory solvers several decision
        // scopes deep, holding that check's branch facts — or `Unsat`, which
        // returns from `solve_with_theory` without unwinding either.  Nothing
        // between two `check` calls pops those scopes: `Solver::pop` is the only
        // other place that clears them, and a script need never call it.  An
        // interposed `(check-sat)` could therefore change the answer of the next
        // one, which is exactly what `tests/scope_leak_hazard.rs` demonstrates.
        //
        // See `rebase_theory_state` for why this is a reset-and-replay rather
        // than a scope unwind, and for the BV solver's own (older) reason to be
        // reset here: its base-level unit facts are not wired into
        // `Solver::push` / `pop` and would leak across a user scope as well.
        self.rebase_theory_state();

        // z3-style axiom-based arithmetic↔EUF equality sharing: add triangle
        // axioms `(t = c) ⟺ (t ≤ c ∧ t ≥ c)` for the fresh `ite`-result terms
        // vs the integer constants in the formula.  This lets CDCL + the arith
        // consistency check drive theory combination soundly (atom-backed merge
        // reasons), complementing the model-based merging in `final_check`.
        // Must run after all assertions are encoded so the arith term set is
        // complete.
        self.axiomatize_arith_constant_equalities(manager);

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
            &self.ite_result_terms,
            &mut self.derived_reasons,
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

        // Lazy array-axiom refinement rounds (see `instantiate_array_axioms`).
        // Bounded independently of the MBQI budget; deduplication guarantees
        // saturation well within this generous cap for realistic inputs.
        let max_array_refinement_rounds = 256;
        let mut array_refinement_rounds = 0;

        // Stamp the start of the search so the non-convex-LIA case-split
        // refinement can be gated on how long the first solve took: the
        // refinement re-solves the whole problem from scratch, so it is only
        // affordable when the first solve was fast.  On a slow (hard) instance
        // we skip it rather than blow the time budget and turn a fast wrong
        // answer into a slow timeout.
        #[cfg(feature = "std")]
        let check_start = std::time::Instant::now();

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
            //
            // `unjustified_conflict` is the same shape for a different cause:
            // a theory refuted the assignment but the manager could not build a
            // clause for it (no reason literal could be blamed), so the conflict
            // was aborted instead of being emitted as the empty clause.  A
            // dropped conflict never justifies `Sat` either.
            let resource_exhausted =
                theory_manager.resource_exhausted() || theory_manager.unjustified_conflict();
            match sat_result {
                SatResult::Unsat => {
                    self.build_unsat_core();
                    // After a theory/Boolean conflict has been turned into an
                    // unsat core: the core must name assertions that still
                    // exist in this context (see `check_unsat_core`).
                    self.debug_check_invariants("check_core: after unsat-core construction");
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
                        // Non-convex LIA refinement: an integer UF argument
                        // pinned to a small finite domain by arithmetic bounds is
                        // invisible to Nelson–Oppen equality sharing (the
                        // disjunction is never entailed case-by-case), so the
                        // CDCL core has no atom to branch on its value and a
                        // genuine `unsat` is wrongly reported `sat`.  Emit an
                        // explicit `(or (= t lo) … (= t hi))` lemma for each
                        // such term and re-solve.  See
                        // [`Solver::refine_int_case_split`].  Gated on the
                        // first solve being fast: the refinement re-solves the
                        // whole problem from scratch, so on a slow (hard)
                        // instance we skip it rather than blow the time budget.
                        #[cfg(feature = "std")]
                        let case_split_affordable = check_start.elapsed()
                            < std::time::Duration::from_millis(
                                int_case_split::CASE_SPLIT_REFINE_BUDGET_MS,
                            );
                        #[cfg(not(feature = "std"))]
                        let case_split_affordable = true;
                        if case_split_affordable && self.refine_int_case_split(manager) {
                            // Re-solve with the freshly asserted case-split
                            // lemmas from a clean state.  `add_clause` left the
                            // SAT core at the candidate model's trail; the
                            // incremental theory solvers still hold that
                            // model's facts, which cannot be surgically undone
                            // (only level-scoped pops), so we drop the trail to
                            // root and reset the three theory solvers.  The fresh
                            // `TheoryManager` then re-drives them from scratch.
                            self.sat.backtrack_to_root();
                            self.euf.reset();
                            self.arith.reset();
                            self.bv.reset();
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
                                &self.ite_result_terms,
                                &mut self.derived_reasons,
                                self.config.theory_mode,
                                &mut self.statistics,
                                self.config.max_conflicts,
                                self.config.max_decisions,
                                self.has_bv_arith_ops,
                                self.config.timeout_ms,
                            );
                            continue;
                        }
                        // Lazy array-axiom instantiation: the syntactic array
                        // pre-checks and EUF congruence do not implement a
                        // complete array decision procedure, so a candidate `Sat`
                        // may violate read-over-write / extensionality.  Watch the
                        // array terms in this candidate model and assert every
                        // axiom instance it does not already satisfy as a lemma,
                        // then re-solve.  Only genuine array models survive.
                        if self.has_array_ops && self.instantiate_array_axioms(manager) {
                            array_refinement_rounds += 1;
                            if array_refinement_rounds >= max_array_refinement_rounds {
                                // Could not saturate the array axioms within the
                                // round budget: do not fabricate a verdict.
                                return SolverResult::Unknown;
                            }
                            // A read-over-write lemma is an `ite` over the two
                            // array values; at Int/Real sort that `ite` is a new
                            // opaque arithmetic atom, so define it before the
                            // re-solve or the lemma carries no numeric meaning.
                            self.instantiate_arith_axioms(manager);
                            // Re-solve with the freshly asserted array lemmas from
                            // a clean state.  `add_clause` backtracked the SAT core
                            // to root for the unit lemmas, but the incremental
                            // theory solvers still hold the facts committed by the
                            // just-refuted candidate model (e.g. a stale
                            // `select = 6`) — including any left in scopes this
                            // round's search never unwound.
                            self.rebase_theory_state();
                            // After backtracking to root and resetting the
                            // theory solvers: the SAT-variable <-> term tables
                            // and the Tseitin memo are *not* reset here, so
                            // they must still describe the same variables the
                            // replayed search will re-derive.
                            self.debug_check_invariants("check_core: after array-lemma backtrack");
                            // Re-solve with the freshly asserted array lemmas.
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
                                &self.ite_result_terms,
                                &mut self.derived_reasons,
                                self.config.theory_mode,
                                &mut self.statistics,
                                self.config.max_conflicts,
                                self.config.max_decisions,
                                self.has_bv_arith_ops,
                                self.config.timeout_ms,
                            );
                            continue;
                        }
                        self.unsat_core = None;
                        self.debug_check_invariants("check_core: before returning sat");
                        return SolverResult::Sat;
                    }

                    // Build partial model for MBQI
                    self.build_model(manager);

                    // Certified `sat`: for the fragments `mbqi::model_certify`
                    // covers, a *total* interpretation of every symbol can be
                    // constructed from this candidate model and checked
                    // against every assertion — quantified ones included, over
                    // their whole infinite domain.  When that check passes we
                    // hold a model in the ordinary semantic sense, so `sat`
                    // follows outright and MBQI has nothing left to add.  When
                    // it does not, nothing changes: the certifier declines and
                    // the instantiation loop below runs exactly as before.
                    if self.certify_quantified_sat(manager) {
                        self.unsat_core = None;
                        self.debug_check_invariants(
                            "check_core: before returning sat (certified model)",
                        );
                        return SolverResult::Sat;
                    }

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
                            self.debug_check_invariants(
                                "check_core: before returning sat (no quantifiers)",
                            );
                            return SolverResult::Sat;
                        }
                        MBQIResult::Satisfied => {
                            // All quantifiers satisfied by the current model.
                            self.unsat_core = None;
                            self.debug_check_invariants(
                                "check_core: before returning sat (mbqi fixpoint)",
                            );
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
                            // Turn the reason into a blocking clause — but only
                            // if *every* reason term names a literal.  Skipping
                            // the ones that do not would not weaken the clause,
                            // it would strengthen it into a claim the reason
                            // never made: that the surviving literals alone are
                            // contradictory.  When the reason cannot be
                            // expressed we add nothing and let the bounded MBQI
                            // loop run out, which costs a round rather than
                            // correctness.
                            let lits: Option<Vec<Lit>> = reason
                                .iter()
                                .map(|&t| self.term_to_var.get(&t).map(|&v| Lit::neg(v)))
                                .collect();
                            if let Some(lits) = lits
                                && !lits.is_empty()
                            {
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
                                    self.debug_check_invariants(
                                        "check_core: before returning sat (trivially valid)",
                                    );
                                    return SolverResult::Sat;
                                }
                                return SolverResult::Unknown;
                            }
                            // Continue MBQI loop
                        }
                    }

                    mbqi_iteration += 1;
                    #[cfg(test)]
                    {
                        self.mbqi_round_clauses.push(self.sat.num_clauses());
                    }
                    if mbqi_iteration >= max_mbqi_iterations {
                        return SolverResult::Unknown;
                    }

                    // MBQI round boundary: this round encoded fresh
                    // instantiation / e-matching lemmas through `encode`, each
                    // of which may allocate SAT variables and extend the
                    // Tseitin memo.  Check before the next round consumes them.
                    self.debug_check_invariants("check_core: mbqi round boundary");

                    // Seam 2 of 2: rebuild the theory solvers before the next
                    // round searches.
                    //
                    // The round that just finished ended `Sat`, so it never
                    // backtracked and left one theory scope open per decision it
                    // took, holding that branch's facts.  The lemmas encoded
                    // just above exist to *retract* that very branch, and the
                    // fresh manager below would assert their consequences on top
                    // of the facts they contradict — in scopes it cannot reach,
                    // because it numbers its own `level_stack` from zero.  That
                    // is the task-#26 false `unsat`.
                    //
                    // What the next round is entitled to survives untouched: the
                    // ground assertions and every kept instantiation / e-matching
                    // lemma live in the SAT clause database with their unit
                    // consequences committed at the root, and the replay below
                    // re-derives the theory state from exactly those.  Nothing is
                    // re-encoded, so no clause is duplicated.
                    self.rebase_theory_state();
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
                        &self.ite_result_terms,
                        &mut self.derived_reasons,
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
    ///
    /// # Why the verdict survives the internal `pop`
    ///
    /// The assumption scope is realised as `push` / `assert` / `check` / `pop`,
    /// and [`Self::pop`] discards the results of the last check (see the private
    /// `Solver::invalidate_results`).  That rule is right for a *user* `pop`,
    /// which replaces the assertion stack, and wrong here: SMT-LIB 2.6 leaves
    /// `check-sat-assuming` in `sat` / `unsat` mode, so a following
    /// `(get-value ...)` / `(get-model)` must still read this check's model.
    ///
    /// Carrying the model across is sound because the assumption scope is a
    /// strict *extension* of the assertion stack: a model of
    /// `assertions ∧ assumptions` satisfies `assertions`, which is exactly the
    /// stack that survives the `pop`.
    ///
    /// The unsat core is carried under one condition, which is a soundness
    /// condition and not merely a bounds check.  With `:produce-unsat-cores` on
    /// every assumption is itself a tracked assertion, and `build_unsat_core`
    /// lists *every* tracked assertion — so a core computed here names an
    /// assumption index whenever any assumption was in play.  Such an index is
    /// past the end of the post-`pop` `assertions` vector: it dangles, exactly
    /// the failure the rule exists to prevent, and `invariants::check_unsat_core`
    /// rejects it.  Conversely a core that survives the range check is one that
    /// named no assumption at all, which makes it a core of the surviving stack.
    /// So: keep it when every index still resolves, drop it otherwise — and
    /// `(get-unsat-core)` then answers the standard "not available" error rather
    /// than a set that is not unsatisfiable on its own.
    ///
    /// The proof is deliberately *not* carried.  A refutation of
    /// `assertions ∧ assumptions` is not a refutation of `assertions`, so
    /// letting `(get-proof)` report it would be the same error the unsat-core
    /// condition above rules out, minus the index that makes it detectable.
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

        // Take the verdict out before the `pop` drops it, then restore it (see
        // the doc comment for why each half is or is not allowed to survive).
        let model = self.model.take();
        let unsat_core = self.unsat_core.take();

        // Restore state
        self.pop();

        self.model = model;
        let num_assertions = self.assertions.len() as u32;
        self.unsat_core =
            unsat_core.filter(|core| core.indices.iter().all(|&i| i < num_assertions));
        self.debug_check_invariants("after check_with_assumptions");

        result
    }

    /// Whether a complete interpretation satisfying *every* assertion can be
    /// built from the current candidate model and verified.
    ///
    /// This is the honest route from "the ground search is satisfied" to `sat`
    /// on a quantified goal: [`crate::mbqi::model_certify::certify`] answers
    /// `true` only with a total interpretation in hand that it has checked
    /// against every assertion, quantifiers included, over the whole of their
    /// domain.  A `false` answer claims nothing and leaves the caller's
    /// existing behaviour — ultimately `unknown` — in place.
    fn certify_quantified_sat(&mut self, manager: &TermManager) -> bool {
        let Some(model) = self.model.as_ref() else {
            return false;
        };
        let assignments = model.assignments().clone();
        crate::mbqi::model_certify::certify(&self.assertions, &assignments, manager)
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
        // Trivial verdicts first, mirroring `check_core`: an asserted `False`
        // never reaches the SAT core as a clause (`assert` records the flag
        // and returns), so solving the clause set alone would miss it and
        // report a wrong `Sat` for e.g. `{false}`.
        if self.has_false_assertion {
            return SolverResult::Unsat;
        }
        if self.assertions.is_empty() {
            return SolverResult::Sat;
        }
        // Honesty gate (soundness): an assertion the encoder refused because
        // it nests deeper than `ENCODE_DEPTH_LIMIT` contributed *no clauses at
        // all*, so even the pure-SAT view of the problem is incomplete — a
        // verdict over the remaining clauses would be a guess about a formula
        // this solver never saw.  Same rule as `check_core`'s top gate.
        if self.encode_depth_exceeded {
            return SolverResult::Unknown;
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

    /// Assert multiple terms at once
    /// This is more efficient than calling assert() multiple times
    pub fn assert_many(&mut self, terms: &[TermId], manager: &mut TermManager) {
        for &term in terms {
            self.assert(term, manager);
        }
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
        // A `push` opens a scope the previous verdict knew nothing about.  It
        // adds no assertion by itself, so the old model would still satisfy the
        // stack *at this instant* — but the only way to observe it is to ask
        // after the `assert`s that follow, by which time it is stale.  Dropping
        // it here rather than at the first following `assert` keeps the rule
        // stated once ("the verdict belongs to the stack it was computed on")
        // instead of depending on what the caller does next.
        self.invalidate_results();
        self.context_stack.push(ContextState {
            num_assertions: self.assertions.len(),
            num_vars: self.var_to_term.len(),
            has_false_assertion: self.has_false_assertion,
            trail_position: self.trail.len(),
            num_mbqi_quantifiers: self.mbqi.num_quantifiers(),
            num_ematch_quantifiers: self.ematch_engine.num_quantifiers(),
            has_quantifiers: self.has_quantifiers,
            has_bv_arith_ops: self.has_bv_arith_ops,
            has_array_ops: self.has_array_ops,
            encode_depth_exceeded: self.encode_depth_exceeded,
            dt_axioms_incomplete: self.dt_axioms_incomplete,
        });
        self.sat.push();
        // No EUF / arithmetic scope is opened here on purpose.
        //
        // It used to be, and it was an *untracked* scope: it bypassed
        // `TheoryManager::push_theory_scope`, so the absolute depth counter in
        // `derived_reasons` did not see it, and the matching `Solver::pop`
        // resets the two solvers wholesale rather than popping (see the comment
        // there for why a single pop retracted an arbitrary search scope).  A
        // push with no pop, invisible to the one counter that tracks the true
        // depth, is exactly the shape of defect `rebase_theory_state` exists to
        // remove.
        //
        // Dropping it is behaviour-preserving: every `check` now rebases the
        // three theory solvers at its entry and re-derives their state from the
        // SAT trail, so nothing between this `push` and the next verdict can
        // observe the scope, and `pop` resets regardless.
        #[cfg(feature = "std")]
        if let Some(nlsat) = &mut self.nlsat {
            nlsat.push();
        }
        self.debug_check_invariants("after push");
    }

    /// Pop a context level using trail-based undo
    pub fn pop(&mut self) {
        if let Some(state) = self.context_stack.pop() {
            // The verdict on the table was computed against the scope being
            // retracted.  Its unsat core indexes an `assertions` vector this
            // call is about to truncate, so keeping it hands
            // `minimize_unsat_core` a dangling index (it panicked outright on
            // `(push)(assert)(check-sat)(pop)(get-unsat-core)`) and trips
            // `invariants::check_unsat_core` in the debug net below.  See
            // `invalidate_results` for the rule.
            self.invalidate_results();

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
                            // Remove the constraint.  Every site that records a
                            // parsed linear constraint for a variable also
                            // records this op for the same variable, so the two
                            // maps are retracted together — a surviving
                            // `var_to_parsed_arith` entry would keep feeding a
                            // retracted inequality to the arithmetic solver.
                            self.var_to_constraint.remove(&var);
                            self.var_to_parsed_arith.remove(&var);
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
                        TrailOp::DtVarConstructorAdded { term } => {
                            // Forget the constructor this variable was pinned
                            // to; keeping it would make a later, unrelated
                            // constructor equality look mutually exclusive with
                            // a retracted one and force a wrong `unsat`.
                            self.dt_var_constructors.remove(&term);
                        }
                        TrailOp::TrackedCompoundAdded { term } => {
                            // Re-open this compound term for traversal: the
                            // theory-variable registrations the walk performed
                            // are themselves undone above, so the memo must go
                            // too or the sub-terms would never be re-registered.
                            self.tracked_compound_terms.remove(&term);
                        }
                        TrailOp::ArrayAxiomInstanceAdded { term } => {
                            // The lemma clause for this instance is retracted
                            // with the scope's clauses, so its dedup entry must
                            // go as well — otherwise a later scope would never
                            // re-assert an axiom it still needs.
                            self.array_axiom_instances.remove(&term);
                        }
                        TrailOp::ArithDefinedTermAdded { term } => {
                            // The defining lemmas for this `div`/`mod`/`ite`
                            // term are retracted with the scope's clauses, so
                            // the mark must go too: keeping it would let the
                            // honesty gate trust an atom whose meaning has just
                            // been dropped from the SAT core.
                            self.arith_defined_terms.remove(&term);
                        }
                        TrailOp::ArithConstAxiomAdded { term, const_val } => {
                            // The triangle clauses for this `(term, const)` pair
                            // are retracted with the scope's clauses; drop the
                            // dedup mark so a later `check` re-axiomatizes it.
                            self.arith_const_axiom_pairs.remove(&(term, const_val));
                        }
                        TrailOp::EncodedTermAdded { term, previous } => {
                            // Take back exactly this one memo write.  `None`
                            // means the term's whole encoding was emitted inside
                            // this scope (forget it, so the next `encode`
                            // re-emits); `Some` means only the implication
                            // direction that *widened* the coverage was (restore
                            // the narrower coverage, whose clauses predate the
                            // push and survive `sat.pop()`).
                            match previous {
                                Some(entry) => {
                                    self.encoded_terms.insert(term, entry);
                                }
                                None => {
                                    self.encoded_terms.remove(&term);
                                }
                            }
                        }
                        TrailOp::DtAxiomInstanceAdded { term } => {
                            // Same reasoning as the array axioms: the lemma
                            // clause is retracted with the scope's clauses, so
                            // its dedup entry must go too or a later scope would
                            // never re-assert a datatype axiom it still needs.
                            self.dt_axiom_instances.remove(&term);
                        }
                    }
                }
            }

            // Use state to restore other fields
            self.assertions.truncate(state.num_assertions);

            // Every entailed-constant entry was justified by *some* assertion,
            // and the truncation above may have retracted it.  Dropping the map
            // wholesale (rather than journalling each entry) keeps a popped
            // `(assert (= n 5))` from making a later quantifier's `(< i n)`
            // look like the concrete bound `i <= 4` — an unsound expansion.
            // The next quantified assertion re-folds the surviving assertions,
            // so the only cost is one linear re-scan per `pop`.
            self.entailed_int_consts.clear();
            self.entailed_int_consts_upto = 0;
            self.var_to_term.truncate(state.num_vars);
            self.has_false_assertion = state.has_false_assertion;

            // Quantifier reasoning state: MBQI and the e-matching engine turn a
            // registered quantifier into hard ground lemmas, so a quantifier
            // whose only asserting scope has been popped must stop being
            // instantiated (it produced a false `unsat` otherwise).  Both
            // registries are append-only, so the push-time counts restore them
            // exactly.
            self.mbqi.truncate_quantifiers(state.num_mbqi_quantifiers);
            self.ematch_engine
                .truncate_quantifiers(state.num_ematch_quantifiers);
            self.has_quantifiers = state.has_quantifiers;

            // Sticky encoder flags derived from the retracted assertions.
            self.has_bv_arith_ops = state.has_bv_arith_ops;
            self.has_array_ops = state.has_array_ops;
            self.encode_depth_exceeded = state.encode_depth_exceeded;
            self.dt_axioms_incomplete = state.dt_axioms_incomplete;

            // The Tseitin memo is retracted per entry, by the
            // `TrailOp::EncodedTermAdded` arm of the undo loop above — not
            // cleared wholesale, as it once was.  The clear was justified by
            // "`sat.pop()` retracts the definitional clauses of everything in
            // the memo", which holds only for entries written *inside* the
            // scope: an entry written outside keeps its clauses and (because
            // `TrailOp::VarCreated` is journalled) its SAT variable, so dropping
            // it made the next `encode` walk the term again and re-emit
            // byte-identical clauses that `oxiz_sat::Solver::add_clause` cannot
            // recognise as duplicates — one extra copy of the encoding per
            // `(push)(pop)` pair, growing without bound (task #28).  See
            // `Solver::memoize_encoding` for why the journalled `previous` value
            // makes the per-entry retraction exact.
            self.sat.pop();

            // Drop the incremental theory state instead of popping one scope off
            // it, through the *same seam* the search-time rebase uses.
            //
            // Their scope stacks are NOT aligned with the assertion scopes: the
            // CDCL(T) search pushes one theory scope per *decision level* and
            // `TheoryManager::resync_theory_state` rebuilds the stack from
            // scratch, so after a `check` the depth bears no relation to the
            // depth `Solver::push` left behind.  A single `pop` here therefore
            // retracted an arbitrary search scope and left facts derived from the
            // retracted assertions committed — an MBQI instantiation lemma
            // (`f(7) = 1`) survived its scope and refuted the satisfiable
            // `(= (f k) 2)` that followed the `pop`.
            //
            // Resetting is safe because the theory state is fully re-derived on
            // every `check`: `Solver::check` builds a fresh `TheoryManager` and
            // `solve_with_theory` replays the *entire* SAT trail through it, so
            // each solver is repopulated from exactly the constraints that are
            // active in the current context — which is precisely what
            // [`Self::rebase_theory_state`] documents and does.
            //
            // Routing through it (rather than repeating three of its five lines
            // here) is what keeps the two teardowns from drifting: this site used
            // to reset `euf` and `arith` and clear `derived_reasons` but *not*
            // reset `bv`, so a bit-vector unit fact pinned at the BV solver's own
            // base level (`assert_const` for `x = 5`) outlived the scope that
            // asserted it, until the next `check`'s rebase happened to clear it.
            // The `sat.backtrack_to_root()` the rebase performs first is a no-op
            // here: `sat.pop()` above already ends at decision level 0, and
            // `Trail::backtrack_to_with_callback` returns immediately when asked
            // for a level it is already at — in particular it does not disturb
            // the propagation head that `sat.pop()` deliberately rewound.
            self.rebase_theory_state();
            #[cfg(feature = "std")]
            if let Some(nlsat) = &mut self.nlsat {
                nlsat.pop();
            }

            #[cfg(debug_assertions)]
            self.debug_assert_scope_restored(&state);
            // Structural counterpart to the scope check above: the undo trail
            // must have left the term/variable maps, the side tables and the
            // remaining context snapshots mutually consistent.
            self.debug_check_invariants("after pop");
        }
    }

    /// Reset the solver
    pub fn reset(&mut self) {
        self.sat.reset();
        self.euf.reset();
        self.arith.reset();
        self.bv.reset();
        self.derived_reasons.clear();
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
        self.invalidate_results();
        self.context_stack.clear();
        self.trail.clear();
        self.logic = None;
        // `reset` clears the logic without going through `set_logic`, so it owes
        // the same announcement every setter in `solver::config` makes.
        self.settings_changed();
        self.theory_processed_up_to = 0;
        self.has_false_assertion = false;
        self.has_bv_arith_ops = false;
        self.polarities.clear();
        self.bv_terms.clear();
        self.arith_terms.clear();
        self.ite_result_terms.clear();
        self.dt_var_constructors.clear();
        self.arith_parse_cache.clear();
        self.tracked_compound_terms.clear();
        self.encoded_terms.clear();
        self.fp_constraint_cache.clear();
        self.encode_depth_exceeded = false;
        self.has_array_ops = false;
        self.array_axiom_instances.clear();
        self.arith_defined_terms.clear();
        self.arith_const_axiom_pairs.clear();
        // The assertions that entailed these constants are gone; a survivor
        // would license a finite-range expansion the new formula never asserts.
        self.entailed_int_consts.clear();
        self.entailed_int_consts_upto = 0;
        self.case_split_terms.clear();
        self.case_split_rounds = 0;
        self.debug_check_invariants("after reset");
    }

    /// Get solver statistics
    #[must_use]
    pub fn stats(&self) -> &oxiz_sat::SolverStats {
        self.sat.stats()
    }
}

#[cfg(test)]
mod scope_rebase_tests;
#[cfg(test)]
mod tests;
