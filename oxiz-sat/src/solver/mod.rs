//! CDCL SAT Solver

mod bve;
mod conflict;
mod congruence;
mod decide;
mod equiv;
pub mod heuristic;
mod incremental;
mod learn;
mod lucky;
mod propagate;
mod search_ext;

pub use heuristic::{BoxedBranchingHeuristic, BranchingHeuristic};

use crate::chb::CHB;
use crate::chrono::ChronoBacktrack;
use crate::clause::{ClauseDatabase, ClauseId};
use crate::literal::{LBool, Lit, Var};
use crate::lrb::LRB;
use crate::memory_opt::{MemoryAction, MemoryOptimizer};
#[allow(unused_imports)]
use crate::prelude::*;
use crate::restart_model::{GlueAverages, Reluctant};
use crate::trail::{Reason, Trail};
use crate::vmtf::VMTF;
use crate::vsids::VSIDS;
use crate::watched::{WatchLists, Watcher};
use core::sync::atomic::{AtomicBool, Ordering};
use smallvec::SmallVec;

// Packed per-variable LRAT minimization flags (`Flags` in upstream), stored
// in [`Solver::lrat_flags`] indexed by `Var::index()`. The bit layout mirrors
// cadical's `Flags` fields used by `minimize.cpp`.
pub(super) const MF_KEEP: u8 = 1;
pub(super) const MF_POISON: u8 = 2;
pub(super) const MF_REMOVABLE: u8 = 4;
pub(super) const MF_ADDED: u8 = 8;
pub(super) const MF_SEEN: u8 = 16;

/// Convert a path to a UTF-8 string for the file tracers (which take `&str`,
/// faithful to upstream). Returns an error for non-UTF8 paths.
fn path_to_str(path: &std::path::Path) -> std::io::Result<&str> {
    path.to_str().ok_or_else(|| {
        std::io::Error::new(
            std::io::ErrorKind::InvalidInput,
            "proof file path must be valid UTF-8",
        )
    })
}

/// Binary implication graph for efficient binary clause propagation
/// For each literal L, stores the list of literals that are implied when L is false
/// (i.e., for binary clause (~L v M), when L is assigned false, M must be true)
#[derive(Debug, Clone)]
pub(super) struct BinaryImplicationGraph {
    /// implications[lit] = list of (implied_lit, clause_id) pairs
    implications: Vec<Vec<(Lit, ClauseId)>>,
}

impl BinaryImplicationGraph {
    fn new(num_vars: usize) -> Self {
        Self {
            implications: vec![Vec::new(); num_vars * 2],
        }
    }

    fn resize(&mut self, num_vars: usize) {
        self.implications.resize(num_vars * 2, Vec::new());
    }

    fn add(&mut self, lit: Lit, implied: Lit, clause_id: ClauseId) {
        self.implications[lit.code() as usize].push((implied, clause_id));
    }

    fn get(&self, lit: Lit) -> &[(Lit, ClauseId)] {
        &self.implications[lit.code() as usize]
    }

    fn clear(&mut self) {
        for implications in &mut self.implications {
            implications.clear();
        }
    }

    /// Remove every edge belonging to `clause_id` that is keyed under `trigger`.
    /// Used to purge binary implications when a clause is retracted so the graph
    /// does not accumulate stale (and, after slot reuse, misleading) edges.
    fn remove_clause_edges(&mut self, trigger: Lit, clause_id: ClauseId) {
        let idx = trigger.code() as usize;
        if idx < self.implications.len() {
            self.implications[idx].retain(|(_, cid)| *cid != clause_id);
        }
    }
}

/// Result from a theory check
#[derive(Debug, Clone)]
pub enum TheoryCheckResult {
    /// Theory is satisfied under current assignment
    Sat,
    /// Theory detected a conflict, returns conflict clause literals
    Conflict(SmallVec<[Lit; 8]>),
    /// Theory propagated new literals (lit, reason clause)
    Propagated(Vec<(Lit, SmallVec<[Lit; 8]>)>),
}

/// Callback trait for theory solvers
/// The CDCL(T) solver implements this to receive theory callbacks
pub trait TheoryCallback {
    /// Called when a literal is assigned
    /// Returns a theory check result
    fn on_assignment(&mut self, lit: Lit) -> TheoryCheckResult;

    /// Called after propagation is complete to do a full theory check
    fn final_check(&mut self) -> TheoryCheckResult;

    /// Called when the decision level increases
    fn on_new_level(&mut self, _level: u32) {}

    /// Called when backtracking
    fn on_backtrack(&mut self, level: u32);
}

/// Result of SAT solving
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SolverResult {
    /// Satisfiable
    Sat,
    /// Unsatisfiable
    Unsat,
    /// Unknown (e.g., timeout, resource limit)
    Unknown,
}

/// Outcome of [`Solver::pre_check_effective_unit`], resolved *before* any
/// watches are chosen for a new clause in [`Solver::add_clause`].
enum PreAttachOutcome {
    /// Already satisfied by the current assignment, or simply not
    /// effectively unit (2+ literals still undefined). Either way, nothing
    /// special is needed: add and watch the clause normally.
    Ordinary,
    /// Every literal is false and, after resolving level-0-only facts via
    /// [`Solver::backtrack_to_root`] where needed, still is: an
    /// unconditional (level-0) conflict. The caller must set
    /// `trivially_unsat` and return `false` without adding the clause.
    UnconditionalConflict,
    /// The clause is an effective unit (every literal false except this one,
    /// which is undefined) and every false literal is confirmed to be a
    /// permanent level-0 fact. The caller must force this literal via
    /// `Trail::assign_propagation_at(_, clause_id, 0)` once the clause has
    /// been inserted and its `ClauseId` is known (not yet, at the point this
    /// outcome is produced).
    ForceUnitAtLevelZero(Lit),
}

/// Solver configuration
#[derive(Clone)]
pub struct SolverConfig {
    /// Restart interval (number of conflicts)
    pub restart_interval: u64,
    /// Restart multiplier for geometric restarts
    pub restart_multiplier: f64,
    /// Clause deletion threshold
    pub clause_deletion_threshold: usize,
    /// Variable decay factor
    pub var_decay: f64,
    /// Clause decay factor
    pub clause_decay: f64,
    /// Random polarity probability (0.0 to 1.0)
    pub random_polarity_prob: f64,
    /// Restart strategy: "luby" or "geometric"
    pub restart_strategy: RestartStrategy,
    /// Enable lazy hyper-binary resolution
    pub enable_lazy_hyper_binary: bool,
    /// Use CHB instead of VSIDS for branching
    pub use_chb_branching: bool,
    /// Use LRB (Learning Rate Branching) for branching
    pub use_lrb_branching: bool,
    /// Enable inprocessing (periodic preprocessing during search)
    pub enable_inprocessing: bool,
    /// Enable equivalent-literal substitution (SCC on the binary implication
    /// graph) as a one-shot pre-search pass. Sound and well-tested (50k+
    /// differential fuzz vs the un-substituted path), but OFF by default: it
    /// folds equivalent variables out of the search, which is incompatible with
    /// incremental/AllSAT clients that reference original variables between
    /// solve() calls, and on the one structured benchmark with many
    /// equivalences (`longmult15`, 29% of vars in SCCs) it does not help —
    /// CaDiCaL's edge there is pure search quality, not structural collapse.
    /// Enable for one-shot solving of binary-heavy formulas where collapsing
    /// equivalences is expected to pay off.
    pub enable_equiv_substitution: bool,
    /// Enable bounded variable elimination (BVE / SatELite) as a one-shot
    /// pre-search pass. Eliminates variables by resolving their clauses when
    /// the resolvents don't grow the formula, with model reconstruction. The
    /// most foundational SAT preprocessing technique. Off by default (same
    /// incremental/AllSAT caveat as substitution).
    pub enable_bve: bool,
    /// Inprocessing interval (number of conflicts between inprocessing)
    pub inprocessing_interval: u64,
    /// Enable chronological backtracking
    pub enable_chronological_backtrack: bool,
    /// Chronological backtracking threshold (max distance from assertion level)
    pub chrono_backtrack_threshold: u32,
    /// Cap on the Luby restart multiplier. The Luby sequence grows as 2^k, so
    /// without a cap the restart interval explodes on long runs into
    /// multi-10k-conflict grinds (a 3-30x slowdown vs cadical on r3sat
    /// n300/n350). 0 = uncapped (legacy). Default caps at 1024× the base
    /// restart interval.
    pub luby_cap: u64,
    /// Enable the cadical-style stable/focused restart schedule: alternate
    /// focused mode (frequent restarts, `focused_luby_cap`) and stable mode
    /// (rare restarts + rephase) on a quadratically-growing conflict schedule.
    /// Default true. Makes restart aggressiveness adaptive to the instance
    /// instead of a single fixed cap.
    pub enable_stabilize: bool,
    /// Base conflict interval for the first stable/focused switch; subsequent
    /// intervals grow quadratically (`base × phase²`).
    pub stabilize_base: u64,
    /// Luby restart cap used in *focused* mode (frequent restarts). Stable
    /// mode restarts uncapped (rare). 0 = uncapped.
    pub focused_luby_cap: u64,
    /// Use VMTF (variable move-to-front) as the decision heuristic instead
    /// of VSIDS — cadical's default focused-mode branching.
    pub use_vmtf: bool,
    /// Use VMTF (variable move-to-front) as the decision heuristic instead of
    /// VSIDS — cadical's default focused-mode branching. Conflict-involved
    /// variables are moved to the tail of a list; the next decision is the
    /// most-recently-bumped unassigned variable.
    /// Restarts between phase inversions (rephasing). 0 disables rephase.
    /// Periodically flipping the saved polarity lets a restart explore the
    /// complementary phase region instead of re-deriving the previous trail —
    /// essential for frequent (LBD) restarts to be productive rather than
    /// counterproductive.
    pub rephase_interval: u32,
    /// Whether restarts reuse the decision trail prefix (Heule/cadical
    /// reuse-trail) instead of backtracking to the root. Default true.
    pub reuse_trail: bool,
    /// Run failed-literal probing as the first step of inprocessing. Default
    /// true; can be disabled to exercise the other inprocessing passes
    /// (pure-literal / subsumption / strengthening) in isolation.
    pub enable_failed_literal_probing: bool,
    /// Run failed-literal probing with on-the-fly hyper-binary resolution as
    /// part of inprocessing. Default true when inprocessing is on.
    pub enable_hyper_binary_probing: bool,
    /// Try CaDiCaL-style "lucky" pre-solving phase guesses before search
    /// (uniform all-false / all-true, ordered-with-flip, positive/negative
    /// Horn). Default **true**, matching CaDiCaL's `opts.lucky = 1`: the
    /// strategies are soundness-preserving — a doomed guess performs at most a
    /// pure `O(|literals|)` scan or a single-literal-at-a-time probe that
    /// backtracks to the root on failure, so it never perturbs the search
    /// state. Set `false` to disable (e.g. to isolate search-only behaviour).
    pub enable_lucky: bool,
    /// Optional external branching heuristic. When `Some`, called before built-in
    /// VSIDS/LRB/CHB; returning `None` from the heuristic falls back to built-in.
    /// Default: `None` (pure built-in strategy).
    pub external_branching: Option<BoxedBranchingHeuristic>,
}

impl core::fmt::Debug for SolverConfig {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("SolverConfig")
            .field("restart_interval", &self.restart_interval)
            .field("restart_multiplier", &self.restart_multiplier)
            .field("clause_deletion_threshold", &self.clause_deletion_threshold)
            .field("var_decay", &self.var_decay)
            .field("clause_decay", &self.clause_decay)
            .field("random_polarity_prob", &self.random_polarity_prob)
            .field("restart_strategy", &self.restart_strategy)
            .field("enable_lazy_hyper_binary", &self.enable_lazy_hyper_binary)
            .field("use_chb_branching", &self.use_chb_branching)
            .field("use_lrb_branching", &self.use_lrb_branching)
            .field("enable_inprocessing", &self.enable_inprocessing)
            .field("inprocessing_interval", &self.inprocessing_interval)
            .field(
                "enable_chronological_backtrack",
                &self.enable_chronological_backtrack,
            )
            .field(
                "chrono_backtrack_threshold",
                &self.chrono_backtrack_threshold,
            )
            .field(
                "external_branching",
                &self
                    .external_branching
                    .as_ref()
                    .map(|_| "<BranchingHeuristic>"),
            )
            .finish()
    }
}

/// Restart strategy
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RestartStrategy {
    /// Luby sequence restarts
    Luby,
    /// Geometric restarts
    Geometric,
    /// Glucose-style dynamic restarts based on LBD
    Glucose,
    /// Local restarts based on LBD trail
    LocalLbd,
}

impl Default for SolverConfig {
    fn default() -> Self {
        Self {
            restart_interval: 100,
            restart_multiplier: 1.5,
            clause_deletion_threshold: 10000,
            var_decay: 0.95,
            clause_decay: 0.999,
            random_polarity_prob: 0.02,
            restart_strategy: RestartStrategy::Luby,
            // Off by default: the lazy hyper-binary derivation in
            // `check_hyper_binary_resolution` is not currently sound.  Its learned
            // binaries go straight into the binary implication graph, where they
            // both propagate and act as conflict reasons, so an unimplied one
            // produces a wrong top-level UNSAT on satisfiable input (QF_UF
            // quasigroup `iso_brn*`: enabling it flips `sat` to `unsat`, and a
            // wrong UNSAT can only come from a clause the formula does not
            // entail).  Re-enable once the derivation is proven and tested.
            enable_lazy_hyper_binary: false,
            use_chb_branching: false,
            use_lrb_branching: false,
            enable_inprocessing: false,
            enable_equiv_substitution: false,
            enable_bve: false,
            inprocessing_interval: 5000,
            enable_chronological_backtrack: true,
            chrono_backtrack_threshold: 100,
            luby_cap: 64,
            enable_stabilize: true,
            stabilize_base: 5000,
            focused_luby_cap: 16,
            use_vmtf: true,
            rephase_interval: 0,
            reuse_trail: true,
            enable_failed_literal_probing: true,
            enable_hyper_binary_probing: true,
            enable_lucky: true,
            external_branching: None,
        }
    }
}

/// Statistics for the solver
#[derive(Debug, Default, Clone)]
pub struct SolverStats {
    /// Number of decisions made
    pub decisions: u64,
    /// Number of propagations
    pub propagations: u64,
    /// Number of conflicts
    pub conflicts: u64,
    /// Number of restarts
    pub restarts: u64,
    /// Number of learned clauses
    pub learned_clauses: u64,
    /// Number of deleted clauses
    pub deleted_clauses: u64,
    /// Number of binary clauses learned
    pub binary_clauses: u64,
    /// Number of unit clauses learned
    pub unit_clauses: u64,
    /// Number of variables eliminated by equivalent-literal substitution.
    pub substitutions: u64,
    /// Number of variables eliminated by bounded variable elimination (BVE).
    pub bve_eliminated: u64,
    /// Number of clauses removed by forward subsumption.
    pub subsumed_removed: u64,
    /// Number of literals removed by BIG-based self-subsumption.
    pub self_subsumed: u64,
    /// Total LBD of learned clauses
    pub total_lbd: u64,
    /// Number of clause minimizations
    pub minimizations: u64,
    /// Literals removed by minimization
    pub literals_removed: u64,
    /// Number of chronological backtracks
    pub chrono_backtracks: u64,
    /// Number of non-chronological backtracks
    pub non_chrono_backtracks: u64,
    /// Number of CaDiCaL-style "lucky" pre-solving attempts (see `lucky_phases`).
    pub lucky_tried: u64,
    /// Number of "lucky" attempts that produced a model without search.
    pub lucky_succeeded: u64,
}

impl SolverStats {
    /// Get average LBD of learned clauses
    #[must_use]
    pub fn avg_lbd(&self) -> f64 {
        if self.learned_clauses == 0 {
            0.0
        } else {
            self.total_lbd as f64 / self.learned_clauses as f64
        }
    }

    /// Get average decisions per conflict
    #[must_use]
    pub fn avg_decisions_per_conflict(&self) -> f64 {
        if self.conflicts == 0 {
            0.0
        } else {
            self.decisions as f64 / self.conflicts as f64
        }
    }

    /// Get propagations per conflict
    #[must_use]
    pub fn propagations_per_conflict(&self) -> f64 {
        if self.conflicts == 0 {
            0.0
        } else {
            self.propagations as f64 / self.conflicts as f64
        }
    }

    /// Get clause deletion ratio
    #[must_use]
    pub fn deletion_ratio(&self) -> f64 {
        if self.learned_clauses == 0 {
            0.0
        } else {
            self.deleted_clauses as f64 / self.learned_clauses as f64
        }
    }

    /// Get chronological backtrack ratio
    #[must_use]
    pub fn chrono_backtrack_ratio(&self) -> f64 {
        let total = self.chrono_backtracks + self.non_chrono_backtracks;
        if total == 0 {
            0.0
        } else {
            self.chrono_backtracks as f64 / total as f64
        }
    }

    /// Display formatted statistics
    pub fn display(&self) {
        println!("========== Solver Statistics ==========");
        println!("Decisions:              {:>12}", self.decisions);
        println!("Propagations:           {:>12}", self.propagations);
        println!("Conflicts:              {:>12}", self.conflicts);
        println!("Restarts:               {:>12}", self.restarts);
        println!("Learned clauses:        {:>12}", self.learned_clauses);
        println!("  - Unit clauses:       {:>12}", self.unit_clauses);
        println!("  - Binary clauses:     {:>12}", self.binary_clauses);
        println!("Deleted clauses:        {:>12}", self.deleted_clauses);
        println!("Minimizations:          {:>12}", self.minimizations);
        println!("Literals removed:       {:>12}", self.literals_removed);
        println!("Chrono backtracks:      {:>12}", self.chrono_backtracks);
        println!("Non-chrono backtracks:  {:>12}", self.non_chrono_backtracks);
        println!("---------------------------------------");
        println!("Avg LBD:                {:>12.2}", self.avg_lbd());
        println!(
            "Avg decisions/conflict: {:>12.2}",
            self.avg_decisions_per_conflict()
        );
        println!(
            "Propagations/conflict:  {:>12.2}",
            self.propagations_per_conflict()
        );
        println!(
            "Deletion ratio:         {:>12.2}%",
            self.deletion_ratio() * 100.0
        );
        println!(
            "Chrono backtrack ratio: {:>12.2}%",
            self.chrono_backtrack_ratio() * 100.0
        );
        println!("=======================================");
    }
}

/// CDCL SAT Solver
#[derive(Debug)]
pub struct Solver {
    /// Configuration
    pub(super) config: SolverConfig,
    /// Number of variables
    pub(super) num_vars: usize,
    /// Clause database
    pub(super) clauses: ClauseDatabase,
    /// Assignment trail
    pub(super) trail: Trail,
    /// Watch lists
    pub(super) watches: WatchLists,
    /// VSIDS branching heuristic
    pub(super) vsids: VSIDS,
    /// Prefer these variables before VSIDS (highest priority first). Cleared
    /// when empty; used for finite-domain table-index equalities.
    pub(super) domain_priority: Vec<Var>,
    /// VMTF move-to-front decision queue (cadical focused-mode branching).
    pub(super) vmtf: VMTF,
    /// CHB branching heuristic
    pub(super) chb: CHB,
    /// LRB branching heuristic
    pub(super) lrb: LRB,
    /// Statistics
    pub(super) stats: SolverStats,
    /// Learnt clause for conflict analysis
    pub(super) learnt: SmallVec<[Lit; 16]>,
    /// Seen flags for conflict analysis
    pub(super) seen: Vec<bool>,
    /// Analyze stack
    pub(super) analyze_stack: Vec<Lit>,
    /// Current restart threshold
    pub(super) restart_threshold: u64,
    /// Assertions stack for incremental solving (number of original clauses)
    pub(super) assertion_levels: Vec<usize>,
    /// Set once `push()` is called.  Retracted clauses stay live in the database
    /// after `pop()` (watch lists are cleaned lazily), so the fully-falsified
    /// scan in `trail_falsifies_live_clause` cannot distinguish a genuinely
    /// broken trail from ordinary incremental bookkeeping; the check is disabled
    /// for the rest of this solver's life once incremental mode is entered.
    pub(super) ever_pushed: bool,
    /// Trail sizes at each assertion level (for proper pop backtracking)
    pub(super) assertion_trail_sizes: Vec<usize>,
    /// Clause IDs added at each assertion level (for proper pop)
    pub(super) assertion_clause_ids: Vec<Vec<ClauseId>>,
    /// Model (if sat)
    pub(super) model: Vec<LBool>,
    /// Whether formula is trivially unsatisfiable
    pub(super) trivially_unsat: bool,
    /// Optional per-call propagation step limit for preprocessing passes
    /// (lucky/probing/vivify). When set, `propagate` stops and sets
    /// `propagate_aborted` once the limit is reached, so a single doomed
    /// cascade can't run unbounded (it was a ~7s slowdown on Urquhart). `None`
    /// (the default, used by the real search) means no limit.
    pub(super) propagate_step_limit: Option<u64>,
    /// Set by `propagate` when it bailed early due to `propagate_step_limit`.
    pub(super) propagate_aborted: bool,
    /// Phase saving: last polarity assigned to each variable
    pub(super) phase: Vec<bool>,
    /// Global polarity flip applied on top of saved phases (rephasing). Toggled
    /// periodically on restart so a restart explores the complementary phase
    /// region instead of re-deriving the same trail — without it, frequent
    /// (Glucose) restarts just redo work and inflate the conflict count.
    pub(super) phase_inverted: bool,
    /// Best partial assignment found so far (the phase of the longest trail
    /// reached without conflict). Restored on some rephase rounds to refocus
    /// the search near the best-known region — the one genuinely missing
    /// SAT-side phase signal (cadical's "best" phase array).
    pub(super) best_phase: Vec<bool>,
    /// Length of the trail that produced `best_phase` (0 until a trail is
    /// snappedshotted).
    pub(super) best_trail_size: usize,
    /// Rephase round counter (alternates restore-best vs invert).
    pub(super) rephase_count: u64,
    /// Luby sequence index for restarts
    pub(super) luby_index: u64,
    /// cadical-style stable/focused mode flag. Focused (false) = frequent
    /// restarts (aggressive search); stable (true) = rare restarts + rephase
    /// (deep exploration). Alternated on a growing schedule.
    pub(super) stable: bool,
    /// Stabilization phase counter (drives the quadratic switch-interval
    /// growth).
    pub(super) stabphases: u64,
    /// Conflict count at which to next switch stable/focused mode.
    ///
    /// Legacy: the tick-based schedule (`lim_stabilize`) drives the actual
    /// transitions; retained for inspection but not read by the search.
    #[allow(dead_code)]
    pub(super) next_stabilize: u64,
    /// Per-mode glue averages (current/saved), swapped on stable/focused
    /// transitions (cadical `swap_averages`).
    pub(super) glue_current: GlueAverages,
    pub(super) glue_saved: GlueAverages,
    /// Knuth reluctant-doubling (Luby) restart trigger for stable mode.
    pub(super) reluctant: Reluctant,
    /// Per-mode tick (propagation) accumulators (cadical `stats.ticks.search`).
    pub(super) ticks_focused: u64,
    pub(super) ticks_stable: u64,
    /// cadical `lim.restart`: next conflict count at which to check the
    /// focused-mode Glucose restart condition.
    pub(super) lim_restart: u64,
    /// cadical `lim.stabilize` expressed in ticks of the upcoming mode.
    pub(super) lim_stabilize: u64,
    /// Level marks for LBD computation
    pub(super) level_marks: Vec<u32>,
    /// Current mark counter for LBD computation
    pub(super) lbd_mark: u32,
    /// Learned clause IDs for deletion
    pub(super) learned_clause_ids: Vec<ClauseId>,
    /// Number of conflicts since last clause deletion
    pub(super) conflicts_since_deletion: u64,
    /// PRNG state (xorshift64)
    pub(super) rng_state: u64,
    /// For Glucose-style restarts: average LBD of recent conflicts
    pub(super) recent_lbd_sum: u64,
    /// Number of conflicts contributing to recent_lbd_sum
    pub(super) recent_lbd_count: u64,
    /// Fast EMA of learned-clause LBD (short window) for Glucose restarts.
    /// Restart when this exceeds the slow EMA — clause quality is degrading.
    pub(super) lbd_ema_fast: f64,
    /// Slow EMA of learned-clause LBD (long window) for Glucose restarts.
    pub(super) lbd_ema_slow: f64,
    /// Binary implication graph for fast binary clause propagation
    pub(super) binary_graph: BinaryImplicationGraph,
    /// Global average LBD for local restarts
    pub(super) global_lbd_sum: u64,
    /// Number of conflicts contributing to global LBD
    pub(super) global_lbd_count: u64,
    /// Conflicts since last local restart
    pub(super) conflicts_since_local_restart: u64,
    /// Conflicts since last inprocessing
    pub(super) conflicts_since_inprocessing: u64,
    /// Chronological backtracking helper
    pub(super) chrono_backtrack: ChronoBacktrack,
    /// Clause activity bump increment (for MapleSAT-style clause bumping)
    pub(super) clause_bump_increment: f64,
    /// Memory optimizer with size-class pools for clause allocation
    pub(super) memory_optimizer: MemoryOptimizer,
    /// Model-reconstruction stack for pure literals eliminated during
    /// inprocessing. Pure-literal elimination deletes clauses that are only
    /// satisfiable *if* the pure literal is fixed to its polarity; the search
    /// itself may assign the variable the opposite phase, so each recorded
    /// literal is forced to `true` in the reconstructed model (see
    /// [`Solver::save_model`]). At most one polarity per variable is recorded.
    pub(super) pure_literal_reconstruction: Vec<Lit>,
    /// One-shot latch: once equivalent-literal substitution has rewritten the
    /// clause database we must not run it again (a second pass would operate on
    /// already-substituted clauses and, for incremental callers, on top of
    /// assumptions/blocking clauses expressed in the original variable space).
    pub(super) did_equiv_subst: bool,
    /// Whether `equiv_substitution` has been identity-initialized (one-time;
    /// subsequent substitution rounds compose onto it).
    pub(super) equiv_subst_inited: bool,
    /// One-shot latch for BVE (see `did_equiv_subst`).
    pub(super) did_bve: bool,
    /// Model-reconstruction map for equivalent-literal substitution
    /// (`equiv.rs`): `equiv_substitution[v]` is the representative literal
    /// whose value variable `v` should inherit in the model. For a variable
    /// that was *not* eliminated this is `Lit::pos(v)` (identity). For an
    /// eliminated variable it is a literal of a different variable.
    pub(super) equiv_substitution: Vec<Lit>,
    /// Model-reconstruction data for BVE-eliminated variables. Indexed by
    /// variable; `bve_def[v]` holds the non-`v` literals of every clause that
    /// contained `v` *positively* at elimination time. At model-extension time
    /// `v` is set true iff all of those clauses are falsified by the current
    /// model (else false) — see [`Solver::save_model`].
    pub(super) bve_def: Vec<Vec<SmallVec<[Lit; 4]>>>,
    /// Elimination order of BVE-eliminated variables (reconstruction runs in
    /// reverse, so a variable eliminated later — which may appear in an earlier
    /// variable's recorded clauses — is assigned first).
    pub(super) bve_order: Vec<Var>,
    pub(super) interrupt: Option<Arc<AtomicBool>>,
    /// Optional conflict budget. When `Some(n)`, the search loop returns
    /// [`SolverResult::Unknown`] once `n` conflicts have been reached instead of
    /// running unbounded. `None` (the default) means no conflict limit. This is
    /// the resource budget consulted by the CDCL loop and drives, e.g.,
    /// `oxiz-cli --timeout`-style bounded solving.
    pub(super) max_conflicts: Option<u64>,
    /// Proof dispatcher (`class Proof`). When `Some`, every proof event the
    /// CDCL loop / inprocessing emits (learned/original/deleted clause, empty
    /// clause, in-place strengthen/flush) is fanned out to the attached
    /// tracers ([`crate::proof::DratTracer`] and/or [`crate::proof::LratTracer`]).
    /// `None` (the default) means no proof is produced and every proof hook is a
    /// no-op, so proof logging costs nothing when unused.
    pub(super) proof: Option<crate::proof::Proof>,
    /// `true` once an LRAT tracer (or any antecedent-requiring tracer) is
    /// connected. Drives clause-id bookkeeping (`clause_lrat_id`,
    /// `unit_clauses_idx`) and RUP-chain assembly in conflict analysis. DRAT-only
    /// proofs leave this `false` — DRAT needs neither ids nor chains.
    pub(super) lrat: bool,
    /// Monotonic clause-id counter (`clause_id` in upstream). Original clauses
    /// draw ids `1..K` in file order; derived clauses draw the rest. Maintained
    /// only while a proof is active.
    pub(super) clause_id: i64,
    /// Per-stored-clause LRAT id, indexed by `ClauseId.index()` (`c->id` in
    /// upstream). `0` = unassigned/none. Grown only while `lrat` is on.
    pub(super) clause_lrat_id: Vec<i64>,
    /// Per-literal unit-clause id table (`unit_clauses_idx` in upstream),
    /// indexed by `Lit::index()` (`2·var + sign`). Holds the LRAT id of the
    /// (original or derived) unit clause fixing that literal true. Grown only
    /// while `lrat` is on.
    pub(super) unit_clauses_idx: Vec<i64>,
    /// LRAT RUP-chain scratch (`lrat_chain` in upstream): reason-clause ids
    /// collected during 1-UIP analysis, in trail-walk order, reversed at the
    /// end. Always present (empty when no proof).
    pub(super) lrat_chain: Vec<i64>,
    /// Unit-clause id chain collected during analysis (`unit_chain`):
    /// level-0 literals resolved out of reason clauses. Appended to
    /// `lrat_chain` before the final reversal.
    pub(super) unit_chain: Vec<i64>,
    /// Minimization chain scratch (`mini_chain` / `minimize_chain`): per
    /// Minimization chain scratch (`mini_chain` / `minimize_chain`): per
    /// minimized-away literal's reason sub-chain.
    pub(super) mini_chain: Vec<i64>,
    /// Level-0 literals marked `seen` during analysis, for cleanup
    /// (`unit_analyzed` in upstream).
    pub(super) unit_analyzed: Vec<i32>,
    /// Packed per-literal minimization flags (`Flags` in upstream), indexed by
    /// `Lit::index()`. Bit layout: [`MF_KEEP`]|[`MF_POISON`]|[`MF_REMOVABLE`]|
    /// [`MF_ADDED`]|[`MF_SEEN`]. Grown only while `lrat` is on.
    pub(super) lrat_flags: Vec<u8>,
    /// Literals marked during minimization, for flag cleanup (`minimized`).
    #[allow(dead_code)]
    pub(super) lrat_minimized: Vec<i32>,
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
        let chrono_enabled = config.enable_chronological_backtrack;
        let chrono_threshold = config.chrono_backtrack_threshold;
        let stabilize_base = config.stabilize_base;

        Self {
            restart_threshold: config.restart_interval,
            config,
            num_vars: 0,
            clauses: ClauseDatabase::new(),
            trail: Trail::new(0),
            watches: WatchLists::new(0),
            vsids: VSIDS::new(0),
            domain_priority: Vec::new(),
            vmtf: VMTF::new(0),
            chb: CHB::new(0),
            lrb: LRB::new(0),
            stats: SolverStats::default(),
            learnt: SmallVec::new(),
            seen: Vec::new(),
            analyze_stack: Vec::new(),
            assertion_levels: vec![0],
            ever_pushed: false,
            assertion_trail_sizes: vec![0],
            assertion_clause_ids: vec![Vec::new()],
            model: Vec::new(),
            trivially_unsat: false,
            propagate_step_limit: None,
            propagate_aborted: false,
            phase: Vec::new(),
            phase_inverted: false,
            best_phase: Vec::new(),
            best_trail_size: 0,
            rephase_count: 0,
            luby_index: 0,
            stable: false,
            stabphases: 0,
            next_stabilize: stabilize_base,
            glue_current: GlueAverages::new(),
            glue_saved: GlueAverages::new(),
            reluctant: Reluctant::default(),
            ticks_focused: 0,
            ticks_stable: 0,
            lim_restart: 0,
            lim_stabilize: 0,
            level_marks: Vec::new(),
            lbd_mark: 0,
            learned_clause_ids: Vec::new(),
            conflicts_since_deletion: 0,
            rng_state: 0x853c_49e6_748f_ea9b, // Random seed
            recent_lbd_sum: 0,
            recent_lbd_count: 0,
            lbd_ema_fast: 0.0,
            lbd_ema_slow: 0.0,
            binary_graph: BinaryImplicationGraph::new(0),
            global_lbd_sum: 0,
            global_lbd_count: 0,
            conflicts_since_local_restart: 0,
            conflicts_since_inprocessing: 0,
            chrono_backtrack: ChronoBacktrack::new(chrono_enabled, chrono_threshold),
            clause_bump_increment: 1.0,
            memory_optimizer: MemoryOptimizer::new(),
            pure_literal_reconstruction: Vec::new(),
            equiv_substitution: Vec::new(),
            bve_def: Vec::new(),
            bve_order: Vec::new(),
            did_bve: false,
            did_equiv_subst: false,
            equiv_subst_inited: false,
            interrupt: None,
            max_conflicts: None,
            proof: None,
            lrat: false,
            clause_id: 0,
            clause_lrat_id: Vec::new(),
            unit_clauses_idx: Vec::new(),
            lrat_chain: Vec::new(),
            unit_chain: Vec::new(),
            mini_chain: Vec::new(),
            unit_analyzed: Vec::new(),
            lrat_flags: Vec::new(),
            lrat_minimized: Vec::new(),
        }
    }

    /// Enable DRAT proof logging to `path`.
    ///
    /// While enabled, the CDCL search emits a DRAT proof: one addition line per
    /// learned clause, one deletion line per clause removed by database
    /// reduction / subsumption / vivification / incremental forgetting, and the
    /// empty clause when unconditional UNSAT is derived. The resulting file can
    /// be checked by any DRAT proof checker. Enabling it does not change the
    /// search itself — only whether the trace is recorded.
    pub fn enable_drat_proof(&mut self, path: impl AsRef<std::path::Path>) -> std::io::Result<()> {
        self.connect_drat(path, false)
    }

    /// Disable all proof logging, flushing and closing every attached tracer.
    pub fn disable_proof(&mut self) {
        if let Some(mut proof) = self.proof.take() {
            proof.flush(false);
            proof.close(false);
        }
        self.lrat = false;
    }

    /// Back-compat alias for [`Solver::disable_proof`].
    pub fn disable_drat_proof(&mut self) {
        self.disable_proof();
    }

    /// Returns `true` when any proof logging is currently enabled.
    #[must_use]
    pub fn proof_enabled(&self) -> bool {
        self.proof.is_some()
    }

    /// Returns `true` when DRAT/LRAT proof logging is currently enabled
    /// (back-compat name).
    #[must_use]
    pub fn drat_proof_enabled(&self) -> bool {
        self.proof.is_some()
    }

    /// Returns `true` when LRAT (antecedent) proof logging is enabled.
    #[must_use]
    pub fn lrat_proof_enabled(&self) -> bool {
        self.lrat
    }

    // -- proof connection helpers -------------------------------------

    fn proof_ensure(&mut self) -> &mut crate::proof::Proof {
        self.proof.get_or_insert_with(crate::proof::Proof::new)
    }

    fn connect_drat(
        &mut self,
        path: impl AsRef<std::path::Path>,
        binary: bool,
    ) -> std::io::Result<()> {
        let s = path_to_str(path.as_ref())?;
        let tracer = if binary {
            crate::proof::DratTracer::open_binary(s)?
        } else {
            crate::proof::DratTracer::open(s)?
        };
        let clause_id = self.clause_id;
        let proof = self.proof_ensure();
        proof.begin_proof(clause_id);
        proof.connect(Box::new(tracer));
        Ok(())
    }

    /// Enable **binary** DRAT proof logging to `path`.
    pub fn enable_drat_proof_binary(
        &mut self,
        path: impl AsRef<std::path::Path>,
    ) -> std::io::Result<()> {
        self.connect_drat(path, true)
    }

    fn connect_lrat(
        &mut self,
        path: impl AsRef<std::path::Path>,
        binary: bool,
    ) -> std::io::Result<()> {
        let s = path_to_str(path.as_ref())?;
        let tracer = if binary {
            crate::proof::LratTracer::open_binary(s)?
        } else {
            crate::proof::LratTracer::open(s)?
        };
        // LRAT needs clause ids + RUP chains: switch on the bookkeeping.
        self.lrat = true;
        self.unit_clauses_idx.resize(2 * self.num_vars, 0);
        self.lrat_flags.resize(2 * self.num_vars, 0);
        let clause_id = self.clause_id;
        let proof = self.proof_ensure();
        proof.begin_proof(clause_id);
        proof.connect(Box::new(tracer));
        Ok(())
    }

    /// Enable **text** LRAT proof logging to `path`.
    pub fn enable_lrat_proof(&mut self, path: impl AsRef<std::path::Path>) -> std::io::Result<()> {
        self.connect_lrat(path, false)
    }

    /// Enable **binary** LRAT proof logging to `path`.
    pub fn enable_lrat_proof_binary(
        &mut self,
        path: impl AsRef<std::path::Path>,
    ) -> std::io::Result<()> {
        self.connect_lrat(path, true)
    }

    /// Flush all attached file tracers to disk.
    pub fn flush_proof(&mut self) {
        if let Some(proof) = &mut self.proof {
            proof.flush(false);
        }
    }

    // -- clause-id bookkeeping ---------------------------------------

    /// Allocate the next monotonic clause id (`++clause_id`). Returns 0 when no
    /// proof is active (ids are meaningless without a tracer).
    fn proof_next_id(&mut self) -> i64 {
        if self.proof.is_some() {
            self.clause_id += 1;
            self.clause_id
        } else {
            0
        }
    }

    /// Record that stored clause `cid` carries LRAT id `id` (`c->id = id`).
    fn proof_set_clause_id(&mut self, cid: ClauseId, id: i64) {
        if !self.lrat {
            return;
        }
        let idx = cid.index();
        if idx >= self.clause_lrat_id.len() {
            self.clause_lrat_id.resize(idx + 1, 0);
        }
        self.clause_lrat_id[idx] = id;
    }

    /// Look up the LRAT id of stored clause `cid` (0 if unassigned/unknown).
    fn proof_clause_id(&self, cid: ClauseId) -> i64 {
        let idx = cid.index();
        if idx < self.clause_lrat_id.len() {
            self.clause_lrat_id[idx]
        } else {
            0
        }
    }

    /// Record the unit clause fixing `lit_dimacs` (a *true* DIMACS literal) as
    /// LRAT id `id` (`unit_clauses_idx[vlit(lit)] = id`).
    fn proof_set_unit_id(&mut self, lit_dimacs: i32, id: i64) {
        if !self.lrat {
            return;
        }
        let lit = Lit::from_dimacs(lit_dimacs);
        let li = lit.index();
        if li >= self.unit_clauses_idx.len() {
            let need = 2 * self.num_vars.max(lit.var().index() + 1);
            self.unit_clauses_idx.resize(need, 0);
        }
        self.unit_clauses_idx[li] = id;
    }

    /// Look up the LRAT id of the unit clause fixing *true* literal `lit_dimacs`
    /// (`unit_id(lit)` in upstream).
    fn proof_unit_id(&self, lit_dimacs: i32) -> i64 {
        debug_assert!(self.lrat);
        self.proof_unit_id_get_or_zero(lit_dimacs)
    }

    fn proof_unit_id_get_or_zero(&self, lit_dimacs: i32) -> i64 {
        if !self.lrat {
            return 0;
        }
        let lit = Lit::from_dimacs(lit_dimacs);
        let li = lit.index();
        if li < self.unit_clauses_idx.len() {
            self.unit_clauses_idx[li]
        } else {
            0
        }
    }

    /// Flush a level-0 propagation to an explicit derived unit (the principled
    /// fix that makes every level-0 literal a unit with an LRAT id, matching
    /// cadical's invariant). Called right after a literal is propagated at
    /// decision level 0: emits a derived unit `[lit]` whose RUP chain is the
    /// antecedent unit ids (already flushed — propagation is in trail order)
    /// followed by the propagating clause's id, and records the new unit id.
    ///
    /// This lets conflict analysis, the empty-clause walk, and minimization
    /// reference any level-0 literal by a single unit id instead of re-walking
    /// its reason sub-graph.
    pub(super) fn flush_level0_unit(&mut self, lit: Lit, cid: ClauseId) {
        if !self.lrat || self.proof.is_none() {
            return;
        }
        let lit_dimacs = lit.to_dimacs();
        if self.proof_unit_id_get_or_zero(lit_dimacs) != 0 {
            return; // already a recorded unit (original/learned unit or already flushed)
        }
        // Chain: [unit id of each antecedent's true form] ++ [propagating clause id].
        // Under ¬lit the antecedent units make the reason clause's antecedent
        // literals false, so the reason clause is fully falsified → conflict.
        let reason_lits: SmallVec<[Lit; 8]> = self
            .clauses
            .get(cid)
            .map(|c| c.lits.iter().copied().collect())
            .unwrap_or_default();
        let mut chain: SmallVec<[i64; 8]> = SmallVec::new();
        for &l in &reason_lits {
            if l.var() == lit.var() {
                continue; // the propagated literal
            }
            let v = l.var();
            let true_dimacs = if self.trail.lit_value(Lit::pos(v)).is_true() {
                Lit::pos(v).to_dimacs()
            } else {
                Lit::neg(v).to_dimacs()
            };
            chain.push(self.proof_unit_id(true_dimacs));
        }
        chain.push(self.proof_clause_id(cid));
        let id = self.proof_next_id();
        self.proof_set_unit_id(lit_dimacs, id);
        if let Some(proof) = &mut self.proof {
            proof.add_derived_unit_clause(id, lit_dimacs, &chain);
        }
    }

    // -- higher-level proof events used by learn.rs / inprocessing ----

    /// Emit a derived clause for a *theory* lemma / explanation clause
    /// (`add_derived_clause` with an empty RUP chain). Pure-SAT runs never hit
    /// this; CDCL(T) LRAT would need the theory layer to supply a real chain.
    fn proof_theory_clause(&mut self, dimacs: &[i32]) -> i64 {
        if self.proof.is_none() {
            return 0;
        }
        let id = self.proof_next_id();
        if let Some(proof) = &mut self.proof {
            proof.add_derived_clause(id, false, dimacs, &[]);
        }
        id
    }

    /// Emit a derived *unit* theory lemma and record its unit id.
    fn proof_theory_unit(&mut self, unit_dimacs: i32) -> i64 {
        if self.proof.is_none() {
            return 0;
        }
        let id = self.proof_next_id();
        self.proof_set_unit_id(unit_dimacs, id);
        if let Some(proof) = &mut self.proof {
            proof.add_derived_unit_clause(id, unit_dimacs, &[]);
        }
        id
    }

    /// Emit a *learned* clause's derived-clause proof event: unit clauses go
    /// through the unit variant and get a unit-id table entry; multi-literal
    /// clauses go through the plain variant. The RUP chain is taken from
    /// [`Solver::lrat_chain`] (assembled by `analyze`/`minimize`). Returns the
    /// allocated id (0 if inactive) so the caller can bind it to the stored
    /// clause via [`Solver::proof_set_clause_id`].
    pub(super) fn proof_learn_clause(&mut self, lits: &[Lit]) -> i64 {
        if self.proof.is_none() {
            return 0;
        }
        let id = self.proof_next_id();
        let chain = if self.lrat {
            let c = std::mem::take(&mut self.lrat_chain);
            // A 0 hint id means a clause/unit id was never bound — the proof
            // would be un-checkable. Catch it early in debug builds.
            debug_assert!(
                !c.contains(&0),
                "zero-id hint in derived clause {} (lits={:?})",
                id,
                lits.iter().map(|l| l.to_dimacs()).collect::<Vec<_>>()
            );
            c
        } else {
            Vec::new()
        };
        if lits.len() == 1 {
            let unit = lits[0].to_dimacs();
            self.proof_set_unit_id(unit, id);
            if let Some(proof) = &mut self.proof {
                proof.add_derived_unit_clause(id, unit, &chain);
            }
        } else {
            let dimacs: SmallVec<[i32; 16]> = lits.iter().map(|l| l.to_dimacs()).collect();
            if let Some(proof) = &mut self.proof {
                proof.add_derived_clause(id, false, &dimacs, &chain);
            }
        }
        id
    }

    /// Emit a clause *strengthen* (in-place shortening) as a proof event: add a
    /// fresh derived clause with the kept literals, then delete the old clause,
    /// finally rebind the stored clause's LRAT id to the new one
    /// (`c->id = new_id` in upstream's `strengthen_clause`). The RUP chain is
    /// empty — used by vivification, which proves the shorter clause is
    /// RUP-derivable but does not currently expose its antecedents.
    fn proof_strengthen_clause(&mut self, cid: ClauseId, kept: &[Lit]) {
        if self.proof.is_none() {
            return;
        }
        let old_id = self.proof_clause_id(cid);
        let kept_dimacs: SmallVec<[i32; 8]> = kept.iter().map(|l| l.to_dimacs()).collect();
        let old_dimacs: SmallVec<[i32; 8]> = self
            .clauses
            .get(cid)
            .map(|c| c.lits.iter().map(|l| l.to_dimacs()).collect())
            .unwrap_or_default();
        let new_id = self.proof_next_id();
        if let Some(proof) = &mut self.proof {
            proof.strengthen_clause(new_id, false, &kept_dimacs, &[]);
            proof.delete_clause(old_id, false, &old_dimacs);
        }
        self.proof_set_clause_id(cid, new_id);
    }

    /// Emit a clause deletion by stored-clause id, reading its literals before
    /// the clause is detached (no-op when proof logging is off or the clause is
    /// already gone). For LRAT the deletion is keyed by the clause's LRAT id;
    /// for DRAT it is keyed by the literal set.
    pub(super) fn drat_delete(&mut self, clause_id: ClauseId) {
        if self.proof.is_none() {
            return;
        }
        let lits: Option<SmallVec<[Lit; 8]>> = self
            .clauses
            .get(clause_id)
            .filter(|c| !c.deleted)
            .map(|c| c.lits.iter().copied().collect());
        let Some(lits) = lits else { return };
        let dimacs: SmallVec<[i32; 8]> = lits.iter().map(|l| l.to_dimacs()).collect();
        let id = self.proof_clause_id(clause_id);
        if let Some(proof) = &mut self.proof {
            proof.delete_clause(id, false, &dimacs);
        }
    }

    /// Emit a clause deletion by an explicit literal set (used when a clause is
    /// strengthened in place and its pre-strengthening form must be retired).
    pub(super) fn drat_delete_lits(&mut self, lits: &[Lit]) {
        if self.proof.is_none() {
            return;
        }
        let dimacs: SmallVec<[i32; 8]> = lits.iter().map(|l| l.to_dimacs()).collect();
        // Best-effort id: a unit's id is recoverable from the unit table.
        let id = if lits.len() == 1 {
            self.proof_unit_id_get_or_zero(lits[0].to_dimacs())
        } else {
            0
        };
        if let Some(proof) = &mut self.proof {
            proof.delete_clause(id, false, &dimacs);
        }
    }

    /// Emit the empty clause (unconditional UNSAT). For LRAT this first builds
    /// the empty clause's RUP chain from the current conflict.
    pub(super) fn drat_emit_empty(&mut self, conflict: Option<ClauseId>) {
        if self.proof.is_none() {
            return;
        }
        if self.lrat {
            self.build_chain_for_empty(conflict);
        }
        let id = self.proof_next_id();
        let chain = if self.lrat {
            std::mem::take(&mut self.lrat_chain)
        } else {
            Vec::new()
        };
        if let Some(proof) = &mut self.proof {
            proof.add_derived_empty_clause(id, &chain);
        }
        self.lrat_chain.clear();
    }

    /// Purge every binary-implication-graph edge belonging to `clause_id`.
    ///
    /// The binary graph is a direct-index fast path over binary clauses; unlike
    /// the watch lists (which lazily skip deleted clauses) it is consulted
    /// without a liveness check at its call sites' hot loop, so a retracted
    /// binary clause must have its edges physically removed. Reads the clause's
    /// literals, so it must run *before* the clause is removed from the database.
    pub(super) fn purge_binary_edges(&mut self, clause_id: ClauseId) {
        let binary_lits = self.clauses.get(clause_id).and_then(|c| {
            if c.lits.len() == 2 && !c.deleted {
                Some((c.lits[0], c.lits[1]))
            } else {
                None
            }
        });
        if let Some((a, b)) = binary_lits {
            self.binary_graph.remove_clause_edges(a.negate(), clause_id);
            self.binary_graph.remove_clause_edges(b.negate(), clause_id);
        }
    }

    /// Attach a cooperative interrupt flag.
    ///
    /// While solving, the CDCL loop periodically checks this flag; if another
    /// thread sets it to `true`, the current `solve*` call abandons the search
    /// and returns [`SolverResult::Unknown`]. Combined with
    /// [`Solver::set_max_conflicts`], this lets callers bound solving by both
    /// wall-clock time (via an external timer that sets the flag) and work.
    pub fn set_interrupt(&mut self, flag: Arc<AtomicBool>) {
        self.interrupt = Some(flag);
    }

    /// Set the conflict budget (`None` clears it). When set, the CDCL search
    /// loop returns [`SolverResult::Unknown`] once the budget is reached.
    pub fn set_max_conflicts(&mut self, max_conflicts: Option<u64>) {
        self.max_conflicts = max_conflicts;
    }

    /// Set the preferred (default) decision phase for a variable.
    ///
    /// Used by theory-combination axiomatization (the z3-style "triangle"
    /// axioms `(t1=t2) ⟺ (t1≤t2 ∧ t1≥t2)`): biasing the equality atom toward
    /// `true` (`try_true_first`) makes CDCL prefer merging shared terms, so the
    /// arithmetic solver's consistency check (`check`) — not fragile reason
    /// extraction — drives theory combination.
    /// Theory-aware decision hint: bump the activity of these variables so
    /// the branching heuristic prefers deciding them early.  Mirrors the
    /// per-conflict bump in conflict.rs so it works under every strategy.
    pub fn bump_decision_hint(&mut self, vars: &[Var]) {
        if vars.is_empty() { return; }
        self.vsids.bump_batch(vars);
        if self.config.use_chb_branching { self.chb.bump_batch(vars); }
        if self.config.use_vmtf {
            for &v in vars { self.vmtf.bump(v, |v| self.trail.is_assigned(v)); }
        }
    }

    pub fn set_preferred_phase(&mut self, var: Var, phase: bool) {
        let idx = var.index();
        if idx < self.phase.len() {
            self.phase[idx] = phase;
        }
        if idx < self.best_phase.len() {
            self.best_phase[idx] = phase;
        }
    }

    /// Raise VSIDS activity so `var` is decided early.
    ///
    /// Used after finite-domain case-splits on table indices: once those
    /// equalities are fixed, lookup tables unit-propagate and the remaining
    /// arithmetic is nearly determined.
    pub fn bump_var_activity(&mut self, var: Var, times: u32) {
        if !self.vsids.contains(var) {
            self.vsids.insert(var);
        }
        for _ in 0..times {
            self.vsids.bump(var);
        }
    }

    /// Install (or replace) an external branching heuristic.
    pub fn set_external_branching(&mut self, h: crate::solver::BoxedBranchingHeuristic) {
        self.config.external_branching = Some(h);
    }

    /// Variables to decide before VSIDS (highest priority first).
    ///
    /// Finite-domain table-index equalities: O(|priority|) per decision instead
    /// of scanning all unassigned vars via external branching.
    pub fn set_domain_priority(&mut self, vars: Vec<Var>) {
        self.domain_priority = vars;
    }

    /// Returns `true` when the search must stop early: the conflict budget has
    /// been reached or an external interrupt flag has been raised.
    #[inline]
    pub(super) fn should_stop_search(&self) -> bool {
        if let Some(max) = self.max_conflicts
            && self.stats.conflicts >= max
        {
            return true;
        }
        if let Some(flag) = &self.interrupt
            && flag.load(Ordering::Relaxed)
        {
            return true;
        }
        false
    }

    /// Create a new variable
    pub fn new_var(&mut self) -> Var {
        let var = Var::new(self.num_vars as u32);
        self.num_vars += 1;
        self.trail.resize(self.num_vars);
        self.watches.resize(self.num_vars);
        self.binary_graph.resize(self.num_vars);
        self.vsids.insert(var);
        self.chb.insert(var);
        self.vmtf.resize(self.num_vars);
        self.lrb.resize(self.num_vars);
        self.seen.resize(self.num_vars, false);
        self.model.resize(self.num_vars, LBool::Undef);
        self.phase.resize(self.num_vars, false); // Default phase: negative
        self.best_phase.resize(self.num_vars, false);
        // Resize level_marks to at least num_vars (enough for decision levels)
        if self.level_marks.len() < self.num_vars {
            self.level_marks.resize(self.num_vars, 0);
        }
        // Grow the LRAT per-literal tables to cover the new variable. These
        // are only non-empty while an LRAT tracer is connected.
        if self.lrat {
            self.unit_clauses_idx.resize(2 * self.num_vars, 0);
            self.lrat_flags.resize(2 * self.num_vars, 0);
        }
        var
    }

    /// Export the current SAT problem (every live clause plus every level-0
    /// trail literal as a unit clause) in DIMACS int-literal encoding
    /// (1-based, sign = polarity), together with the variable count. Used to
    /// hand the problem to an external SAT backend.
    pub fn export_problem_dimacs(&self) -> (usize, Vec<Vec<i32>>) {
        let mut clauses: Vec<Vec<i32>> = Vec::new();
        // Level-0 trail literals are the unconditional assertions; an external
        // solver needs them as unit clauses.
        for lit in self.trail.assignments() {
            if self.trail.level(lit.var()) == 0 {
                clauses.push(vec![lit.to_dimacs()]);
            }
        }
        for id in self.clauses.iter_ids() {
            let Some(c) = self.clauses.get(id) else {
                continue;
            };
            if c.deleted {
                continue;
            }
            clauses.push(c.lits.iter().map(|l| l.to_dimacs()).collect());
        }
        (self.num_vars, clauses)
    }

    /// Ensure we have at least n variables
    pub fn ensure_vars(&mut self, n: usize) {
        while self.num_vars < n {
            self.new_var();
        }
    }

    /// Scan `clause_lits` against the *current* trail: is any literal true,
    /// what is the highest level among the false literals (0 if there are
    /// none), and which literals are still undefined.
    ///
    /// Read-only. Used by [`Solver::pre_check_effective_unit`] both before
    /// and (when it backtracks) after a `backtrack_to_root()` call, so it
    /// must not itself assume anything about levels.
    fn scan_clause_for_attach(&self, clause_lits: &[Lit]) -> (bool, u32, SmallVec<[Lit; 4]>) {
        let mut has_true = false;
        let mut max_false_level = 0u32;
        let mut undefined: SmallVec<[Lit; 4]> = SmallVec::new();
        for &lit in clause_lits {
            let value = self.trail.lit_value(lit);
            if value.is_true() {
                has_true = true;
                break;
            } else if value.is_false() {
                max_false_level = max_false_level.max(self.trail.level(lit.var()));
            } else {
                undefined.push(lit);
            }
        }
        (has_true, max_false_level, undefined)
    }

    /// Resolve `clause_lits`'s conflict / effective-unit status against the
    /// current trail, performing any necessary backtrack, *before* the
    /// caller chooses which literals to watch.
    ///
    /// # Why this must run before watch selection
    ///
    /// The two-watched-literal ranking (`watch_rank` and its call sites in
    /// `add_clause`) is computed against whatever the trail looks like when
    /// it runs. A `backtrack_to_root()` performed *after* that ranking would
    /// silently invalidate it: literals the ranking saw as false may now be
    /// undefined, so the "watch the two latest-falsified literals" choice it
    /// made is no longer meaningful. Running this check first, and letting
    /// its backtrack (if any) land before ranking ever executes, keeps the
    /// two steps consistent with each other.
    ///
    /// # Why "effectively unit" needs the same treatment as "all false"
    ///
    /// A clause is only safe to attach as-is when every literal that is
    /// currently false is false *permanently* (at level 0). A literal false
    /// above level 0 can be unassigned by a future backtrack while some
    /// *other* disjunct of the clause survives (in particular, an implied
    /// literal this same function forces at the wrong level would -- see the
    /// history of this function for the bug that motivated this rewrite):
    /// the clause is then silently reopened, with no live watcher able to
    /// notice, because watch/graph registration only fires on a literal's
    /// *next* transition, not because of anything a backtrack does. This is
    /// true whether the clause is fully false (a conflict) or has exactly
    /// one literal left undefined (an effective unit) -- both are handled by
    /// the same rule here.
    ///
    /// `backtrack_to_root()` resolves the ambiguity outright: every literal
    /// false above level 0 becomes undefined, so a mandatory re-scan
    /// afterward finds either 2+ undefined literals (ordinary watching is
    /// then correct and sufficient -- the clause is genuinely open again) or
    /// still at most one undefined literal, with every remaining false
    /// literal now unconditionally at level 0 (forced at level 0, which
    /// survives every future backtrack by construction).
    fn pre_check_effective_unit(&mut self, clause_lits: &[Lit]) -> PreAttachOutcome {
        let (has_true, max_false_level, undefined) = self.scan_clause_for_attach(clause_lits);
        if has_true || undefined.len() >= 2 {
            return PreAttachOutcome::Ordinary;
        }

        if max_false_level > 0 {
            self.backtrack_to_root();
            // Mandatory re-scan: the sets computed above are now stale.
            let (has_true, _post_backtrack_max_level, undefined) =
                self.scan_clause_for_attach(clause_lits);
            debug_assert!(
                !has_true,
                "backtrack_to_root() cannot turn a false/undefined literal true"
            );
            return if undefined.is_empty() {
                PreAttachOutcome::UnconditionalConflict
            } else if undefined.len() == 1 {
                PreAttachOutcome::ForceUnitAtLevelZero(undefined[0])
            } else {
                PreAttachOutcome::Ordinary
            };
        }

        if undefined.is_empty() {
            PreAttachOutcome::UnconditionalConflict
        } else {
            // Force the unit *physically* at level 0: main's simple-pop trail
            // removes by position, so appending this permanent fact at a higher
            // level would let the next backtrack pop it. max_false_level == 0
            // here, so no clause literal sits above level 0 and `undefined` is
            // unchanged by the backtrack.
            if self.trail.decision_level() > 0 {
                self.backtrack_to_root();
            }
            PreAttachOutcome::ForceUnitAtLevelZero(undefined[0])
        }
    }

    /// Add a clause
    pub fn add_clause(&mut self, lits: impl IntoIterator<Item = Lit>) -> bool {
        let mut clause_lits: SmallVec<[Lit; 8]> = lits.into_iter().collect();

        // Ensure we have all variables
        for lit in &clause_lits {
            let var_idx = lit.var().index();
            if var_idx >= self.num_vars {
                self.ensure_vars(var_idx + 1);
            }
        }

        // Assign this original clause a monotonic LRAT id *before* any
        // early-return (tautology / unit / empty), so every input clause draws
        // exactly one id in file order — matching `lrat-check`'s CNF numbering
        // (`1..K`). `0` when no proof is active. The id is bound to a stored
        // clause / unit entry below; tautologies consume it but bind nothing.
        let proof_oid = if self.proof.is_some() {
            let id = self.proof_next_id();
            let dimacs: SmallVec<[i32; 8]> = clause_lits.iter().map(|l| l.to_dimacs()).collect();
            if let Some(proof) = &mut self.proof {
                proof.add_original_clause(id, false, &dimacs);
            }
            id
        } else {
            0
        };

        // Remove duplicates and check for tautology
        clause_lits.sort_by_key(|l| l.code());
        clause_lits.dedup();

        // Check for tautology (x and ~x in same clause)
        for i in 0..clause_lits.len() {
            for j in (i + 1)..clause_lits.len() {
                if clause_lits[i] == clause_lits[j].negate() {
                    return true; // Tautology - always satisfied
                }
            }
        }

        // Handle special cases
        match clause_lits.len() {
            0 => {
                self.trivially_unsat = true;
                return false; // Empty clause - unsat
            }
            1 => {
                // Unit clause - enqueue at decision level 0
                // Unit clauses must be assigned at level 0 to survive backtracking.
                // After solve(), current_level may be > 0, so we must backtrack first.
                let lit = clause_lits[0];
                // Record the unit clause's LRAT id against its true literal so it
                // can be referenced as an antecedent in RUP chains (`assign_original_unit`).
                self.proof_set_unit_id(lit.to_dimacs(), proof_oid);

                if self.trail.lit_value(lit).is_false() {
                    // The literal conflicts with the current trail.
                    // Check if the conflict is at decision level 0 (permanent constraint)
                    // or from a previous solve (can be retried after backtrack).
                    let var = lit.var();
                    let level = self.trail.level(var);
                    if level == 0 {
                        // Conflict with a level-0 assignment - truly UNSAT
                        self.trivially_unsat = true;
                        return false;
                    } else {
                        // Conflict with higher-level assignment from previous solve.
                        // Backtrack to root and assign the new unit literal at level 0.
                        self.backtrack_to_root();
                        self.trail.assign_decision(lit);
                        return true;
                    }
                }

                if self.trail.lit_value(lit).is_true() {
                    // Already satisfied - check if at level 0
                    let var = lit.var();
                    let level = self.trail.level(var);
                    if level == 0 {
                        // Already assigned at level 0, nothing to do
                        return true;
                    }
                    // Assigned at higher level - backtrack and reassign at level 0
                    self.backtrack_to_root();
                    self.trail.assign_decision(lit);
                    return true;
                }

                // Variable is unassigned - backtrack to level 0 first to ensure
                // the assignment is at level 0 (survives future backtracks)
                if self.trail.decision_level() > 0 {
                    self.backtrack_to_root();
                }
                self.trail.assign_decision(lit);
                return true;
            }
            2 => {
                // Binary clause - check if it conflicts with current assignment
                let lit0 = clause_lits[0];
                let lit1 = clause_lits[1];
                let val0 = self.trail.lit_value(lit0);
                let val1 = self.trail.lit_value(lit1);

                // If clause is satisfied, just add it
                if val0.is_true() || val1.is_true() {
                    // Clause already satisfied by current assignment
                    let clause_id = self.clauses.add_original(clause_lits.iter().copied());
                    self.proof_set_clause_id(clause_id, proof_oid);
                    if let Some(current_level_clauses) = self.assertion_clause_ids.last_mut() {
                        current_level_clauses.push(clause_id);
                    }
                    self.binary_graph.add(lit0.negate(), lit1, clause_id);
                    self.binary_graph.add(lit1.negate(), lit0, clause_id);
                    self.watches
                        .add(lit0.negate(), Watcher::new(clause_id, lit1));
                    self.watches
                        .add(lit1.negate(), Watcher::new(clause_id, lit0));
                    return true;
                }

                // Resolve conflict / effective-unit status *before*
                // attaching the clause -- see `pre_check_effective_unit`'s
                // doc comment for the full reasoning (in particular why an
                // "effectively unit" binary clause, not just an "all false"
                // one, needs its level bookkeeping resolved this way: the
                // watches registered below cannot be trusted to discover it
                // on their own, since they only fire on a literal's *next*
                // transition -- a level-0 fact from earlier in this
                // incremental session was already dequeued long ago and will
                // never be dequeued again).
                let outcome = self.pre_check_effective_unit(&clause_lits);
                if matches!(outcome, PreAttachOutcome::UnconditionalConflict) {
                    self.trivially_unsat = true;
                    return false;
                }

                let clause_id = self.clauses.add_original(clause_lits.iter().copied());
                self.proof_set_clause_id(clause_id, proof_oid);
                if let Some(current_level_clauses) = self.assertion_clause_ids.last_mut() {
                    current_level_clauses.push(clause_id);
                }
                self.binary_graph.add(lit0.negate(), lit1, clause_id);
                self.binary_graph.add(lit1.negate(), lit0, clause_id);
                self.watches
                    .add(lit0.negate(), Watcher::new(clause_id, lit1));
                self.watches
                    .add(lit1.negate(), Watcher::new(clause_id, lit0));

                if let PreAttachOutcome::ForceUnitAtLevelZero(forced) = outcome {
                    self.trail.assign_propagation_at(forced, clause_id, 0);
                }
                return true;
            }
            _ => {}
        }

        // Add clause (3+ literals)
        // Resolve conflict / effective-unit status *before* choosing watches
        // -- see `pre_check_effective_unit`'s doc comment. Must run before
        // the `watch_rank` selection below: a `backtrack_to_root()` decided
        // on afterward would silently invalidate whatever ranking that
        // selection just computed.
        let outcome = self.pre_check_effective_unit(&clause_lits);
        if matches!(outcome, PreAttachOutcome::UnconditionalConflict) {
            self.trivially_unsat = true;
            return false;
        }

        // Choose the two watch literals *before* storing the clause, following
        // MiniSat's attachClause invariant: watch the two literals that are the
        // last to become false under the current assignment. Ranking prefers a
        // true literal, then an unassigned one, and only then a false literal at
        // the highest decision level (see `watch_rank`).
        //
        // The previous code unconditionally watched `clause_lits[0..2]`. After a
        // prior `solve()` left a full trail (with `prop_head == len`), a clause
        // whose two lowest-code literals are false-but-already-propagated would
        // have both watches on false literals; those watch events never fire
        // again, so the clause could be silently falsified. A later `solve()`
        // could then return Sat on a model violating the clause, or miss a
        // conflict on an actually-UNSAT formula. Watching the two
        // latest-falsified literals restores the invariant that a watched
        // literal becoming false always re-examines the clause.
        //
        // Safe to run *after* `pre_check_effective_unit` above: any
        // `backtrack_to_root()` it performed has already happened, so this
        // ranking sees the final, post-backtrack trail state rather than one
        // that gets invalidated out from under it.
        let n = clause_lits.len();
        let mut best = 0;
        for i in 1..n {
            if self.watch_rank(clause_lits[i]) > self.watch_rank(clause_lits[best]) {
                best = i;
            }
        }
        clause_lits.swap(0, best);
        let mut second = 1;
        for i in 2..n {
            if self.watch_rank(clause_lits[i]) > self.watch_rank(clause_lits[second]) {
                second = i;
            }
        }
        clause_lits.swap(1, second);

        let clause_id = self.clauses.add_original(clause_lits.iter().copied());
        self.proof_set_clause_id(clause_id, proof_oid);

        // Track clause for incremental solving
        if let Some(current_level_clauses) = self.assertion_clause_ids.last_mut() {
            current_level_clauses.push(clause_id);
        }

        let lit0 = clause_lits[0];
        let lit1 = clause_lits[1];

        self.watches
            .add(lit0.negate(), Watcher::new(clause_id, lit1));
        self.watches
            .add(lit1.negate(), Watcher::new(clause_id, lit0));

        // `pre_check_effective_unit` already determined -- against the exact
        // pre-watch-selection trail state, before anything here could shift
        // it -- whether this clause needs its sole undefined literal forced,
        // and confirmed every false literal is a permanent level-0 fact when
        // it did. Apply that decision now that `clause_id` exists.
        if let PreAttachOutcome::ForceUnitAtLevelZero(forced) = outcome {
            self.trail.assign_propagation_at(forced, clause_id, 0);
        }

        true
    }

    /// Rank a literal for two-watched-literal selection; a higher rank is a
    /// better watch. A true literal is best (the clause is satisfied through it),
    /// then an unassigned literal, and finally a false literal — and among false
    /// literals the one assigned at the highest decision level (falsified latest)
    /// is preferred. Watching the two highest-ranked literals mirrors MiniSat's
    /// attachClause invariant so a watch always fires when a watched literal is
    /// (re)falsified.
    pub(super) fn watch_rank(&self, l: Lit) -> (u8, u32) {
        let v = self.trail.lit_value(l);
        if v.is_true() {
            (2, u32::MAX)
        } else if v.is_false() {
            (0, self.trail.level(l.var()))
        } else {
            (1, u32::MAX)
        }
    }

    /// Add a clause from DIMACS literals
    pub fn add_clause_dimacs(&mut self, lits: &[i32]) -> bool {
        self.add_clause(lits.iter().map(|&l| Lit::from_dimacs(l)))
    }

    /// Decay clause activity the MiniSat way: grow the per-conflict bump
    /// increment (so recently-useful clauses dominate) instead of multiplying
    /// every clause's activity on every conflict. Rescale only when the
    /// increment approaches the f64 range limit — a rare O(n) pass that
    /// replaces what was an O(n) pass *every* conflict (a top flamegraph
    /// hotspot). The only active consumer of clause activity is
    /// `reduce_clause_database`, which ranks clauses relatively, so the
    /// implicit decay preserves correctness.
    pub(super) fn decay_clause_activity(&mut self) {
        self.clause_bump_increment /= self.config.clause_decay;
        if self.clause_bump_increment > 1e100 {
            const FACTOR: f64 = 1e-100;
            self.clauses.rescale_activity(FACTOR);
            self.clause_bump_increment *= FACTOR;
        }
    }

    /// Solve the SAT problem
    pub fn solve(&mut self) -> SolverResult {
        // Check if trivially unsatisfiable
        if self.trivially_unsat {
            self.drat_emit_empty(None);
            return SolverResult::Unsat;
        }

        // Initial propagation
        if self.propagate().is_some() {
            self.drat_emit_empty(None);
            return SolverResult::Unsat;
        }

        // Equivalent-literal substitution (SCC on the binary implication graph).
        // Collapses binary-heavy formulas before search; a no-op (early-out)
        // when there are no non-trivial SCCs. Runs at level 0 / base scope only.
        if self.config.enable_bve {
            if self.bounded_variable_elimination() == equiv::SubstOutcome::Unsat {
                self.drat_emit_empty(None);
                return SolverResult::Unsat;
            }
            if self.trivially_unsat {
                self.drat_emit_empty(None);
                return SolverResult::Unsat;
            }
        }
        if self.config.enable_equiv_substitution {
            if self.substitute_equivalent_literals() == equiv::SubstOutcome::Unsat {
                self.drat_emit_empty(None);
                return SolverResult::Unsat;
            }
            if self.trivially_unsat {
                self.drat_emit_empty(None);
                return SolverResult::Unsat;
            }
        }
        // Forward subsumption + self-subsumption. Skipped when equivalent-
        // literal substitution rewrote the clause database: the subsumption-
        // after-substitution sequence has a rare (≈1/15k) wrong-model
        // interaction still under investigation, so the two are not run
        // together. Also skipped after BVE: running forward-subsumption over
        // the BVE-reduced clause set (with BVE-derived units on the level-0
        // trail) derives a spurious level-0 conflict on some SAT instances
        // (reproduces on noL-11-14: SAT -> false UNSAT, 0 conflicts). BVE is
        // currently off in every preset -- with the sound literal-count bound
        // it eliminates no variables on the benchmarks tried -- so this guard
        // is preventive, but it documents a real soundness hazard if BVE is
        // re-enabled without also fixing the subsumption interaction.
        if (self.config.enable_bve || self.config.enable_equiv_substitution)
            && !self.did_equiv_subst
            && !self.did_bve
        {
            self.forward_subsumption();
            self.self_subsumption_pass();
            if self.trivially_unsat {
                self.drat_emit_empty(None);
                return SolverResult::Unsat;
            }
        }

        // Lucky pre-solving (CaDiCaL `lucky_phases`): try to satisfy the
        // formula without search via a small set of structured phase guesses
        // (uniform / Horn / ordered-with-flip). On by default, matching
        // CaDiCaL — each strategy is soundness-preserving (a pure scan or a
        // single-literal-at-a-time probe that bails to the root on failure, so
        // a doomed guess never perturbs the watched-literal state).
        if self.config.enable_lucky {
            match self.lucky_phases() {
                Some(SolverResult::Sat) => {
                    self.save_model();
                    return SolverResult::Sat;
                }
                Some(SolverResult::Unsat) => return SolverResult::Unsat,
                _ => {}
            }
        }

        // Pre-search inprocessing pass (failed-literal probing + subsumption +
        // strengthening) when enabled. Mirrors cadical's preprocessing: for
        // structured instances (e.g. `longmult`) probing deduces forced units
        // up front. Probing runs once here (not on every periodic inprocess
        // call) because brute-force per-variable probing is too expensive to
        // repeat — cadical schedules it on binary-implication roots, which is a
        // larger follow-up.
        if self.config.enable_inprocessing {
            if self.config.enable_failed_literal_probing {
                self.failed_literal_probing();
            }
            if !self.trivially_unsat && self.config.enable_hyper_binary_probing {
                self.probe_hyper_binary();
            }
            if !self.trivially_unsat {
                self.inprocess();
            }
            if !self.trivially_unsat {
                self.vivify_clauses();
            }
            if self.trivially_unsat {
                self.drat_emit_empty(None);
                return SolverResult::Unsat;
            }
        }

        loop {
            // Resource budget / interrupt check: honor a configured conflict
            // limit or an external interrupt by returning Unknown rather than
            // spinning forever on a hard instance.
            if self.should_stop_search() {
                return SolverResult::Unknown;
            }

            // Propagate
            if let Some(conflict) = self.propagate() {
                self.debug_check_conflict_clause(conflict);
                self.stats.conflicts += 1;
                self.conflicts_since_inprocessing += 1;

                if self.trail.decision_level() == 0 {
                    // Conflict under only level-0 (unconditional) facts: the empty
                    // clause is derivable, completing the proof of UNSAT. Pass the
                    // conflict clause so the LRAT empty-clause chain can be built.
                    self.drat_emit_empty(Some(conflict));
                    return SolverResult::Unsat;
                }

                // Analyze conflict
                let (backtrack_level, learnt_clause) = self.analyze(conflict);

                // Empty learned clause = genuine root-level (level-0) refutation:
                // every conflict literal is false under unconditional facts, so
                // the instance is UNSAT and the empty clause completes the proof.
                // `analyze` can report this even above decision level 0 when a
                // clause is falsified purely at the root.
                if learnt_clause.is_empty() {
                    self.trivially_unsat = true;
                    self.drat_emit_empty(Some(conflict));
                    return SolverResult::Unsat;
                }

                // Backtrack with phase saving
                self.backtrack_with_phase_saving(backtrack_level);
                self.debug_check_invariants("after backtrack");

                // Emit the learned clause as a derived-clause proof event
                // (RUP-derivable from the current database by construction of
                // 1-UIP learning, with the chain assembled in `analyze`). Covers
                // both the unit and general learned-clause branches below; the
                // returned id is bound to the stored clause once added.
                let proof_id = self.proof_learn_clause(&learnt_clause);

                // Learn clause
                if learnt_clause.len() == 1 {
                    // Store unit learned clause in database for persistence
                    let clause_id = self.clauses.add_learned(learnt_clause.iter().copied());
                    self.proof_set_clause_id(clause_id, proof_id);
                    self.stats.learned_clauses += 1;
                    self.stats.unit_clauses += 1;
                    self.learned_clause_ids.push(clause_id);

                    // Track for incremental solving
                    if let Some(current_level_clauses) = self.assertion_clause_ids.last_mut() {
                        current_level_clauses.push(clause_id);
                    }

                    self.assert_learned_clause(&learnt_clause, clause_id);
                } else {
                    // Compute LBD for the learned clause
                    let lbd = self.compute_lbd(&learnt_clause);

                    // Accumulate for the `avg_lbd` stat. (The only other writers
                    // of `stats.total_lbd` are on a dead legacy path in
                    // `learn.rs`, so without this the reported average was 0.)
                    self.stats.total_lbd = self.stats.total_lbd.saturating_add(lbd as u64);

                    // Track recent LBD for the local-restart strategy.
                    self.recent_lbd_sum += u64::from(lbd);
                    self.recent_lbd_count += 1;
                    self.global_lbd_sum += u64::from(lbd);
                    self.global_lbd_count += 1;

                    // cadical glue EMA update (per-mode `current` averages) +
                    // reluctant-doubling tick for stable-mode restarts.
                    let l = f64::from(lbd);
                    self.glue_current.fast.update(l);
                    self.glue_current.slow.update(l);
                    self.reluctant.tick();

                    // Reset recent LBD tracking periodically
                    if self.recent_lbd_count >= 5000 {
                        self.recent_lbd_sum /= 2;
                        self.recent_lbd_count /= 2;
                    }

                    let clause_id = self.clauses.add_learned(learnt_clause.iter().copied());
                    self.proof_set_clause_id(clause_id, proof_id);
                    self.stats.learned_clauses += 1;

                    // Set LBD score for the clause
                    if let Some(clause) = self.clauses.get_mut(clause_id) {
                        clause.lbd = lbd;
                        clause.assign_tier_from_lbd();
                    }
                    self.debug_check_learned_clause_lbd(clause_id);

                    // Track learned clause for potential deletion
                    self.learned_clause_ids.push(clause_id);

                    // Track clause for incremental solving
                    if let Some(current_level_clauses) = self.assertion_clause_ids.last_mut() {
                        current_level_clauses.push(clause_id);
                    }

                    // Watch first two literals
                    let lit0 = learnt_clause[0];
                    let lit1 = learnt_clause[1];
                    self.watches
                        .add(lit0.negate(), Watcher::new(clause_id, lit1));
                    self.watches
                        .add(lit1.negate(), Watcher::new(clause_id, lit0));

                    // Propagate the asserting literal at its true implication
                    // level (see `Solver::assert_learned_clause`).
                    self.assert_learned_clause(&learnt_clause, clause_id);
                }

                // Decay activities
                self.vsids.decay();
                if self.config.use_chb_branching {
                    self.chb.decay();
                }
                if self.config.use_lrb_branching {
                    self.lrb.decay();
                    self.lrb.on_conflict();
                }
                self.decay_clause_activity();

                // Track conflicts for clause deletion
                self.conflicts_since_deletion += 1;

                // Periodic clause database reduction
                if self.conflicts_since_deletion >= self.config.clause_deletion_threshold as u64 {
                    self.reduce_clause_database();
                    self.debug_check_invariants("after clause database reduction");
                    self.conflicts_since_deletion = 0;

                    // Vivification after clause database reduction (at level 0 after restart)
                    if self.stats.restarts.is_multiple_of(10) {
                        let saved_level = self.trail.decision_level();
                        if saved_level == 0 {
                            self.vivify_clauses();
                        }
                    }
                }

                // Stable/focused mode switch (cadical-style adaptive restart
                // schedule) — checked each conflict, before the restart decision
                // so the mode affects this restart's interval.
                self.check_stabilize();

                // cadical restart: focused mode uses the Glucose EMA condition
                // (fast glue >= (1+margin)*slow, checked every `restartint=2`
                // conflicts); stable mode uses the reluctant (Luby) trigger.
                // The legacy strategies (Luby-cap etc.) apply only when the
                // stable/focused schedule is disabled.
                let do_restart = if self.config.enable_stabilize {
                    if self.stable {
                        self.reluctant.activated()
                    } else {
                        // Focused Glucose: check every 2 conflicts.
                        if self.stats.conflicts < self.lim_restart {
                            false
                        } else {
                            self.lim_restart = self.stats.conflicts.saturating_add(2);
                            let slow = self.glue_current.slow.value();
                            let fast = self.glue_current.fast.value();
                            // 10% margin (cadical restartmarginfocused); guard
                            // against the all-zero initial state.
                            slow > 0.0 && fast >= 1.10 * slow
                        }
                    }
                } else {
                    let past_threshold = self.stats.conflicts >= self.restart_threshold;
                    let is_glucose =
                        matches!(self.config.restart_strategy, RestartStrategy::Glucose);
                    past_threshold && (!is_glucose || self.lbd_ema_fast >= 1.1 * self.lbd_ema_slow)
                };
                if do_restart {
                    self.restart();
                    // Reuse-trail restarts backtrack only to reuse_trail()
                    // (>0), so the level-0 restart-consistency invariant does
                    // not apply (see handle_clause_deletion_and_restart).
                    if !self.config.reuse_trail {
                        self.debug_check_restart_consistency();
                    }
                }

                // Periodic inprocessing
                if self.config.enable_inprocessing
                    && self.conflicts_since_inprocessing >= self.config.inprocessing_interval
                {
                    self.inprocess();
                    self.conflicts_since_inprocessing = 0;
                }
            } else {
                // No conflict - try to decide. `propagate()` just returned `None`,
                // i.e. reached a fixpoint, which is exactly where the watched-literal
                // and unit-propagation-completeness invariants become meaningful.
                self.debug_check_fixpoint_invariants("after propagation fixpoint");
                if let Some(var) = self.pick_branch_var() {
                    self.stats.decisions += 1;
                    self.trail.new_decision_level();

                    // Use phase saving with random polarity, XORed with the
                    // global rephase flip so a restart can explore the complementary
                    // phase region instead of re-deriving the same trail.
                    let polarity = if self.rand_bool(self.config.random_polarity_prob) {
                        // Random polarity
                        self.rand_bool(0.5)
                    } else {
                        // Saved phase, optionally inverted by rephasing
                        self.phase[var.index()] ^ self.phase_inverted
                    };
                    let lit = if polarity {
                        Lit::pos(var)
                    } else {
                        Lit::neg(var)
                    };
                    self.trail.assign_decision(lit);
                } else {
                    // All variables assigned - SAT
                    self.save_model();
                    self.debug_verify_model();
                    self.debug_check_invariants("at SAT");
                    return SolverResult::Sat;
                }
            }
        }
    }

    /// Solve with assumptions and return unsat core if UNSAT
    ///
    /// This is the key method for MaxSAT: it solves under assumptions and
    /// if the result is UNSAT, returns the subset of assumptions in the core.
    ///
    /// # Arguments
    /// * `assumptions` - Literals that must be true
    ///
    /// # Returns
    /// * `(SolverResult, Option<Vec<Lit>>)` - Result and unsat core (if UNSAT)
    pub fn solve_with_assumptions(
        &mut self,
        assumptions: &[Lit],
    ) -> (SolverResult, Option<Vec<Lit>>) {
        if self.trivially_unsat {
            return (SolverResult::Unsat, Some(Vec::new()));
        }

        // Ensure all assumption variables exist
        for &lit in assumptions {
            while self.num_vars <= lit.var().index() {
                self.new_var();
            }
        }

        // A prior solve() may have returned Sat while leaving its full model on the
        // trail (decisions at levels > 0). Fully restart the search state by
        // backtracking to the root BEFORE capturing `assumption_level_start` and
        // testing the assumptions. Otherwise leftover model decisions masquerade as
        // fixed level-0 facts: an assumption that merely disagrees with the previous
        // arbitrary model would hit `value.is_false()` below and be reported as a
        // false UNSAT (e.g. (a∨b); solve() picks ¬a,b; then assumptions=[a] must be
        // SAT, not UNSAT). This is the standard incremental / MaxSAT entry protocol.
        self.backtrack_with_phase_saving(0);

        // Clear conflict-analysis marks so a stale `seen` array left by a previous
        // solve cannot pollute the extracted assumption core.
        for s in &mut self.seen {
            *s = false;
        }

        // Initial propagation at level 0
        if self.propagate().is_some() {
            return (SolverResult::Unsat, Some(Vec::new()));
        }

        // Create a new decision level for assumptions
        let assumption_level_start = self.trail.decision_level();

        // Assign assumptions as decisions
        for (i, &lit) in assumptions.iter().enumerate() {
            // Check if already assigned
            let value = self.trail.lit_value(lit);
            if value.is_true() {
                continue; // Already satisfied
            }
            if value.is_false() {
                // Conflict with assumption - extract core from conflicting assumptions
                let core = self.extract_assumption_core(assumptions, i);
                self.backtrack(assumption_level_start);
                return (SolverResult::Unsat, Some(core));
            }

            // Make decision for assumption
            self.trail.new_decision_level();
            self.trail.assign_decision(lit);

            // Propagate after each assumption
            if let Some(conflict) = self.propagate() {
                // Conflict during assumption propagation: collect the full set of
                // contributing assumptions from the conflict clause.
                let core = self.analyze_assumption_conflict(assumptions, conflict);
                self.backtrack(assumption_level_start);
                return (SolverResult::Unsat, Some(core));
            }
        }

        // Now solve normally
        loop {
            // Resource budget / interrupt check: abandon under-assumption search
            // and report Unknown when the conflict budget or interrupt fires.
            if self.should_stop_search() {
                self.backtrack(assumption_level_start);
                return (SolverResult::Unknown, None);
            }

            if let Some(conflict) = self.propagate() {
                self.debug_check_conflict_clause(conflict);
                self.stats.conflicts += 1;

                // Check if conflict involves assumptions
                let backtrack_level = self.analyze_conflict_level(conflict);

                if backtrack_level <= assumption_level_start {
                    // Conflict forces backtracking past assumptions - UNSAT
                    let core = self.analyze_assumption_conflict(assumptions, conflict);
                    self.backtrack(assumption_level_start);
                    return (SolverResult::Unsat, Some(core));
                }

                let (bt_level, learnt_clause) = self.analyze(conflict);

                // Empty learned clause = genuine root-level (level-0) refutation.
                // The `backtrack_level <= assumption_level_start` guard above
                // already routes all-level-0 conflicts to the UNSAT-core path, so
                // this is a belt-and-braces guard that also avoids an empty-clause
                // index panic in `learn_clause`.
                if learnt_clause.is_empty() {
                    let core = self.analyze_assumption_conflict(assumptions, conflict);
                    self.backtrack(assumption_level_start);
                    return (SolverResult::Unsat, Some(core));
                }

                self.backtrack_with_phase_saving(bt_level.max(assumption_level_start + 1));
                self.debug_check_invariants("after backtrack (assumptions)");
                self.learn_clause(learnt_clause);

                self.vsids.decay();
                self.decay_clause_activity();
                self.handle_clause_deletion_and_restart_limited(assumption_level_start);
            } else {
                // No conflict - try to decide. `propagate()` just returned `None`,
                // i.e. reached a fixpoint.
                self.debug_check_fixpoint_invariants("after propagation fixpoint (assumptions)");
                if let Some(var) = self.pick_branch_var() {
                    self.stats.decisions += 1;
                    self.trail.new_decision_level();

                    let polarity = if self.rand_bool(self.config.random_polarity_prob) {
                        self.rand_bool(0.5)
                    } else {
                        self.phase.get(var.index()).copied().unwrap_or(false) ^ self.phase_inverted
                    };
                    let lit = if polarity {
                        Lit::pos(var)
                    } else {
                        Lit::neg(var)
                    };
                    self.trail.assign_decision(lit);
                } else {
                    // All variables assigned - SAT
                    self.save_model();
                    self.debug_verify_model();
                    self.debug_check_invariants("at SAT (assumptions)");
                    self.backtrack(assumption_level_start);
                    return (SolverResult::Sat, None);
                }
            }
        }
    }

    /// Get the model (if sat)
    #[must_use]
    pub fn model(&self) -> &[LBool] {
        &self.model
    }

    /// Get the value of a variable in the model
    #[must_use]
    pub fn model_value(&self, var: Var) -> LBool {
        self.model.get(var.index()).copied().unwrap_or(LBool::Undef)
    }

    /// Get statistics
    #[must_use]
    pub fn stats(&self) -> &SolverStats {
        &self.stats
    }

    /// Get memory optimizer statistics
    #[must_use]
    pub fn memory_opt_stats(&self) -> &crate::memory_opt::MemoryOptStats {
        self.memory_optimizer.stats()
    }

    /// Get number of variables
    #[must_use]
    pub fn num_vars(&self) -> usize {
        self.num_vars
    }

    /// Get number of clauses
    /// Soundness gate: does the current trail falsify a live clause?
    ///
    /// With a correct BCP this is never true — a clause whose every literal is
    /// false is a conflict, and `propagate` must have reported it before the
    /// search could run out of variables to assign.  It is checked anyway at the
    /// one place a wrong answer would escape (the `Sat` exit of the CDCL(T)
    /// loop), because a stale watch means `propagate` silently stops enforcing a
    /// clause: the search then assigns every variable, sees no conflict, and
    /// reports a "model" that violates the formula.
    ///
    /// Answering `Unknown` on such a trail is a backstop, not a repair; the
    /// underlying propagation defect still needs fixing.  Cost is one linear
    /// scan of the clause database, paid once per `Sat` verdict.
    ///
    /// Disabled once `push()` has been used: `pop()` leaves retracted clauses
    /// live in the database (watch lists are cleaned lazily), so the scan would
    /// flag them and turn a correct `Sat` into `Unknown`.
    #[must_use]
    pub fn trail_falsifies_live_clause(&self) -> bool {
        if self.ever_pushed {
            return false;
        }
        self.clauses.iter_ids().any(|id| {
            self.clauses.get(id).is_some_and(|c| {
                !c.deleted
                    && !c.lits.is_empty()
                    && c.lits.iter().all(|l| self.trail.lit_value(*l).is_false())
            })
        })
    }

    /// Total number of clauses currently in the database (original + learned).
    #[must_use]
    pub fn num_clauses(&self) -> usize {
        self.clauses.len()
    }

    /// Number of *original* (asserted, non-learned) clauses in the database.
    ///
    /// This is the ground truth for "how much did the caller's encoding grow",
    /// and it is **not** the same as `num_clauses() - learned_clause_count()`:
    /// [`Self::learned_clause_count`] reports the size of the
    /// `learned_clause_ids` registry, which is a *subset* of the clauses the
    /// database itself flags as learned (the registry exists so an incremental
    /// caller can forget a probe's learned clauses again).  Subtracting it from
    /// the total therefore silently counts every unregistered learned clause as
    /// "original".  Callers that want to pin encoder growth must use this.
    #[must_use]
    pub fn num_original_clauses(&self) -> usize {
        self.clauses.num_original()
    }

    /// Number of clauses the database flags as learned.
    ///
    /// See [`Self::num_original_clauses`] for why this can exceed
    /// [`Self::learned_clause_count`].
    #[must_use]
    pub fn num_learned_clauses(&self) -> usize {
        self.clauses.num_learned()
    }

    /// Push a new assertion level (for incremental solving)
    ///
    /// This saves the current state so that clauses added after this point
    /// can be removed with pop(). Automatically backtracks to decision level 0
    /// to ensure a clean state for adding new constraints.
    pub fn push(&mut self) {
        self.ever_pushed = true;
        // Backtrack to level 0 to ensure clean state
        // This is necessary because solve() may leave assignments on the trail
        // Use phase-saving backtrack to properly re-insert variables into decision heaps
        self.backtrack_with_phase_saving(0);

        self.assertion_levels.push(self.clauses.num_original());
        self.assertion_trail_sizes.push(self.trail.size());
        self.assertion_clause_ids.push(Vec::new());
    }

    /// Pop to previous assertion level
    pub fn pop(&mut self) {
        if self.assertion_levels.len() > 1 {
            self.assertion_levels.pop();

            // Get the trail size to backtrack to
            let trail_size = self.assertion_trail_sizes.pop().unwrap_or(0);

            // Remove all clauses added at this assertion level
            if let Some(clause_ids_to_remove) = self.assertion_clause_ids.pop() {
                for clause_id in clause_ids_to_remove {
                    // Purge any binary-implication-graph edges for this clause
                    // before removing it. Unlike the watch lists (which lazily
                    // skip deleted clauses during propagation), the binary graph
                    // is consulted directly, so leaving stale edges behind would
                    // let a retracted binary clause keep propagating after pop().
                    self.purge_binary_edges(clause_id);

                    // Record the retraction in the DRAT proof (if enabled) before
                    // the clause's literals become inaccessible.
                    self.drat_delete(clause_id);

                    // Remove from clause database
                    self.clauses.remove(clause_id);

                    // Remove from learned clause tracking if it's a learned clause
                    self.learned_clause_ids.retain(|&id| id != clause_id);

                    // Note: Watch lists will be cleaned up naturally during propagation
                    // as they check if clauses are deleted before using them
                }
            }

            // Backtrack trail to the exact size it was at push()
            // This properly handles unit clauses that were added after push
            // Note: backtrack_to_size clears values but doesn't re-insert into heaps,
            // so we need to manually re-insert unassigned variables.
            let current_size = self.trail.size();
            if current_size > trail_size {
                // Collect variables that will be unassigned
                let mut unassigned_vars = Vec::new();
                for i in trail_size..current_size {
                    let lit = self.trail.assignments()[i];
                    unassigned_vars.push(lit.var());
                }

                self.trail.backtrack_to_size(trail_size);

                // Re-insert unassigned variables into decision heaps
                for var in unassigned_vars {
                    if !self.vsids.contains(var) {
                        self.vsids.insert(var);
                    }
                    if !self.chb.contains(var) {
                        self.chb.insert(var);
                    }
                    self.lrb.unassign(var);
                }
            }

            // Ensure we're at decision level 0 with proper heap re-insertion
            self.backtrack_with_phase_saving(0);

            // Re-arm unit propagation over the retained prefix.
            //
            // `backtrack_to_size` parks the propagation head at the end of the
            // surviving trail, declaring that prefix fully propagated. That is
            // false here for two independent reasons: the discarded suffix held
            // level-0 *consequences* of the retained prefix, and this pop has
            // just removed clauses the prefix was propagated against. The
            // surviving literals are therefore assigned but no longer followed by
            // their implications, and nothing would ever recompute them —
            // `backtrack_with_phase_saving(0)` above only clamps the head when it
            // actually rolls a level back, and after `backtrack_to_size` the
            // solver already sits at level 0.
            //
            // A clause left falsified that way is never revisited: its watched
            // literals were assigned before the head and so are never
            // re-propagated, so the conflict is silently lost and the next
            // `solve()` reports `Sat` on a model violating it. Rewinding costs
            // one extra pass over the retained watch lists; re-propagating an
            // already-assigned literal is a no-op, so it has no semantic effect
            // beyond restoring the facts the pop erased. Mirrors the same rewind
            // in `Solver::restore_to_trail_size`.
            self.trail.reset_propagation_head();

            // Clear the trivially_unsat flag as we've removed problematic clauses
            self.trivially_unsat = false;
        }
    }

    /// Backtrack to decision level 0 (for AllSAT enumeration)
    ///
    /// This is necessary after a SAT result before adding blocking clauses
    /// to ensure the new clauses can trigger propagation correctly.
    /// Uses phase-saving backtrack to properly re-insert unassigned variables
    /// into the decision heaps (VSIDS, CHB, LRB).
    pub fn backtrack_to_root(&mut self) {
        self.backtrack_with_phase_saving(0);
    }

    /// Reset the solver
    pub fn reset(&mut self) {
        self.clauses = ClauseDatabase::new();
        self.trail.clear();
        self.watches.clear();
        self.vsids.clear();
        self.domain_priority.clear();
        self.chb.clear();
        self.stats = SolverStats::default();
        self.learnt.clear();
        self.seen.clear();
        self.analyze_stack.clear();
        self.assertion_levels.clear();
        self.assertion_levels.push(0);
        self.assertion_trail_sizes.clear();
        self.assertion_trail_sizes.push(0);
        self.assertion_clause_ids.clear();
        self.assertion_clause_ids.push(Vec::new());
        self.model.clear();
        self.num_vars = 0;
        // Decision heuristics: `vsids`/`chb` are cleared below, but `vmtf`
        // and `lrb` only ever *grow* (`resize` is a no-op when num_vars shrinks),
        // so without resetting them they keep every variable from the pre-reset
        // problem as a live decision candidate.  Reusing the solver then lets
        // `pick_branch_var` return a variable index that no longer exists
        // (`num_vars` was reset to 0 and only the new problem's vars were
        // re-created via `new_var`), which `assign_decision` happily pushes onto
        // the trail — and the next `propagate` indexes the still-small
        // `binary_graph` (and other var-indexed arrays) out of bounds.
        // Rebuild them empty so `new_var` repopulates from scratch.
        self.vmtf = VMTF::new(0);
        self.lrb = LRB::new(0);
        self.best_phase.clear();
        self.best_trail_size = 0;
        // `ever_pushed` latches once push/pop is used and permanently disables
        // the `trail_falsifies_live_clause` backstop.  It must be cleared on
        // reset so a fresh problem gets the backstop again.
        self.ever_pushed = false;
        self.restart_threshold = self.config.restart_interval;
        self.trivially_unsat = false;
        self.phase.clear();
        self.luby_index = 0;
        self.level_marks.clear();
        self.lbd_mark = 0;
        self.learned_clause_ids.clear();
        self.conflicts_since_deletion = 0;
        self.rng_state = 0x853c_49e6_748f_ea9b;
        self.recent_lbd_sum = 0;
        self.recent_lbd_count = 0;
        self.binary_graph.clear();
        self.global_lbd_sum = 0;
        self.global_lbd_count = 0;
        self.conflicts_since_local_restart = 0;
        self.pure_literal_reconstruction.clear();
        // Drop any proof logger: its clause ids refer to the now-cleared database,
        // so continuing to emit against it would produce a meaningless proof.
        self.disable_proof();
    }

    /// Get the current trail (for theory solvers)
    #[must_use]
    pub fn trail(&self) -> &Trail {
        &self.trail
    }

    /// Get the current decision level
    #[must_use]
    pub fn decision_level(&self) -> u32 {
        self.trail.decision_level()
    }

    /// Debug method: print all learned clauses
    pub fn debug_print_learned_clauses(&self) {
        println!(
            "=== Learned Clauses ({}) ===",
            self.learned_clause_ids.len()
        );
        for (i, &cid) in self.learned_clause_ids.iter().enumerate() {
            if let Some(clause) = self.clauses.get(cid)
                && !clause.deleted
            {
                let lits: Vec<String> = clause
                    .lits
                    .iter()
                    .map(|lit| {
                        let var = lit.var().index();
                        if lit.is_pos() {
                            format!("v{}", var)
                        } else {
                            format!("~v{}", var)
                        }
                    })
                    .collect();
                println!(
                    "  Learned {}: ({}), LBD={}",
                    i,
                    lits.join(" | "),
                    clause.lbd
                );
            }
        }
    }

    /// Debug method: print binary implication graph entries
    pub fn debug_print_binary_graph(&self) {
        println!("=== Binary Implication Graph ===");
        for lit_code in 0..(self.num_vars * 2) {
            let lit = Lit::from_code(lit_code as u32);
            let implications = self.binary_graph.get(lit);
            if !implications.is_empty() {
                let lit_str = if lit.is_pos() {
                    format!("v{}", lit.var().index())
                } else {
                    format!("~v{}", lit.var().index())
                };
                for &(implied, _cid) in implications {
                    let impl_str = if implied.is_pos() {
                        format!("v{}", implied.var().index())
                    } else {
                        format!("~v{}", implied.var().index())
                    };
                    println!("  {} -> {}", lit_str, impl_str);
                }
            }
        }
    }
}

#[cfg(test)]
mod tests;
