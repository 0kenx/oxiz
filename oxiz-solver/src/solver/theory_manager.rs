//! Theory manager that bridges the SAT solver with theory solvers

#[allow(unused_imports)]
use crate::prelude::*;
use num_rational::Rational64;
use num_traits::ToPrimitive;
use oxiz_core::ast::{TermId, TermKind, TermManager};
use oxiz_sat::{Lit, TheoryCallback, TheoryCheckResult, Var};
use oxiz_theories::arithmetic::ArithSolver;
use oxiz_theories::bv::BvSolver;
use oxiz_theories::euf::EufSolver;
use oxiz_theories::{EqualityNotification, Theory, TheoryCombination};
use smallvec::SmallVec;

use super::theory_bv_encode::{debug_verify_bv_circuits, encode_bv_term_recursive};
use super::types::{
    ArithConstraintType, Constraint, ParsedArithConstraint, Statistics, TheoryMode,
};

mod conflict_clause;
mod derived_reasons;
pub(crate) use derived_reasons::DerivedReasons;

/// One entry of the theory manager's own deduplicated assignment trail.
///
/// The SAT core drives theory state incrementally through `on_assignment` /
/// `on_new_level` / `on_backtrack`, but its conflict analysis can (on some
/// formulas) compute a wrong backtrack level and *overwrite* a variable's
/// assignment in place — flipping a decision literal's polarity without ever
/// popping the theory scope that recorded the old polarity.  The incremental
/// EUF / arith / BV solvers only support level-scoped `pop`, not point removal
/// of a single mid-level assertion, so a flipped literal would otherwise leave
/// the theory state permanently reflecting the stale polarity and manufacture a
/// spurious conflict (observed as a wrong top-level UNSAT on satisfiable
/// disjunctive LIA chains).  We therefore shadow every theory-relevant
/// assignment here, keyed so a flip is detected in O(1), and rebuild theory
/// state from the corrected trail when one occurs.
#[derive(Debug, Clone, Copy)]
struct TrailAtom {
    /// The SAT variable that was assigned.
    var: Var,
    /// `true` when the atom was assigned true, `false` when assigned false.
    is_positive: bool,
    /// The SAT decision level at which the assignment currently holds.
    level: u32,
}

/// One pending application of an iterative EUF interning walk
/// ([`TheoryManager::intern_term_deep`] and
/// [`TheoryManager::intern_term_for_congruence`]).
///
/// The frame owns the application's operand list and the EUF nodes of the
/// operands already interned, so the walk never needs the native call stack
/// and never needs to re-borrow a half-finished parent.
struct InternFrame {
    /// The application term whose operands are being interned.
    term: TermId,
    /// EUF function symbol of the application (`SELECT_FUNC_ID` for `select`).
    func_id: u32,
    /// The application's operands, in order.
    operands: SmallVec<[TermId; 4]>,
    /// Index of the next operand to descend into.
    next: usize,
    /// EUF nodes of the operands interned so far, in order.
    nodes: SmallVec<[u32; 4]>,
}

/// Theory manager that bridges the SAT solver with theory solvers
pub(crate) struct TheoryManager<'a> {
    /// Reference to the term manager
    manager: &'a TermManager,
    /// Reference to the EUF solver
    euf: &'a mut EufSolver,
    /// Reference to the arithmetic solver
    arith: &'a mut ArithSolver,
    /// Reference to the bitvector solver
    bv: &'a mut BvSolver,
    /// Bitvector terms (for identifying BV variables)
    bv_terms: &'a FxHashSet<TermId>,
    /// Mapping from SAT variables to constraints
    var_to_constraint: &'a FxHashMap<Var, Constraint>,
    /// Mapping from SAT variables to parsed arithmetic constraints
    var_to_parsed_arith: &'a FxHashMap<Var, ParsedArithConstraint>,
    /// Mapping from terms to SAT variables (for conflict clause generation)
    term_to_var: &'a FxHashMap<TermId, Var>,
    /// Reverse mapping from SAT variables to terms (for EUF merge reasons)
    var_to_term: &'a Vec<TermId>,
    /// Fresh `ite`-result constants (`__oxiz_ite_*`) axiomatized against
    /// constants (z3-style triangle).  Used by `final_check` to theory-propagate
    /// the `le`/`ge` atoms deterministically when arithmetic fixes such a term
    /// to a constant, so the equality is shared to EUF without CDCL search and
    /// without fragile model-based merging.
    ite_result_terms: &'a FxHashSet<TermId>,
    /// `(ite-result term, constant value) → (le_var, ge_var)` for the z3-style
    /// triangle axioms added at encode time.  Built once in [`new`] by scanning
    /// `var_to_constraint`; used by `final_check` to theory-propagate the `le`/
    /// `ge` atoms when arithmetic fixes an ite-result to a constant.
    ite_const_axioms: FxHashMap<(TermId, i64), (Var, Var)>,
    /// Current decision level stack for backtracking
    level_stack: Vec<usize>,
    /// Number of processed assignments
    processed_count: usize,
    /// Theory checking mode
    theory_mode: TheoryMode,
    /// Pending assignments for lazy theory checking
    pending_assignments: Vec<(Lit, bool)>,
    /// Pending equality notifications for Nelson-Oppen
    pending_equalities: Vec<EqualityNotification>,
    /// Processed equalities (to avoid duplicates)
    processed_equalities: FxHashMap<(TermId, TermId), bool>,
    /// Reference to solver statistics (for tracking)
    statistics: &'a mut Statistics,
    /// Maximum conflicts allowed (0 = unlimited)
    max_conflicts: u64,
    /// Maximum decisions allowed (0 = unlimited)
    #[allow(dead_code)]
    max_decisions: u64,
    /// Whether formula contains BV arithmetic operations (division/remainder)
    #[allow(dead_code)]
    has_bv_arith_ops: bool,
    /// Canonical EUF node for each distinct integer constant value.
    ///
    /// Maps an integer literal value (i64) to the canonical EUF node that
    /// represents it.  When a new `IntConst(v)` term is first encountered for a
    /// value `v`, we create its EUF node, assert pairwise disequalities against
    /// every canonical node of a different value, and record it here.
    ///
    /// If the same value `v` appears again (e.g., as a fresh TermId created
    /// during MBQI instantiation), we merge the new node with the existing
    /// canonical node rather than appending another entry.  This keeps the
    /// number of distinct entries — and therefore the number of pairwise
    /// disequality edges — bounded by the number of *distinct* integer literal
    /// values in the original formula, not by the total number of term IDs
    /// created across all MBQI iterations (which grows without bound).
    interned_int_constants: FxHashMap<i64, u32>,
    /// Canonical EUF nodes for distinct bit-vector constant *values*, keyed by
    /// `(value, width)`.  Mirrors `interned_int_constants` but for the BV theory:
    /// EUF has no notion that `#x00 != #x01`, so without explicit disequality
    /// edges a congruence chain merging `g(a)` (= `#x00`) with `g(b)` (= `#x01`)
    /// when `a = b` would not produce a conflict.  We track one canonical node
    /// per distinct `(value, width)` pair and assert pairwise disequalities
    /// between same-width constants, bounding the edge count by the number of
    /// distinct BV literals in the formula.
    ///
    /// The value half of the key is the constant's *full* little-endian limb
    /// sequence, not a `u64` digest of it.  Keying on the low 64 bits merged
    /// two genuinely different wide constants — `0` and `2^64` at width 128
    /// share those bits — into one EUF class, which turned a satisfiable
    /// `(distinct (g a) (g b))` into `unsat`.
    interned_bv_constants: FxHashMap<(SmallVec<[u64; 2]>, u32), u32>,
    /// Canonical EUF nodes for Boolean true and false values.
    /// Used to track Bool-valued function applications in EUF:
    /// when `f(x)` is assigned true by the SAT solver, we merge its EUF node
    /// with `bool_true_node`; when assigned false, with `bool_false_node`.
    /// A disequality `true != false` is asserted so that congruence closure
    /// detects conflicts (e.g., f(a)=true, f(b)=false, but a=b).
    bool_true_node: Option<u32>,
    bool_false_node: Option<u32>,
    /// Set to `true` when a genuine theory conflict was detected but suppressed
    /// because the conflict limit (`max_conflicts`) had been reached.  On
    /// exhaustion the manager returns `TheoryCheckResult::Sat` to make the SAT
    /// solver stop searching; that `Sat` is a resource signal, not a model.
    /// The owning `Solver` reads this flag after `solve_with_theory` and, when
    /// set, answers `Unknown` instead of trusting the `Sat` — so a dropped
    /// conflict never turns into a fabricated satisfiability result.
    resource_exhausted: bool,
    /// Set to `true` when a theory reported a conflict whose justification this
    /// manager could not account for, so that no conflict clause could be built
    /// (see [`Self::conflict_from_terms`]).
    ///
    /// Read like [`Self::resource_exhausted`], and for the same reason: the
    /// conflict was *dropped*, so a subsequent `Sat` rests on an assignment the
    /// theories may already have refuted and the owning `Solver` must answer
    /// `Unknown`.  An `Unsat` reached from other conflicts stays sound —
    /// dropping a lemma only ever removes refutations.
    ///
    /// This is a bug channel, not a resource one: every path that sets it is
    /// guarded by a `debug_assert!` that fails the build's tests first.  It
    /// exists so that the *release* build degrades to `Unknown` instead of
    /// emitting the empty clause, which claims an unconditional refutation.
    unjustified_conflict: bool,
    /// Wall-clock deadline for this solve, derived from `timeout_ms`.  `None`
    /// means no timeout.  Checked in the theory callbacks so a single
    /// uninterruptible `solve_with_theory` call cannot run past the budget:
    /// once the deadline passes we set `resource_exhausted` and stop reporting
    /// conflicts, forcing the search to terminate; the owning `Solver` then
    /// answers `Unknown`.
    #[cfg(feature = "std")]
    deadline: Option<std::time::Instant>,
    /// Latest SAT-assignment polarity of each theory-atom variable
    /// (`true` = atom assigned true, `false` = assigned false).  Recorded in
    /// `on_assignment` / lazy `final_check` so that `terms_to_conflict_clause`
    /// can emit, for each reason atom, the literal that is currently *false*
    /// (the negation of its assignment).  Without this a negatively-assigned
    /// atom would contribute a currently-*true* literal, violating the
    /// all-literals-false convention `analyze_theory_conflict` relies on and
    /// yielding an unsound lemma.
    assigned_polarity: FxHashMap<Var, bool>,
    /// Current SAT decision level, mirrored from `on_new_level` / `on_backtrack`.
    /// Used to stamp shadow-trail entries with the level they hold at.
    current_level: u32,
    /// Deduplicated shadow of every theory-relevant SAT assignment, in the
    /// order asserted.  Each variable appears at most once.  See [`TrailAtom`]
    /// for why this exists: it lets us detect an in-place polarity flip by the
    /// SAT core and rebuild theory state soundly rather than trust the stale
    /// incremental state.
    assignment_trail: Vec<TrailAtom>,
    /// Map from a theory variable to its index in `assignment_trail`, for O(1)
    /// flip detection.  Rebuilt whenever the trail is truncated on backtrack.
    trail_index: FxHashMap<Var, usize>,
    /// Decision level at which each entry of `assigned_polarity` currently
    /// holds, pruned on backtrack.  Unlike `assignment_trail` this is
    /// maintained in *both* eager and lazy theory modes, because it backs
    /// [`Self::full_assignment_conflict_clause`] — the sound fallback used
    /// when a theory reason cannot be justified.
    assigned_level: FxHashMap<Var, u32>,
    /// Reason terms that are theory *tautologies*: facts the theory layer
    /// injects itself, true in every model and justified by no literal.
    ///
    /// The interned-constant machinery asserts `10 ≠ 20`, `#x00 ≠ #x01` and
    /// `true ≠ false`, and merges two term ids that denote the same constant.
    /// Those assertions carry the constant's own term id as their reason, and
    /// that term id has no SAT variable.  Registering them here is what lets
    /// [`Self::terms_to_conflict_clause`] tell "correctly contributes nothing
    /// to the clause" apart from "justification silently lost".
    tautological_reasons: FxHashSet<TermId>,
    /// Explanations for reason terms that stand for a *derived* equality
    /// propagated between theories.
    ///
    /// `ArithSolver` records a single `TermId` per assertion, so an equality
    /// propagated out of congruence closure (`f(a) = f(b)` because `a = b`) can
    /// only be tagged with one of its own operands — a term that names no
    /// literal.  The EUF explanation of that equality is kept here, keyed by the
    /// tag, and [`Self::terms_to_conflict_clause`] expands the tag into those
    /// literals.  Without this the conflict clause would blame only the
    /// arithmetic atoms and refute a satisfiable formula at level 0.
    ///
    /// The table is **owned by the `Solver`**, not by this manager, because the
    /// arithmetic solver it explains is: `Solver::check` builds a fresh manager
    /// for every MBQI round while deliberately keeping the theory solvers'
    /// state.  A per-manager map started empty in front of a tableau that still
    /// held the previous round's derived equalities.  See
    /// [`DerivedReasons`] for the scope-depth pruning rule.
    derived_reasons: &'a mut DerivedReasons,
}

impl<'a> TheoryManager<'a> {
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn new(
        manager: &'a TermManager,
        euf: &'a mut EufSolver,
        arith: &'a mut ArithSolver,
        bv: &'a mut BvSolver,
        bv_terms: &'a FxHashSet<TermId>,
        var_to_constraint: &'a FxHashMap<Var, Constraint>,
        var_to_parsed_arith: &'a FxHashMap<Var, ParsedArithConstraint>,
        term_to_var: &'a FxHashMap<TermId, Var>,
        var_to_term: &'a Vec<TermId>,
        ite_result_terms: &'a FxHashSet<TermId>,
        derived_reasons: &'a mut DerivedReasons,
        theory_mode: TheoryMode,
        statistics: &'a mut Statistics,
        max_conflicts: u64,
        max_decisions: u64,
        has_bv_arith_ops: bool,
        timeout_ms: u64,
    ) -> Self {
        #[cfg(feature = "std")]
        let deadline = if timeout_ms > 0 {
            std::time::Instant::now().checked_add(core::time::Duration::from_millis(timeout_ms))
        } else {
            None
        };
        #[cfg(not(feature = "std"))]
        let _ = timeout_ms;
        Self {
            manager,
            euf,
            arith,
            bv,
            bv_terms,
            var_to_constraint,
            var_to_parsed_arith,
            term_to_var,
            var_to_term,
            ite_result_terms,
            derived_reasons,
            level_stack: vec![0],
            processed_count: 0,
            theory_mode,
            pending_assignments: Vec::new(),
            pending_equalities: Vec::new(),
            processed_equalities: FxHashMap::default(),
            statistics,
            max_conflicts,
            max_decisions,
            has_bv_arith_ops,
            interned_int_constants: FxHashMap::default(),
            interned_bv_constants: FxHashMap::default(),
            ite_const_axioms: Self::build_ite_const_axioms(
                var_to_constraint,
                ite_result_terms,
                manager,
            ),
            bool_true_node: None,
            bool_false_node: None,
            resource_exhausted: false,
            unjustified_conflict: false,
            #[cfg(feature = "std")]
            deadline,
            assigned_polarity: FxHashMap::default(),
            current_level: 0,
            assignment_trail: Vec::new(),
            trail_index: FxHashMap::default(),
            assigned_level: FxHashMap::default(),
            tautological_reasons: FxHashSet::default(),
        }
    }

    /// Build the `(ite-result, const) → (le_var, ge_var)` map for the z3-style
    /// triangle axioms by scanning the encoded comparison atoms.
    ///
    /// For every `le`/`ge` atom whose left operand is an axiomatized
    /// `ite`-result term and whose right operand is an integer constant, record
    /// the atom's SAT variable keyed by `(term, const_value)`.  `final_check`
    /// then theory-propagates both variables when arithmetic fixes the term to
    /// that constant, so the triangle clause `(eq ∨ ¬le ∨ ¬ge)` forces the
    /// equality deterministically.
    fn build_ite_const_axioms(
        var_to_constraint: &FxHashMap<Var, Constraint>,
        ite_result_terms: &FxHashSet<TermId>,
        manager: &TermManager,
    ) -> FxHashMap<(TermId, i64), (Var, Var)> {
        let int_const_value = |t: TermId| -> Option<i64> {
            manager.get(t).and_then(|tm| match &tm.kind {
                TermKind::IntConst(n) => n.to_i64(),
                _ => None,
            })
        };
        let mut map: FxHashMap<(TermId, i64), (Option<Var>, Option<Var>)> =
            FxHashMap::default();
        for (&var, constraint) in var_to_constraint {
            let (lhs, rhs, is_le) = match constraint {
                Constraint::Le(l, r) => (*l, *r, true),
                Constraint::Ge(l, r) => (*l, *r, false),
                _ => continue,
            };
            if !ite_result_terms.contains(&lhs) {
                continue;
            }
            let Some(c) = int_const_value(rhs) else {
                continue;
            };
            let entry = map.entry((lhs, c)).or_insert((None, None));
            if is_le {
                entry.0 = Some(var);
            } else {
                entry.1 = Some(var);
            }
        }
        map.into_iter()
            .filter_map(|(k, (le, ge))| Some((k, (le?, ge?))))
            .collect()
    }

    /// The polarity a theory variable is currently assigned, or `None` if it is
    /// unassigned (not yet decided/propagated by the SAT core).
    #[inline]
    fn assigned_pol_of(&self, var: Var) -> Option<bool> {
        self.assigned_polarity.get(&var).copied()
    }

    /// Returns `true` once the configured wall-clock deadline has passed.
    /// Always `false` when no timeout was set or in `no_std` builds (no clock).
    #[inline]
    fn timed_out(&self) -> bool {
        #[cfg(feature = "std")]
        {
            match self.deadline {
                Some(d) => std::time::Instant::now() >= d,
                None => false,
            }
        }
        #[cfg(not(feature = "std"))]
        {
            false
        }
    }

    /// Returns `true` if a real theory conflict was suppressed because the
    /// conflict limit was reached during this solve.  When set, the caller must
    /// treat any subsequent `Sat` as `Unknown`: the dropped conflict means the
    /// current assignment is not a verified model.
    pub(crate) fn resource_exhausted(&self) -> bool {
        self.resource_exhausted
    }

    /// Returns `true` if a theory conflict was dropped because its justification
    /// could not be accounted for.  Like [`Self::resource_exhausted`], the
    /// caller must then treat a `Sat` as `Unknown`.
    pub(crate) fn unjustified_conflict(&self) -> bool {
        self.unjustified_conflict
    }

    /// The single seam from "a theory refuted these reason terms" to a
    /// [`TheoryCheckResult`].
    ///
    /// Builds the conflict clause with [`Self::terms_to_conflict_clause`] and,
    /// when that cannot justify the conflict, **aborts the conflict** rather
    /// than emitting a clause: it flags [`Self::unjustified_conflict`] and
    /// reports `Sat`, which stops the SAT core from learning anything and makes
    /// the owning `Solver` answer `Unknown`.
    ///
    /// Routing every call site through here is what keeps the empty clause
    /// unrepresentable.  The alternative — returning "the negation of the empty
    /// assignment" — is the empty clause, i.e. a claim that the input is
    /// refuted unconditionally, produced by a code path whose whole premise is
    /// that it does not know why anything is refuted.  Answering `Unknown`
    /// loses a verdict; emitting that clause invents one.
    fn conflict_from_terms(&mut self, terms: &[TermId]) -> TheoryCheckResult {
        match self.terms_to_conflict_clause(terms) {
            Some(conflict) => TheoryCheckResult::Conflict(conflict),
            None => {
                self.unjustified_conflict = true;
                TheoryCheckResult::Sat
            }
        }
    }

    /// Open one theory scope on the EUF, arithmetic and bit-vector solvers.
    ///
    /// Every push of the three solvers goes through here (and every pop through
    /// [`Self::pop_theory_scope`]) so that `derived_reasons` — which outlives
    /// this manager — tracks their true depth.  Counting scopes from
    /// `level_stack` instead would restart at zero for every manager, while a
    /// CDCL(T) search that ends in `Sat` never backtracks and therefore hands
    /// the next manager solvers that are still several scopes deep.
    fn push_theory_scope(&mut self) {
        use oxiz_theories::Theory;

        self.level_stack.push(self.processed_count);
        self.euf.push();
        self.arith.push();
        self.bv.push();
        self.derived_reasons.push_scope();
    }

    /// Close one theory scope on the EUF, arithmetic and bit-vector solvers,
    /// dropping the derived-equality explanations that belonged to it.
    fn pop_theory_scope(&mut self) {
        use oxiz_theories::Theory;

        self.level_stack.pop();
        self.euf.pop();
        self.arith.pop();
        self.bv.pop();
        self.derived_reasons.pop_scope();
    }

    /// Rebuild all incremental theory state from the deduplicated shadow trail.
    ///
    /// Invoked when the SAT core overwrites a variable's assignment in place
    /// (flips a decision literal's polarity without a matching backtrack — a
    /// wrong assertion-level result from its conflict analysis).  The
    /// incremental EUF / arith / BV solvers still reflect the stale polarity and,
    /// because they support only level-scoped `pop` (not point removal of a
    /// single mid-level assertion), the stale fact cannot be surgically undone.
    /// We therefore `reset` the three theory solvers and replay the corrected
    /// trail level by level, re-establishing exactly one push scope per decision
    /// level so subsequent `on_backtrack` pops stay aligned with `level_stack`.
    ///
    /// Replay continues through every level even after a conflict is found, so
    /// that `level_stack` ends fully populated (`current_level + 1` entries) and
    /// any later backtrack — to any level — pops a matching number of scopes.
    /// The first conflict encountered is remembered and returned; a returned
    /// `Conflict` triggers the SAT core to backtrack, which the now-consistent
    /// scope stack handles correctly.
    fn resync_theory_state(&mut self) -> TheoryCheckResult {
        use oxiz_theories::Theory;

        // Drop all incremental theory state and derived caches.
        self.euf.reset();
        self.arith.reset();
        self.bv.reset();
        self.interned_int_constants.clear();
        self.interned_bv_constants.clear();
        self.bool_true_node = None;
        self.bool_false_node = None;
        self.processed_equalities.clear();
        self.pending_equalities.clear();
        // The proof forest these explanations were read out of is gone; the
        // equalities they justified are gone from the tableau with it.
        self.derived_reasons.clear();

        // Rebuild the level-scope bookkeeping to match the current level.
        self.level_stack = vec![0];
        self.processed_count = 0;

        let max_level = self.current_level;
        // Snapshot the trail so we can call `&mut self` methods while iterating.
        let trail = self.assignment_trail.clone();
        let mut first_conflict: Option<TheoryCheckResult> = None;

        for lvl in 0..=max_level {
            if lvl > 0 {
                self.push_theory_scope();
            }
            for atom in trail.iter().filter(|a| a.level == lvl) {
                let Some(constraint) = self.var_to_constraint.get(&atom.var).cloned() else {
                    continue;
                };
                self.processed_count += 1;
                let result =
                    self.process_constraint(atom.var, constraint, atom.is_positive, self.manager);
                if first_conflict.is_none() && matches!(result, TheoryCheckResult::Conflict(_)) {
                    first_conflict = Some(result);
                }
            }
        }

        first_conflict.unwrap_or(TheoryCheckResult::Sat)
    }

    /// Process Nelson-Oppen equality sharing
    /// Propagates equalities between theories until a fixed point is reached
    #[allow(dead_code)]
    fn propagate_equalities(&mut self) -> TheoryCheckResult {
        // Process all pending equalities
        while let Some(eq) = self.pending_equalities.pop() {
            // Avoid processing the same equality twice
            let key = if eq.lhs < eq.rhs {
                (eq.lhs, eq.rhs)
            } else {
                (eq.rhs, eq.lhs)
            };

            if self.processed_equalities.contains_key(&key) {
                continue;
            }
            self.processed_equalities.insert(key, true);

            // Notify EUF theory
            let lhs_node = self.euf.intern(eq.lhs);
            let rhs_node = self.euf.intern(eq.rhs);
            if let Err(_e) = self
                .euf
                .merge(lhs_node, rhs_node, eq.reason.unwrap_or(eq.lhs))
            {
                // Merge failed - should not happen
                continue;
            }

            // Check for conflicts after merging
            if let Some(conflict_terms) = self.euf.check_conflicts() {
                return self.conflict_from_terms(&conflict_terms);
            }

            // Notify arithmetic theory
            self.arith.notify_equality(eq);
        }

        TheoryCheckResult::Sat
    }

    /// Propagate EUF-derived equalities to the arithmetic solver.
    ///
    /// When EUF fires congruence closure and derives `f(x) = f(y)` because
    /// `x = y` was asserted, the arithmetic solver is unaware of this equality.
    /// This method gathers all arithmetic terms from `var_to_parsed_arith`,
    /// looks each one up in EUF (via `term_to_node`), and for any pair whose
    /// EUF nodes are in the same equivalence class asserts `t1 - t2 = 0` into
    /// the arithmetic solver.
    ///
    /// Note: `euf.intern(t)` uses the `term_to_node` map first, so it correctly
    /// returns the shared node index even when two distinct term IDs (e.g.
    /// `f_x_term` and `f_y_term`) were mapped to the same node via congruence
    /// during `intern_app`.
    ///
    /// The equality crosses a theory boundary, so it must arrive at the tableau
    /// with an **explanation**: `ArithSolver` stores one `TermId` per assertion
    /// and the only term ids available here — `t1`, `t2` — name no literal, so a
    /// conflict resting on the equality would be blamed on the arithmetic atoms
    /// alone.  We therefore ask congruence closure why `t1 = t2` holds
    /// ([`EufSolver::explain_eq`]) and record that answer under the tag `t1` in
    /// `derived_reason_justifications`, where `terms_to_conflict_clause` expands
    /// it back into literals.  An equality congruence closure cannot explain is
    /// not propagated at all: losing a propagation costs completeness, asserting
    /// an unexplainable fact costs soundness.
    fn propagate_euf_equalities_to_arith(
        &mut self,
        dedup: &mut FxHashSet<(TermId, TermId)>,
    ) -> TheoryCheckResult {
        // Collect every unique term ID that appears in any parsed arithmetic
        // constraint.  These are the terms the arithmetic solver knows about.
        let mut arith_terms: Vec<TermId> = Vec::new();
        for parsed in self.var_to_parsed_arith.values() {
            for &(term, _coef) in &parsed.terms {
                if !arith_terms.contains(&term) {
                    arith_terms.push(term);
                }
            }
        }

        // Incremental: group arith terms by EUF equivalence-class root and only
        // consider pairs *within* a class.  The old O(n^2) all-pairs scan (most
        // pairs are in different EUF classes and can never be equal) dominated
        // runtime on QF_UFLIA, where this runs once per full SAT assignment.
        // The class index skips the cross-class pairs for free; `dedup` avoids
        // re-asserting a pair already sent to Arith this call.
        let mut classes: FxHashMap<u32, Vec<TermId>> = FxHashMap::default();
        for term in &arith_terms {
            let Some(node) = self.euf.term_to_node(*term) else {
                continue;
            };
            let root = self.euf.find(node);
            classes.entry(root).or_default().push(*term);
        }

        for members in classes.values() {
            if members.len() < 2 {
                continue;
            }
            for i in 0..members.len() {
                for j in (i + 1)..members.len() {
                    let (mut t1, mut t2) = (members[i], members[j]);
                    if t1 > t2 {
                        std::mem::swap(&mut t1, &mut t2);
                    }
                    if !dedup.insert((t1, t2)) {
                        continue;
                    }
                    // EUF has derived t1 = t2 (same class). Assert the equality
                    // into the arithmetic solver.
                    if let Some(conflict) = self.assert_explained_equality(t1, t2) {
                        return conflict;
                    }
                }
            }
        }

        TheoryCheckResult::Sat
    }

    /// Assert an EUF-derived equality `t1 = t2` into the arithmetic solver,
    /// carrying the explanation that justifies it, and report any resulting
    /// arithmetic conflict.
    ///
    /// This is the single crossing point between congruence closure and the
    /// tableau, and the only place allowed to tag an arithmetic assertion with a
    /// term that names no literal.  It upholds two invariants:
    ///
    /// * an equality congruence closure cannot explain is **not propagated** —
    ///   skipping it only costs completeness, whereas asserting an unexplainable
    ///   fact makes every conflict that uses it unsound;
    /// * an equality that *is* propagated has its explanation recorded under the
    ///   tag `t1`, so [`Self::terms_to_conflict_clause`] can expand the tag back
    ///   into the literals it stands for.
    ///
    /// Returns `Some(Conflict(..))` only when the arithmetic solver refutes the
    /// system after the equality is added.
    fn assert_explained_equality(&mut self, t1: TermId, t2: TermId) -> Option<TheoryCheckResult> {
        use oxiz_theories::Theory;
        use oxiz_theories::TheoryCheckResult as TheoryCheckResultEnum;

        let n1 = self.euf.term_to_node(t1)?;
        let n2 = self.euf.term_to_node(t2)?;

        // `n1 == n2` means the two term ids were hash-consed onto one node, so
        // the equality is structural and rests on no assertion.  An empty
        // explanation for *distinct* nodes means no proof path was found, and
        // propagating then would re-create exactly the unjustified equality this
        // whole path exists to prevent.
        let justification = self.euf.explain_eq(n1, n2);
        if n1 != n2 && justification.is_empty() {
            return None;
        }
        self.derived_reasons.record(t1, justification);

        self.arith.assert_eq(
            &[
                (t1, Rational64::from_integer(1)),
                (t2, Rational64::from_integer(-1)),
            ],
            Rational64::from_integer(0),
            t1,
        );

        match self.arith.check() {
            Ok(TheoryCheckResultEnum::Unsat(conflict_terms)) => {
                Some(self.conflict_from_terms(&conflict_terms))
            }
            _ => None,
        }
    }

    /// Model-based theory combination.
    ///
    /// Finds shared terms that congruence closure has put in one equivalence
    /// class while the tableau's current model gives them different values.
    /// Two terms can only disagree inside a class, so instead of the naive O(n²)
    /// all-pairs scan we bucket each shared term by its EUF representative node
    /// in a single O(n) pass and compare each later class member against the
    /// first witness.
    ///
    /// A disagreement is a *model* disagreement, not a refutation: the tableau
    /// is free to pick another model that honours the equality.  The previous
    /// implementation reported it as a conflict and built the clause from the
    /// two disagreeing terms, which asserts that those two atoms are jointly
    /// contradictory — nothing entails that.  We instead resolve the
    /// disagreement the Nelson-Oppen way: hand the (explained) equality to the
    /// tableau via [`Self::assert_explained_equality`] and let it decide, so a
    /// conflict is reported only when arithmetic really is refuted and comes
    /// with arithmetic's own core.
    fn model_based_combination(&mut self) -> TheoryCheckResult {
        // Sound bound propagation: resolve forced comparison atoms before the
        // model-based disagreement check.
        if let Some(props) = self.derive_arith_propagations() {
            self.statistics.theory_propagations += props.len() as u64;
            return TheoryCheckResult::Propagated(props);
        }
        // Map EUF representative node -> (witness term, its arith value) for the
        // first class member that carries a concrete arithmetic value.  Terms
        // without an arith value cannot participate in an arith disagreement and
        // are simply skipped (mirroring the old `if let (Some, Some)` guard).
        let mut witness: FxHashMap<u32, (TermId, Rational64)> = FxHashMap::default();

        // `term_to_var` is a hash map, so iterate in term-id order: which member
        // of a class becomes the witness — and hence which equality is asserted
        // — must not depend on hash iteration order.
        let mut shared_terms: Vec<TermId> = self.term_to_var.keys().copied().collect();
        shared_terms.sort_unstable_by_key(|t| t.raw());
        for term in shared_terms {
            let Some(value) = self.arith.value(term) else {
                continue;
            };
            // `intern` returns the existing node (or creates one, matching the
            // previous behaviour), and `find` yields its equivalence-class root.
            let node = self.euf.intern(term);
            let rep = self.euf.find(node);

            match witness.get(&rep) {
                Some(&(prev_term, prev_value)) => {
                    if prev_value != value
                        && let Some(conflict) = self.assert_explained_equality(prev_term, term)
                    {
                        return conflict;
                    }
                }
                None => {
                    witness.insert(rep, (term, value));
                }
            }
        }

        TheoryCheckResult::Sat
    }

    /// Bidirectional Nelson–Oppen combination to a fixpoint.
    ///
    /// tip's [`Self::model_based_combination`] is one direction of the equality
    /// exchange — it propagates EUF-derived equalities *into* arithmetic (two
    /// shared terms in one EUF class with different arithmetic values must be
    /// equal, so assert the equality and let the tableau refute it).  The other
    /// direction — arithmetic-**entailed** equalities propagated *into* EUF —
    /// was missing, and its absence is the source of the non-convex
    /// QF_UFLIA/QF_UFIDL false-SAT: arithmetic can force `x = y` (e.g. two
    /// `ite`-result terms both pinned to `2·t`) while EUF holds them distinct
    /// under a `distinct`/disequality, and without propagating that entailed
    /// equality the `distinct` conflict is never seen.
    ///
    /// This closes the loop: alternate the two directions until neither produces
    /// new information (bounded, since each round strictly grows the EUF merge
    /// set or the asserted-equality set), then fall back to the model-based
    /// disagreement check.  Arithmetic-entailed equalities come with their
    /// Farkas reason ([`ArithSolver::entailed_equal_reason`]) and are
    /// recorded under their tag in [`derived_reasons`], so a conflict that cites
    /// the resulting EUF merge expands back to the arithmetic atoms that forced
    /// it — the merge is a *deduction*, never a guess, so it cannot cause a
    /// false `unsat`.
    fn nelson_oppen_combine(&mut self) -> TheoryCheckResult {
        use oxiz_theories::Theory;
        use oxiz_theories::TheoryCheckResult as TheoryCheckResultEnum;

        const NO_MAX_ROUNDS: usize = 8;
        for _ in 0..NO_MAX_ROUNDS {
            // ---- arithmetic → EUF: propagate entailed equalities. ----
            //
            // Care graph (cvc5-style watched differences): difference-constraint
            // pairs (x − y ≤ c) + live EUF disequality operands.  No model-equal
            // filter — the probe is sound regardless and catches chain-derived
            // equalities the model-equal filter misses.
            let mut candidates: rustc_hash::FxHashSet<(TermId, TermId)> =
                rustc_hash::FxHashSet::default();
            for parsed in self.var_to_parsed_arith.values() {
                if parsed.terms.len() == 2 {
                    let (t0, c0) = (parsed.terms[0].0, parsed.terms[0].1);
                    let (t1, c1) = (parsed.terms[1].0, parsed.terms[1].1);
                    let is_diff = (c0 == Rational64::from_integer(1)
                        && c1 == Rational64::from_integer(-1))
                        || (c0 == Rational64::from_integer(-1)
                            && c1 == Rational64::from_integer(1));
                    if is_diff {
                        candidates.insert(if t0 < t1 { (t0, t1) } else { (t1, t0) });
                    }
                }
            }
            for (a, b) in self.euf.live_diseq_pairs() {
                candidates.insert(if a < b { (a, b) } else { (b, a) });
            }
            // Model-equal shared-term pairs: arithmetic terms the simplex
            // currently assigns the *same* value are candidates for an entailed
            // equality (e.g. two purified UF-argument proxies `v1`, `v2` both
            // pinned to `3`).  Difference-constraint pairs alone miss these, so
            // without this the congruence `f(v1) = f(v2)` never fires.  Group
            // the shared interface by arith value and add same-valued pairs
            // (capped) for the probe.  Sound: `entailed_equal_reason`
            // re-verifies entailment per pair.
            const MAX_MODEL_EQ_PAIRS: usize = 1024;
            let mut by_val: rustc_hash::FxHashMap<Rational64, Vec<TermId>> =
                rustc_hash::FxHashMap::default();
            for &t in self.arith.interface_terms() {
                if let Some(v) = self.arith.value(t) {
                    by_val.entry(v).or_default().push(t);
                }
            }
            let mut added_pairs = 0usize;
            for terms in by_val.values() {
                if added_pairs >= MAX_MODEL_EQ_PAIRS { break; }
                if terms.len() < 2 { continue; }
                'pair: for i in 0..terms.len() {
                    for j in (i + 1)..terms.len() {
                        if added_pairs >= MAX_MODEL_EQ_PAIRS { break 'pair; }
                        let (a, b) = (terms[i], terms[j]);
                        candidates.insert(if a < b { (a, b) } else { (b, a) });
                        added_pairs += 1;
                    }
                }
            }
            let mut merged_any = false;
            for &(x, y) in &candidates {
                let l_node = self.euf.intern(x);
                let r_node = self.euf.intern(y);
                if self.euf.are_equal(l_node, r_node) { continue; }
                let Some(reason) = self.arith.entailed_equal_reason(x, y) else { continue; };
                self.derived_reasons.record(x, reason);
                let _ = self.euf.merge(l_node, r_node, x);
                merged_any = true;
            }
            // cvc5 watchedVariableCannotBeZero: propagate arith-entailed
            // DISEQUALITIES.  For candidate pairs now EUF-merged (by the
            // equality loop above or by congruence), if arith forces x≠y,
            // assert the disequality in EUF → immediate conflict.
            for &(x, y) in &candidates {
                let lx = self.euf.intern(x);
                let ly = self.euf.intern(y);
                if !self.euf.are_equal(lx, ly) { continue; }
                let Some(reason) = self.arith.entailed_disequal_reason(x, y) else { continue; };
                self.derived_reasons.record(x, reason);
                self.euf.assert_diseq(lx, ly, x);
                if let Some(conflict_terms) = self.euf.check_conflicts() {
                    self.statistics.theory_conflicts += 1;
                    self.statistics.conflicts += 1;
                    if self.max_conflicts > 0 && self.statistics.conflicts >= self.max_conflicts {
                        self.resource_exhausted = true;
                        return TheoryCheckResult::Sat;
                    }
                    return self.conflict_from_terms(&conflict_terms);
                }
                merged_any = true;
            }
            if merged_any {
                if let Some(conflict_terms) = self.euf.check_conflicts() {
                    self.statistics.theory_conflicts += 1;
                    self.statistics.conflicts += 1;
                    if self.max_conflicts > 0
                        && self.statistics.conflicts >= self.max_conflicts
                    {
                        self.resource_exhausted = true;
                        return TheoryCheckResult::Sat;
                    }
                    return self.conflict_from_terms(&conflict_terms);
                }
            }
            if !merged_any {
                break;
            }

            // ---- EUF → arithmetic: the new merges may put two terms in one
            //       class with different arithmetic values; assert the equality
            //       and let the tableau refute it. ----
            let mut dedup: FxHashSet<(TermId, TermId)> = FxHashSet::default();
            let eu = self.propagate_euf_equalities_to_arith(&mut dedup);
            if let TheoryCheckResult::Conflict(_) = eu {
                self.statistics.theory_conflicts += 1;
                self.statistics.conflicts += 1;
                if self.max_conflicts > 0
                    && self.statistics.conflicts >= self.max_conflicts
                {
                    self.resource_exhausted = true;
                    return TheoryCheckResult::Sat;
                }
                return eu;
            }
            // `eu == Sat` here; any other variant would be terminal and is
            // covered by returning it directly.
            if !matches!(eu, TheoryCheckResult::Sat) {
                return eu;
            }
            match self.arith.check() {
                Ok(TheoryCheckResultEnum::Sat) => {
                    // continue to the next arith→EUF round
                }
                Ok(TheoryCheckResultEnum::Unsat(conflict_terms)) => {
                    self.statistics.theory_conflicts += 1;
                    self.statistics.conflicts += 1;
                    if self.max_conflicts > 0
                        && self.statistics.conflicts >= self.max_conflicts
                    {
                        self.resource_exhausted = true;
                        return TheoryCheckResult::Sat;
                    }
                    return self.conflict_from_terms(&conflict_terms);
                }
                Ok(_) => {
                    self.resource_exhausted = true;
                    return TheoryCheckResult::Sat;
                }
                Err(_) => {
                    self.resource_exhausted = true;
                    return TheoryCheckResult::Sat;
                }
            }
        }
        // Fixpoint reached (or round bound hit): final model-based
        // disagreement check covers any residual EUF-class/arithmetic-value
        // disagreement the entailed-equality pass did not force.
        self.model_based_combination()
    }

    /// Sound forward theory propagation of comparison atoms (bound propagation).
    ///
    /// Scans every UNASSIGNED comparison atom and, for each whose truth is
    /// forced by the current arithmetic bounds, emits a propagation with a
    /// sound all-true-atom reason.  Resolves `ite` side-conditions
    /// deductively from decided values instead of letting CDCL branch on them.
    fn derive_arith_propagations(&mut self) -> Option<Vec<(Lit, SmallVec<[Lit; 8]>)>> {
        const MAX_ATOMS: usize = 1024;
        if self.var_to_constraint.len() > MAX_ATOMS { return None; }
        let candidates: Vec<(Var, Vec<(TermId, Rational64)>, Rational64, bool, bool)> =
            self.var_to_constraint.iter().filter_map(|(&var, _)| {
                if self.assigned_pol_of(var).is_some() { return None; }
                let parsed = self.var_to_parsed_arith.get(&var)?;
                let (less, strict) = match parsed.constraint_type {
                    ArithConstraintType::Lt => (true, true),
                    ArithConstraintType::Le => (true, false),
                    ArithConstraintType::Gt => (false, true),
                    ArithConstraintType::Ge => (false, false),
                };
                Some((var, parsed.terms.to_vec(), parsed.constant, less, strict))
            }).collect();
        let mut props: Vec<(Lit, SmallVec<[Lit; 8]>)> = Vec::new();
        for (var, terms, constant, less, strict) in candidates {
            let Some((truth, reasons)) = self.arith.comparison_entailed_reason(
                &terms, constant, less, strict,
            ) else { continue; };
            let mut reason_lits: SmallVec<[Lit; 8]> = SmallVec::new();
            let mut ok = true;
            for &r in &reasons {
                match self.term_to_var.get(&r) {
                    Some(&rv) if self.assigned_pol_of(rv) == Some(true) => {
                        reason_lits.push(Lit::pos(rv));
                    }
                    _ => { ok = false; break; }
                }
            }
            if ok {
                props.push((if truth { Lit::pos(var) } else { Lit::neg(var) }, reason_lits));
            }
        }
        if props.is_empty() { None } else { Some(props) }
    }

    /// Add an equality to be shared between theories
    #[allow(dead_code)]
    fn add_shared_equality(&mut self, lhs: TermId, rhs: TermId, reason: Option<TermId>) {
        self.pending_equalities
            .push(EqualityNotification { lhs, rhs, reason });
    }

    /// Sentinel function ID used for array `select(array, index)` in EUF.
    ///
    /// `Spur::into_inner()` always returns a `NonZeroU32` (>= 1), so 0 is safe
    /// to use as a special, collision-free function ID for the built-in select
    /// operation.  By interning `select(a, i)` as `intern_app(term, SELECT_FUNC_ID,
    /// [a_node, i_node])`, the EUF congruence closure engine treats select like any
    /// other binary function application and will automatically derive
    /// `select(a, x) = select(a, y)` whenever `x = y` is merged.
    const SELECT_FUNC_ID: u32 = 0;

    /// Intern a term into EUF, using `intern_app` for Apply terms and
    /// `TermKind::Select` terms so that congruence closure works correctly.
    ///
    /// Plain `intern` creates opaque nodes with no function-symbol or argument
    /// information, which prevents the congruence closure algorithm from firing
    /// when argument classes are merged.
    ///
    /// `Select(array, index)` is treated as a binary function application with
    /// the special function ID `SELECT_FUNC_ID` (0).  This ensures that when
    /// `x = y` causes their EUF nodes to merge, congruence automatically
    /// derives `select(a, x) = select(a, y)`, which in turn allows further
    /// congruence steps (e.g., `f(select(a,x)) = f(select(a,y))`).
    ///
    /// Iterative: `Apply` arguments and `Select` operands are interned through
    /// an explicit frame stack (post-order, left to right — the recursive
    /// order), so operand nesting depth cannot overflow the native call
    /// stack.  `euf.term_to_node` remains the cross-call memo, so shared
    /// sub-terms of the hash-consed DAG are interned once.
    #[allow(dead_code)]
    fn intern_term_deep(&mut self, term: TermId, manager: &TermManager) -> u32 {
        let mut frames: Vec<InternFrame> = Vec::new();
        let mut current = term;
        'open: loop {
            // Intern `current`, descending into application operands first.
            let mut value: u32 = loop {
                if let Some(idx) = self.euf.term_to_node(current) {
                    break idx;
                }
                match Self::intern_operands(current, manager) {
                    Some((func_id, operands)) => match operands.first().copied() {
                        Some(first) => {
                            frames.push(InternFrame {
                                term: current,
                                func_id,
                                operands,
                                next: 1,
                                nodes: SmallVec::new(),
                            });
                            current = first;
                        }
                        None => {
                            break self.euf.intern_app(
                                current,
                                func_id,
                                SmallVec::<[u32; 4]>::new(),
                            );
                        }
                    },
                    None => break self.intern_leaf_deep(current, manager),
                }
            };

            // Hand the finished operand node to the innermost application.
            loop {
                let Some(mut frame) = frames.pop() else {
                    return value;
                };
                frame.nodes.push(value);
                if let Some(&child) = frame.operands.get(frame.next) {
                    frame.next += 1;
                    frames.push(frame);
                    current = child;
                    continue 'open;
                }
                value = self.euf.intern_app(frame.term, frame.func_id, frame.nodes);
            }
        }
    }

    /// The application structure of `term` for EUF interning: `Apply` uses its
    /// function symbol, `Select(array, index)` is a binary application of the
    /// sentinel [`Self::SELECT_FUNC_ID`] so that congruence closure fires when
    /// the index (or array) arguments become equal.  Everything else is a leaf.
    fn intern_operands(
        term: TermId,
        manager: &TermManager,
    ) -> Option<(u32, SmallVec<[TermId; 4]>)> {
        match manager.get(term).map(|t| &t.kind) {
            Some(TermKind::Apply { func, args, .. }) => {
                Some((func.into_inner().get(), args.clone()))
            }
            Some(TermKind::Select(array, index)) => Some((
                Self::SELECT_FUNC_ID,
                SmallVec::from_slice(&[*array, *index]),
            )),
            _ => None,
        }
    }

    /// Intern a non-application term for [`Self::intern_term_deep`]: integer
    /// constants get a canonical node plus pairwise disequalities, everything
    /// else a plain opaque node.
    fn intern_leaf_deep(&mut self, term: TermId, manager: &TermManager) -> u32 {
        if let Some(t) = manager.get(term) {
            if let TermKind::IntConst(n) = &t.kind {
                // Intern the integer constant as an EUF node and maintain
                // pairwise disequalities between *distinct* integer values.
                //
                // EUF has no built-in notion of numeric inequality.  Without
                // explicit disequality edges, a congruence chain equating a
                // node merged with `10` and one merged with `20` would not
                // produce a conflict.  We therefore assert `10 ≠ 20` etc.
                //
                // Performance: we track one *canonical* EUF node per unique
                // integer value.  When the same value appears again (e.g. as a
                // fresh TermId created during MBQI instantiation) we merge the
                // new node into the canonical one.  This bounds the number of
                // entries — and therefore of pairwise disequality edges — to the
                // number of *distinct* literal values in the formula, preventing
                // the O(n²) blowup that arises when MBQI creates many fresh
                // TermIds for the same integer literal across iterations.
                if let Some(val) = n.to_i64() {
                    let new_node = self.euf.intern(term);
                    // Both the merge and the disequalities below carry `term`
                    // as their reason and `term` names no literal; they are
                    // true in every model.  Declaring that keeps
                    // `terms_to_conflict_clause` able to distinguish "omitted
                    // because tautological" from "justification lost".
                    self.tautological_reasons.insert(term);
                    if let Some(&canonical) = self.interned_int_constants.get(&val) {
                        // This value already has a canonical node.  Merge the
                        // new term's node into it so that congruence closure
                        // treats them as equal (they represent the same number).
                        // Ignore merge errors: the nodes may already be in the
                        // same class if this term was interned before.
                        let _ = self.euf.merge(new_node, canonical, term);
                        return canonical;
                    }
                    // First time we see this value: register the canonical node
                    // and assert disequality against every other distinct value.
                    let diseq_targets: Vec<u32> =
                        self.interned_int_constants.values().copied().collect();
                    for other_node in diseq_targets {
                        self.euf.assert_diseq(new_node, other_node, term);
                    }
                    self.interned_int_constants.insert(val, new_node);
                    return new_node;
                }
                // BigInt too large for i64 -- fall through to plain intern.
            }
        }
        self.euf.intern(term)
    }

    /// Intern a term into EUF for congruence closure, using `intern_app` for
    /// Apply and Select terms so that congruence fires correctly.
    ///
    /// Unlike `intern_term_deep`, this variant does NOT add IntConst pairwise
    /// disequality edges.  Those edges are necessary for conflict detection when
    /// numeric constants are compared via the EUF layer, but they cause spurious
    /// UNSAT in SAT cases where the ArithSolver is the one tracking numeric
    /// inequalities.  This function is used exclusively inside
    /// `process_constraint` for equality/disequality assertions so that
    /// `f(a)=f(b)` congruence works while arithmetic stays in the ArithSolver.
    ///
    /// Iterative: `Apply` arguments and `Select` operands are interned through
    /// an explicit [`InternFrame`] stack in post-order, left to right — exactly
    /// the order the recursive version used, which matters because
    /// `intern_app` assigns node indices in creation order.  Operand nesting
    /// depth is therefore bounded by memory rather than by the native call
    /// stack.  `euf.term_to_node` remains the memo, so shared sub-terms of the
    /// hash-consed DAG are interned once.
    fn intern_term_for_congruence(&mut self, term: TermId, manager: &TermManager) -> u32 {
        let mut frames: Vec<InternFrame> = Vec::new();
        let mut current = term;
        'open: loop {
            // Intern `current`, descending into application operands first.
            let mut value: u32 = loop {
                if let Some(idx) = self.euf.term_to_node(current) {
                    break idx;
                }
                match Self::intern_operands(current, manager) {
                    Some((func_id, operands)) => match operands.first().copied() {
                        Some(first) => {
                            frames.push(InternFrame {
                                term: current,
                                func_id,
                                operands,
                                next: 1,
                                nodes: SmallVec::new(),
                            });
                            current = first;
                        }
                        None => {
                            break self.euf.intern_app(
                                current,
                                func_id,
                                SmallVec::<[u32; 4]>::new(),
                            );
                        }
                    },
                    None => break self.intern_leaf_for_congruence(current, manager),
                }
            };

            // Hand the finished operand node to the innermost application.
            loop {
                let Some(mut frame) = frames.pop() else {
                    return value;
                };
                frame.nodes.push(value);
                if let Some(&child) = frame.operands.get(frame.next) {
                    frame.next += 1;
                    frames.push(frame);
                    current = child;
                    continue 'open;
                }
                value = self.euf.intern_app(frame.term, frame.func_id, frame.nodes);
            }
        }
    }

    /// Intern a non-application term for [`Self::intern_term_for_congruence`]:
    /// bit-vector constants get a canonical node plus pairwise disequalities
    /// against the other distinct constants of the same width, everything else
    /// a plain opaque node.  Unlike [`Self::intern_leaf_deep`], integer
    /// constants get **no** disequality edges (see the caller's docs).
    fn intern_leaf_for_congruence(&mut self, term: TermId, manager: &TermManager) -> u32 {
        if let Some(t) = manager.get(term) {
            if let TermKind::BitVecConst { value, width } = &t.kind {
                // Register the BV constant as an EUF node and maintain pairwise
                // disequalities between *distinct* same-width constant values.
                //
                // EUF has no built-in notion that two different bit-vector
                // literals are unequal.  Without explicit disequality edges, a
                // congruence chain that equates a node merged with `#x00` and one
                // merged with `#x01` (e.g. `g(a)=#x00`, `g(b)=#x01`, `a=b`) would
                // not produce a conflict.  We therefore assert `#x00 ≠ #x01` etc.
                //
                // As with `interned_int_constants`, we keep one canonical EUF
                // node per distinct `(value, width)` pair: when the same value
                // reappears (a fresh TermId) we merge it into the canonical node,
                // bounding the number of pairwise edges by the count of distinct
                // BV literals rather than the total number of term IDs.
                //
                // The key carries every limb of the value.  Truncating it to
                // the low 64 bits made `0` and `2^64` the *same* key at width
                // 128, so the two constants were merged into one EUF class —
                // and the merge was recorded as tautological, which is exactly
                // what it was not.  `(distinct (g a) (g b))` over those two
                // constants was then reported `unsat`.
                let key = (
                    value.iter_u64_digits().collect::<SmallVec<[u64; 2]>>(),
                    *width,
                );
                let new_node = self.euf.intern(term);
                // Every edge asserted from here carries `term` as its reason
                // and `term` names no literal: two ids for the same constant
                // really are equal and two distinct constants really are
                // unequal, in every model.  Declare that so a conflict clause
                // can omit it *knowingly*.
                self.tautological_reasons.insert(term);
                if let Some(&canonical) = self.interned_bv_constants.get(&key) {
                    let _ = self.euf.merge(new_node, canonical, term);
                    return canonical;
                }
                // First time we see this value: assert disequality against every
                // other distinct constant of the SAME width (different widths are
                // different sorts and are never merged), then register it.
                let diseq_targets: Vec<u32> = self
                    .interned_bv_constants
                    .iter()
                    .filter_map(|(&(_, w), &node)| (w == *width).then_some(node))
                    .collect();
                for other_node in diseq_targets {
                    self.euf.assert_diseq(new_node, other_node, term);
                }
                self.interned_bv_constants.insert(key, new_node);
                return new_node;
            }
        }
        self.euf.intern(term)
    }

    /// Ensure canonical EUF nodes for Boolean true/false exist, with a
    /// disequality between them.  Returns `(true_node, false_node)`.
    fn ensure_bool_nodes(&mut self) -> (u32, u32) {
        if let (Some(t), Some(f)) = (self.bool_true_node, self.bool_false_node) {
            return (t, f);
        }
        // Use sentinel TermIds that will never collide with real terms.
        // TermId(u32::MAX) and TermId(u32::MAX - 1) are reserved for this.
        let true_term = TermId::new(u32::MAX);
        let false_term = TermId::new(u32::MAX - 1);
        let t = self.euf.intern(true_term);
        let f = self.euf.intern(false_term);
        // `true ≠ false` holds in every model and rests on no literal.
        self.tautological_reasons.insert(true_term);
        self.euf.assert_diseq(t, f, true_term);
        self.bool_true_node = Some(t);
        self.bool_false_node = Some(f);
        (t, f)
    }

    /// Look up the term ID for a SAT variable.
    /// Returns a sentinel zero TermId if not found.
    #[inline]
    fn term_for_var(&self, var: Var) -> TermId {
        self.var_to_term
            .get(var.index())
            .copied()
            .unwrap_or_else(|| TermId::new(0))
    }

    /// Register every shared term of a parsed arithmetic constraint in EUF.
    ///
    /// `intern_term_for_congruence` descends only through the *arguments* of an
    /// application, so an application buried inside an arithmetic expression —
    /// the `f(a)` of `(+ (f a) b)` — never reached congruence closure at all.
    /// With `a = b` asserted, `f(a) = f(b)` was therefore never derived and
    /// `(= a b) ∧ (> (+ (f a) b) (+ (f b) a))` came back `sat`, a model that
    /// does not exist.  The same hole swallowed `(select arr i)` under `(+ …)`.
    ///
    /// The linear parser has already reduced the expression to exactly the
    /// opaque terms the tableau reasons about, so interning those — and only
    /// those — is both necessary and sufficient: after it, the two solvers share
    /// the same atoms and every congruence the tableau could use is available.
    fn intern_arith_shared_terms(&mut self, var: Var, manager: &TermManager) {
        let Some(parsed) = self.var_to_parsed_arith.get(&var) else {
            return;
        };
        // Copy the term ids out so the map borrow ends before the `&mut self`
        // interning calls below.
        let shared: SmallVec<[TermId; 4]> = parsed.terms.iter().map(|&(t, _c)| t).collect();
        for term in shared {
            self.intern_term_for_congruence(term, manager);
        }
    }

    /// Look up the BV bit-width of a term from its sort, if it has a BV sort.
    fn bv_width_of(&self, term: TermId, manager: &TermManager) -> Option<u32> {
        manager
            .get(term)
            .and_then(|t| manager.sorts.get(t.sort))
            .and_then(|s| s.bitvec_width())
    }

    /// Bit-blast both operands of a BV constraint into the embedded SAT solver.
    ///
    /// Each side is encoded recursively; a bare leaf that the recursive encoder
    /// cannot handle falls back to a fresh BV variable of the operand's width.
    /// Returns `true` if both operands are BV-sorted with equal width (so that
    /// `assert_eq` / `assert_neq` may be called safely), `false` otherwise.
    fn bit_blast_bv_pair(&mut self, lhs: TermId, rhs: TermId, manager: &TermManager) -> bool {
        let (lw, rw) = match (
            self.bv_width_of(lhs, manager),
            self.bv_width_of(rhs, manager),
        ) {
            (Some(lw), Some(rw)) if lw == rw => (lw, rw),
            _ => return false,
        };
        let mut encoded: FxHashSet<TermId> = FxHashSet::default();
        if !encode_bv_term_recursive(self.bv, lhs, manager, &mut encoded) {
            self.bv.new_bv(lhs, lw);
        }
        if !encode_bv_term_recursive(self.bv, rhs, manager, &mut encoded) {
            self.bv.new_bv(rhs, rw);
        }
        true
    }

    /// Run the embedded BV SAT check after the caller has asserted a constraint.
    ///
    /// Records `constraint_term` so the conflict clause is non-empty, then
    /// returns `Some(Conflict(..))` if the embedded solver reports UNSAT and
    /// `None` otherwise (so the caller falls through to its conservative path).
    ///
    /// `operands` are the two sides of the atom just asserted.  When the check
    /// comes back SAT they are handed to [`debug_verify_bv_circuits`], the
    /// debug-only model-validity net: every bit-blasted node under them must
    /// reproduce its own operation concretely on the model the solver just
    /// found.  That is the check which distinguishes "the search is right" from
    /// "the circuit is wrong", and it costs nothing in release builds.
    fn bv_run_check(
        &mut self,
        constraint_term: TermId,
        operands: (TermId, TermId),
        manager: &TermManager,
    ) -> Option<TheoryCheckResult> {
        use oxiz_theories::Theory;
        use oxiz_theories::TheoryCheckResult as TheoryCheckResultEnum;
        self.bv.record_constraint_term(constraint_term);
        match self.bv.check() {
            Ok(TheoryCheckResultEnum::Unsat(conflict_terms)) => {
                Some(self.conflict_from_terms(&conflict_terms))
            }
            Ok(TheoryCheckResultEnum::Sat) => {
                debug_verify_bv_circuits(self.bv, operands.0, manager);
                debug_verify_bv_circuits(self.bv, operands.1, manager);
                None
            }
            _ => None,
        }
    }

    /// Bit-blast `lhs`/`rhs`, assert `lhs != b` at the bit level, and check.
    ///
    /// Returns `Some(Conflict(..))` on a detected BV theory conflict, `None`
    /// otherwise (including when the operands are not equal-width BV terms).
    fn bv_check_neq(
        &mut self,
        lhs: TermId,
        rhs: TermId,
        constraint_term: TermId,
        manager: &TermManager,
    ) -> Option<TheoryCheckResult> {
        if !self.bit_blast_bv_pair(lhs, rhs, manager) {
            return None;
        }
        self.bv.assert_neq(lhs, rhs);
        self.bv_run_check(constraint_term, (lhs, rhs), manager)
    }

    /// Bit-blast `lhs`/`rhs`, assert `lhs = b` at the bit level, and check.
    ///
    /// Returns `Some(Conflict(..))` on a detected BV theory conflict, `None`
    /// otherwise (including when the operands are not equal-width BV terms).
    fn bv_check_eq(
        &mut self,
        lhs: TermId,
        rhs: TermId,
        constraint_term: TermId,
        manager: &TermManager,
    ) -> Option<TheoryCheckResult> {
        if !self.bit_blast_bv_pair(lhs, rhs, manager) {
            return None;
        }
        self.bv.assert_eq(lhs, rhs);
        self.bv_run_check(constraint_term, (lhs, rhs), manager)
    }

    /// Process a theory constraint
    fn process_constraint(
        &mut self,
        var: Var,
        constraint: Constraint,
        is_positive: bool,
        manager: &TermManager,
    ) -> TheoryCheckResult {
        match constraint {
            Constraint::Eq(lhs, rhs) => {
                if is_positive {
                    // Positive assignment: a = b, tell EUF to merge.
                    // Use the constraint term (which has a SAT variable) as the
                    // merge reason so that conflict clause generation can find it
                    // in term_to_var.
                    let constraint_term = self.term_for_var(var);
                    // Use intern_term_for_congruence so that Apply/Select terms are
                    // registered with intern_app, enabling EUF congruence closure
                    // (e.g., a=b → f(a)=f(b)).  This variant does NOT add IntConst
                    // pairwise disequality edges, keeping arithmetic reasoning in the
                    // ArithSolver and avoiding spurious UNSAT in SAT cases.
                    let lhs_node = self.intern_term_for_congruence(lhs, manager);
                    let rhs_node = self.intern_term_for_congruence(rhs, manager);
                    if let Err(_e) = self.euf.merge(lhs_node, rhs_node, constraint_term) {
                        // Merge failed - should not happen in normal operation
                        return TheoryCheckResult::Sat;
                    }

                    // Check for immediate conflicts
                    if let Some(conflict_terms) = self.euf.check_conflicts() {
                        // Convert term IDs to literals for conflict clause
                        return self.conflict_from_terms(&conflict_terms);
                    }

                    // For arithmetic equalities, also send to ArithSolver
                    // Use pre-parsed constraint if available
                    self.intern_arith_shared_terms(var, manager);
                    if let Some(parsed) = self.var_to_parsed_arith.get(&var) {
                        let terms: Vec<(TermId, Rational64)> =
                            parsed.terms.iter().copied().collect();
                        let constant = parsed.constant;
                        let reason = parsed.reason_term;

                        // For equality, use assert_eq which has GCD-based infeasibility detection
                        // This is critical for LIA: e.g., 2x + 2y = 7 is unsatisfiable because
                        // gcd(2,2) = 2 doesn't divide 7
                        self.arith.assert_eq(&terms, constant, reason);

                        // Check ArithSolver for conflicts
                        use oxiz_theories::Theory;
                        use oxiz_theories::TheoryCheckResult as TheoryCheckResultEnum;
                        if let Ok(TheoryCheckResultEnum::Unsat(conflict_terms)) = self.arith.check()
                        {
                            return self.conflict_from_terms(&conflict_terms);
                        }
                    }

                    // For bitvector equalities, also send to BvSolver
                    // Handle variables, constants, and BV operations
                    // Check if terms have BV sort (not just if they're in bv_terms)
                    let lhs_is_bv = manager
                        .get(lhs)
                        .and_then(|t| manager.sorts.get(t.sort))
                        .is_some_and(|s| s.is_bitvec());
                    let rhs_is_bv = manager
                        .get(rhs)
                        .and_then(|t| manager.sorts.get(t.sort))
                        .is_some_and(|s| s.is_bitvec());

                    // Bit-blast the equality through the *general* recursive
                    // encoder rather than a hand-rolled case analysis over
                    // operand shapes.
                    //
                    // The previous implementation dispatched on a whitelist of
                    // "BV operation" kinds that listed only the arithmetic and
                    // bitwise ops (`bvadd`/`bvmul`/`bvand`/`bvudiv`/...).  Every
                    // BV term whose head was outside that list — `concat`,
                    // `extract`, the shifts `bvshl`/`bvlshr`/`bvashr`, and any
                    // BV-sorted `ite` (which is what `bvsmod`, `bvcomp`,
                    // `rotate_*`, `zero_extend`/`sign_extend` lower to) — matched
                    // none of the cases, left `did_assert` false, and so was
                    // never asserted into the embedded SAT solver at all.  The
                    // atom then survived as a *free boolean*, and the solver
                    // happily reported `sat` with a model that does not satisfy
                    // it (`(= (concat #b000000 w) #x10)` answered `sat, w = #b00`
                    // where every model is impossible).
                    //
                    // `bv_check_eq` bit-blasts both sides with
                    // `encode_bv_term_recursive` — which handles the full BV
                    // TermKind set and pins `BitVecConst` leaves to their concrete
                    // bits — asserts the bit-level equality and consults the
                    // embedded SAT solver.  It is the same path the negative-`Eq`
                    // and `Diseq` branches already take, so the four polarities of
                    // a BV (dis)equality now share one encoding.
                    if lhs_is_bv
                        && rhs_is_bv
                        && let Some(result) = self.bv_check_eq(lhs, rhs, constraint_term, manager)
                    {
                        return result;
                    }
                } else {
                    // Negative assignment: a != b, tell EUF about disequality.
                    // Use the constraint term as the reason (it has a SAT variable).
                    let constraint_term = self.term_for_var(var);
                    let lhs_node = self.intern_term_for_congruence(lhs, manager);
                    let rhs_node = self.intern_term_for_congruence(rhs, manager);
                    self.euf.assert_diseq(lhs_node, rhs_node, constraint_term);

                    // Check for immediate conflicts (if a = b was already derived)
                    if let Some(conflict_terms) = self.euf.check_conflicts() {
                        return self.conflict_from_terms(&conflict_terms);
                    }

                    // For bit-vector operands also send the disequality to the BV
                    // solver.  Mirrors the positive branch: fully bit-blast both
                    // operands, assert `a != b` at the bit level, then consult the
                    // embedded SAT solver.  This catches e.g. `not(= x x)` and
                    // `not(= (bvadd x y) (bvadd y x))`, which the EUF layer alone
                    // cannot refute (it has no bit-level arithmetic semantics).
                    if let Some(result) = self.bv_check_neq(lhs, rhs, constraint_term, manager) {
                        return result;
                    }
                }
            }
            Constraint::Diseq(lhs, rhs) => {
                if is_positive {
                    // Positive assignment: a != b.
                    // Use the constraint term as the reason for EUF disequality.
                    let constraint_term = self.term_for_var(var);
                    let lhs_node = self.intern_term_for_congruence(lhs, manager);
                    let rhs_node = self.intern_term_for_congruence(rhs, manager);
                    self.euf.assert_diseq(lhs_node, rhs_node, constraint_term);

                    if let Some(conflict_terms) = self.euf.check_conflicts() {
                        return self.conflict_from_terms(&conflict_terms);
                    }

                    // BV disequality (e.g. `(distinct x x)`): bit-blast and assert
                    // `a != b`, mirroring the negative-Eq branch.
                    if let Some(result) = self.bv_check_neq(lhs, rhs, constraint_term, manager) {
                        return result;
                    }
                } else {
                    // Negative assignment: ~(a != b) means a = b.
                    // Use the constraint term as the merge reason.
                    let constraint_term = self.term_for_var(var);
                    let lhs_node = self.intern_term_for_congruence(lhs, manager);
                    let rhs_node = self.intern_term_for_congruence(rhs, manager);
                    if let Err(_e) = self.euf.merge(lhs_node, rhs_node, constraint_term) {
                        return TheoryCheckResult::Sat;
                    }

                    if let Some(conflict_terms) = self.euf.check_conflicts() {
                        return self.conflict_from_terms(&conflict_terms);
                    }

                    // BV equality forced by `~(a != b)`: bit-blast and assert `a = b`.
                    if let Some(result) = self.bv_check_eq(lhs, rhs, constraint_term, manager) {
                        return result;
                    }
                }
            }
            // Arithmetic constraints - use parsed linear expressions
            Constraint::Lt(lhs, rhs)
            | Constraint::Le(lhs, rhs)
            | Constraint::Gt(lhs, rhs)
            | Constraint::Ge(lhs, rhs) => {
                // Intern both sides into EUF with congruence support so that
                // Apply/Select terms are registered for congruence closure.
                self.intern_term_for_congruence(lhs, manager);
                self.intern_term_for_congruence(rhs, manager);
                self.intern_arith_shared_terms(var, manager);

                // Check if this is a BV comparison.  Detect it from the operand
                // *sorts*, exactly as the `Eq` arm above does — `bv_terms` only
                // holds BV-sorted *variables*, so keying off it silently skipped
                // every comparison whose sides are both compound, such as
                // `(bvugt (bvxor x x) (bvand #xff x))`, leaving the atom as a
                // free boolean and answering a spurious `sat`.
                let is_bv_sorted = |tid: TermId| -> bool {
                    manager
                        .get(tid)
                        .and_then(|t| manager.sorts.get(t.sort))
                        .is_some_and(|s| s.is_bitvec())
                };
                let lhs_is_bv = is_bv_sorted(lhs);
                let rhs_is_bv = is_bv_sorted(rhs);

                // Handle BV comparisons
                if lhs_is_bv || rhs_is_bv {
                    // Get BV width.  Both operands must agree: `BvSolver`'s
                    // comparison asserts require equal-width operands, and
                    // bit-blasting each side at its *own* declared width (which
                    // `encode_bv_term_recursive` does) would otherwise hand it a
                    // mismatched pair for an ill-sorted input term.  A
                    // width-mismatched comparison is not a well-sorted SMT-LIB
                    // atom, so leaving it to the remaining (boolean) handling is
                    // the correct conservative response.
                    let bv_width_of = |tid: TermId| -> Option<u32> {
                        manager
                            .get(tid)
                            .and_then(|t| manager.sorts.get(t.sort).and_then(|s| s.bitvec_width()))
                    };
                    let width = match (bv_width_of(lhs), bv_width_of(rhs)) {
                        (Some(lw), Some(rw)) if lw == rw => Some(lw),
                        _ => None,
                    };

                    if let Some(width) = width {
                        // Bit-blast both operands *with constant bits pinned*.
                        //
                        // `new_bv` alone allocates a fresh, completely
                        // unconstrained bit-vector for whatever term it is
                        // handed — including `BitVecConst` operands.  A
                        // comparison such as `(bvult x #b00000000)` then reads
                        // as `x <u c` for an arbitrary `c`, which is trivially
                        // satisfiable, so the BV solver could never refute the
                        // always-false strict comparisons (`t <u 0`,
                        // `t <s INT_MIN`, `MAX <u t`, ...).  Reference: Z3's
                        // bv_rewriter.cpp folds those atoms to `false`; here the
                        // equivalent refutation comes from the bit-blasted
                        // circuit, which only works once the literal operand is
                        // pinned to its concrete bits.
                        //
                        // `encode_bv_term_recursive` pins `BitVecConst` leaves
                        // and bit-blasts compound BV structure (`bvadd`,
                        // `bvand`, extract, ...) that appears under a
                        // comparison; `new_bv` remains the fallback for term
                        // shapes it does not model (e.g. an `Apply` of an
                        // uninterpreted function returning a bit-vector), where
                        // a free bit-vector is the correct abstraction.
                        let mut bv_encoded: FxHashSet<TermId> = FxHashSet::default();
                        if !encode_bv_term_recursive(self.bv, lhs, manager, &mut bv_encoded) {
                            self.bv.new_bv(lhs, width);
                        }
                        if !encode_bv_term_recursive(self.bv, rhs, manager, &mut bv_encoded) {
                            self.bv.new_bv(rhs, width);
                        }

                        // Derive signedness from the original TermKind stored for
                        // the SAT variable.  Both BvSlt and BvUlt encode to
                        // Constraint::Lt(lhs, rhs) during formula encoding (encode.rs),
                        // so the distinction is only recoverable by inspecting the term
                        // that the SAT variable was created for.
                        let constraint_term_id = self.term_for_var(var);
                        let is_signed = manager.get(constraint_term_id).is_some_and(|t| {
                            matches!(t.kind, TermKind::BvSlt(_, _) | TermKind::BvSle(_, _))
                        });

                        if is_positive {
                            // Positive assignment: constraint holds
                            match constraint {
                                Constraint::Lt(a, b) => {
                                    if is_signed {
                                        self.bv.assert_slt(a, b);
                                    } else {
                                        self.bv.assert_ult(a, b);
                                    }
                                }
                                Constraint::Le(a, b) if is_signed => {
                                    self.bv.assert_sle(a, b);
                                }
                                Constraint::Le(a, b) => {
                                    // Unsigned a <= b ≡ NOT(b <u a).
                                    self.bv.assert_ule(a, b);
                                }
                                _ => {}
                            }
                        } else {
                            // Negated assignment: the negation of the comparator
                            // holds.  By totality of BV orders the negation is the
                            // swapped non-strict / strict comparator:
                            //   ¬(a <u  b) ≡ b <=u a   ¬(a <=u b) ≡ b <u  a
                            //   ¬(a <s  b) ≡ b <=s a   ¬(a <=s b) ≡ b <s  a
                            match constraint {
                                Constraint::Lt(a, b) => {
                                    if is_signed {
                                        self.bv.assert_sle(b, a);
                                    } else {
                                        self.bv.assert_ule(b, a);
                                    }
                                }
                                Constraint::Le(a, b) => {
                                    if is_signed {
                                        self.bv.assert_slt(b, a);
                                    } else {
                                        self.bv.assert_ult(b, a);
                                    }
                                }
                                _ => {}
                            }
                        }

                        // Check BV solver for conflicts.  Routed through
                        // `bv_run_check` so the comparison path shares the
                        // (dis)equality path's debug-only model-validity net.
                        let constraint_term = self.term_for_var(var);
                        if let Some(result) =
                            self.bv_run_check(constraint_term, (lhs, rhs), manager)
                        {
                            return result;
                        }
                    }
                }

                // Look up the pre-parsed linear constraint for arithmetic
                if let Some(parsed) = self.var_to_parsed_arith.get(&var) {
                    // Add constraint to ArithSolver
                    let terms: Vec<(TermId, Rational64)> = parsed.terms.iter().copied().collect();
                    let reason = parsed.reason_term;
                    let constant = parsed.constant;

                    if is_positive {
                        // Positive assignment: constraint holds
                        match parsed.constraint_type {
                            ArithConstraintType::Lt => {
                                // lhs - rhs < 0, i.e., sum of terms < constant
                                self.arith.assert_lt(&terms, constant, reason);
                            }
                            ArithConstraintType::Le => {
                                // lhs - rhs <= 0
                                self.arith.assert_le(&terms, constant, reason);
                            }
                            ArithConstraintType::Gt => {
                                // lhs - rhs > 0, i.e., sum of terms > constant
                                self.arith.assert_gt(&terms, constant, reason);
                            }
                            ArithConstraintType::Ge => {
                                // lhs - rhs >= 0
                                self.arith.assert_ge(&terms, constant, reason);
                            }
                        }
                    } else {
                        // Negative assignment: negation of constraint holds
                        // ~(a < b) => a >= b
                        // ~(a <= b) => a > b
                        // ~(a > b) => a <= b
                        // ~(a >= b) => a < b
                        match parsed.constraint_type {
                            ArithConstraintType::Lt => {
                                // ~(lhs < rhs) => lhs >= rhs
                                self.arith.assert_ge(&terms, constant, reason);
                            }
                            ArithConstraintType::Le => {
                                // ~(lhs <= rhs) => lhs > rhs
                                self.arith.assert_gt(&terms, constant, reason);
                            }
                            ArithConstraintType::Gt => {
                                // ~(lhs > rhs) => lhs <= rhs
                                self.arith.assert_le(&terms, constant, reason);
                            }
                            ArithConstraintType::Ge => {
                                // ~(lhs >= rhs) => lhs < rhs
                                self.arith.assert_lt(&terms, constant, reason);
                            }
                        }
                    }

                    // Check ArithSolver for conflicts
                    use oxiz_theories::Theory;
                    use oxiz_theories::TheoryCheckResult as TheoryCheckResultEnum;
                    let arith_result = self.arith.check();
                    match arith_result {
                        Ok(TheoryCheckResultEnum::Unsat(conflict_terms)) => {
                            return self.conflict_from_terms(&conflict_terms);
                        }
                        Ok(TheoryCheckResultEnum::Sat) => {}
                        other => {
                            let _ = other;
                        }
                    }
                }
            }
            Constraint::BoolApp(app_term) => {
                // Bool-valued function application (e.g., `t(m)`).
                // Intern the application in EUF so that congruence closure
                // can fire.  Then merge its EUF node with the canonical
                // true or false node depending on the SAT assignment.
                let app_node = self.intern_term_for_congruence(app_term, manager);
                let (true_node, false_node) = self.ensure_bool_nodes();
                let merge_target = if is_positive { true_node } else { false_node };
                let constraint_term = self.term_for_var(var);
                if let Err(_e) = self.euf.merge(app_node, merge_target, constraint_term) {
                    // Merge error (should not happen in normal operation)
                    return TheoryCheckResult::Sat;
                }

                // Check for immediate conflicts
                if let Some(conflict_terms) = self.euf.check_conflicts() {
                    return self.conflict_from_terms(&conflict_terms);
                }
            }
        }
        TheoryCheckResult::Sat
    }
}

impl TheoryCallback for TheoryManager<'_> {
    fn on_assignment(&mut self, lit: Lit) -> TheoryCheckResult {
        let var = lit.var();
        let is_positive = !lit.is_neg();

        // Record the atom's current polarity so conflict clauses can emit the
        // correct (currently-false) literal for this variable, and the level it
        // holds at so `full_assignment_conflict_clause` never names a literal
        // the SAT core has since unassigned.
        self.assigned_polarity.insert(var, is_positive);
        self.assigned_level.insert(var, self.current_level);

        // Mirror the assignment into the embedded BV solver's boolean-node
        // cache.  A BV-sorted `ite` whose selector is a bare boolean variable
        // gets a *free* variable inside that solver, so without this link the
        // embedded search can take the branch the outer search has ruled out
        // and both halves look consistent — a false `sat` for
        // `(= (ite c #x01 #x02) x) ∧ ¬c ∧ (= x #x01)`.  Only variables that
        // actually carry a term are replayed: `term_for_var`'s `TermId::new(0)`
        // fallback would otherwise pin an unrelated term.
        if let Some(term) = self.var_to_term.get(var.index()).copied() {
            self.bv.assert_bool_value(term, is_positive);
        }

        // Enforce the wall-clock timeout mid-search.  Suppressing conflicts
        // (returning Sat) drives the search to a full assignment quickly; the
        // `resource_exhausted` flag makes the owning solver answer `Unknown`.
        if self.timed_out() {
            self.resource_exhausted = true;
            return TheoryCheckResult::Sat;
        }

        // Track propagation
        self.statistics.propagations += 1;

        // In lazy mode, just collect assignments for batch processing
        if self.theory_mode == TheoryMode::Lazy {
            // Check if this variable has a theory constraint
            if self.var_to_constraint.contains_key(&var) {
                self.pending_assignments.push((lit, is_positive));
            }
            return TheoryCheckResult::Sat;
        }

        // Eager mode: process immediately
        // Check if this variable has a theory constraint
        let Some(constraint) = self.var_to_constraint.get(&var).cloned() else {
            return TheoryCheckResult::Sat;
        };

        // Shadow-trail bookkeeping + in-place-flip detection.
        //
        // If the SAT core has assigned this variable before (and not yet
        // backtracked past it) with the OPPOSITE polarity, it has overwritten
        // its own trail — a wrong assertion-level bug in conflict analysis.  The
        // incremental theory state still holds the old polarity's assertions and
        // cannot be surgically undone, so we replace the trail entry and rebuild
        // theory state from the corrected trail.  A re-assignment with the SAME
        // polarity is an idempotent re-send after a backtrack; it falls through
        // to the normal (re)processing path, preserving pre-existing behaviour.
        match self.trail_index.get(&var).copied() {
            // In-place polarity flip by the SAT core (a wrong assertion-level
            // result from its conflict analysis).  Rebuild theory state from the
            // corrected, deduplicated trail so no stale over-constraint from the
            // old polarity manufactures a spurious conflict (the wrong-UNSAT on
            // satisfiable disjunctive LIA chains).  Any residual unsoundness the
            // corrupted SAT trail could still produce (a full assignment
            // violating a Boolean clause the theory cannot see) is caught
            // downstream by the model-verification gate in `Solver::check`.
            //
            // Scope: the rebuild covers the EUF and arithmetic solvers, so we
            // engage it only when the problem has no bit-vector content.  The BV
            // solver's bit-blasted circuits are rebuilt from scratch on every
            // `check` (see `mod.rs`) and its incremental push/pop already handles
            // flips soundly; resetting and replaying it mid-search would instead
            // corrupt its embedded SAT state.  BV problems therefore retain the
            // existing (correct) incremental behaviour.
            Some(idx)
                if self.assignment_trail[idx].is_positive != is_positive
                    && self.bv_terms.is_empty() =>
            {
                self.assignment_trail[idx] = TrailAtom {
                    var,
                    is_positive,
                    level: self.current_level,
                };
                self.processed_count += 1;
                self.statistics.theory_propagations += 1;

                // Process the flipped literal against the current (stale) state
                // first.  If it stays consistent, keep that result — the extra
                // over-constraint from the not-yet-popped old polarity is
                // harmless here and preserves the existing search trajectory.
                // Only when it manufactures a conflict do we pay for a full
                // rebuild from the corrected, deduplicated trail: that conflict
                // may be spurious (a stale artefact of the SAT core's wrong
                // backtrack level, the wrong-UNSAT cause) so we must re-derive
                // the authoritative verdict — `Conflict` if genuinely
                // inconsistent, `Sat` if the stale state fabricated it.
                let direct = self.process_constraint(var, constraint, is_positive, self.manager);
                let result = if matches!(direct, TheoryCheckResult::Conflict(_)) {
                    self.resync_theory_state()
                } else {
                    direct
                };
                if matches!(result, TheoryCheckResult::Conflict(_)) {
                    self.statistics.theory_conflicts += 1;
                    self.statistics.conflicts += 1;
                    if self.max_conflicts > 0 && self.statistics.conflicts >= self.max_conflicts {
                        self.resource_exhausted = true;
                        return TheoryCheckResult::Sat;
                    }
                }
                return result;
            }
            Some(_) => {
                // Either an idempotent same-polarity re-send after a backtrack,
                // or a flip in a problem that contains bit-vector terms (handled
                // by the BV solver's own incremental push/pop).  Both fall
                // through to normal processing, preserving pre-existing behaviour.
            }
            None => {
                let idx = self.assignment_trail.len();
                self.assignment_trail.push(TrailAtom {
                    var,
                    is_positive,
                    level: self.current_level,
                });
                self.trail_index.insert(var, idx);
            }
        }

        self.processed_count += 1;
        self.statistics.theory_propagations += 1;

        let result = self.process_constraint(var, constraint, is_positive, self.manager);

        // Track theory conflicts
        if matches!(result, TheoryCheckResult::Conflict(_)) {
            self.statistics.theory_conflicts += 1;
            self.statistics.conflicts += 1;

            // Check conflict limit
            if self.max_conflicts > 0 && self.statistics.conflicts >= self.max_conflicts {
                // Resource exhaustion: we are dropping a real conflict to stop
                // the search.  Flag it so the solver answers Unknown, not Sat.
                self.resource_exhausted = true;
                return TheoryCheckResult::Sat; // Return Sat to signal resource exhaustion
            }
        }

        result
    }

    fn final_check(&mut self) -> TheoryCheckResult {
        // Enforce the wall-clock timeout: a full assignment has been reached,
        // but if we are out of time we must not spend it on a (possibly
        // expensive) final theory check.  Flag resource exhaustion and report
        // Sat so the owning solver answers `Unknown`.
        if self.timed_out() {
            self.resource_exhausted = true;
            return TheoryCheckResult::Sat;
        }

        // In lazy mode, process all pending assignments now
        if self.theory_mode == TheoryMode::Lazy {
            for &(lit, is_positive) in &self.pending_assignments.clone() {
                let var = lit.var();
                self.assigned_polarity.insert(var, is_positive);
                let Some(constraint) = self.var_to_constraint.get(&var).cloned() else {
                    continue;
                };

                self.statistics.theory_propagations += 1;

                // Process the constraint (same logic as eager mode)
                let result = self.process_constraint(var, constraint, is_positive, self.manager);
                if let TheoryCheckResult::Conflict(conflict) = result {
                    self.statistics.theory_conflicts += 1;
                    self.statistics.conflicts += 1;

                    // Check conflict limit
                    if self.max_conflicts > 0 && self.statistics.conflicts >= self.max_conflicts {
                        // Dropping a real conflict at the limit: flag it so the
                        // solver reports Unknown rather than trusting Sat.
                        self.resource_exhausted = true;
                        return TheoryCheckResult::Sat; // Signal resource exhaustion
                    }

                    return TheoryCheckResult::Conflict(conflict);
                }
            }
            // Clear pending assignments after processing
            self.pending_assignments.clear();
        }

        // Check EUF for conflicts
        if let Some(conflict_terms) = self.euf.check_conflicts() {
            // Convert TermIds to Lits for the conflict clause
            let conflict = self.conflict_from_terms(&conflict_terms);
            self.statistics.theory_conflicts += 1;
            self.statistics.conflicts += 1;

            // Check conflict limit
            if self.max_conflicts > 0 && self.statistics.conflicts >= self.max_conflicts {
                // Dropping a real EUF conflict at the limit: flag it so the
                // solver reports Unknown rather than trusting Sat.
                self.resource_exhausted = true;
                return TheoryCheckResult::Sat; // Signal resource exhaustion
            }

            return conflict;
        }

        // Soundness backstop: the incremental EUF state, built up across CDCL
        // push/pop, can lose a congruence or disequality, so the live
        // `check_conflicts` above can report a spurious "consistent" on a
        // genuinely-unsatisfiable, *function-bearing* assignment (the live
        // e-graph diverges from a fresh replay of the same asserted equalities).
        // Rebuild the theory state from the deduplicated shadow trail and
        // re-check; honor any conflict the rebuild finds that the incremental
        // state missed. Gated on `has_app_nodes` because the divergence is
        // specific to function-bearing EUF, and pure-equality problems would be
        // unfairly penalized by the per-final_check rebuild cost.
        if self.euf.has_app_nodes() {
            let replay = self.resync_theory_state();
            if let TheoryCheckResult::Conflict(conflict_lits) = replay {
                self.statistics.theory_conflicts += 1;
                self.statistics.conflicts += 1;
                if self.max_conflicts > 0 && self.statistics.conflicts >= self.max_conflicts {
                    self.resource_exhausted = true;
                    return TheoryCheckResult::Sat;
                }
                return TheoryCheckResult::Conflict(conflict_lits);
            }
        }

        // Propagate EUF-derived equalities into the arithmetic solver.
        // When EUF fires congruence closure and derives f(x) = f(y) because
        // x = y was asserted, the arithmetic solver is unaware of this equality.
        // We must propagate it so the arithmetic solver can detect contradictions.
        let mut propagate_dedup: FxHashSet<(TermId, TermId)> = FxHashSet::default();
        let eq_result = self.propagate_euf_equalities_to_arith(&mut propagate_dedup);
        if let TheoryCheckResult::Conflict(_) = eq_result {
            self.statistics.theory_conflicts += 1;
            self.statistics.conflicts += 1;
            return eq_result;
        }

        // Check arithmetic
        match self.arith.check() {
            Ok(result) => {
                match result {
                    oxiz_theories::TheoryCheckResult::Sat => {
                        // z3-style theory propagation: for every axiomatized
                        // `ite`-result term `t`, read its current arithmetic
                        // value `v`; if arithmetic provably fixes `t = v` (with
                        // an all-atom explanation), propagate the triangle's
                        // `le`/`ge` atoms.  The clause `(eq ∨ ¬le ∨ ¬ge)` then
                        // forces `eq`, EUF merges `t` with `v` using the `eq`
                        // atom (SAT-backed reason), and congruence closure
                        // collapses the nested chain — deterministically.
                        // Cost: O(#ite-terms) — one value lookup + at most one
                        // probe per term (only the constant it's assigned).
                        let mut theory_props: Vec<(Lit, SmallVec<[Lit; 8]>)> = Vec::new();
                        for &term in self.ite_result_terms {
                            let Some(val) = self.arith.value(term) else {
                                continue;
                            };
                            let Some(v) = (if val.is_integer() {
                                val.to_i64()
                            } else {
                                None
                            }) else {
                                continue;
                            };
                            let Some(&(le_var, ge_var)) =
                                self.ite_const_axioms.get(&(term, v))
                            else {
                                continue;
                            };
                            // Skip if both already assigned (avoids re-emitting
                            // a no-op Propagated on a fully-assigned trail).
                            if self.assigned_pol_of(le_var).is_some()
                                && self.assigned_pol_of(ge_var).is_some()
                            {
                                continue;
                            }
                            let Some(reasons) = self.arith.fixed_to_const_reason(term, v)
                            else {
                                continue;
                            };
                            let mut reason_lits: SmallVec<[Lit; 8]> = SmallVec::new();
                            let mut ok = true;
                            for &r in &reasons {
                                match self.term_to_var.get(&r) {
                                    Some(&var) if self.assigned_pol_of(var) == Some(true) => {
                                        reason_lits.push(Lit::pos(var));
                                    }
                                    _ => {
                                        ok = false;
                                        break;
                                    }
                                }
                            }
                            if !ok {
                                continue;
                            }
                            if self.assigned_pol_of(le_var).is_none() {
                                theory_props.push((Lit::pos(le_var), reason_lits.clone()));
                            }
                            if self.assigned_pol_of(ge_var).is_none() {
                                theory_props.push((Lit::pos(ge_var), reason_lits));
                            }
                        }
                        if !theory_props.is_empty() {
                            self.statistics.theory_propagations += theory_props.len() as u64;
                            return TheoryCheckResult::Propagated(theory_props);
                        }
                        // Arithmetic is consistent, now check model-based theory combination
                        // This ensures that different theories agree on shared terms
                        self.nelson_oppen_combine()
                    }
                    oxiz_theories::TheoryCheckResult::Unsat(conflict_terms) => {
                        // Arithmetic conflict detected - convert to SAT conflict clause
                        let conflict = self.conflict_from_terms(&conflict_terms);
                        self.statistics.theory_conflicts += 1;
                        self.statistics.conflicts += 1;

                        // Check conflict limit
                        if self.max_conflicts > 0 && self.statistics.conflicts >= self.max_conflicts
                        {
                            // Dropping a real arithmetic conflict at the limit:
                            // flag it so the solver reports Unknown, not Sat.
                            self.resource_exhausted = true;
                            return TheoryCheckResult::Sat; // Signal resource exhaustion
                        }

                        conflict
                    }
                    oxiz_theories::TheoryCheckResult::Propagate(_) => {
                        // Propagations should be handled in on_assignment
                        self.model_based_combination()
                    }
                    oxiz_theories::TheoryCheckResult::Unknown => {
                        // The arithmetic solver could not decide this state
                        // (e.g. LIA branch-and-bound / LP budget exhausted).
                        // Returning a plain `Sat` here would fabricate a model
                        // the solver never verified — an unsound `Sat`.  Flag
                        // resource exhaustion so the owning solver answers
                        // `Unknown`, and stop the search by reporting Sat.
                        self.resource_exhausted = true;
                        TheoryCheckResult::Sat
                    }
                }
            }
            Err(_error) => {
                // Internal error in the arithmetic solver.  We have no verified
                // model, so we must not claim `Sat`.  Flag resource exhaustion
                // (→ solver answers `Unknown`) and stop the search.
                self.resource_exhausted = true;
                TheoryCheckResult::Sat
            }
        }
    }

    fn on_new_level(&mut self, level: u32) {
        // Track the current SAT decision level for the shadow trail.
        self.current_level = level;
        // Push theory state when a new decision level is created
        // Ensure we have enough levels in the stack
        while self.level_stack.len() < (level as usize + 1) {
            self.push_theory_scope();
        }
    }

    fn on_backtrack(&mut self, level: u32) {
        // Track the current SAT decision level and prune the shadow trail of
        // every assignment made above `level` (they have been undone by the SAT
        // core's backtrack).  Rebuild the var -> trail-index map afterwards.
        self.current_level = level;
        if self.assignment_trail.iter().any(|a| a.level > level) {
            self.assignment_trail.retain(|a| a.level <= level);
            self.trail_index.clear();
            for (i, atom) in self.assignment_trail.iter().enumerate() {
                self.trail_index.insert(atom.var, i);
            }
        }
        self.assigned_level.retain(|_var, &mut lvl| lvl <= level);

        // Pop EUF, Arith, and BV states if needed.  Each pop also drops the
        // derived-equality explanations recorded in the scope it retracts —
        // and, just as importantly, keeps the ones recorded at or below the
        // surviving depth: those assertions are still in the tableau, and
        // forgetting their explanation leaves a later conflict citing one of
        // them unable to name the literals it rests on.
        while self.level_stack.len() > (level as usize + 1) {
            self.pop_theory_scope();
        }
        self.processed_count = *self.level_stack.last().unwrap_or(&0);

        // Evict stale integer-constant canonicals whose EUF nodes were removed
        // by the preceding pop().  After truncation, any node index >=
        // euf.node_count() is invalid; keeping such entries would cause an
        // out-of-bounds access in `intern_term_deep` when `merge` is called
        // against the stale canonical.  Evicting them forces re-registration
        // (and fresh disequality assertions) the next time those values appear.
        let live_nodes = self.euf.node_count();
        self.interned_int_constants
            .retain(|_val, &mut canonical| (canonical as usize) < live_nodes);

        // Evict stale bit-vector-constant canonicals for the same reason.
        self.interned_bv_constants
            .retain(|_key, &mut canonical| (canonical as usize) < live_nodes);

        // Evict stale Boolean canonical nodes
        if let Some(t) = self.bool_true_node {
            if (t as usize) >= live_nodes {
                self.bool_true_node = None;
            }
        }
        if let Some(f) = self.bool_false_node {
            if (f as usize) >= live_nodes {
                self.bool_false_node = None;
            }
        }

        // Clear pending assignments on backtrack (in lazy mode)
        if self.theory_mode == TheoryMode::Lazy {
            self.pending_assignments.clear();
        }
    }
}

/// Result from parallel theory checking
#[cfg(feature = "parallel-theories")]
#[allow(dead_code)]
#[derive(Debug, Clone)]
pub enum ParallelTheoryResult {
    /// All theories report SAT
    AllSat,
    /// At least one theory found a conflict
    Conflict(SmallVec<[Lit; 8]>),
}

/// Parallel theory checking support.
#[cfg(feature = "parallel-theories")]
#[allow(dead_code)]
pub struct ParallelTheoryChecker;

#[cfg(feature = "parallel-theories")]
impl ParallelTheoryChecker {
    /// Check multiple independent theory assertions in parallel.
    #[allow(dead_code)]
    pub fn check_parallel(
        assertions: &[(Var, Constraint, bool)],
        _term_to_var: &FxHashMap<TermId, Var>,
    ) -> ParallelTheoryResult {
        use rayon::prelude::*;

        let mut euf_assertions = Vec::new();
        let mut arith_assertions = Vec::new();
        let bv_assertions = Vec::new();

        for (var, constraint, is_positive) in assertions {
            match constraint {
                Constraint::Eq(_, _) | Constraint::Diseq(_, _) => {
                    euf_assertions.push((*var, constraint.clone(), *is_positive));
                }
                Constraint::Le(_, _)
                | Constraint::Lt(_, _)
                | Constraint::Ge(_, _)
                | Constraint::Gt(_, _) => {
                    arith_assertions.push((*var, constraint.clone(), *is_positive));
                }
                Constraint::BoolApp(_) => {
                    euf_assertions.push((*var, constraint.clone(), *is_positive));
                }
            }
        }

        let results: Vec<Option<SmallVec<[Lit; 8]>>> =
            [&euf_assertions, &arith_assertions, &bv_assertions]
                .par_iter()
                .map(|domain| Self::check_domain_contradictions(domain))
                .collect();

        if let Some(conflict) = results.into_iter().flatten().next() {
            return ParallelTheoryResult::Conflict(conflict);
        }

        ParallelTheoryResult::AllSat
    }

    #[allow(dead_code)]
    fn check_domain_contradictions(
        assertions: &[(Var, Constraint, bool)],
    ) -> Option<SmallVec<[Lit; 8]>> {
        for i in 0..assertions.len() {
            for j in (i + 1)..assertions.len() {
                let (var_i, constraint_i, pos_i) = &assertions[i];
                let (var_j, constraint_j, pos_j) = &assertions[j];
                if Self::are_contradictory(constraint_i, *pos_i, constraint_j, *pos_j) {
                    let mut conflict = SmallVec::new();
                    conflict.push(Lit::neg(*var_i));
                    conflict.push(Lit::neg(*var_j));
                    return Some(conflict);
                }
            }
        }
        None
    }

    #[allow(dead_code)]
    fn are_contradictory(c1: &Constraint, pos1: bool, c2: &Constraint, pos2: bool) -> bool {
        match (c1, c2) {
            (Constraint::Eq(a1, b1), Constraint::Eq(a2, b2)) => {
                a1 == a2 && b1 == b2 && pos1 != pos2
            }
            (Constraint::Eq(a1, b1), Constraint::Diseq(a2, b2))
            | (Constraint::Diseq(a2, b2), Constraint::Eq(a1, b1)) => {
                a1 == a2 && b1 == b2 && pos1 && pos2
            }
            _ => false,
        }
    }
}

#[cfg(test)]
mod s8_iterative_tests;
