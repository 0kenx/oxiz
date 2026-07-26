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

use super::theory_bv_encode::encode_bv_term_recursive;
use super::types::{
    ArithConstraintType, Constraint, ParsedArithConstraint, Statistics, TheoryMode,
};

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
    interned_bv_constants: FxHashMap<(u64, u32), u32>,
    /// Canonical EUF nodes for distinct string literals.  EUF has no built-in
    /// notion that `"x" ≠ "y"`, so without explicit diseqs `s="x" ∧ s="y"` is
    /// spuriously sat (issue #14).
    interned_string_constants: FxHashMap<String, u32>,
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
            interned_string_constants: FxHashMap::default(),
            bool_true_node: None,
            bool_false_node: None,
            resource_exhausted: false,
            #[cfg(feature = "std")]
            deadline,
            assigned_polarity: FxHashMap::default(),
            current_level: 0,
            assignment_trail: Vec::new(),
            trail_index: FxHashMap::default(),
        }
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
        self.interned_string_constants.clear();
        self.bool_true_node = None;
        self.bool_false_node = None;
        self.processed_equalities.clear();
        self.pending_equalities.clear();

        // Rebuild the level-scope bookkeeping to match the current level.
        self.level_stack = vec![0];
        self.processed_count = 0;

        let max_level = self.current_level;
        // Snapshot the trail so we can call `&mut self` methods while iterating.
        let trail = self.assignment_trail.clone();
        let mut first_conflict: Option<TheoryCheckResult> = None;

        for lvl in 0..=max_level {
            if lvl > 0 {
                self.level_stack.push(self.processed_count);
                self.euf.push();
                self.arith.push();
                self.bv.push();
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
                let conflict_lits = self.terms_to_conflict_clause(&conflict_terms);
                return TheoryCheckResult::Conflict(conflict_lits);
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
    fn propagate_euf_equalities_to_arith(&mut self) -> TheoryCheckResult {
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

        // For each pair of arith terms, check if they are EUF-equal.
        // `euf.intern(t)` looks up `term_to_node` first, so two terms that
        // share the same EUF node (via congruence at intern-time) correctly
        // return the same node index.
        for i in 0..arith_terms.len() {
            for j in (i + 1)..arith_terms.len() {
                let t1 = arith_terms[i];
                let t2 = arith_terms[j];
                if t1 == t2 {
                    continue;
                }
                // Only consider terms that have been registered in EUF.
                let Some(n1) = self.euf.term_to_node(t1) else {
                    continue;
                };
                let Some(n2) = self.euf.term_to_node(t2) else {
                    continue;
                };
                if self.euf.are_equal(n1, n2) {
                    // EUF has derived t1 = t2.  Assert this equality into the
                    // arithmetic solver as `1*t1 + (-1)*t2 = 0`.
                    // Use t1 as the reason term for conflict clause generation.
                    let reason = t1;
                    self.arith.assert_eq(
                        &[
                            (t1, Rational64::from_integer(1)),
                            (t2, Rational64::from_integer(-1)),
                        ],
                        Rational64::from_integer(0),
                        reason,
                    );

                    // Check ArithSolver for conflicts after each new equality.
                    use oxiz_theories::Theory;
                    use oxiz_theories::TheoryCheckResult as TheoryCheckResultEnum;
                    if let Ok(TheoryCheckResultEnum::Unsat(conflict_terms)) = self.arith.check() {
                        let conflict_lits = self.terms_to_conflict_clause(&conflict_terms);
                        return TheoryCheckResult::Conflict(conflict_lits);
                    }
                }
            }
        }

        TheoryCheckResult::Sat
    }

    /// Model-based theory combination
    /// Detects conflicts where EUF has derived an equality between two terms
    /// but the arithmetic solver assigns them different values.
    ///
    /// Two terms disagree only if they share an EUF equivalence class, so instead
    /// of the naive O(n²) all-pairs scan we bucket each shared term by its EUF
    /// representative node in a single O(n) pass.  Within a bucket we keep the
    /// first (term, arith-value) witness we have seen; the moment a later member
    /// of the same class carries a different arith value we have found a valid
    /// interface conflict (any two class members with distinct arith values form
    /// one).  This turns the per-`final_check` cost from quadratic to linear in
    /// the number of encoded terms while preserving the exact conflict semantics.
    fn model_based_combination(&mut self) -> TheoryCheckResult {
        // Map EUF representative node -> (witness term, its arith value) for the
        // first class member that carries a concrete arithmetic value.  Terms
        // without an arith value cannot participate in an arith disagreement and
        // are simply skipped (mirroring the old `if let (Some, Some)` guard).
        let mut witness: FxHashMap<u32, (TermId, Rational64)> = FxHashMap::default();

        let shared_terms: Vec<TermId> = self.term_to_var.keys().copied().collect();
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
                    if prev_value != value {
                        // Same EUF class, different arith values: interface conflict.
                        let conflict_lits = self.terms_to_conflict_clause(&[prev_term, term]);
                        return TheoryCheckResult::Conflict(conflict_lits);
                    }
                }
                None => {
                    witness.insert(rep, (term, value));
                }
            }
        }

        TheoryCheckResult::Sat
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
    #[allow(dead_code)]
    fn intern_term_deep(&mut self, term: TermId, manager: &TermManager) -> u32 {
        if let Some(idx) = self.euf.term_to_node(term) {
            return idx;
        }
        if let Some(t) = manager.get(term) {
            match &t.kind {
                TermKind::Apply { func, args, .. } => {
                    let func_id = func.into_inner().get();
                    let arg_nodes: SmallVec<[u32; 4]> = args
                        .iter()
                        .map(|&a| self.intern_term_deep(a, manager))
                        .collect();
                    return self.euf.intern_app(term, func_id, arg_nodes);
                }
                TermKind::Select(array, index) => {
                    // Intern both sub-terms first (recursively), then register
                    // `select` as a binary function application so that EUF
                    // congruence closure fires when the index (or array) args
                    // become equal.
                    let array_node = self.intern_term_deep(*array, manager);
                    let index_node = self.intern_term_deep(*index, manager);
                    return self.euf.intern_app(
                        term,
                        Self::SELECT_FUNC_ID,
                        [array_node, index_node],
                    );
                }
                TermKind::IntConst(n) => {
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
                _ => {}
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
    fn intern_term_for_congruence(&mut self, term: TermId, manager: &TermManager) -> u32 {
        if let Some(idx) = self.euf.term_to_node(term) {
            return idx;
        }
        if let Some(t) = manager.get(term) {
            match &t.kind {
                TermKind::Apply { func, args, .. } => {
                    let func_id = func.into_inner().get();
                    let arg_nodes: SmallVec<[u32; 4]> = args
                        .iter()
                        .map(|&a| self.intern_term_for_congruence(a, manager))
                        .collect();
                    return self.euf.intern_app(term, func_id, arg_nodes);
                }
                TermKind::Select(array, index) => {
                    let array_node = self.intern_term_for_congruence(*array, manager);
                    let index_node = self.intern_term_for_congruence(*index, manager);
                    return self.euf.intern_app(
                        term,
                        Self::SELECT_FUNC_ID,
                        [array_node, index_node],
                    );
                }
                TermKind::BitVecConst { value, width } => {
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
                    let key = (value.iter_u64_digits().next().unwrap_or(0), *width);
                    let new_node = self.euf.intern(term);
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
                        .filter_map(|(&(_v, w), &node)| (w == *width).then_some(node))
                        .collect();
                    for other_node in diseq_targets {
                        self.euf.assert_diseq(new_node, other_node, term);
                    }
                    self.interned_bv_constants.insert(key, new_node);
                    return new_node;
                }
                TermKind::StringLit(s) => {
                    // Pairwise diseqs between distinct string literals so
                    // `s = "x" ∧ s = "y"` is unsat in EUF (issue #14).
                    let new_node = self.euf.intern(term);
                    if let Some(&canonical) = self.interned_string_constants.get(s) {
                        let _ = self.euf.merge(new_node, canonical, term);
                        return canonical;
                    }
                    let diseq_targets: Vec<u32> =
                        self.interned_string_constants.values().copied().collect();
                    for other_node in diseq_targets {
                        self.euf.assert_diseq(new_node, other_node, term);
                    }
                    self.interned_string_constants.insert(s.clone(), new_node);
                    return new_node;
                }
                _ => {}
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

    /// Convert a list of reason term IDs into a theory conflict clause.
    ///
    /// `analyze_theory_conflict` (in `oxiz-sat`) requires every literal of the
    /// conflict clause to be **false** under the current assignment.  A reason
    /// atom may have been assigned either polarity: a disequality (`Eq` assigned
    /// false), a `~(a != b)`, or a Bool application assigned false all store
    /// their term as a theory reason.  We therefore emit, for each reason atom,
    /// the literal opposite to its recorded assignment — `¬var` when the atom is
    /// currently true, `var` when it is currently false — so the literal is
    /// false as required.  Emitting `¬var` unconditionally (the previous
    /// behaviour) produced a *true* literal for negatively-assigned atoms,
    /// yielding an unsound lemma.
    ///
    /// Reason terms with no SAT variable are tautological facts injected by the
    /// theory layer itself (e.g. `10 ≠ 20` interned-constant disequalities);
    /// they are not decision literals and are correctly omitted.
    fn terms_to_conflict_clause(&self, terms: &[TermId]) -> SmallVec<[Lit; 8]> {
        let mut conflict = SmallVec::new();
        for &term in terms {
            if let Some(&var) = self.term_to_var.get(&term) {
                let lit = match self.assigned_polarity.get(&var) {
                    // Atom currently true  → its false literal is ¬var.
                    Some(true) => Lit::neg(var),
                    // Atom currently false → its false literal is var.
                    Some(false) => Lit::pos(var),
                    // Polarity unknown (e.g. a shared theory term not assigned as
                    // a Boolean atom): fall back to ¬var, matching legacy behaviour.
                    None => Lit::neg(var),
                };
                conflict.push(lit);
            }
        }
        conflict
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
    fn bv_run_check(&mut self, constraint_term: TermId) -> Option<TheoryCheckResult> {
        use oxiz_theories::Theory;
        use oxiz_theories::TheoryCheckResult as TheoryCheckResultEnum;
        self.bv.record_constraint_term(constraint_term);
        if let Ok(TheoryCheckResultEnum::Unsat(conflict_terms)) = self.bv.check() {
            let conflict_lits = self.terms_to_conflict_clause(&conflict_terms);
            return Some(TheoryCheckResult::Conflict(conflict_lits));
        }
        None
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
        self.bv_run_check(constraint_term)
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
        self.bv_run_check(constraint_term)
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
                        let conflict_lits = self.terms_to_conflict_clause(&conflict_terms);
                        return TheoryCheckResult::Conflict(conflict_lits);
                    }

                    // For arithmetic equalities, also send to ArithSolver
                    // Use pre-parsed constraint if available
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
                            let conflict_lits = self.terms_to_conflict_clause(&conflict_terms);
                            return TheoryCheckResult::Conflict(conflict_lits);
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

                    if lhs_is_bv || rhs_is_bv {
                        let mut did_assert = false;

                        // Helper to extract BV constant info
                        let get_bv_const = |term_id: TermId| -> Option<(u64, u32)> {
                            manager.get(term_id).and_then(|t| match &t.kind {
                                TermKind::BitVecConst { value, width } => {
                                    let val_u64 = value.iter_u64_digits().next().unwrap_or(0);
                                    Some((val_u64, *width))
                                }
                                _ => None,
                            })
                        };

                        // Helper to get BV width from term's sort
                        let get_bv_width = |term_id: TermId| -> Option<u32> {
                            manager.get(term_id).and_then(|t| {
                                manager.sorts.get(t.sort).and_then(|s| s.bitvec_width())
                            })
                        };

                        // Helper to check if term is a simple variable
                        let is_var = |term_id: TermId| -> bool {
                            manager
                                .get(term_id)
                                .is_some_and(|t| matches!(t.kind, TermKind::Var(_)))
                        };

                        // Memo set to track already-encoded TermIds within this
                        // constraint so that shared sub-terms are encoded exactly once.
                        let mut bv_encoded: FxHashSet<TermId> = FxHashSet::default();

                        // Check for BV operations and encode them
                        let lhs_term = manager.get(lhs);
                        let rhs_term = manager.get(rhs);

                        // Helper to check if a term is a BV operation
                        let is_bv_op = |t: &oxiz_core::ast::Term| {
                            matches!(
                                t.kind,
                                TermKind::BvAdd(_, _)
                                    | TermKind::BvMul(_, _)
                                    | TermKind::BvSub(_, _)
                                    | TermKind::BvAnd(_, _)
                                    | TermKind::BvOr(_, _)
                                    | TermKind::BvXor(_, _)
                                    | TermKind::BvNot(_)
                                    | TermKind::BvUdiv(_, _)
                                    | TermKind::BvSdiv(_, _)
                                    | TermKind::BvUrem(_, _)
                                    | TermKind::BvSrem(_, _)
                            )
                        };

                        let lhs_is_op = lhs_term.is_some_and(is_bv_op);
                        let rhs_is_op = rhs_term.is_some_and(is_bv_op);

                        let lhs_const_info = get_bv_const(lhs);
                        let rhs_const_info = get_bv_const(rhs);
                        let lhs_is_var = is_var(lhs);
                        let rhs_is_var = is_var(rhs);

                        // Case 0: BV operation = BV operation
                        // (e.g. (= (bvadd x y) (bvadd y x)), (= (bvmul #x02 x) (bvadd x x))).
                        // Both sides are fully bit-blasted and then constrained equal so
                        // that commutativity / associativity / distributivity conflicts
                        // are detected by the embedded SAT solver.
                        if lhs_is_op && rhs_is_op {
                            if let Some(_width) = get_bv_width(lhs) {
                                encode_bv_term_recursive(self.bv, lhs, manager, &mut bv_encoded);
                                encode_bv_term_recursive(self.bv, rhs, manager, &mut bv_encoded);
                                self.bv.assert_eq(lhs, rhs);
                                did_assert = true;
                            }
                        }
                        // Case 1: BV operation = constant (e.g., (= (bvmul x y) #x0c))
                        else if lhs_is_op {
                            if let Some(width) = get_bv_width(lhs) {
                                // Recursively encode the LHS operation and all its sub-terms
                                encode_bv_term_recursive(self.bv, lhs, manager, &mut bv_encoded);

                                if let Some((val, _)) = rhs_const_info {
                                    // Assert operation result = constant
                                    self.bv.assert_const(lhs, val, width);
                                    did_assert = true;
                                } else if rhs_is_var && self.bv_terms.contains(&rhs) {
                                    // Assert operation result = variable
                                    self.bv.new_bv(rhs, width);
                                    self.bv.assert_eq(lhs, rhs);
                                    did_assert = true;
                                }
                            }
                        }
                        // Case 2: constant = BV operation
                        else if rhs_is_op {
                            if let Some(width) = get_bv_width(rhs) {
                                // Recursively encode the RHS operation and all its sub-terms
                                encode_bv_term_recursive(self.bv, rhs, manager, &mut bv_encoded);

                                if let Some((val, _)) = lhs_const_info {
                                    // Assert operation result = constant
                                    self.bv.assert_const(rhs, val, width);
                                    did_assert = true;
                                } else if lhs_is_var && self.bv_terms.contains(&lhs) {
                                    // Assert variable = operation result
                                    self.bv.new_bv(lhs, width);
                                    self.bv.assert_eq(lhs, rhs);
                                    did_assert = true;
                                }
                            }
                        }
                        // Case 3: Simple variable = constant
                        else if lhs_is_var && self.bv_terms.contains(&lhs) {
                            if let Some((val, width)) = rhs_const_info {
                                self.bv.assert_const(lhs, val, width);
                                did_assert = true;
                            }
                        }
                        // Case 4: constant = simple variable
                        else if rhs_is_var && self.bv_terms.contains(&rhs) {
                            if let Some((val, width)) = lhs_const_info {
                                self.bv.assert_const(rhs, val, width);
                                did_assert = true;
                            }
                        }
                        // Case 5: Both simple variables
                        else if lhs_is_var
                            && rhs_is_var
                            && self.bv_terms.contains(&lhs)
                            && self.bv_terms.contains(&rhs)
                            && let Some(width) = get_bv_width(lhs)
                        {
                            self.bv.new_bv(lhs, width);
                            self.bv.new_bv(rhs, width);
                            self.bv.assert_eq(lhs, rhs);
                            did_assert = true;
                        }

                        // Run the BV SAT check whenever this equality was bit-blasted
                        // and asserted.  The embedded SAT solver is pushed/popped in
                        // lockstep with the outer CDCL decision levels (see
                        // `on_new_level` / `on_backtrack`), and `BvSolver::check`
                        // rolls its internal trail back to the committed (asserted)
                        // prefix after every probe, so no model-specific assignment
                        // from one `check()` survives to corrupt the next.  Any UNSAT
                        // it reports is therefore a genuine theory conflict.  The
                        // outer conflict analysis (`analyze_theory_conflict`) only
                        // forces a top-level UNSAT when ALL conflicting literals are
                        // fixed at decision level 0, so consulting `check()` here is
                        // sound in both directions: it can neither manufacture a false
                        // SAT (the previous bug was the MISSING check) nor a false
                        // UNSAT (the previous bug was the leaked-model trail).
                        if did_assert {
                            use oxiz_theories::Theory;
                            use oxiz_theories::TheoryCheckResult as TheoryCheckResultEnum;
                            // Record the constraint term so that check() can produce a
                            // non-empty conflict clause if the SAT sub-solver returns UNSAT.
                            let constraint_term = self.term_for_var(var);
                            self.bv.record_constraint_term(constraint_term);
                            let bv_check_result = self.bv.check();
                            if let Ok(TheoryCheckResultEnum::Unsat(conflict_terms)) =
                                bv_check_result
                            {
                                let conflict_lits = self.terms_to_conflict_clause(&conflict_terms);
                                return TheoryCheckResult::Conflict(conflict_lits);
                            }
                        }
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
                        let conflict_lits = self.terms_to_conflict_clause(&conflict_terms);
                        return TheoryCheckResult::Conflict(conflict_lits);
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
                        let conflict_lits = self.terms_to_conflict_clause(&conflict_terms);
                        return TheoryCheckResult::Conflict(conflict_lits);
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
                        let conflict_lits = self.terms_to_conflict_clause(&conflict_terms);
                        return TheoryCheckResult::Conflict(conflict_lits);
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

                // Check if this is a BV comparison
                let lhs_is_bv = self.bv_terms.contains(&lhs);
                let rhs_is_bv = self.bv_terms.contains(&rhs);

                // Handle BV comparisons
                if lhs_is_bv || rhs_is_bv {
                    // Bit-blast both operands *with constants pinned*.  Bare
                    // `new_bv` leaves `BitVecConst` bits unconstrained, so
                    // `(bvult x #b0)` was treated as `x < free` and reported
                    // sat (issue #17).  `bit_blast_bv_pair` routes through
                    // `encode_bv_term_recursive`, which calls `assert_const`.
                    if self.bit_blast_bv_pair(lhs, rhs, manager) {
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

                        // Check BV solver for conflicts
                        use oxiz_theories::Theory;
                        use oxiz_theories::TheoryCheckResult as TheoryCheckResultEnum;
                        // Record the constraint term for non-empty conflict clause generation.
                        let constraint_term = self.term_for_var(var);
                        self.bv.record_constraint_term(constraint_term);
                        if let Ok(TheoryCheckResultEnum::Unsat(conflict_terms)) = self.bv.check() {
                            let conflict_lits = self.terms_to_conflict_clause(&conflict_terms);
                            return TheoryCheckResult::Conflict(conflict_lits);
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
                            let conflict_lits = self.terms_to_conflict_clause(&conflict_terms);
                            return TheoryCheckResult::Conflict(conflict_lits);
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
                    let conflict_lits = self.terms_to_conflict_clause(&conflict_terms);
                    return TheoryCheckResult::Conflict(conflict_lits);
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
        // correct (currently-false) literal for this variable.
        self.assigned_polarity.insert(var, is_positive);

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
            let conflict_lits = self.terms_to_conflict_clause(&conflict_terms);
            self.statistics.theory_conflicts += 1;
            self.statistics.conflicts += 1;

            // Check conflict limit
            if self.max_conflicts > 0 && self.statistics.conflicts >= self.max_conflicts {
                // Dropping a real EUF conflict at the limit: flag it so the
                // solver reports Unknown rather than trusting Sat.
                self.resource_exhausted = true;
                return TheoryCheckResult::Sat; // Signal resource exhaustion
            }

            return TheoryCheckResult::Conflict(conflict_lits);
        }

        // Propagate EUF-derived equalities into the arithmetic solver.
        // When EUF fires congruence closure and derives f(x) = f(y) because
        // x = y was asserted, the arithmetic solver is unaware of this equality.
        // We must propagate it so the arithmetic solver can detect contradictions.
        let eq_result = self.propagate_euf_equalities_to_arith();
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
                        // Arithmetic is consistent, now check model-based theory combination
                        // This ensures that different theories agree on shared terms
                        self.model_based_combination()
                    }
                    oxiz_theories::TheoryCheckResult::Unsat(conflict_terms) => {
                        // Arithmetic conflict detected - convert to SAT conflict clause
                        let conflict_lits = self.terms_to_conflict_clause(&conflict_terms);
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

                        TheoryCheckResult::Conflict(conflict_lits)
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
            self.level_stack.push(self.processed_count);
            self.euf.push();
            self.arith.push();
            self.bv.push();
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

        // Pop EUF, Arith, and BV states if needed
        while self.level_stack.len() > (level as usize + 1) {
            self.level_stack.pop();
            self.euf.pop();
            self.arith.pop();
            self.bv.pop();
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
        self.interned_string_constants
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
