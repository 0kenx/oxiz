//! Conflict analysis, backtracking, activity management, and restart/reduction
//! for the NLSAT solver.

use super::NlsatSolver;
use crate::assignment::Justification;
use crate::clause::ClauseId;
use crate::restart::RestartStrategy;
use crate::types::{BoolVar, Literal};
use oxiz_math::polynomial::Var;
use std::cmp::Ordering as CmpOrdering;
use std::collections::{HashMap, HashSet};

/// Outcome of beginning resolution of one variable in
/// [`NlsatSolver::is_redundant_literal`].
enum EntryOutcome {
    /// The variable's redundancy is already known without exploring its
    /// reason clause (no trail entry, a non-propagation justification, a
    /// missing reason clause, or a back-edge).
    Resolved(bool),
    /// The variable is propagated by a live reason clause; these are its
    /// literals to explore.
    Explore(Vec<Literal>),
}

impl NlsatSolver {
    // ========== Conflict Analysis ==========

    /// Analyze a conflict and learn a clause.
    pub(super) fn analyze_conflict(&mut self, conflict_id: ClauseId) -> (Vec<Literal>, u32) {
        self.learnt_clause.clear();
        self.seen.clear();

        // Track this clause for unsat core
        if self.extract_unsat_core {
            self.conflict_clauses.insert(conflict_id);
        }

        let clause_lits: Vec<Literal> = match self.clauses.get(conflict_id) {
            Some(c) => c.literals().to_vec(),
            None => return (Vec::new(), 0),
        };

        let current_level = self.assignment.level();
        let mut counter = 0; // Number of literals at current level

        // Process conflict clause
        for &lit in &clause_lits {
            let var = lit.var();
            if !self.seen.contains(&var) {
                self.seen.insert(var);
                let level = self.assignment.bool_level(var);

                if level == current_level {
                    counter += 1;
                } else if level > 0 {
                    self.learnt_clause.push(lit.negate());
                    self.bump_var_activity(var);
                }
            }
        }

        // Resolve until we have exactly one literal at current level
        let mut trail_idx = self.assignment.trail().len();
        while counter > 1 && trail_idx > 0 {
            // Find next literal to resolve
            trail_idx -= 1;
            let trail = self.assignment.trail();

            let entry = &trail[trail_idx];
            let lit = entry.literal;
            let var = lit.var();

            if !self.seen.contains(&var) {
                continue;
            }
            self.seen.remove(&var);
            counter -= 1;

            // Get the reason clause
            if let Justification::Propagation(reason_id) = &entry.justification {
                // Track reason clause for unsat core
                if self.extract_unsat_core {
                    self.conflict_clauses.insert(*reason_id);
                }

                let reason_lits: Vec<Literal> = match self.clauses.get(*reason_id) {
                    Some(r) => r.literals().to_vec(),
                    None => continue,
                };

                for reason_lit in reason_lits {
                    if reason_lit == lit {
                        continue;
                    }

                    let reason_var = reason_lit.var();
                    if !self.seen.contains(&reason_var) {
                        self.seen.insert(reason_var);
                        let level = self.assignment.bool_level(reason_var);

                        if level == current_level {
                            counter += 1;
                        } else if level > 0 {
                            self.learnt_clause.push(reason_lit.negate());
                            self.bump_var_activity(reason_var);
                        }
                    }
                }
            }
        }

        // Find the UIP (asserting literal)
        trail_idx = self.assignment.trail().len();
        while trail_idx > 0 {
            trail_idx -= 1;
            let trail = self.assignment.trail();
            let entry = &trail[trail_idx];
            let var = entry.literal.var();

            if self.seen.contains(&var) {
                // This is the asserting literal
                self.learnt_clause.insert(0, entry.literal.negate());
                self.bump_var_activity(var);
                break;
            }
        }

        // Compute backtrack level
        let mut backtrack_level = 0;
        for lit in &self.learnt_clause[1..] {
            let level = self.assignment.bool_level(lit.var());
            backtrack_level = backtrack_level.max(level);
        }

        // Minimize learned clause (optional)
        let minimized = self.minimize_clause(self.learnt_clause.clone());

        (minimized, backtrack_level)
    }

    /// Minimize a learned clause by removing redundant literals.
    pub(super) fn minimize_clause(&self, mut clause: Vec<Literal>) -> Vec<Literal> {
        if clause.len() <= 1 {
            return clause;
        }

        // Keep track of which literals can be removed
        let mut to_remove = Vec::new();

        // Try to remove each literal (except the first asserting literal)
        for i in 1..clause.len() {
            let lit = clause[i];
            let var = lit.var();

            // Check if this literal is redundant
            if self.is_redundant_literal(var, &clause) {
                to_remove.push(i);
            }
        }

        // Remove redundant literals (in reverse order to maintain indices)
        for &idx in to_remove.iter().rev() {
            clause.remove(idx);
        }

        clause
    }

    /// Check if a literal at a variable is redundant in the clause.
    ///
    /// A variable is redundant if every *other* literal in its propagation
    /// reason clause is either decided at level 0 (always true, needs no
    /// justification), already present in `clause`, or itself (transitively)
    /// redundant by the same rule.
    ///
    /// # Why iterative
    ///
    /// This predicate is evaluated on every conflict on the default solving
    /// path (via [`Self::minimize_clause`]), so its cost and termination
    /// matter in the common case, not just at the margin. A direct recursive
    /// implementation with no memoization re-explores shared reason-clause
    /// dependencies from scratch every time they are reached (worst case
    /// exponential in the depth of the implication graph), and has no bound
    /// on recursion depth at all -- a long propagation chain overflows the
    /// native stack, and a reason-clause cycle (never expected from a sound
    /// trail, but not something this function could previously detect
    /// either) would recurse forever. This walks the dependency graph with
    /// an explicit worklist instead, memoizing each variable's resolved
    /// verdict and tracking which variables are still being explored
    /// (`on_stack`) to detect a back-edge.
    ///
    /// # Soundness of memoizing
    ///
    /// For a fixed `clause` and a fixed assignment/clause-database snapshot
    /// (both left untouched for the entire call, exactly as before), this
    /// function is a pure function of the variable being asked about: the
    /// trail, clauses, and `clause` itself never change during the walk, so
    /// caching a variable's verdict cannot change what that verdict *is* --
    /// it only avoids recomputing it. A back-edge is resolved as *not*
    /// redundant, never as redundant: clause minimization is
    /// soundness-sensitive, and treating an unresolved dependency as
    /// redundant could drop a literal the clause actually needs, producing
    /// an unsound (too-strong) learned clause. Treating it as not-redundant
    /// only costs minimization quality, never soundness.
    pub(super) fn is_redundant_literal(&self, var: BoolVar, clause: &[Literal]) -> bool {
        struct Frame {
            var: BoolVar,
            reason_lits: Vec<Literal>,
            next: usize,
        }

        let mut memo: HashMap<BoolVar, bool> = HashMap::new();
        let mut on_stack: HashSet<BoolVar> = HashSet::new();

        // `top` is the frame currently being resolved, owned directly rather
        // than peeked from `stack` -- `stack` holds only the *suspended*
        // ancestors waiting for `top` (or one of its descendants) to finish.
        let mut top = match self.redundant_entry(var, &mut on_stack) {
            EntryOutcome::Resolved(v) => return v,
            EntryOutcome::Explore(reason_lits) => Frame {
                var,
                reason_lits,
                next: 0,
            },
        };
        let mut stack: Vec<Frame> = Vec::new();

        loop {
            let Some(&reason_lit) = top.reason_lits.get(top.next) else {
                // Every reason literal is accounted for: `top.var` is
                // redundant. Resume whichever frame is waiting below it, or
                // return directly if none is -- the empty case is not a
                // failure, it is the answer for the original `var`.
                memo.insert(top.var, true);
                on_stack.remove(&top.var);
                top = match stack.pop() {
                    Some(parent) => parent,
                    None => return true,
                };
                continue;
            };
            top.next += 1;

            if reason_lit.var() == top.var {
                continue; // Skip the propagated literal itself.
            }
            let reason_var = reason_lit.var();
            if self.assignment.bool_level(reason_var) == 0 {
                continue; // Level 0 literals are always fine.
            }
            if clause.iter().any(|&cl| cl.var() == reason_var) {
                continue; // Already explicit in the clause being minimized.
            }

            let dependency_redundant = if let Some(&cached) = memo.get(&reason_var) {
                cached
            } else {
                match self.redundant_entry(reason_var, &mut on_stack) {
                    EntryOutcome::Resolved(v) => {
                        memo.insert(reason_var, v);
                        v
                    }
                    EntryOutcome::Explore(reason_lits) => {
                        // Suspend `top` and descend into `reason_var`'s own
                        // reason clause first.
                        stack.push(top);
                        top = Frame {
                            var: reason_var,
                            reason_lits,
                            next: 0,
                        };
                        continue;
                    }
                }
            };

            if dependency_redundant {
                continue; // This dependency checked out; keep resuming `top`.
            }

            // `reason_var` could not be justified, so `top.var` is not
            // redundant either -- mirroring a recursive
            // `if !is_redundant_literal(...) { return false; }`. Every frame
            // still waiting below `top` made that exact same recursive call
            // about `top.var` (or a transitive dependency of it) and so
            // fails the same way in turn: unwind the whole stack rather than
            // resuming any of it.
            memo.insert(top.var, false);
            on_stack.remove(&top.var);
            loop {
                let Some(parent) = stack.pop() else {
                    return false;
                };
                memo.insert(parent.var, false);
                on_stack.remove(&parent.var);
            }
        }
    }

    /// Begin resolving `var` for [`Self::is_redundant_literal`]: resolve it
    /// immediately when possible (no trail entry, a non-propagation
    /// justification, a missing reason clause, or a back-edge to a variable
    /// already being explored), otherwise stake out `on_stack` and hand back
    /// the reason literals to explore.
    fn redundant_entry(&self, var: BoolVar, on_stack: &mut HashSet<BoolVar>) -> EntryOutcome {
        let trail = self.assignment.trail();
        let Some(entry) = trail.iter().find(|e| e.literal.var() == var) else {
            return EntryOutcome::Resolved(false);
        };
        match &entry.justification {
            Justification::Propagation(reason_id) => match self.clauses.get(*reason_id) {
                Some(reason_clause) => {
                    if !on_stack.insert(var) {
                        // Back-edge: `var`'s own resolution is already in
                        // progress higher up this path. A sound trail's
                        // propagation reasons are acyclic by construction
                        // (a reason clause only cites literals assigned
                        // strictly earlier), so this guards against an
                        // inconsistent trail rather than a case expected in
                        // normal operation. Resolve conservatively as "not
                        // redundant" -- see the soundness note on
                        // `is_redundant_literal`.
                        return EntryOutcome::Resolved(false);
                    }
                    EntryOutcome::Explore(reason_clause.literals().to_vec())
                }
                None => EntryOutcome::Resolved(false),
            },
            Justification::Decision | Justification::Unit | Justification::Theory => {
                // Cannot minimize past a decision, unit, or theory literal.
                EntryOutcome::Resolved(false)
            }
        }
    }

    // ========== Backtracking ==========

    /// Backtrack to a given level.
    pub(super) fn backtrack(&mut self, level: u32) {
        // Clear propagation queue
        self.propagation_queue.clear();
        self.conflict_clause = None;

        // Pop assignment levels
        let _unassigned = self.assignment.pop_level(level);

        // Reset arithmetic assignments above this level
        // (Simplified: reset all arithmetic assignments)
        for var in 0..self.num_arith_vars {
            self.assignment.unset_arith(var);
            self.assignment.reset_feasible(var);
        }
        // Greedy arithmetic samples are invalidated with the boolean level.
        self.arith_trail.clear();

        // Clear evaluation cache
        self.eval_cache.clear();
    }

    // ========== Activity Management ==========

    /// Bump the activity of a variable.
    pub(super) fn bump_var_activity(&mut self, var: BoolVar) {
        if (var as usize) >= self.var_activity.len() {
            self.var_activity.resize(var as usize + 1, 0.0);
        }

        self.var_activity[var as usize] += self.var_activity_inc;

        // Rescale if too large
        if self.var_activity[var as usize] > 1e100 {
            for a in &mut self.var_activity {
                *a *= 1e-100;
            }
            self.var_activity_inc *= 1e-100;
        }
    }

    /// Bump the activity of an arithmetic variable.
    pub(super) fn bump_arith_activity(&mut self, var: Var) {
        if (var as usize) >= self.arith_activity.len() {
            self.arith_activity.resize(var as usize + 1, 0.0);
        }

        self.arith_activity[var as usize] += self.arith_activity_inc;

        // Rescale if too large
        if self.arith_activity[var as usize] > 1e100 {
            for a in &mut self.arith_activity {
                *a *= 1e-100;
            }
            self.arith_activity_inc *= 1e-100;
        }
    }

    /// Decay all activities.
    pub(super) fn decay_activities(&mut self) {
        self.var_activity_inc *= 1.0 / self.var_activity_decay;
        self.arith_activity_inc *= 1.0 / self.arith_activity_decay;
        self.clauses.decay_activities();
    }

    // ========== Restart and Reduction ==========

    /// Compute the Literal Block Distance (LBD) of a clause.
    ///
    /// LBD is the number of distinct decision levels in the clause.
    /// Lower LBD indicates a more "glue" clause.
    pub(super) fn compute_lbd(&self, clause_lits: &[Literal]) -> u32 {
        let mut levels = HashSet::new();
        for &lit in clause_lits {
            let level = self.assignment.bool_level(lit.var());
            if level > 0 {
                levels.insert(level);
            }
        }
        levels.len() as u32
    }

    /// Maybe perform a restart using the restart manager.
    pub(super) fn maybe_restart(&mut self) {
        // Use restart manager to determine if we should restart
        let should_restart = if matches!(
            self.config.restart_strategy,
            RestartStrategy::Glucose { .. }
        ) {
            self.restart_manager
                .should_restart(Some(self.recent_avg_lbd))
        } else {
            self.restart_manager.should_restart(None)
        };

        if should_restart && self.assignment.level() > 0 {
            self.stats.restarts += 1;
            self.backtrack(0);
            self.restart_manager.restart();
        }
    }

    /// Reduce learned clauses.
    pub(super) fn reduce_learned(&mut self) {
        let removed = self
            .clauses
            .reduce_learned(self.config.learned_keep_fraction);
        self.stats.clause_deletions += removed.len() as u64;
    }

    /// Perform dynamic variable reordering based on activity scores.
    pub(super) fn dynamic_reorder(&mut self) {
        if !self.config.dynamic_reordering {
            return;
        }

        // Can only reorder unassigned variables
        let mut unassigned_vars: Vec<(Var, f64)> = (0..self.num_arith_vars)
            .filter(|&var| !self.assignment.is_arith_assigned(var))
            .map(|var| {
                let activity = self
                    .arith_activity
                    .get(var as usize)
                    .copied()
                    .unwrap_or(0.0);
                (var, activity)
            })
            .collect();

        // Sort by activity (highest first)
        unassigned_vars.sort_by(|a, b| b.1.partial_cmp(&a.1).unwrap_or(CmpOrdering::Equal));

        // Rebuild var_order: assigned variables first (in current order), then by activity
        let assigned_vars: Vec<Var> = (0..self.num_arith_vars)
            .filter(|&var| self.assignment.is_arith_assigned(var))
            .collect();

        self.var_order.clear();
        self.var_order.extend(assigned_vars);
        self.var_order
            .extend(unassigned_vars.iter().map(|(var, _)| *var));

        self.stats.reorderings += 1;
    }

    // ========== Helper Methods ==========

    /// Check if the formula is completely assigned.
    pub(super) fn is_complete(&self) -> bool {
        // All boolean variables assigned
        for var in 0..self.num_bool_vars {
            if !self.assignment.is_bool_assigned(var) {
                return false;
            }
        }

        // All arithmetic variables assigned
        for var in 0..self.num_arith_vars {
            if !self.assignment.is_arith_assigned(var) {
                return false;
            }
        }

        true
    }

    /// Generate a random number in [0, 1).
    pub(super) fn random(&mut self) -> f64 {
        self.random_int() as f64 / u64::MAX as f64
    }

    /// Generate a random u64.
    pub(super) fn random_int(&mut self) -> u64 {
        // Simple LCG
        self.random_state = self
            .random_state
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.random_state
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Directly register a propagation-justified trail entry for `var`,
    /// bypassing the solver's real unit-propagation machinery so tests can
    /// construct specific (including deliberately cyclic) reason-clause
    /// shapes that a real run of the solver would not produce.
    fn assign_propagated(solver: &mut NlsatSolver, var: BoolVar, reason: ClauseId) {
        solver
            .assignment
            .assign(Literal::positive(var), Justification::Propagation(reason));
    }

    /// Add a clause directly to the clause database, bypassing
    /// `add_clause`'s tautology/dedup/unit-assignment side effects, purely
    /// for use as an `is_redundant_literal` reason clause.
    fn add_reason_clause(solver: &mut NlsatSolver, literals: Vec<Literal>) -> ClauseId {
        solver.clauses.add(literals, 0, false)
    }

    // -----------------------------------------------------------------------
    // Behaviour-preservation: pin the exact redundancy verdict for concrete,
    // hand-verifiable reason-clause shapes (audit: item 4 asked specifically
    // that dedup/memoization must not change which literals are judged
    // redundant).
    // -----------------------------------------------------------------------

    #[test]
    fn test_is_redundant_literal_dependency_already_in_clause() {
        let mut solver = NlsatSolver::new();
        let a = solver.new_bool_var();
        let b = solver.new_bool_var();
        let z = solver.new_bool_var();
        solver.assignment.push_level();

        // a's reason is (a, b); b is at level 1 and IS already present in
        // the clause being minimized, so a is redundant without needing to
        // examine b's own justification at all.
        solver
            .assignment
            .assign(Literal::positive(b), Justification::Decision);
        let reason_a = add_reason_clause(
            &mut solver,
            vec![Literal::positive(a), Literal::positive(b)],
        );
        assign_propagated(&mut solver, a, reason_a);

        let clause = [
            Literal::positive(z),
            Literal::positive(a),
            Literal::positive(b),
        ];
        assert!(
            solver.is_redundant_literal(a, &clause),
            "a's only non-trivial dependency (b) is already explicit in the clause"
        );
    }

    #[test]
    fn test_is_redundant_literal_dependency_not_covered_is_not_redundant() {
        let mut solver = NlsatSolver::new();
        let a = solver.new_bool_var();
        let b = solver.new_bool_var();
        let c = solver.new_bool_var();
        let z = solver.new_bool_var();
        solver.assignment.push_level();

        // c is a decision (terminal, never redundant); b's reason cites c;
        // a's reason cites b. Neither b nor c is present in the clause
        // being minimized, so a must transitively fail through b and c.
        solver
            .assignment
            .assign(Literal::positive(c), Justification::Decision);
        let reason_b = add_reason_clause(
            &mut solver,
            vec![Literal::positive(b), Literal::positive(c)],
        );
        assign_propagated(&mut solver, b, reason_b);
        let reason_a = add_reason_clause(
            &mut solver,
            vec![Literal::positive(a), Literal::positive(b)],
        );
        assign_propagated(&mut solver, a, reason_a);

        let clause = [Literal::positive(z), Literal::positive(a)];
        assert!(
            !solver.is_redundant_literal(a, &clause),
            "a depends on b depends on c, a Decision literal absent from the clause"
        );
    }

    #[test]
    fn test_is_redundant_literal_level_zero_dependency_always_fine() {
        let mut solver = NlsatSolver::new();
        let a = solver.new_bool_var();
        let b = solver.new_bool_var();
        // No push_level(): both variables are assigned at level 0.
        solver
            .assignment
            .assign(Literal::positive(b), Justification::Decision);
        let reason_a = add_reason_clause(
            &mut solver,
            vec![Literal::positive(a), Literal::positive(b)],
        );
        assign_propagated(&mut solver, a, reason_a);

        // b is absent from the clause, but its level-0 assignment is always
        // fine regardless -- no recursion into b's own justification needed.
        let clause = [Literal::positive(a)];
        assert!(solver.is_redundant_literal(a, &clause));
    }

    #[test]
    fn test_minimize_clause_removes_exactly_the_redundant_literal() {
        // End-to-end pin through the actual consumer: learned clause
        // (z, a, b) where a is redundant (its only dependency, b, is
        // explicit in the clause) and b is not (its dependency c is a
        // Decision literal absent from the clause). Only `a` must be
        // dropped; z (the asserting literal, index 0) is never examined.
        let mut solver = NlsatSolver::new();
        let z = solver.new_bool_var();
        let a = solver.new_bool_var();
        let b = solver.new_bool_var();
        let c = solver.new_bool_var();
        solver.assignment.push_level();

        solver
            .assignment
            .assign(Literal::positive(c), Justification::Decision);
        let reason_b = add_reason_clause(
            &mut solver,
            vec![Literal::positive(b), Literal::positive(c)],
        );
        assign_propagated(&mut solver, b, reason_b);
        let reason_a = add_reason_clause(
            &mut solver,
            vec![Literal::positive(a), Literal::positive(b)],
        );
        assign_propagated(&mut solver, a, reason_a);

        let clause = vec![
            Literal::positive(z),
            Literal::positive(a),
            Literal::positive(b),
        ];
        let minimized = solver.minimize_clause(clause);

        assert_eq!(
            minimized,
            vec![Literal::positive(z), Literal::positive(b)],
            "a must be dropped (redundant) and b, z must be kept"
        );
    }

    // -----------------------------------------------------------------------
    // Cycle-safety: a reason-clause cycle can never arise from a sound
    // trail (see the doc comment on `is_redundant_literal`), but the
    // function itself had no way to detect one; construct one directly
    // against the trail/clause database to prove termination.
    // -----------------------------------------------------------------------

    #[test]
    fn test_is_redundant_literal_cycle_terminates_conservatively_false() {
        let mut solver = NlsatSolver::new();
        let a = solver.new_bool_var();
        let b = solver.new_bool_var();
        let z = solver.new_bool_var();
        solver.assignment.push_level();

        // a's reason cites b; b's reason cites a right back.
        let reason_a = add_reason_clause(
            &mut solver,
            vec![Literal::positive(a), Literal::positive(b)],
        );
        let reason_b = add_reason_clause(
            &mut solver,
            vec![Literal::positive(b), Literal::positive(a)],
        );
        assign_propagated(&mut solver, a, reason_a);
        assign_propagated(&mut solver, b, reason_b);

        let clause = [Literal::positive(z)];
        // The primary assertion is that this returns at all.
        let result = solver.is_redundant_literal(a, &clause);
        assert!(
            !result,
            "an unresolvable (cyclic) dependency must resolve to NOT redundant, \
             never to redundant -- the latter could drop a literal the clause needs"
        );
    }

    #[test]
    fn test_is_redundant_literal_reason_citing_only_itself_is_vacuously_redundant() {
        // A degenerate reason clause containing nothing but (repeats of)
        // the propagated literal itself is not a self-cycle: the
        // propagated literal is always skipped (it is not one of the
        // "other" literals a reason must justify), so there is nothing
        // left to check and the loop completes vacuously. This pins that
        // the self-skip is unaffected by the iterative rewrite.
        let mut solver = NlsatSolver::new();
        let a = solver.new_bool_var();
        let z = solver.new_bool_var();
        solver.assignment.push_level();

        let reason_a = add_reason_clause(
            &mut solver,
            vec![Literal::positive(a), Literal::positive(a)],
        );
        assign_propagated(&mut solver, a, reason_a);

        let clause = [Literal::positive(z)];
        assert!(solver.is_redundant_literal(a, &clause));
    }

    #[test]
    fn test_is_redundant_literal_three_cycle_terminates_conservatively_false() {
        // a's reason cites b, b's reason cites c, c's reason cites a: a
        // longer cycle than the direct 2-cycle case above, to confirm the
        // `on_stack` back-edge check catches a cycle at any length.
        let mut solver = NlsatSolver::new();
        let a = solver.new_bool_var();
        let b = solver.new_bool_var();
        let c = solver.new_bool_var();
        let z = solver.new_bool_var();
        solver.assignment.push_level();

        let reason_a = add_reason_clause(
            &mut solver,
            vec![Literal::positive(a), Literal::positive(b)],
        );
        let reason_b = add_reason_clause(
            &mut solver,
            vec![Literal::positive(b), Literal::positive(c)],
        );
        let reason_c = add_reason_clause(
            &mut solver,
            vec![Literal::positive(c), Literal::positive(a)],
        );
        assign_propagated(&mut solver, a, reason_a);
        assign_propagated(&mut solver, b, reason_b);
        assign_propagated(&mut solver, c, reason_c);

        let clause = [Literal::positive(z)];
        let result = solver.is_redundant_literal(a, &clause);
        assert!(
            !result,
            "a 3-cycle must resolve to NOT redundant, never to redundant"
        );
    }

    #[test]
    fn test_is_redundant_literal_deep_chain_small_stack() {
        // Build (iteratively) a long propagation chain v_0 <- v_1 <- ... <-
        // v_depth (each v_i's reason cites v_{i-1}), with v_0 a Decision,
        // and check v_depth's redundancy from inside a thread with a
        // deliberately small (1 MiB) stack. A stack overflow aborts the
        // whole process, so "the thread returned at all" is itself part of
        // the assertion.
        let handle = std::thread::Builder::new()
            .stack_size(1 << 20)
            .spawn(|| {
                let mut solver = NlsatSolver::new();
                let depth: usize = 50_000;
                let vars: Vec<BoolVar> = (0..=depth).map(|_| solver.new_bool_var()).collect();
                solver.assignment.push_level();
                solver
                    .assignment
                    .assign(Literal::positive(vars[0]), Justification::Decision);
                for i in 1..=depth {
                    let reason = add_reason_clause(
                        &mut solver,
                        vec![Literal::positive(vars[i]), Literal::positive(vars[i - 1])],
                    );
                    assign_propagated(&mut solver, vars[i], reason);
                }
                let clause: Vec<Literal> = Vec::new();
                let result = solver.is_redundant_literal(vars[depth], &clause);
                assert!(
                    !result,
                    "the chain bottoms out at a Decision literal, so it is not redundant"
                );
            })
            .expect("spawning a thread with an explicit stack size must succeed");
        handle
            .join()
            .expect("a deep propagation chain must not overflow a 1 MiB stack");
    }
}
