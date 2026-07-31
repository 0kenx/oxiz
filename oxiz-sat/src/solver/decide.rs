//! Decision heuristics, phase saving, backtracking, and restarts

use super::*;

impl Solver {
    /// Pick next variable to branch on
    pub(super) fn pick_branch_var(&mut self) -> Option<Var> {
        // Finite-domain equalities first (O(|priority|), not O(num_vars)).
        if !self.domain_priority.is_empty() {
            for &v in &self.domain_priority {
                if !self.trail.is_assigned(v) && !self.var_eliminated(v) {
                    return Some(v);
                }
            }
        }

        // Try external branching heuristic first.
        if let Some(ref ext) = self.config.external_branching {
            let candidates: Vec<Var> = (0..self.num_vars)
                .map(|i| Var::new(i as u32))
                .filter(|&v| !self.trail.is_assigned(v) && !self.var_eliminated(v))
                .collect();
            let scores: Vec<f64> = candidates.iter().map(|&v| self.vsids.activity(v)).collect();
            if let Ok(mut h) = ext.lock()
                && let Some(chosen) = h.select(&candidates, &scores)
            {
                return Some(chosen);
            }
        }

        if self.config.use_lrb_branching {
            // Use LRB branching
            while let Some(var) = self.lrb.select() {
                if !self.trail.is_assigned(var) && !self.var_eliminated(var) {
                    self.lrb.on_assign(var);
                    return Some(var);
                }
            }
        } else if self.config.use_chb_branching {
            // Use CHB branching
            // Rebuild heap periodically to reflect score changes
            if self.stats.decisions.is_multiple_of(100) {
                self.chb.rebuild_heap();
            }

            while let Some(var) = self.chb.pop_max() {
                if !self.trail.is_assigned(var) && !self.var_eliminated(var) {
                    return Some(var);
                }
            }
        } else {
            // Mode-dependent branching (cadical use_scores = score && stable):
            // focused → VMTF, stable → VSIDS/EVSIDS.
            let use_vmtf_now = if self.config.enable_stabilize {
                !self.stable
            } else {
                self.config.use_vmtf
            };
            if use_vmtf_now {
                // Borrow only `trail`, `equiv_substitution`, and `bve_def`
                // (disjoint from the `&mut self.vmtf` the call below needs) —
                // a full `&self` method like `var_eliminated` would conflict.
                let trail = &self.trail;
                let subst = &self.equiv_substitution;
                let bve = &self.bve_def;
                let eliminated = |v: Var| {
                    subst.get(v.index()).is_some_and(|&r| r.var() != v)
                        || bve.get(v.index()).is_some_and(|d| !d.is_empty())
                };
                if let Some(var) = self
                    .vmtf
                    .next_decision(|v| trail.is_assigned(v) || eliminated(v))
                {
                    return Some(var);
                }
            }
            while let Some(var) = self.vsids.pop_max() {
                if !self.trail.is_assigned(var) && !self.var_eliminated(var) {
                    return Some(var);
                }
            }
        }

        // An exhausted heap is *not* proof that every variable is assigned.
        // All three heuristics consume their candidates destructively
        // (`pop_max` / `select`), so any variable unassigned by a rollback that
        // failed to re-insert it disappears from the search entirely.
        //
        // Both search loops read `None` as "all variables assigned - SAT" and
        // hand the trail straight to `save_model`, so a drained heap used to
        // surface as a `Sat` verdict over a *partial* assignment: the model kept
        // `Undef` entries for the lost variables and falsified clauses that
        // nothing had ever decided. Conceding only when the assignment really is
        // total makes `None` mean what its callers assume it means. With the
        // heaps kept in repair by `backtrack`, this scan is a fallback that
        // essentially never runs.
        (0..self.num_vars)
            .map(|i| Var::new(i as u32))
            .find(|&var| !self.trail.is_assigned(var))
            .inspect(|&var| {
                if self.config.use_lrb_branching {
                    self.lrb.on_assign(var);
                }
            })
    }

    /// Backtrack with phase saving
    ///
    /// Performs every per-variable side effect of unassignment (phase saving
    /// and branching-heap reinsertion) directly inside the trail's backtrack
    /// callback by borrowing the disjoint Solver fields, instead of first
    /// collecting the unassigned variables into a throwaway `Vec`. That
    /// allocation happened on every backtrack (one per conflict) and showed up
    /// as ~3% allocator time on BCP-heavy runs.
    pub(super) fn backtrack_with_phase_saving(&mut self, level: u32) {
        if level >= self.trail.decision_level() {
            return;
        }
        // Borrow disjoint Solver fields (everything except `trail`, which the
        // `backtrack_to_with_callback` call borrows mutably).
        let phase = &mut self.phase;
        let lrb = &mut self.lrb;
        let vsids = &mut self.vsids;
        let chb = &mut self.chb;
        let vmtf = &mut self.vmtf;
        let use_lrb = self.config.use_lrb_branching;
        let use_chb = self.config.use_chb_branching;
        let use_vmtf = self.config.use_vmtf;
        self.trail.backtrack_to_with_callback(level, move |lit| {
            let var = lit.var();
            let vi = var.index();
            if vi < phase.len() {
                phase[vi] = lit.is_pos();
            }
            // Re-insert variable into the LRB heap (only when LRB is active).
            if use_lrb {
                lrb.unassign(var);
            }
            // Re-insert into VSIDS/CHB heaps and update the VMTF search pointer
            // (cadical `unassign` → `update_queue_unassigned`): the pointer
            // moves to the most-recently-bumped unassigned variable, keeping
            // decisions O(1) amortized.
            if !vsids.contains(var) {
                vsids.insert(var);
            }
            if use_chb && !chb.contains(var) {
                chb.insert(var);
            }
            if use_vmtf {
                vmtf.notify_unassigned(var);
            }
        });
    }

    /// Backtrack to a given level without saving phases.
    ///
    /// Returns the rollback boundary, exactly like
    /// [`Self::backtrack_with_phase_saving`]; the only difference between the
    /// two is that this one does not record the discarded polarities.
    ///
    /// In particular it must still hand the freed variables back to the decision
    /// heaps. `pick_branch_var` pops candidates *destructively*, so a variable
    /// unassigned without being re-inserted is lost to the search for good.
    /// `solve_with_assumptions` ends every probe on this path, so each probe used
    /// to drain the heaps a little further; once they ran dry the next probe had
    /// nothing left to branch on and reported `Sat` over a partial assignment —
    /// a model with `Undef` entries that falsified clauses the search had never
    /// even looked at. The vivification and distillation probes in
    /// `learn.rs` unwind through here too, with the same consequence.
    pub(super) fn backtrack(&mut self, level: u32) -> usize {
        let mut unassigned_vars = Vec::new();

        let lrb = &mut self.lrb;
        self.trail.backtrack_to_with_callback(level, |lit| {
            let var = lit.var();
            lrb.unassign(var);
            unassigned_vars.push(var);
        });

        for var in unassigned_vars {
            if !self.vsids.contains(var) {
                self.vsids.insert(var);
            }
            if !self.chb.contains(var) {
                self.chb.insert(var);
            }
        }

        // `backtrack_to_with_callback` no longer returns the rollback boundary
        // (main's alloc-free variant); derive it from the post-backtrack trail.
        self.trail.assignments().len()
    }

    /// Compute the Luby sequence value for index i (1-indexed: luby(1)=1, luby(2)=1, ...)
    /// Sequence: 1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 4, 8, ...
    /// For 0-indexed input, we add 1 internally.
    pub(super) fn luby(i: u64) -> u64 {
        let i = i + 1; // Convert to 1-indexed

        // Find k such that 2^k - 1 >= i
        let mut k = 1u32;
        while (1u64 << k) - 1 < i {
            k += 1;
        }

        let seq_len = (1u64 << k) - 1;

        if i == seq_len {
            // i is exactly 2^k - 1, return 2^(k-1)
            1u64 << (k - 1)
        } else {
            // Recurse: luby(i) = luby(i - (2^(k-1) - 1))
            // The sequence up to 2^k - 1 is: luby(1..2^(k-1)-1), luby(1..2^(k-1)-1), 2^(k-1)
            let half_len = (1u64 << (k - 1)) - 1;
            if i <= half_len {
                Self::luby(i - 1) // Already 0-indexed internally
            } else if i <= 2 * half_len {
                Self::luby(i - half_len - 1)
            } else {
                1u64 << (k - 1)
            }
        }
    }

    /// Reuse-trail restart (Marijn Heule / cadical): instead of backtracking to
    /// the root on every restart, backtrack only as far as the highest level
    /// whose decision variable would be re-decided anyway (activity >= the
    /// next variable to decide). This preserves the optimal decision prefix so
    /// the restart does not throw away and re-derive the whole trail — the main
    /// reason frequent restarts were counterproductive here.
    pub(super) fn reuse_trail(&self) -> u32 {
        // Only meaningful under VSIDS scoring (the default); under CHB/LRB the
        // VSIDS heap does not reflect the active branching order.
        if self.config.use_chb_branching || self.config.use_lrb_branching {
            return 0;
        }
        if !self.config.reuse_trail {
            return 0;
        }
        let level = self.trail.decision_level();
        if level <= 1 {
            return 0;
        }
        // Next variable to decide = top of the VSIDS heap; its activity is the
        // reuse threshold (decisions with at least that activity are kept).
        let Some(next_var) = self.vsids.peek_max() else {
            return 0;
        };
        let threshold = self.vsids.activity(next_var);
        let mut reuse = 0u32;
        for l in 1..=level {
            let Some(dec_var) = self.trail.decision_var_at_level(l) else {
                break;
            };
            if self.vsids.activity(dec_var) >= threshold {
                reuse = l;
            } else {
                break;
            }
        }
        reuse
    }

    /// cadical `stabilizing()`: switch focused/stable modes when the current
    /// mode's tick (propagation) count reaches `lim_stabilize`, swapping the
    /// per-mode glue averages and growing the interval quadratically
    /// (`stabilize_base × phase²`). On entering stable mode the reluctant
    /// (Luby) restart trigger is enabled; on entering focused it is disabled
    /// (focused mode uses the Glucose EMA condition instead).
    pub(super) fn check_stabilize(&mut self) {
        if !self.config.enable_stabilize {
            return;
        }
        let current_ticks = if self.stable {
            self.ticks_stable
        } else {
            self.ticks_focused
        };
        // First switch is conflict-based (ticks have barely accumulated);
        // thereafter tick-based, like cadical.
        let ready = if self.stabphases == 0 {
            self.ticks_focused >= self.config.stabilize_base
        } else {
            current_ticks >= self.lim_stabilize
        };
        if !ready {
            return;
        }
        // Swap per-mode averages and switch mode.
        core::mem::swap(&mut self.glue_current, &mut self.glue_saved);
        self.stable = !self.stable;
        self.stabphases = self.stabphases.saturating_add(1);
        // Quadratic growth of the next phase length (cadical `next_delta =
        // inc × stabphases²`), measured in the new mode's ticks.
        let next_delta = self
            .config
            .stabilize_base
            .saturating_mul(self.stabphases)
            .saturating_mul(self.stabphases);
        let new_mode_ticks = if self.stable {
            self.ticks_stable
        } else {
            self.ticks_focused
        };
        self.lim_stabilize = new_mode_ticks.saturating_add(next_delta);
        // Enable/disable the reluctant (Luby) restart trigger for stable mode.
        if self.stable {
            self.reluctant.enable(1024, 1 << 20);
        } else {
            self.reluctant.disable();
        }
    }

    /// Restart
    pub(super) fn restart(&mut self) {
        self.stats.restarts += 1;

        // Best-phase tracking: snapshot the current (pre-backtrack) trail when
        // it is the longest reached so far. The trail holds the just-explored
        // partial assignment; remembering its polarities lets a later rephase
        // refocus the search near the best-known region (cadical's "best"
        // phase array — the one genuinely missing SAT-side phase signal).
        let trail_size = self.trail.size();
        if trail_size > self.best_trail_size {
            self.best_trail_size = trail_size;
            self.best_phase.resize(self.num_vars, false);
            for &lit in self.trail.assignments() {
                self.best_phase[lit.var().index()] = lit.is_pos();
            }
        }

        self.backtrack_with_phase_saving(self.reuse_trail());

        // Rephase: periodically flip the global polarity so the next descent
        // explores the complementary phase region instead of re-deriving the
        // previous trail. Alternates with restoring the best-known phase to
        // refocus near the longest trail. Without this, frequent (LBD) restarts
        // just redo work and inflate the conflict count.
        // Rephase fires only in stable mode (cadical-style): stable mode runs
        // long Luby intervals where refocusing the phase has room to compound,
        // whereas in focused mode (frequent Glucose restarts) rephasing just
        // discards the memoized phase and the search re-derives it. Measured:
        // ungated rephase regresses broadly; stable-gated rephase is neutral.
        if self.config.rephase_interval > 0
            && self.stable
            && self
                .stats
                .restarts
                .is_multiple_of(u64::from(self.config.rephase_interval))
        {
            self.rephase_count += 1;
            if self.rephase_count % 2 == 1 && self.best_trail_size > 0 {
                // Restore the best partial assignment's polarities.
                let n = self.best_phase.len().min(self.phase.len());
                self.phase[..n].copy_from_slice(&self.best_phase[..n]);
                self.phase_inverted = false;
            } else {
                self.phase_inverted = !self.phase_inverted;
            }
        }

        // Calculate next restart threshold based on strategy
        match self.config.restart_strategy {
            RestartStrategy::Luby => {
                self.luby_index += 1;
                // Cap the Luby value: the sequence grows as 2^k, so on long runs
                // the restart interval explodes into multi-10k-conflict grinds
                // (a 3-30x slowdown vs cadical on r3sat n300/n350). Capping
                // keeps restarts regular without losing Luby's short-window
                // structure. Mode-dependent under the stable/focused schedule:
                // focused = frequent (focused_luby_cap), stable = rare (uncapped).
                let cap = if self.config.enable_stabilize {
                    if self.stable {
                        0
                    } else {
                        self.config.focused_luby_cap
                    }
                } else {
                    self.config.luby_cap
                };
                let luby = if cap == 0 {
                    Self::luby(self.luby_index)
                } else {
                    Self::luby(self.luby_index).min(cap)
                };
                self.restart_threshold = self.stats.conflicts + luby * self.config.restart_interval;
            }
            RestartStrategy::Geometric => {
                let current_interval = if self.restart_threshold > self.stats.conflicts {
                    self.restart_threshold - self.stats.conflicts
                } else {
                    self.config.restart_interval
                };
                let next_interval =
                    (current_interval as f64 * self.config.restart_multiplier) as u64;
                self.restart_threshold = self.stats.conflicts + next_interval;
            }
            RestartStrategy::Glucose => {
                // LBD-driven restart: the restart *decision* is made in the solve
                // loop (fire only when the fast LBD EMA exceeds the slow one).
                // Here we just enforce a minimum gap between restarts
                // (`restart_interval`) so the solver does not thrash, then wait
                // for the next degradation.
                self.restart_threshold = self.stats.conflicts + self.config.restart_interval;
            }
            RestartStrategy::LocalLbd => {
                // Local restarts based on LBD
                // Check if we should do a local restart
                self.conflicts_since_local_restart += 1;

                if self.conflicts_since_local_restart >= 50 && self.should_local_restart() {
                    // Perform local restart - backtrack to a safe level, not to 0
                    let local_level = self.compute_local_restart_level();
                    self.backtrack_with_phase_saving(local_level);
                    self.conflicts_since_local_restart = 0;
                    // Reset recent LBD for next window
                    self.recent_lbd_sum = 0;
                    self.recent_lbd_count = 0;
                } else {
                    // Standard restart if too many conflicts
                    let current_interval = if self.restart_threshold > self.stats.conflicts {
                        self.restart_threshold - self.stats.conflicts
                    } else {
                        self.config.restart_interval
                    };
                    self.restart_threshold = self.stats.conflicts + current_interval;
                }
                return; // Don't do full backtrack to 0
            }
        }

        // Re-add all unassigned variables to VSIDS heap
        for i in 0..self.num_vars {
            let var = Var::new(i as u32);
            if !self.trail.is_assigned(var) && !self.vsids.contains(var) {
                self.vsids.insert(var);
            }
        }
    }

    /// Check if we should perform a local restart
    /// Returns true if recent average LBD is significantly higher than global average
    pub(super) fn should_local_restart(&self) -> bool {
        if self.recent_lbd_count < 50 || self.global_lbd_count < 100 {
            return false;
        }

        let recent_avg = self.recent_lbd_sum / self.recent_lbd_count.max(1);
        let global_avg = self.global_lbd_sum / self.global_lbd_count.max(1);

        // Local restart if recent average is 1.25x higher than global average
        recent_avg * 4 > global_avg * 5
    }

    /// Compute the level to backtrack to for local restart
    /// Use a level that preserves some of the search progress
    pub(super) fn compute_local_restart_level(&self) -> u32 {
        let current_level = self.trail.decision_level();

        // Backtrack to about 20% of current depth to preserve some work
        if current_level > 5 {
            current_level / 5
        } else {
            0
        }
    }

    /// Seed the internal xorshift64 PRNG from a user-supplied `:random-seed`.
    ///
    /// The raw seed is mixed through a splitmix64 step before it becomes the
    /// xorshift state, because xorshift64 has a fixed point at `0`: a raw seed of
    /// `0` (the single most common user choice) would otherwise disable phase
    /// randomization entirely.  The mixing also spreads nearby seeds (`1`, `2`,
    /// `3`, …) into well-separated states so consecutive seeds explore genuinely
    /// different search orders.  A seed of `0` maps to the historical default
    /// state, so `set_random_seed(0)` reproduces the out-of-the-box behaviour.
    pub fn set_random_seed(&mut self, seed: u64) {
        self.rng_state = Self::seed_to_rng_state(seed);
    }

    /// Derive a nonzero xorshift64 state from a user seed via one splitmix64
    /// round.  A seed of `0` (or any input that mixes to `0`) falls back to the
    /// solver's historical default state so default behaviour is preserved.
    #[must_use]
    pub(crate) fn seed_to_rng_state(seed: u64) -> u64 {
        const DEFAULT_STATE: u64 = 0x853c_49e6_748f_ea9b;
        if seed == 0 {
            return DEFAULT_STATE;
        }
        let mut z = seed.wrapping_add(0x9E37_79B9_7F4A_7C15);
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^= z >> 31;
        if z == 0 { DEFAULT_STATE } else { z }
    }

    /// Generate a random u64 using xorshift64
    pub(super) fn rand_u64(&mut self) -> u64 {
        let mut x = self.rng_state;
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        self.rng_state = x;
        x
    }

    /// Generate a random f64 in [0, 1)
    pub(super) fn rand_f64(&mut self) -> f64 {
        const MAX: f64 = u64::MAX as f64;
        (self.rand_u64() as f64) / MAX
    }

    /// Generate a random boolean with given probability of being true
    pub(super) fn rand_bool(&mut self, probability: f64) -> bool {
        self.rand_f64() < probability
    }
}
