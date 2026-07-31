//! Conflict detection and proof-forest explanation.
//!
//! Split out of `euf/solver.rs` along the "what justifies a derived equality"
//! seam.  Nothing here mutates the e-graph; the mutating half lives in
//! [`super::congruence`].
//!
//! # The one invariant this module exists to protect
//!
//! An explanation is either **complete** — the conjunction of the returned
//! reason terms really does entail `a = b` — or it is **absent**.  There is no
//! third outcome.  A partial explanation is not a weaker conflict clause, it is
//! an unsound one: the clause asserts that the literals it *does* name are by
//! themselves contradictory, which is false whenever a justification was
//! dropped.  Every path that could fail therefore returns `None` from
//! [`EufSolver::try_explain_equality`], and [`EufSolver::check_conflicts`]
//! answers a `None` with the conservative core over *all* currently asserted
//! reasons — weaker, but valid.

use super::{EufSolver, MergeReason, ordered_pair};
#[allow(unused_imports)]
use crate::prelude::*;
use core::mem;
use oxiz_core::ast::TermId;
use smallvec::SmallVec;

impl EufSolver {
    /// Check for conflicts.
    ///
    /// Returns the reason terms of a violated disequality together with a
    /// justification of the equality that violates it.  The justification is
    /// always *complete*: when congruence closure cannot produce one — an
    /// invariant violation, see `try_explain_equality` — the result falls back
    /// to `all_asserted_reasons`, the core over every literal EUF currently
    /// holds.  That core is valid by construction (the assertion set
    /// really is contradictory, or there would be no conflict) and is the only
    /// admissible substitute: any *smaller* set would claim a refutation that its
    /// members do not support.
    pub fn check_conflicts(&mut self) -> Option<Vec<TermId>> {
        // Disequality violations are detected eagerly — at the merge (or the
        // assert_diseq) that causes them, recorded in `pending_diseq_conflict`.
        // So this is O(1): surface the pending violation, or report none. The
        // old O(diseqs) full scan on every theory check was the dominant EUF cost.
        let conflict_idx = self.pending_diseq_conflict?;

        let (lhs, rhs, reason) = {
            let d = &self.diseqs[conflict_idx as usize];
            (d.lhs, d.rhs, d.reason)
        };

        // Borrow of self.diseqs is fully released here.
        let mut explanation = match self.try_explain_equality(lhs, rhs) {
            Some(expl) => expl,
            None => self.all_asserted_reasons(),
        };
        if !explanation.contains(&reason) {
            explanation.push(reason);
        }
        Some(explanation)
    }

    /// Every reason term EUF is currently resting on: the label of every live
    /// proof-forest edge plus the reason of every live disequality.
    ///
    /// This is the conservative conflict core.  It is sound whenever a conflict
    /// exists (the full assertion set is then contradictory by definition) and it
    /// is deterministic — both sources are `Vec`s walked in index order, so the
    /// clause, and hence the search, does not depend on hash iteration order.
    ///
    /// Reserved for the "explanation unavailable" path that
    /// [`Self::try_explain_equality`] declares unreachable; it is the weakest
    /// useful lemma, so reaching it costs search progress but never soundness.
    pub(super) fn all_asserted_reasons(&self) -> Vec<TermId> {
        let mut out: Vec<TermId> = Vec::new();
        let mut seen: FxHashSet<TermId> = FxHashSet::default();
        for edges in &self.proof_forest {
            for edge in edges {
                if let MergeReason::Assertion(term_id) = edge.reason
                    && term_id.raw() != 0
                    && seen.insert(term_id)
                {
                    out.push(term_id);
                }
            }
        }
        for diseq in &self.diseqs {
            if diseq.reason.raw() != 0 && seen.insert(diseq.reason) {
                out.push(diseq.reason);
            }
        }
        out
    }

    /// Public entry point to the congruence-closure explanation engine.
    ///
    /// Returns the asserted reason terms whose conjunction implies `a = b`,
    /// with every congruence step on the proof path expanded down to the
    /// argument equalities that justify it.  This is what a *client* theory
    /// needs when it propagates an EUF-derived equality into another solver:
    /// the propagated fact is not itself an asserted literal, so a conflict
    /// resting on it must be blamed on this explanation instead.
    ///
    /// An empty result is meaningful only when `a == b` (the two term ids were
    /// hash-consed onto the same node, so the equality holds structurally and
    /// needs no justification).  When `a != b` an empty result means no complete
    /// proof was found — the caller must treat the equality as *unjustifiable*
    /// and refrain from propagating it rather than propagate an unexplainable
    /// fact.  Callers that want to tell "no justification" from "justified by
    /// nothing" apart should use [`Self::try_explain_eq`].
    pub fn explain_eq(&mut self, a: u32, b: u32) -> Vec<TermId> {
        self.try_explain_eq(a, b).unwrap_or_default()
    }

    /// Fallible form of [`Self::explain_eq`].
    ///
    /// `Some(reasons)` is a **complete** justification of `a = b`; `None` means
    /// congruence closure could not produce one (the nodes are not equal, or an
    /// invariant of the proof forest is broken).  Never returns a partial answer.
    pub fn try_explain_eq(&mut self, a: u32, b: u32) -> Option<Vec<TermId>> {
        self.try_explain_equality(a, b)
    }

    /// Explain why two nodes are equal, or report that it cannot be done.
    ///
    /// Searches the proof forest for a path from `a` to `b` and collects the
    /// asserted equalities labelling that path. A congruence edge on the path is
    /// only justified once its argument equalities are justified as well; those
    /// sub-goals are pushed onto an explicit worklist (`explain_todo`) instead of
    /// being discharged by a recursive call, so the routine runs in constant stack
    /// space however deeply the terms nest.
    ///
    /// Every pair is expanded at most once (tracked in `explain_enqueued`). That
    /// both avoids repeating identical searches and bounds the loop by the number
    /// of distinct node pairs, so no arrangement of proof edges can make it
    /// diverge. Since the collected reasons form a set, re-encountering an
    /// already-expanded pair cannot contribute anything new.
    ///
    /// # Failure is reported, never absorbed
    ///
    /// Three things can go wrong, and each yields `None` rather than a shorter
    /// list:
    ///
    /// 1. **The BFS finds no path** between two nodes the union-find says are
    ///    equal.  Every applied union appends exactly one edge pair, and `pop()`
    ///    rewinds edges and unions together, so the forest spans each class and
    ///    this cannot happen — hence the `debug_assert!`.  It is kept as a live
    ///    check because the alternative, `continue`, silently returned a partial
    ///    explanation.
    /// 2. **A congruence edge names a node that no longer exists**, or two
    ///    applications of different arity.  Equal canonical signatures have equal
    ///    length, so this too is an invariant violation.
    /// 3. **An argument of one side has no partner in the same class on the
    ///    other.**  The arguments are matched as a multiset rather than
    ///    positionally, because a commutative symbol's canonical signature is
    ///    sorted and its two applications may list their arguments in different
    ///    orders.  Equal canonical signatures guarantee a perfect matching
    ///    exists; failing to find one means the edge was not a congruence.
    ///
    /// The scratch buffers are moved out of `self` via `mem::take` at entry and
    /// restored at exit — on the failure path as well — so their heap capacity is
    /// retained across calls.
    pub(super) fn try_explain_equality(&mut self, a: u32, b: u32) -> Option<Vec<TermId>> {
        if a == b {
            return Some(Vec::new());
        }

        let n = self.proof_forest.len();
        // Guard against out-of-bounds indices.
        if (a as usize) >= n || (b as usize) >= n {
            return None;
        }
        // Nothing to explain if the nodes are not equal in the first place; a
        // non-empty answer here would be a fabrication.
        if !self.uf.same_no_compress(a, b) {
            return None;
        }

        if let Some(cached) = self.expl_cache.get(&ordered_pair(a, b)) {
            return Some(cached.clone());
        }

        // Take reusable buffers out of self so the shared reads on `self.nodes`,
        // `self.proof_forest` and `self.uf` below do not conflict with them.
        let mut settled = mem::take(&mut self.explain_visited);
        let mut seen_gen = mem::take(&mut self.explain_seen_gen);
        let mut dist = mem::take(&mut self.explain_dist);
        let mut heap = mem::take(&mut self.explain_heap);
        let mut parent = mem::take(&mut self.explain_parent);
        // Generation stamps never wrap in practice; roll the buffers over
        // defensively so a wrap can never make stale entries look live.
        if self.explain_generation >= u32::MAX - 1 {
            self.explain_generation = 0;
            settled.iter_mut().for_each(|v| *v = 0);
            seen_gen.iter_mut().for_each(|v| *v = 0);
        }
        let mut generation = self.explain_generation;
        let mut todo = mem::take(&mut self.explain_todo);
        let mut enqueued = mem::take(&mut self.explain_enqueued);

        todo.clear();
        enqueued.clear();
        enqueued.insert(ordered_pair(a, b));
        todo.push((a, b));

        let mut reasons: Vec<TermId> = Vec::new();
        let mut seen_reasons: FxHashSet<TermId> = FxHashSet::default();
        let mut path: Vec<(u32, usize)> = Vec::new();
        let mut complete = true;

        'goals: while let Some((from, to)) = todo.pop() {
            // Bottleneck (minimax) search: among all paths from -> to, take one
            // whose *latest* edge is as early as possible (smallest max stamp).
            // Plain BFS minimises hop count instead, and a short path may route
            // through merges made long after `from = to` was already derived —
            // exactly the circular route that used to produce truncated
            // explanations and spurious UNSAT. Minimising the maximum stamp
            // reconstructs the derivation-time path, so every congruence edge on
            // it is justified strictly earlier (well-founded recursion).
            //
            // The per-node tables are generation-stamped rather than cleared: one
            // conflict explanation runs this search once per pair on the worklist,
            // and re-zeroing O(nodes) entries each time dominated the whole solver.
            if dist.len() < n {
                dist.resize(n, u64::MAX);
                parent.resize(n, None);
                settled.resize(n, 0);
                seen_gen.resize(n, 0);
            }
            generation += 1;
            heap.clear();
            dist[from as usize] = 0;
            seen_gen[from as usize] = generation;
            heap.push(core::cmp::Reverse((0u64, from)));

            let mut found = false;
            while let Some(core::cmp::Reverse((d, node))) = heap.pop() {
                if settled[node as usize] == generation {
                    continue;
                }
                settled[node as usize] = generation;
                if node == to {
                    found = true;
                    break;
                }

                let Some(edges) = self.proof_forest.get(node as usize) else {
                    continue;
                };
                for (idx, edge) in edges.iter().enumerate() {
                    let other_idx = edge.other as usize;
                    if other_idx >= n || settled[other_idx] == generation {
                        continue;
                    }
                    // Lexicographic relaxation: first minimise the latest stamp on
                    // the path (soundness), then the hop count (small reason set).
                    let nd_stamp = ((d >> 32) as u32).max(edge.stamp);
                    let nd_hops = (d as u32) + 1;
                    let nd = (u64::from(nd_stamp) << 32) | u64::from(nd_hops);
                    let known = if seen_gen[other_idx] == generation {
                        dist[other_idx]
                    } else {
                        u64::MAX
                    };
                    if nd < known {
                        seen_gen[other_idx] = generation;
                        dist[other_idx] = nd;
                        parent[other_idx] = Some((node, idx));
                        heap.push(core::cmp::Reverse((nd, edge.other)));
                    }
                }
            }

            if !found {
                // Failure mode (1): the proof forest does not span the class.
                debug_assert!(
                    false,
                    "no proof-forest path between nodes {from} and {to} that the \
                     union-find reports as equal: every applied union appends an \
                     edge pair and pop() rewinds both together, so the forest must \
                     span every class"
                );
                complete = false;
                break 'goals;
            }

            // Walk the parent chain back from `to` to `from`. Stop at `from`
            // (its parent may be a leftover from an earlier generation) and guard
            // on the generation stamp so a stale entry never sends us off-path.
            path.clear();
            let mut current = to;
            while current != from {
                if seen_gen[current as usize] != generation {
                    break;
                }
                let Some((prev, edge_idx)) = parent[current as usize] else {
                    break;
                };
                path.push((prev, edge_idx));
                current = prev;
            }

            for &(prev, edge_idx) in &path {
                let Some(edge) = self
                    .proof_forest
                    .get(prev as usize)
                    .and_then(|edges| edges.get(edge_idx))
                else {
                    // Failure mode (2): the path referenced an edge that is gone.
                    debug_assert!(
                        false,
                        "proof-forest edge {edge_idx} of node {prev} vanished \
                         between the search and the path walk"
                    );
                    complete = false;
                    break 'goals;
                };

                match edge.reason {
                    MergeReason::Assertion(term_id) => {
                        if term_id.raw() != 0 && seen_reasons.insert(term_id) {
                            reasons.push(term_id);
                        }
                    }
                    MergeReason::Congruence { term1, term2 } => {
                        // The congruence holds because the arguments are pairwise
                        // equal — schedule each argument pair for explanation.
                        let (Some(node1), Some(node2)) = (
                            self.nodes.get(term1 as usize),
                            self.nodes.get(term2 as usize),
                        ) else {
                            debug_assert!(
                                false,
                                "congruence edge names missing node(s) {term1}/{term2}"
                            );
                            complete = false;
                            break 'goals;
                        };
                        // Cloned so the `self.uf` reads in the matching loop do not
                        // overlap the `self.nodes` borrow.  Arities are tiny.
                        let args1: SmallVec<[u32; 4]> = node1.args.clone();
                        let args2: SmallVec<[u32; 4]> = node2.args.clone();
                        if args1.len() != args2.len() {
                            // Failure mode (2): equal signatures have equal arity.
                            debug_assert!(
                                false,
                                "congruence edge between applications of different \
                                 arity ({} vs {})",
                                args1.len(),
                                args2.len()
                            );
                            complete = false;
                            break 'goals;
                        }
                        if !self.schedule_congruence_subgoals(
                            &args1,
                            &args2,
                            n,
                            &mut todo,
                            &mut enqueued,
                        ) {
                            // Failure mode (3): no argument matching exists.
                            debug_assert!(
                                false,
                                "congruence edge between {term1} and {term2} has an \
                                 argument with no equal partner: the edge does not \
                                 justify the equality it labels"
                            );
                            complete = false;
                            break 'goals;
                        }
                    }
                }
            }
        }

        // Restore buffers so the next call reuses their capacity — on the failure
        // path too, otherwise a single failure would strand them empty forever.
        self.explain_generation = generation;
        self.explain_visited = settled;
        self.explain_seen_gen = seen_gen;
        self.explain_dist = dist;
        self.explain_heap = heap;
        self.explain_parent = parent;
        self.explain_todo = todo;
        self.explain_enqueued = enqueued;

        if !complete {
            return None;
        }
        self.expl_cache.insert(ordered_pair(a, b), reasons.clone());
        Some(reasons)
    }

    /// Match the arguments of two congruent applications as a multiset over
    /// equivalence classes and schedule each unequal pair for explanation.
    ///
    /// Positional matching is wrong for a commutative symbol: its canonical
    /// signature is *sorted*, so `f(a, b)` and `f(b, a)` match on signature while
    /// `args[0]` of one is equal to `args[1]` of the other.  Greedy matching by
    /// class is exact here — equal canonical signatures mean the two argument
    /// class-multisets are equal (later merges only coarsen them), so every
    /// argument does have an unused partner, and taking any one of them cannot
    /// strand a later argument.
    ///
    /// Returns `false` if some argument has no partner, i.e. the edge does not
    /// justify a congruence at all.
    fn schedule_congruence_subgoals(
        &self,
        args1: &[u32],
        args2: &[u32],
        node_count: usize,
        todo: &mut Vec<(u32, u32)>,
        enqueued: &mut FxHashSet<(u32, u32)>,
    ) -> bool {
        let mut matched: SmallVec<[bool; 8]> = SmallVec::from_elem(false, args2.len());
        for &arg1 in args1 {
            let partner = (0..args2.len()).find(|&j| {
                !matched[j] && (args2[j] == arg1 || self.uf.same_no_compress(arg1, args2[j]))
            });
            let Some(pos) = partner else {
                return false;
            };
            matched[pos] = true;
            let arg2 = args2[pos];
            if arg1 != arg2
                && (arg1 as usize) < node_count
                && (arg2 as usize) < node_count
                && enqueued.insert(ordered_pair(arg1, arg2))
            {
                todo.push((arg1, arg2));
            }
        }
        true
    }
}
