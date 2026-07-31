//! EUF Theory Solver
//!
//! The solver is split across three files along the seams of what each one is
//! responsible for:
//!
//! * this module — the e-graph's data model (`ENode`, the trails, the context
//!   stack), term interning, and the [`Theory`] implementation (`push`/`pop`/
//!   `reset`);
//! * [`congruence`] — everything that *mutates* the e-graph: use lists,
//!   signature-table maintenance and merge propagation;
//! * [`explain`] — everything that *justifies* a derived equality: conflict
//!   detection and proof-forest explanation.
//!
//! Reference: Z3's `euf_egraph.cpp` for the overall congruence-closure design.

use super::union_find::UnionFind;
#[allow(unused_imports)]
use crate::prelude::*;
use crate::theory::{Theory, TheoryId, TheoryResult};
use oxiz_core::ast::TermId;
use oxiz_core::error::Result;
use smallvec::SmallVec;

mod congruence;
mod explain;
#[cfg(test)]
mod tests;

/// Capacity of the explanation cache: how many (a, b) -> reasons entries to retain.
/// Each entry records the BFS-derived reason set for a pair of E-graph node indices.
/// 1024 covers the vast majority of repeated sub-explanation queries that arise from
/// congruence closure without consuming significant memory.
const EUF_EXPL_CACHE_CAPACITY: usize = 1024;

/// Records an insertion into sig_table or fingerprint_table for undo on pop().
#[derive(Debug, Clone)]
enum SigTrailEntry {
    /// Inserted `key -> node` into sig_table; undo removes `key` and restores
    /// `node_sig_key[node]` to `None` (the state before this registration).
    InsertedSig {
        key: (u32, SmallVec<[u32; 4]>),
        node: u32,
    },
    /// Removed `key -> node` from sig_table because the node's signature changed
    /// in `propagate`; undo re-inserts `key -> node` and restores
    /// `node_sig_key[node] = Some(key)`.
    RemovedSig {
        key: (u32, SmallVec<[u32; 4]>),
        node: u32,
    },
    /// Pushed node_idx into fingerprint_table[fp]; undo removes it from the bucket.
    InsertedFingerprint { fp: ENodeFingerprint, node_idx: u32 },
}

/// Function properties for dynamic arity support
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct FunctionProperties {
    /// Is the function associative? (e.g., +, *, and, or)
    pub associative: bool,
    /// Is the function commutative? (e.g., +, *, and, or)
    pub commutative: bool,
    /// Does the function have an identity element?
    pub has_identity: bool,
}

/// 64-bit fingerprint for fast congruence pre-filtering.
/// Before doing full signature comparison in the congruence table,
/// we compare fingerprints first (cheap u64 comparison) to avoid
/// expensive argument-level equality checks.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
pub struct ENodeFingerprint(u64);

impl ENodeFingerprint {
    /// Compute a fingerprint from a function symbol and canonical argument representatives.
    /// Uses a fast multiplicative hash to combine func and args into a single u64.
    #[must_use]
    pub fn compute(func: u32, args: &[u32]) -> Self {
        let mut h = func as u64;
        for &arg in args {
            h = h
                .wrapping_mul(0x517c_c1b7_2722_0a95)
                .wrapping_add(arg as u64);
        }
        Self(h)
    }

    /// Return the raw fingerprint value
    #[must_use]
    pub fn raw(self) -> u64 {
        self.0
    }
}

/// Congruence-closed view of one interned function application, produced by
/// [`EufSolver::function_application_entries`] for model extraction.
///
/// All representatives are canonical equivalence-class node indices (taken
/// through `find`), so applications whose arguments are pairwise congruent share
/// identical `arg_reps`/`result_rep` and collapse onto the same value class.
#[derive(Debug, Clone)]
pub struct FuncAppEntry {
    /// Canonical class representative (node index) of each argument, in order.
    pub arg_reps: SmallVec<[u32; 4]>,
    /// Every `TermId` interned into each argument's equivalence class, in the
    /// same order as `arg_reps`.  A model builder can scan these to find a
    /// member that carries a concrete value.
    pub arg_class_terms: SmallVec<[Vec<TermId>; 4]>,
    /// Canonical class representative (node index) of the application result.
    pub result_rep: u32,
    /// Every `TermId` interned into the result's equivalence class.
    pub result_class_terms: Vec<TermId>,
}

/// A term node in the E-graph
#[derive(Debug, Clone)]
struct ENode {
    /// Function symbol index; `u32::MAX` (= `ENode::NO_FUNC`) means leaf (no application).
    /// Placed first so that the hot `func` discriminant is at offset 0 of the struct.
    func: u32,
    /// 64-bit fingerprint for fast congruence pre-filtering.
    /// Placed second (after the 4-byte func + 4-byte implicit pad) so it aligns to 8 bytes
    /// without additional padding waste.
    fingerprint: ENodeFingerprint,
    /// Arguments (indices into nodes)
    args: SmallVec<[u32; 4]>,
    /// The original term
    term: TermId,
}

impl ENode {
    /// Sentinel value meaning "no function symbol" (leaf node).
    const NO_FUNC: u32 = u32::MAX;

    /// Create a leaf node (no function application).
    fn leaf(term: TermId) -> Self {
        ENode {
            func: Self::NO_FUNC,
            fingerprint: ENodeFingerprint::default(),
            args: SmallVec::new(),
            term,
        }
    }

    /// Create a function application node.
    fn app(
        func: u32,
        args: SmallVec<[u32; 4]>,
        fingerprint: ENodeFingerprint,
        term: TermId,
    ) -> Self {
        debug_assert!(
            func != Self::NO_FUNC,
            "func must not be u32::MAX (reserved sentinel)"
        );
        ENode {
            func,
            fingerprint,
            args,
            term,
        }
    }

    /// Returns true if this node is a function application (not a leaf).
    #[inline]
    fn is_app(&self) -> bool {
        self.func != Self::NO_FUNC
    }
}

/// Disequality constraint
#[derive(Debug, Clone)]
struct Diseq {
    /// First term
    lhs: u32,
    /// Second term
    rhs: u32,
    /// Reason for the disequality
    reason: TermId,
}

/// A merge reason: why two nodes became equal
#[derive(Debug, Clone)]
enum MergeReason {
    /// Direct equality assertion
    Assertion(TermId),
    /// Congruence: f(a1,...,an) = f(b1,...,bn) because ai = bi for all i
    Congruence {
        /// The terms that became equal by congruence
        term1: u32,
        term2: u32,
    },
}

/// Normalize a node pair so that `(a, b)` and `(b, a)` map to the same key.
#[inline]
fn ordered_pair(a: u32, b: u32) -> (u32, u32) {
    if a <= b { (a, b) } else { (b, a) }
}

/// A merge edge in the proof forest
#[derive(Debug, Clone)]
struct MergeEdge {
    /// The other node in the merge
    other: u32,
    /// The reason for the merge
    reason: MergeReason,
}

/// EUF Theory Solver using congruence closure
#[derive(Debug)]
pub struct EufSolver {
    /// Union-Find for equivalence classes
    uf: UnionFind,
    /// E-nodes
    nodes: Vec<ENode>,
    /// Term to node index mapping.
    ///
    /// Every entry points at the node that was *created* for that term, and
    /// nodes are truncated in LIFO order by `pop()`, so the index-based `retain`
    /// there is exact.  An application is never mapped onto a pre-existing
    /// congruent node: see [`EufSolver::intern_app`].
    term_to_node: FxHashMap<TermId, u32>,
    /// Disequality constraints
    diseqs: Vec<Diseq>,
    /// Pending merges for congruence closure.
    ///
    /// Each entry carries the justification that will label the proof-forest edge
    /// once the merge is actually performed. The edge is *not* created at
    /// detection time: doing so would connect two nodes in the proof forest
    /// without performing the corresponding union, and a later merge joining the
    /// same two classes through a different route would then close a cycle in
    /// what must remain a spanning forest (see `propagate`).
    pending: Vec<(u32, u32, MergeReason)>,
    /// Use list: for each node, which applications use it as an argument.
    ///
    /// An application is registered on the *representative* of each argument, and
    /// `propagate` splices the absorbed root's list into the survivor's, so the
    /// invariant "`use_list[r]` holds every application with an argument in `r`'s
    /// class" holds for every root `r`.  Registering on the raw argument instead
    /// breaks it: an application interned while its argument was a non-root would
    /// never be re-canonicalized when that argument's class merged again, and the
    /// congruence would be missed.
    use_list: Vec<SmallVec<[u32; 8]>>,
    /// Signature table for congruence closure
    sig_table: FxHashMap<(u32, SmallVec<[u32; 4]>), u32>,
    /// For each node, the key under which it is currently registered in
    /// `sig_table` (`None` for leaf nodes and for app nodes merged into a
    /// congruent existing node on intern). `propagate` consults this to remove a
    /// node's *old* signature entry when its canonical arguments change, so that
    /// stale entries keyed by obsolete representatives never accumulate (the
    /// root cause of missed congruences / spurious sat). Parallel to `nodes`;
    /// truncated in lockstep on `pop`.
    node_sig_key: Vec<Option<(u32, SmallVec<[u32; 4]>)>>,
    /// Per-representative watch list of disequality indices: `diseq_watch[rep]`
    /// holds every asserted disequality with an endpoint currently in `rep`'s
    /// class. On a merge the loser class's watched disequalities are tested
    /// (both endpoints now equal -> conflict) and copied to the winner, so a
    /// violation is caught at the merge that causes it and `check_conflicts`
    /// never scans all disequalities. Mirrors the `use_list` migration + trailing.
    diseq_watch: Vec<Vec<u32>>,
    /// Undo trail for `diseq_watch` appends: the rep whose list was extended.
    diseq_watch_trail: Vec<u32>,
    /// Scope checkpoints into `diseq_watch_trail`, parallel to `sig_trail_limits`.
    diseq_watch_trail_limits: Vec<usize>,
    /// Index (into `diseqs`) of a disequality detected violated during a merge or
    /// at `assert_diseq`, awaiting `check_conflicts` to surface it. None = none.
    pending_diseq_conflict: Option<u32>,
    /// Saved `pending_diseq_conflict` per scope so `pop()` restores it: a
    /// violation found inside a popped scope retracts with the merge that caused it.
    pending_trail: Vec<Option<u32>>,
    /// Scope checkpoints into `pending_trail`.
    pending_trail_limits: Vec<usize>,
    /// Fingerprint table: maps fingerprint -> list of node indices with that fingerprint.
    /// Used as a fast pre-filter before full signature comparison in congruence checks.
    ///
    /// Invariant: every key of `sig_table` has its fingerprint present here, so
    /// "fingerprint absent" soundly implies "signature absent".
    fingerprint_table: FxHashMap<ENodeFingerprint, SmallVec<[u32; 4]>>,
    /// Context stack for push/pop
    context_stack: Vec<ContextState>,
    /// Proof forest: for each node, edges to explain equalities.
    /// SmallVec<[MergeEdge; 4]> avoids heap allocation for nodes with ≤4 proof edges,
    /// which covers the vast majority of E-graph nodes in practice.
    proof_forest: Vec<SmallVec<[MergeEdge; 4]>>,
    /// Function properties for dynamic arity support
    function_properties: FxHashMap<u32, FunctionProperties>,
    /// Reused queue for newly discovered propagations during congruence closure.
    propagation_buf: Vec<(u32, u32, MergeReason)>,
    /// Undo trail for sig_table and fingerprint_table insertions.
    sig_trail: Vec<SigTrailEntry>,
    /// Scope checkpoints into sig_trail, parallel to uf.trail_limits.
    sig_trail_limits: Vec<usize>,
    /// Undo trail for proof-forest edge insertions.
    ///
    /// Each entry is the node index onto whose `proof_forest` adjacency list an
    /// edge was pushed while a scope was active.  `pop()` replays these in LIFO
    /// order, popping exactly one edge off the recorded node's list, so that merge
    /// edges appended to *pre-existing* nodes during a popped scope are removed
    /// (truncation alone only reclaims edges belonging to nodes created in the
    /// scope, leaving stale edges on older nodes that would let `explain_equality`
    /// cite retracted assertions).
    proof_trail: Vec<u32>,
    /// Scope checkpoints into proof_trail, parallel to sig_trail_limits.
    proof_trail_limits: Vec<usize>,
    /// Undo trail for `use_list` appends.
    ///
    /// Each entry is the node index onto whose `use_list` an entry was pushed
    /// while a scope was active. `pop()` replays these in LIFO order, popping
    /// exactly one entry off the recorded node's list. This removes use-list
    /// entries appended to *pre-existing* nodes during a popped scope
    /// (truncation alone only reclaims the lists of nodes created in the scope,
    /// leaving stale entries on older nodes — which would corrupt congruence
    /// once a popped node index is reused by a later `intern`).
    use_list_trail: Vec<u32>,
    /// Scope checkpoints into use_list_trail, parallel to sig_trail_limits.
    use_list_trail_limits: Vec<usize>,
    /// Reusable BFS queue for explain_equality — avoids per-call VecDeque allocation.
    explain_queue: crate::prelude::VecDeque<u32>,
    /// Reusable visited flags for explain_equality — resized to proof_forest.len() and cleared at entry.
    explain_visited: Vec<bool>,
    /// Reusable parent-pointer table for explain_equality — parallel to explain_visited.
    explain_parent: Vec<Option<(u32, usize)>>,
    /// Reusable worklist of node pairs whose equality still has to be explained.
    ///
    /// `explain_equality` discharges the argument sub-goals of a congruence edge
    /// through this list instead of recursing, so its stack consumption is
    /// constant no matter how deeply the terms nest.
    explain_todo: Vec<(u32, u32)>,
    /// Pairs already scheduled on `explain_todo` during the current explanation,
    /// normalized via `ordered_pair`. Expanding every pair at most once avoids
    /// redundant path searches and bounds the worklist loop by the number of
    /// distinct node pairs.
    explain_enqueued: FxHashSet<(u32, u32)>,
    /// Bounded LRU cache for explanation results.
    ///
    /// Maps `(a, b)` node-index pairs to the `Vec<TermId>` reason set returned by
    /// `try_explain_equality`.  Only *complete* explanations are stored.  The
    /// cache is valid as long as the proof forest is unchanged; it is cleared
    /// eagerly whenever an edge is added (`propagate`), removed (`pop`), or the
    /// whole solver is `reset`, so a stale entry can never be observed.
    expl_cache: crate::lru_cache::LruCache<(u32, u32), Vec<TermId>>,
}

/// State to save for push/pop
#[derive(Debug, Clone)]
struct ContextState {
    num_nodes: usize,
    num_diseqs: usize,
}

impl Default for EufSolver {
    fn default() -> Self {
        Self::new()
    }
}

impl EufSolver {
    /// Create a new EUF solver
    #[must_use]
    pub fn new() -> Self {
        Self {
            uf: UnionFind::new(0),
            nodes: Vec::new(),
            term_to_node: FxHashMap::default(),
            diseqs: Vec::new(),
            pending: Vec::new(),
            use_list: Vec::new(),
            sig_table: FxHashMap::default(),
            node_sig_key: Vec::new(),
            diseq_watch: Vec::new(),
            diseq_watch_trail: Vec::new(),
            diseq_watch_trail_limits: Vec::new(),
            pending_diseq_conflict: None,
            pending_trail: Vec::new(),
            pending_trail_limits: Vec::new(),
            fingerprint_table: FxHashMap::default(),
            context_stack: Vec::new(),
            proof_forest: Vec::new(),
            function_properties: FxHashMap::default(),
            propagation_buf: Vec::new(),
            sig_trail: Vec::new(),
            sig_trail_limits: Vec::new(),
            proof_trail: Vec::new(),
            proof_trail_limits: Vec::new(),
            use_list_trail: Vec::new(),
            use_list_trail_limits: Vec::new(),
            explain_queue: crate::prelude::VecDeque::new(),
            explain_visited: Vec::new(),
            explain_parent: Vec::new(),
            explain_todo: Vec::new(),
            explain_enqueued: FxHashSet::default(),
            expl_cache: crate::lru_cache::LruCache::new(EUF_EXPL_CACHE_CAPACITY),
        }
    }

    /// Intern a term, returning its node index
    #[inline]
    pub fn intern(&mut self, term: TermId) -> u32 {
        if let Some(&idx) = self.term_to_node.get(&term) {
            return idx;
        }

        let idx = self.nodes.len() as u32;
        self.nodes.push(ENode::leaf(term));
        self.uf.add();
        self.use_list.push(SmallVec::new());
        self.proof_forest.push(SmallVec::new());
        self.node_sig_key.push(None);
        self.term_to_node.insert(term, idx);
        idx
    }

    /// Intern a function application.
    ///
    /// A new term **always** gets a node of its own.  When the signature table
    /// already holds a congruent application the two are joined by a *merge*, not
    /// by sharing a node index.
    ///
    /// Sharing the index was a backtracking bug: the congruence rests on the
    /// argument classes that hold right now, but `term_to_node` survives `pop()`
    /// (its entries are dropped by node index, and the borrowed index belongs to
    /// an older, still-live node).  After `a = 0` was retracted, `f(0)` therefore
    /// stayed pinned to `f(a)`'s node — so `f(0)` had no node, no use-list entry
    /// and no signature of its own, the congruence `f(f(a)) = f(0)` could never be
    /// discovered, and the solver answered `sat` for
    /// `a ∈ {0,1} ∧ f(0),f(1) ∈ {0,1} ∧ f(f(a)) > 1`, which has no model.
    /// Merging instead keeps the equality on the trail, where `pop()` retracts it
    /// with everything else.  Reference: Z3's `euf_egraph.cpp`, where
    /// `egraph::mk` calls `push_merge(n, n2)` on a congruence-table hit.
    #[inline]
    pub fn intern_app(
        &mut self,
        term: TermId,
        func: u32,
        args: impl IntoIterator<Item = u32>,
    ) -> u32 {
        if let Some(&idx) = self.term_to_node.get(&term) {
            return idx;
        }

        let args: SmallVec<[u32; 4]> = args.into_iter().collect();

        // Flatten for associative functions
        let flattened_args = self.flatten_args(func, &args);

        // Canonicalize arguments (handles commutativity and finds canonical reps)
        let canonical_args = self.canonicalize_args(func, &flattened_args);

        // Compute fingerprint for fast congruence pre-filtering
        let fp = ENodeFingerprint::compute(func, &canonical_args);

        let sig = (func, canonical_args);
        let congruent = self.lookup_valid_sig(&sig);

        let idx = self.nodes.len() as u32;
        self.nodes
            .push(ENode::app(func, flattened_args.clone(), fp, term));
        self.uf.add();
        self.use_list.push(SmallVec::new());
        self.proof_forest.push(SmallVec::new());
        // Record the key under which this node is registered in sig_table (None
        // when it will merge into a congruent existing node and so never publish
        // its own signature), so a later signature change in `propagate` can
        // remove exactly this entry.
        self.node_sig_key.push(if congruent.is_some() {
            None
        } else {
            Some(sig.clone())
        });
        self.term_to_node.insert(term, idx);

        // Register the application on the *representative* of each argument, so a
        // later merge of that class re-canonicalizes this node.  Trailed so pop()
        // removes these appends from pre-existing argument nodes (idx itself is
        // truncated wholesale).
        for &arg in &flattened_args {
            let arg_root = self.uf.find(arg);
            self.use_list_push(arg_root, idx);
        }

        match congruent {
            Some(existing) => {
                // The signature is already published under `existing`; leave the
                // entry alone (its undo record is a plain `remove`, so overwriting
                // would lose the older mapping on pop) and record the congruence
                // as a retractable merge instead.
                self.merge_congruent(idx, existing);
            }
            None => {
                self.insert_signature(func, sig.1, idx, fp);
            }
        }

        idx
    }

    /// Merge two equivalence classes
    #[inline]
    pub fn merge(&mut self, a: u32, b: u32, reason: TermId) -> Result<()> {
        // Any pending merge invalidates previously cached explanations because the
        // proof forest will grow new edges that could shorten existing paths.
        self.expl_cache.clear();
        self.pending.push((a, b, MergeReason::Assertion(reason)));
        self.propagate();
        Ok(())
    }

    /// Assert a disequality
    pub fn assert_diseq(&mut self, a: u32, b: u32, reason: TermId) {
        let idx = self.diseqs.len() as u32;
        self.diseqs.push(Diseq {
            lhs: a,
            rhs: b,
            reason,
        });
        // Watch the disequality on each endpoint's current representative.
        // When either class later merges, `propagate` tests it for violation.
        // find_no_compress (read-only): the watch key is the current rep, and
        // migration on merge keeps it current, so we never need to mutate here.
        let ra = self.uf.find_no_compress(a);
        let rb = self.uf.find_no_compress(b);
        self.diseq_watch_push(ra, idx);
        if ra != rb {
            self.diseq_watch_push(rb, idx);
        } else if self.pending_diseq_conflict.is_none() {
            // Already equal: the new disequality is violated right now.
            self.pending_diseq_conflict = Some(idx);
        }
    }

    /// Check if two terms are equivalent
    #[inline]
    pub fn are_equal(&mut self, a: u32, b: u32) -> bool {
        self.uf.same(a, b)
    }

    /// Get the representative of a term
    #[inline]
    pub fn find(&mut self, a: u32) -> u32 {
        self.uf.find(a)
    }

    /// Get the representative of a term without path compression (immutable)
    #[inline]
    pub fn find_immutable(&self, a: u32) -> u32 {
        self.uf.find_no_compress(a)
    }

    /// Check equivalence without mutation (immutable)
    #[inline]
    pub fn are_equal_immutable(&self, a: u32, b: u32) -> bool {
        self.uf.same_no_compress(a, b)
    }

    /// Get the number of E-graph nodes
    pub fn node_count(&self) -> usize {
        self.nodes.len()
    }

    /// Whether the e-graph contains any function-application nodes (as opposed
    /// to only leaf constants). Used to gate the from-scratch rebuild backstop
    /// in the CDCL(T) final check: the incremental-state false-sat bug
    /// (live e-graph diverging from a fresh replay of the same equalities)
    /// manifests on function-bearing EUF, not on pure-equality (constants-only)
    /// problems.
    pub fn has_app_nodes(&self) -> bool {
        self.nodes.iter().any(|n| n.is_app())
    }

    /// Get the term associated with a node index
    pub fn node_term(&self, idx: u32) -> Option<TermId> {
        self.nodes.get(idx as usize).map(|n| n.term)
    }

    /// Get the function symbol of a node (if it is a function application)
    pub fn node_func(&self, idx: u32) -> Option<u32> {
        self.nodes
            .get(idx as usize)
            .and_then(|n| if n.is_app() { Some(n.func) } else { None })
    }

    /// Get the arguments of a node (if it is a function application)
    pub fn node_args(&self, idx: u32) -> Option<&SmallVec<[u32; 4]>> {
        let node = self.nodes.get(idx as usize)?;
        if node.is_app() {
            Some(&node.args)
        } else {
            None
        }
    }

    /// Look up the node index for a given TermId
    pub fn term_to_node(&self, term: TermId) -> Option<u32> {
        self.term_to_node.get(&term).copied()
    }

    /// Iterate over all node indices that are function applications of a given function symbol.
    /// Returns a Vec of node indices.
    pub fn apps_by_func(&self, func_id: u32) -> Vec<u32> {
        let mut result = Vec::new();
        for (idx, node) in self.nodes.iter().enumerate() {
            if node.is_app() && node.func == func_id {
                result.push(idx as u32);
            }
        }
        result
    }

    /// Collect, for every interned application of `func_id`, the congruence-closed
    /// data a model builder needs to assemble a function interpretation.
    ///
    /// For each application node `f(a1, …, an)` the returned [`FuncAppEntry`]
    /// records:
    /// - `arg_reps`: the canonical equivalence-class representative (node index,
    ///   obtained via [`find_immutable`](Self::find_immutable)) of each argument,
    /// - `arg_class_terms`: every `TermId` interned into each argument's class —
    ///   so the caller can pick whichever member carries a concrete model value,
    /// - `result_rep`: the canonical class representative of the application
    ///   itself,
    /// - `result_class_terms`: every `TermId` interned into the result's class.
    ///
    /// Because the argument and result classes are taken through `find`, two
    /// applications whose arguments are pairwise congruent (e.g. `f(a)` and
    /// `f(b)` when `a = b`) yield identical `arg_reps` and `result_rep`. The
    /// caller can therefore deduplicate on `arg_reps` and rely on congruence
    /// having already collapsed them onto the same value class.
    ///
    /// This is a read-only `O(nodes)` scan (it never mutates the union-find, so
    /// no path compression occurs) and is intended for the post-`Sat` model
    /// extraction path, not the hot solving loop.
    #[must_use]
    pub fn function_application_entries(&self, func_id: u32) -> Vec<FuncAppEntry> {
        // Single O(nodes) pass: bucket every node's TermId under its canonical
        // class representative.  This avoids the O(apps × nodes) blow-up of
        // calling `class_members` once per application.
        let mut class_to_terms: FxHashMap<u32, Vec<TermId>> = FxHashMap::default();
        for idx in 0..self.nodes.len() as u32 {
            let rep = self.uf.find_no_compress(idx);
            class_to_terms
                .entry(rep)
                .or_default()
                .push(self.nodes[idx as usize].term);
        }

        let mut entries = Vec::new();
        for (idx, node) in self.nodes.iter().enumerate() {
            if !node.is_app() || node.func != func_id {
                continue;
            }

            // Canonical class rep of each argument plus the member TermIds of
            // that class (for value resolution by the caller).
            let mut arg_reps: SmallVec<[u32; 4]> = SmallVec::with_capacity(node.args.len());
            let mut arg_class_terms: SmallVec<[Vec<TermId>; 4]> =
                SmallVec::with_capacity(node.args.len());
            for &arg in &node.args {
                let rep = self.uf.find_no_compress(arg);
                arg_reps.push(rep);
                arg_class_terms.push(class_to_terms.get(&rep).cloned().unwrap_or_default());
            }

            let result_rep = self.uf.find_no_compress(idx as u32);
            let result_class_terms = class_to_terms.get(&result_rep).cloned().unwrap_or_default();

            entries.push(FuncAppEntry {
                arg_reps,
                arg_class_terms,
                result_rep,
                result_class_terms,
            });
        }
        entries
    }

    /// Get all members of an equivalence class (all node indices with the same representative).
    /// This is an O(n) scan; for performance-critical paths, consider caching.
    pub fn class_members(&self, class_rep: u32) -> Vec<u32> {
        let rep = self.uf.find_no_compress(class_rep);
        let mut members = Vec::new();
        for idx in 0..self.nodes.len() {
            if self.uf.find_no_compress(idx as u32) == rep {
                members.push(idx as u32);
            }
        }
        members
    }

    /// Iterate over all node indices (0..node_count)
    pub fn all_node_indices(&self) -> std::ops::Range<u32> {
        0..self.nodes.len() as u32
    }

    /// Get all distinct function symbols present in the E-graph
    pub fn all_func_symbols(&self) -> Vec<u32> {
        use rustc_hash::FxHashSet;
        let mut funcs = FxHashSet::default();
        for node in &self.nodes {
            if node.is_app() {
                funcs.insert(node.func);
            }
        }
        funcs.into_iter().collect()
    }

    /// Get the fingerprint table size (for testing/debugging)
    #[cfg(test)]
    fn fingerprint_table_len(&self) -> usize {
        self.fingerprint_table.len()
    }

    /// Get the sig table size (for testing/debugging)
    #[cfg(test)]
    fn sig_table_len(&self) -> usize {
        self.sig_table.len()
    }
}

impl Theory for EufSolver {
    fn id(&self) -> TheoryId {
        TheoryId::EUF
    }

    fn name(&self) -> &str {
        "EUF"
    }

    fn can_handle(&self, _term: TermId) -> bool {
        // EUF can handle equality and function applications
        true
    }

    // Audit note (theories-euf): `EufSolver` (like `crate::simplify` and
    // the MBQI matcher) only ever sees opaque `TermId`s here -- it has no
    // AST/term-manager access, so it cannot parse an arbitrary boolean
    // `term` into the `(lhs, rhs)` pair a "term is a true/false equality"
    // assertion needs. The production integration
    // (`oxiz-solver`'s theory manager) knows this and never calls these
    // two generic `Theory` methods: it always resolves `lhs`/`rhs` itself
    // and calls `merge`/`assert_diseq` directly with the correctly parsed
    // nodes. These two methods exist only to satisfy the `Theory` trait
    // for callers that go through the generic interface; interning `term`
    // is the only thing they can honestly do without term structure.
    fn assert_true(&mut self, term: TermId) -> Result<TheoryResult> {
        let _ = self.intern(term);
        Ok(TheoryResult::Sat)
    }

    fn assert_false(&mut self, term: TermId) -> Result<TheoryResult> {
        // Previously called `self.assert_diseq(node, node, term)` here --
        // asserting a node disequal to ITSELF, which is unconditionally
        // false in any congruence closure. That made every call to this
        // method (regardless of what `term` actually meant) an instant,
        // fabricated contradiction. Since this method cannot honestly
        // determine `term`'s actual negated meaning without term
        // structure (see the note above), the correct, non-fabricating
        // behavior is to record the term without asserting anything false
        // about it -- mirroring `assert_true`'s equally honest limitation
        // above -- rather than poison every subsequent `check()`.
        let _ = self.intern(term);
        Ok(TheoryResult::Sat)
    }

    fn check(&mut self) -> Result<TheoryResult> {
        if let Some(conflict) = self.check_conflicts() {
            Ok(TheoryResult::Unsat(conflict))
        } else {
            Ok(TheoryResult::Sat)
        }
    }

    fn push(&mut self) {
        self.context_stack.push(ContextState {
            num_nodes: self.nodes.len(),
            num_diseqs: self.diseqs.len(),
        });
        self.uf.push();
        // Record sig_trail checkpoint, mirroring uf.trail_limits.push(...)
        self.sig_trail_limits.push(self.sig_trail.len());
        // Record proof_trail checkpoint so pop() can rewind proof-forest edges
        // appended during this scope.
        self.proof_trail_limits.push(self.proof_trail.len());
        // Record use_list_trail checkpoint so pop() can rewind use-list appends
        // to pre-existing nodes made during this scope.
        self.use_list_trail_limits.push(self.use_list_trail.len());
        // Disequality watch-list + pending-conflict checkpoints for pop().
        self.diseq_watch_trail_limits
            .push(self.diseq_watch_trail.len());
        self.pending_trail_limits.push(self.pending_trail.len());
        self.pending_trail.push(self.pending_diseq_conflict);
    }

    fn pop(&mut self) {
        if let Some(state) = self.context_stack.pop() {
            let num_nodes = state.num_nodes;

            // Every merge is applied to a fixed point before control leaves the
            // e-graph, so this queue is normally empty; clearing it makes that a
            // guarantee rather than an assumption, so no merge scheduled inside
            // the popped scope can be applied after it is gone.
            self.pending.clear();

            self.nodes.truncate(num_nodes);
            self.diseqs.truncate(state.num_diseqs);
            self.uf.pop();

            // Also truncate related structures. Truncation removes the adjacency
            // lists of nodes created in the popped scope, but NOT edges appended to
            // pre-existing nodes' lists — those are undone via proof_trail below.
            self.use_list.truncate(num_nodes);
            self.proof_forest.truncate(num_nodes);
            self.node_sig_key.truncate(num_nodes);
            self.diseq_watch.truncate(num_nodes);

            // Rewind use_list_trail: for each append recorded during the popped
            // scope, pop exactly one entry off the recorded node's use-list.
            // Nodes created in this scope (index >= num_nodes) were already
            // dropped by the truncate above, so guard against them.
            if let Some(use_list_limit) = self.use_list_trail_limits.pop() {
                while self.use_list_trail.len() > use_list_limit {
                    let Some(node) = self.use_list_trail.pop() else {
                        break;
                    };
                    if (node as usize) < self.use_list.len() {
                        self.use_list[node as usize].pop();
                    }
                }
            }

            // Rewind proof_trail: for each edge recorded during the popped scope,
            // pop exactly one edge off the recorded node's adjacency list. Nodes
            // created in this scope (index >= num_nodes) were already dropped by
            // the truncate above, so guard against out-of-range indices.
            if let Some(proof_limit) = self.proof_trail_limits.pop() {
                while self.proof_trail.len() > proof_limit {
                    let Some(node) = self.proof_trail.pop() else {
                        break;
                    };
                    if (node as usize) < self.proof_forest.len() {
                        self.proof_forest[node as usize].pop();
                    }
                }
            }

            // Any cached explanation may reference edges just removed; drop them.
            self.expl_cache.clear();

            // Rewind diseq_watch_trail: for each watch-list append recorded
            // during the popped scope, pop one entry off the recorded rep's list
            // (mirror of use_list_trail above).
            if let Some(dw_limit) = self.diseq_watch_trail_limits.pop() {
                while self.diseq_watch_trail.len() > dw_limit {
                    let Some(rep) = self.diseq_watch_trail.pop() else {
                        break;
                    };
                    if (rep as usize) < self.diseq_watch.len() {
                        self.diseq_watch[rep as usize].pop();
                    }
                }
            }
            // Restore pending_diseq_conflict to its scope-entry value: the saved
            // value lives at index `pending_limit` (pushed at scope entry), then
            // the trail is rewound to that checkpoint.
            if let Some(pending_limit) = self.pending_trail_limits.pop() {
                self.pending_diseq_conflict = self
                    .pending_trail
                    .get(pending_limit)
                    .copied()
                    .unwrap_or(None);
                self.pending_trail.truncate(pending_limit);
            }

            // Remove term_to_node mappings that point to removed nodes.  Every
            // term maps to the node created for it (never to a borrowed congruent
            // one), and nodes are truncated in LIFO order, so this drops exactly
            // the terms first interned inside the popped scope.
            self.term_to_node
                .retain(|_term, &mut idx| (idx as usize) < num_nodes);

            // Rewind sig_trail to the saved limit, undoing all sig/fp insertions
            // made since the matching push().  Mirrors UnionFind::pop() exactly.
            if let Some(sig_limit) = self.sig_trail_limits.pop() {
                while self.sig_trail.len() > sig_limit {
                    if let Some(entry) = self.sig_trail.pop() {
                        match entry {
                            SigTrailEntry::InsertedSig { key, node } => {
                                self.sig_table.remove(&key);
                                if let Some(slot) = self.node_sig_key.get_mut(node as usize) {
                                    *slot = None;
                                }
                            }
                            SigTrailEntry::RemovedSig { key, node } => {
                                self.sig_table.insert(key.clone(), node);
                                if let Some(slot) = self.node_sig_key.get_mut(node as usize) {
                                    *slot = Some(key);
                                }
                            }
                            SigTrailEntry::InsertedFingerprint { fp, node_idx } => {
                                if let Some(bucket) = self.fingerprint_table.get_mut(&fp) {
                                    // Remove in LIFO order: the last push is the first to undo.
                                    if let Some(pos) = bucket.iter().rposition(|&n| n == node_idx) {
                                        bucket.swap_remove(pos);
                                    }
                                    if bucket.is_empty() {
                                        self.fingerprint_table.remove(&fp);
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    fn reset(&mut self) {
        self.uf = UnionFind::new(0);
        self.nodes.clear();
        self.term_to_node.clear();
        self.diseqs.clear();
        self.pending.clear();
        self.use_list.clear();
        self.sig_table.clear();
        self.node_sig_key.clear();
        self.diseq_watch.clear();
        self.diseq_watch_trail.clear();
        self.diseq_watch_trail_limits.clear();
        self.pending_diseq_conflict = None;
        self.pending_trail.clear();
        self.pending_trail_limits.clear();
        self.fingerprint_table.clear();
        self.context_stack.clear();
        self.proof_forest.clear();
        self.function_properties.clear();
        self.propagation_buf.clear();
        self.sig_trail.clear();
        self.sig_trail_limits.clear();
        self.proof_trail.clear();
        self.proof_trail_limits.clear();
        self.use_list_trail.clear();
        self.use_list_trail_limits.clear();
        self.explain_todo.clear();
        self.explain_enqueued.clear();
        self.expl_cache.clear();
    }
}
