//! Equality-logic decision via static transitivity constraints (chordal
//! "Sparse" method of Bryant & Velev, "Boolean Satisfiability with
//! Transitivity Constraints", TOCL; the construction the `eq_diamond`
//! benchmark family of Strichman & Rozanov is designed to exercise).
//!
//! For pure **Equality Logic** — Boolean combinations of `(= a b)` and
//! `(not (= a b))` over constants, with no functions, arithmetic, bit-vectors,
//! arrays, strings, or quantifiers — the congruence-closure / CDCL(T) core can
//! blow up exponentially on disjunctive equality chains. We instead recover the
//! lost transitivity of equality *statically*: build the equality graph, make
//! it chordal by elimination (adding fresh auxiliary "chord" variables for fill
//! edges), and add a transitivity clause for every triangle. A chordal graph
//! has only triangles as chord-free cycles, so this clause set is sound and
//! complete, and the SAT core alone decides the formula in polynomial time for
//! the families that matter.
//!
//! Per triangle `(x, y, z)` we add the three implications (each one 3-CNF
//! clause): `e_xy ∧ e_yz → e_xz`, `e_xy ∧ e_xz → e_yz`, `e_xz ∧ e_yz → e_xy`,
//! where `e_ab` is the Boolean variable of the `(= a b)` atom (an original atom
//! variable, or a fresh auxiliary for a chord). Auxiliary chord variables are
//! existentially free; setting one `true` only adds an equality, which by NNF
//! monotonicity preserves satisfiability of the skeleton, so the reduction is
//! equisatisfiable.
//!
//! Because the SAT core plus these clauses is a *complete* decision procedure
//! for the formula, when the preprocessing applies we solve with plain SAT and
//! skip the CDCL(T) loop entirely — otherwise the EUF theory would keep emitting
//! the long chain-conflict clauses that cause the original exponential blowup.

use crate::solver::Solver;
use oxiz_core::ast::{TermId, TermKind, TermManager};
use oxiz_sat::{Lit, Var};
use rustc_hash::FxHashMap;
use std::collections::BTreeSet;

impl Solver {
    /// Solve a pure-equality-logic formula using plain SAT over the skeleton
    /// conjoined with the static transitivity clauses added by
    /// [`Self::equality_transitivity_preprocess`].
    pub(super) fn solve_equality_via_sat(
        &mut self,
        manager: &mut TermManager,
    ) -> super::SolverResult {
        match self.sat.solve() {
            oxiz_sat::SolverResult::Unsat => {
                self.build_unsat_core();
                super::SolverResult::Unsat
            }
            oxiz_sat::SolverResult::Sat => {
                self.build_model(manager);
                if self.model_refutes_assertions(manager) {
                    // The SAT core committed a trail that violates an assertion
                    // (a backstop for any skeleton-encoding gap). Stay honest.
                    self.model = None;
                    self.unsat_core = None;
                    return super::SolverResult::Unknown;
                }
                self.unsat_core = None;
                super::SolverResult::Sat
            }
            oxiz_sat::SolverResult::Unknown => super::SolverResult::Unknown,
        }
    }

    /// If the current assertion set is pure Equality Logic, add chordal-Sparse
    /// transitivity clauses to the SAT core and return `true`. Returns `false`
    /// (changing nothing) otherwise, so it is safe to call unconditionally.
    pub(super) fn equality_transitivity_preprocess(&mut self, manager: &TermManager) -> bool {
        if self.has_quantifiers || self.has_array_ops {
            return false;
        }

        // Collect the equality graph: canonical (min,max) operand pair -> the
        // Boolean var of the `(= a b)` atom. The walk sets `pure = false` on
        // the first non-equality-logic construct.
        let mut edge_var: FxHashMap<(TermId, TermId), Var> = FxHashMap::default();
        let mut pure = true;
        for &assertion in &self.assertions {
            Self::collect_eq_edges(
                assertion,
                manager,
                &self.term_to_var,
                &mut edge_var,
                &mut pure,
            );
            if !pure {
                return false;
            }
        }
        if edge_var.is_empty() {
            return false;
        }

        // Dense vertex indices.
        let mut term_index: FxHashMap<TermId, usize> = FxHashMap::default();
        let mut idx_term: Vec<TermId> = Vec::new();
        for &(a, b) in edge_var.keys() {
            for t in [a, b] {
                if let std::collections::hash_map::Entry::Vacant(e) = term_index.entry(t) {
                    e.insert(idx_term.len());
                    idx_term.push(t);
                }
            }
        }
        let n = idx_term.len();

        // Adjacency over vertex indices.
        let mut adj: Vec<BTreeSet<usize>> = vec![BTreeSet::new(); n];
        for &(a, b) in edge_var.keys() {
            let i = term_index[&a];
            let j = term_index[&b];
            if i != j {
                adj[i].insert(j);
                adj[j].insert(i);
            }
        }

        // Chordalize via min-fill elimination. Each fill edge (chord) gets a
        // fresh auxiliary Boolean variable.
        let mut removed = vec![false; n];
        for _ in 0..n {
            let mut best: Option<usize> = None;
            let mut best_fill = usize::MAX;
            for v in 0..n {
                if removed[v] {
                    continue;
                }
                let nbrs: Vec<usize> = adj[v].iter().copied().filter(|&u| !removed[u]).collect();
                let mut fill = 0usize;
                for i in 0..nbrs.len() {
                    for &u in &nbrs[i + 1..] {
                        if !adj[nbrs[i]].contains(&u) {
                            fill += 1;
                        }
                    }
                }
                if fill < best_fill {
                    best_fill = fill;
                    best = Some(v);
                }
            }
            let Some(v) = best else { break };
            let nbrs: Vec<usize> = adj[v].iter().copied().filter(|&u| !removed[u]).collect();
            for i in 0..nbrs.len() {
                for &u in &nbrs[i + 1..] {
                    let a = nbrs[i];
                    if !adj[a].contains(&u) {
                        adj[a].insert(u);
                        adj[u].insert(a);
                        let new_var = self.sat.new_var();
                        let (ta, tu) = (idx_term[a], idx_term[u]);
                        let key = if ta < tu { (ta, tu) } else { (tu, ta) };
                        edge_var.insert(key, new_var);
                    }
                }
            }
            removed[v] = true;
        }

        let var_of = |i: usize, j: usize| -> Var {
            let (ti, tj) = (idx_term[i], idx_term[j]);
            let key = if ti < tj { (ti, tj) } else { (tj, ti) };
            *edge_var.get(&key).expect("edge var for every graph edge")
        };

        // Three transitivity clauses per triangle (v < a < b).
        for v in 0..n {
            let nbrs: Vec<usize> = adj[v].iter().copied().filter(|&u| u > v).collect();
            for i in 0..nbrs.len() {
                let a = nbrs[i];
                for &b in &nbrs[i + 1..] {
                    if !adj[a].contains(&b) {
                        continue;
                    }
                    let e_va = var_of(v, a);
                    let e_vb = var_of(v, b);
                    let e_ab = var_of(a, b);
                    self.sat
                        .add_clause([Lit::neg(e_va), Lit::neg(e_vb), Lit::pos(e_ab)]);
                    self.sat
                        .add_clause([Lit::neg(e_va), Lit::neg(e_ab), Lit::pos(e_vb)]);
                    self.sat
                        .add_clause([Lit::neg(e_vb), Lit::neg(e_ab), Lit::pos(e_va)]);
                }
            }
        }

        true
    }

    /// Recursive walk recording equality-graph edges. Sets `pure = false` on
    /// the first construct outside pure equality logic.
    fn collect_eq_edges(
        term: TermId,
        manager: &TermManager,
        term_to_var: &FxHashMap<TermId, Var>,
        edge_var: &mut FxHashMap<(TermId, TermId), Var>,
        pure: &mut bool,
    ) {
        if !*pure {
            return;
        }
        let Some(t) = manager.get(term) else {
            *pure = false;
            return;
        };
        match &t.kind {
            TermKind::True | TermKind::False => {}
            TermKind::Not(inner) => {
                Self::collect_eq_edges(*inner, manager, term_to_var, edge_var, pure);
            }
            TermKind::And(ts) | TermKind::Or(ts) => {
                for &c in ts {
                    Self::collect_eq_edges(c, manager, term_to_var, edge_var, pure);
                    if !*pure {
                        return;
                    }
                }
            }
            TermKind::Eq(a, b) => {
                let ok = manager
                    .get(*a)
                    .is_some_and(|x| matches!(x.kind, TermKind::Var(_)))
                    && manager
                        .get(*b)
                        .is_some_and(|x| matches!(x.kind, TermKind::Var(_)));
                if !ok {
                    *pure = false;
                    return;
                }
                let Some(&var) = term_to_var.get(&term) else {
                    *pure = false;
                    return;
                };
                let key = if a < b { (*a, *b) } else { (*b, *a) };
                edge_var.insert(key, var);
            }
            // Distinct, ite, xor, =>, arithmetic, bit-vector, strings,
            // datatypes, function applications, quantifiers -> not pure.
            _ => *pure = false,
        }
    }
}
