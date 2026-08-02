//! Equality-`ite` lookup-table flattening for QF_LIA (and friends).
//!
//! Tool-generated SMT often encodes finite maps as right-spines:
//!
//! ```text
//! (ite (= x 1) v1 (ite (= x 2) v2 (ite (= x 3) v3 … default)))
//! ```
//!
//! This pass:
//! 1. Collapses each long equality-spine into one result + implications
//! 2. Folds 0/1 Discord/Fan nests (`ite(>t 0,t,0)→t`, `max→a+b−ab`, …)
//! 3. Eagerly case-splits table indices with small asserted bounds (ALO+AMO)
//! 4. Boolean-links comparison atoms (`(> idx c)`) to those domain eqs
//!
//! so nested tool-generated nests unit-propagate / collapse once indices pin.

use num_traits::ToPrimitive;
use oxiz_core::ast::{TermId, TermKind, TermManager, collect_subterms};
use oxiz_core::sort::SortId;
use oxiz_sat::Lit;
use rustc_hash::{FxHashMap, FxHashSet};

use super::types::Constraint;
use super::Solver;

const MIN_TABLE_CASES: usize = 4;
const MAX_EAGER_TABLE_DOMAIN: i64 = 64;

struct EqIteTable {
    root: TermId,
    index: TermId,
    cases: Vec<(i64, TermId)>,
    default: TermId,
    spine: Vec<TermId>,
}

impl Solver {
    /// Flatten long equality-`ite` lookup tables in `term`.
    pub(super) fn flatten_eq_ite_tables(
        &mut self,
        term: TermId,
        manager: &mut TermManager,
    ) -> TermId {
        let bool_sort = manager.sorts.bool_sort;
        let subterms = collect_subterms(term, manager);

        let mut matches: Vec<EqIteTable> = Vec::new();
        for &st in &subterms {
            if let Some(m) = match_eq_ite_table(st, manager, bool_sort) {
                matches.push(m);
            }
        }
        if matches.is_empty() {
            return term;
        }

        let mut covered: FxHashSet<TermId> = FxHashSet::default();
        matches.sort_by_key(|m| std::cmp::Reverse(m.cases.len()));
        let mut maximal: Vec<EqIteTable> = Vec::with_capacity(matches.len());
        for m in matches {
            if covered.contains(&m.root) {
                continue;
            }
            for &node in &m.spine {
                covered.insert(node);
            }
            maximal.push(m);
        }
        if maximal.is_empty() {
            return term;
        }

        let mut map: FxHashMap<TermId, TermId> = FxHashMap::default();
        let mut side: Vec<TermId> = Vec::new();

        for (i, m) in maximal.iter().enumerate() {
            let sort = manager
                .get(m.root)
                .map(|t| t.sort)
                .unwrap_or(manager.sorts.int_sort);
            let r = manager.mk_var(&format!("__oxiz_tbl_{}_{}", m.root.0, i), sort);
            self.ite_result_terms.insert(r);
            self.table_index_terms.insert(m.index);
            {
                let keys = self.table_index_keys.entry(m.index).or_default();
                for &(k, _) in &m.cases {
                    if !keys.contains(&k) {
                        keys.push(k);
                    }
                }
                keys.sort_unstable();
            }
            map.insert(m.root, r);

            let mut not_cases: Vec<TermId> = Vec::with_capacity(m.cases.len());
            let mut const_vals: Vec<i64> = Vec::new();
            let mut all_const = true;
            for &(k, then_br) in &m.cases {
                let k_term = manager.mk_int(k);
                let eq_idx = manager.mk_eq(m.index, k_term);
                let eq_r = manager.mk_eq(r, then_br);
                side.push(manager.mk_implies(eq_idx, eq_r));
                not_cases.push(manager.mk_not(eq_idx));
                match int_const_val(then_br, manager) {
                    Some(v) => {
                        const_vals.push(v);
                        // Accumulate |payload| for domain branching heuristic.
                        let rep = self.unit_eq_rep.get(&m.index).copied().unwrap_or(m.index);
                        let e = self
                            .table_index_key_score
                            .entry(rep)
                            .or_default()
                            .entry(k)
                            .or_insert(0);
                        *e = e.saturating_add(v.unsigned_abs() as i64);
                        let e2 = self
                            .table_index_key_score
                            .entry(m.index)
                            .or_default()
                            .entry(k)
                            .or_insert(0);
                        *e2 = e2.saturating_add(v.unsigned_abs() as i64);
                    }
                    None => all_const = false,
                }
            }
            let none = manager.mk_and(not_cases);
            let eq_def = manager.mk_eq(r, m.default);
            side.push(manager.mk_implies(none, eq_def));
            if all_const {
                if let Some(v) = int_const_val(m.default, manager) {
                    const_vals.push(v);
                } else {
                    all_const = false;
                }
            }
            if all_const {
                const_vals.sort_unstable();
                const_vals.dedup();
                // Track 0/1 images for nest folding + result domain split.
                if !const_vals.is_empty()
                    && const_vals.iter().all(|&v| v == 0 || v == 1)
                {
                    self.zero_one_terms.insert(r);
                    self.binary_table_results.insert(r);
                }
            }
        }

        // Keep define-fun aliases in sync when an inlined body is rewritten
        // inside a later assertion (e.g. `(<= Discord 4)` with Discord inlined).
        self.rebind_aliases_through_map(manager, &map);
        self.rebind_table_indices_through_map(manager, &map);

        let rewritten = manager.substitute(term, &map);
        let side: Vec<TermId> = side
            .into_iter()
            .map(|s| manager.substitute(s, &map))
            .collect();
        let mut parts = side;
        parts.insert(0, rewritten);
        manager.mk_and(parts)
    }

    pub(super) fn rebind_aliases_through_map(
        &mut self,
        manager: &mut TermManager,
        map: &FxHashMap<TermId, TermId>,
    ) {
        if map.is_empty() || self.unit_eq_rep.is_empty() {
            return;
        }
        let snapshot: Vec<(TermId, TermId)> = self.unit_eq_rep.iter().map(|(&k, &v)| (k, v)).collect();
        for (body, rep) in snapshot {
            let body2 = manager.substitute(body, map);
            if body2 != body {
                self.unit_eq_rep.insert(body2, rep);
            }
        }
    }

    pub(super) fn rebind_table_indices_through_map(
        &mut self,
        manager: &mut TermManager,
        map: &FxHashMap<TermId, TermId>,
    ) {
        if map.is_empty() || self.table_index_keys.is_empty() {
            return;
        }
        let snapshot: Vec<(TermId, Vec<i64>)> = self
            .table_index_keys
            .iter()
            .map(|(&k, v)| (k, v.clone()))
            .collect();
        for (idx, keys) in snapshot {
            let idx2 = manager.substitute(idx, map);
            if idx2 != idx {
                self.table_index_terms.insert(idx2);
                let e = self.table_index_keys.entry(idx2).or_default();
                for k in keys {
                    if !e.contains(&k) {
                        e.push(k);
                    }
                }
                e.sort_unstable();
            }
        }
    }

    /// Collapse Discord/Fan-style nests over 0/1 table leaves into arithmetic.
    ///
    /// Rewrites (bottom-up, iterated to fixpoint, capped):
    /// - `ite(> t 0, t, 0) → t` when `t` is 0/1-valued
    /// - `ite(> t 0, 1, 0) → t` when `t` is 0/1-valued
    /// - `ite(> a b, a, b) → a+b−a·b` (max) when both are 0/1-valued
    /// - `ite(< x 0, −x, x) → x·x` (abs) when `x` is in {−1,0,1} as a−b of 0/1s
    ///
    /// Marks derived terms as 0/1 so outer folds fire.
    pub(super) fn fold_zero_one_nests(
        &mut self,
        term: TermId,
        manager: &mut TermManager,
    ) -> TermId {
        if self.zero_one_terms.is_empty() {
            return term;
        }
        let bool_sort = manager.sorts.bool_sort;
        let mut cur = term;
        for _ in 0..8 {
            let subterms = collect_subterms(cur, manager);
            let mut map: FxHashMap<TermId, TermId> = FxHashMap::default();
            let mut zo = self.zero_one_terms.clone();

            for st in subterms {
                let Some(t) = manager.get(st) else { continue };
                if t.sort == bool_sort {
                    continue;
                }
                let out = match &t.kind {
                    TermKind::Ite(c0, th0, el0) => {
                        let c = *map.get(c0).unwrap_or(c0);
                        let th = *map.get(th0).unwrap_or(th0);
                        let el = *map.get(el0).unwrap_or(el0);
                        fold_one_ite(c, th, el, manager, &mut zo)
                    }
                    TermKind::Add(args) => {
                        let args: Vec<TermId> =
                            args.iter().map(|a| *map.get(a).unwrap_or(a)).collect();
                        // sum of 0/1 is not necessarily 0/1
                        manager.mk_add(args)
                    }
                    TermKind::Sub(a0, b0) => {
                        let a = *map.get(a0).unwrap_or(a0);
                        let b = *map.get(b0).unwrap_or(b0);
                        manager.mk_sub(a, b)
                    }
                    TermKind::Mul(args) => {
                        let args: Vec<TermId> =
                            args.iter().map(|a| *map.get(a).unwrap_or(a)).collect();
                        let m = manager.mk_mul(args.clone());
                        if args.iter().all(|a| zo.contains(a)) {
                            zo.insert(m);
                        }
                        m
                    }
                    _ => continue,
                };
                if out != st {
                    map.insert(st, out);
                }
            }
            self.zero_one_terms = zo;
            if map.is_empty() {
                break;
            }
            self.rebind_aliases_through_map(manager, &map);
            self.rebind_table_indices_through_map(manager, &map);
            cur = manager.substitute(cur, &map);
        }
        cur
    }

    /// Rewrite inlined define-fun bodies to their named representative vars.
    ///
    /// The SMT-LIB parser expands nullary `define-fun` at every use site.  After
    /// we have processed `(= Name body)`, subsequent assertions that still carry
    /// the raw `body` DAG should mention `Name` instead — otherwise Discord/EM/R
    /// are re-flattened on every mention (catastrophic on qi_1_h1).
    pub(super) fn fold_unit_eq_reps(
        &mut self,
        term: TermId,
        manager: &mut TermManager,
    ) -> TermId {
        // The alias fold exists to give flattened table indices their define-fun
        // names; without tables it only churns through ordinary `(= var var)`
        // constraint equalities (tens of thousands on ite-heavy QF_UF), so gate
        // it on table presence.  `note_unit_eq_alias` (the builder) stays
        // ungated so aliases noted before a table appears are still available.
        if self.unit_eq_rep.is_empty() || self.table_index_terms.is_empty() {
            return term;
        }
        let mut map: FxHashMap<TermId, TermId> = FxHashMap::default();
        for (&body, &rep) in &self.unit_eq_rep {
            if body != rep {
                map.insert(body, rep);
            }
        }
        if map.is_empty() {
            term
        } else {
            manager.substitute(term, &map)
        }
    }

    /// Record unit top-level `(= var t)` so bounds on `var` apply to `t`.
    pub(super) fn note_unit_eq_alias(&mut self, term: TermId, manager: &TermManager) {
        // Peel a top-level and to find bare equalities.
        let mut stack = vec![term];
        while let Some(t) = stack.pop() {
            let Some(node) = manager.get(t) else {
                continue;
            };
            match &node.kind {
                TermKind::And(args) => stack.extend(args.iter().copied()),
                TermKind::Eq(a, b) => {
                    let (a, b) = (*a, *b);
                    let a_var = matches!(manager.get(a).map(|x| &x.kind), Some(TermKind::Var(_)));
                    let b_var = matches!(manager.get(b).map(|x| &x.kind), Some(TermKind::Var(_)));
                    match (a_var, b_var) {
                        (true, false) => {
                            self.unit_eq_rep.entry(a).or_insert(a);
                            self.unit_eq_rep.insert(b, a);
                        }
                        (false, true) => {
                            self.unit_eq_rep.entry(b).or_insert(b);
                            self.unit_eq_rep.insert(a, b);
                        }
                        (true, true) => {
                            // Prefer lower id as rep
                            let (rep, oth) = if a.0 <= b.0 { (a, b) } else { (b, a) };
                            self.unit_eq_rep.entry(rep).or_insert(rep);
                            self.unit_eq_rep.insert(oth, rep);
                        }
                        _ => {}
                    }
                }
                _ => {}
            }
        }
    }

    /// Eager finite-domain case-split on table indices with small asserted bounds.
    pub(super) fn eager_table_index_case_split(&mut self, manager: &mut TermManager) {
        if self.table_index_terms.is_empty() {
            return;
        }
        let dbg = std::env::var("OXIZ_DBG_ITE").is_ok();
        let mut bounds: FxHashMap<TermId, (Option<i64>, Option<i64>)> = FxHashMap::default();
        for &assertion in &self.assertions {
            collect_conjunctive_int_bounds(
                assertion,
                manager,
                &mut bounds,
                &self.unit_eq_rep,
            );
        }

        // Group indices by representative so we case-split each domain once.
        let mut by_rep: FxHashMap<TermId, Vec<TermId>> = FxHashMap::default();
        for &idx in &self.table_index_terms {
            let rep = self.unit_eq_rep.get(&idx).copied().unwrap_or(idx);
            by_rep.entry(rep).or_default().push(idx);
        }

        // (rep_total_score, key_score, var) — sorted for domain_priority.
        let mut domain_priority_scored: Vec<(i64, i64, oxiz_sat::Var)> = Vec::new();

        for (rep, idxs) in by_rep {
            if self.case_split_terms.contains(&rep) {
                // Still bridge any new idx aliases.
                if let Some(pairs) = self.table_index_domain_eqs.get(&rep).cloned() {
                    for idx in idxs {
                        if idx != rep && !self.case_split_terms.contains(&idx) {
                            self.bridge_index_to_rep(idx, &pairs, manager, dbg);
                        }
                    }
                }
                continue;
            }

            // Merge keys across all aliases of this rep.
            let mut keys: Vec<i64> = Vec::new();
            for &idx in &idxs {
                if let Some(k) = self.table_index_keys.get(&idx) {
                    for &v in k {
                        if !keys.contains(&v) {
                            keys.push(v);
                        }
                    }
                }
            }
            keys.sort_unstable();

            let mut b_lo: Option<i64> = None;
            let mut b_hi: Option<i64> = None;
            for (t, (lo, hi)) in &bounds {
                let t_rep = self.unit_eq_rep.get(t).copied().unwrap_or(*t);
                if *t == rep || t_rep == rep || idxs.contains(t) {
                    if let Some(l) = lo {
                        b_lo = Some(b_lo.map_or(*l, |x| x.max(*l)));
                    }
                    if let Some(h) = hi {
                        b_hi = Some(b_hi.map_or(*h, |x| x.min(*h)));
                    }
                }
            }

            let domain_vals: Option<Vec<i64>> = match (b_lo, b_hi) {
                (Some(lo), Some(hi)) if hi >= lo && hi - lo <= MAX_EAGER_TABLE_DOMAIN => {
                    Some((lo..=hi).collect())
                }
                (None, Some(hi)) if hi >= 0 && hi <= MAX_EAGER_TABLE_DOMAIN => {
                    let lo = keys.iter().copied().min().unwrap_or(0).max(0);
                    if lo <= hi {
                        Some((lo..=hi).collect())
                    } else {
                        None
                    }
                }
                (Some(lo), None) if !keys.is_empty() => {
                    let kmax = keys.iter().copied().max().unwrap_or(0);
                    if kmax >= lo && kmax - lo <= MAX_EAGER_TABLE_DOMAIN {
                        Some((lo..=kmax).collect())
                    } else {
                        None
                    }
                }
                _ => None,
            };

            let Some(vals) = domain_vals else {
                if dbg {
                    eprintln!(
                        "[ite] skip rep={} idxs={} keys={} lo={b_lo:?} hi={b_hi:?}",
                        rep.0,
                        idxs.len(),
                        keys.len()
                    );
                }
                continue;
            };
            if vals.is_empty() {
                continue;
            }
            if dbg {
                eprintln!(
                    "[ite] SPLIT rep={} n_idx={} domain={}..{}",
                    rep.0,
                    idxs.len(),
                    vals.first().copied().unwrap_or(0),
                    vals.last().copied().unwrap_or(0)
                );
            }

            let mut pairs: Vec<(i64, Lit)> = Vec::with_capacity(vals.len());
            let mut lits: Vec<Lit> = Vec::with_capacity(vals.len());
            for k in &vals {
                let k_term = manager.mk_int(*k);
                let eq = manager.mk_eq(rep, k_term);
                let lit = self.encode_depth(eq, manager, 0);
                pairs.push((*k, lit));
                lits.push(lit);
            }
            self.sat.add_clause(lits.clone());
            for i in 0..lits.len() {
                for j in (i + 1)..lits.len() {
                    self.sat
                        .add_clause([lits[i].negate(), lits[j].negate()]);
                }
            }
            // Decide domain equalities early; weight by table payload so
            // high-value keys (e.g. R9 scores) are tried first.
            let scores = self.table_index_key_score.get(&rep).cloned().unwrap_or_default();
            let max_score = scores.values().copied().max().unwrap_or(0).max(1);
            let rep_total: i64 = scores.values().sum();
            // Sort keys by payload for this index.
            let mut keyed: Vec<(i64, Lit)> = pairs
                .iter()
                .map(|&(k, lit)| (scores.get(&k).copied().unwrap_or(0), lit))
                .collect();
            keyed.sort_by(|a, b| b.0.cmp(&a.0));
            // Only force-priority the top keys of large domains (rest via VSIDS).
            let top_n = if vals.len() <= 8 {
                vals.len()
            } else {
                10.min(vals.len())
            };
            for (i, &(sc, lit)) in keyed.iter().enumerate() {
                let base = if vals.len() <= 8 { 48 } else { 12 };
                let extra = ((sc as u128 * 128) / max_score as u128) as u32;
                self.sat.bump_var_activity(lit.var(), base + extra);
                self.sat.set_preferred_phase(lit.var(), true);
                if i < top_n {
                    // Group by rep importance, then key score.
                    domain_priority_scored.push((rep_total, sc, lit.var()));
                }
            }
            self.table_index_domain_eqs.insert(rep, pairs.clone());
            self.case_split_terms.insert(rep);

            for idx in idxs {
                if idx != rep {
                    self.bridge_index_to_rep(idx, &pairs, manager, dbg);
                }
            }
        }

        if !domain_priority_scored.is_empty() {
            // High-importance indices first, then high payload keys within.
            domain_priority_scored.sort_by(|a, b| {
                b.0.cmp(&a.0)
                    .then_with(|| b.1.cmp(&a.1))
                    .then_with(|| a.2.index().cmp(&b.2.index()))
            });
            let vars: Vec<_> = domain_priority_scored.into_iter().map(|(_, _, v)| v).collect();
            self.sat.set_domain_priority(vars);
        }
    }

    /// Case-split 0/1 table results so `(> r 0)` links to `(= r 1)`.
    pub(super) fn eager_binary_result_case_split(&mut self, manager: &mut TermManager) {
        if self.binary_table_results.is_empty() {
            return;
        }
        let results: Vec<TermId> = self.binary_table_results.iter().copied().collect();
        let zero = manager.mk_int(0);
        let one = manager.mk_int(1);
        for r in results {
            if self.case_split_terms.contains(&r) {
                continue;
            }
            let eq0 = manager.mk_eq(r, zero);
            let eq1 = manager.mk_eq(r, one);
            let lit0 = self.encode_depth(eq0, manager, 0);
            let lit1 = self.encode_depth(eq1, manager, 0);
            // Exactly one of r=0, r=1.
            self.sat.add_clause([lit0, lit1]);
            self.sat.add_clause([lit0.negate(), lit1.negate()]);
            self.table_index_domain_eqs
                .insert(r, vec![(0, lit0), (1, lit1)]);
            self.case_split_terms.insert(r);
            // Don't put these on domain_priority — index vars first; result
            // eqs should unit-prop from table implications once index is set.
        }
    }

    fn bridge_index_to_rep(
        &mut self,
        idx: TermId,
        rep_pairs: &[(i64, Lit)],
        manager: &mut TermManager,
        dbg: bool,
    ) {
        if self.case_split_terms.contains(&idx) {
            return;
        }
        let _ = dbg;
        let mut idx_pairs: Vec<(i64, Lit)> = Vec::with_capacity(rep_pairs.len());
        for &(k, lit_rep) in rep_pairs {
            let k_term = manager.mk_int(k);
            let eq_idx = manager.mk_eq(idx, k_term);
            let lit_idx = self.encode_depth(eq_idx, manager, 0);
            self.sat.add_clause([lit_rep.negate(), lit_idx]);
            self.sat.add_clause([lit_idx.negate(), lit_rep]);
            idx_pairs.push((k, lit_idx));
        }
        self.table_index_domain_eqs.insert(idx, idx_pairs);
        self.case_split_terms.insert(idx);
    }

    /// Boolean-link comparison atoms on table indices/results to domain eqs.
    pub(super) fn link_table_index_comparisons(&mut self, manager: &mut TermManager) {
        if self.table_index_domain_eqs.is_empty() {
            return;
        }

        let mut jobs: Vec<(Lit, TermId, i64, CompKind)> = Vec::new();
        for (&var, constraint) in &self.var_to_constraint {
            let (a, b, kind) = match constraint {
                Constraint::Lt(a, b) => (*a, *b, CompKind::Lt),
                Constraint::Le(a, b) => (*a, *b, CompKind::Le),
                Constraint::Gt(a, b) => (*a, *b, CompKind::Gt),
                Constraint::Ge(a, b) => (*a, *b, CompKind::Ge),
                _ => continue,
            };
            let cmp_lit = Lit::pos(var);
            if self.table_index_domain_eqs.contains_key(&a) {
                if let Some(c) = int_const_val(b, manager) {
                    jobs.push((cmp_lit, a, c, kind));
                }
            } else if self.table_index_domain_eqs.contains_key(&b) {
                if let Some(c) = int_const_val(a, manager) {
                    let flipped = match kind {
                        CompKind::Lt => CompKind::Gt,
                        CompKind::Le => CompKind::Ge,
                        CompKind::Gt => CompKind::Lt,
                        CompKind::Ge => CompKind::Le,
                    };
                    jobs.push((cmp_lit, b, c, flipped));
                }
            }
        }

        for (cmp_lit, idx, c, kind) in jobs {
            let Some(pairs) = self.table_index_domain_eqs.get(&idx).cloned() else {
                continue;
            };
            let true_set: FxHashSet<i64> = pairs
                .iter()
                .map(|(k, _)| *k)
                .filter(|&k| match kind {
                    CompKind::Gt => k > c,
                    CompKind::Ge => k >= c,
                    CompKind::Lt => k < c,
                    CompKind::Le => k <= c,
                })
                .collect();
            let true_lits: Vec<Lit> = pairs
                .iter()
                .filter(|(k, _)| true_set.contains(k))
                .map(|(_, l)| *l)
                .collect();
            let false_lits: Vec<Lit> = pairs
                .iter()
                .filter(|(k, _)| !true_set.contains(k))
                .map(|(_, l)| *l)
                .collect();

            if true_lits.is_empty() {
                self.sat.add_clause([cmp_lit.negate()]);
            } else {
                let mut clause = Vec::with_capacity(true_lits.len() + 1);
                clause.push(cmp_lit.negate());
                clause.extend_from_slice(&true_lits);
                self.sat.add_clause(clause);
            }
            for &eq in &true_lits {
                self.sat.add_clause([eq.negate(), cmp_lit]);
            }
            for &eq in &false_lits {
                self.sat.add_clause([eq.negate(), cmp_lit.negate()]);
            }
        }
    }
}

#[derive(Clone, Copy)]
enum CompKind {
    Lt,
    Le,
    Gt,
    Ge,
}

/// Fold one arithmetic ite given already-rewritten children.
fn fold_one_ite(
    c: TermId,
    th: TermId,
    el: TermId,
    manager: &mut TermManager,
    zo: &mut FxHashSet<TermId>,
) -> TermId {
    if th == el {
        if zo.contains(&th) {
            zo.insert(th);
        }
        return th;
    }

    // ite(> t 0, t, 0) → t when t is 0/1
    if is_gt_zero_of(c, th, manager) && is_int_const(el, 0, manager) && zo.contains(&th) {
        return th;
    }
    // ite(> t 0, 1, 0) → t when t is 0/1
    if let Some(t) = gt_zero_lhs(c, manager) {
        if is_int_const(th, 1, manager) && is_int_const(el, 0, manager) && zo.contains(&t) {
            return t;
        }
    }
    // ite(> a b, a, b) → max = a+b−a·b when both 0/1
    if is_gt_of(c, th, el, manager) && zo.contains(&th) && zo.contains(&el) {
        let sum = manager.mk_add([th, el]);
        let prod = manager.mk_mul([th, el]);
        let mx = manager.mk_sub(sum, prod);
        zo.insert(mx);
        return mx;
    }
    // ite(< x 0, −x, x) → x·x when x is a−b of 0/1s (abs on {-1,0,1})
    if let Some(x) = lt_zero_lhs(c, manager) {
        if el == x && is_negation_of(th, x, manager) && is_zo_diff(x, manager, zo) {
            let a = manager.mk_mul([x, x]);
            zo.insert(a); // abs ∈ {0,1}
            return a;
        }
    }

    // ite(c, zo, zo) stays 0/1
    let rebuilt = manager.mk_ite(c, th, el);
    if zo.contains(&th) && zo.contains(&el) {
        zo.insert(rebuilt);
    }
    rebuilt
}

fn is_int_const(term: TermId, want: i64, manager: &TermManager) -> bool {
    int_const_val(term, manager) == Some(want)
}

fn is_gt_zero_of(cond: TermId, term: TermId, manager: &TermManager) -> bool {
    match manager.get(cond).map(|t| &t.kind) {
        Some(TermKind::Gt(a, b)) => *a == term && is_int_const(*b, 0, manager),
        _ => false,
    }
}

fn is_gt_of(cond: TermId, a: TermId, b: TermId, manager: &TermManager) -> bool {
    match manager.get(cond).map(|t| &t.kind) {
        Some(TermKind::Gt(x, y)) => *x == a && *y == b,
        _ => false,
    }
}

fn gt_zero_lhs(cond: TermId, manager: &TermManager) -> Option<TermId> {
    match manager.get(cond).map(|t| &t.kind) {
        Some(TermKind::Gt(a, b)) if is_int_const(*b, 0, manager) => Some(*a),
        _ => None,
    }
}

fn lt_zero_lhs(cond: TermId, manager: &TermManager) -> Option<TermId> {
    match manager.get(cond).map(|t| &t.kind) {
        Some(TermKind::Lt(a, b)) if is_int_const(*b, 0, manager) => Some(*a),
        _ => None,
    }
}

fn is_negation_of(term: TermId, x: TermId, manager: &mut TermManager) -> bool {
    match manager.get(term).map(|t| t.kind.clone()) {
        Some(TermKind::Neg(a)) => a == x,
        Some(TermKind::Sub(a, b)) => is_int_const(a, 0, manager) && b == x,
        _ => {
            // Hash-cons check against freshly built (0 − x)
            let zero = manager.mk_int(0);
            term == manager.mk_sub(zero, x)
        }
    }
}

fn is_zo_diff(x: TermId, manager: &TermManager, zo: &FxHashSet<TermId>) -> bool {
    match manager.get(x).map(|t| &t.kind) {
        Some(TermKind::Sub(a, b)) => zo.contains(a) && zo.contains(b),
        Some(TermKind::Neg(a)) => zo.contains(a),
        _ => false,
    }
}

fn match_eq_ite_table(
    term: TermId,
    manager: &TermManager,
    bool_sort: SortId,
) -> Option<EqIteTable> {
    let t = manager.get(term)?;
    if t.sort == bool_sort || !matches!(&t.kind, TermKind::Ite(..)) {
        return None;
    }

    let mut index: Option<TermId> = None;
    let mut cases: Vec<(i64, TermId)> = Vec::new();
    let mut spine: Vec<TermId> = Vec::new();
    let mut seen_k: FxHashSet<i64> = FxHashSet::default();
    let mut cur = term;

    loop {
        let Some(tt) = manager.get(cur) else {
            break;
        };
        if tt.sort == bool_sort {
            break;
        }
        let TermKind::Ite(cond, then_br, else_br) = &tt.kind else {
            break;
        };
        let (cond, then_br, else_br) = (*cond, *then_br, *else_br);
        let Some((idx, k)) = eq_index_const(cond, manager) else {
            break;
        };
        if let Some(prev) = index {
            if prev != idx {
                break;
            }
        } else {
            index = Some(idx);
        }
        if !seen_k.insert(k) {
            break;
        }
        spine.push(cur);
        cases.push((k, then_br));
        cur = else_br;
    }

    if cases.len() < MIN_TABLE_CASES {
        return None;
    }
    Some(EqIteTable {
        root: term,
        index: index?,
        cases,
        default: cur,
        spine,
    })
}

fn eq_index_const(cond: TermId, manager: &TermManager) -> Option<(TermId, i64)> {
    let t = manager.get(cond)?;
    let TermKind::Eq(a, b) = &t.kind else {
        return None;
    };
    let (a, b) = (*a, *b);
    if let Some(k) = int_const_val(a, manager) {
        return Some((b, k));
    }
    if let Some(k) = int_const_val(b, manager) {
        return Some((a, k));
    }
    None
}

fn int_const_val(term: TermId, manager: &TermManager) -> Option<i64> {
    match &manager.get(term)?.kind {
        TermKind::IntConst(v) => v.to_i64(),
        _ => None,
    }
}


fn collect_conjunctive_int_bounds(
    term: TermId,
    manager: &TermManager,
    bounds: &mut FxHashMap<TermId, (Option<i64>, Option<i64>)>,
    aliases: &FxHashMap<TermId, TermId>,
) {
    let Some(t) = manager.get(term) else {
        return;
    };
    match &t.kind {
        TermKind::And(args) => {
            for &a in args {
                collect_conjunctive_int_bounds(a, manager, bounds, aliases);
            }
        }
        TermKind::Ge(a, b) => note_ge(*a, *b, false, manager, bounds, aliases),
        TermKind::Gt(a, b) => note_ge(*a, *b, true, manager, bounds, aliases),
        TermKind::Le(a, b) => note_le(*a, *b, false, manager, bounds, aliases),
        TermKind::Lt(a, b) => note_le(*a, *b, true, manager, bounds, aliases),
        TermKind::Eq(a, b) => {
            if let (Some(v), Some(c)) = (bound_term(*a, manager, aliases), int_const_val(*b, manager))
            {
                let e = bounds.entry(v).or_insert((None, None));
                e.0 = Some(e.0.map_or(c, |x| x.max(c)));
                e.1 = Some(e.1.map_or(c, |x| x.min(c)));
            } else if let (Some(c), Some(v)) =
                (int_const_val(*a, manager), bound_term(*b, manager, aliases))
            {
                let e = bounds.entry(v).or_insert((None, None));
                e.0 = Some(e.0.map_or(c, |x| x.max(c)));
                e.1 = Some(e.1.map_or(c, |x| x.min(c)));
            }
        }
        _ => {}
    }
}

/// Variable, or define-fun alias representative for a (possibly inlined) body.
fn bound_term(
    term: TermId,
    manager: &TermManager,
    aliases: &FxHashMap<TermId, TermId>,
) -> Option<TermId> {
    if let Some(&rep) = aliases.get(&term) {
        return Some(rep);
    }
    match manager.get(term)?.kind {
        TermKind::Var(_) => Some(term),
        _ => None,
    }
}

fn note_ge(
    a: TermId,
    b: TermId,
    strict: bool,
    manager: &TermManager,
    bounds: &mut FxHashMap<TermId, (Option<i64>, Option<i64>)>,
    aliases: &FxHashMap<TermId, TermId>,
) {
    if let (Some(v), Some(c)) = (bound_term(a, manager, aliases), int_const_val(b, manager)) {
        let lo = if strict { c + 1 } else { c };
        let e = bounds.entry(v).or_insert((None, None));
        e.0 = Some(e.0.map_or(lo, |x| x.max(lo)));
    } else if let (Some(c), Some(v)) = (int_const_val(a, manager), bound_term(b, manager, aliases)) {
        let hi = if strict { c - 1 } else { c };
        let e = bounds.entry(v).or_insert((None, None));
        e.1 = Some(e.1.map_or(hi, |x| x.min(hi)));
    }
}

fn note_le(
    a: TermId,
    b: TermId,
    strict: bool,
    manager: &TermManager,
    bounds: &mut FxHashMap<TermId, (Option<i64>, Option<i64>)>,
    aliases: &FxHashMap<TermId, TermId>,
) {
    if let (Some(v), Some(c)) = (bound_term(a, manager, aliases), int_const_val(b, manager)) {
        let hi = if strict { c - 1 } else { c };
        let e = bounds.entry(v).or_insert((None, None));
        e.1 = Some(e.1.map_or(hi, |x| x.min(hi)));
        // Also bind the raw term so rewritten inlined bodies keep the bound.
        if a != v {
            let e2 = bounds.entry(a).or_insert((None, None));
            e2.1 = Some(e2.1.map_or(hi, |x| x.min(hi)));
        }
    } else if let (Some(c), Some(v)) = (int_const_val(a, manager), bound_term(b, manager, aliases)) {
        let lo = if strict { c + 1 } else { c };
        let e = bounds.entry(v).or_insert((None, None));
        e.0 = Some(e.0.map_or(lo, |x| x.max(lo)));
        if b != v {
            let e2 = bounds.entry(b).or_insert((None, None));
            e2.0 = Some(e2.0.map_or(lo, |x| x.max(lo)));
        }
    } else if let Some(c) = int_const_val(b, manager) {
        // Complex term without alias: still record hi on the term itself.
        let hi = if strict { c - 1 } else { c };
        let e = bounds.entry(a).or_insert((None, None));
        e.1 = Some(e.1.map_or(hi, |x| x.min(hi)));
    } else if let Some(c) = int_const_val(a, manager) {
        let lo = if strict { c + 1 } else { c };
        let e = bounds.entry(b).or_insert((None, None));
        e.0 = Some(e.0.map_or(lo, |x| x.max(lo)));
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::solver::types::SolverResult;
    use oxiz_core::ast::TermManager;

    #[test]
    fn eq_ite_table_lookup_sat() {
        let mut solver = Solver::new();
        let mut m = TermManager::new();
        let x = m.mk_var("x", m.sorts.int_sort);
        let mut t = m.mk_int(0);
        for k in (1..=4).rev() {
            let k_t = m.mk_int(k);
            let cond = m.mk_eq(x, k_t);
            let val = m.mk_int(k * 10);
            t = m.mk_ite(cond, val, t);
        }
        let r = m.mk_var("r", m.sorts.int_sort);
        let eq_r = m.mk_eq(r, t);
        solver.assert(eq_r, &mut m);
        let three = m.mk_int(3);
        let eq_x = m.mk_eq(x, three);
        solver.assert(eq_x, &mut m);
        let thirty = m.mk_int(30);
        let eq_rv = m.mk_eq(r, thirty);
        solver.assert(eq_rv, &mut m);
        assert_eq!(solver.check(&mut m), SolverResult::Sat);
    }

    #[test]
    fn eq_ite_table_lookup_unsat() {
        let mut solver = Solver::new();
        let mut m = TermManager::new();
        let x = m.mk_var("x", m.sorts.int_sort);
        let mut t = m.mk_int(0);
        let mut domain = Vec::new();
        for k in (1..=5).rev() {
            let k_t = m.mk_int(k);
            domain.push(m.mk_eq(x, k_t));
            let cond = m.mk_eq(x, k_t);
            let val = m.mk_int(k);
            t = m.mk_ite(cond, val, t);
        }
        let r = m.mk_var("r", m.sorts.int_sort);
        let eq_r = m.mk_eq(r, t);
        solver.assert(eq_r, &mut m);
        let dom = m.mk_or(domain);
        solver.assert(dom, &mut m);
        let zero = m.mk_int(0);
        let eq0 = m.mk_eq(r, zero);
        solver.assert(eq0, &mut m);
        assert_eq!(solver.check(&mut m), SolverResult::Unsat);
    }

    #[test]
    fn long_table_discrete_choice_sat() {
        let mut solver = Solver::new();
        let mut m = TermManager::new();
        let j = m.mk_var("j", m.sorts.int_sort);
        let zero = m.mk_int(0);
        let twenty = m.mk_int(20);
        let ge0 = m.mk_ge(j, zero);
        let le20 = m.mk_le(j, twenty);
        solver.assert(ge0, &mut m);
        solver.assert(le20, &mut m);
        let mut score = m.mk_int(0);
        let rewards = [(5, 100), (7, 200), (11, 50), (15, 300), (19, 80)];
        for k in (0..=20).rev() {
            let v = rewards
                .iter()
                .find(|(kk, _)| *kk == k)
                .map(|(_, v)| *v)
                .unwrap_or(0);
            let k_t = m.mk_int(k);
            let cond = m.mk_eq(j, k_t);
            let val = m.mk_int(v);
            score = m.mk_ite(cond, val, score);
        }
        let thr = m.mk_int(250);
        let ge_s = m.mk_ge(score, thr);
        solver.assert(ge_s, &mut m);
        assert_eq!(solver.check(&mut m), SolverResult::Sat);
    }

    #[test]
    fn table_index_domain_unsat_via_bounds() {
        let mut solver = Solver::new();
        let mut m = TermManager::new();
        let x = m.mk_var("x", m.sorts.int_sort);
        let one = m.mk_int(1);
        let five = m.mk_int(5);
        let ge = m.mk_ge(x, one);
        let le = m.mk_le(x, five);
        solver.assert(ge, &mut m);
        solver.assert(le, &mut m);
        let mut t = m.mk_int(0);
        for k in (1..=5).rev() {
            let k_t = m.mk_int(k);
            let cond = m.mk_eq(x, k_t);
            let val = m.mk_int(k * 10);
            t = m.mk_ite(cond, val, t);
        }
        let r = m.mk_var("r", m.sorts.int_sort);
        let eq_r = m.mk_eq(r, t);
        solver.assert(eq_r, &mut m);
        let zero = m.mk_int(0);
        let eq0 = m.mk_eq(r, zero);
        solver.assert(eq0, &mut m);
        assert_eq!(solver.check(&mut m), SolverResult::Unsat);
    }

    #[test]
    fn comparison_links_to_domain_eqs() {
        let mut solver = Solver::new();
        let mut m = TermManager::new();
        let x = m.mk_var("x", m.sorts.int_sort);
        let zero = m.mk_int(0);
        let three = m.mk_int(3);
        let ge = m.mk_ge(x, zero);
        let le = m.mk_le(x, three);
        solver.assert(ge, &mut m);
        solver.assert(le, &mut m);
        let mut t = m.mk_int(0);
        for k in (0..=3).rev() {
            let k_t = m.mk_int(k);
            let cond = m.mk_eq(x, k_t);
            let val = m.mk_int(k * 10);
            t = m.mk_ite(cond, val, t);
        }
        let r = m.mk_var("r", m.sorts.int_sort);
        let eq_r = m.mk_eq(r, t);
        solver.assert(eq_r, &mut m);
        let two = m.mk_int(2);
        let twenty = m.mk_int(20);
        let eq_x = m.mk_eq(x, two);
        let eq_rv = m.mk_eq(r, twenty);
        solver.assert(eq_x, &mut m);
        solver.assert(eq_rv, &mut m);
        let gt = m.mk_gt(x, zero);
        solver.assert(gt, &mut m);
        assert_eq!(solver.check(&mut m), SolverResult::Sat);
    }

    #[test]
    fn zero_one_max_fold_sat() {
        let mut solver = Solver::new();
        let mut m = TermManager::new();
        let x = m.mk_var("x", m.sorts.int_sort);
        let y = m.mk_var("y", m.sorts.int_sort);
        let z = m.mk_var("z", m.sorts.int_sort);
        let zero = m.mk_int(0);
        let one = m.mk_int(1);
        let three = m.mk_int(3);
        let ge_x = m.mk_ge(x, zero);
        let le_x = m.mk_le(x, one);
        let ge_y = m.mk_ge(y, zero);
        let le_y = m.mk_le(y, one);
        let ge_z = m.mk_ge(z, zero);
        let le_z = m.mk_le(z, three);
        solver.assert(ge_x, &mut m);
        solver.assert(le_x, &mut m);
        solver.assert(ge_y, &mut m);
        solver.assert(le_y, &mut m);
        solver.assert(ge_z, &mut m);
        solver.assert(le_z, &mut m);
        let mut tx = zero;
        for k in (0..=3).rev() {
            let kt = m.mk_int(k);
            let cond = m.mk_eq(x, kt);
            let val = m.mk_int(if k <= 1 { k } else { 0 });
            tx = m.mk_ite(cond, val, tx);
        }
        let mut ty = zero;
        for k in (0..=3).rev() {
            let kt = m.mk_int(k);
            let cond = m.mk_eq(y, kt);
            let val = m.mk_int(if k <= 1 { k } else { 0 });
            ty = m.mk_ite(cond, val, ty);
        }
        let mut tz = zero;
        for k in (0..=3).rev() {
            let kt = m.mk_int(k);
            let cond = m.mk_eq(z, kt);
            let val = m.mk_int(if k <= 1 { k } else { 0 });
            tz = m.mk_ite(cond, val, tz);
        }
        let rx = m.mk_var("rx", m.sorts.int_sort);
        let ry = m.mk_var("ry", m.sorts.int_sort);
        let rz = m.mk_var("rz", m.sorts.int_sort);
        let eq_rx = m.mk_eq(rx, tx);
        let eq_ry = m.mk_eq(ry, ty);
        let eq_rz = m.mk_eq(rz, tz);
        solver.assert(eq_rx, &mut m);
        solver.assert(eq_ry, &mut m);
        solver.assert(eq_rz, &mut m);
        let gt = m.mk_gt(rx, ry);
        let mx = m.mk_ite(gt, rx, ry);
        let r = m.mk_var("r", m.sorts.int_sort);
        let eq_r = m.mk_eq(r, mx);
        solver.assert(eq_r, &mut m);
        let eq_x = m.mk_eq(x, one);
        let eq_y = m.mk_eq(y, zero);
        let eq_rv = m.mk_eq(r, one);
        solver.assert(eq_x, &mut m);
        solver.assert(eq_y, &mut m);
        solver.assert(eq_rv, &mut m);
        assert_eq!(solver.check(&mut m), SolverResult::Sat);
    }

    #[test]
    fn comparison_link_unsat_when_x_zero() {
        let mut solver = Solver::new();
        let mut m = TermManager::new();
        let x = m.mk_var("x", m.sorts.int_sort);
        let zero = m.mk_int(0);
        let three = m.mk_int(3);
        let ge = m.mk_ge(x, zero);
        let le = m.mk_le(x, three);
        solver.assert(ge, &mut m);
        solver.assert(le, &mut m);
        let mut t = m.mk_int(0);
        for k in (0..=3).rev() {
            let k_t = m.mk_int(k);
            let cond = m.mk_eq(x, k_t);
            let val = m.mk_int(k);
            t = m.mk_ite(cond, val, t);
        }
        let r = m.mk_var("r", m.sorts.int_sort);
        let eq_r = m.mk_eq(r, t);
        solver.assert(eq_r, &mut m);
        let eq_x = m.mk_eq(x, zero);
        solver.assert(eq_x, &mut m);
        let gt = m.mk_gt(x, zero);
        solver.assert(gt, &mut m);
        assert_eq!(solver.check(&mut m), SolverResult::Unsat);
    }
}
