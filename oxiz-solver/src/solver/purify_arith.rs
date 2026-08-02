//! Grammar-driven arithmetic purification.
//!
//! Under arithmetic contexts (`+`, `-`, `*`, `div`, `mod`, comparisons), any
//! subterm whose head is **not** an arithmetic constructor is replaced by a
//! fresh constant of the same numeric sort, and an interface equality
//! `fresh = original` is recorded.
//!
//! ```text
//! ArithCtor  ::= IntConst | RealConst | Var
//!              | Neg | Add | Sub | Mul | Div | Mod
//!              | Ite   (condition purified as formula; branches as arith)
//!
//! Foreign    ::= Select | Store | Apply | …  (anything else with numeric sort)
//! ```
//!
//! This is the standard SMT purification step: the arithmetic solver only ever
//! sees pure polynomials over variables; array/UF theories own the foreign
//! structure via the interface equalities.

use oxiz_core::ast::{TermId, TermKind, TermManager};
use oxiz_core::sort::SortId;
use rustc_hash::FxHashMap;

/// Result of purifying one assertion.
#[derive(Debug)]
pub struct PurifyResult {
    /// Assertion rewritten so every arith context is pure.
    pub term: TermId,
    /// Interface equalities `(fresh_const, original_foreign_term)`.
    #[allow(dead_code)]
    pub interface: Vec<(TermId, TermId)>,
}

/// Fresh-name counter shared across assertions in one solver.
#[derive(Debug, Default)]
pub struct PurifyState {
    next_id: u64,
    /// Memo: original foreign term → fresh constant (stable across asserts).
    foreign_to_fresh: FxHashMap<TermId, TermId>,
}

impl PurifyState {
    pub fn new() -> Self {
        Self::default()
    }
}

fn is_numeric_sort(manager: &TermManager, sort: SortId) -> bool {
    sort == manager.sorts.int_sort || sort == manager.sorts.real_sort
}

fn is_array_sort(manager: &TermManager, sort: SortId) -> bool {
    manager
        .sorts
        .get(sort)
        .is_some_and(|s| matches!(s.kind, oxiz_core::sort::SortKind::Array { .. }))
}

/// Head is a pure arithmetic constructor (operands still may need purification).
///
/// `Ite` is kept as a constructor so nested table-style definitions remain
/// available to the boolean layer; its condition is purified as a formula and
/// its branches as arith. Foreign leaves under those branches (select, apply)
/// still become interface constants.
fn is_arith_constructor(kind: &TermKind) -> bool {
    matches!(
        kind,
        TermKind::IntConst(_)
            | TermKind::RealConst(_)
            | TermKind::Var(_)
            | TermKind::Neg(_)
            | TermKind::Add(_)
            | TermKind::Sub(_, _)
            | TermKind::Mul(_)
            | TermKind::Div(_, _)
            | TermKind::Mod(_, _)
            | TermKind::Ite(_, _, _)
            | TermKind::Let { .. }
    )
}

/// Purify `term` for use as a top-level assertion.
pub fn purify_assertion(
    term: TermId,
    manager: &mut TermManager,
    state: &mut PurifyState,
) -> PurifyResult {
    let mut interface = Vec::new();
    let rewritten = purify_rec(term, manager, state, &mut interface, false);
    // Conjoin interface equalities so array/EUF see `c = select(...)` etc.
    if interface.is_empty() {
        return PurifyResult {
            term: rewritten,
            interface,
        };
    }
    let mut parts = vec![rewritten];
    for &(fresh, orig) in &interface {
        parts.push(manager.mk_eq(fresh, orig));
    }
    let term = if parts.len() == 1 {
        parts[0]
    } else {
        manager.mk_and(parts)
    };
    PurifyResult { term, interface }
}

fn purify_rec(
    term: TermId,
    manager: &mut TermManager,
    state: &mut PurifyState,
    interface: &mut Vec<(TermId, TermId)>,
    under_arith: bool,
) -> TermId {
    let Some(node) = manager.get(term) else {
        return term;
    };
    let kind = node.kind.clone();
    let sort = node.sort;

    // Under arith, a numeric non-constructor is a foreign leaf → fresh const.
    if under_arith && is_numeric_sort(manager, sort) && !is_arith_constructor(&kind) {
        return allocate_fresh(term, sort, manager, state, interface);
    }

    match kind {
        // --- leaves ---
        TermKind::IntConst(_)
        | TermKind::RealConst(_)
        | TermKind::Var(_)
        | TermKind::True
        | TermKind::False
        | TermKind::StringLit(_)
        | TermKind::BitVecConst { .. } => term,

        // --- arithmetic constructors: stay under arith ---
        TermKind::Neg(a) => {
            let a = purify_rec(a, manager, state, interface, true);
            manager.mk_neg(a)
        }
        TermKind::Add(args) => {
            let args: Vec<TermId> = args
                .iter()
                .map(|&a| purify_rec(a, manager, state, interface, true))
                .collect();
            manager.mk_add(args)
        }
        TermKind::Mul(args) => {
            let args: Vec<TermId> = args
                .iter()
                .map(|&a| purify_rec(a, manager, state, interface, true))
                .collect();
            manager.mk_mul(args)
        }
        TermKind::Sub(a, b) => {
            let a = purify_rec(a, manager, state, interface, true);
            let b = purify_rec(b, manager, state, interface, true);
            manager.mk_sub(a, b)
        }
        TermKind::Div(a, b) => {
            let a = purify_rec(a, manager, state, interface, true);
            let b = purify_rec(b, manager, state, interface, true);
            manager.mk_div(a, b)
        }
        TermKind::Mod(a, b) => {
            let a = purify_rec(a, manager, state, interface, true);
            let b = purify_rec(b, manager, state, interface, true);
            manager.mk_mod(a, b)
        }
        TermKind::Ite(c, t, e) => {
            // Outside arith: keep ite, purify children in their contexts.
            // (Under arith with non-constructor path already handled above —
            // ite *is* a constructor so we keep structure.)
            let c = purify_rec(c, manager, state, interface, false);
            let branch_arith = under_arith || is_numeric_sort(manager, sort);
            let t = purify_rec(t, manager, state, interface, branch_arith);
            let e = purify_rec(e, manager, state, interface, branch_arith);
            manager.mk_ite(c, t, e)
        }
        TermKind::Let { bindings, body } => {
            // `let` is transparent naming. The SMT-LIB parser usually inlines
            // names into `body` already; still purify binding values and body
            // so selects under a let inside `*` become interface constants
            // rather than collapsing the whole let to one unbound fresh var.
            for &(_, val) in bindings.iter() {
                let _ = purify_rec(val, manager, state, interface, under_arith);
            }
            purify_rec(body, manager, state, interface, under_arith)
        }

        // --- comparisons: operands enter arith ---
        TermKind::Eq(a, b) => {
            let a_sort = manager.get(a).map(|t| t.sort);
            let b_sort = manager.get(b).map(|t| t.sort);
            let numeric = a_sort.is_some_and(|s| is_numeric_sort(manager, s))
                || b_sort.is_some_and(|s| is_numeric_sort(manager, s));
            // Array equalities stay outside arith (no purification of store chains).
            let array_eq = a_sort.is_some_and(|s| is_array_sort(manager, s))
                || b_sort.is_some_and(|s| is_array_sort(manager, s));
            if array_eq {
                // Still purify nested numeric subterms in indices if any appear
                // only inside; store trees themselves are left intact.
                return term;
            }
            let a = purify_rec(a, manager, state, interface, numeric);
            let b = purify_rec(b, manager, state, interface, numeric);
            manager.mk_eq(a, b)
        }
        TermKind::Lt(a, b) => {
            let a = purify_rec(a, manager, state, interface, true);
            let b = purify_rec(b, manager, state, interface, true);
            manager.mk_lt(a, b)
        }
        TermKind::Le(a, b) => {
            let a = purify_rec(a, manager, state, interface, true);
            let b = purify_rec(b, manager, state, interface, true);
            manager.mk_le(a, b)
        }
        TermKind::Gt(a, b) => {
            let a = purify_rec(a, manager, state, interface, true);
            let b = purify_rec(b, manager, state, interface, true);
            manager.mk_gt(a, b)
        }
        TermKind::Ge(a, b) => {
            let a = purify_rec(a, manager, state, interface, true);
            let b = purify_rec(b, manager, state, interface, true);
            manager.mk_ge(a, b)
        }

        // --- boolean structure ---
        TermKind::Not(a) => {
            let a = purify_rec(a, manager, state, interface, false);
            manager.mk_not(a)
        }
        TermKind::And(args) => {
            let args: Vec<TermId> = args
                .iter()
                .map(|&a| purify_rec(a, manager, state, interface, false))
                .collect();
            manager.mk_and(args)
        }
        TermKind::Or(args) => {
            let args: Vec<TermId> = args
                .iter()
                .map(|&a| purify_rec(a, manager, state, interface, false))
                .collect();
            manager.mk_or(args)
        }
        TermKind::Xor(a, b) => {
            let a = purify_rec(a, manager, state, interface, false);
            let b = purify_rec(b, manager, state, interface, false);
            manager.mk_xor(a, b)
        }
        TermKind::Implies(a, b) => {
            let a = purify_rec(a, manager, state, interface, false);
            let b = purify_rec(b, manager, state, interface, false);
            manager.mk_implies(a, b)
        }
        TermKind::Distinct(args) => {
            let args: Vec<TermId> = args
                .iter()
                .map(|&a| {
                    let s = manager.get(a).map(|t| t.sort);
                    let num = s.is_some_and(|s| is_numeric_sort(manager, s));
                    purify_rec(a, manager, state, interface, num)
                })
                .collect();
            manager.mk_distinct(args)
        }

        // Foreign / other: if numeric under arith already handled; else leave.
        _ => term,
    }
}

fn allocate_fresh(
    original: TermId,
    sort: SortId,
    manager: &mut TermManager,
    state: &mut PurifyState,
    interface: &mut Vec<(TermId, TermId)>,
) -> TermId {
    if let Some(&f) = state.foreign_to_fresh.get(&original) {
        // Ensure this assertion's interface list mentions it (for callers that
        // only look at the per-assert interface vec).
        if !interface.iter().any(|(c, o)| *c == f && *o == original) {
            interface.push((f, original));
        }
        return f;
    }
    let name = format!("$p{}", state.next_id);
    state.next_id += 1;
    let fresh = manager.mk_var(&name, sort);
    state.foreign_to_fresh.insert(original, fresh);
    interface.push((fresh, original));
    fresh
}

/// True when a top-level assertion is purely array/UF structure (not arithmetic).
#[allow(dead_code)]
pub fn is_array_structural_assertion(term: TermId, manager: &TermManager) -> bool {
    let Some(t) = manager.get(term) else {
        return false;
    };
    match &t.kind {
        TermKind::Eq(a, b) => {
            let as_ = manager.get(*a).map(|x| x.sort);
            let bs = manager.get(*b).map(|x| x.sort);
            as_.is_some_and(|s| is_array_sort(manager, s))
                || bs.is_some_and(|s| is_array_sort(manager, s))
        }
        TermKind::And(args) => args
            .iter()
            .all(|&a| is_array_structural_assertion(a, manager)),
        _ => false,
    }
}

/// True when atom is an interface naming `var = foreign` (or swapped).
#[allow(dead_code)]
pub fn is_interface_equality(term: TermId, manager: &TermManager) -> bool {
    let Some(t) = manager.get(term) else {
        return false;
    };
    let TermKind::Eq(a, b) = &t.kind else {
        return false;
    };
    is_var_like(manager, *a) && is_foreign_numeric(manager, *b)
        || is_var_like(manager, *b) && is_foreign_numeric(manager, *a)
}

fn is_var_like(manager: &TermManager, t: TermId) -> bool {
    manager
        .get(t)
        .is_some_and(|n| matches!(n.kind, TermKind::Var(_)))
}

fn is_foreign_numeric(manager: &TermManager, t: TermId) -> bool {
    let Some(n) = manager.get(t) else {
        return false;
    };
    if !is_numeric_sort(manager, n.sort) {
        return false;
    }
    !is_arith_constructor(&n.kind)
        || matches!(
            n.kind,
            TermKind::Select(_, _) | TermKind::Apply { .. } | TermKind::Store(_, _, _)
        )
}

#[cfg(test)]
mod tests {
    use super::*;
    use oxiz_core::ast::TermManager;
    use oxiz_theories::nlsat::{NlDispatchResult, dispatch_nia_constraints};

    #[test]
    fn purifies_select_product() {
        let mut tm = TermManager::new();
        let int_s = tm.sorts.int_sort;
        let arr_s = tm.sorts.array(int_s, int_s);
        let a = tm.mk_var("A", arr_s);
        let b = tm.mk_var("B", arr_s);
        let i = tm.mk_var("i", int_s);
        let j = tm.mk_var("j", int_s);
        let sa = tm.mk_select(a, i);
        let sb = tm.mk_select(b, j);
        let prod = tm.mk_mul(vec![sa, sb]);
        let six = tm.mk_int(6);
        let eq = tm.mk_eq(prod, six);

        let mut state = PurifyState::new();
        let r = purify_assertion(eq, &mut tm, &mut state);
        assert_eq!(r.interface.len(), 2, "two selects → two interface vars");
        assert!(
            !term_has_select_under_mul(r.term, &tm),
            "arith product must be pure after purification"
        );
    }

    #[test]
    fn purified_select_box_unsat_via_nia() {
        let mut tm = TermManager::new();
        let int_s = tm.sorts.int_sort;
        let arr_s = tm.sorts.array(int_s, int_s);
        let a = tm.mk_var("A", arr_s);
        let b = tm.mk_var("B", arr_s);
        let i = tm.mk_var("i", int_s);
        let j = tm.mk_var("j", int_s);
        let sa = tm.mk_select(a, i);
        let sb = tm.mk_select(b, j);
        let one = tm.mk_int(1);
        let three = tm.mk_int(3);
        let seven = tm.mk_int(7);
        let ge_a = tm.mk_ge(sa, one);
        let le_a = tm.mk_le(sa, three);
        let ge_b = tm.mk_ge(sb, one);
        let le_b = tm.mk_le(sb, three);
        let prod = tm.mk_mul(vec![sa, sb]);
        let eq_prod = tm.mk_eq(prod, seven);
        let raw = [ge_a, le_a, ge_b, le_b, eq_prod];
        let mut state = PurifyState::new();
        let purified: Vec<_> = raw
            .into_iter()
            .map(|t| purify_assertion(t, &mut tm, &mut state).term)
            .collect();
        let r = dispatch_nia_constraints(&purified, &mut tm, true);
        assert_eq!(
            r,
            Some(NlDispatchResult::Unsat),
            "purified select box product 7 must be NIA-unsat"
        );
    }

    fn term_has_select_under_mul(term: TermId, tm: &TermManager) -> bool {
        let mut stack = vec![(term, false)];
        while let Some((id, in_mul)) = stack.pop() {
            let Some(n) = tm.get(id) else { continue };
            match &n.kind {
                TermKind::Mul(args) => {
                    for &a in args {
                        stack.push((a, true));
                    }
                }
                TermKind::Select(_, _) if in_mul => return true,
                TermKind::Add(args) | TermKind::And(args) | TermKind::Or(args) => {
                    for &a in args {
                        stack.push((a, in_mul));
                    }
                }
                TermKind::Eq(a, b)
                | TermKind::Sub(a, b)
                | TermKind::Div(a, b)
                | TermKind::Mod(a, b)
                | TermKind::Lt(a, b)
                | TermKind::Le(a, b)
                | TermKind::Gt(a, b)
                | TermKind::Ge(a, b) => {
                    stack.push((*a, in_mul));
                    stack.push((*b, in_mul));
                }
                TermKind::Neg(a) | TermKind::Not(a) => stack.push((*a, in_mul)),
                TermKind::Ite(c, a, b) => {
                    stack.push((*c, false));
                    stack.push((*a, in_mul));
                    stack.push((*b, in_mul));
                }
                _ => {}
            }
        }
        false
    }
}
