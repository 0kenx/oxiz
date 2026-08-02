//! Ground QF_ANIA decision procedure.
//!
//! Handles formulas whose arrays are defined by constant `store` towers and
//! whose free integer variables (indices and similar) lie in finite boxes.
//! Under each concrete assignment we evaluate the full term DAG — including
//! nested `select`, `ite`, `abs`-as-ite, and multi-factor products — via
//! read-over-write on the store maps.
//!
//! Works on purified assertions (`c = select(A,i)` interfaces + pure arith)
//! and on residual `ite`/`select` still present under arith after purification.

use crate::nlsat::NlDispatchResult;
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{ToPrimitive, Zero};
use oxiz_core::ast::{TermId, TermKind, TermManager};
use oxiz_core::sort::SortKind;
use std::collections::{HashMap, HashSet};

/// Soft cap on visited leaves (full assignments tried). Pruning usually keeps
/// real work far below this for constrained formulas.
const MAX_LEAVES: u64 = 5_000_000;

/// Try to decide ground-store + finite-box ANIA.
pub fn try_decide_ground_ania(
    assertions: &[TermId],
    manager: &TermManager,
) -> Option<NlDispatchResult> {
    let mut arrays: HashMap<TermId, ArrayInterp> = HashMap::new();
    let mut interfaces: Vec<Interface> = Vec::new();
    // `v = t` where `t` is evaluable once indices are bound (nullary define-fun).
    let mut definitions: Vec<(TermId, TermId)> = Vec::new();
    let mut bounds: HashMap<TermId, (Option<i64>, Option<i64>)> = HashMap::new();
    let mut atoms: Vec<Atom> = Vec::new();
    let mut bool_atoms: Vec<TermId> = Vec::new(); // must eval to true
    let mut free_ints: HashSet<TermId> = HashSet::new();
    let mut cond_defs: Vec<(TermId, TermId, TermId)> = Vec::new();

    for &a in assertions {
        collect_assertion(
            a,
            manager,
            &mut arrays,
            &mut interfaces,
            &mut definitions,
            &mut bounds,
            &mut atoms,
            &mut bool_atoms,
            &mut free_ints,
            &mut cond_defs,
        )?;
    }

    if arrays.is_empty() || (atoms.is_empty() && bool_atoms.is_empty()) {
        return None;
    }

    // Every select (in atoms or interfaces) must read a defined array.
    for atom in &atoms {
        ensure_selects_defined(atom.lhs, manager, &arrays)?;
        ensure_selects_defined(atom.rhs, manager, &arrays)?;
    }
    for &b in &bool_atoms {
        ensure_selects_defined(b, manager, &arrays)?;
    }
    for iface in &interfaces {
        if !arrays.contains_key(&iface.array) {
            return None;
        }
        collect_int_vars(iface.index, manager, &mut free_ints);
    }
    for &(_, rhs) in &definitions {
        ensure_selects_defined(rhs, manager, &arrays)?;
        collect_int_vars(rhs, manager, &mut free_ints);
    }
    // Soundness: a conditional-definition guard (`Implies(p, (= v body))` from
    // encoder-lifted `ite`) that depends on a free Boolean variable can never
    // be resolved by this integer-only enumeration, leaving `v` unbound and
    // any atom reading it silently satisfied. Refuse to decide in that case.
    if cond_defs.iter().any(|(p, _v, b)| {
        references_free_bool_var(*p, manager) || references_free_bool_var(*b, manager)
    }) {
        return None;
    }

    // Index / free int vars need finite boxes.
    let mut domains: Vec<(TermId, i64, i64)> = Vec::new();
    for &v in &free_ints {
        // Skip vars determined by interface selects, definitional eqs, or
        // conditional (encoder-lifted `ite`) definitions.
        if interfaces.iter().any(|i| i.const_var == v) {
            continue;
        }
        if definitions.iter().any(|(lhs, _)| *lhs == v) {
            continue;
        }
        if cond_defs.iter().any(|(_, var, _)| *var == v) {
            continue;
        }
        let (lo, hi) = bounds.get(&v).copied().unwrap_or((None, None));
        let lo = lo?;
        let hi = hi?;
        if hi < lo {
            return Some(NlDispatchResult::Unsat);
        }
        domains.push((v, lo, hi));
    }
    // Prefer smaller domains first for stronger early pruning.
    domains.sort_by_key(|(_, lo, hi)| hi - lo);

    // Recursive search with early pruning: once enough vars are bound to
    // evaluate an atom, reject partial assignments immediately (critical when
    // e.g. `(select A i) = c` with sparse table values kills most of 1..N).
    let mut env = HashMap::new();
    let mut leaves = 0u64;
    match search_rec(
        0,
        &domains,
        &interfaces,
        &definitions,
        &cond_defs,
        &atoms,
        &bool_atoms,
        &arrays,
        manager,
        &mut env,
        &mut leaves,
    ) {
        Some(true) => {
            let mut assignments = HashMap::new();
            for (term, val) in env {
                assignments.insert(term, BigRational::from_integer(val));
            }
            Some(NlDispatchResult::sat_with(assignments))
        }
        Some(false) => Some(NlDispatchResult::Unsat),
        None => None, // exhausted leaf budget
    }
}

/// Try to decide a *pure* nonlinear-integer formula by exhaustive finite-domain
/// enumeration. Diagnostic stub for now.
pub fn try_decide_finite_domain_nia(
    assertions: &[TermId],
    manager: &TermManager,
) -> Option<NlDispatchResult> {
    /// `true` iff `term` is concretely evaluable by the shared `eval_int`/
    /// `eval_bool` machinery once its integer variables are bound.  Rejects
    /// anything those evaluators do not handle (`div`, `mod`, uninterpreted
    /// `apply`, `select`, …) so we never report a spurious verdict, and rejects
    /// free Boolean variables (which this finite-domain search does not
    /// enumerate).
    fn fully_evaluable(term: TermId, manager: &TermManager) -> bool {
        let mut stack = vec![term];
        let mut seen = HashSet::new();
        while let Some(id) = stack.pop() {
            if !seen.insert(id) {
                continue;
            }
            let Some(n) = manager.get(id) else {
                return false;
            };
            match &n.kind {
                TermKind::IntConst(_) | TermKind::True | TermKind::False => {}
                TermKind::Var(_) => {
                    if n.sort != manager.sorts.int_sort {
                        return false;
                    }
                }
                TermKind::Neg(a) | TermKind::Not(a) => stack.push(*a),
                TermKind::Add(xs) | TermKind::Mul(xs) | TermKind::And(xs) | TermKind::Or(xs) => {
                    stack.extend(xs.iter().copied());
                }
                TermKind::Distinct(xs) => stack.extend(xs.iter().copied()),
                TermKind::Sub(a, b)
                | TermKind::Eq(a, b)
                | TermKind::Le(a, b)
                | TermKind::Lt(a, b)
                | TermKind::Ge(a, b)
                | TermKind::Gt(a, b)
                | TermKind::Implies(a, b) => {
                    stack.push(*a);
                    stack.push(*b);
                }
                TermKind::Ite(c, a, b) => {
                    stack.push(*c);
                    stack.push(*a);
                    stack.push(*b);
                }
                TermKind::Let { bindings, body } => {
                    for &(_, v) in bindings.iter() {
                        stack.push(v);
                    }
                    stack.push(*body);
                }
                // div / mod / apply / select / store / quantifiers / … — not
                // concretely evaluable here.
                _ => return false,
            }
        }
        true
    }

    let mut arrays: HashMap<TermId, ArrayInterp> = HashMap::new();
    let mut interfaces: Vec<Interface> = Vec::new();
    let mut definitions: Vec<(TermId, TermId)> = Vec::new();
    let mut bounds: HashMap<TermId, (Option<i64>, Option<i64>)> = HashMap::new();
    let mut atoms: Vec<Atom> = Vec::new();
    let mut bool_atoms: Vec<TermId> = Vec::new();
    let mut free_ints: HashSet<TermId> = HashSet::new();
    let mut cond_defs: Vec<(TermId, TermId, TermId)> = Vec::new();
    for &a in assertions {
        collect_assertion(
            a,
            manager,
            &mut arrays,
            &mut interfaces,
            &mut definitions,
            &mut bounds,
            &mut atoms,
            &mut bool_atoms,
            &mut free_ints,
            &mut cond_defs,
        )?;
    }
    // This path is for *pure* integer arithmetic; defer ground-store formulas
    // (arrays) to [`try_decide_ground_ania`].
    if !arrays.is_empty() {
        return None;
    }
    // Any purification interface (`c = (select A i)`) must read a *defined*
    // array — but `arrays` is empty here (no stores), so an uninterpreted
    // array select cannot be concretely evaluated. Refuse to decide rather
    // than report a false verdict.
    if interfaces.iter().any(|i| !arrays.contains_key(&i.array)) {
        return None;
    }
    if atoms.is_empty() && bool_atoms.is_empty() {
        return None;
    }
    // Soundness gate: every atom/bool_atom must reduce to a concrete Boolean
    // once its integer variables are bound.  An unevaluable atom (div/mod/
    // apply/…) would make `eval_atom` return `false` for every assignment and
    // yield a false `Unsat`; refuse to decide instead.
    for atom in &atoms {
        if !fully_evaluable(atom.lhs, manager) || !fully_evaluable(atom.rhs, manager) {
            return None;
        }
    }
    for &b in &bool_atoms {
        if !fully_evaluable(b, manager) {
            return None;
        }
    }
    // Conditional-definition guards (`Implies(p, (= v body))` from encoder-
    // lifted `ite`) must also be concretely decidable once the enumerated
    // integers are bound. A guard that references a free Boolean variable
    // (never enumerated here) could neither fire nor be refuted, leaving `v`
    // unbound and the atom that reads it silently satisfied — a false `Sat`.
    for &(premise, _var, body) in &cond_defs {
        if !fully_evaluable(premise, manager) || !fully_evaluable(body, manager) {
            return None;
        }
    }
    // Every free integer variable must carry a small arithmetic box, else the
    // search space is not finite (or too large) — bail to the caller.
    let mut domains: Vec<(TermId, i64, i64)> = Vec::new();
    let mut total: u64 = 1;
    for &v in &free_ints {
        if interfaces.iter().any(|i| i.const_var == v)
            || definitions.iter().any(|(l, _)| *l == v)
            || cond_defs.iter().any(|(_, var, _)| *var == v)
        {
            continue;
        }
        let (lo, hi) = bounds.get(&v).copied().unwrap_or((None, None));
        let lo = lo?;
        let hi = hi?;
        if hi < lo {
            return Some(NlDispatchResult::Unsat);
        }
        let size = (hi - lo + 1) as u64;
        total = total.checked_mul(size)?;
        if total > MAX_LEAVES {
            return None;
        }
        domains.push((v, lo, hi));
    }
    // Smaller domains first → stronger early pruning.
    domains.sort_by_key(|(_, lo, hi)| hi - lo);

    let mut env = HashMap::new();
    let mut leaves = 0u64;
    match search_rec(
        0,
        &domains,
        &interfaces,
        &definitions,
        &cond_defs,
        &atoms,
        &bool_atoms,
        &arrays,
        manager,
        &mut env,
        &mut leaves,
    ) {
        Some(true) => {
            let mut assignments = HashMap::new();
            for (term, val) in env {
                assignments.insert(term, BigRational::from_integer(val));
            }
            Some(NlDispatchResult::sat_with(assignments))
        }
        Some(false) => Some(NlDispatchResult::Unsat),
        None => None, // exhausted the leaf budget
    }
}

fn realize_interfaces(
    interfaces: &[Interface],
    definitions: &[(TermId, TermId)],
    arrays: &HashMap<TermId, ArrayInterp>,
    manager: &TermManager,
    env: &mut HashMap<TermId, BigInt>,
) -> bool {
    for iface in interfaces {
        let Some(idx_val) = eval_int(iface.index, manager, arrays, env) else {
            continue; // index not yet bound — skip for now
        };
        let Some(i64v) = idx_val.to_i64() else {
            return false;
        };
        let Some(interp) = arrays.get(&iface.array) else {
            return false;
        };
        let sel = interp
            .entries
            .get(&i64v)
            .cloned()
            .unwrap_or_else(|| interp.default.clone());
        env.insert(iface.const_var, sel);
    }
    // Definitional eqs from nullary define-fun: `P = (* (select A i) …)`.
    // Evaluate rhs once its free vars are bound; bind lhs.
    for &(lhs, rhs) in definitions {
        if env.contains_key(&lhs) {
            continue;
        }
        if !term_fully_bound(rhs, manager, env, arrays) {
            continue;
        }
        let Some(v) = eval_int(rhs, manager, arrays, env) else {
            return false;
        };
        env.insert(lhs, v);
    }
    true
}

/// Resolve conditional definitions `(premise, var, body)` (encoder-lifted
/// `ite` fresh constants) into `env` to a fixpoint. A guard whose variables are
/// all bound and that evaluates `true` pins `var := eval(body)`. Returns `false`
/// if two fired guards disagree on a variable (the assignment is inconsistent).
fn realize_cond_defs(
    cond_defs: &[(TermId, TermId, TermId)],
    arrays: &HashMap<TermId, ArrayInterp>,
    manager: &TermManager,
    env: &mut HashMap<TermId, BigInt>,
) -> bool {
    let mut changed = true;
    while changed {
        changed = false;
        for &(premise, var, body) in cond_defs {
            if env.contains_key(&var) {
                continue;
            }
            if !term_fully_bound(premise, manager, env, arrays) {
                continue;
            }
            // Guard did not fire → skip (the variable may be pinned by another
            // guard, or stay unbound if no `ite` branch matches).
            match eval_bool(premise, manager, arrays, env) {
                Some(true) => {}
                _ => continue,
            }
            if !term_fully_bound(body, manager, env, arrays) {
                continue;
            }
            let Some(v) = eval_int(body, manager, arrays, env) else {
                return false;
            };
            env.insert(var, v);
            changed = true;
        }
    }
    true
}

fn partial_atoms_ok(
    atoms: &[Atom],
    bool_atoms: &[TermId],
    arrays: &HashMap<TermId, ArrayInterp>,
    manager: &TermManager,
    env: &HashMap<TermId, BigInt>,
) -> bool {
    for atom in atoms {
        // Only check atoms whose free vars are all bound.
        if !term_fully_bound(atom.lhs, manager, env, arrays) {
            continue;
        }
        if !term_fully_bound(atom.rhs, manager, env, arrays) {
            continue;
        }
        if !eval_atom(atom, manager, arrays, env) {
            return false;
        }
    }
    for &b in bool_atoms {
        if !term_fully_bound(b, manager, env, arrays) {
            continue;
        }
        match eval_bool(b, manager, arrays, env) {
            Some(true) => {}
            _ => return false,
        }
    }
    true
}

fn term_fully_bound(
    term: TermId,
    manager: &TermManager,
    env: &HashMap<TermId, BigInt>,
    arrays: &HashMap<TermId, ArrayInterp>,
) -> bool {
    let mut stack = vec![term];
    let mut seen = HashSet::new();
    while let Some(id) = stack.pop() {
        if !seen.insert(id) {
            continue;
        }
        if env.contains_key(&id) {
            continue;
        }
        let Some(n) = manager.get(id) else {
            return false;
        };
        match &n.kind {
            TermKind::IntConst(_) | TermKind::True | TermKind::False => {}
            TermKind::Var(_) => return false,
            TermKind::Select(arr, idx) => {
                if !arrays.contains_key(arr) {
                    return false;
                }
                stack.push(*idx);
            }
            TermKind::Add(xs) | TermKind::Mul(xs) | TermKind::And(xs) | TermKind::Or(xs) => {
                stack.extend(xs.iter().copied())
            }
            TermKind::Neg(a) | TermKind::Not(a) => stack.push(*a),
            TermKind::Sub(a, b)
            | TermKind::Div(a, b)
            | TermKind::Mod(a, b)
            | TermKind::Eq(a, b)
            | TermKind::Le(a, b)
            | TermKind::Lt(a, b)
            | TermKind::Ge(a, b)
            | TermKind::Gt(a, b) => {
                stack.push(*a);
                stack.push(*b);
            }
            TermKind::Ite(c, a, b) => {
                stack.push(*c);
                stack.push(*a);
                stack.push(*b);
            }
            TermKind::Let { bindings, body } => {
                for &(_, v) in bindings.iter() {
                    stack.push(v);
                }
                stack.push(*body);
            }
            _ => return false,
        }
    }
    true
}

/// `Some(true)` sat, `Some(false)` unsat (subtree exhausted), `None` budget.
#[allow(clippy::too_many_arguments)]
fn search_rec(
    pos: usize,
    domains: &[(TermId, i64, i64)],
    interfaces: &[Interface],
    definitions: &[(TermId, TermId)],
    cond_defs: &[(TermId, TermId, TermId)],
    atoms: &[Atom],
    bool_atoms: &[TermId],
    arrays: &HashMap<TermId, ArrayInterp>,
    manager: &TermManager,
    env: &mut HashMap<TermId, BigInt>,
    leaves: &mut u64,
) -> Option<bool> {
    if !realize_interfaces(interfaces, definitions, arrays, manager, env) {
        return Some(false);
    }
    // Derive conditionally-defined integer variables (encoder-lifted `ite`
    // fresh constants) to a fixpoint: a guard `p` whose variables are all
    // bound and that evaluates `true` pins its variable. Two guards firing
    // with disagreeing values make this assignment inconsistent.
    if !realize_cond_defs(cond_defs, arrays, manager, env) {
        return Some(false);
    }
    if !partial_atoms_ok(atoms, bool_atoms, arrays, manager, env) {
        return Some(false);
    }
    if pos == domains.len() {
        *leaves += 1;
        if *leaves > MAX_LEAVES {
            return None;
        }
        // Full assignment — atoms already checked when fully bound.
        return Some(true);
    }
    let (var, lo, hi) = domains[pos];
    for v in lo..=hi {
        env.insert(var, BigInt::from(v));
        match search_rec(
            pos + 1,
            domains,
            interfaces,
            definitions,
            cond_defs,
            atoms,
            bool_atoms,
            arrays,
            manager,
            env,
            leaves,
        ) {
            Some(true) => return Some(true),
            Some(false) => {}
            None => return None,
        }
        env.remove(&var);
    }
    Some(false)
}

#[derive(Clone, Debug)]
pub(crate) struct ArrayInterp {
    default: BigInt,
    entries: HashMap<i64, BigInt>,
}

#[derive(Clone, Debug)]
struct Interface {
    const_var: TermId,
    array: TermId,
    index: TermId,
}

#[derive(Clone, Debug)]
struct Atom {
    kind: CmpKind,
    lhs: TermId,
    rhs: TermId,
}

#[derive(Clone, Copy, Debug)]
enum CmpKind {
    Eq,
    Le,
    Lt,
    Ge,
    Gt,
}

#[allow(clippy::too_many_arguments)]
fn collect_assertion(
    term: TermId,
    manager: &TermManager,
    arrays: &mut HashMap<TermId, ArrayInterp>,
    interfaces: &mut Vec<Interface>,
    definitions: &mut Vec<(TermId, TermId)>,
    bounds: &mut HashMap<TermId, (Option<i64>, Option<i64>)>,
    atoms: &mut Vec<Atom>,
    bool_atoms: &mut Vec<TermId>,
    free_ints: &mut HashSet<TermId>,
    cond_defs: &mut Vec<(TermId, TermId, TermId)>,
) -> Option<()> {
    let t = manager.get(term)?;
    match &t.kind {
        TermKind::And(args) => {
            for &a in args {
                collect_assertion(
                    a,
                    manager,
                    arrays,
                    interfaces,
                    definitions,
                    bounds,
                    atoms,
                    bool_atoms,
                    free_ints,
                    cond_defs,
                )?;
            }
            Some(())
        }
        TermKind::True => Some(()),
        TermKind::Not(_) | TermKind::Or(_) | TermKind::Implies(_, _) => {
            // A conditional definition `Implies(p, (= v body))` with `v` a free
            // integer variable (the encoder lifts non-Bool `ite` into exactly
            // this shape) is recorded separately so the search can derive `v`
            // once `p`'s variables are bound, instead of treating it as an
            // opaque Boolean.  Anything else is a plain Boolean constraint.
            if let TermKind::Implies(p, q) = &t.kind
                && let Some((v, body)) = parse_cond_definition(*q, manager)
            {
                free_ints.insert(v);
                collect_int_vars(*p, manager, free_ints);
                collect_int_vars(body, manager, free_ints);
                cond_defs.push((*p, v, body));
                return Some(());
            }
            // Boolean constraint that must hold (e.g. negated predicates,
            // disjunctions, or non-definitional implications).
            collect_int_vars(term, manager, free_ints);
            bool_atoms.push(term);
            Some(())
        }
        TermKind::Eq(lhs, rhs) => {
            if is_array_sorted(manager, *lhs) || is_array_sorted(manager, *rhs) {
                let (var, def) = if is_array_var(manager, *lhs) {
                    (*lhs, *rhs)
                } else if is_array_var(manager, *rhs) {
                    (*rhs, *lhs)
                } else {
                    return None;
                };
                arrays.insert(var, eval_array_def(def, manager)?);
                return Some(());
            }
            if let Some(iface) = parse_interface(manager, *lhs, *rhs) {
                interfaces.push(iface);
                return Some(());
            }
            // Definitional equality from nullary define-fun:
            //   P = (* (select A i) (select B i))
            // Bind P when the rhs is evaluable; do not search over P.
            if let Some((v, body)) = parse_definition(manager, *lhs, *rhs) {
                definitions.push((v, body));
                collect_int_vars(body, manager, free_ints);
                return Some(());
            }
            if let Some((v, lo, hi)) = parse_bound_eq(manager, *lhs, *rhs) {
                tighten(bounds, v, lo, hi);
                free_ints.insert(v);
            }
            collect_int_vars(*lhs, manager, free_ints);
            collect_int_vars(*rhs, manager, free_ints);
            atoms.push(Atom {
                kind: CmpKind::Eq,
                lhs: *lhs,
                rhs: *rhs,
            });
            Some(())
        }
        TermKind::Le(a, b) | TermKind::Lt(a, b) | TermKind::Ge(a, b) | TermKind::Gt(a, b) => {
            if let Some((v, lo, hi)) = parse_bound_cmp(manager, term) {
                tighten(bounds, v, lo, hi);
                free_ints.insert(v);
            }
            let kind = match &t.kind {
                TermKind::Le(_, _) => CmpKind::Le,
                TermKind::Lt(_, _) => CmpKind::Lt,
                TermKind::Ge(_, _) => CmpKind::Ge,
                _ => CmpKind::Gt,
            };
            collect_int_vars(*a, manager, free_ints);
            collect_int_vars(*b, manager, free_ints);
            atoms.push(Atom {
                kind,
                lhs: *a,
                rhs: *b,
            });
            Some(())
        }
        _ => None,
    }
}

fn collect_int_vars(term: TermId, manager: &TermManager, out: &mut HashSet<TermId>) {
    let mut stack = vec![term];
    let mut seen = HashSet::new();
    while let Some(id) = stack.pop() {
        if !seen.insert(id) {
            continue;
        }
        let Some(n) = manager.get(id) else { continue };
        match &n.kind {
            TermKind::Var(_) if n.sort == manager.sorts.int_sort => {
                out.insert(id);
            }
            TermKind::Add(xs) | TermKind::Mul(xs) | TermKind::And(xs) | TermKind::Or(xs) => {
                stack.extend(xs.iter().copied())
            }
            TermKind::Neg(a) | TermKind::Not(a) => stack.push(*a),
            TermKind::Sub(a, b)
            | TermKind::Div(a, b)
            | TermKind::Mod(a, b)
            | TermKind::Eq(a, b)
            | TermKind::Le(a, b)
            | TermKind::Lt(a, b)
            | TermKind::Ge(a, b)
            | TermKind::Gt(a, b)
            | TermKind::Select(a, b) => {
                stack.push(*a);
                stack.push(*b);
            }
            TermKind::Ite(c, a, b) | TermKind::Store(c, a, b) => {
                stack.push(*c);
                stack.push(*a);
                stack.push(*b);
            }
            TermKind::Let { bindings, body } => {
                for &(_, v) in bindings.iter() {
                    stack.push(v);
                }
                stack.push(*body);
            }
            TermKind::Apply { args, .. } => stack.extend(args.iter().copied()),
            _ => {}
        }
    }
}

fn ensure_selects_defined(
    term: TermId,
    manager: &TermManager,
    arrays: &HashMap<TermId, ArrayInterp>,
) -> Option<()> {
    let mut stack = vec![term];
    let mut seen = HashSet::new();
    while let Some(id) = stack.pop() {
        if !seen.insert(id) {
            continue;
        }
        let n = manager.get(id)?;
        match &n.kind {
            TermKind::Select(arr, idx) => {
                if !arrays.contains_key(arr) {
                    return None;
                }
                stack.push(*idx);
            }
            TermKind::Add(xs) | TermKind::Mul(xs) => stack.extend(xs.iter().copied()),
            TermKind::Neg(a) | TermKind::Not(a) => stack.push(*a),
            TermKind::Sub(a, b)
            | TermKind::Div(a, b)
            | TermKind::Mod(a, b)
            | TermKind::Eq(a, b)
            | TermKind::Le(a, b)
            | TermKind::Lt(a, b)
            | TermKind::Ge(a, b)
            | TermKind::Gt(a, b) => {
                stack.push(*a);
                stack.push(*b);
            }
            TermKind::Ite(c, a, b) => {
                stack.push(*c);
                stack.push(*a);
                stack.push(*b);
            }
            TermKind::Let { bindings, body } => {
                for &(_, v) in bindings.iter() {
                    stack.push(v);
                }
                stack.push(*body);
            }
            TermKind::And(xs) | TermKind::Or(xs) => stack.extend(xs.iter().copied()),
            TermKind::Distinct(xs) => stack.extend(xs.iter().copied()),
            TermKind::Implies(a, b) => {
                stack.push(*a);
                stack.push(*b);
            }
            TermKind::Var(_) | TermKind::IntConst(_) | TermKind::True | TermKind::False => {}
            _ => return None,
        }
    }
    Some(())
}

/// Evaluate integer or boolean term under env + arrays.
pub(crate) fn eval_int(
    term: TermId,
    manager: &TermManager,
    arrays: &HashMap<TermId, ArrayInterp>,
    env: &HashMap<TermId, BigInt>,
) -> Option<BigInt> {
    if let Some(v) = env.get(&term) {
        return Some(v.clone());
    }
    let n = manager.get(term)?;
    match &n.kind {
        TermKind::IntConst(k) => Some(k.clone()),
        TermKind::Var(_) => None, // unbound
        TermKind::Neg(a) => Some(-eval_int(*a, manager, arrays, env)?),
        TermKind::Add(xs) => {
            let mut s = BigInt::zero();
            for &x in xs {
                s += eval_int(x, manager, arrays, env)?;
            }
            Some(s)
        }
        TermKind::Mul(xs) => {
            let mut p = BigInt::from(1);
            for &x in xs {
                p *= eval_int(x, manager, arrays, env)?;
            }
            Some(p)
        }
        TermKind::Sub(a, b) => {
            Some(eval_int(*a, manager, arrays, env)? - eval_int(*b, manager, arrays, env)?)
        }
        TermKind::Select(arr, idx) => {
            let i = eval_int(*idx, manager, arrays, env)?;
            let i64v = i.to_i64()?;
            let interp = arrays.get(arr)?;
            Some(
                interp
                    .entries
                    .get(&i64v)
                    .cloned()
                    .unwrap_or_else(|| interp.default.clone()),
            )
        }
        TermKind::Ite(c, a, b) => {
            if eval_bool(*c, manager, arrays, env)? {
                eval_int(*a, manager, arrays, env)
            } else {
                eval_int(*b, manager, arrays, env)
            }
        }
        TermKind::Let { bindings, body } => {
            // Parser inlines let-names into the body via the binding table while
            // parsing, so `body` already contains the bound values as subterms.
            // Still evaluate binding values first (in case substitute left name
            // vars), then body. Bindings are `(name_spur, value_term)`.
            let local = env.clone();
            for &(_name, val_term) in bindings {
                // Force evaluation of binding values (side-effect free).
                let _ = eval_int(val_term, manager, arrays, &local)?;
            }
            eval_int(*body, manager, arrays, &local)
        }
        _ => None,
    }
}

pub(crate) fn eval_bool(
    term: TermId,
    manager: &TermManager,
    arrays: &HashMap<TermId, ArrayInterp>,
    env: &HashMap<TermId, BigInt>,
) -> Option<bool> {
    let n = manager.get(term)?;
    match &n.kind {
        TermKind::True => Some(true),
        TermKind::False => Some(false),
        TermKind::Not(a) => Some(!eval_bool(*a, manager, arrays, env)?),
        TermKind::And(xs) => {
            for &x in xs {
                if !eval_bool(x, manager, arrays, env)? {
                    return Some(false);
                }
            }
            Some(true)
        }
        TermKind::Or(xs) => {
            for &x in xs {
                if eval_bool(x, manager, arrays, env)? {
                    return Some(true);
                }
            }
            Some(false)
        }
        TermKind::Eq(a, b) => {
            // Could be int or bool eq
            if manager
                .get(*a)
                .is_some_and(|t| t.sort == manager.sorts.bool_sort)
            {
                Some(eval_bool(*a, manager, arrays, env)? == eval_bool(*b, manager, arrays, env)?)
            } else {
                Some(eval_int(*a, manager, arrays, env)? == eval_int(*b, manager, arrays, env)?)
            }
        }
        TermKind::Le(a, b) => {
            Some(eval_int(*a, manager, arrays, env)? <= eval_int(*b, manager, arrays, env)?)
        }
        TermKind::Lt(a, b) => {
            Some(eval_int(*a, manager, arrays, env)? < eval_int(*b, manager, arrays, env)?)
        }
        TermKind::Ge(a, b) => {
            Some(eval_int(*a, manager, arrays, env)? >= eval_int(*b, manager, arrays, env)?)
        }
        TermKind::Gt(a, b) => {
            Some(eval_int(*a, manager, arrays, env)? > eval_int(*b, manager, arrays, env)?)
        }
        TermKind::Ite(c, a, b) => {
            if eval_bool(*c, manager, arrays, env)? {
                eval_bool(*a, manager, arrays, env)
            } else {
                eval_bool(*b, manager, arrays, env)
            }
        }
        TermKind::Implies(a, b) => {
            Some(!eval_bool(*a, manager, arrays, env)? || eval_bool(*b, manager, arrays, env)?)
        }
        TermKind::Distinct(args) => {
            // All pairwise-distinct over evaluable int terms.
            let mut seen: Vec<BigInt> = Vec::with_capacity(args.len());
            for &x in args {
                let v = eval_int(x, manager, arrays, env)?;
                if seen.contains(&v) {
                    return Some(false);
                }
                seen.push(v);
            }
            Some(true)
        }
        _ => None,
    }
}

fn eval_atom(
    atom: &Atom,
    manager: &TermManager,
    arrays: &HashMap<TermId, ArrayInterp>,
    env: &HashMap<TermId, BigInt>,
) -> bool {
    let Some(l) = eval_int(atom.lhs, manager, arrays, env) else {
        return false;
    };
    let Some(r) = eval_int(atom.rhs, manager, arrays, env) else {
        return false;
    };
    match atom.kind {
        CmpKind::Eq => l == r,
        CmpKind::Le => l <= r,
        CmpKind::Lt => l < r,
        CmpKind::Ge => l >= r,
        CmpKind::Gt => l > r,
    }
}

fn parse_interface(manager: &TermManager, a: TermId, b: TermId) -> Option<Interface> {
    let one = |c, s| {
        let cn = manager.get(c)?;
        let sn = manager.get(s)?;
        if !matches!(cn.kind, TermKind::Var(_)) {
            return None;
        }
        let TermKind::Select(arr, idx) = &sn.kind else {
            return None;
        };
        Some(Interface {
            const_var: c,
            array: *arr,
            index: *idx,
        })
    };
    one(a, b).or_else(|| one(b, a))
}

/// `v = t` where `v` is a variable and `t` is a non-variable evaluable term
/// (nullary define-fun body: product of selects, ite, …).
fn parse_definition(manager: &TermManager, a: TermId, b: TermId) -> Option<(TermId, TermId)> {
    let one = |v, body| {
        as_var(manager, v)?;
        // Body must not itself be a bare variable or numeral-only (those are
        // ordinary eqs / bounds).
        if as_var(manager, body).is_some() || eval_ground_int(body, manager).is_some() {
            return None;
        }
        // Must be evaluable under a concrete index env (select/ite/mul/…).
        if !is_evaluable_arith(body, manager) {
            return None;
        }
        Some((v, body))
    };
    one(a, b).or_else(|| one(b, a))
}

fn is_evaluable_arith(term: TermId, manager: &TermManager) -> bool {
    let mut stack = vec![term];
    let mut seen = HashSet::new();
    while let Some(id) = stack.pop() {
        if !seen.insert(id) {
            continue;
        }
        let Some(n) = manager.get(id) else {
            return false;
        };
        match &n.kind {
            TermKind::IntConst(_) | TermKind::Var(_) => {}
            TermKind::Neg(a) | TermKind::Not(a) => stack.push(*a),
            TermKind::Add(xs) | TermKind::Mul(xs) | TermKind::And(xs) | TermKind::Or(xs) => {
                stack.extend(xs.iter().copied())
            }
            TermKind::Sub(a, b)
            | TermKind::Div(a, b)
            | TermKind::Mod(a, b)
            | TermKind::Eq(a, b)
            | TermKind::Le(a, b)
            | TermKind::Lt(a, b)
            | TermKind::Ge(a, b)
            | TermKind::Gt(a, b)
            | TermKind::Select(a, b) => {
                stack.push(*a);
                stack.push(*b);
            }
            TermKind::Ite(c, a, b) => {
                stack.push(*c);
                stack.push(*a);
                stack.push(*b);
            }
            TermKind::Let { bindings, body } => {
                for &(_, v) in bindings.iter() {
                    stack.push(v);
                }
                stack.push(*body);
            }
            _ => return false,
        }
    }
    true
}

fn is_array_sorted(manager: &TermManager, t: TermId) -> bool {
    manager.get(t).is_some_and(|n| {
        manager
            .sorts
            .get(n.sort)
            .is_some_and(|s| matches!(s.kind, SortKind::Array { .. }))
    })
}

fn is_array_var(manager: &TermManager, t: TermId) -> bool {
    manager
        .get(t)
        .is_some_and(|n| matches!(n.kind, TermKind::Var(_)) && is_array_sorted(manager, t))
}

fn eval_array_def(term: TermId, manager: &TermManager) -> Option<ArrayInterp> {
    let mut cur = term;
    let mut entries_rev: Vec<(i64, BigInt)> = Vec::new();
    loop {
        let n = manager.get(cur)?;
        match &n.kind {
            TermKind::Store(arr, idx, val) => {
                let i = eval_ground_int(*idx, manager)?;
                let v = eval_ground_int(*val, manager)?;
                entries_rev.push((i, BigInt::from(v)));
                cur = *arr;
            }
            TermKind::Apply { func, args } => {
                let name = manager.resolve_str(*func);
                if name.contains("const") && args.len() == 1 {
                    let d = eval_ground_int(args[0], manager)?;
                    let mut entries = HashMap::new();
                    for (i, v) in entries_rev.into_iter().rev() {
                        entries.insert(i, v);
                    }
                    return Some(ArrayInterp {
                        default: BigInt::from(d),
                        entries,
                    });
                }
                return None;
            }
            _ => return None,
        }
    }
}

fn eval_ground_int(term: TermId, manager: &TermManager) -> Option<i64> {
    let n = manager.get(term)?;
    match &n.kind {
        TermKind::IntConst(k) => k.to_i64(),
        TermKind::Neg(inner) => Some(-eval_ground_int(*inner, manager)?),
        _ => None,
    }
}

fn parse_bound_eq(
    manager: &TermManager,
    lhs: TermId,
    rhs: TermId,
) -> Option<(TermId, Option<i64>, Option<i64>)> {
    if let (Some(v), Some(k)) = (as_var(manager, lhs), eval_ground_int(rhs, manager)) {
        return Some((v, Some(k), Some(k)));
    }
    if let (Some(v), Some(k)) = (as_var(manager, rhs), eval_ground_int(lhs, manager)) {
        return Some((v, Some(k), Some(k)));
    }
    None
}

fn parse_bound_cmp(
    manager: &TermManager,
    term: TermId,
) -> Option<(TermId, Option<i64>, Option<i64>)> {
    let n = manager.get(term)?;
    match &n.kind {
        TermKind::Ge(a, b) => {
            if let (Some(v), Some(k)) = (as_var(manager, *a), eval_ground_int(*b, manager)) {
                return Some((v, Some(k), None));
            }
        }
        TermKind::Gt(a, b) => {
            if let (Some(v), Some(k)) = (as_var(manager, *a), eval_ground_int(*b, manager)) {
                return Some((v, Some(k + 1), None));
            }
        }
        TermKind::Le(a, b) => {
            if let (Some(v), Some(k)) = (as_var(manager, *a), eval_ground_int(*b, manager)) {
                return Some((v, None, Some(k)));
            }
        }
        TermKind::Lt(a, b) => {
            if let (Some(v), Some(k)) = (as_var(manager, *a), eval_ground_int(*b, manager)) {
                return Some((v, None, Some(k - 1)));
            }
        }
        _ => {}
    }
    None
}

fn as_var(manager: &TermManager, t: TermId) -> Option<TermId> {
    manager
        .get(t)
        .and_then(|n| matches!(n.kind, TermKind::Var(_)).then_some(t))
}

/// Parse `Implies(p, q)` conclusion `q` as a definitional equality `(= v body)`
/// with `v` a free integer variable (either side). Returns `(v, body)`.
/// This is the shape produced when the encoder lifts a non-Bool `ite` term to
/// a fresh constant plus guarded equalities.
fn parse_cond_definition(q: TermId, manager: &TermManager) -> Option<(TermId, TermId)> {
    let n = manager.get(q)?;
    let TermKind::Eq(a, b) = &n.kind else {
        return None;
    };
    let a_var = as_var(manager, *a);
    let b_var = as_var(manager, *b);
    match (a_var, b_var) {
        (Some(v), None) => Some((v, *b)),
        (None, Some(v)) => Some((v, *a)),
        _ => None,
    }
}

/// `true` iff `term` mentions a free Boolean-sorted variable. The finite-domain
/// searches enumerate only integer variables, so a Boolean variable that an
/// atom, a Boolean constraint, or an encoder-lifted-`ite` guard depends on can
/// neither be pinned nor refuted — its dependent term stays unbound and would
/// be silently satisfied. Callers must refuse to decide in that case.
fn references_free_bool_var(term: TermId, manager: &TermManager) -> bool {
    let mut stack = vec![term];
    let mut seen = HashSet::new();
    while let Some(id) = stack.pop() {
        if !seen.insert(id) {
            continue;
        }
        let Some(n) = manager.get(id) else { continue };
        match &n.kind {
            TermKind::Var(_) => {
                if n.sort == manager.sorts.bool_sort {
                    return true;
                }
            }
            TermKind::Neg(a) | TermKind::Not(a) => stack.push(*a),
            TermKind::Add(xs) | TermKind::Mul(xs) | TermKind::And(xs) | TermKind::Or(xs) => {
                stack.extend(xs.iter().copied());
            }
            TermKind::Distinct(xs) => stack.extend(xs.iter().copied()),
            TermKind::Sub(a, b)
            | TermKind::Eq(a, b)
            | TermKind::Le(a, b)
            | TermKind::Lt(a, b)
            | TermKind::Ge(a, b)
            | TermKind::Gt(a, b)
            | TermKind::Implies(a, b) => {
                stack.push(*a);
                stack.push(*b);
            }
            TermKind::Ite(c, a, b) => {
                stack.push(*c);
                stack.push(*a);
                stack.push(*b);
            }
            TermKind::Let { bindings, body } => {
                for &(_, v) in bindings.iter() {
                    stack.push(v);
                }
                stack.push(*body);
            }
            _ => {}
        }
    }
    false
}

fn tighten(
    bounds: &mut HashMap<TermId, (Option<i64>, Option<i64>)>,
    v: TermId,
    lo: Option<i64>,
    hi: Option<i64>,
) {
    let e = bounds.entry(v).or_insert((None, None));
    if let Some(l) = lo {
        e.0 = Some(e.0.map_or(l, |x| x.max(l)));
    }
    if let Some(h) = hi {
        e.1 = Some(e.1.map_or(h, |x| x.min(h)));
    }
}

/// True if any assertion contains a `store`.
pub fn assertions_contain_store(assertions: &[TermId], manager: &TermManager) -> bool {
    assertions.iter().any(|&a| term_contains_store(a, manager))
}

fn term_contains_store(term: TermId, manager: &TermManager) -> bool {
    let mut stack = vec![term];
    let mut seen = HashSet::new();
    while let Some(id) = stack.pop() {
        if !seen.insert(id) {
            continue;
        }
        let Some(n) = manager.get(id) else { continue };
        match &n.kind {
            TermKind::Store(_, _, _) => return true,
            TermKind::And(xs) | TermKind::Or(xs) | TermKind::Add(xs) | TermKind::Mul(xs) => {
                stack.extend(xs.iter().copied())
            }
            TermKind::Eq(a, b)
            | TermKind::Le(a, b)
            | TermKind::Lt(a, b)
            | TermKind::Ge(a, b)
            | TermKind::Gt(a, b)
            | TermKind::Sub(a, b)
            | TermKind::Select(a, b) => {
                stack.push(*a);
                stack.push(*b);
            }
            TermKind::Neg(a) | TermKind::Not(a) => stack.push(*a),
            TermKind::Ite(c, a, b) => {
                stack.push(*c);
                stack.push(*a);
                stack.push(*b);
            }
            TermKind::Apply { args, .. } => stack.extend(args.iter().copied()),
            _ => {}
        }
    }
    false
}
