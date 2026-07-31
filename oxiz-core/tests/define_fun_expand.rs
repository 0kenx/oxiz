use oxiz_core::ast::{TermKind, TermManager};
use oxiz_core::smtlib::{Command, parse_script};

fn term_mentions_var(tm: &TermManager, id: oxiz_core::ast::TermId, name: &str) -> bool {
    let Some(t) = tm.get(id) else {
        return false;
    };
    match &t.kind {
        TermKind::Var(s) => tm.resolve_str(*s) == name,
        TermKind::Not(a) | TermKind::Neg(a) => term_mentions_var(tm, *a, name),
        TermKind::And(xs) | TermKind::Or(xs) | TermKind::Add(xs) | TermKind::Mul(xs) => {
            xs.iter().any(|&x| term_mentions_var(tm, x, name))
        }
        TermKind::Eq(a, b)
        | TermKind::Lt(a, b)
        | TermKind::Le(a, b)
        | TermKind::Gt(a, b)
        | TermKind::Ge(a, b)
        | TermKind::Sub(a, b)
        | TermKind::Xor(a, b)
        | TermKind::Implies(a, b) => {
            term_mentions_var(tm, *a, name) || term_mentions_var(tm, *b, name)
        }
        TermKind::Ite(c, a, b) => {
            term_mentions_var(tm, *c, name)
                || term_mentions_var(tm, *a, name)
                || term_mentions_var(tm, *b, name)
        }
        TermKind::Apply { args, .. } => args.iter().any(|&x| term_mentions_var(tm, x, name)),
        _ => false,
    }
}

#[test]
fn define_fun_substitutes_parameter() {
    let mut tm = TermManager::new();
    let cmds = parse_script(
        r#"
(declare-const i Int)
(define-fun f ((k Int)) Int (+ k 1))
(assert (= (f i) 3))
"#,
        &mut tm,
    )
    .unwrap();
    let a = cmds
        .iter()
        .find_map(|c| {
            if let Command::Assert(t) = c {
                Some(*t)
            } else {
                None
            }
        })
        .unwrap();
    assert!(
        term_mentions_var(&tm, a, "i"),
        "expanded body must mention call-site argument i"
    );
    assert!(
        !term_mentions_var(&tm, a, "k"),
        "expanded body must not retain free parameter k"
    );
}

#[test]
fn define_fun_ite_substitutes_parameter() {
    let mut tm = TermManager::new();
    let cmds = parse_script(
        r#"
(declare-const i Int)
(define-fun f ((k Int)) Int (ite (= k 1) 3 0))
(assert (= (f i) 3))
"#,
        &mut tm,
    )
    .unwrap();
    let a = cmds
        .iter()
        .find_map(|c| {
            if let Command::Assert(t) = c {
                Some(*t)
            } else {
                None
            }
        })
        .unwrap();
    assert!(
        !term_mentions_var(&tm, a, "k"),
        "expanded ite body must not retain free parameter k"
    );
    assert!(
        term_mentions_var(&tm, a, "i"),
        "expanded ite body must mention call-site argument i"
    );
}
