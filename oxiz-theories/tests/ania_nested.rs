use oxiz_core::ast::TermManager;
use oxiz_core::smtlib::{Command, parse_script};
use oxiz_theories::ania_ground::try_decide_ground_ania;
use oxiz_theories::nlsat::NlDispatchResult;

#[test]
fn nested_ite_select_product_range() {
    let mut tm = TermManager::new();
    let script = r#"
(set-logic QF_ANIA)
(declare-const i Int)
(declare-const t Int)
(declare-const A (Array Int Int))
(declare-const B (Array Int Int))
(declare-const C (Array Int Int))
(declare-const D (Array Int Int))
(assert (= A (store (store ((as const (Array Int Int)) 0) 1 30) 2 32)))
(assert (= B (store (store ((as const (Array Int Int)) 0) 1 76) 2 74)))
(assert (= C (store (store ((as const (Array Int Int)) 0) 1 5) 2 5)))
(assert (= D (store (store ((as const (Array Int Int)) 0) 1 3) 2 3)))
(define-fun absi ((x Int)) Int (ite (< x 0) (- x) x))
(define-fun w ((k Int) (s Int)) Int
  (let ((d (absi (- s (select C k)))))
    (ite (<= d (select D k)) 10 (ite (<= d (* 2 (select D k))) 6 0))))
(assert (and (>= i 1)(<= i 2)(>= t 1)(<= t 9)
  (>= (* (select A i) (select B i) (w i t) 10) 200000)
  (<= (* (select A i) (select B i) (w i t) 10) 300000)))
"#;
    let cmds = parse_script(script, &mut tm).expect("parse");
    let asserts: Vec<_> = cmds
        .into_iter()
        .filter_map(|c| match c {
            Command::Assert(t) => Some(t),
            _ => None,
        })
        .collect();
    let r = try_decide_ground_ania(&asserts, &tm);
    assert!(matches!(r, Some(NlDispatchResult::Sat(_))));
}
