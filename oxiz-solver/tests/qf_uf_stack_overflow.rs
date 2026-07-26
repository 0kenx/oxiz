//! Issue #18: QF_UF must not stack-overflow on satisfiable nested EUF formulas.

use oxiz_solver::{Context, SolverResult};

#[test]
fn uf01_nested_apps_no_stack_overflow() {
    let source = r#"
(set-logic QF_UF)
(declare-sort U 0)
(declare-const c0 U)
(declare-const c1 U)
(declare-const c2 U)
(declare-const c3 U)
(declare-fun f (U) U)
(declare-fun g (U U) U)
(assert (and (and (not (distinct (f (g c0 c3)) (g (f c3) (f c3)))) (distinct (g c3 (f c2)) (g c3 (f c3))) (=> (distinct (g c3 (g c0 c2)) (f c1)) (= c0 (g (f c2) c3)))) (xor (and (distinct (f (f c3)) (f (f c3))) (distinct (g (f c0) (f c2)) (f c0)) (distinct c3 (g c2 (g c3 c1)))) (xor (distinct (g (f c2) (g c3 c2)) (g (f c2) c0)) (distinct (f c0) c2))) (distinct (g (f c1) (f c3)) c2)))
(assert (distinct (g (g c0 c1) (f c2)) (g (g c1 c0) (g c2 c0))))
(assert (= c1 (g (f c0) c2)))
(assert (xor (and (ite (distinct c1 c0) (distinct (f (f c2)) (f (g c3 c2))) (distinct (g (f c2) (f c3)) (f (g c3 c3)))) (not (= (f (f c0)) c3)) (= c1 c0)) (distinct c2 (f (g c0 c1)))))
(assert (not (=> (= c2 (f (f c0))) (=> (= (g (g c3 c2) (g c1 c3)) (f (g c3 c1))) (= c2 c3)))))
(assert (and (xor (or (= c2 (g (g c2 c0) c3)) (= (g (g c2 c1) (f c3)) c1) (distinct c2 (g (f c0) (f c2)))) (not (= (f (f c1)) c1))) (not (distinct (g c2 c0) (g (f c2) c1))) (or (not (distinct (f c2) (g c3 (f c1)))) (and (= (g c1 (f c3)) (g (g c1 c0) c1)) (distinct (g c0 (f c1)) (f (f c2)))) (=> (distinct (f c3) (f (f c2))) (= (f (f c1)) c1)))))
(check-sat)
"#;
    let mut ctx = Context::new();
    let outputs = ctx
        .execute_script(source)
        .expect("script must not abort");
    let result = outputs.iter().rev().find_map(|l| match l.trim() {
        "sat" => Some(SolverResult::Sat),
        "unsat" => Some(SolverResult::Unsat),
        "unknown" => Some(SolverResult::Unknown),
        _ => None,
    });
    assert_eq!(
        result,
        Some(SolverResult::Sat),
        "expected sat (z3), got {outputs:?}"
    );
}
