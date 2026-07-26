//! Issue #22: `(not (distinct …))` must not force arithmetic disequality splits.

use oxiz_solver::{Context, SolverResult};

fn run(script: &str) -> SolverResult {
    let mut ctx = Context::new();
    let outputs = ctx.execute_script(script).expect("script");
    outputs
        .iter()
        .rev()
        .find_map(|l| match l.trim() {
            "sat" => Some(SolverResult::Sat),
            "unsat" => Some(SolverResult::Unsat),
            "unknown" => Some(SolverResult::Unknown),
            _ => None,
        })
        .unwrap_or(SolverResult::Unknown)
}

#[test]
fn not_distinct_two_ints_is_sat() {
    assert_eq!(
        run(r#"
            (set-logic QF_LIA)
            (declare-const x Int)
            (declare-const y Int)
            (assert (not (distinct x y)))
            (check-sat)
        "#),
        SolverResult::Sat
    );
}

#[test]
fn not_distinct_x_x_is_sat() {
    assert_eq!(
        run(r#"
            (set-logic QF_LIA)
            (declare-const x Int)
            (assert (not (distinct x x)))
            (check-sat)
        "#),
        SolverResult::Sat
    );
}

#[test]
fn positive_distinct_still_unsat_when_equal() {
    assert_eq!(
        run(r#"
            (set-logic QF_LIA)
            (declare-const x Int)
            (assert (distinct x x))
            (check-sat)
        "#),
        SolverResult::Unsat
    );
}

#[test]
fn arr01_read_over_write_not_distinct_is_sat() {
    assert_eq!(
        run(r#"
(set-logic QF_AUFLIA)
(declare-const a0 (Array Int Int))
(declare-const a1 (Array Int Int))
(declare-const i0 Int)
(declare-const i1 Int)
(declare-const i2 Int)
(assert (not (distinct (select (store a1 (div 7 7) (mod (- 3) (- 5))) (+ 2 i1)) (select (store a0 (ite (<= (mod (abs 7) 2) (- 3)) (- 9) i0) (div i1 8)) (div i2 10)))))
(check-sat)
        "#),
        SolverResult::Sat
    );
}
