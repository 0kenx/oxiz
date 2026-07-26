//! Issue #14: QF_S conflicting string equalities must be unsat; models must
//! carry concrete string values.

use oxiz_solver::{Context, SolverResult};

fn run(script: &str) -> (SolverResult, Vec<String>) {
    let mut ctx = Context::new();
    let outputs = ctx.execute_script(script).expect("script");
    let result = outputs
        .iter()
        .rev()
        .find_map(|l| match l.trim() {
            "sat" => Some(SolverResult::Sat),
            "unsat" => Some(SolverResult::Unsat),
            "unknown" => Some(SolverResult::Unknown),
            _ => None,
        })
        .unwrap_or(SolverResult::Unknown);
    (result, outputs)
}

#[test]
fn conflicting_string_eq_is_unsat() {
    let (r, out) = run(
        r#"
        (set-logic QF_S)
        (declare-const s String)
        (assert (= s "x"))
        (assert (= s "y"))
        (check-sat)
        "#,
    );
    assert_eq!(r, SolverResult::Unsat, "outputs={out:?}");
}

#[test]
fn concat_prefix_mismatch_is_unsat() {
    let (r, out) = run(
        r#"
        (set-logic QF_S)
        (declare-const s String)
        (assert (= (str.++ "a" s) "bcd"))
        (check-sat)
        "#,
    );
    assert_eq!(r, SolverResult::Unsat, "outputs={out:?}");
}

#[test]
fn string_eq_get_value_and_model() {
    let (r, out) = run(
        r#"
        (set-logic QF_S)
        (declare-const s String)
        (assert (= s "353"))
        (check-sat)
        (get-value (s))
        (get-model)
        "#,
    );
    assert_eq!(r, SolverResult::Sat, "outputs={out:?}");
    let joined = out.join("\n");
    assert!(
        joined.contains("\"353\""),
        "model/value must contain string 353, got: {joined}"
    );
    assert!(
        !joined.contains("((s s))"),
        "get-value must not echo the variable: {joined}"
    );
    assert!(
        !joined.contains("Bool"),
        "string const must not get Bool sort: {joined}"
    );
}

#[test]
fn concat_solve_get_value() {
    let (r, out) = run(
        r#"
        (set-logic QF_S)
        (declare-const s String)
        (assert (= (str.++ "* " s) "* 353"))
        (check-sat)
        (get-value (s))
        (get-model)
        "#,
    );
    assert_eq!(r, SolverResult::Sat, "outputs={out:?}");
    let joined = out.join("\n");
    assert!(
        joined.contains("\"353\""),
        "s must be 353, got: {joined}"
    );
}
