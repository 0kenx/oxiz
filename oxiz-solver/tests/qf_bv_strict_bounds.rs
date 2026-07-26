//! Issue #17: trivially-unsatisfiable strict BV comparisons must be unsat,
//! not sat with a malformed model (`#x-1`).

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
fn bvult_x_zero_is_unsat() {
    let (r, out) = run(
        r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 8))
        (assert (bvult x #b00000000))
        (check-sat)
        "#,
    );
    assert_eq!(r, SolverResult::Unsat, "outputs={out:?}");
}

#[test]
fn bvslt_x_smin_is_unsat() {
    // signed min for 8-bit is #b10000000 = -128; nothing is strictly less
    let (r, out) = run(
        r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 8))
        (assert (bvslt x #b10000000))
        (check-sat)
        "#,
    );
    assert_eq!(r, SolverResult::Unsat, "outputs={out:?}");
}

#[test]
fn bvsgt_smin_x_is_unsat() {
    // −128 > x is unsat for all x
    let (r, out) = run(
        r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 8))
        (assert (bvsgt #b10000000 x))
        (check-sat)
        "#,
    );
    assert_eq!(r, SolverResult::Unsat, "outputs={out:?}");
}

#[test]
fn bvule_x_zero_is_sat_at_zero() {
    let (r, out) = run(
        r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 8))
        (assert (bvule x #b00000000))
        (check-sat)
        (get-value (x))
        "#,
    );
    assert_eq!(r, SolverResult::Sat, "outputs={out:?}");
    let joined = out.join("\n");
    assert!(
        !joined.contains("#x-1") && !joined.contains("-1"),
        "model must not contain malformed negative BV literal: {joined}"
    );
}

#[test]
fn bvsle_x_smin_is_sat() {
    let (r, out) = run(
        r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 8))
        (assert (bvsle x #b10000000))
        (check-sat)
        "#,
    );
    assert_eq!(r, SolverResult::Sat, "outputs={out:?}");
}

#[test]
fn bvult_x_zero_widths() {
    for w in [4u32, 8, 16, 32] {
        let zeros = "0".repeat(w as usize);
        let script = format!(
            r#"
            (set-logic QF_BV)
            (declare-const x (_ BitVec {w}))
            (assert (bvult x #b{zeros}))
            (check-sat)
            "#
        );
        let (r, out) = run(&script);
        assert_eq!(r, SolverResult::Unsat, "width={w} outputs={out:?}");
    }
}
