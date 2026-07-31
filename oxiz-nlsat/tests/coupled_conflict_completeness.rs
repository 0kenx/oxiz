//! Regression tests for the sound multivariate coupled-conflict explanation
//! (`NlsatSolver::certify_sign_conflict`, wired into the `GreedyEmpty` branch of
//! `pick_arith_value` and the multivariate arm of `explain_theory_conflict`).
//!
//! Before this wiring the solver returned `Unknown` whenever the emptiness of an
//! arithmetic variable's feasible region was *coupled* with an earlier-assigned
//! variable (it could not certify a variable-local Sturm lemma). The sign
//! abstraction now certifies GLOBAL infeasibility of the coupled atoms and
//! learns a valid lemma, recovering `Unsat`. The abstraction is a sound
//! over-approximation, so the accompanying SAT cases must stay `Sat`: a
//! satisfiable coupled system must never be turned into a wrong `Unsat`.

use num_bigint::BigInt;
use num_rational::BigRational;
use oxiz_math::polynomial::Polynomial;
use oxiz_nlsat::solver::{NlsatSolver, SolverResult};
use oxiz_nlsat::types::{AtomKind, Literal};

fn rat(n: i64) -> BigRational {
    BigRational::from_integer(BigInt::from(n))
}

fn x() -> Polynomial {
    Polynomial::from_var(0)
}

fn y() -> Polynomial {
    Polynomial::from_var(1)
}

fn cst(n: i64) -> Polynomial {
    Polynomial::constant(rat(n))
}

/// `x - c`.
fn x_minus(c: i64) -> Polynomial {
    Polynomial::sub(&x(), &cst(c))
}

/// `x*y - c`.
fn xy_minus(c: i64) -> Polynomial {
    Polynomial::sub(&Polynomial::mul(&x(), &y()), &cst(c))
}

/// `x > 1 ∧ x·y > 1 ∧ y < 0` is UNSAT: `x > 1 ⇒ x > 0` and `y < 0`, so
/// `x·y < 0 < 1`, contradicting `x·y > 1`. The conflict couples `x` and `y`
/// through the product atom, so the old solver reported `Unknown`.
#[test]
fn coupled_product_conflict_is_unsat() {
    let mut solver = NlsatSolver::new();
    let a1 = solver.new_ineq_atom(x_minus(1), AtomKind::Gt); // x > 1
    let a2 = solver.new_ineq_atom(xy_minus(1), AtomKind::Gt); // x*y > 1
    let a3 = solver.new_ineq_atom(y(), AtomKind::Lt); // y < 0
    solver.add_clause(vec![solver.atom_literal(a1, true)]);
    solver.add_clause(vec![solver.atom_literal(a2, true)]);
    solver.add_clause(vec![solver.atom_literal(a3, true)]);

    assert_eq!(
        solver.solve(),
        SolverResult::Unsat,
        "x>1 ∧ x*y>1 ∧ y<0 must be UNSAT (coupled sign conflict)"
    );
}

/// The same coupled conflict, but exercised at decision level > 0. Two free
/// boolean variables and the clause `(a ∨ b)` force the solver to make boolean
/// decisions (raising the decision level) before it ever assigns the arithmetic
/// variables and discovers the coupled emptiness. On the pre-fix code this is
/// exactly the `GreedyEmpty`-at-level>0 case that returned `Unknown`; the sign
/// certifier now learns a valid lemma and the search terminates with `Unsat`.
#[test]
fn coupled_product_conflict_unsat_under_decisions() {
    let mut solver = NlsatSolver::new();

    // Free boolean structure forcing a decision at level >= 1.
    let a = solver.new_bool_var();
    let b = solver.new_bool_var();
    solver.add_clause(vec![Literal::positive(a), Literal::positive(b)]);

    let a1 = solver.new_ineq_atom(x_minus(1), AtomKind::Gt); // x > 1
    let a2 = solver.new_ineq_atom(xy_minus(1), AtomKind::Gt); // x*y > 1
    let a3 = solver.new_ineq_atom(y(), AtomKind::Lt); // y < 0
    solver.add_clause(vec![solver.atom_literal(a1, true)]);
    solver.add_clause(vec![solver.atom_literal(a2, true)]);
    solver.add_clause(vec![solver.atom_literal(a3, true)]);

    assert_eq!(
        solver.solve(),
        SolverResult::Unsat,
        "coupled conflict must be UNSAT even when discovered at level > 0"
    );
}

/// A second coupled shape: `x < 0 ∧ y > 0 ∧ x·y > 0` is UNSAT
/// (`sign(x·y) = (−)(+) = −`, contradicting `x·y > 0`).
#[test]
fn coupled_product_conflict_negative_positive_is_unsat() {
    let mut solver = NlsatSolver::new();
    let a1 = solver.new_ineq_atom(x(), AtomKind::Lt); // x < 0
    let a2 = solver.new_ineq_atom(y(), AtomKind::Gt); // y > 0
    let a3 = solver.new_ineq_atom(Polynomial::mul(&x(), &y()), AtomKind::Gt); // x*y > 0
    solver.add_clause(vec![solver.atom_literal(a1, true)]);
    solver.add_clause(vec![solver.atom_literal(a2, true)]);
    solver.add_clause(vec![solver.atom_literal(a3, true)]);

    assert_eq!(
        solver.solve(),
        SolverResult::Unsat,
        "x<0 ∧ y>0 ∧ x*y>0 must be UNSAT"
    );
}

/// Soundness guard: `x > 0 ∧ y > 0 ∧ x·y > 1` is SAT (e.g. x = y = 2). The sign
/// abstraction must NOT fabricate a conflict here — a satisfiable coupled system
/// must stay `Sat`.
#[test]
fn satisfiable_coupled_product_stays_sat() {
    let mut solver = NlsatSolver::new();
    let a1 = solver.new_ineq_atom(x(), AtomKind::Gt); // x > 0
    let a2 = solver.new_ineq_atom(y(), AtomKind::Gt); // y > 0
    let a3 = solver.new_ineq_atom(xy_minus(1), AtomKind::Gt); // x*y > 1
    solver.add_clause(vec![solver.atom_literal(a1, true)]);
    solver.add_clause(vec![solver.atom_literal(a2, true)]);
    solver.add_clause(vec![solver.atom_literal(a3, true)]);

    let result = solver.solve();
    assert_ne!(
        result,
        SolverResult::Unsat,
        "x>0 ∧ y>0 ∧ x*y>1 is satisfiable and must never be reported UNSAT"
    );
}

/// Soundness guard: `x > 0 ∧ y < 0` (no coupling constraint that conflicts) is
/// SAT; the certifier must not fire.
#[test]
fn independent_signs_stay_sat() {
    let mut solver = NlsatSolver::new();
    let a1 = solver.new_ineq_atom(x(), AtomKind::Gt); // x > 0
    let a2 = solver.new_ineq_atom(y(), AtomKind::Lt); // y < 0
    solver.add_clause(vec![solver.atom_literal(a1, true)]);
    solver.add_clause(vec![solver.atom_literal(a2, true)]);

    assert_eq!(
        solver.solve(),
        SolverResult::Sat,
        "x>0 ∧ y<0 is satisfiable"
    );
}

/// Bare product equality must not collapse to Unsat via a greedy `x = 0` sample.
#[test]
fn bare_product_equality_is_sat() {
    let mut solver = NlsatSolver::new();
    let a = solver.new_ineq_atom(xy_minus(12), AtomKind::Eq);
    solver.add_clause(vec![solver.atom_literal(a, true)]);
    assert_eq!(
        solver.solve(),
        SolverResult::Sat,
        "x*y = 12 is satisfiable over the reals"
    );
}

/// Magnitude product conflict: x>1 ∧ y>1 ∧ x·y = 1.
#[test]
fn product_bound_conflict_is_unsat() {
    let mut solver = NlsatSolver::new();
    let a1 = solver.new_ineq_atom(x_minus(1), AtomKind::Gt);
    let a2 = solver.new_ineq_atom(Polynomial::sub(&y(), &cst(1)), AtomKind::Gt);
    let a3 = solver.new_ineq_atom(xy_minus(1), AtomKind::Eq);
    solver.add_clause(vec![solver.atom_literal(a1, true)]);
    solver.add_clause(vec![solver.atom_literal(a2, true)]);
    solver.add_clause(vec![solver.atom_literal(a3, true)]);
    assert_eq!(
        solver.solve(),
        SolverResult::Unsat,
        "x>1 ∧ y>1 ∧ x*y=1 is UNSAT"
    );
}

/// Linear sum bound conflict: x>5 ∧ y>5 ∧ x+y<5.
#[test]
fn linear_sum_bound_conflict_is_unsat() {
    let mut solver = NlsatSolver::new();
    let a1 = solver.new_ineq_atom(x_minus(5), AtomKind::Gt);
    let a2 = solver.new_ineq_atom(Polynomial::sub(&y(), &cst(5)), AtomKind::Gt);
    let sum = Polynomial::sub(&Polynomial::add(&x(), &y()), &cst(5));
    let a3 = solver.new_ineq_atom(sum, AtomKind::Lt);
    solver.add_clause(vec![solver.atom_literal(a1, true)]);
    solver.add_clause(vec![solver.atom_literal(a2, true)]);
    solver.add_clause(vec![solver.atom_literal(a3, true)]);
    assert_eq!(
        solver.solve(),
        SolverResult::Unsat,
        "x>5 ∧ y>5 ∧ x+y<5 is UNSAT"
    );
}

/// Forced singleton + circle: x=2 ∧ x²+y²=1 is UNSAT.
#[test]
fn forced_point_outside_circle_is_unsat() {
    let mut solver = NlsatSolver::new();
    let circle = Polynomial::sub(
        &Polynomial::add(&Polynomial::mul(&x(), &x()), &Polynomial::mul(&y(), &y())),
        &cst(1),
    );
    let a1 = solver.new_ineq_atom(circle, AtomKind::Eq);
    let a2 = solver.new_ineq_atom(x_minus(2), AtomKind::Eq);
    solver.add_clause(vec![solver.atom_literal(a1, true)]);
    solver.add_clause(vec![solver.atom_literal(a2, true)]);
    assert_eq!(
        solver.solve(),
        SolverResult::Unsat,
        "x=2 ∧ x²+y²=1 is UNSAT"
    );
}
