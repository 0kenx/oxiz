//! Regression tests for audited defects in the SMT-LIB term parser
//! (`oxiz-core/src/smtlib/parser/terms.rs`).
//!
//! Each test reproduces a specific soundness bug that the parser used to
//! exhibit and asserts the corrected behavior:
//!
//! 1. `(div a b)` / `(mod a b)` were lowered to subtraction.
//! 2. Real `/`, `abs`, `to_real`, `to_int`, `is_int`, `divisible` fell through
//!    to Bool-sorted uninterpreted applies (or were unsupported).
//! 3. Undeclared symbols silently became fresh Bool variables.
//! 4. Indexed BV ops (`zero_extend`, `sign_extend`, `rotate_*`, `repeat`)
//!    degraded to Bool-sorted generic applies.

use oxiz_core::ast::{RoundingMode, TermKind, TermManager};
use oxiz_core::smtlib::{Command, parse_script};
use oxiz_core::sort::SortKind;

/// Parse a full script, returning the manager plus the asserted term ids in
/// order.
fn parse_asserts(script: &str) -> (TermManager, Vec<oxiz_core::ast::TermId>) {
    let mut manager = TermManager::new();
    let commands = parse_script(script, &mut manager).expect("script should parse");
    let asserts = commands
        .into_iter()
        .filter_map(|c| match c {
            Command::Assert(t) => Some(t),
            _ => None,
        })
        .collect();
    (manager, asserts)
}

fn kind(manager: &TermManager, t: oxiz_core::ast::TermId) -> TermKind {
    manager.get(t).expect("term should exist").kind.clone()
}

/// Return the two operand term ids of an equality (`mk_eq` canonicalizes
/// operand order, so callers must not assume which side is which).
fn eq_operands(
    m: &TermManager,
    t: oxiz_core::ast::TermId,
) -> (oxiz_core::ast::TermId, oxiz_core::ast::TermId) {
    match kind(m, t) {
        TermKind::Eq(a, b) => (a, b),
        other => panic!("expected equality, got {other:?}"),
    }
}

/// Find, among the two operands of an equality, the one satisfying `pred`.
fn eq_side_matching(
    m: &TermManager,
    t: oxiz_core::ast::TermId,
    pred: impl Fn(&TermKind) -> bool,
) -> oxiz_core::ast::TermId {
    let (a, b) = eq_operands(m, t);
    if pred(&kind(m, a)) {
        a
    } else if pred(&kind(m, b)) {
        b
    } else {
        panic!(
            "neither operand matched: {:?} / {:?}",
            kind(m, a),
            kind(m, b)
        )
    }
}

// ---------------------------------------------------------------------------
// Finding 1: div / mod must not become subtraction.
// ---------------------------------------------------------------------------

#[test]
fn div_is_not_subtraction() {
    let (m, asserts) = parse_asserts(
        r#"
        (declare-const a Int)
        (declare-const b Int)
        (assert (= (div a b) 0))
        "#,
    );
    // One side of the equality must be a Div node, never Sub.
    let (a, b) = eq_operands(&m, asserts[0]);
    let ka = kind(&m, a);
    let kb = kind(&m, b);
    assert!(
        matches!(ka, TermKind::Div(_, _)) || matches!(kb, TermKind::Div(_, _)),
        "expected Div, got {ka:?} / {kb:?} (regression: div lowered to subtraction)"
    );
    assert!(
        !matches!(ka, TermKind::Sub(_, _)) && !matches!(kb, TermKind::Sub(_, _)),
        "div must not be Sub"
    );
}

#[test]
fn mod_is_not_subtraction() {
    let (m, asserts) = parse_asserts(
        r#"
        (declare-const a Int)
        (declare-const b Int)
        (assert (= (mod a b) 0))
        "#,
    );
    let _ = eq_side_matching(&m, asserts[0], |k| matches!(k, TermKind::Mod(_, _)));
}

// ---------------------------------------------------------------------------
// Finding 2: real division and Int/Real conversions.
// ---------------------------------------------------------------------------

#[test]
fn real_division_stays_in_arithmetic() {
    let (m, asserts) = parse_asserts(
        r#"
        (declare-const x Real)
        (assert (= (/ x 3.0) 1.0))
        "#,
    );
    let _ = eq_side_matching(&m, asserts[0], |k| matches!(k, TermKind::Div(_, _)));
}

#[test]
fn abs_lowers_to_ite() {
    let (m, asserts) = parse_asserts(
        r#"
        (declare-const x Int)
        (assert (= (abs x) 5))
        "#,
    );
    let _ = eq_side_matching(&m, asserts[0], |k| matches!(k, TermKind::Ite(_, _, _)));
}

#[test]
fn to_real_is_value_preserving_and_not_bool_apply() {
    let (m, asserts) = parse_asserts(
        r#"
        (declare-const n Int)
        (assert (< (to_real n) 2.5))
        "#,
    );
    let TermKind::Lt(lhs, _) = kind(&m, asserts[0]) else {
        panic!("expected <");
    };
    // to_real(n) must be the integer variable itself (the injection), never a
    // Bool-sorted uninterpreted apply.
    match kind(&m, lhs) {
        TermKind::Var(_) => {}
        other => panic!("expected Var for to_real arg, got {other:?}"),
    }
    // Its sort must NOT be Bool.
    let sort = m.get(lhs).unwrap().sort;
    assert!(
        !matches!(m.sorts.get(sort).unwrap().kind, SortKind::Bool),
        "to_real result must not be Bool-sorted"
    );
}

#[test]
fn to_int_is_honest_error_not_silent_wrong() {
    // to_int needs a genuine floor operator we do not have; the parser must
    // reject it rather than silently produce a wrong (Bool-sorted apply) term.
    let mut manager = TermManager::new();
    let script = r#"
        (declare-const x Real)
        (assert (= (to_int x) 3))
    "#;
    assert!(
        parse_script(script, &mut manager).is_err(),
        "to_int must be an honest parse error, not a silent wrong term"
    );
}

#[test]
fn is_int_is_honest_error() {
    let mut manager = TermManager::new();
    let script = r#"
        (declare-const x Real)
        (assert (is_int x))
    "#;
    assert!(parse_script(script, &mut manager).is_err());
}

#[test]
fn divisible_lowers_to_mod_equals_zero() {
    let (m, asserts) = parse_asserts(
        r#"
        (declare-const x Int)
        (assert ((_ divisible 3) x))
        "#,
    );
    // ((_ divisible 3) x) lowers to (= (mod x 3) 0).
    let _ = eq_side_matching(&m, asserts[0], |k| matches!(k, TermKind::Mod(_, _)));
}

// ---------------------------------------------------------------------------
// Finding 3: undeclared symbols must be rejected in a real script.
// ---------------------------------------------------------------------------

#[test]
fn undeclared_symbol_in_script_is_error() {
    let mut manager = TermManager::new();
    // `typo_var` is never declared; declaring `x` establishes script context.
    let script = r#"
        (declare-const x Int)
        (assert (< x typo_var))
    "#;
    let err = parse_script(script, &mut manager);
    assert!(
        err.is_err(),
        "undeclared symbol must be rejected, not turned into a fresh Bool var"
    );
}

#[test]
fn declared_symbols_still_parse() {
    // Sanity: a fully declared script must still parse fine.
    let mut manager = TermManager::new();
    let script = r#"
        (declare-const x Int)
        (declare-const y Int)
        (assert (< x y))
    "#;
    assert!(parse_script(script, &mut manager).is_ok());
}

#[test]
fn quantifier_bound_vars_not_rejected() {
    // Bound variables are not "declared" via declare-const but must still
    // resolve, even under the strict undeclared-symbol rule.
    let mut manager = TermManager::new();
    let script = r#"
        (declare-const c Int)
        (assert (forall ((i Int)) (> (+ i c) 0)))
    "#;
    assert!(
        parse_script(script, &mut manager).is_ok(),
        "quantifier-bound variable wrongly treated as undeclared"
    );
}

// ---------------------------------------------------------------------------
// Finding 4: indexed BV ops must be real bit-vector terms.
// ---------------------------------------------------------------------------

fn bv_width(m: &TermManager, t: oxiz_core::ast::TermId) -> Option<u32> {
    let sort = m.get(t)?.sort;
    m.sorts.get(sort)?.bitvec_width()
}

/// Return the operand of an equality that is a `BvConcat` (the lowered
/// extend/rotate/repeat term), regardless of canonicalized operand order.
fn concat_side(m: &TermManager, t: oxiz_core::ast::TermId) -> oxiz_core::ast::TermId {
    eq_side_matching(m, t, |k| matches!(k, TermKind::BvConcat(_, _)))
}

#[test]
fn zero_extend_produces_bitvector_of_correct_width() {
    let (m, asserts) = parse_asserts(
        r#"
        (declare-const x (_ BitVec 8))
        (assert (= ((_ zero_extend 8) x) #x0000))
        "#,
    );
    // 8-bit value zero-extended by 8 => 16-bit bit-vector via concat.
    let side = concat_side(&m, asserts[0]);
    assert_eq!(bv_width(&m, side), Some(16), "zero_extend width wrong");
}

#[test]
fn sign_extend_produces_bitvector_of_correct_width() {
    let (m, asserts) = parse_asserts(
        r#"
        (declare-const x (_ BitVec 8))
        (assert (= ((_ sign_extend 4) x) #x000))
        "#,
    );
    let side = concat_side(&m, asserts[0]);
    assert_eq!(bv_width(&m, side), Some(12), "sign_extend width wrong");
}

#[test]
fn rotate_left_preserves_width() {
    let (m, asserts) = parse_asserts(
        r#"
        (declare-const x (_ BitVec 8))
        (assert (= ((_ rotate_left 3) x) #x00))
        "#,
    );
    // A non-trivial rotation is a concat of two extracts, not a Bool apply.
    let side = concat_side(&m, asserts[0]);
    assert_eq!(
        bv_width(&m, side),
        Some(8),
        "rotate_left must preserve width"
    );
}

#[test]
fn repeat_produces_correct_width() {
    let (m, asserts) = parse_asserts(
        r#"
        (declare-const x (_ BitVec 8))
        (assert (= ((_ repeat 3) x) #x000000))
        "#,
    );
    let side = concat_side(&m, asserts[0]);
    assert_eq!(bv_width(&m, side), Some(24), "repeat width wrong");
}

// ---------------------------------------------------------------------------
// Recursion depth guard: pathological nesting yields an error, not a crash.
// ---------------------------------------------------------------------------

#[test]
fn deeply_nested_term_errors_instead_of_overflowing() {
    // Build (- (- (- ... 0 ...))) far deeper than MAX_PARSE_DEPTH.
    let depth = 200_000;
    let mut s = String::with_capacity(depth * 4);
    for _ in 0..depth {
        s.push_str("(- ");
    }
    s.push('0');
    for _ in 0..depth {
        s.push(')');
    }
    let script = format!("(declare-const z Int)(assert (= {s} 0))");
    let mut manager = TermManager::new();
    // Must return an error rather than overflow the stack.
    assert!(
        parse_script(&script, &mut manager).is_err(),
        "deep nesting should be rejected by the depth guard"
    );
}

// ---------------------------------------------------------------------------
// FP indexed conversion operators take a RoundingMode as their first argument.
// Previously the bare `RNE`/`RNA`/... symbol fell through to the generic
// indexed-operator path and was rejected as an undeclared constant, regressing
// every QF_FP benchmark that uses `((_ to_fp e s) RNE ...)`. These tests pin
// the four SMT-LIB FP conversion operators and confirm source-sort dispatch.
// ---------------------------------------------------------------------------

/// Walk the asserted terms of a script and return the first sub-term whose
/// `TermKind` matches `pred`, panicking with a helpful message if none is
/// found. Recurses into children so that e.g. a conversion nested inside an
/// `(= ...)` assertion is still located.
fn first_assert_kind<F: Fn(&TermKind) -> bool>(
    m: &TermManager,
    asserts: &[oxiz_core::ast::TermId],
    pred: F,
    what: &str,
) -> oxiz_core::ast::TermId {
    for &t in asserts {
        if let Some(id) = find_first_id(m, t, &pred) {
            return id;
        }
    }
    panic!(
        "no assert matched {what}; top-level kinds were: {:?}",
        asserts.iter().map(|t| kind(m, *t)).collect::<Vec<_>>()
    )
}

/// Recursive search returning the TermId of the first sub-term whose kind
/// satisfies `pred`.
fn find_first_id<F: Fn(&TermKind) -> bool>(
    m: &TermManager,
    t: oxiz_core::ast::TermId,
    pred: &F,
) -> Option<oxiz_core::ast::TermId> {
    let k = kind(m, t);
    if pred(&k) {
        return Some(t);
    }
    let children = oxiz_core::ast::traversal::get_children(&k);
    for c in children {
        if let Some(id) = find_first_id(m, c, pred) {
            return Some(id);
        }
    }
    None
}

#[test]
fn to_fp_from_real_uses_real_to_fp_and_keeps_rounding_mode() {
    // ((_ to_fp 8 24) RNE 1.5) over a Real source must lower to RealToFp
    // with rounding mode RNE — not a Bool-sorted apply, and not a parse error.
    let (m, asserts) = parse_asserts(
        r#"
        (declare-const r Real)
        (assert (= ((_ to_fp 8 24) RNA r) ((_ to_fp 8 24) RNA 1.5)))
        "#,
    );
    let conv = first_assert_kind(
        &m,
        &asserts,
        |k| matches!(k, TermKind::RealToFp { .. }),
        "RealToFp",
    );
    match kind(&m, conv) {
        TermKind::RealToFp { rm, eb, sb, .. } => {
            assert_eq!(rm, RoundingMode::RNA, "rounding mode dropped/wrong");
            assert_eq!((eb, sb), (8, 24), "wrong FP format");
        }
        other => panic!("expected RealToFp, got {other:?}"),
    }
}

#[test]
fn to_fp_from_float_uses_fp_to_fp() {
    // ((_ to_fp 11 53) RTN x) where x is Float64 must lower to FpToFp.
    let (m, asserts) = parse_asserts(
        r#"
        (declare-const x (_ FloatingPoint 11 53))
        (assert (= ((_ to_fp 8 24) RTN x) x))
        "#,
    );
    let conv = first_assert_kind(
        &m,
        &asserts,
        |k| matches!(k, TermKind::FpToFp { .. }),
        "FpToFp",
    );
    match kind(&m, conv) {
        TermKind::FpToFp { rm, eb, sb, .. } => {
            assert_eq!(rm, RoundingMode::RTN);
            assert_eq!((eb, sb), (8, 24));
        }
        other => panic!("expected FpToFp, got {other:?}"),
    }
}

#[test]
fn to_fp_from_bv_is_signed_and_to_fp_unsigned_is_unsigned() {
    // `(_ to_fp e s)` over a BitVec is the SIGNED conversion, while
    // `(_ to_fp_unsigned e s)` is the UNSIGNED one.
    let (m, asserts) = parse_asserts(
        r#"
        (declare-const b (_ BitVec 32))
        (assert (= ((_ to_fp 8 24) RNE b) ((_ to_fp_unsigned 8 24) RNE b)))
        "#,
    );
    first_assert_kind(
        &m,
        &asserts,
        |k| matches!(k, TermKind::SBVToFp { .. }),
        "SBVToFp (signed to_fp)",
    );
    first_assert_kind(
        &m,
        &asserts,
        |k| matches!(k, TermKind::UBVToFp { .. }),
        "UBVToFp (to_fp_unsigned)",
    );
}

#[test]
fn fp_to_sbv_and_fp_to_ubv_parse_with_rounding_mode() {
    let (m, asserts) = parse_asserts(
        r#"
        (declare-const x (_ FloatingPoint 8 24))
        (assert (= ((_ fp.to_sbv 32) RTP x) ((_ fp.to_ubv 32) RTP x)))
        "#,
    );
    let sbv = first_assert_kind(
        &m,
        &asserts,
        |k| matches!(k, TermKind::FpToSBV { .. }),
        "FpToSBV",
    );
    let ubv = first_assert_kind(
        &m,
        &asserts,
        |k| matches!(k, TermKind::FpToUBV { .. }),
        "FpToUBV",
    );
    match kind(&m, sbv) {
        TermKind::FpToSBV { rm, width, .. } => {
            assert_eq!(rm, RoundingMode::RTP);
            assert_eq!(width, 32);
        }
        other => panic!("expected FpToSBV, got {other:?}"),
    }
    match kind(&m, ubv) {
        TermKind::FpToUBV { rm, width, .. } => {
            assert_eq!(rm, RoundingMode::RTP);
            assert_eq!(width, 32);
        }
        other => panic!("expected FpToUBV, got {other:?}"),
    }
}

#[test]
fn to_fp_rejects_wrong_arity() {
    // `(_ to_fp e)` (one index) is malformed and must be a parse error,
    // not a silent wrong-sort term.
    let mut manager = TermManager::new();
    let script = "(declare-const r Real)(assert (= ((_ to_fp 8) RNE r) ((_ to_fp 8) RNE r)))";
    assert!(
        parse_script(script, &mut manager).is_err(),
        "(_ to_fp e) with one index must be rejected"
    );
}

// ---------------------------------------------------------------------------
// SMT-LIB Strings regex constants (`re.allchar` etc.) are zero-argument
// operators that previously hit the strict-undeclared-symbol check, regressing
// every QF_S benchmark that uses `(re.* re.allchar)`.
// ---------------------------------------------------------------------------

#[test]
fn regex_constants_parse_as_zero_arg_applies() {
    // All four documented SMT-LIB regex constants must parse without being
    // rejected as undeclared symbols. They are minted as zero-argument apply
    // terms (oxiz has no dedicated RegEx sort), consistent with how compound
    // regex operators are lowered today.
    for sym in ["re.allchar", "re.all", "re.none", "re.empty"] {
        let (m, asserts) = parse_asserts(&format!(
            "(declare-const s String)(assert (str.in_re s (re.* {sym})))"
        ));
        // The apply for the constant is nested inside re.* inside str.in_re;
        // walk the asserted term to find an Apply whose resolved name matches.
        let mut found = false;
        for &t in &asserts {
            walk(&m, t, &mut |k| {
                if let TermKind::Apply { func, args } = k
                    && m.resolve_str(*func) == sym
                    && args.is_empty()
                {
                    found = true;
                }
            });
            if found {
                break;
            }
        }
        assert!(found, "bare `{sym}` did not parse as a zero-arg apply");
    }
}

/// Pre-order walk of a term's `TermKind` sub-tree, invoking `f` on every
/// node's kind. Used by the regex-constant test to find the apply node deep
/// inside `(str.in_re s (re.* <const>))`.
fn walk<F: FnMut(&TermKind)>(m: &TermManager, t: oxiz_core::ast::TermId, f: &mut F) {
    let kind = m.get(t).expect("term exists").kind.clone();
    f(&kind);
    for child in oxiz_core::ast::traversal::get_children(&kind) {
        walk(m, child, f);
    }
}
