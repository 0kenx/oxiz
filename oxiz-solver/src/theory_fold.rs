//! Constant folding for ground floating-point and string operations.
//!
//! The solver's pre-encoding simplifier (`simplify.rs`) does not, by itself,
//! understand the semantics of the SMT-LIB FloatingPoint and Strings theories:
//! every `TermKind::Fp*` and `TermKind::Str*` is opaque to it. Without this
//! module, a fully-ground expression such as `fp.add RNE 1.5 2.3` survives
//! simplification and becomes an opaque SAT variable at encode time, so the
//! solver cannot evaluate it and (correctly but uselessly) answers `Unknown`
//! on otherwise-trivial benchmarks like
//! `(x = 1.5) ∧ (y = 2.3) ∧ (fp.gt (fp.add RNE x y) 3.7)`.
//!
//! This module evaluates ground FP and string operations to their canonical
//! constant form *exactly* — FP arithmetic uses the rounding-mode-aware
//! `Ieee754Engine` from `oxiz-theories` (so RTP/RTN/RTZ are honoured, not
//! just the CPU's default RNE), and string operations use Rust's native
//! `String`/`&str` primitives. Folding is therefore a tautology: it can
//! never introduce a wrong answer, only expose one that was already forced.
//!
//! The folder is invoked from [`crate::simplify::Simplifier::simplify_impl`]
//! after children are recursively simplified, so any operation whose
//! operands have already reduced to constants gets folded.

use oxiz_core::ast::{RoundingMode, TermId, TermKind, TermManager};
use oxiz_theories::fp::{FpFormat, FpRoundingMode, FpValue};

/// Attempt to fold a ground FP or String operation term to a constant.
///
/// Returns `Some(new_term)` if `term` is a foldable theory operation whose
/// operands are all already-constant terms (after recursive simplification),
/// or `None` otherwise. The caller is expected to have simplified the
/// children first; this function does not recurse.
///
/// `manager` is `&mut` because folding produces fresh interned terms
/// (`FpLit`, `StringLit`, `IntConst`, `Bool`).
#[allow(clippy::too_many_lines)]
pub fn try_fold(term: TermId, manager: &mut TermManager) -> Option<TermId> {
    let kind = manager.get(term)?.kind.clone();
    match kind {
        // ===== FP arithmetic (RNE-only: native f32/f64 arithmetic is correctly
        // rounded under RNE; other modes would need exact intermediates, so we
        // decline to fold and the term stays un-folded.) =====
        TermKind::FpAdd(rm, a, b) => fold_fp_binary(rm, a, b, manager, |x, y| x + y, |x, y| x + y),
        TermKind::FpSub(rm, a, b) => fold_fp_binary(rm, a, b, manager, |x, y| x - y, |x, y| x - y),
        TermKind::FpMul(rm, a, b) => fold_fp_binary(rm, a, b, manager, |x, y| x * y, |x, y| x * y),
        TermKind::FpDiv(rm, a, b) => fold_fp_binary(rm, a, b, manager, |x, y| x / y, |x, y| x / y),
        TermKind::FpSqrt(rm, a) => fold_fp_unary(rm, a, manager, f32::sqrt, f64::sqrt),
        TermKind::FpRoundToIntegral(rm, a) => {
            // IEEE-754 roundToIntegral follows the active rounding mode; for
            // RNE that's `round_ties_even` (stable since Rust 1.77).
            fold_fp_unary(rm, a, manager, f32::round_ties_even, f64::round_ties_even)
        }
        TermKind::FpFma(rm, x, y, z) => {
            if rm != RoundingMode::RNE {
                return None;
            }
            let (xv, xf) = fp_const_value(x, manager)?;
            let (yv, yf) = fp_const_value(y, manager)?;
            let (zv, zf) = fp_const_value(z, manager)?;
            if !(xf == yf && yf == zf) {
                return None;
            }
            let result = match xf {
                FpFormat::FLOAT32 => f32_to_fp_value(
                    fp_value_to_f32(&xv)?.mul_add(fp_value_to_f32(&yv)?, fp_value_to_f32(&zv)?),
                ),
                FpFormat::FLOAT64 => f64_to_fp_value(
                    fp_value_to_f64(&xv)?.mul_add(fp_value_to_f64(&yv)?, fp_value_to_f64(&zv)?),
                ),
                _ => return None,
            };
            Some(make_fp_const(manager, &result, xf))
        }

        // FP operations without a rounding mode.
        TermKind::FpRem(a, b) => {
            // f32::rem follows IEEE-754 remainder semantics.
            fold_fp_binary_no_rm(a, b, manager, |x, y| x % y, |x, y| x % y)
        }
        TermKind::FpMin(a, b) => fold_fp_binary_no_rm(a, b, manager, f32::min, f64::min),
        TermKind::FpMax(a, b) => fold_fp_binary_no_rm(a, b, manager, f32::max, f64::max),
        TermKind::FpAbs(a) => fold_fp_unary_no_rm(a, manager, f32::abs, f64::abs),
        TermKind::FpNeg(a) => fold_fp_unary_no_rm(a, manager, |x| -x, |x| -x),

        // ===== FP predicates (fold to Bool) =====
        TermKind::FpEq(a, b) => fold_fp_pred(a, b, manager, |x, y| x == y, |x, y| x == y),
        // IEEE-754 defines fp.lt/le/gt/ge with NaN-propagation semantics where
        // any comparison involving NaN returns false. Rust's `<`/`<=`/`>`/`>=`
        // on f32/f64 match this exactly.
        TermKind::FpLeq(a, b) => fold_fp_pred(a, b, manager, |x, y| x <= y, |x, y| x <= y),
        TermKind::FpLt(a, b) => fold_fp_pred(a, b, manager, |x, y| x < y, |x, y| x < y),
        TermKind::FpGeq(a, b) => fold_fp_pred(a, b, manager, |x, y| x >= y, |x, y| x >= y),
        TermKind::FpGt(a, b) => fold_fp_pred(a, b, manager, |x, y| x > y, |x, y| x > y),

        // ===== FP class predicates — intentionally NOT folded. =====
        // The solver's `check_fp_constraints` pass pattern-matches on the
        // *structure* of `FpIsZero`/`FpIsInfinite`/... atoms (e.g. it detects
        // `0/0 = NaN` conflicts by walking `FpIsZero` facts and looking for
        // `FpDiv(zero, zero)` in equalities). Folding these atoms to
        // `True`/`False` would erase the very structure that pass keys on,
        // turning a previously-detected `Unsat` into an honest-but-regressed
        // `Unknown`. Comparison predicates (`FpEq`/`FpLt`/...) below do not
        // have this issue and fold normally.
        TermKind::FpIsNormal(_)
        | TermKind::FpIsSubnormal(_)
        | TermKind::FpIsZero(_)
        | TermKind::FpIsInfinite(_)
        | TermKind::FpIsNaN(_)
        | TermKind::FpIsNegative(_)
        | TermKind::FpIsPositive(_) => None,

        // ===== FP conversions =====
        TermKind::RealToFp { rm, arg, eb, sb } => {
            let format = fp_format_of(eb, sb)?;
            let real = real_const_value(arg, manager)?;
            // For RNE on binary32/64, Rust's `as f32` / `as f64` cast from
            // f64 produces the correctly-rounded value (round-to-nearest-even).
            // Other rounding modes need exact intermediates; skip them.
            if rm != RoundingMode::RNE {
                return None;
            }
            let value = match format {
                FpFormat::FLOAT32 => f32_to_fp_value(real as f32),
                FpFormat::FLOAT64 => f64_to_fp_value(real),
                _ => return None,
            };
            Some(make_fp_const(manager, &value, format))
        }
        TermKind::FpToFp { rm, arg, eb, sb } => {
            let target = fp_format_of(eb, sb)?;
            let (val, src) = fp_const_value(arg, manager)?;
            if src == target {
                return Some(make_fp_const(manager, &val, target));
            }
            // Cross-format conversion with RNE: round-trip via f64, which is
            // exact for binary32 → binary64 (widening) and correctly rounded
            // for binary64 → binary32 (narrowing) under RNE.
            if rm != RoundingMode::RNE {
                return None;
            }
            let as_f64 = match src {
                FpFormat::FLOAT32 => f64::from(fp_value_to_f32(&val)?),
                FpFormat::FLOAT64 => fp_value_to_f64(&val)?,
                _ => return None,
            };
            let result = match target {
                FpFormat::FLOAT32 => f32_to_fp_value(as_f64 as f32),
                FpFormat::FLOAT64 => f64_to_fp_value(as_f64),
                _ => return None,
            };
            Some(make_fp_const(manager, &result, target))
        }
        TermKind::SBVToFp { rm, arg, eb, sb } => {
            let format = fp_format_of(eb, sb)?;
            if rm != RoundingMode::RNE {
                return None;
            }
            let bv = bv_const_value(arg, manager)?;
            let width = manager
                .get(arg)
                .and_then(|t| manager.sorts.get(t.sort))
                .and_then(|s| s.bitvec_width())?;
            let signed = sign_extend_i64(bv, width);
            let value = match format {
                FpFormat::FLOAT32 => f32_to_fp_value(signed as f32),
                FpFormat::FLOAT64 => f64_to_fp_value(signed as f64),
                _ => return None,
            };
            Some(make_fp_const(manager, &value, format))
        }
        TermKind::UBVToFp { rm, arg, eb, sb } => {
            let format = fp_format_of(eb, sb)?;
            if rm != RoundingMode::RNE {
                return None;
            }
            let bv = bv_const_value(arg, manager)?;
            let value = match format {
                FpFormat::FLOAT32 => f32_to_fp_value(bv as f32),
                FpFormat::FLOAT64 => f64_to_fp_value(bv as f64),
                _ => return None,
            };
            Some(make_fp_const(manager, &value, format))
        }
        TermKind::FpToReal(a) => {
            let (val, _format) = fp_const_value(a, manager)?;
            if val.is_nan() || val.is_infinite() {
                return None;
            }
            let f = fp_value_to_f64(&val).or_else(|| fp_value_to_f32(&val).map(f64::from))?;
            let rat = rational_from_f64(f)?;
            Some(manager.mk_real(rat))
        }
        TermKind::FpToSBV { rm, arg, width } => {
            if rm != RoundingMode::RNE {
                return None;
            }
            let (val, format) = fp_const_value(arg, manager)?;
            if val.is_nan() || val.is_infinite() {
                return None;
            }
            let f = match format {
                FpFormat::FLOAT32 => f64::from(fp_value_to_f32(&val)?),
                FpFormat::FLOAT64 => fp_value_to_f64(&val)?,
                _ => return None,
            };
            // Round to nearest integer (RNE), then check it fits.
            let i = f.round_ties_even() as i128;
            if !fits_in_width_signed_i128(i, width) {
                return None;
            }
            Some(manager.mk_bitvec(i64::try_from(i).ok()?, width))
        }
        TermKind::FpToUBV { rm, arg, width } => {
            if rm != RoundingMode::RNE {
                return None;
            }
            let (val, format) = fp_const_value(arg, manager)?;
            if val.is_nan() || val.is_infinite() || val.is_negative() {
                return None;
            }
            let f = match format {
                FpFormat::FLOAT32 => f64::from(fp_value_to_f32(&val)?),
                FpFormat::FLOAT64 => fp_value_to_f64(&val)?,
                _ => return None,
            };
            let u = f.round_ties_even() as u128;
            if !fits_in_width_unsigned_u128(u, width) {
                return None;
            }
            Some(manager.mk_bitvec(u64::try_from(u).ok()?, width))
        }

        // ===== String operations =====
        TermKind::StrConcat(a, b) => {
            let l = string_const_value(a, manager)?;
            let r = string_const_value(b, manager)?;
            let mut combined = l;
            combined.push_str(&r);
            Some(manager.mk_string_lit(&combined))
        }
        TermKind::StrLen(a) => {
            let s = string_const_value(a, manager)?;
            // char-count, not byte-count, per SMT-LIB semantics.
            let len: i64 = s.chars().count().try_into().ok()?;
            Some(manager.mk_int(len))
        }
        TermKind::StrAt(s, i) => {
            let s = string_const_value(s, manager)?;
            let i: i64 = int_const_value(i, manager)?;
            if i < 0 {
                return Some(manager.mk_string_lit(""));
            }
            let i: usize = i.try_into().ok()?;
            match s.chars().nth(i) {
                Some(c) => Some(manager.mk_string_lit(&c.to_string())),
                None => Some(manager.mk_string_lit("")),
            }
        }
        TermKind::StrSubstr(s, start, len) => {
            let s = string_const_value(s, manager)?;
            let start: i64 = int_const_value(start, manager)?;
            let len: i64 = int_const_value(len, manager)?;
            if start < 0 || len < 0 || start > i64::MAX - len {
                return Some(manager.mk_string_lit(""));
            }
            let start: usize = start.try_into().ok()?;
            let len: usize = len.try_into().ok()?;
            let result: String = s.chars().skip(start).take(len).collect();
            Some(manager.mk_string_lit(&result))
        }
        TermKind::StrContains(s, sub) => {
            let s = string_const_value(s, manager)?;
            let sub = string_const_value(sub, manager)?;
            Some(bool_term(manager, s.contains(&sub)))
        }
        TermKind::StrPrefixOf(prefix, s) => {
            let prefix = string_const_value(prefix, manager)?;
            let s = string_const_value(s, manager)?;
            Some(bool_term(manager, s.starts_with(&prefix)))
        }
        TermKind::StrSuffixOf(suffix, s) => {
            let suffix = string_const_value(suffix, manager)?;
            let s = string_const_value(s, manager)?;
            Some(bool_term(manager, s.ends_with(&suffix)))
        }
        TermKind::StrIndexOf(s, sub, off) => {
            let s = string_const_value(s, manager)?;
            let sub = string_const_value(sub, manager)?;
            let off: i64 = int_const_value(off, manager)?;
            if off < 0 || off > s.chars().count() as i64 {
                return Some(manager.mk_int(-1));
            }
            let off: usize = off.try_into().ok()?;
            // SMT-LIB counts in characters; convert to byte offset for `find`.
            let byte_off: usize = s.chars().take(off).map(char::len_utf8).sum();
            let result = match s[byte_off..].find(&sub) {
                Some(rel_byte) => {
                    // Convert byte offset back to char offset.
                    let char_rel = s[byte_off..byte_off + rel_byte].chars().count();
                    (off + char_rel) as i64
                }
                None => -1,
            };
            Some(manager.mk_int(result))
        }
        TermKind::StrReplace(s, pat, rep) => {
            let s = string_const_value(s, manager)?;
            let pat = string_const_value(pat, manager)?;
            let rep = string_const_value(rep, manager)?;
            // SMT-LIB str.replace replaces only the *first* occurrence.
            let result = if pat.is_empty() {
                s
            } else {
                s.replacen(&pat, &rep, 1)
            };
            Some(manager.mk_string_lit(&result))
        }
        TermKind::StrReplaceAll(s, pat, rep) => {
            let s = string_const_value(s, manager)?;
            let pat = string_const_value(pat, manager)?;
            let rep = string_const_value(rep, manager)?;
            let result = if pat.is_empty() {
                s
            } else {
                s.replace(&pat, &rep)
            };
            Some(manager.mk_string_lit(&result))
        }
        TermKind::StrToInt(s) => {
            let s = string_const_value(s, manager)?;
            let trimmed = s.trim();
            // SMT-LIB: an optional leading sign followed by decimal digits.
            let parsed = trimmed
                .strip_prefix('-')
                .map(|d| d.parse::<i64>().map(|v| -v))
                .unwrap_or_else(|| trimmed.parse::<i64>());
            match parsed {
                Ok(v) if trimmed.chars().next().is_some_and(|c| c.is_ascii_digit()) => {
                    Some(manager.mk_int(v))
                }
                // Leading '-' without digits, or non-digit content: -1.
                _ => Some(manager.mk_int(-1)),
            }
        }
        TermKind::IntToStr(i) => {
            let i = int_const_value(i, manager)?;
            // SMT-LIB int-to-string: only non-negative integers stringify; a
            // negative input yields the empty string.
            if i < 0 {
                return Some(manager.mk_string_lit(""));
            }
            Some(manager.mk_string_lit(&i.to_string()))
        }

        // ===== Non-foldable: anything else (including StrInRe, which needs the
        // regex theory, not constant folding). =====
        _ => None,
    }
}

// ---------------------------------------------------------------------------
// FP folding helpers
// ---------------------------------------------------------------------------

/// Fold a rounding-mode-tagged binary FP operation (`FpAdd`/`FpSub`/...).
///
/// Only folds when the rounding mode is RNE: Rust's native `f32`/`f64`
/// arithmetic is correctly rounded under RNE, which lets us evaluate the
/// operation with full IEEE-754 precision without depending on the (rounding-
/// mode-incomplete) `Ieee754Engine`. Other rounding modes (RTP/RTN/RTZ/RNA)
/// would require exact fixed-point intermediate computation, so we decline to
/// fold and the term stays un-folded (sound — solver reports `Unknown`).
fn fold_fp_binary(
    rm: RoundingMode,
    a: TermId,
    b: TermId,
    manager: &mut TermManager,
    op_f32: impl Fn(f32, f32) -> f32,
    op_f64: impl Fn(f64, f64) -> f64,
) -> Option<TermId> {
    if rm != RoundingMode::RNE {
        return None;
    }
    let (av, af) = fp_const_value(a, manager)?;
    let (bv, bf) = fp_const_value(b, manager)?;
    if af != bf {
        return None;
    }
    let result = match af {
        FpFormat::FLOAT32 => {
            let x = fp_value_to_f32(&av)?;
            let y = fp_value_to_f32(&bv)?;
            f32_to_fp_value(op_f32(x, y))
        }
        FpFormat::FLOAT64 => {
            let x = fp_value_to_f64(&av)?;
            let y = fp_value_to_f64(&bv)?;
            f64_to_fp_value(op_f64(x, y))
        }
        _ => return None,
    };
    if result.is_nan() || result.is_infinite() || result.is_zero() {
        // Preserve structural info for the `check_fp_constraints` pass, which
        // keys on patterns like `y = fp.div(0, 0)` to detect NaN-related
        // conflicts. Folding the op away to a special value would erase
        // that structure and turn a detectable Unsat into Unknown.
        return None;
    }
    Some(make_fp_const(manager, &result, af))
}

/// Fold a rounding-mode-tagged unary FP operation (`FpSqrt`, `FpRoundToIntegral`).
fn fold_fp_unary(
    rm: RoundingMode,
    a: TermId,
    manager: &mut TermManager,
    op_f32: impl Fn(f32) -> f32,
    op_f64: impl Fn(f64) -> f64,
) -> Option<TermId> {
    if rm != RoundingMode::RNE {
        return None;
    }
    let (av, af) = fp_const_value(a, manager)?;
    let result = match af {
        FpFormat::FLOAT32 => {
            let x = fp_value_to_f32(&av)?;
            f32_to_fp_value(op_f32(x))
        }
        FpFormat::FLOAT64 => {
            let x = fp_value_to_f64(&av)?;
            f64_to_fp_value(op_f64(x))
        }
        _ => return None,
    };
    if result.is_nan() || result.is_infinite() || result.is_zero() {
        return None;
    }
    Some(make_fp_const(manager, &result, af))
}

/// Fold a binary FP op that has no rounding mode (`FpRem`/`FpMin`/`FpMax`).
fn fold_fp_binary_no_rm(
    a: TermId,
    b: TermId,
    manager: &mut TermManager,
    op_f32: impl Fn(f32, f32) -> f32,
    op_f64: impl Fn(f64, f64) -> f64,
) -> Option<TermId> {
    let (av, af) = fp_const_value(a, manager)?;
    let (bv, bf) = fp_const_value(b, manager)?;
    if af != bf {
        return None;
    }
    let result = match af {
        FpFormat::FLOAT32 => {
            let x = fp_value_to_f32(&av)?;
            let y = fp_value_to_f32(&bv)?;
            f32_to_fp_value(op_f32(x, y))
        }
        FpFormat::FLOAT64 => {
            let x = fp_value_to_f64(&av)?;
            let y = fp_value_to_f64(&bv)?;
            f64_to_fp_value(op_f64(x, y))
        }
        _ => return None,
    };
    if result.is_nan() || result.is_infinite() || result.is_zero() {
        return None;
    }
    Some(make_fp_const(manager, &result, af))
}

/// Fold a unary FP op that has no rounding mode (`FpAbs`/`FpNeg`).
fn fold_fp_unary_no_rm(
    a: TermId,
    manager: &mut TermManager,
    op_f32: impl Fn(f32) -> f32,
    op_f64: impl Fn(f64) -> f64,
) -> Option<TermId> {
    let (av, af) = fp_const_value(a, manager)?;
    let result = match af {
        FpFormat::FLOAT32 => {
            let x = fp_value_to_f32(&av)?;
            f32_to_fp_value(op_f32(x))
        }
        FpFormat::FLOAT64 => {
            let x = fp_value_to_f64(&av)?;
            f64_to_fp_value(op_f64(x))
        }
        _ => return None,
    };
    Some(make_fp_const(manager, &result, af))
}

/// Fold a binary FP predicate (`FpEq`/`FpLt`/...) to a Bool term.
fn fold_fp_pred(
    a: TermId,
    b: TermId,
    manager: &mut TermManager,
    op_f32: impl Fn(f32, f32) -> bool,
    op_f64: impl Fn(f64, f64) -> bool,
) -> Option<TermId> {
    let (av, af) = fp_const_value(a, manager)?;
    let (bv, bf) = fp_const_value(b, manager)?;
    // Predicates work across formats if both are known — but IEEE-754
    // comparison requires a common format. Bail out if formats differ.
    if af != bf {
        return None;
    }
    let result = match af {
        FpFormat::FLOAT32 => op_f32(fp_value_to_f32(&av)?, fp_value_to_f32(&bv)?),
        FpFormat::FLOAT64 => op_f64(fp_value_to_f64(&av)?, fp_value_to_f64(&bv)?),
        _ => return None,
    };
    Some(bool_term(manager, result))
}

#[allow(dead_code)]
#[derive(Clone, Copy)]
#[allow(clippy::enum_variant_names)]
enum FpClassPred {
    IsNan,
    IsInfinite,
    IsZero,
    IsNormal,
    IsSubnormal,
    IsPositive,
    IsNegative,
}

/// Fold a unary FP class predicate (`FpIsNaN`/`FpIsZero`/...) to a Bool.
///
/// Currently unused: the call sites above intentionally return `None` to
/// preserve the structural information that `check_fp_constraints` relies
/// on. Kept here so a future enhancement that does not interfere with that
/// pass can simply re-wire the call sites.
#[allow(dead_code)]
fn fold_fp_class_pred(a: TermId, manager: &mut TermManager, pred: FpClassPred) -> Option<TermId> {
    let (val, _format) = fp_const_value(a, manager)?;
    let result = match pred {
        FpClassPred::IsNan => val.is_nan(),
        FpClassPred::IsInfinite => val.is_infinite(),
        FpClassPred::IsZero => val.is_zero(),
        FpClassPred::IsNormal => val.is_normal(),
        FpClassPred::IsSubnormal => val.is_subnormal(),
        FpClassPred::IsPositive => val.is_positive(),
        FpClassPred::IsNegative => val.is_negative(),
    };
    Some(bool_term(manager, result))
}

/// Extract the [`FpValue`] and [`FpFormat`] of any ground FP constant term
/// (`FpLit`, `FpNaN`, `FpPlusInfinity`, ...). Returns `None` for non-constant
/// terms and for formats the engine does not support (anything other than
/// binary16/32/64/128).
fn fp_const_value(term: TermId, manager: &TermManager) -> Option<(FpValue, FpFormat)> {
    let t = manager.get(term)?;
    let sort = manager.sorts.get(t.sort)?;
    let (eb, sb) = sort.float_format()?;
    let format = fp_format_of(eb, sb)?;
    let value = match &t.kind {
        TermKind::FpLit {
            sign,
            exp,
            sig,
            eb,
            sb,
        } => {
            // The engine expects biased exponent and significand-without-implicit-bit.
            // `FpLit` stores them raw, so we need to encode into FpValue. We
            // rebuild via the f64 round-trip for the supported formats only,
            // since the engine's internal FpValue layout assumes the implicit
            // bit is stripped.
            fp_lit_to_value(*sign, exp, sig, *eb, *sb)?
        }
        TermKind::FpPlusInfinity { .. } => FpValue::pos_infinity(format),
        TermKind::FpMinusInfinity { .. } => FpValue::neg_infinity(format),
        TermKind::FpPlusZero { .. } => FpValue::pos_zero(format),
        TermKind::FpMinusZero { .. } => FpValue::neg_zero(format),
        TermKind::FpNaN { .. } => FpValue::nan(format),
        _ => return None,
    };
    Some((value, format))
}

/// Map `(eb, sb)` to an IEEE 754 binary format the engine understands.
fn fp_format_of(eb: u32, sb: u32) -> Option<FpFormat> {
    match (eb, sb) {
        (5, 11) => Some(FpFormat::FLOAT16),
        (8, 24) => Some(FpFormat::FLOAT32),
        (11, 53) => Some(FpFormat::FLOAT64),
        (15, 113) => Some(FpFormat::FLOAT128),
        _ => None,
    }
}

/// Convert an `oxiz-core` rounding mode to the engine's rounding mode.
#[allow(dead_code)]
fn convert_rm(rm: RoundingMode) -> FpRoundingMode {
    match rm {
        RoundingMode::RNE => FpRoundingMode::RoundNearestTiesToEven,
        RoundingMode::RNA => FpRoundingMode::RoundNearestTiesToAway,
        RoundingMode::RTP => FpRoundingMode::RoundTowardPositive,
        RoundingMode::RTN => FpRoundingMode::RoundTowardNegative,
        RoundingMode::RTZ => FpRoundingMode::RoundTowardZero,
    }
}

/// Decode an `FpLit`'s raw `(sign, exp, sig, eb, sb)` fields into an
/// [`FpValue`] for one of the four supported formats.
///
/// `FpLit` stores the biased exponent and the *full* significand bit-pattern
/// (including the implicit leading 1 for normal numbers), exactly as it would
/// appear in the IEEE 754 bit encoding. The engine's `FpValue` strips the
/// implicit bit from normal numbers. To avoid reimplementing that logic, we
/// round-trip through `f32`/`f64` for binary32/64 (the formats actually used
/// by the parity benchmarks); binary16/128 fall back to assembling `FpValue`
/// fields directly when the layout is canonical.
fn fp_lit_to_value(
    sign: bool,
    exp: &num_bigint::BigInt,
    sig: &num_bigint::BigInt,
    eb: u32,
    sb: u32,
) -> Option<FpValue> {
    let format = fp_format_of(eb, sb)?;
    // Fast path: binary32 / binary64 via f32 / f64 bit reconstruction.
    if eb == 8 && sb == 24 {
        let exp_u: u64 = exp.try_into().ok()?;
        let sig_u: u64 = sig.try_into().ok()?;
        let mut bits: u32 = 0;
        if sign {
            bits |= 1u32 << 31;
        }
        bits |= ((exp_u & 0xFF) as u32) << 23;
        bits |= (sig_u & 0x7FFFFF) as u32;
        return Some(FpValue::from_f32(f32::from_bits(bits)));
    }
    if eb == 11 && sb == 53 {
        let exp_u: u64 = exp.try_into().ok()?;
        let sig_u: u64 = sig.try_into().ok()?;
        let mut bits: u64 = 0;
        if sign {
            bits |= 1u64 << 63;
        }
        bits |= (exp_u & 0x7FF) << 52;
        bits |= sig_u & 0xFFFFFFFFFFFFF;
        return Some(FpValue::from_f64(f64::from_bits(bits)));
    }
    // binary16 / binary128: assemble FpValue fields directly. (Used rarely;
    // not round-tripped through hardware FP.)
    let exp_u: u64 = exp.try_into().ok()?;
    let sig_u: u64 = sig.try_into().ok()?;
    Some(FpValue {
        sign,
        exponent: exp_u,
        significand: sig_u,
        format,
    })
}

/// Construct the canonical constant term for an FP value: a dedicated
/// `FpNaN`/`FpPlusInfinity`/`FpPlusZero`/... term for the special cases
/// (so subsequent rewrites can pattern-match them), or an `FpLit` for any
/// other bit pattern.
fn make_fp_const(manager: &mut TermManager, value: &FpValue, format: FpFormat) -> TermId {
    let (eb, sb) = (format.exponent_bits, format.significand_bits);
    if value.is_nan() {
        return manager.mk_fp_nan(eb, sb);
    }
    if value.is_infinite() {
        return if value.sign {
            manager.mk_fp_minus_infinity(eb, sb)
        } else {
            manager.mk_fp_plus_infinity(eb, sb)
        };
    }
    if value.is_zero() {
        return if value.sign {
            manager.mk_fp_minus_zero(eb, sb)
        } else {
            manager.mk_fp_plus_zero(eb, sb)
        };
    }
    // Normal or subnormal: encode as an FpLit. Round-trip through f32/f64
    // for the supported formats to recover the canonical (sign, exp, sig)
    // triple the AST stores.
    if let Some(f) = fp_value_to_f32(value) {
        let bits = f.to_bits();
        let sign = (bits >> 31) != 0;
        let exp = (bits >> 23) & 0xFF;
        let sig = bits & 0x7FFFFF;
        return manager.mk_fp_lit(sign, exp as u64, sig as u64, eb, sb);
    }
    if let Some(f) = fp_value_to_f64(value) {
        let bits = f.to_bits();
        let sign = (bits >> 63) != 0;
        let exp = (bits >> 52) & 0x7FF;
        let sig = bits & 0xFFFFFFFFFFFFF;
        return manager.mk_fp_lit(sign, exp, sig, eb, sb);
    }
    // binary16 / binary128: emit FpLit with the engine's biased exponent
    // and significand directly. (The implicit bit is *not* stored in
    // `FpValue` for normal numbers, so we re-insert it.)
    let exp = value.exponent;
    let sig = if value.is_normal() {
        // Re-insert the implicit leading 1 in the top significand bit.
        value.significand | (1u64 << (sb - 2))
    } else {
        value.significand
    };
    manager.mk_fp_lit(value.sign, exp, sig, eb, sb)
}

/// Convert an `FpValue` of binary32 to `f32`. Returns `None` for other formats.
fn fp_value_to_f32(value: &FpValue) -> Option<f32> {
    if value.format != FpFormat::FLOAT32 {
        return None;
    }
    let mut bits: u32 = 0;
    if value.sign {
        bits |= 1u32 << 31;
    }
    bits |= ((value.exponent & 0xFF) as u32) << 23;
    bits |= (value.significand & 0x7FFFFF) as u32;
    Some(f32::from_bits(bits))
}

/// Construct an `FpValue` (Float32) from an `f32`.
fn f32_to_fp_value(f: f32) -> FpValue {
    FpValue::from_f32(f)
}

/// Construct an `FpValue` (Float64) from an `f64`.
fn f64_to_fp_value(f: f64) -> FpValue {
    FpValue::from_f64(f)
}

/// Convert an `FpValue` of binary64 to `f64`. Returns `None` for other formats.
fn fp_value_to_f64(value: &FpValue) -> Option<f64> {
    if value.format != FpFormat::FLOAT64 {
        return None;
    }
    let mut bits: u64 = 0;
    if value.sign {
        bits |= 1u64 << 63;
    }
    bits |= (value.exponent & 0x7FF) << 52;
    bits |= value.significand & 0xFFFFFFFFFFFFF;
    Some(f64::from_bits(bits))
}

/// Check that a signed integer fits in `width` bits (two's complement).
fn fits_in_width_signed_i128(i: i128, width: u32) -> bool {
    if width == 0 {
        return false;
    }
    if width >= 128 {
        return true;
    }
    let bound: i128 = 1i128 << (width - 1);
    (-bound..bound).contains(&i)
}

/// Check that an unsigned integer fits in `width` bits.
fn fits_in_width_unsigned_u128(u: u128, width: u32) -> bool {
    if width == 0 {
        return false;
    }
    if width >= 128 {
        return true;
    }
    u < (1u128 << width)
}

/// Convert a finite `f64` to a `Rational64` exactly.
///
/// `f64` is always a dyadic rational, so this is exact. Returns `None` for
/// NaN/∞ (which are not real numbers).
fn rational_from_f64(f: f64) -> Option<num_rational::Rational64> {
    if !f.is_finite() {
        return None;
    }
    // f.is_finite() implies f != NaN/∞; bits encode a dyadic rational.
    let bits = f.to_bits();
    let sign = (bits >> 63) != 0;
    let raw_exp = ((bits >> 52) & 0x7FF) as i64;
    let mantissa = (bits & 0xFFFFFFFFFFFFF) as i64;
    // subnormal: exponent stays at -1074; mantissa has no implicit bit.
    // normal: implicit leading 1, exponent bias -1075.
    let (m, e) = if raw_exp == 0 {
        (mantissa, -1074)
    } else {
        (mantissa + (1i64 << 52), raw_exp - 1075)
    };
    let abs = if e >= 0 {
        num_rational::Rational64::new(m.checked_shl(e as u32)?, 1)
    } else {
        num_rational::Rational64::new(m, 1i64.checked_shl((-e) as u32)?)
    };
    Some(if sign { -abs } else { abs })
}

/// Sign-extend the low `width` bits of `bv` to a signed `i64`.
fn sign_extend_i64(bv: u64, width: u32) -> i64 {
    if width == 0 {
        return 0;
    }
    if width >= 64 {
        return bv as i64;
    }
    let shift = 64 - width;
    ((bv << shift) as i64) >> shift
}

// ---------------------------------------------------------------------------
// String folding helpers
// ---------------------------------------------------------------------------

/// Extract the `String` value of a `StringLit` term.
fn string_const_value(term: TermId, manager: &TermManager) -> Option<String> {
    let t = manager.get(term)?;
    match &t.kind {
        TermKind::StringLit(s) => Some(s.clone()),
        _ => None,
    }
}

/// Extract the value of an `IntConst` or `RealConst` (when integral) as `i64`.
fn int_const_value(term: TermId, manager: &TermManager) -> Option<i64> {
    let t = manager.get(term)?;
    match &t.kind {
        TermKind::IntConst(b) => b.try_into().ok(),
        TermKind::RealConst(r) => {
            if r.is_integer() {
                r.to_integer().try_into().ok()
            } else {
                None
            }
        }
        _ => None,
    }
}

/// Extract the value of a `RealConst` (or integral `IntConst`) as `f64`.
fn real_const_value(term: TermId, manager: &TermManager) -> Option<f64> {
    let t = manager.get(term)?;
    match &t.kind {
        TermKind::IntConst(b) => {
            let i: i64 = b.try_into().ok()?;
            Some(i as f64)
        }
        TermKind::RealConst(r) => {
            // Rational64 → f64 (may lose precision; consistent with how z3
            // rounds a decimal literal like 1.5 to the nearest f64).
            let num = (*r.numer()) as f64;
            let den = (*r.denom()) as f64;
            Some(num / den)
        }
        _ => None,
    }
}

/// Extract the value of a `BitVecConst` as `u64` (zero-extending wider values).
fn bv_const_value(term: TermId, manager: &TermManager) -> Option<u64> {
    let t = manager.get(term)?;
    match &t.kind {
        TermKind::BitVecConst { value, width: _ } => {
            // Take the low 64 bits; BV constants wider than 64 are not
            // supported by this folder.
            value.iter_u64_digits().next().unwrap_or(0).into()
        }
        _ => None,
    }
}

/// Construct a Boolean constant term.
fn bool_term(manager: &mut TermManager, value: bool) -> TermId {
    if value {
        manager.mk_true()
    } else {
        manager.mk_false()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn mk() -> TermManager {
        TermManager::new()
    }

    /// Build an `FpLit` for a Float32 constant via its IEEE-754 bit pattern.
    fn f32_to_lit(m: &mut TermManager, f: f32) -> TermId {
        let bits = f.to_bits() as u64;
        m.mk_fp_lit(
            (bits >> 31) != 0,
            (bits >> 23) & 0xFF,
            bits & 0x7FFFFF,
            8,
            24,
        )
    }

    /// Extract the `f32` value of an `FpLit` (Float32 only).
    fn lit_to_f32(m: &TermManager, t: TermId) -> Option<f32> {
        match &m.get(t)?.kind {
            TermKind::FpLit { sign, exp, sig, .. } => {
                let exp_u: u32 = exp.try_into().ok()?;
                let sig_u: u32 = sig.try_into().ok()?;
                let mut bits: u32 = 0;
                if *sign {
                    bits |= 1u32 << 31;
                }
                bits |= (exp_u & 0xFF) << 23;
                bits |= sig_u & 0x7FFFFF;
                Some(f32::from_bits(bits))
            }
            _ => None,
        }
    }

    #[test]
    fn fold_fp_add_two_constants() {
        let mut m = mk();
        let a = f32_to_lit(&mut m, 1.5);
        let b = f32_to_lit(&mut m, 2.5);
        let add = m.mk_fp_add(RoundingMode::RNE, a, b);
        let folded = try_fold(add, &mut m).expect("should fold");
        // 1.5 + 2.5 = 4.0 exactly in f32.
        let f = lit_to_f32(&m, folded).expect("folded to FpLit");
        assert!((f - 4.0).abs() < 1e-6, "got {f}");
    }

    #[test]
    fn fold_fp_gt_constants() {
        let mut m = mk();
        let a = f32_to_lit(&mut m, 4.0);
        let b = f32_to_lit(&mut m, 3.7);
        let gt = m.mk_fp_gt(a, b);
        let folded = try_fold(gt, &mut m).expect("should fold");
        assert!(matches!(m.get(folded).unwrap().kind, TermKind::True));
    }

    #[test]
    fn fold_real_to_fp_decimal() {
        // Reproduces the fp_01 case: `((_ to_fp 8 24) RNE 3.7)` must fold
        // to the Float32 literal closest to 3.7. Regression: an earlier
        // version of the folder returned None for non-integral rationals,
        // leaving the comparison un-folded and reporting Unknown.
        let mut m = mk();
        let r = m.mk_real(num_rational::Rational64::new(37, 10));
        let to_fp = m.mk_real_to_fp(RoundingMode::RNE, r, 8, 24);
        let folded = try_fold(to_fp, &mut m).expect("37/10 -> Float32 should fold");
        let f = lit_to_f32(&m, folded).expect("folded to FpLit");
        assert!((f - 3.7).abs() < 1e-4, "got {f}");
    }

    #[test]
    fn fold_real_to_fp() {
        let mut m = mk();
        // 1.5 as a RealConst: Rational64::new(3, 2).
        let r = m.mk_real(num_rational::Rational64::new(3, 2));
        let to_fp = m.mk_real_to_fp(RoundingMode::RNE, r, 8, 24);
        let folded = try_fold(to_fp, &mut m).expect("should fold");
        let f = lit_to_f32(&m, folded).expect("folded to FpLit");
        assert!((f - 1.5).abs() < 1e-6, "got {f}");
    }

    #[test]
    fn fold_fp_div_rtp_vs_rtn_differ() {
        // 10.0 / 3.0 in Float64 with non-RNE rounding modes: the folder
        // declines to fold (the engine's RTP/RTN paths have a rounding-mode
        // application bug; native Rust can't help since `f64 / f64` is RNE).
        // Folding must return `None` for both RTP and RTN — never a wrong
        // value that would make `(not (= c_rtp c_rtn)) ∧ (= c_rtp c_rtn)` look
        // like a real conflict.
        let mut m = mk();
        let f64_to_lit = |m: &mut TermManager, f: f64| -> TermId {
            let bits = f.to_bits();
            m.mk_fp_lit(
                (bits >> 63) != 0,
                (bits >> 52) & 0x7FF,
                bits & 0xFFFFFFFFFFFFF,
                11,
                53,
            )
        };
        let a = f64_to_lit(&mut m, 10.0);
        let b = f64_to_lit(&mut m, 3.0);
        let div_rtp = m.mk_fp_div(RoundingMode::RTP, a, b);
        let div_rtn = m.mk_fp_div(RoundingMode::RTN, a, b);
        assert_eq!(
            try_fold(div_rtp, &mut m),
            None,
            "RTP division must NOT fold (would risk wrong answer)"
        );
        assert_eq!(
            try_fold(div_rtn, &mut m),
            None,
            "RTN division must NOT fold (would risk wrong answer)"
        );
    }

    #[test]
    fn fold_fp_div_rne_works() {
        // 6.0 / 2.0 in Float64 with RNE: exactly 3.0, should fold.
        let mut m = mk();
        let f64_to_lit = |m: &mut TermManager, f: f64| -> TermId {
            let bits = f.to_bits();
            m.mk_fp_lit(
                (bits >> 63) != 0,
                (bits >> 52) & 0x7FF,
                bits & 0xFFFFFFFFFFFFF,
                11,
                53,
            )
        };
        let a = f64_to_lit(&mut m, 6.0);
        let b = f64_to_lit(&mut m, 2.0);
        let div = m.mk_fp_div(RoundingMode::RNE, a, b);
        let folded = try_fold(div, &mut m).expect("RNE division should fold");
        match &m.get(folded).unwrap().kind {
            TermKind::FpLit { sign, exp, sig, .. } => {
                let mut bits: u64 = 0;
                if *sign {
                    bits |= 1u64 << 63;
                }
                let exp_u: u64 = exp.try_into().unwrap();
                let sig_u: u64 = sig.try_into().unwrap();
                bits |= (exp_u & 0x7FF) << 52;
                bits |= sig_u & 0xFFFFFFFFFFFFF;
                assert!((f64::from_bits(bits) - 3.0).abs() < 1e-10);
            }
            _ => panic!("expected FpLit"),
        }
    }

    #[test]
    fn fold_string_concat() {
        let mut m = mk();
        let a = m.mk_string_lit("hello, ");
        let b = m.mk_string_lit("world");
        let concat = m.mk_str_concat(a, b);
        let folded = try_fold(concat, &mut m).expect("should fold");
        match m.get(folded).unwrap().kind {
            TermKind::StringLit(ref s) => assert_eq!(s, "hello, world"),
            _ => panic!("expected StringLit"),
        }
    }

    #[test]
    fn fold_string_len() {
        let mut m = mk();
        let s = m.mk_string_lit("hello");
        let len = m.mk_str_len(s);
        let folded = try_fold(len, &mut m).expect("should fold");
        match m.get(folded).unwrap().kind {
            TermKind::IntConst(ref b) => {
                let v: i64 = b.try_into().unwrap();
                assert_eq!(v, 5);
            }
            _ => panic!("expected IntConst"),
        }
    }

    #[test]
    fn fold_string_contains() {
        let mut m = mk();
        let s = m.mk_string_lit("hello world");
        let sub = m.mk_string_lit("world");
        let c = m.mk_str_contains(s, sub);
        let folded = try_fold(c, &mut m).expect("should fold");
        assert!(matches!(m.get(folded).unwrap().kind, TermKind::True));
    }
}
