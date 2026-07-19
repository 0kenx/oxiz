//! Term parsing for the SMT-LIB2 parser

use super::super::lexer::TokenKind;
use super::{Attribute, Parser, parse_decimal_to_rational};
use crate::ast::{RoundingMode, TermId};
use crate::error::{OxizError, Result};
#[allow(unused_imports)]
use crate::prelude::*;
use crate::sort::SortKind;
use num_bigint::BigInt;
use num_rational::Rational64;
use smallvec::SmallVec;
use std::cell::Cell;

/// Maximum recursive nesting depth accepted by the recursive-descent term
/// parser. Adversarial inputs with pathologically deep nesting (e.g. millions
/// of `(- (- (- ...)))`) would otherwise overflow the native call stack; once
/// this bound is exceeded we surface an honest [`OxizError::ParseError`]
/// instead of aborting the process.
const MAX_PARSE_DEPTH: u32 = 1024;

thread_local! {
    /// Current recursion depth of [`Parser::parse_term`] on this thread.
    static PARSE_DEPTH: Cell<u32> = const { Cell::new(0) };
}

/// RAII guard that decrements the [`PARSE_DEPTH`] counter when it leaves scope,
/// including on error unwinding, so the depth stays accurate across every
/// return path of `parse_term`.
struct DepthGuard;

impl Drop for DepthGuard {
    fn drop(&mut self) {
        PARSE_DEPTH.with(|d| d.set(d.get().saturating_sub(1)));
    }
}

impl<'a> Parser<'a> {
    /// Parse a term.
    ///
    /// This wraps the actual recursive-descent logic in a depth guard so that
    /// deeply nested input cannot overflow the stack; see [`MAX_PARSE_DEPTH`].
    pub fn parse_term(&mut self) -> Result<TermId> {
        let depth = PARSE_DEPTH.with(|d| {
            let next = d.get().saturating_add(1);
            d.set(next);
            next
        });
        let _guard = DepthGuard;
        if depth > MAX_PARSE_DEPTH {
            return Err(OxizError::ParseError {
                position: self.lexer.position(),
                message: "term nesting too deep".to_string(),
            });
        }
        self.parse_term_inner()
    }

    /// Inner term parser; callers must go through [`Parser::parse_term`] so the
    /// recursion-depth guard stays in effect.
    fn parse_term_inner(&mut self) -> Result<TermId> {
        let token = self
            .lexer
            .next_token()
            .ok_or_else(|| OxizError::ParseError {
                position: self.lexer.position(),
                message: "unexpected end of input".to_string(),
            })?;

        match token.kind {
            TokenKind::LParen => self.parse_compound_term(),
            TokenKind::Symbol(s) => self.parse_symbol(&s),
            TokenKind::Numeral(n) => {
                let value: BigInt = n.parse().map_err(|_| OxizError::ParseError {
                    position: token.start,
                    message: format!("invalid numeral: {n}"),
                })?;
                Ok(self.manager.mk_int(value))
            }
            TokenKind::Hexadecimal(h) => {
                let value =
                    BigInt::parse_bytes(h.as_bytes(), 16).ok_or_else(|| OxizError::ParseError {
                        position: token.start,
                        message: format!("invalid hexadecimal: {h}"),
                    })?;
                let width = (h.len() * 4) as u32;
                Ok(self.manager.mk_bitvec(value, width))
            }
            TokenKind::Binary(b) => {
                let value =
                    BigInt::parse_bytes(b.as_bytes(), 2).ok_or_else(|| OxizError::ParseError {
                        position: token.start,
                        message: format!("invalid binary: {b}"),
                    })?;
                let width = b.len() as u32;
                Ok(self.manager.mk_bitvec(value, width))
            }
            TokenKind::Decimal(d) => {
                // Parse decimal literal as Rational64
                let rational =
                    parse_decimal_to_rational(&d).map_err(|e| OxizError::ParseError {
                        position: token.start,
                        message: format!("invalid decimal: {d} - {e}"),
                    })?;
                Ok(self.manager.mk_real(rational))
            }
            TokenKind::StringLit(s) => {
                // Parse string literal
                Ok(self.manager.mk_string_lit(&s))
            }
            _ => Err(OxizError::ParseError {
                position: token.start,
                message: format!("unexpected token: {:?}", token.kind),
            }),
        }
    }

    pub(super) fn parse_symbol(&mut self, s: &str) -> Result<TermId> {
        match s {
            "true" => Ok(self.manager.mk_true()),
            "false" => Ok(self.manager.mk_false()),
            // SMT-LIB Strings theory regex constants. These are zero-argument
            // regex operators that appear as bare symbols (e.g.
            // `(re.* re.allchar)`), so without an explicit case they would be
            // rejected by the strict-undeclared-symbol check below. oxiz's
            // term layer models regexes as opaque uninterpreted applies (it
            // has no dedicated RegEx sort), so we mint them as zero-argument
            // applies of the same name — consistent with how compound regex
            // operators (`re.*`, `re.++`, `re.union`, `re.range`, ...) are
            // lowered today via the generic compound-operator fallback.
            "re.allchar" | "re.all" | "re.none" | "re.empty" => {
                Ok(self.manager.mk_apply(s, [], self.manager.sorts.bool_sort))
            }
            _ => {
                // Check bindings first
                if let Some(&term) = self.bindings.get(s) {
                    return Ok(term);
                }
                // Check if this is a datatype constructor (e.g., Monday, nil, cons, etc.)
                if let Some(&dt_sort) = self.dt_constructors.get(s) {
                    return Ok(self.manager.mk_dt_constructor(s, vec![], dt_sort));
                }
                // Check constants
                if let Some(&sort) = self.constants.get(s) {
                    return Ok(self.manager.mk_var(s, sort));
                }
                // Z3-compatible shortcut: the SMT-LIB 2 grammar does not treat
                // `-3` or `-3.0` as a numeric literal (they parse as symbols
                // because `-` is a valid symbol char), but Z3 accepts them as
                // negative numbers.  If the symbol matches the pattern of a
                // negative numeral or decimal and has not been bound to
                // anything else, interpret it as such — otherwise arithmetic
                // constraints like `(* -3.0 x)` silently become nonsense
                // boolean-sorted variables.
                if let Some(rest) = s.strip_prefix('-')
                    && !rest.is_empty()
                    && rest.chars().next().is_some_and(|c| c.is_ascii_digit())
                {
                    if let Some(dot_idx) = rest.find('.') {
                        let (int_part, frac_part) = rest.split_at(dot_idx);
                        let frac_part = &frac_part[1..];
                        if int_part.chars().all(|c| c.is_ascii_digit())
                            && !frac_part.is_empty()
                            && frac_part.chars().all(|c| c.is_ascii_digit())
                        {
                            let rational =
                                super::parse_decimal_to_rational(rest).map_err(|_| {
                                    OxizError::ParseError {
                                        position: self.lexer.position(),
                                        message: format!("invalid negative decimal: {s}"),
                                    }
                                })?;
                            return Ok(self.manager.mk_real(-rational));
                        }
                    } else if rest.chars().all(|c| c.is_ascii_digit()) {
                        let value: BigInt = rest.parse().map_err(|_| OxizError::ParseError {
                            position: self.lexer.position(),
                            message: format!("invalid negative numeral: {s}"),
                        })?;
                        return Ok(self.manager.mk_int(-value));
                    }
                }
                // At this point `s` is not a bound variable, a datatype
                // constructor, a declared constant, or a negative numeric
                // literal. In a genuine SMT-LIB script every symbol must be
                // declared before use, so an unknown symbol here is a typo or
                // a missing `declare-const`/`declare-fun`. Silently minting a
                // fresh Bool-sorted variable (the old behavior) makes such a
                // script solve a *different* problem and can report `sat` with
                // a meaningless model. Reject it, matching Z3's "unknown
                // constant" error.
                //
                // The one exception is the bare `parse_term` convenience path
                // used to build ad-hoc terms with no declarations at all: when
                // parsing an isolated term (not a script) we stay lenient so
                // that free variables can still be constructed.
                if self.script_mode {
                    return Err(OxizError::ParseError {
                        position: self.lexer.position(),
                        message: format!("unknown constant or symbol: {s}"),
                    });
                }
                // Lenient fallback (bare-term mode): boolean variable.
                let sort = self.manager.sorts.bool_sort;
                Ok(self.manager.mk_var(s, sort))
            }
        }
    }

    /// Returns `true` if the given term has Real sort.
    fn is_real_term(&self, term: TermId) -> bool {
        self.manager
            .get(term)
            .and_then(|t| self.manager.sorts.get(t.sort))
            .is_some_and(|s| matches!(s.kind, SortKind::Real))
    }

    /// Returns the bit-vector width of `term`, if it has a bit-vector sort.
    fn bv_width(&self, term: TermId) -> Option<u32> {
        let sort = self.manager.get(term)?.sort;
        self.manager.sorts.get(sort)?.bitvec_width()
    }

    /// Build the conjunction of the boolean atoms produced by a chainable
    /// operator (`=`, `<`, `<=`, `>`, `>=`). SMT-LIB defines these operators as
    /// *chainable*: `(op a b c)` means `(and (op a b) (op b c))`. When there is
    /// a single atom (the binary case) it is returned directly so that ordinary
    /// binary uses keep their exact term kind (e.g. `Lt`, `Eq`) rather than
    /// being wrapped in a one-element `and`.
    fn chain_conjunction(&mut self, atoms: Vec<TermId>) -> TermId {
        if atoms.len() == 1 {
            atoms[0]
        } else {
            self.manager.mk_and(atoms)
        }
    }

    /// Two-operand XOR lowered to `and`/`or`/`not`, used to fold the
    /// left-associative n-ary `xor`.
    fn mk_xor2(&mut self, lhs: TermId, rhs: TermId) -> TermId {
        let not_lhs = self.manager.mk_not(lhs);
        let not_rhs = self.manager.mk_not(rhs);
        let and1 = self.manager.mk_and([lhs, not_rhs]);
        let and2 = self.manager.mk_and([not_lhs, rhs]);
        self.manager.mk_or([and1, and2])
    }

    /// Construct an honest arity error for a core operator that requires at
    /// least `min` operands but received `got`.
    fn min_arity_err(&self, op: &str, min: usize, got: usize) -> OxizError {
        OxizError::ParseError {
            position: self.lexer.position(),
            message: format!("{op} requires at least {min} arguments, got {got}"),
        }
    }

    /// If the next token is a closing `)`, consume it and return `true`;
    /// otherwise leave the stream untouched and return `false`.
    ///
    /// The n-ary/chainable core operators use this to parse their first operand
    /// with a *direct* [`Parser::parse_term`] call and then loop over the rest,
    /// mirroring the existing `div` / `/` / `str.++` idiom. Parsing the first
    /// operand directly (rather than through [`Parser::parse_term_list`]) keeps
    /// the recursive-descent stack-frame count per nesting level identical to
    /// the original binary handlers, so deeply nested input still trips the
    /// [`MAX_PARSE_DEPTH`] guard before it can overflow the native stack.
    fn try_consume_rparen(&mut self) -> bool {
        if let Some(token) = self.lexer.peek()
            && matches!(token.kind, TokenKind::RParen)
        {
            self.lexer.next_token();
            return true;
        }
        false
    }

    /// Attempt to build an indexed operator whose name/indices/arguments have
    /// already been parsed.
    ///
    /// Handles the indexed bit-vector operators that have no dedicated
    /// [`crate::ast::TermKind`] (`zero_extend`, `sign_extend`, `rotate_left`,
    /// `rotate_right`, `repeat`) by lowering them to existing primitives
    /// (`concat`, `extract`), and the arithmetic `divisible` predicate.
    ///
    /// Returns `Ok(Some(term))` when the operator was recognized and built,
    /// `Ok(None)` when it is not one of these operators (so the caller can fall
    /// back to a generic application), or `Err(..)` on a malformed use.
    fn build_indexed_op(
        &mut self,
        name: &str,
        index_parts: &[String],
        args: &[TermId],
    ) -> Result<Option<TermId>> {
        // Parse the leading numeric index shared by every operator here.
        let single_index = |parts: &[String]| -> Result<u32> {
            if parts.len() != 1 {
                return Err(OxizError::ParseError {
                    position: 0,
                    message: format!(
                        "(_ {name} ...) requires exactly 1 index, got {}",
                        parts.len()
                    ),
                });
            }
            parts[0].parse::<u32>().map_err(|_| OxizError::ParseError {
                position: 0,
                message: format!("invalid index for (_ {name} ...): {}", parts[0]),
            })
        };
        let single_arg = |args: &[TermId]| -> Result<TermId> {
            if args.len() != 1 {
                return Err(OxizError::ParseError {
                    position: 0,
                    message: format!(
                        "(_ {name} ...) requires exactly 1 argument, got {}",
                        args.len()
                    ),
                });
            }
            Ok(args[0])
        };

        match name {
            "zero_extend" => {
                let n = single_index(index_parts)?;
                let arg = single_arg(args)?;
                if n == 0 {
                    return Ok(Some(arg));
                }
                // Prepend `n` zero bits: concat(0:n, arg).
                let zeros = self.manager.mk_bitvec(0, n);
                Ok(Some(self.manager.mk_bv_concat(zeros, arg)))
            }
            "sign_extend" => {
                let n = single_index(index_parts)?;
                let arg = single_arg(args)?;
                if n == 0 {
                    return Ok(Some(arg));
                }
                let width = self.bv_width(arg).ok_or_else(|| OxizError::ParseError {
                    position: 0,
                    message: "sign_extend requires a bit-vector argument".to_string(),
                })?;
                // Replicate the sign bit `n` times, then concat with the arg.
                let sign_bit = self.manager.mk_bv_extract(width - 1, width - 1, arg);
                let mut ext = sign_bit;
                for _ in 1..n {
                    ext = self.manager.mk_bv_concat(ext, sign_bit);
                }
                Ok(Some(self.manager.mk_bv_concat(ext, arg)))
            }
            "rotate_left" | "rotate_right" => {
                let raw = single_index(index_parts)?;
                let arg = single_arg(args)?;
                let width = self.bv_width(arg).ok_or_else(|| OxizError::ParseError {
                    position: 0,
                    message: format!("{name} requires a bit-vector argument"),
                })?;
                if width == 0 {
                    return Ok(Some(arg));
                }
                // Effective left-rotation amount in 0..width.
                let amount = if name == "rotate_left" {
                    raw % width
                } else {
                    (width - (raw % width)) % width
                };
                if amount == 0 {
                    return Ok(Some(arg));
                }
                // rol(x, a) = concat(x[width-1-a : 0], x[width-1 : width-a]).
                let low = self.manager.mk_bv_extract(width - 1 - amount, 0, arg);
                let high = self.manager.mk_bv_extract(width - 1, width - amount, arg);
                Ok(Some(self.manager.mk_bv_concat(low, high)))
            }
            "repeat" => {
                let n = single_index(index_parts)?;
                let arg = single_arg(args)?;
                if n == 0 {
                    return Err(OxizError::ParseError {
                        position: 0,
                        message: "(_ repeat 0 ...) is not a valid bit-vector".to_string(),
                    });
                }
                let mut result = arg;
                for _ in 1..n {
                    result = self.manager.mk_bv_concat(result, arg);
                }
                Ok(Some(result))
            }
            "divisible" => {
                // ((_ divisible n) x) <=> (= (mod x n) 0).
                if index_parts.len() != 1 {
                    return Err(OxizError::ParseError {
                        position: 0,
                        message: format!(
                            "(_ divisible ...) requires exactly 1 index, got {}",
                            index_parts.len()
                        ),
                    });
                }
                let arg = single_arg(args)?;
                let n: BigInt = index_parts[0].parse().map_err(|_| OxizError::ParseError {
                    position: 0,
                    message: format!("invalid divisor for divisible: {}", index_parts[0]),
                })?;
                let divisor = self.manager.mk_int(n);
                let modulo = self.manager.mk_mod(arg, divisor);
                let zero = self.manager.mk_int(0);
                Ok(Some(self.manager.mk_eq(modulo, zero)))
            }
            _ => Ok(None),
        }
    }

    /// Parse an indexed floating-point conversion operator whose first
    /// argument is a `RoundingMode` symbol.
    ///
    /// SMT-LIB defines four such operators:
    /// - `(_ to_fp e s)` — convert a `FloatingPoint`, `Real`, or signed
    ///   `BitVec` source into `FloatingPoint(e, s)`. The source sort selects
    ///   the concrete conversion (`mk_fp_to_fp` / `mk_real_to_fp` /
    ///   `mk_sbv_to_fp`).
    /// - `(_ to_fp_unsigned e s)` — convert an *unsigned* `BitVec` source
    ///   into `FloatingPoint(e, s)` via `mk_ubv_to_fp`.
    /// - `(_ fp.to_sbv w)` — convert a `FloatingPoint` into a signed
    ///   `BitVec` of width `w` via `mk_fp_to_sbv`.
    /// - `(_ fp.to_ubv w)` — convert a `FloatingPoint` into an unsigned
    ///   `BitVec` of width `w` via `mk_fp_to_ubv`.
    ///
    /// All four take the form `((_ <name> <indices...>) <RM> <arg>)`, where
    /// `<RM>` is one of `RNE`/`RNA`/`RTP`/`RTN`/`RTZ`. Without this helper
    /// the bare `RNE` argument would fall through to the generic
    /// indexed-operator path, which would try to parse it as an ordinary
    /// term and reject it as an undeclared symbol (see the audit finding
    /// that prompted this helper).
    ///
    /// Returns `Ok(Some(term))` when `name` matches one of the four FP
    /// conversion operators, consuming the rounding mode, the source term,
    /// and the closing `)` of the surrounding application. Returns
    /// `Ok(None)` for any other `name`, leaving the lexer position
    /// unchanged so the caller can fall through to the generic path.
    fn parse_indexed_fp_conversion(
        &mut self,
        name: &str,
        index_parts: &[String],
    ) -> Result<Option<TermId>> {
        // (eb, sb) for the `to_fp` family; `width` for the `fp.to_*bv` family.
        let (eb, sb, width): (u32, u32, u32) = match name {
            "to_fp" | "to_fp_unsigned" => {
                if index_parts.len() != 2 {
                    return Err(OxizError::ParseError {
                        position: self.lexer.position(),
                        message: format!(
                            "(_ {name} ...) requires exactly 2 indices (eb sb), got {}",
                            index_parts.len()
                        ),
                    });
                }
                let eb: u32 = index_parts[0].parse().map_err(|_| OxizError::ParseError {
                    position: self.lexer.position(),
                    message: format!(
                        "invalid exponent width for (_ {name} ...): {}",
                        index_parts[0]
                    ),
                })?;
                let sb: u32 = index_parts[1].parse().map_err(|_| OxizError::ParseError {
                    position: self.lexer.position(),
                    message: format!(
                        "invalid significand width for (_ {name} ...): {}",
                        index_parts[1]
                    ),
                })?;
                (eb, sb, 0)
            }
            "fp.to_sbv" | "fp.to_ubv" => {
                if index_parts.len() != 1 {
                    return Err(OxizError::ParseError {
                        position: self.lexer.position(),
                        message: format!(
                            "(_ {name} ...) requires exactly 1 index (width), got {}",
                            index_parts.len()
                        ),
                    });
                }
                let w: u32 = index_parts[0].parse().map_err(|_| OxizError::ParseError {
                    position: self.lexer.position(),
                    message: format!(
                        "invalid bit-vector width for (_ {name} ...): {}",
                        index_parts[0]
                    ),
                })?;
                (0, 0, w)
            }
            _ => return Ok(None),
        };

        // First argument is always a RoundingMode symbol; parse it before
        // the source term so the bare `RNE`/`RTN`/etc. is not mistaken for
        // an undeclared constant.
        let rm: RoundingMode = self.parse_rounding_mode()?;
        let arg = self.parse_term()?;
        self.expect_rparen()?; // close the surrounding application

        let result = match name {
            "to_fp" => {
                // Dispatch on the source sort. SMT-LIB `(_ to_fp e s)` is
                // overloaded across FloatingPoint / Real / signed-BitVec;
                // integers are accepted by coercing through Real, matching
                // how the printer emits Real->FP using the same `to_fp`
                // syntax.
                let src_kind = self
                    .manager
                    .get(arg)
                    .and_then(|t| self.manager.sorts.get(t.sort))
                    .map(|s| s.kind.clone());
                match src_kind {
                    Some(SortKind::FloatingPoint { .. }) => {
                        self.manager.mk_fp_to_fp(rm, arg, eb, sb)
                    }
                    Some(SortKind::Real) | Some(SortKind::Int) => {
                        self.manager.mk_real_to_fp(rm, arg, eb, sb)
                    }
                    Some(SortKind::BitVec(_)) => self.manager.mk_sbv_to_fp(rm, arg, eb, sb),
                    _ => {
                        // Unknown / uninterpreted source sort: lower to an
                        // uninterpreted apply with the correct result sort,
                        // rather than silently producing a Bool-sorted term.
                        let func = format!("(_ to_fp {eb} {sb})");
                        let sort = self.manager.sorts.float_sort(eb, sb);
                        self.manager.mk_apply(&func, std::iter::once(arg), sort)
                    }
                }
            }
            "to_fp_unsigned" => self.manager.mk_ubv_to_fp(rm, arg, eb, sb),
            "fp.to_sbv" => self.manager.mk_fp_to_sbv(rm, arg, width),
            "fp.to_ubv" => self.manager.mk_fp_to_ubv(rm, arg, width),
            _ => unreachable!("guarded by the match above"),
        };
        Ok(Some(result))
    }

    pub(super) fn parse_compound_term(&mut self) -> Result<TermId> {
        let op_token = self
            .lexer
            .next_token()
            .ok_or_else(|| OxizError::ParseError {
                position: self.lexer.position(),
                message: "unexpected end of input".to_string(),
            })?;

        // Handle indexed identifiers that start with `(`: ((_ to_fp 8 24) RNE 1.5)
        // or qualified identifiers: ((as const (Array Int Int)) 0)
        if matches!(op_token.kind, TokenKind::LParen) {
            // Peek at the next symbol to determine what kind of compound operator this is
            let qualifier = self.expect_symbol()?;
            if qualifier == "as" {
                // SMT-LIB qualified identifier: (as <symbol> <sort>)
                // Consumes: symbol, sort, closing ')'
                let symbol = self.expect_symbol()?;
                let sort = self.parse_sort()?;
                self.expect_rparen()?; // Close the (as ...) form
                // Now parse arguments for the qualified function application
                let args = self.parse_term_list()?;
                // Build a qualified apply node with the annotated sort
                // For known forms like (as const (Array D R)), we represent this
                // as an Apply node with function name "(as const)" and the proper sort.
                let func_name = format!("(as {symbol})");
                return Ok(self.manager.mk_apply(&func_name, args, sort));
            }
            if qualifier != "_" {
                return Err(OxizError::ParseError {
                    position: self.lexer.position(),
                    message: format!(
                        "expected '_' or 'as' in compound operator, found '{qualifier}'"
                    ),
                });
            }

            let name = self.expect_symbol()?;

            // Parse indices (can be numerals or symbols, depending on the operation)
            let mut index_parts = Vec::new();
            loop {
                if let Some(token) = self.lexer.peek() {
                    match &token.kind {
                        TokenKind::RParen => {
                            self.lexer.next_token(); // consume rparen
                            break;
                        }
                        TokenKind::Numeral(n) => {
                            let n = n.clone();
                            self.lexer.next_token();
                            index_parts.push(n);
                        }
                        TokenKind::Symbol(s) => {
                            // For datatype testers like (_ is nil), the constructor name is a symbol
                            let s = s.clone();
                            self.lexer.next_token();
                            index_parts.push(s);
                        }
                        _ => {
                            return Err(OxizError::ParseError {
                                position: token.start,
                                message: format!(
                                    "expected numeral, symbol, or ')' in indexed identifier, found {:?}",
                                    token.kind
                                ),
                            });
                        }
                    }
                } else {
                    break;
                }
            }

            // Handle special indexed operators
            if name == "is" {
                // Handle datatype tester: ((_ is constructor) arg)
                if index_parts.len() != 1 {
                    return Err(OxizError::ParseError {
                        position: self.lexer.position(),
                        message: format!(
                            "(_ is) requires exactly 1 constructor name, got {}",
                            index_parts.len()
                        ),
                    });
                }
                let constructor_name = &index_parts[0];
                let arg = self.parse_term()?;
                self.expect_rparen()?; // Close the outer application
                return Ok(self.manager.mk_dt_tester(constructor_name, arg));
            }

            // Parse arguments first so indexed operators with real handling
            // (BV extend/rotate/repeat, divisible) can be lowered to concrete
            // terms instead of degrading to a Bool-sorted uninterpreted apply.
            //
            // FP conversion operators (`to_fp`, `to_fp_unsigned`,
            // `fp.to_sbv`, `fp.to_ubv`) are special-cased first because their
            // first argument is a RoundingMode symbol, not a term, so the
            // generic `parse_term_list` below would reject `RNE`/`RTN`/etc.
            // as undeclared constants.
            if let Some(term) = self.parse_indexed_fp_conversion(&name, &index_parts)? {
                return Ok(term);
            }
            let args = self.parse_term_list()?;
            if let Some(term) = self.build_indexed_op(&name, &index_parts, &args)? {
                return Ok(term);
            }

            // Build the indexed identifier name for the generic fallback.
            let indices_str = index_parts.join(" ");
            let func_name = if index_parts.is_empty() {
                format!("(_ {name})")
            } else {
                format!("(_ {name} {indices_str})")
            };
            let sort = self.manager.sorts.bool_sort; // Default
            return Ok(self.manager.mk_apply(&func_name, args, sort));
        }

        // Handle indexed identifiers: (_ extract 7 4), (_ sign_extend 16), etc.
        if matches!(op_token.kind, TokenKind::Symbol(ref s) if s == "_") {
            let name = self.expect_symbol()?;

            // Parse indices (can be numerals or symbols)
            let mut indices = Vec::new();
            let mut index_parts = Vec::new();
            loop {
                if let Some(token) = self.lexer.peek() {
                    match &token.kind {
                        TokenKind::RParen => {
                            break;
                        }
                        TokenKind::Numeral(n) => {
                            let n = n.clone();
                            self.lexer.next_token();
                            let idx = n.parse::<u32>().map_err(|_| OxizError::ParseError {
                                position: token.start,
                                message: format!("invalid index: {n}"),
                            })?;
                            indices.push(idx);
                            index_parts.push(n);
                        }
                        TokenKind::Symbol(s) => {
                            // For datatype testers and similar constructs
                            let s = s.clone();
                            self.lexer.next_token();
                            index_parts.push(s);
                        }
                        _ => break,
                    }
                } else {
                    break;
                }
            }

            // Handle indexed operations
            // Check for bitvector literal: (_ bvN M) where N is the value and M is the width
            if let Some(bv_val_str) = name.strip_prefix("bv") {
                // (_ bvN M) is a bitvector literal with value N and width M
                if indices.len() != 1 {
                    return Err(OxizError::ParseError {
                        position: self.lexer.position(),
                        message: format!(
                            "bitvector literal (_ {name} ...) requires exactly 1 index (width), got {}",
                            indices.len()
                        ),
                    });
                }
                let value: i64 = bv_val_str.parse().map_err(|_| OxizError::ParseError {
                    position: self.lexer.position(),
                    message: format!("invalid bitvector literal value: {bv_val_str}"),
                })?;
                let width = indices[0];
                if width == 0 || width > 65536 {
                    return Err(OxizError::ParseError {
                        position: self.lexer.position(),
                        message: format!("invalid bitvector width: {width} (must be 1-65536)"),
                    });
                }
                // Consume the closing rparen of (_ bvN M)
                self.expect_rparen()?;
                return Ok(self.manager.mk_bitvec(value, width));
            }

            match name.as_str() {
                "extract" => {
                    if indices.len() != 2 {
                        return Err(OxizError::ParseError {
                            position: self.lexer.position(),
                            message: format!(
                                "extract requires exactly 2 indices, got {}",
                                indices.len()
                            ),
                        });
                    }
                    let arg = self.parse_term()?;
                    self.expect_rparen()?;
                    return Ok(self.manager.mk_bv_extract(indices[0], indices[1], arg));
                }
                "is" => {
                    // Handle datatype tester: (_ is constructor) arg
                    if index_parts.len() != 1 {
                        return Err(OxizError::ParseError {
                            position: self.lexer.position(),
                            message: format!(
                                "(_ is) requires exactly 1 constructor name, got {}",
                                index_parts.len()
                            ),
                        });
                    }
                    self.expect_rparen()?; // Close the (_ is X) part
                    let constructor_name = &index_parts[0];
                    let arg = self.parse_term()?;
                    self.expect_rparen()?; // Close the outer application
                    return Ok(self.manager.mk_dt_tester(constructor_name, arg));
                }
                _ => {
                    // For unrecognized indexed identifiers, expect the closing
                    // paren of the `(_ name indices)` head, then parse args.
                    self.expect_rparen()?;

                    // FP conversion operators (`to_fp`, `to_fp_unsigned`,
                    // `fp.to_sbv`, `fp.to_ubv`) take a RoundingMode symbol as
                    // their first argument, which the generic
                    // `parse_term_list` below would reject as an undeclared
                    // constant; special-case them first.
                    if let Some(term) = self.parse_indexed_fp_conversion(&name, &index_parts)? {
                        return Ok(term);
                    }

                    // Parse arguments first so indexed operators with real
                    // handling (BV extend/rotate/repeat, divisible) can be
                    // lowered to concrete terms rather than degrading to a
                    // Bool-sorted uninterpreted apply.
                    let args = self.parse_term_list()?;
                    if let Some(term) = self.build_indexed_op(&name, &index_parts, &args)? {
                        return Ok(term);
                    }

                    // Build the indexed identifier name for the generic fallback.
                    let indices_str = index_parts.join(" ");
                    let func_name = if index_parts.is_empty() {
                        format!("(_ {name})")
                    } else {
                        format!("(_ {name} {indices_str})")
                    };
                    let sort = self.manager.sorts.bool_sort; // Default
                    return Ok(self.manager.mk_apply(&func_name, args, sort));
                }
            }
        }

        let op = match &op_token.kind {
            TokenKind::Symbol(s) => s.clone(),
            TokenKind::Keyword(k) => format!(":{k}"),
            _ => {
                return Err(OxizError::ParseError {
                    position: op_token.start,
                    message: format!("expected operator, found {:?}", op_token.kind),
                });
            }
        };

        let result = match op.as_str() {
            "!" => {
                // Annotation: (! term :attr1 val1 :attr2 val2 ...)
                let term = self.parse_term()?;
                let attrs = self.parse_attributes()?;
                self.expect_rparen()?;

                // Store annotations for this term
                if !attrs.is_empty() {
                    self.annotations.insert(term, attrs);
                }

                term
            }
            "not" => {
                let arg = self.parse_term()?;
                self.expect_rparen()?;
                self.manager.mk_not(arg)
            }
            "and" => {
                let args = self.parse_term_list()?;
                self.manager.mk_and(args)
            }
            "or" => {
                let args = self.parse_term_list()?;
                self.manager.mk_or(args)
            }
            "=>" => {
                // `=>` is right-associative n-ary in SMT-LIB:
                // `(=> a b c)` means `(=> a (=> b c))`. Parse the first operand
                // directly (recursion-friendly), collect the rest, then fold
                // from the right.
                let first = self.parse_term()?;
                let mut rest = Vec::new();
                while !self.try_consume_rparen() {
                    rest.push(self.parse_term()?);
                }
                if rest.is_empty() {
                    return Err(self.min_arity_err("=>", 2, 1));
                }
                let mut result = rest[rest.len() - 1];
                for &lhs in rest[..rest.len() - 1].iter().rev() {
                    result = self.manager.mk_implies(lhs, result);
                }
                self.manager.mk_implies(first, result)
            }
            "xor" => {
                // `xor` is left-associative n-ary in SMT-LIB:
                // `(xor a b c)` means `(xor (xor a b) c)`.
                let first = self.parse_term()?;
                let mut result = first;
                let mut count = 1usize;
                while !self.try_consume_rparen() {
                    let next = self.parse_term()?;
                    result = self.mk_xor2(result, next);
                    count += 1;
                }
                if count < 2 {
                    return Err(self.min_arity_err("xor", 2, count));
                }
                result
            }
            "ite" => {
                let cond = self.parse_term()?;
                let then_branch = self.parse_term()?;
                let else_branch = self.parse_term()?;
                self.expect_rparen()?;
                self.manager.mk_ite(cond, then_branch, else_branch)
            }
            "=" => {
                // `=` is chainable: `(= a b c)` means `(and (= a b) (= b c))`.
                let first = self.parse_term()?;
                let mut prev = first;
                let mut atoms: Vec<TermId> = Vec::new();
                while !self.try_consume_rparen() {
                    let next = self.parse_term()?;
                    atoms.push(self.manager.mk_eq(prev, next));
                    prev = next;
                }
                if atoms.is_empty() {
                    return Err(self.min_arity_err("=", 2, 1));
                }
                self.chain_conjunction(atoms)
            }
            "distinct" => {
                let args = self.parse_term_list()?;
                self.manager.mk_distinct(args)
            }
            "+" => {
                let args = self.parse_term_list()?;
                self.manager.mk_add(args)
            }
            "-" => {
                // `-` is unary negation with one operand and left-associative
                // n-ary subtraction otherwise: `(- a b c)` means `(- (- a b) c)`.
                let first = self.parse_term()?;
                if self.try_consume_rparen() {
                    // Unary minus - use mk_neg for proper negation.
                    return Ok(self.manager.mk_neg(first));
                }
                let mut result = first;
                while !self.try_consume_rparen() {
                    let next = self.parse_term()?;
                    result = self.manager.mk_sub(result, next);
                }
                result
            }
            "*" => {
                let args = self.parse_term_list()?;
                self.manager.mk_mul(args)
            }
            "div" => {
                // Integer (Euclidean) division. `div`/`mod` are left-
                // associative n-ary in SMT-LIB; fold left over the operands.
                let mut result = self.parse_term()?;
                loop {
                    if let Some(token) = self.lexer.peek()
                        && matches!(token.kind, TokenKind::RParen)
                    {
                        self.lexer.next_token();
                        break;
                    }
                    let next = self.parse_term()?;
                    result = self.manager.mk_div(result, next);
                }
                result
            }
            "mod" => {
                let lhs = self.parse_term()?;
                let rhs = self.parse_term()?;
                self.expect_rparen()?;
                self.manager.mk_mod(lhs, rhs)
            }
            "/" => {
                // Real division. Left-associative n-ary. Routed to the general
                // division term kind (which the rewriter/evaluator interpret as
                // exact rational division) so QF_LRA constraints stay in the
                // arithmetic theory instead of degrading to a Bool apply.
                let mut result = self.parse_term()?;
                loop {
                    if let Some(token) = self.lexer.peek()
                        && matches!(token.kind, TokenKind::RParen)
                    {
                        self.lexer.next_token();
                        break;
                    }
                    let next = self.parse_term()?;
                    result = self.manager.mk_div(result, next);
                }
                result
            }
            "abs" => {
                // (abs x) = (ite (>= x 0) x (- x)), with the zero literal typed
                // to match the operand sort so mixed Int/Real reasoning stays
                // consistent.
                let arg = self.parse_term()?;
                self.expect_rparen()?;
                let zero = if self.is_real_term(arg) {
                    self.manager.mk_real(Rational64::from_integer(0))
                } else {
                    self.manager.mk_int(0)
                };
                let cond = self.manager.mk_ge(arg, zero);
                let neg = self.manager.mk_neg(arg);
                self.manager.mk_ite(cond, arg, neg)
            }
            "to_real" => {
                // Int -> Real injection. The arithmetic engine represents both
                // sorts as rationals and the value is preserved exactly, so the
                // injection is the identity on the term; the operand keeps its
                // (integer) constraints, which is exactly `to_real` semantics.
                let arg = self.parse_term()?;
                self.expect_rparen()?;
                arg
            }
            "to_int" => {
                // (to_int r) is the floor of a real. For a *constant* operand
                // we can compute the exact Euclidean floor
                // (`numer.div_euclid(denom)`, denom always positive in a
                // normalized rational); an already-integer constant maps to
                // itself. For a *symbolic* real there is no floor operator in
                // this term representation, so rather than emit a silently
                // wrong term we surface an honest parse error.
                let arg = self.parse_term()?;
                self.expect_rparen()?;
                let kind = self.manager.get(arg).map(|t| t.kind.clone());
                match kind {
                    Some(crate::ast::TermKind::IntConst(_)) => arg,
                    Some(crate::ast::TermKind::RealConst(r)) => {
                        let floor = r.numer().div_euclid(*r.denom());
                        self.manager.mk_int(floor)
                    }
                    _ => {
                        return Err(OxizError::ParseError {
                            position: self.lexer.position(),
                            message: "unsupported to_int on a symbolic real (no floor operator)"
                                .to_string(),
                        });
                    }
                }
            }
            "is_int" => {
                // (is_int r) tests whether a real is integer-valued. For a
                // constant operand this is decidable exactly; for a symbolic
                // real we have no integrality predicate to lower to, so we
                // surface an honest parse error instead of a wrong term.
                let arg = self.parse_term()?;
                self.expect_rparen()?;
                let kind = self.manager.get(arg).map(|t| t.kind.clone());
                match kind {
                    Some(crate::ast::TermKind::IntConst(_)) => self.manager.mk_true(),
                    Some(crate::ast::TermKind::RealConst(r)) => {
                        if r.is_integer() {
                            self.manager.mk_true()
                        } else {
                            self.manager.mk_false()
                        }
                    }
                    _ => {
                        return Err(OxizError::ParseError {
                            position: self.lexer.position(),
                            message:
                                "unsupported is_int on a symbolic real (no integrality predicate)"
                                    .to_string(),
                        });
                    }
                }
            }
            "<" => {
                // Chainable: `(< a b c)` means `(and (< a b) (< b c))`.
                let first = self.parse_term()?;
                let mut prev = first;
                let mut atoms: Vec<TermId> = Vec::new();
                while !self.try_consume_rparen() {
                    let next = self.parse_term()?;
                    atoms.push(self.manager.mk_lt(prev, next));
                    prev = next;
                }
                if atoms.is_empty() {
                    return Err(self.min_arity_err("<", 2, 1));
                }
                self.chain_conjunction(atoms)
            }
            "<=" => {
                // Chainable: `(<= a b c)` means `(and (<= a b) (<= b c))`.
                let first = self.parse_term()?;
                let mut prev = first;
                let mut atoms: Vec<TermId> = Vec::new();
                while !self.try_consume_rparen() {
                    let next = self.parse_term()?;
                    atoms.push(self.manager.mk_le(prev, next));
                    prev = next;
                }
                if atoms.is_empty() {
                    return Err(self.min_arity_err("<=", 2, 1));
                }
                self.chain_conjunction(atoms)
            }
            ">" => {
                // Chainable: `(> a b c)` means `(and (> a b) (> b c))`.
                let first = self.parse_term()?;
                let mut prev = first;
                let mut atoms: Vec<TermId> = Vec::new();
                while !self.try_consume_rparen() {
                    let next = self.parse_term()?;
                    atoms.push(self.manager.mk_gt(prev, next));
                    prev = next;
                }
                if atoms.is_empty() {
                    return Err(self.min_arity_err(">", 2, 1));
                }
                self.chain_conjunction(atoms)
            }
            ">=" => {
                // Chainable: `(>= a b c)` means `(and (>= a b) (>= b c))`.
                let first = self.parse_term()?;
                let mut prev = first;
                let mut atoms: Vec<TermId> = Vec::new();
                while !self.try_consume_rparen() {
                    let next = self.parse_term()?;
                    atoms.push(self.manager.mk_ge(prev, next));
                    prev = next;
                }
                if atoms.is_empty() {
                    return Err(self.min_arity_err(">=", 2, 1));
                }
                self.chain_conjunction(atoms)
            }
            "select" => {
                let array = self.parse_term()?;
                let index = self.parse_term()?;
                self.expect_rparen()?;
                self.manager.mk_select(array, index)
            }
            "store" => {
                let array = self.parse_term()?;
                let index = self.parse_term()?;
                let value = self.parse_term()?;
                self.expect_rparen()?;
                self.manager.mk_store(array, index, value)
            }
            "let" => self.parse_let()?,
            "forall" => self.parse_forall()?,
            "exists" => self.parse_exists()?,
            // BitVector operations
            "bvnot" => {
                let arg = self.parse_term()?;
                self.expect_rparen()?;
                self.manager.mk_bv_not(arg)
            }
            "bvand" => {
                let lhs = self.parse_term()?;
                let rhs = self.parse_term()?;
                self.expect_rparen()?;
                self.manager.mk_bv_and(lhs, rhs)
            }
            "bvor" => {
                let lhs = self.parse_term()?;
                let rhs = self.parse_term()?;
                self.expect_rparen()?;
                self.manager.mk_bv_or(lhs, rhs)
            }
            "bvadd" => {
                let lhs = self.parse_term()?;
                let rhs = self.parse_term()?;
                self.expect_rparen()?;
                self.manager.mk_bv_add(lhs, rhs)
            }
            "bvsub" => {
                let lhs = self.parse_term()?;
                let rhs = self.parse_term()?;
                self.expect_rparen()?;
                self.manager.mk_bv_sub(lhs, rhs)
            }
            "bvmul" => {
                let lhs = self.parse_term()?;
                let rhs = self.parse_term()?;
                self.expect_rparen()?;
                self.manager.mk_bv_mul(lhs, rhs)
            }
            "bvult" => {
                let lhs = self.parse_term()?;
                let rhs = self.parse_term()?;
                self.expect_rparen()?;
                self.manager.mk_bv_ult(lhs, rhs)
            }
            "bvslt" => {
                let lhs = self.parse_term()?;
                let rhs = self.parse_term()?;
                self.expect_rparen()?;
                self.manager.mk_bv_slt(lhs, rhs)
            }
            "bvule" => {
                let lhs = self.parse_term()?;
                let rhs = self.parse_term()?;
                self.expect_rparen()?;
                self.manager.mk_bv_ule(lhs, rhs)
            }
            "bvsle" => {
                let lhs = self.parse_term()?;
                let rhs = self.parse_term()?;
                self.expect_rparen()?;
                self.manager.mk_bv_sle(lhs, rhs)
            }
            "bvugt" => {
                // bvugt(a, b) = bvult(b, a)
                let lhs = self.parse_term()?;
                let rhs = self.parse_term()?;
                self.expect_rparen()?;
                self.manager.mk_bv_ult(rhs, lhs)
            }
            "bvsgt" => {
                // bvsgt(a, b) = bvslt(b, a)
                let lhs = self.parse_term()?;
                let rhs = self.parse_term()?;
                self.expect_rparen()?;
                self.manager.mk_bv_slt(rhs, lhs)
            }
            "bvuge" => {
                // bvuge(a, b) = NOT bvult(a, b)
                let lhs = self.parse_term()?;
                let rhs = self.parse_term()?;
                self.expect_rparen()?;
                let ult = self.manager.mk_bv_ult(lhs, rhs);
                self.manager.mk_not(ult)
            }
            "bvsge" => {
                // bvsge(a, b) = NOT bvslt(a, b)
                let lhs = self.parse_term()?;
                let rhs = self.parse_term()?;
                self.expect_rparen()?;
                let slt = self.manager.mk_bv_slt(lhs, rhs);
                self.manager.mk_not(slt)
            }
            "bvxor" => {
                let lhs = self.parse_term()?;
                let rhs = self.parse_term()?;
                self.expect_rparen()?;
                self.manager.mk_bv_xor(lhs, rhs)
            }
            "bvudiv" => {
                let lhs = self.parse_term()?;
                let rhs = self.parse_term()?;
                self.expect_rparen()?;
                self.manager.mk_bv_udiv(lhs, rhs)
            }
            "bvsdiv" => {
                let lhs = self.parse_term()?;
                let rhs = self.parse_term()?;
                self.expect_rparen()?;
                self.manager.mk_bv_sdiv(lhs, rhs)
            }
            "bvurem" => {
                let lhs = self.parse_term()?;
                let rhs = self.parse_term()?;
                self.expect_rparen()?;
                self.manager.mk_bv_urem(lhs, rhs)
            }
            "bvsrem" => {
                let lhs = self.parse_term()?;
                let rhs = self.parse_term()?;
                self.expect_rparen()?;
                self.manager.mk_bv_srem(lhs, rhs)
            }
            "bvshl" => {
                let lhs = self.parse_term()?;
                let rhs = self.parse_term()?;
                self.expect_rparen()?;
                self.manager.mk_bv_shl(lhs, rhs)
            }
            "bvlshr" => {
                let lhs = self.parse_term()?;
                let rhs = self.parse_term()?;
                self.expect_rparen()?;
                self.manager.mk_bv_lshr(lhs, rhs)
            }
            "bvashr" => {
                let lhs = self.parse_term()?;
                let rhs = self.parse_term()?;
                self.expect_rparen()?;
                self.manager.mk_bv_ashr(lhs, rhs)
            }
            "concat" => {
                let lhs = self.parse_term()?;
                let rhs = self.parse_term()?;
                self.expect_rparen()?;
                self.manager.mk_bv_concat(lhs, rhs)
            }
            // Floating-point arithmetic operations (take rounding mode as first argument)
            "fp.add" => {
                let rm = self.parse_rounding_mode()?;
                let lhs = self.parse_term()?;
                let rhs = self.parse_term()?;
                self.expect_rparen()?;
                self.manager.mk_fp_add(rm, lhs, rhs)
            }
            "fp.sub" => {
                let rm = self.parse_rounding_mode()?;
                let lhs = self.parse_term()?;
                let rhs = self.parse_term()?;
                self.expect_rparen()?;
                self.manager.mk_fp_sub(rm, lhs, rhs)
            }
            "fp.mul" => {
                let rm = self.parse_rounding_mode()?;
                let lhs = self.parse_term()?;
                let rhs = self.parse_term()?;
                self.expect_rparen()?;
                self.manager.mk_fp_mul(rm, lhs, rhs)
            }
            "fp.div" => {
                let rm = self.parse_rounding_mode()?;
                let lhs = self.parse_term()?;
                let rhs = self.parse_term()?;
                self.expect_rparen()?;
                self.manager.mk_fp_div(rm, lhs, rhs)
            }
            "fp.rem" => {
                let lhs = self.parse_term()?;
                let rhs = self.parse_term()?;
                self.expect_rparen()?;
                self.manager.mk_fp_rem(lhs, rhs)
            }
            "fp.sqrt" => {
                let rm = self.parse_rounding_mode()?;
                let arg = self.parse_term()?;
                self.expect_rparen()?;
                self.manager.mk_fp_sqrt(rm, arg)
            }
            "fp.fma" => {
                let rm = self.parse_rounding_mode()?;
                let x = self.parse_term()?;
                let y = self.parse_term()?;
                let z = self.parse_term()?;
                self.expect_rparen()?;
                self.manager.mk_fp_fma(rm, x, y, z)
            }
            "fp.roundToIntegral" => {
                let rm = self.parse_rounding_mode()?;
                let arg = self.parse_term()?;
                self.expect_rparen()?;
                self.manager.mk_fp_round_to_integral(rm, arg)
            }
            // Floating-point comparisons
            "fp.eq" => {
                let lhs = self.parse_term()?;
                let rhs = self.parse_term()?;
                self.expect_rparen()?;
                self.manager.mk_fp_eq(lhs, rhs)
            }
            "fp.lt" => {
                let lhs = self.parse_term()?;
                let rhs = self.parse_term()?;
                self.expect_rparen()?;
                self.manager.mk_fp_lt(lhs, rhs)
            }
            "fp.gt" => {
                let lhs = self.parse_term()?;
                let rhs = self.parse_term()?;
                self.expect_rparen()?;
                self.manager.mk_fp_gt(lhs, rhs)
            }
            "fp.leq" => {
                let lhs = self.parse_term()?;
                let rhs = self.parse_term()?;
                self.expect_rparen()?;
                self.manager.mk_fp_leq(lhs, rhs)
            }
            "fp.geq" => {
                let lhs = self.parse_term()?;
                let rhs = self.parse_term()?;
                self.expect_rparen()?;
                self.manager.mk_fp_geq(lhs, rhs)
            }
            // Floating-point predicates
            "fp.isNormal" => {
                let arg = self.parse_term()?;
                self.expect_rparen()?;
                self.manager.mk_fp_is_normal(arg)
            }
            "fp.isSubnormal" => {
                let arg = self.parse_term()?;
                self.expect_rparen()?;
                self.manager.mk_fp_is_subnormal(arg)
            }
            "fp.isZero" => {
                let arg = self.parse_term()?;
                self.expect_rparen()?;
                self.manager.mk_fp_is_zero(arg)
            }
            "fp.isInfinite" => {
                let arg = self.parse_term()?;
                self.expect_rparen()?;
                self.manager.mk_fp_is_infinite(arg)
            }
            "fp.isNaN" => {
                let arg = self.parse_term()?;
                self.expect_rparen()?;
                self.manager.mk_fp_is_nan(arg)
            }
            "fp.isNegative" => {
                let arg = self.parse_term()?;
                self.expect_rparen()?;
                self.manager.mk_fp_is_negative(arg)
            }
            "fp.isPositive" => {
                let arg = self.parse_term()?;
                self.expect_rparen()?;
                self.manager.mk_fp_is_positive(arg)
            }
            // Floating-point unary operations
            "fp.abs" => {
                let arg = self.parse_term()?;
                self.expect_rparen()?;
                self.manager.mk_fp_abs(arg)
            }
            "fp.neg" => {
                let arg = self.parse_term()?;
                self.expect_rparen()?;
                self.manager.mk_fp_neg(arg)
            }
            // Floating-point binary min/max
            "fp.min" => {
                let lhs = self.parse_term()?;
                let rhs = self.parse_term()?;
                self.expect_rparen()?;
                self.manager.mk_fp_min(lhs, rhs)
            }
            "fp.max" => {
                let lhs = self.parse_term()?;
                let rhs = self.parse_term()?;
                self.expect_rparen()?;
                self.manager.mk_fp_max(lhs, rhs)
            }
            // String operations
            "str.++" => {
                let mut result = self.parse_term()?;
                loop {
                    if let Some(token) = self.lexer.peek()
                        && matches!(token.kind, TokenKind::RParen)
                    {
                        self.lexer.next_token();
                        break;
                    }
                    let next = self.parse_term()?;
                    result = self.manager.mk_str_concat(result, next);
                }
                result
            }
            "str.len" => {
                let arg = self.parse_term()?;
                self.expect_rparen()?;
                self.manager.mk_str_len(arg)
            }
            "str.substr" => {
                let s = self.parse_term()?;
                let start = self.parse_term()?;
                let len = self.parse_term()?;
                self.expect_rparen()?;
                self.manager.mk_str_substr(s, start, len)
            }
            "str.at" => {
                let s = self.parse_term()?;
                let i = self.parse_term()?;
                self.expect_rparen()?;
                self.manager.mk_str_at(s, i)
            }
            "str.contains" => {
                let s = self.parse_term()?;
                let sub = self.parse_term()?;
                self.expect_rparen()?;
                self.manager.mk_str_contains(s, sub)
            }
            "str.prefixof" => {
                let prefix = self.parse_term()?;
                let s = self.parse_term()?;
                self.expect_rparen()?;
                self.manager.mk_str_prefixof(prefix, s)
            }
            "str.suffixof" => {
                let suffix = self.parse_term()?;
                let s = self.parse_term()?;
                self.expect_rparen()?;
                self.manager.mk_str_suffixof(suffix, s)
            }
            "str.indexof" => {
                let s = self.parse_term()?;
                let sub = self.parse_term()?;
                let offset = self.parse_term()?;
                self.expect_rparen()?;
                self.manager.mk_str_indexof(s, sub, offset)
            }
            "str.replace" => {
                let s = self.parse_term()?;
                let pattern = self.parse_term()?;
                let replacement = self.parse_term()?;
                self.expect_rparen()?;
                self.manager.mk_str_replace(s, pattern, replacement)
            }
            "str.replace_all" => {
                let s = self.parse_term()?;
                let pattern = self.parse_term()?;
                let replacement = self.parse_term()?;
                self.expect_rparen()?;
                self.manager.mk_str_replace_all(s, pattern, replacement)
            }
            "str.to_int" | "str.to.int" => {
                let s = self.parse_term()?;
                self.expect_rparen()?;
                self.manager.mk_str_to_int(s)
            }
            "int.to_str" | "int.to.str" | "str.from_int" => {
                let n = self.parse_term()?;
                self.expect_rparen()?;
                self.manager.mk_int_to_str(n)
            }
            "str.in_re" | "str.in.re" => {
                let s = self.parse_term()?;
                let re = self.parse_term()?;
                self.expect_rparen()?;
                self.manager.mk_str_in_re(s, re)
            }
            _ => {
                // Check for defined function
                if let Some((params, body)) = self.function_defs.get(&op).cloned() {
                    // Parse arguments
                    let args = self.parse_term_list()?;

                    if args.len() != params.len() {
                        return Err(OxizError::ParseError {
                            position: 0,
                            message: format!(
                                "wrong number of arguments for {}: expected {}, got {}",
                                op,
                                params.len(),
                                args.len()
                            ),
                        });
                    }

                    // Substitute arguments into the body
                    let mut substitution = FxHashMap::default();
                    for ((param_name, _param_sort), &arg) in params.iter().zip(args.iter()) {
                        // Find the parameter variable in the body
                        let param_sort = self
                            .constants
                            .get(param_name)
                            .copied()
                            .unwrap_or(self.manager.sorts.bool_sort);
                        let param_var = self.manager.mk_var(param_name, param_sort);
                        substitution.insert(param_var, arg);
                    }

                    // Apply substitution to get the result
                    self.manager.substitute(body, &substitution)
                } else {
                    // Regular function application.
                    //
                    // Look up the declared return sort from the functions table so
                    // that the Apply node carries the correct sort (e.g. `Int` for
                    // `(declare-fun f (Int) Int)` applications).  This is essential
                    // for theory reasoning: without the correct sort, an expression
                    // like `(> (f k) 10)` would be created with `f(k)` having
                    // `Bool` sort, causing the arithmetic theory to ignore it.
                    let args = self.parse_term_list()?;
                    let sort = self
                        .functions
                        .get(&op)
                        .map(|(_, ret)| *ret)
                        .unwrap_or(self.manager.sorts.bool_sort);
                    self.manager.mk_apply(&op, args, sort)
                }
            }
        };

        Ok(result)
    }

    pub(super) fn parse_term_list(&mut self) -> Result<SmallVec<[TermId; 4]>> {
        let mut args = SmallVec::new();
        loop {
            if let Some(token) = self.lexer.peek()
                && matches!(token.kind, TokenKind::RParen)
            {
                self.lexer.next_token();
                break;
            }
            args.push(self.parse_term()?);
        }
        Ok(args)
    }

    /// Parse attributes in an annotation
    pub(super) fn parse_attributes(&mut self) -> Result<Vec<Attribute>> {
        let mut attrs = Vec::new();

        loop {
            // Check if we've reached the closing paren
            if let Some(token) = self.lexer.peek() {
                if matches!(token.kind, TokenKind::RParen) {
                    break;
                }

                // Attributes start with a keyword (e.g., :named, :pattern)
                if let TokenKind::Keyword(key) = &token.kind {
                    let key = key.clone();
                    self.lexer.next_token(); // consume the keyword

                    // Try to parse the attribute value
                    let value = if let Some(next_token) = self.lexer.peek() {
                        match &next_token.kind {
                            // If next is a keyword or rparen, this attribute has no value
                            TokenKind::Keyword(_) | TokenKind::RParen => None,
                            // Otherwise, parse the value
                            _ => Some(self.parse_attribute_value()?),
                        }
                    } else {
                        None
                    };

                    attrs.push(Attribute { key, value });
                } else {
                    return Err(OxizError::ParseError {
                        position: token.start,
                        message: format!("expected keyword in annotation, found {:?}", token.kind),
                    });
                }
            } else {
                return Err(OxizError::ParseError {
                    position: self.lexer.position(),
                    message: "unexpected end of input in annotation".to_string(),
                });
            }
        }

        Ok(attrs)
    }

    /// Parse an attribute value
    pub(super) fn parse_attribute_value(&mut self) -> Result<super::AttributeValue> {
        let token = self.lexer.peek().ok_or_else(|| OxizError::ParseError {
            position: self.lexer.position(),
            message: "unexpected end of input in attribute value".to_string(),
        })?;

        match &token.kind {
            TokenKind::Symbol(s) => {
                let s = s.clone();
                self.lexer.next_token();
                Ok(super::AttributeValue::Symbol(s))
            }
            TokenKind::Numeral(n) => {
                let n = n.clone();
                self.lexer.next_token();
                Ok(super::AttributeValue::Numeral(n))
            }
            TokenKind::StringLit(s) => {
                let s = s.clone();
                self.lexer.next_token();
                Ok(super::AttributeValue::String(s))
            }
            TokenKind::LParen => {
                // Could be an S-expression or a term
                // For :pattern, this would be a term list
                self.lexer.next_token(); // consume lparen
                let mut values = Vec::new();

                loop {
                    if let Some(t) = self.lexer.peek()
                        && matches!(t.kind, TokenKind::RParen)
                    {
                        self.lexer.next_token();
                        break;
                    }

                    // Try to parse as term first
                    let term = self.parse_term()?;
                    values.push(super::AttributeValue::Term(term));
                }

                Ok(super::AttributeValue::SExpr(values))
            }
            _ => Err(OxizError::ParseError {
                position: token.start,
                message: format!("unexpected token in attribute value: {:?}", token.kind),
            }),
        }
    }
}
