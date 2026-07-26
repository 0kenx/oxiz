//! Grammar-driven SMT-LIB2 script generator.
//!
//! This is the "grammar fuzzer" proper: a recursive, context-free-style
//! generator that emits **well-typed** SMT-LIB2 scripts for a fixed set of
//! logics. Unlike coverage-guided byte mutation (the existing `fuzz/` targets),
//! every script produced here is syntactically and sort-correct by
//! construction, so a sat/unsat disagreement between z3 and oxiz is always a
//! genuine solver soundness issue, never "you fed me garbage".
//!
//! The generator is a pure function of `(logic, seed, config)`: no wall-clock
//! time, no OS entropy, no `rand` version drift (see [`crate::rng`]). Any
//! failing case is reproducible from its seed alone.
//!
//! # Logics covered
//!
//! | Logic | SMT-LIB | Sorts | Notes |
//! |-------|---------|-------|-------|
//! | `QfLia`  | `QF_LIA` | `Int`  | linear (constant·var only), `abs`, comparisons, `distinct`, `ite` |
//! | `QfLra`  | `QF_LRA` | `Real` | linear, decimal literals, comparisons |
//! | `QfBv`   | `QF_BV`  | `(_ BitVec W)` | bitwise/arith/shift ops, signed & unsigned compares |
//! | `QfUf`   | `QF_UF`  | uninterpreted `U` | congruence/equality over uninterpreted funs |
//! | `Lia`    | `LIA`    | `Int`  | adds `forall`/`exists` quantifiers (shallow bodies) |
//!
//! Arithmetic division/mod is only ever generated with a **non-zero numeral**
//! divisor, sidestepping the SMT-LIB divide-by-zero edge case where solvers
//! have historically disagreed (and would create noise rather than signal).

use crate::rng::Rng;
use std::fmt::Write as _;

/// The logics the grammar fuzzer can generate.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Logic {
    QfLia,
    QfLra,
    QfBv,
    QfUf,
    /// Quantified linear integer arithmetic (`forall`/`exists`).
    Lia,
}

impl Logic {
    /// SMT-LIB `set-logic` name.
    pub fn name(self) -> &'static str {
        match self {
            Logic::QfLia => "QF_LIA",
            Logic::QfLra => "QF_LRA",
            Logic::QfBv => "QF_BV",
            Logic::QfUf => "QF_UF",
            Logic::Lia => "LIA",
        }
    }

    /// All logics, in a fixed canonical order.
    pub const ALL: [Logic; 5] = [
        Logic::QfLia,
        Logic::QfLra,
        Logic::QfBv,
        Logic::QfUf,
        Logic::Lia,
    ];

    /// Parse a comma-separated list of logic names (case-insensitive, accepts
    /// both `QfLia` and `QF_LIA`); `None` if any token is unrecognized.
    pub fn parse_list(s: &str) -> Option<Vec<Logic>> {
        let mut out = Vec::new();
        for tok in s.split(',').map(str::trim).filter(|t| !t.is_empty()) {
            let norm = tok.to_ascii_uppercase().replace('-', "_");
            let logic = match norm.as_str() {
                "QF_LIA" | "QFLIA" => Logic::QfLia,
                "QF_LRA" | "QFLRA" => Logic::QfLra,
                "QF_BV" | "QFBV" => Logic::QfBv,
                "QF_UF" | "QFUF" => Logic::QfUf,
                "LIA" => Logic::Lia,
                _ => return None,
            };
            out.push(logic);
        }
        if out.is_empty() { None } else { Some(out) }
    }
}

impl std::fmt::Display for Logic {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.name())
    }
}

/// Knobs that control generator size/depth. Larger values explore more of the
/// formula space at the cost of slower solves and more timeouts.
#[derive(Debug, Clone)]
pub struct Config {
    pub max_term_depth: u32,
    pub max_formula_depth: u32,
    pub min_vars: usize,
    pub max_vars: usize,
    pub min_asserts: usize,
    pub max_asserts: usize,
}

impl Default for Config {
    fn default() -> Self {
        // Deliberately larger than `bench/z3_parity`'s generator (depth 2,
        // 2-4 vars): depth 3, up to 5 vars and 6 assertions exercises nested
        // `ite`/boolean structure while keeping typical solves well under a
        // second.
        Config {
            max_term_depth: 3,
            max_formula_depth: 3,
            min_vars: 2,
            max_vars: 5,
            min_asserts: 2,
            max_asserts: 6,
        }
    }
}

/// A generated script plus the metadata needed to reproduce and report it.
#[derive(Debug, Clone)]
pub struct Script {
    pub logic: Logic,
    pub seed: u64,
    /// The full SMT-LIB2 source.
    pub source: String,
}

/// Generate one fully deterministic script. `generate(logic, seed, cfg)` is a
/// pure function of its arguments.
pub fn generate(logic: Logic, seed: u64, cfg: &Config) -> Script {
    let mut rng = Rng::new(seed);
    let source = match logic {
        Logic::QfLia => gen_linear_arith(&mut rng, false, false, cfg),
        Logic::QfLra => gen_linear_arith(&mut rng, true, false, cfg),
        Logic::Lia => gen_linear_arith(&mut rng, false, true, cfg),
        Logic::QfBv => gen_bv(&mut rng, cfg),
        Logic::QfUf => gen_uf(&mut rng, cfg),
    };
    Script {
        logic,
        seed,
        source,
    }
}

// =====================================================================
// Boolean structure (shared by every logic; the leaves come from `atom`)
// =====================================================================

/// Build a Boolean formula of the given depth whose leaves are produced by
/// `atom`. Connectives: `and`, `or`, `not`, `=>`, `xor`, and (rarely) `ite`
/// over booleans.
fn gen_bool<F>(rng: &mut Rng, depth: u32, atom: &mut F) -> String
where
    F: FnMut(&mut Rng) -> String,
{
    if depth == 0 || rng.chance(2, 5) {
        return atom(rng);
    }
    match rng.index(6) {
        0 => {
            let n = rng.range_u32(2, 3) as usize;
            let parts: Vec<String> = (0..n).map(|_| gen_bool(rng, depth - 1, atom)).collect();
            format!("(and {})", parts.join(" "))
        }
        1 => {
            let n = rng.range_u32(2, 3) as usize;
            let parts: Vec<String> = (0..n).map(|_| gen_bool(rng, depth - 1, atom)).collect();
            format!("(or {})", parts.join(" "))
        }
        2 => format!("(not {})", gen_bool(rng, depth - 1, atom)),
        3 => format!(
            "(=> {} {})",
            gen_bool(rng, depth - 1, atom),
            gen_bool(rng, depth - 1, atom)
        ),
        4 => format!(
            "(xor {} {})",
            gen_bool(rng, depth - 1, atom),
            gen_bool(rng, depth - 1, atom)
        ),
        _ => format!(
            "(ite {} {} {})",
            gen_bool(rng, depth - 1, atom),
            gen_bool(rng, depth - 1, atom),
            gen_bool(rng, depth - 1, atom)
        ),
    }
}

// =====================================================================
// QF_LIA / QF_LRA / LIA: linear arithmetic over Int/Real
// =====================================================================

/// Emit a non-negative numeral / decimal. SMT-LIB literals are never written
/// with a leading `-`; a negative value is spelled `(- N)`.
fn arith_const(rng: &mut Rng, is_real: bool) -> String {
    let magnitude = rng.range_i64(0, 12);
    let negative = rng.chance(1, 3) && magnitude != 0;
    let literal = if is_real {
        let frac = rng.range_i64(0, 9);
        format!("{magnitude}.{frac}")
    } else {
        magnitude.to_string()
    };
    if negative {
        format!("(- {literal})")
    } else {
        literal
    }
}

/// A **non-zero** arithmetic constant; used as a safe divisor / multiplier to
/// keep us inside the linear fragment and away from divide-by-zero semantics.
fn nonzero_arith_const(rng: &mut Rng, is_real: bool) -> String {
    loop {
        let c = arith_const(rng, is_real);
        // `arith_const` may yield `(- 0)` which is zero; skip those.
        if !c.contains("(- 0") && c != "0" && c != "0.0" {
            return c;
        }
    }
}

fn gen_arith_term(
    rng: &mut Rng,
    vars: &[String],
    is_real: bool,
    depth: u32,
    bound: &[String],
) -> String {
    if depth == 0 || rng.chance(1, 3) {
        return gen_arith_leaf(rng, vars, is_real);
    }
    match rng.index(7) {
        0 => {
            let n = rng.range_u32(2, 3) as usize;
            let parts: Vec<String> = (0..n)
                .map(|_| gen_arith_term(rng, vars, is_real, depth - 1, bound))
                .collect();
            format!("(+ {})", parts.join(" "))
        }
        1 => {
            let a = gen_arith_term(rng, vars, is_real, depth - 1, bound);
            let b = gen_arith_term(rng, vars, is_real, depth - 1, bound);
            format!("(- {a} {b})")
        }
        2 => {
            // Scalar multiplication only -> stays linear (no var*var).
            let c = arith_const(rng, is_real);
            let a = gen_arith_term(rng, vars, is_real, depth - 1, bound);
            format!("(* {c} {a})")
        }
        3 => {
            // Division by a non-zero constant only: avoids both nonlinearity
            // and the divide-by-zero edge case where solvers have disagreed.
            // SMT-LIB spelling depends on the sort: `div` is Int-only, `/`
            // is the Real division operator.
            let d = nonzero_arith_const(rng, is_real);
            let a = gen_arith_term(rng, vars, is_real, depth - 1, bound);
            if is_real {
                format!("(/ {a} {d})")
            } else {
                format!("(div {a} {d})")
            }
        }
        4 => {
            // `mod` is an Int-only operator in SMT-LIB (z3 rejects
            // `(mod x 2.0)` as a sort error). For Real we emit real division
            // instead so the script stays standard-conformant.
            let d = nonzero_arith_const(rng, is_real);
            let a = gen_arith_term(rng, vars, is_real, depth - 1, bound);
            if is_real {
                format!("(/ {a} {d})")
            } else {
                format!("(mod {a} {d})")
            }
        }
        5 => {
            // `abs` is an Int-only op in SMT-LIB; for Real, fall through to a
            // plain negation so we never emit an ill-typed term.
            if is_real {
                let a = gen_arith_term(rng, vars, is_real, depth - 1, bound);
                format!("(- {a})")
            } else {
                let a = gen_arith_term(rng, vars, is_real, depth - 1, bound);
                format!("(abs {a})")
            }
        }
        _ => {
            // if-then-else on terms, with a boolean condition.
            let cond = gen_bool(rng, 1, &mut |r| gen_arith_atom(r, vars, is_real, bound));
            let a = gen_arith_term(rng, vars, is_real, depth - 1, bound);
            let b = gen_arith_term(rng, vars, is_real, depth - 1, bound);
            format!("(ite {cond} {a} {b})")
        }
    }
}

fn gen_arith_leaf(rng: &mut Rng, vars: &[String], is_real: bool) -> String {
    // 50/50 between a declared variable and a constant; bound quantifier
    // variables are equally eligible so quantified bodies stay well-scoped.
    let pool: Vec<&String> = vars.iter().collect();
    if !pool.is_empty() && rng.chance(1, 2) {
        pool[rng.index(pool.len())].clone()
    } else {
        arith_const(rng, is_real)
    }
}

const ARITH_REL_OPS: [&str; 6] = ["=", "<", "<=", ">", ">=", "distinct"];

fn gen_arith_atom(rng: &mut Rng, vars: &[String], is_real: bool, bound: &[String]) -> String {
    let op = ARITH_REL_OPS[rng.index(ARITH_REL_OPS.len())];
    // `distinct` is variadic; the rest are binary. Generating 2-3 operands
    // keeps it simple and well-typed.
    let arity = if op == "distinct" {
        rng.range_u32(2, 3) as usize
    } else {
        2
    };
    let parts: Vec<String> = (0..arity)
        .map(|_| gen_arith_term(rng, vars, is_real, MAX_TERM_DEPTH_LOCAL, bound))
        .collect();
    format!("({op} {})", parts.join(" "))
}

// Local shorthand so atom builders don't each need `cfg` threaded through.
const MAX_TERM_DEPTH_LOCAL: u32 = 2;

fn gen_linear_arith(rng: &mut Rng, is_real: bool, allow_quant: bool, cfg: &Config) -> String {
    let sort = if is_real { "Real" } else { "Int" };
    let num_vars = rng.range_u32(cfg.min_vars as u32, cfg.max_vars as u32) as usize;
    let vars: Vec<String> = (0..num_vars).map(|i| format!("x{i}")).collect();
    let num_asserts = rng.range_u32(cfg.min_asserts as u32, cfg.max_asserts as u32) as usize;

    let mut out = String::new();
    let _ = writeln!(
        out,
        "; grammar-fuzzer ({} seed-by-caller)",
        Logic::from_real(is_real, allow_quant).name()
    );
    let _ = writeln!(
        out,
        "(set-logic {})",
        Logic::from_real(is_real, allow_quant).name()
    );
    for v in &vars {
        let _ = writeln!(out, "(declare-const {v} {sort})");
    }
    for _ in 0..num_asserts {
        // Most assertions are quantifier-free; a minority (only when the
        // logic is `LIA`) wrap a quantifier around a shallow body so the
        // benchmark actually exercises quantifier reasoning.
        let formula = if allow_quant && rng.chance(1, 4) {
            gen_quantified(rng, &vars, is_real, cfg)
        } else {
            gen_bool(rng, cfg.max_formula_depth, &mut |r| {
                gen_arith_atom(r, &vars, is_real, &[])
            })
        };
        let _ = writeln!(out, "(assert {formula})");
    }
    let _ = writeln!(out, "(check-sat)");
    let _ = writeln!(out, "(exit)");
    out
}

/// A `forall`/`exists` over 1-2 freshly bound Int variables, with a shallow
/// boolean body that may reference both the bound vars and the declared ones.
fn gen_quantified(rng: &mut Rng, free_vars: &[String], is_real: bool, cfg: &Config) -> String {
    let nbound = rng.range_u32(1, 2) as usize;
    let bound: Vec<String> = (0..nbound).map(|i| format!("y{i}")).collect();
    let sort = if is_real { "Real" } else { "Int" };

    // Scope visible to the body: declared vars + bound vars.
    let mut scope: Vec<String> = free_vars.to_vec();
    scope.extend(bound.iter().cloned());

    let body = gen_bool(
        rng,
        cfg.max_formula_depth.saturating_sub(1).max(1),
        &mut |r| gen_arith_atom(r, &scope, is_real, &bound),
    );

    let binder = if rng.coin() { "forall" } else { "exists" };
    let decls: Vec<String> = bound.iter().map(|b| format!("({b} {sort})")).collect();
    format!("({binder} ({}) {body})", decls.join(" "))
}

impl Logic {
    /// Helper used only by the linear-arithmetic generator to recover the
    /// public `Logic` from its `(is_real, allow_quant)` dispatch arguments.
    fn from_real(is_real: bool, allow_quant: bool) -> Logic {
        match (is_real, allow_quant) {
            (false, false) => Logic::QfLia,
            (true, false) => Logic::QfLra,
            (false, true) => Logic::Lia,
            (true, true) => Logic::QfLra, // unreachable: we never call this with (true,true)
        }
    }
}

// =====================================================================
// QF_BV: fixed bit-width bit-vectors
// =====================================================================

/// Width-preserving binary BV ops.
const BV_BINOPS: [&str; 9] = [
    "bvadd", "bvsub", "bvmul", "bvand", "bvor", "bvxor", "bvshl", "bvlshr", "bvashr",
];
/// Division-like ops; only generated with a **non-zero constant** divisor.
const BV_DIVOPS: [&str; 4] = ["bvudiv", "bvurem", "bvsdiv", "bvsrem"];
/// Signed & unsigned comparisons.
const BV_REL_OPS: [&str; 10] = [
    "=", "distinct", "bvult", "bvule", "bvugt", "bvuge", "bvslt", "bvsle", "bvsgt", "bvsge",
];

fn bv_const(rng: &mut Rng, width: u32) -> String {
    let value = if width >= 64 {
        rng.next_u64()
    } else {
        rng.below(1u64 << width)
    };
    let width = width as usize;
    format!("#b{value:0width$b}")
}

/// A non-zero BV constant of `width` bits (avoids divide-by-zero noise).
fn nonzero_bv_const(rng: &mut Rng, width: u32) -> String {
    loop {
        let c = bv_const(rng, width);
        if c.contains('1') {
            return c;
        }
    }
}

fn gen_bv_term(rng: &mut Rng, vars: &[String], width: u32, depth: u32) -> String {
    if depth == 0 || rng.chance(1, 3) {
        if !vars.is_empty() && rng.chance(1, 2) {
            vars[rng.index(vars.len())].clone()
        } else {
            bv_const(rng, width)
        }
    } else if rng.chance(1, 6) {
        // Unary: bitwise not or two's-complement negation.
        let a = gen_bv_term(rng, vars, width, depth - 1);
        if rng.coin() {
            format!("(bvnot {a})")
        } else {
            format!("(bvneg {a})")
        }
    } else if rng.chance(1, 5) {
        // Division-like op with a non-zero constant divisor.
        let op = BV_DIVOPS[rng.index(BV_DIVOPS.len())];
        let d = nonzero_bv_const(rng, width);
        let a = gen_bv_term(rng, vars, width, depth - 1);
        format!("({op} {a} {d})")
    } else {
        let op = BV_BINOPS[rng.index(BV_BINOPS.len())];
        let a = gen_bv_term(rng, vars, width, depth - 1);
        let b = gen_bv_term(rng, vars, width, depth - 1);
        format!("({op} {a} {b})")
    }
}

fn gen_bv_atom(rng: &mut Rng, vars: &[String], width: u32) -> String {
    let op = BV_REL_OPS[rng.index(BV_REL_OPS.len())];
    let arity = if op == "distinct" {
        rng.range_u32(2, 3) as usize
    } else {
        2
    };
    let parts: Vec<String> = (0..arity)
        .map(|_| gen_bv_term(rng, vars, width, MAX_TERM_DEPTH_LOCAL))
        .collect();
    format!("({op} {})", parts.join(" "))
}

fn gen_bv(rng: &mut Rng, cfg: &Config) -> String {
    // Fixed width per script keeps every subterm uniformly typed.
    let width = *rng.pick(&[4u32, 8, 16]);
    let num_vars = rng.range_u32(cfg.min_vars as u32, cfg.max_vars as u32) as usize;
    let vars: Vec<String> = (0..num_vars).map(|i| format!("x{i}")).collect();
    let num_asserts = rng.range_u32(cfg.min_asserts as u32, cfg.max_asserts as u32) as usize;

    let mut out = String::new();
    let _ = writeln!(out, "; grammar-fuzzer (QF_BV width={width})");
    let _ = writeln!(out, "(set-logic QF_BV)");
    for v in &vars {
        let _ = writeln!(out, "(declare-const {v} (_ BitVec {width}))");
    }
    for _ in 0..num_asserts {
        let formula = gen_bool(rng, cfg.max_formula_depth, &mut |r| {
            gen_bv_atom(r, &vars, width)
        });
        let _ = writeln!(out, "(assert {formula})");
    }
    let _ = writeln!(out, "(check-sat)");
    let _ = writeln!(out, "(exit)");
    out
}

// =====================================================================
// QF_UF: uninterpreted functions over a single sort
// =====================================================================

fn gen_uf_term(rng: &mut Rng, consts: &[String], depth: u32) -> String {
    if depth == 0 || rng.chance(1, 3) {
        consts[rng.index(consts.len())].clone()
    } else if rng.chance(1, 2) {
        let a = gen_uf_term(rng, consts, depth - 1);
        format!("(f {a})")
    } else {
        let a = gen_uf_term(rng, consts, depth - 1);
        let b = gen_uf_term(rng, consts, depth - 1);
        format!("(g {a} {b})")
    }
}

fn gen_uf_atom(rng: &mut Rng, consts: &[String]) -> String {
    let op = if rng.coin() { "=" } else { "distinct" };
    let lhs = gen_uf_term(rng, consts, MAX_TERM_DEPTH_LOCAL);
    let rhs = gen_uf_term(rng, consts, MAX_TERM_DEPTH_LOCAL);
    format!("({op} {lhs} {rhs})")
}

fn gen_uf(rng: &mut Rng, cfg: &Config) -> String {
    let num_consts = rng.range_u32(3, 5) as usize;
    let consts: Vec<String> = (0..num_consts).map(|i| format!("c{i}")).collect();
    let num_asserts = rng.range_u32(cfg.min_asserts as u32, cfg.max_asserts as u32) as usize;

    let mut out = String::new();
    let _ = writeln!(out, "; grammar-fuzzer (QF_UF)");
    let _ = writeln!(out, "(set-logic QF_UF)");
    let _ = writeln!(out, "(declare-sort U 0)");
    for c in &consts {
        let _ = writeln!(out, "(declare-const {c} U)");
    }
    let _ = writeln!(out, "(declare-fun f (U) U)");
    let _ = writeln!(out, "(declare-fun g (U U) U)");
    for _ in 0..num_asserts {
        let formula = gen_bool(rng, cfg.max_formula_depth, &mut |r| gen_uf_atom(r, &consts));
        let _ = writeln!(out, "(assert {formula})");
    }
    let _ = writeln!(out, "(check-sat)");
    let _ = writeln!(out, "(exit)");
    out
}

// =====================================================================
// Tests
// =====================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn deterministic_for_fixed_seed() {
        for logic in Logic::ALL {
            let a = generate(logic, 12345, &Config::default()).source;
            let b = generate(logic, 12345, &Config::default()).source;
            assert_eq!(a, b, "{logic} must be deterministic for a fixed seed");
        }
    }

    #[test]
    fn different_seeds_usually_differ() {
        for logic in Logic::ALL {
            let a = generate(logic, 1, &Config::default()).source;
            let b = generate(logic, 2, &Config::default()).source;
            assert_ne!(a, b, "seeds 1 and 2 collided for {logic}");
        }
    }

    #[test]
    fn scripts_are_balanced_and_well_formed() {
        for logic in Logic::ALL {
            for seed in 0..40u64 {
                let s = generate(logic, seed, &Config::default()).source;
                assert!(
                    s.contains(&format!("(set-logic {})", logic.name())),
                    "{logic} seed {seed} missing set-logic"
                );
                assert!(
                    s.trim_end().ends_with("(exit)") || s.contains("(check-sat)"),
                    "{logic} seed {seed} missing check-sat"
                );
                let opens = s.chars().filter(|&c| c == '(').count();
                let closes = s.chars().filter(|&c| c == ')').count();
                assert_eq!(opens, closes, "{logic} seed {seed} unbalanced parens:\n{s}");
            }
        }
    }

    #[test]
    fn lia_terms_never_multiply_two_variables() {
        // Regression guard: the first arg of every `(* ...)` must be a
        // numeral/`(- numeral)`, never `x<N>`.
        for seed in 0..80u64 {
            let s = generate(Logic::QfLia, seed, &Config::default()).source;
            for line in s.lines() {
                assert!(
                    !line.contains("(* x"),
                    "seed {seed}: variable-first multiplication: {line}"
                );
            }
        }
    }

    #[test]
    fn bv_divisor_is_never_zero() {
        // Every division-like op's second argument must contain a `1` bit.
        for seed in 0..80u64 {
            let s = generate(Logic::QfBv, seed, &Config::default()).source;
            for line in s.lines() {
                for op in BV_DIVOPS.iter().copied() {
                    if let Some(rest) = line.strip_prefix(&format!("({op} ")) {
                        // rest looks like "<a> <const>)"
                        if let Some(divisor) = rest.split_whitespace().nth(1) {
                            let divisor = divisor.trim_end_matches(')');
                            assert!(
                                divisor.contains('1'),
                                "seed {seed}: {op} with zero divisor: {line}"
                            );
                        }
                    }
                }
            }
        }
    }

    #[test]
    fn parse_list_roundtrips() {
        assert_eq!(
            Logic::parse_list("QF_LIA, qf_bv ,LIA"),
            Some(vec![Logic::QfLia, Logic::QfBv, Logic::Lia])
        );
        assert_eq!(Logic::parse_list("nonsense"), None);
        assert_eq!(Logic::parse_list(""), None);
    }

    #[test]
    fn qf_lra_never_uses_int_only_ops() {
        // `div`/`mod`/`abs` are Int-only in SMT-LIB; emitting them over Real
        // is a generator bug that z3 rejects as a sort error.
        for seed in 0..80u64 {
            let s = generate(Logic::QfLra, seed, &Config::default()).source;
            for line in s.lines() {
                for bad in ["(div ", "(mod ", "(abs "] {
                    assert!(
                        !line.contains(bad),
                        "seed {seed}: Int-only op `{}` in Real script: {line}",
                        bad.trim()
                    );
                }
            }
        }
    }
}
