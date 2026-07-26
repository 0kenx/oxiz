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
//! | `QfLia`  | `QF_LIA` | `Int`  | linear, `abs`, `div`/`mod` (non-zero divisor), `ite` |
//! | `QfLra`  | `QF_LRA` | `Real` | linear, decimal literals, `/` |
//! | `QfNia`  | `QF_NIA` | `Int`  | nonlinear (var·var allowed) |
//! | `QfNra`  | `QF_NRA` | `Real` | nonlinear |
//! | `QfBv`   | `QF_BV`  | `(_ BitVec W)` | bitwise/arith/shift, signed & unsigned compares |
//! | `QfUf`   | `QF_UF`  | uninterpreted `U` | congruence/equality over uninterpreted funs |
//! | `QfA`    | `QF_AUFLIA` | `(Array Int Int)` | `select`/`store`, extensionality |
//! | `QfS`    | `QF_S`   | `String` | `str.++`/`at`/`substr`/`replace`, `len`, `contains`, … |
//! | `Lia`    | `LIA`    | `Int`  | adds `forall`/`exists` (shallow bodies) |
//!
//! Integer division/mod is only ever generated with a **non-zero numeral**
//! divisor, sidestepping the SMT-LIB divide-by-zero edge case where solvers
//! have historically disagreed (and would create noise rather than signal).

use crate::rng::Rng;
use std::fmt::Write as _;

/// The logics the grammar fuzzer can generate.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Logic {
    QfLia,
    QfLra,
    QfNia,
    QfNra,
    QfBv,
    QfUf,
    QfA,
    QfS,
    /// Quantified linear integer arithmetic (`forall`/`exists`).
    Lia,
}

impl Logic {
    /// SMT-LIB `set-logic` name.
    pub fn name(self) -> &'static str {
        match self {
            Logic::QfLia => "QF_LIA",
            Logic::QfLra => "QF_LRA",
            Logic::QfNia => "QF_NIA",
            Logic::QfNra => "QF_NRA",
            Logic::QfBv => "QF_BV",
            Logic::QfUf => "QF_UF",
            Logic::QfA => "QF_AUFLIA",
            Logic::QfS => "QF_S",
            Logic::Lia => "LIA",
        }
    }

    /// All logics, in a fixed canonical order.
    pub const ALL: [Logic; 9] = [
        Logic::QfLia,
        Logic::QfLra,
        Logic::QfNia,
        Logic::QfNra,
        Logic::QfBv,
        Logic::QfUf,
        Logic::QfA,
        Logic::QfS,
        Logic::Lia,
    ];

    /// `true` for logics over `Real` arithmetic.
    pub fn is_real(self) -> bool {
        matches!(self, Logic::QfLra | Logic::QfNra)
    }

    /// `true` for logics whose arithmetic may include variable·variable
    /// products (the nonlinear fragments).
    pub fn is_nonlinear(self) -> bool {
        matches!(self, Logic::QfNia | Logic::QfNra)
    }

    /// `true` when a sat model assigns **concrete scalar values** to every
    /// declared variable (so a `get-value` model can be grounded and
    /// re-checked). Arrays and uninterpreted functions are excluded because
    /// their models are stores/function-graphs rather than atoms.
    pub fn has_scalar_models(self) -> bool {
        matches!(
            self,
            Logic::QfLia | Logic::QfLra | Logic::QfNia | Logic::QfNra | Logic::QfBv | Logic::QfS
        )
    }

    /// Parse a comma-separated list of logic names (case-insensitive, accepts
    /// both `QfLia` and `QF_LIA`); `None` if any token is unrecognized.
    pub fn parse_list(s: &str) -> Option<Vec<Logic>> {
        let mut out = Vec::new();
        for tok in s.split(',').map(str::trim).filter(|t| !t.is_empty()) {
            let norm = tok.to_ascii_uppercase().replace('-', "_");
            let logic = match norm.as_str() {
                "QF_LIA" | "QFLIA" => Logic::QfLia,
                "QF_LRA" | "QFLRA" => Logic::QfLra,
                "QF_NIA" | "QFNIA" => Logic::QfNia,
                "QF_NRA" | "QFNRA" => Logic::QfNra,
                "QF_BV" | "QFBV" => Logic::QfBv,
                "QF_UF" | "QFUF" => Logic::QfUf,
                "QF_A" | "QFA" | "QF_AUFLIA" | "QFAUFLIA" => Logic::QfA,
                "QF_S" | "QFS" => Logic::QfS,
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

/// Knobs that control generator size/depth.
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
/// `vars` lists every top-level declared constant name (used by the
/// model-validity oracle to issue a `get-value` query and ground the result).
#[derive(Debug, Clone)]
pub struct Script {
    pub logic: Logic,
    pub seed: u64,
    pub source: String,
    pub vars: Vec<String>,
}

/// Generate one fully deterministic script. `generate(logic, seed, cfg)` is a
/// pure function of its arguments.
pub fn generate(logic: Logic, seed: u64, cfg: &Config) -> Script {
    let mut rng = Rng::new(seed);
    let (source, vars) = match logic {
        Logic::QfLia | Logic::QfLra | Logic::QfNia | Logic::QfNra | Logic::Lia => {
            gen_arith_logic(&mut rng, logic, cfg)
        }
        Logic::QfBv => gen_bv(&mut rng, cfg),
        Logic::QfUf => gen_uf(&mut rng, cfg),
        Logic::QfA => gen_array(&mut rng, cfg),
        Logic::QfS => gen_string(&mut rng, cfg),
    };
    Script {
        logic,
        seed,
        source,
        vars,
    }
}

// =====================================================================
// Boolean structure (shared by every logic; the leaves come from `atom`)
// =====================================================================

/// Build a Boolean formula of the given depth whose leaves are produced by
/// `atom`. Connectives: `and`, `or`, `not`, `=>`, `xor`, and `ite`.
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
// Arithmetic: Int/Real, linear or nonlinear (QF_LIA/LRA/NIA/NRA/LIA)
// =====================================================================

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

/// A **non-zero** arithmetic constant (safe divisor/multiplier; keeps linear
/// fragments linear and avoids divide-by-zero divergence between solvers).
fn nonzero_arith_const(rng: &mut Rng, is_real: bool) -> String {
    loop {
        let c = arith_const(rng, is_real);
        if !c.contains("(- 0") && c != "0" && c != "0.0" {
            return c;
        }
    }
}

fn gen_arith_term(
    rng: &mut Rng,
    vars: &[String],
    is_real: bool,
    nonlinear: bool,
    depth: u32,
) -> String {
    if depth == 0 || rng.chance(1, 3) {
        return gen_arith_leaf(rng, vars, is_real);
    }
    match rng.index(7) {
        0 => {
            let n = rng.range_u32(2, 3) as usize;
            let parts: Vec<String> = (0..n)
                .map(|_| gen_arith_term(rng, vars, is_real, nonlinear, depth - 1))
                .collect();
            format!("(+ {})", parts.join(" "))
        }
        1 => {
            let a = gen_arith_term(rng, vars, is_real, nonlinear, depth - 1);
            let b = gen_arith_term(rng, vars, is_real, nonlinear, depth - 1);
            format!("(- {a} {b})")
        }
        2 => {
            // Multiplication. Linear fragments restrict the first factor to a
            // numeral; nonlinear fragments allow variable·subterm.
            if nonlinear && !vars.is_empty() && rng.chance(1, 2) {
                let v = vars[rng.index(vars.len())].clone();
                let a = gen_arith_term(rng, vars, is_real, nonlinear, depth - 1);
                format!("(* {v} {a})")
            } else {
                let c = arith_const(rng, is_real);
                let a = gen_arith_term(rng, vars, is_real, nonlinear, depth - 1);
                format!("(* {c} {a})")
            }
        }
        3 => {
            // Division by a non-zero constant. `div` is Int-only; `/` is Real.
            let d = nonzero_arith_const(rng, is_real);
            let a = gen_arith_term(rng, vars, is_real, nonlinear, depth - 1);
            if is_real {
                format!("(/ {a} {d})")
            } else {
                format!("(div {a} {d})")
            }
        }
        4 => {
            // `mod` is Int-only; Real reuses real division.
            let d = nonzero_arith_const(rng, is_real);
            let a = gen_arith_term(rng, vars, is_real, nonlinear, depth - 1);
            if is_real {
                format!("(/ {a} {d})")
            } else {
                format!("(mod {a} {d})")
            }
        }
        5 => {
            // `abs` is Int-only; Real falls back to unary negation.
            let a = gen_arith_term(rng, vars, is_real, nonlinear, depth - 1);
            if is_real {
                format!("(- {a})")
            } else {
                format!("(abs {a})")
            }
        }
        _ => {
            let cond = gen_bool(rng, 1, &mut |r| gen_arith_atom(r, vars, is_real, nonlinear));
            let a = gen_arith_term(rng, vars, is_real, nonlinear, depth - 1);
            let b = gen_arith_term(rng, vars, is_real, nonlinear, depth - 1);
            format!("(ite {cond} {a} {b})")
        }
    }
}

fn gen_arith_leaf(rng: &mut Rng, vars: &[String], is_real: bool) -> String {
    let pool: Vec<&String> = vars.iter().collect();
    if !pool.is_empty() && rng.chance(1, 2) {
        pool[rng.index(pool.len())].clone()
    } else {
        arith_const(rng, is_real)
    }
}

const ARITH_REL_OPS: [&str; 6] = ["=", "<", "<=", ">", ">=", "distinct"];

fn gen_arith_atom(rng: &mut Rng, vars: &[String], is_real: bool, nonlinear: bool) -> String {
    let op = ARITH_REL_OPS[rng.index(ARITH_REL_OPS.len())];
    let arity = if op == "distinct" {
        rng.range_u32(2, 3) as usize
    } else {
        2
    };
    let parts: Vec<String> = (0..arity)
        .map(|_| gen_arith_term(rng, vars, is_real, nonlinear, MAX_TERM_DEPTH_LOCAL))
        .collect();
    format!("({op} {})", parts.join(" "))
}

/// Quantifier body over the given scope (declared vars + bound vars).
fn gen_arith_atom_scoped(
    rng: &mut Rng,
    scope: &[String],
    is_real: bool,
    nonlinear: bool,
) -> String {
    gen_arith_atom(rng, scope, is_real, nonlinear)
}

/// A `forall`/`exists` over 1-2 bound Int variables with a shallow body that
/// may reference both bound and declared variables.
fn gen_quantified(rng: &mut Rng, free_vars: &[String], is_real: bool, cfg: &Config) -> String {
    let nbound = rng.range_u32(1, 2) as usize;
    let bound: Vec<String> = (0..nbound).map(|i| format!("y{i}")).collect();
    let sort = if is_real { "Real" } else { "Int" };
    let mut scope: Vec<String> = free_vars.to_vec();
    scope.extend(bound.iter().cloned());
    let body = gen_bool(
        rng,
        cfg.max_formula_depth.saturating_sub(1).max(1),
        &mut |r| gen_arith_atom_scoped(r, &scope, is_real, false),
    );
    let binder = if rng.coin() { "forall" } else { "exists" };
    let decls: Vec<String> = bound.iter().map(|b| format!("({b} {sort})")).collect();
    format!("({binder} ({}) {body})", decls.join(" "))
}

fn gen_arith_logic(rng: &mut Rng, logic: Logic, cfg: &Config) -> (String, Vec<String>) {
    let is_real = logic.is_real();
    let nonlinear = logic.is_nonlinear();
    let allow_quant = logic == Logic::Lia;
    let sort = if is_real { "Real" } else { "Int" };

    let num_vars = rng.range_u32(cfg.min_vars as u32, cfg.max_vars as u32) as usize;
    let vars: Vec<String> = (0..num_vars).map(|i| format!("x{i}")).collect();
    let num_asserts = rng.range_u32(cfg.min_asserts as u32, cfg.max_asserts as u32) as usize;

    let mut out = String::new();
    let _ = writeln!(out, "; grammar-fuzzer ({logic} seed-by-caller)");
    let _ = writeln!(out, "(set-logic {logic})");
    for v in &vars {
        let _ = writeln!(out, "(declare-const {v} {sort})");
    }
    for _ in 0..num_asserts {
        let formula = if allow_quant && rng.chance(1, 4) {
            gen_quantified(rng, &vars, is_real, cfg)
        } else {
            gen_bool(rng, cfg.max_formula_depth, &mut |r| {
                gen_arith_atom(r, &vars, is_real, nonlinear)
            })
        };
        let _ = writeln!(out, "(assert {formula})");
    }
    let _ = writeln!(out, "(check-sat)");
    let _ = writeln!(out, "(exit)");
    (out, vars)
}

// =====================================================================
// QF_BV: fixed bit-width bit-vectors
// =====================================================================

const BV_BINOPS: [&str; 9] = [
    "bvadd", "bvsub", "bvmul", "bvand", "bvor", "bvxor", "bvshl", "bvlshr", "bvashr",
];
const BV_DIVOPS: [&str; 4] = ["bvudiv", "bvurem", "bvsdiv", "bvsrem"];
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
        let a = gen_bv_term(rng, vars, width, depth - 1);
        if rng.coin() {
            format!("(bvnot {a})")
        } else {
            format!("(bvneg {a})")
        }
    } else if rng.chance(1, 5) {
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

fn gen_bv(rng: &mut Rng, cfg: &Config) -> (String, Vec<String>) {
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
    (out, vars)
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

fn gen_uf(rng: &mut Rng, cfg: &Config) -> (String, Vec<String>) {
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
    // UF models are function graphs, not scalar atoms -> excluded from the
    // model-validity oracle.
    (out, Vec::new())
}

// =====================================================================
// QF_A: arrays of Int -> Int
// =====================================================================

/// Array-typed term: a declared array, or `(store arr i v)`.
fn gen_array_term(rng: &mut Rng, arrays: &[String], idxvars: &[String], depth: u32) -> String {
    if depth == 0 || rng.chance(1, 2) {
        arrays[rng.index(arrays.len())].clone()
    } else {
        let a = gen_array_term(rng, arrays, idxvars, depth - 1);
        let i = gen_small_int_term(rng, idxvars);
        let v = gen_small_int_term(rng, idxvars);
        format!("(store {a} {i} {v})")
    }
}

/// A small linear Int term used as an array index/value.
fn gen_small_int_term(rng: &mut Rng, idxvars: &[String]) -> String {
    gen_arith_term(rng, idxvars, false, false, 1)
}

fn gen_array_atom(rng: &mut Rng, arrays: &[String], idxvars: &[String]) -> String {
    let kind = rng.index(3);
    match kind {
        0 => {
            // equality/distinct of two array-typed terms (exercises
            // extensionality).
            let op = if rng.coin() { "=" } else { "distinct" };
            let a = gen_array_term(rng, arrays, idxvars, MAX_TERM_DEPTH_LOCAL);
            let b = gen_array_term(rng, arrays, idxvars, MAX_TERM_DEPTH_LOCAL);
            format!("({op} {a} {b})")
        }
        1 => {
            // read-then-compare: (rel (select a i) j)
            let op = ARITH_REL_OPS[rng.index(ARITH_REL_OPS.len())];
            let a = gen_array_term(rng, arrays, idxvars, 1);
            let i = gen_small_int_term(rng, idxvars);
            let lhs = format!("(select {a} {i})");
            let rhs = gen_small_int_term(rng, idxvars);
            format!("({op} {lhs} {rhs})")
        }
        _ => {
            // two reads compared: (rel (select a i) (select b j))
            let op = ARITH_REL_OPS[rng.index(ARITH_REL_OPS.len())];
            let a = gen_array_term(rng, arrays, idxvars, 1);
            let b = gen_array_term(rng, arrays, idxvars, 1);
            let i = gen_small_int_term(rng, idxvars);
            let j = gen_small_int_term(rng, idxvars);
            format!("({op} (select {a} {i}) (select {b} {j}))")
        }
    }
}

fn gen_array(rng: &mut Rng, cfg: &Config) -> (String, Vec<String>) {
    let narr = rng.range_u32(2, 3) as usize;
    let arrays: Vec<String> = (0..narr).map(|i| format!("a{i}")).collect();
    let nidx = rng.range_u32(2, 3) as usize;
    let idxvars: Vec<String> = (0..nidx).map(|i| format!("i{i}")).collect();
    let num_asserts = rng.range_u32(cfg.min_asserts as u32, cfg.max_asserts as u32) as usize;

    let mut out = String::new();
    let _ = writeln!(out, "; grammar-fuzzer (QF_AUFLIA Array Int Int)");
    let _ = writeln!(out, "(set-logic QF_AUFLIA)");
    for a in &arrays {
        let _ = writeln!(out, "(declare-const {a} (Array Int Int))");
    }
    for i in &idxvars {
        let _ = writeln!(out, "(declare-const {i} Int)");
    }
    for _ in 0..num_asserts {
        let formula = gen_bool(rng, cfg.max_formula_depth, &mut |r| {
            gen_array_atom(r, &arrays, &idxvars)
        });
        let _ = writeln!(out, "(assert {formula})");
    }
    let _ = writeln!(out, "(check-sat)");
    let _ = writeln!(out, "(exit)");
    // Array models are stores -> excluded from the model oracle.
    (out, Vec::new())
}

// =====================================================================
// QF_S: strings
// =====================================================================

const STR_ALPHABET: &str = "ab";

fn str_literal(rng: &mut Rng) -> String {
    let len = rng.range_u32(0, 3) as usize;
    let mut s = String::new();
    for _ in 0..len {
        s.push(STR_ALPHABET.as_bytes()[rng.index(STR_ALPHABET.len())] as char);
    }
    // Escape backslashes/quotes defensively (alphabet has none, but keep
    // future-proof).
    s.replace('\\', "\\\\").replace('"', "\\\"")
}

fn small_int_const(rng: &mut Rng) -> i64 {
    rng.range_i64(0, 3)
}

/// A string-typed term.
fn gen_str_term(rng: &mut Rng, vars: &[String], depth: u32) -> String {
    if depth == 0 || rng.chance(1, 3) {
        if !vars.is_empty() && rng.chance(1, 2) {
            return vars[rng.index(vars.len())].clone();
        }
        return format!("\"{}\"", str_literal(rng));
    }
    match rng.index(5) {
        0 => {
            let a = gen_str_term(rng, vars, depth - 1);
            let b = gen_str_term(rng, vars, depth - 1);
            format!("(str.++ {a} {b})")
        }
        1 => {
            let a = gen_str_term(rng, vars, depth - 1);
            let i = small_int_const(rng);
            format!("(str.at {a} {i})")
        }
        2 => {
            let a = gen_str_term(rng, vars, depth - 1);
            let i = small_int_const(rng);
            let j = small_int_const(rng).max(1);
            format!("(str.substr {a} {i} {j})")
        }
        3 => {
            let a = gen_str_term(rng, vars, depth - 1);
            let b = format!("\"{}\"", str_literal(rng));
            let c = format!("\"{}\"", str_literal(rng));
            format!("(str.replace {a} {b} {c})")
        }
        _ => format!("\"{}\"", str_literal(rng)),
    }
}

fn gen_str_atom(rng: &mut Rng, vars: &[String]) -> String {
    match rng.index(6) {
        0 => {
            let op = if rng.coin() { "=" } else { "distinct" };
            let a = gen_str_term(rng, vars, MAX_TERM_DEPTH_LOCAL);
            let b = gen_str_term(rng, vars, MAX_TERM_DEPTH_LOCAL);
            format!("({op} {a} {b})")
        }
        1 => {
            let a = gen_str_term(rng, vars, MAX_TERM_DEPTH_LOCAL);
            let b = gen_str_term(rng, vars, MAX_TERM_DEPTH_LOCAL);
            format!("(str.contains {a} {b})")
        }
        2 => {
            let a = gen_str_term(rng, vars, MAX_TERM_DEPTH_LOCAL);
            let b = gen_str_term(rng, vars, MAX_TERM_DEPTH_LOCAL);
            format!("(str.prefixof {a} {b})")
        }
        3 => {
            let a = gen_str_term(rng, vars, MAX_TERM_DEPTH_LOCAL);
            let b = gen_str_term(rng, vars, MAX_TERM_DEPTH_LOCAL);
            format!("(str.suffixof {a} {b})")
        }
        4 => {
            // (str.len s) compared to a small int.
            let op = ARITH_REL_OPS[rng.index(ARITH_REL_OPS.len())];
            let a = gen_str_term(rng, vars, MAX_TERM_DEPTH_LOCAL);
            let n = small_int_const(rng);
            format!("({op} (str.len {a}) {n})")
        }
        _ => {
            // str.indexof compared to a small int.
            let op = ARITH_REL_OPS[rng.index(ARITH_REL_OPS.len())];
            let a = gen_str_term(rng, vars, MAX_TERM_DEPTH_LOCAL);
            let b = gen_str_term(rng, vars, MAX_TERM_DEPTH_LOCAL);
            let n = small_int_const(rng);
            format!("({op} (str.indexof {a} {b} 0) {n})")
        }
    }
}

fn gen_string(rng: &mut Rng, cfg: &Config) -> (String, Vec<String>) {
    let num_vars = rng.range_u32(cfg.min_vars as u32, cfg.max_vars as u32) as usize;
    let vars: Vec<String> = (0..num_vars).map(|i| format!("s{i}")).collect();
    let num_asserts = rng.range_u32(cfg.min_asserts as u32, cfg.max_asserts as u32) as usize;

    let mut out = String::new();
    let _ = writeln!(out, "; grammar-fuzzer (QF_S)");
    let _ = writeln!(out, "(set-logic QF_S)");
    for v in &vars {
        let _ = writeln!(out, "(declare-const {v} String)");
    }
    for _ in 0..num_asserts {
        let formula = gen_bool(rng, cfg.max_formula_depth, &mut |r| gen_str_atom(r, &vars));
        let _ = writeln!(out, "(assert {formula})");
    }
    let _ = writeln!(out, "(check-sat)");
    let _ = writeln!(out, "(exit)");
    (out, vars)
}

// Local shorthand so atom builders don't each need `cfg` threaded through.
const MAX_TERM_DEPTH_LOCAL: u32 = 2;

// =====================================================================
// Tests
// =====================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn deterministic_for_fixed_seed() {
        for logic in Logic::ALL {
            let a = generate(logic, 12345, &Config::default());
            let b = generate(logic, 12345, &Config::default());
            assert_eq!(a.source, b.source, "{logic} must be deterministic");
            assert_eq!(a.vars, b.vars, "{logic} vars must be deterministic");
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
                    s.contains("(check-sat)"),
                    "{logic} seed {seed} missing check-sat"
                );
                let opens = s.chars().filter(|&c| c == '(').count();
                let closes = s.chars().filter(|&c| c == ')').count();
                assert_eq!(opens, closes, "{logic} seed {seed} unbalanced parens:\n{s}");
            }
        }
    }

    #[test]
    fn qf_lia_terms_never_multiply_two_variables() {
        // QF_LIA must stay linear: the first arg of `(* ...)` is always a
        // numeral, never `x<N>`.
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
    fn qf_nia_does_reach_nonlinear_products() {
        // Sanity that the nonlinear fragment is actually nonlinear across a
        // reasonable seed range.
        let mut seen_nonlinear = 0;
        for seed in 0..200u64 {
            let s = generate(Logic::QfNia, seed, &Config::default()).source;
            if s.contains("(* x") {
                seen_nonlinear += 1;
            }
        }
        assert!(
            seen_nonlinear > 50,
            "QF_NIA rarely produced var*var ({seen_nonlinear}/200)"
        );
    }

    #[test]
    fn qf_lra_never_uses_int_only_ops() {
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

    #[test]
    fn bv_divisor_is_never_zero() {
        for seed in 0..80u64 {
            let s = generate(Logic::QfBv, seed, &Config::default()).source;
            for line in s.lines() {
                for op in BV_DIVOPS.iter().copied() {
                    if let Some(rest) = line.strip_prefix(&format!("({op} ")) {
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
    fn array_scripts_only_index_with_int_terms() {
        // Cheap structural guard: no Real/Bool leakage into QF_A.
        for seed in 0..40u64 {
            let s = generate(Logic::QfA, seed, &Config::default()).source;
            assert!(s.contains("(declare-const a0 (Array Int Int))"));
            assert!(s.contains("(set-logic QF_AUFLIA)"));
            assert!(!s.contains("Real"));
        }
    }

    #[test]
    fn parse_list_roundtrips() {
        assert_eq!(
            Logic::parse_list("QF_LIA, qf_nia ,QF_S,QF_A"),
            Some(vec![Logic::QfLia, Logic::QfNia, Logic::QfS, Logic::QfA])
        );
        assert_eq!(Logic::parse_list("nonsense"), None);
        assert_eq!(Logic::parse_list(""), None);
    }
}
