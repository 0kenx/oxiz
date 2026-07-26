//! Ground string decision procedure with model construction and verification.
//!
//! The CDCL(T) core maps every string-theory atom (`str.++`, `str.len`,
//! `str.in_re`, `str.contains`, …) to a fresh SAT variable — there is no
//! incremental string theory wired into the propagation loop. Historically the
//! only string reasoning was a small set of definite-conflict detectors in
//! `oxiz-solver`, which could refute a fixed family of unsatisfiable formulas
//! but never *construct* a satisfying assignment, so every satisfiable ground
//! string benchmark fell through to an honest `Unknown`.
//!
//! This module closes that gap for the ground fragment (`QF_S` / the ground
//! part of `QF_SLIA`). It:
//!
//! 1. gathers per-variable string constraints from the asserted formula
//!    (constant equalities, length equalities/bounds, regex memberships,
//!    `prefixof`/`suffixof`/`contains` predicates, and concatenation
//!    equations),
//! 2. builds a candidate assignment for every string variable — propagating
//!    functional definitions, splitting concatenation equations by known
//!    operand lengths, and reducing the remaining regular constraints on each
//!    variable to a language-emptiness / shortest-word search over the
//!    Brzozowski derivative engine in [`super::regex_membership`], and
//! 3. **verifies** the candidate by concretely evaluating *every* assertion
//!    under it.
//!
//! The final verification step is what makes the answer sound: a `Sat` verdict
//! is returned only when a concrete witness satisfies the entire formula, so a
//! heuristic (necessarily incomplete) construction can never yield a spurious
//! `Sat`. Anything the construction cannot certify is reported as `Unknown`.

use super::regex::Regex;
use super::regex_membership::{WordSearch, compile_regex, search_word};
#[allow(unused_imports)]
use crate::prelude::*;
use num_bigint::BigInt;
use num_traits::ToPrimitive;
use oxiz_core::ast::{TermId, TermKind, TermManager};

/// Outcome of the ground string decision procedure.
///
/// `Unsat` is intentionally never produced here — refutation of ground string
/// formulas is handled by the definite-conflict detectors in `oxiz-solver`.
/// This procedure only ever *confirms* satisfiability with a concrete witness
/// (`Sat`) or gives up (`Unknown`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum GroundStringOutcome {
    /// A concrete model was constructed and verified against every assertion.
    /// The map assigns every free string variable a concrete value.
    Sat(FxHashMap<TermId, String>),
    /// No verified model could be built within the search bounds.
    Unknown,
}

/// Resource bounds shared by the per-variable regular-constraint search.
const MAX_REGEX_STATES: usize = 8000;
const MAX_REGEX_WORD_LEN: usize = 4096;
/// Recursion guard for the concrete evaluator.
const MAX_EVAL_DEPTH: usize = 4096;

/// Attempt to decide a ground string formula by constructing and verifying a
/// concrete model.
///
/// Returns [`GroundStringOutcome::Sat`] only when a concrete assignment to every
/// string variable makes *all* `assertions` evaluate to `true`; otherwise
/// [`GroundStringOutcome::Unknown`].
#[must_use]
pub fn solve_ground_string(manager: &TermManager, assertions: &[TermId]) -> GroundStringOutcome {
    let mut builder = ModelBuilder::new(manager, assertions);
    builder.gather();
    if builder.build_assignment() && builder.verify() {
        return GroundStringOutcome::Sat(builder.model);
    }
    GroundStringOutcome::Unknown
}

/// A concrete value the evaluator can produce for a ground term.
#[derive(Debug, Clone, PartialEq, Eq)]
enum Val {
    /// A string value.
    Str(String),
    /// An integer value.
    Int(BigInt),
    /// A Boolean value.
    Bool(bool),
}

impl Val {
    fn as_str(&self) -> Option<&str> {
        match self {
            Val::Str(s) => Some(s),
            _ => None,
        }
    }
    fn as_int(&self) -> Option<&BigInt> {
        match self {
            Val::Int(n) => Some(n),
            _ => None,
        }
    }
    fn as_bool(&self) -> Option<bool> {
        match self {
            Val::Bool(b) => Some(*b),
            _ => None,
        }
    }
}

/// Collected constraints and the growing model for one `check` invocation.
struct ModelBuilder<'a> {
    manager: &'a TermManager,
    assertions: &'a [TermId],
    /// Every string-sorted variable that appears in the formula.
    string_vars: FxHashSet<TermId>,
    /// Exact length equalities `len(var) = n`.
    len_eq: FxHashMap<TermId, i64>,
    /// Length lower bounds `len(var) >= lo` (the maximum lower bound seen).
    len_lo: FxHashMap<TermId, i64>,
    /// Length upper bounds `len(var) <= hi` (the minimum upper bound seen).
    len_hi: FxHashMap<TermId, i64>,
    /// Regular-language memberships per variable: `(regex, positive)`.
    memberships: FxHashMap<TermId, Vec<(Arc<Regex>, bool)>>,
    /// The current (partial) string assignment.
    model: FxHashMap<TermId, String>,
}

impl<'a> ModelBuilder<'a> {
    fn new(manager: &'a TermManager, assertions: &'a [TermId]) -> Self {
        Self {
            manager,
            assertions,
            string_vars: FxHashSet::default(),
            len_eq: FxHashMap::default(),
            len_lo: FxHashMap::default(),
            len_hi: FxHashMap::default(),
            memberships: FxHashMap::default(),
            model: FxHashMap::default(),
        }
    }

    /// Return `true` when `term` is a string-sorted variable.
    fn is_string_var(&self, term: TermId) -> bool {
        let Some(td) = self.manager.get(term) else {
            return false;
        };
        if !matches!(td.kind, TermKind::Var(_)) {
            return false;
        }
        self.manager
            .sorts
            .get(td.sort)
            .is_some_and(oxiz_core::sort::Sort::is_string)
    }

    // -------------------------------------------------------------------
    // Constraint gathering
    // -------------------------------------------------------------------

    /// Walk every assertion, recording string variables and the atomic
    /// constraints used to guide model construction.
    fn gather(&mut self) {
        // Collect all string variables first (traversing through every node).
        let mut stack: Vec<TermId> = self.assertions.to_vec();
        let mut seen: FxHashSet<TermId> = FxHashSet::default();
        while let Some(t) = stack.pop() {
            if !seen.insert(t) {
                continue;
            }
            if self.is_string_var(t) {
                self.string_vars.insert(t);
            }
            if let Some(td) = self.manager.get(t) {
                push_children(&td.kind, &mut stack);
            }
        }

        // Record top-level (conjunctive) atomic constraints. Assertions are an
        // implicit conjunction; we descend through `And` but treat everything
        // else structurally as an atom for constraint extraction.
        let assertions = self.assertions.to_vec();
        for a in assertions {
            self.record_atom(a);
        }
    }

    /// Extract a single asserted atom (descending through top-level `And`).
    fn record_atom(&mut self, term: TermId) {
        let Some(td) = self.manager.get(term) else {
            return;
        };
        match &td.kind {
            TermKind::And(args) => {
                let children: Vec<TermId> = args.iter().copied().collect();
                for c in children {
                    self.record_atom(c);
                }
            }
            TermKind::Eq(lhs, rhs) => self.record_eq(*lhs, *rhs),
            TermKind::StrInRe(var, re) => self.record_membership(*var, *re, true),
            TermKind::Not(inner) => {
                if let Some(inner_td) = self.manager.get(*inner)
                    && let TermKind::StrInRe(var, re) = &inner_td.kind
                {
                    self.record_membership(*var, *re, false);
                }
            }
            TermKind::StrContains(hay, needle) => self.record_contains(*hay, *needle),
            TermKind::StrPrefixOf(pre, var) => self.record_prefix(*pre, *var),
            TermKind::StrSuffixOf(suf, var) => self.record_suffix(*suf, *var),
            TermKind::Ge(a, b) => self.record_len_ineq(*a, *b, IneqKind::Ge),
            TermKind::Gt(a, b) => self.record_len_ineq(*a, *b, IneqKind::Gt),
            TermKind::Le(a, b) => self.record_len_ineq(*a, *b, IneqKind::Le),
            TermKind::Lt(a, b) => self.record_len_ineq(*a, *b, IneqKind::Lt),
            _ => {}
        }
    }

    /// Extract equalities: length equalities and regex/predicate memberships are
    /// treated specially; other equalities are only consulted during the
    /// definitional / concat-splitting phase (via a fresh traversal).
    fn record_eq(&mut self, lhs: TermId, rhs: TermId) {
        // len(v) = n  (either orientation)
        if let Some((v, n)) = self.as_len_const(lhs, rhs) {
            self.len_eq.insert(v, n);
            self.set_lo(v, n);
            self.set_hi(v, n);
            return;
        }
        if let Some((v, n)) = self.as_len_const(rhs, lhs) {
            self.len_eq.insert(v, n);
            self.set_lo(v, n);
            self.set_hi(v, n);
        }
    }

    /// Record `str.contains(hay, needle)` with a constant `needle` as a
    /// membership `hay ∈ Σ* · needle · Σ*`.
    fn record_contains(&mut self, hay: TermId, needle: TermId) {
        if !self.is_string_var(hay) {
            return;
        }
        if let Some(n) = self.const_string(needle) {
            let re = Regex::concat(vec![Regex::all(), Regex::literal(&n), Regex::all()]);
            self.memberships.entry(hay).or_default().push((re, true));
        }
    }

    /// Record `str.prefixof(pre, var)` with a constant `pre` as a membership
    /// `var ∈ pre · Σ*`.
    fn record_prefix(&mut self, pre: TermId, var: TermId) {
        if !self.is_string_var(var) {
            return;
        }
        if let Some(p) = self.const_string(pre) {
            let re = Regex::concat(vec![Regex::literal(&p), Regex::all()]);
            self.memberships.entry(var).or_default().push((re, true));
        }
    }

    /// Record `str.suffixof(suf, var)` with a constant `suf` as a membership
    /// `var ∈ Σ* · suf`.
    fn record_suffix(&mut self, suf: TermId, var: TermId) {
        if !self.is_string_var(var) {
            return;
        }
        if let Some(s) = self.const_string(suf) {
            let re = Regex::concat(vec![Regex::all(), Regex::literal(&s)]);
            self.memberships.entry(var).or_default().push((re, true));
        }
    }

    /// Record a `str.in_re` membership on a variable with a ground regex.
    fn record_membership(&mut self, var: TermId, re: TermId, positive: bool) {
        if !self.is_string_var(var) {
            return;
        }
        if let Some(compiled) = compile_regex(self.manager, re) {
            self.memberships
                .entry(var)
                .or_default()
                .push((compiled, positive));
        }
    }

    /// Record a length inequality `len(v) ▷ n` (or its mirror) into the bounds.
    fn record_len_ineq(&mut self, a: TermId, b: TermId, kind: IneqKind) {
        // a ▷ b with one side `len(v)` and the other a constant.
        if let (Some(v), Some(n)) = (self.as_len(a), self.int_const(b)) {
            // len(v) ▷ n
            match kind {
                IneqKind::Ge => self.set_lo(v, n),
                IneqKind::Gt => self.set_lo(v, n + 1),
                IneqKind::Le => self.set_hi(v, n),
                IneqKind::Lt => self.set_hi(v, n - 1),
            }
            return;
        }
        if let (Some(n), Some(v)) = (self.int_const(a), self.as_len(b)) {
            // n ▷ len(v)  ==>  len(v) ◁ n
            match kind {
                IneqKind::Ge => self.set_hi(v, n),     // n >= len  => len <= n
                IneqKind::Gt => self.set_hi(v, n - 1), // n > len => len <= n-1
                IneqKind::Le => self.set_lo(v, n),     // n <= len => len >= n
                IneqKind::Lt => self.set_lo(v, n + 1), // n < len => len >= n+1
            }
        }
    }

    fn set_lo(&mut self, v: TermId, n: i64) {
        let e = self.len_lo.entry(v).or_insert(n);
        if n > *e {
            *e = n;
        }
    }
    fn set_hi(&mut self, v: TermId, n: i64) {
        let e = self.len_hi.entry(v).or_insert(n);
        if n < *e {
            *e = n;
        }
    }

    /// If `len_term` is `(str.len v)` for a string variable `v`, return `v`.
    fn as_len(&self, len_term: TermId) -> Option<TermId> {
        match &self.manager.get(len_term)?.kind {
            TermKind::StrLen(inner) if self.is_string_var(*inner) => Some(*inner),
            _ => None,
        }
    }

    /// Match `(= (str.len v) n)` shape: `len_term` is `str.len v`, `int_term`
    /// is an integer constant. Returns `(v, n)`.
    fn as_len_const(&self, len_term: TermId, int_term: TermId) -> Option<(TermId, i64)> {
        let v = self.as_len(len_term)?;
        let n = self.int_const(int_term)?;
        Some((v, n))
    }

    /// Decode an integer constant term to `i64`.
    fn int_const(&self, term: TermId) -> Option<i64> {
        match &self.manager.get(term)?.kind {
            TermKind::IntConst(n) => n.to_i64(),
            _ => None,
        }
    }

    /// Fold a ground string term (literal or constant concatenation) to a value.
    fn const_string(&self, term: TermId) -> Option<String> {
        match &self.manager.get(term)?.kind {
            TermKind::StringLit(s) => Some(s.clone()),
            TermKind::StrConcat(a, b) => {
                let mut s = self.const_string(*a)?;
                s.push_str(&self.const_string(*b)?);
                Some(s)
            }
            _ => None,
        }
    }

    // -------------------------------------------------------------------
    // Model construction
    // -------------------------------------------------------------------

    /// Build a full assignment for every string variable. Returns `false` only
    /// when construction is impossible within scope (the caller then reports
    /// `Unknown`); a `true` return still requires [`Self::verify`] to confirm.
    fn build_assignment(&mut self) -> bool {
        // Fixpoint: propagate functional definitions and split concatenation
        // equations until no further variable can be pinned.
        let mut changed = true;
        let mut rounds = 0usize;
        while changed && rounds < 64 {
            changed = false;
            rounds += 1;
            changed |= self.propagate_definitions();
            changed |= self.split_concats();
        }

        // Regular-constraint construction for remaining constrained variables.
        let constrained: Vec<TermId> = self
            .string_vars
            .iter()
            .copied()
            .filter(|v| {
                !self.model.contains_key(v)
                    && (self.memberships.contains_key(v)
                        || self.len_eq.contains_key(v)
                        || self.len_lo.contains_key(v)
                        || self.len_hi.contains_key(v))
            })
            .collect();
        for v in constrained {
            if let Some(word) = self.solve_regular(v) {
                self.model.insert(v, word);
            }
        }

        // Any still-unassigned variable is unconstrained: pick the empty string.
        let leftover: Vec<TermId> = self
            .string_vars
            .iter()
            .copied()
            .filter(|v| !self.model.contains_key(v))
            .collect();
        for v in leftover {
            self.model.insert(v, String::new());
        }

        true
    }

    /// Assign a variable whenever it is defined by `var = <ground/known term>`.
    fn propagate_definitions(&mut self) -> bool {
        let mut assignments: Vec<(TermId, String)> = Vec::new();
        for &a in self.assertions {
            self.collect_definitions(a, &mut assignments);
        }
        let mut changed = false;
        for (v, s) in assignments {
            if let hash_map::Entry::Vacant(slot) = self.model.entry(v) {
                slot.insert(s);
                changed = true;
            }
        }
        changed
    }

    /// Descend through top-level `And`s collecting `Eq(var, rhs)` definitions
    /// where `rhs` currently evaluates to a concrete string.
    fn collect_definitions(&self, term: TermId, out: &mut Vec<(TermId, String)>) {
        let Some(td) = self.manager.get(term) else {
            return;
        };
        match &td.kind {
            TermKind::And(args) => {
                for &c in args {
                    self.collect_definitions(c, out);
                }
            }
            TermKind::Eq(lhs, rhs) => {
                self.try_definition(*lhs, *rhs, out);
                self.try_definition(*rhs, *lhs, out);
            }
            _ => {}
        }
    }

    /// If `var` is an unassigned string variable and `rhs` evaluates to a
    /// concrete string, record `var := value`.
    fn try_definition(&self, var: TermId, rhs: TermId, out: &mut Vec<(TermId, String)>) {
        if !self.is_string_var(var) || self.model.contains_key(&var) {
            return;
        }
        if let Some(Val::Str(s)) = self.eval(rhs, 0) {
            out.push((var, s));
        }
    }

    /// Split concatenation equations `concat(ops) = target` whose operand
    /// lengths are all determined, assigning each unknown variable operand its
    /// positional slice of `target`.
    fn split_concats(&mut self) -> bool {
        let mut plans: Vec<(TermId, String)> = Vec::new();
        for &a in self.assertions {
            self.collect_concat_plans(a, &mut plans);
        }
        let mut changed = false;
        for (v, s) in plans {
            if let hash_map::Entry::Vacant(slot) = self.model.entry(v) {
                slot.insert(s);
                changed = true;
            }
        }
        changed
    }

    /// Descend through top-level `And`s collecting concat-split assignments.
    fn collect_concat_plans(&self, term: TermId, out: &mut Vec<(TermId, String)>) {
        let Some(td) = self.manager.get(term) else {
            return;
        };
        match &td.kind {
            TermKind::And(args) => {
                for &c in args {
                    self.collect_concat_plans(c, out);
                }
            }
            TermKind::Eq(lhs, rhs) => {
                self.try_concat_split(*lhs, *rhs, out);
                self.try_concat_split(*rhs, *lhs, out);
            }
            _ => {}
        }
    }

    /// If `concat_term` is a concatenation and `target_term` evaluates to a
    /// concrete string, try to solve for the unknown operands.
    fn try_concat_split(
        &self,
        concat_term: TermId,
        target_term: TermId,
        out: &mut Vec<(TermId, String)>,
    ) {
        let Some(td) = self.manager.get(concat_term) else {
            return;
        };
        if !matches!(td.kind, TermKind::StrConcat(_, _)) {
            return;
        }
        let Some(Val::Str(target)) = self.eval(target_term, 0) else {
            return;
        };
        let mut ops: Vec<TermId> = Vec::new();
        self.flatten_concat(concat_term, &mut ops);
        self.plan_split(&ops, &target, out);
    }

    /// Flatten a `str.++` tree into a left-to-right operand list.
    fn flatten_concat(&self, term: TermId, ops: &mut Vec<TermId>) {
        match self.manager.get(term).map(|t| &t.kind) {
            Some(TermKind::StrConcat(a, b)) => {
                self.flatten_concat(*a, ops);
                self.flatten_concat(*b, ops);
            }
            _ => ops.push(term),
        }
    }

    /// Given the operands of a concatenation and the target string, determine
    /// each operand's length (from a known value or an exact length equality)
    /// and, when at most one operand length is left free, assign every unknown
    /// variable operand its positional slice.
    fn plan_split(&self, ops: &[TermId], target: &str, out: &mut Vec<(TermId, String)>) {
        let target_chars: Vec<char> = target.chars().collect();
        let total = target_chars.len() as i64;

        // Determine each operand's known value (if any) and known length.
        let mut known_val: Vec<Option<String>> = Vec::with_capacity(ops.len());
        let mut known_len: Vec<Option<i64>> = Vec::with_capacity(ops.len());
        for &op in ops {
            let val = match self.eval(op, 0) {
                Some(Val::Str(s)) => Some(s),
                _ => None,
            };
            let len = match &val {
                Some(s) => Some(s.chars().count() as i64),
                None => self.len_eq.get(&op).copied(),
            };
            known_val.push(val);
            known_len.push(len);
        }

        // Identify operands whose length is still unknown.
        let free_idx: Vec<usize> = (0..ops.len()).filter(|&i| known_len[i].is_none()).collect();
        let mut lens: Vec<i64> = known_len.iter().map(|l| l.unwrap_or(0)).collect();
        match free_idx.as_slice() {
            [] => {
                let sum: i64 = lens.iter().sum();
                if sum != total {
                    return; // length conflict — refuted elsewhere
                }
            }
            [only] => {
                let sum_known: i64 = known_len.iter().flatten().sum();
                let remaining = total - sum_known;
                if remaining < 0 {
                    return;
                }
                lens[*only] = remaining;
            }
            _ => return, // too underdetermined to split
        }

        // Slice the target positionally and emit assignments for variable
        // operands whose value is not yet known.
        let mut pos: i64 = 0;
        for (i, &op) in ops.iter().enumerate() {
            let len = lens[i];
            if len < 0 || pos + len > total {
                return;
            }
            let seg: String = target_chars[pos as usize..(pos + len) as usize]
                .iter()
                .collect();
            match &known_val[i] {
                Some(existing) => {
                    if existing != &seg {
                        return; // inconsistent placement — this split cannot hold
                    }
                }
                None => {
                    if self.is_string_var(op) && !self.model.contains_key(&op) {
                        out.push((op, seg));
                    }
                }
            }
            pos += len;
        }
    }

    /// Construct a witness for a single variable from its intersected regular
    /// constraints (memberships + prefix/suffix/contains) subject to its length
    /// window, using the derivative-automaton shortest-word search.
    fn solve_regular(&self, var: TermId) -> Option<String> {
        let mut parts: Vec<Arc<Regex>> = Vec::new();
        if let Some(ms) = self.memberships.get(&var) {
            for (re, positive) in ms {
                if *positive {
                    parts.push(re.clone());
                } else {
                    parts.push(Regex::complement(re.clone()));
                }
            }
        }
        let combined = Regex::inter(parts);

        let lo = self.len_lo.get(&var).copied().unwrap_or(0).max(0) as usize;
        let hi = self.len_hi.get(&var).and_then(|h| {
            if *h < 0 {
                Some(0usize) // upper bound below zero: unsatisfiable window
            } else {
                (*h).to_usize()
            }
        });
        if let Some(h) = hi
            && lo > h
        {
            return None;
        }

        match search_word(&combined, lo, hi, MAX_REGEX_STATES, MAX_REGEX_WORD_LEN) {
            WordSearch::Found(w) => Some(w),
            WordSearch::Empty | WordSearch::Unknown => None,
        }
    }

    // -------------------------------------------------------------------
    // Verification
    // -------------------------------------------------------------------

    /// Verify the constructed model by concretely evaluating every assertion.
    fn verify(&self) -> bool {
        for &a in self.assertions {
            match self.eval(a, 0) {
                Some(Val::Bool(true)) => {}
                _ => return false,
            }
        }
        true
    }

    // -------------------------------------------------------------------
    // Concrete evaluator
    // -------------------------------------------------------------------

    /// Evaluate a ground term (under the current `model`) to a concrete value.
    /// Returns `None` when a value cannot be determined (unassigned variable,
    /// unsupported operator, non-ground regex, out-of-range integer, …).
    ///
    /// Note: this is a total structural *interpreter* over the typed SMT term
    /// AST — it walks `TermKind` nodes and computes their SMT-LIB semantics. It
    /// executes no external or user code (the name `eval` refers to term
    /// evaluation, not dynamic code evaluation).
    fn eval(&self, term: TermId, depth: usize) -> Option<Val> {
        if depth > MAX_EVAL_DEPTH {
            return None;
        }
        let d = depth + 1;
        let td = self.manager.get(term)?;
        match &td.kind {
            TermKind::True => Some(Val::Bool(true)),
            TermKind::False => Some(Val::Bool(false)),
            TermKind::IntConst(n) => Some(Val::Int(n.clone())),
            TermKind::StringLit(s) => Some(Val::Str(s.clone())),
            TermKind::Var(_) => self.model.get(&term).map(|s| Val::Str(s.clone())),

            TermKind::Not(a) => Some(Val::Bool(!self.eval(*a, d)?.as_bool()?)),
            TermKind::And(args) => {
                let mut all_true = true;
                let mut saw_unknown = false;
                for &c in args {
                    match self.eval(c, d).and_then(|v| v.as_bool()) {
                        Some(false) => return Some(Val::Bool(false)),
                        Some(true) => {}
                        None => {
                            saw_unknown = true;
                            all_true = false;
                        }
                    }
                }
                if saw_unknown {
                    None
                } else {
                    Some(Val::Bool(all_true))
                }
            }
            TermKind::Or(args) => {
                let mut saw_unknown = false;
                for &c in args {
                    match self.eval(c, d).and_then(|v| v.as_bool()) {
                        Some(true) => return Some(Val::Bool(true)),
                        Some(false) => {}
                        None => saw_unknown = true,
                    }
                }
                if saw_unknown {
                    None
                } else {
                    Some(Val::Bool(false))
                }
            }
            TermKind::Xor(a, b) => Some(Val::Bool(
                self.eval(*a, d)?.as_bool()? ^ self.eval(*b, d)?.as_bool()?,
            )),
            TermKind::Implies(a, b) => {
                match self.eval(*a, d).and_then(|v| v.as_bool()) {
                    Some(false) => Some(Val::Bool(true)),
                    Some(true) => Some(Val::Bool(self.eval(*b, d)?.as_bool()?)),
                    None => {
                        // false antecedent already handled; if consequent is true, true.
                        match self.eval(*b, d).and_then(|v| v.as_bool()) {
                            Some(true) => Some(Val::Bool(true)),
                            _ => None,
                        }
                    }
                }
            }
            TermKind::Ite(c, t, e) => match self.eval(*c, d)?.as_bool()? {
                true => self.eval(*t, d),
                false => self.eval(*e, d),
            },
            TermKind::Eq(a, b) => self.eval_eq(*a, *b, d),
            TermKind::Distinct(args) => {
                let mut vals: Vec<Val> = Vec::with_capacity(args.len());
                for &c in args {
                    vals.push(self.eval(c, d)?);
                }
                for i in 0..vals.len() {
                    for j in (i + 1)..vals.len() {
                        if vals[i] == vals[j] {
                            return Some(Val::Bool(false));
                        }
                    }
                }
                Some(Val::Bool(true))
            }

            TermKind::Neg(a) => Some(Val::Int(-self.eval(*a, d)?.as_int()?.clone())),
            TermKind::Add(args) => {
                let mut acc = BigInt::from(0);
                for &c in args {
                    acc += self.eval(c, d)?.as_int()?;
                }
                Some(Val::Int(acc))
            }
            TermKind::Sub(a, b) => Some(Val::Int(
                self.eval(*a, d)?.as_int()? - self.eval(*b, d)?.as_int()?,
            )),
            TermKind::Mul(args) => {
                let mut acc = BigInt::from(1);
                for &c in args {
                    acc *= self.eval(c, d)?.as_int()?;
                }
                Some(Val::Int(acc))
            }
            TermKind::Lt(a, b) => self.eval_cmp(*a, *b, d, |o| o == core::cmp::Ordering::Less),
            TermKind::Le(a, b) => self.eval_cmp(*a, *b, d, |o| o != core::cmp::Ordering::Greater),
            TermKind::Gt(a, b) => self.eval_cmp(*a, *b, d, |o| o == core::cmp::Ordering::Greater),
            TermKind::Ge(a, b) => self.eval_cmp(*a, *b, d, |o| o != core::cmp::Ordering::Less),

            TermKind::StrConcat(a, b) => {
                let mut s = self.eval(*a, d)?.as_str()?.to_string();
                s.push_str(self.eval(*b, d)?.as_str()?);
                Some(Val::Str(s))
            }
            TermKind::StrLen(a) => {
                let s = self.eval(*a, d)?;
                Some(Val::Int(BigInt::from(s.as_str()?.chars().count())))
            }
            TermKind::StrSubstr(s, i, l) => self.eval_substr(*s, *i, *l, d),
            TermKind::StrAt(s, i) => self.eval_at(*s, *i, d),
            TermKind::StrContains(hay, needle) => {
                let h = self.eval(*hay, d)?;
                let n = self.eval(*needle, d)?;
                Some(Val::Bool(h.as_str()?.contains(n.as_str()?)))
            }
            TermKind::StrPrefixOf(pre, s) => {
                let p = self.eval(*pre, d)?;
                let s = self.eval(*s, d)?;
                Some(Val::Bool(s.as_str()?.starts_with(p.as_str()?)))
            }
            TermKind::StrSuffixOf(suf, s) => {
                let sf = self.eval(*suf, d)?;
                let s = self.eval(*s, d)?;
                Some(Val::Bool(s.as_str()?.ends_with(sf.as_str()?)))
            }
            TermKind::StrIndexOf(s, t, i) => self.eval_indexof(*s, *t, *i, d),
            TermKind::StrReplace(s, t, r) => self.eval_replace(*s, *t, *r, d, false),
            TermKind::StrReplaceAll(s, t, r) => self.eval_replace(*s, *t, *r, d, true),
            TermKind::StrToInt(s) => {
                let s = self.eval(*s, d)?;
                Some(Val::Int(str_to_int(s.as_str()?)))
            }
            TermKind::IntToStr(n) => {
                let n = self.eval(*n, d)?;
                Some(Val::Str(int_to_str(n.as_int()?)))
            }
            TermKind::StrInRe(s, re) => {
                let s = self.eval(*s, d)?;
                let compiled = compile_regex(self.manager, *re)?;
                Some(Val::Bool(compiled.matches(s.as_str()?)))
            }

            _ => None,
        }
    }

    /// Evaluate an equality between two evaluable operands.
    fn eval_eq(&self, a: TermId, b: TermId, d: usize) -> Option<Val> {
        let va = self.eval(a, d)?;
        let vb = self.eval(b, d)?;
        Some(Val::Bool(va == vb))
    }

    /// Evaluate an integer comparison; `pred` maps the operand ordering to the
    /// truth value.
    fn eval_cmp(
        &self,
        a: TermId,
        b: TermId,
        d: usize,
        pred: impl Fn(core::cmp::Ordering) -> bool,
    ) -> Option<Val> {
        let va = self.eval(a, d)?;
        let vb = self.eval(b, d)?;
        let ord = va.as_int()?.cmp(vb.as_int()?);
        Some(Val::Bool(pred(ord)))
    }

    /// SMT-LIB `str.substr`: the substring of length at most `l` starting at
    /// `i`, or the empty string when the indices are out of range.
    fn eval_substr(&self, s: TermId, i: TermId, l: TermId, d: usize) -> Option<Val> {
        let s = self.eval(s, d)?;
        let chars: Vec<char> = s.as_str()?.chars().collect();
        let n = chars.len() as i64;
        let i = self.eval(i, d)?.as_int()?.to_i64()?;
        let l = self.eval(l, d)?.as_int()?.to_i64()?;
        if i < 0 || i >= n || l <= 0 {
            return Some(Val::Str(String::new()));
        }
        let end = (i + l).min(n);
        Some(Val::Str(chars[i as usize..end as usize].iter().collect()))
    }

    /// SMT-LIB `str.at`: the one-character string at index `i`, or empty.
    fn eval_at(&self, s: TermId, i: TermId, d: usize) -> Option<Val> {
        let s = self.eval(s, d)?;
        let chars: Vec<char> = s.as_str()?.chars().collect();
        let n = chars.len() as i64;
        let i = self.eval(i, d)?.as_int()?.to_i64()?;
        if i < 0 || i >= n {
            return Some(Val::Str(String::new()));
        }
        Some(Val::Str(chars[i as usize].to_string()))
    }

    /// SMT-LIB `str.indexof`: first index of `t` in `s` at or after `i`, or -1.
    fn eval_indexof(&self, s: TermId, t: TermId, i: TermId, d: usize) -> Option<Val> {
        let s = self.eval(s, d)?;
        let t = self.eval(t, d)?;
        let s_chars: Vec<char> = s.as_str()?.chars().collect();
        let t_chars: Vec<char> = t.as_str()?.chars().collect();
        let n = s_chars.len() as i64;
        let start = self.eval(i, d)?.as_int()?.to_i64()?;
        if start < 0 || start > n {
            return Some(Val::Int(BigInt::from(-1)));
        }
        // Empty needle matches at `start`.
        if t_chars.is_empty() {
            return Some(Val::Int(BigInt::from(start)));
        }
        let start = start as usize;
        let tlen = t_chars.len();
        if tlen > s_chars.len() {
            return Some(Val::Int(BigInt::from(-1)));
        }
        let last = s_chars.len() - tlen;
        for begin in start..=last {
            if s_chars[begin..begin + tlen] == t_chars[..] {
                return Some(Val::Int(BigInt::from(begin)));
            }
        }
        Some(Val::Int(BigInt::from(-1)))
    }

    /// SMT-LIB `str.replace` / `str.replace_all`. With an empty pattern the
    /// string is returned unchanged.
    fn eval_replace(&self, s: TermId, t: TermId, r: TermId, d: usize, all: bool) -> Option<Val> {
        let s = self.eval(s, d)?.as_str()?.to_string();
        let t = self.eval(t, d)?.as_str()?.to_string();
        let r = self.eval(r, d)?.as_str()?.to_string();
        if t.is_empty() {
            // Match Z3/SMT-LIB empty-pattern semantics: `str.replace` (first)
            // prepends the replacement (`r ++ s`), whereas `str.replace_all`
            // leaves the string unchanged (it cannot replace infinitely).
            let out = if all { s } else { format!("{r}{s}") };
            return Some(Val::Str(out));
        }
        let out = if all {
            s.replace(&t, &r)
        } else {
            s.replacen(&t, &r, 1)
        };
        Some(Val::Str(out))
    }
}

/// Which inequality relation an atom encodes.
#[derive(Clone, Copy)]
enum IneqKind {
    Ge,
    Gt,
    Le,
    Lt,
}

/// SMT-LIB `str.to_int`: the numeric value of an all-digit non-empty string,
/// else `-1`.
fn str_to_int(s: &str) -> BigInt {
    if s.is_empty() || !s.bytes().all(|b| b.is_ascii_digit()) {
        return BigInt::from(-1);
    }
    s.parse::<BigInt>().unwrap_or_else(|_| BigInt::from(-1))
}

/// SMT-LIB `str.from_int`: the decimal string of a non-negative integer, else
/// the empty string.
fn int_to_str(n: &BigInt) -> String {
    if *n < BigInt::from(0) {
        String::new()
    } else {
        n.to_string()
    }
}

/// Push every immediate sub-term of `kind` onto `out` (used to discover all
/// string variables). Traverses through every compound kind that can carry a
/// string sub-term; leaves without children push nothing.
fn push_children(kind: &TermKind, out: &mut Vec<TermId>) {
    match kind {
        TermKind::Not(a)
        | TermKind::Neg(a)
        | TermKind::StrLen(a)
        | TermKind::StrToInt(a)
        | TermKind::IntToStr(a) => out.push(*a),
        TermKind::Xor(a, b)
        | TermKind::Implies(a, b)
        | TermKind::Eq(a, b)
        | TermKind::Sub(a, b)
        | TermKind::Div(a, b)
        | TermKind::Mod(a, b)
        | TermKind::Lt(a, b)
        | TermKind::Le(a, b)
        | TermKind::Gt(a, b)
        | TermKind::Ge(a, b)
        | TermKind::StrConcat(a, b)
        | TermKind::StrContains(a, b)
        | TermKind::StrPrefixOf(a, b)
        | TermKind::StrSuffixOf(a, b)
        | TermKind::StrInRe(a, b)
        | TermKind::StrAt(a, b)
        | TermKind::Select(a, b) => {
            out.push(*a);
            out.push(*b);
        }
        TermKind::Ite(a, b, c)
        | TermKind::StrSubstr(a, b, c)
        | TermKind::StrIndexOf(a, b, c)
        | TermKind::StrReplace(a, b, c)
        | TermKind::StrReplaceAll(a, b, c)
        | TermKind::Store(a, b, c) => {
            out.push(*a);
            out.push(*b);
            out.push(*c);
        }
        TermKind::And(args)
        | TermKind::Or(args)
        | TermKind::Add(args)
        | TermKind::Mul(args)
        | TermKind::Distinct(args) => out.extend(args.iter().copied()),
        TermKind::Apply { args, .. } | TermKind::DtConstructor { args, .. } => {
            out.extend(args.iter().copied())
        }
        TermKind::DtTester { arg, .. } | TermKind::DtSelector { arg, .. } => out.push(*arg),
        _ => {}
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use oxiz_core::smtlib::{Command, parse_script};

    /// Parse a whole SMT-LIB2 script, returning the manager and asserted terms.
    fn parse_asserts(src: &str) -> (TermManager, Vec<TermId>) {
        let mut m = TermManager::new();
        let cmds = parse_script(src, &mut m).expect("script parses");
        let mut asserts = Vec::new();
        for cmd in cmds {
            match cmd {
                Command::Assert(t) | Command::AssertNamed(t, _) => asserts.push(t),
                _ => {}
            }
        }
        (m, asserts)
    }

    fn solve(src: &str) -> GroundStringOutcome {
        let (m, asserts) = parse_asserts(src);
        solve_ground_string(&m, &asserts)
    }

    #[test]
    fn concat_with_pinned_operands() {
        let out = solve(
            r#"(declare-const x String)
               (declare-const y String)
               (assert (= (str.++ x y) "hello"))
               (assert (= x "hel"))
               (assert (= y "lo"))"#,
        );
        assert!(matches!(out, GroundStringOutcome::Sat(_)));
    }

    #[test]
    fn concat_split_by_lengths() {
        let out = solve(
            r#"(declare-const s String)
               (declare-const t String)
               (assert (= (str.len s) 5))
               (assert (= (str.len t) 3))
               (assert (= (str.++ s t) "worldfoo"))"#,
        );
        assert!(matches!(out, GroundStringOutcome::Sat(_)));
    }

    #[test]
    fn contains_prefix_length() {
        let out = solve(
            r#"(declare-const s String)
               (assert (str.contains s "test"))
               (assert (str.prefixof "my" s))
               (assert (>= (str.len s) 6))"#,
        );
        assert!(matches!(out, GroundStringOutcome::Sat(_)));
    }

    #[test]
    fn suffix_contains_upper_bound() {
        let out = solve(
            r#"(declare-const text String)
               (assert (str.suffixof ".txt" text))
               (assert (str.contains text "file"))
               (assert (<= (str.len text) 15))"#,
        );
        assert!(matches!(out, GroundStringOutcome::Sat(_)));
    }

    #[test]
    fn replace_pinned() {
        let out = solve(
            r#"(declare-const input String)
               (declare-const output String)
               (assert (= output (str.replace input "old" "new")))
               (assert (= input "the old way"))
               (assert (= output "the new way"))"#,
        );
        assert!(matches!(out, GroundStringOutcome::Sat(_)));
    }

    #[test]
    fn regex_digit_suffix_prefix_length() {
        let out = solve(
            r#"(declare-const phone String)
               (assert (str.in_re phone (re.++ (re.* re.allchar) (re.++ (re.range "0" "9") (re.++ (re.range "0" "9") (re.range "0" "9"))))))
               (assert (= (str.len phone) 10))
               (assert (str.prefixof "call" phone))"#,
        );
        assert!(matches!(out, GroundStringOutcome::Sat(_)));
    }

    #[test]
    fn regex_lowercase_range_contains() {
        let out = solve(
            r#"(declare-const word String)
               (assert (str.in_re word (re.++ (re.range "a" "z") (re.++ (re.range "a" "z") (re.++ (re.range "a" "z") (re.* (re.range "a" "z")))))))
               (assert (>= (str.len word) 3))
               (assert (<= (str.len word) 8))
               (assert (str.contains word "test"))"#,
        );
        assert!(matches!(out, GroundStringOutcome::Sat(_)));
    }

    #[test]
    fn unsat_length_conflict_is_unknown_here() {
        // This procedure never reports Unsat; a length conflict just fails to
        // build a verified model.
        let out = solve(
            r#"(declare-const x String)
               (assert (= (str.len x) 10))
               (assert (= x "short"))"#,
        );
        assert_eq!(out, GroundStringOutcome::Unknown);
    }

    #[test]
    fn empty_pattern_replace_semantics() {
        // str.replace (first) with empty pattern prepends the replacement.
        let out = solve(
            r#"(declare-const r String)
               (assert (= r (str.replace "abc" "" "X")))
               (assert (= r "Xabc"))"#,
        );
        assert!(matches!(out, GroundStringOutcome::Sat(_)));
        // The wrong reading (unchanged) must NOT verify.
        let bad = solve(
            r#"(declare-const r String)
               (assert (= r (str.replace "abc" "" "X")))
               (assert (= r "abc"))"#,
        );
        assert_eq!(bad, GroundStringOutcome::Unknown);
        // str.replace_all with empty pattern leaves the string unchanged.
        let all = solve(
            r#"(declare-const r String)
               (assert (= r (str.replace_all "abc" "" "X")))
               (assert (= r "abc"))"#,
        );
        assert!(matches!(all, GroundStringOutcome::Sat(_)));
    }

    #[test]
    fn contradiction_does_not_verify() {
        // (= s "abc") ∧ (str.contains s "xyz") is unsatisfiable — the ground
        // solver must not fabricate a Sat witness for it.
        let out = solve(
            r#"(declare-const s String)
               (assert (= s "abc"))
               (assert (str.contains s "xyz"))"#,
        );
        assert_eq!(out, GroundStringOutcome::Unknown);
    }

    #[test]
    fn negated_membership_builds_witness() {
        // Not a "cat" but length 3 over {a..z}: some 3-letter word that is not
        // exactly "cat" is a valid witness.
        let out = solve(
            r#"(declare-const w String)
               (assert (not (str.in_re w (str.to_re "cat"))))
               (assert (str.in_re w (re.++ (re.range "a" "z") (re.++ (re.range "a" "z") (re.range "a" "z")))))"#,
        );
        assert!(matches!(out, GroundStringOutcome::Sat(_)));
    }
}
