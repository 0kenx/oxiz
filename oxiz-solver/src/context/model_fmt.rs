//! Model and function-interpretation output formatting for [`Context`].
//!
//! These methods turn the solver's model, term values, and sorts into
//! SMT-LIB2 display strings for `(get-model)` / `(get-value ...)` and the Z3
//! function-interpretation extensions.  They live in a child module so the
//! (already large) `context` module stays under the 2000-line policy limit;
//! being a child of `context`, they retain full access to `Context`'s private
//! fields.

#[allow(unused_imports)]
use crate::prelude::*;
use crate::solver::SolverResult;
use oxiz_core::ast::{TermId, TermKind};
use oxiz_core::sort::{SortId, SortKind};

use super::{Context, RawFuncInterp};

impl Context {
    /// Get the model (if SAT)
    /// Returns a list of (name, sort, value) tuples
    pub fn get_model(&self) -> Option<Vec<(String, String, String)>> {
        if self.last_result != Some(SolverResult::Sat) {
            return None;
        }

        let mut model = Vec::new();
        let solver_model = self.solver.model()?;

        // Witness bookkeeping for unconstrained uninterpreted-sort constants:
        // `per_sort_next` is the next fresh witness index for a sort, and
        // `class_witness` maps an EUF congruence class (or a lone, never-equated
        // term) to its already-assigned index — so constants proven equal share
        // one witness while distinct constants get distinct ones.
        let mut per_sort_next: crate::prelude::HashMap<SortId, usize> =
            crate::prelude::HashMap::new();
        let mut class_witness: crate::prelude::HashMap<(SortId, u64), usize> =
            crate::prelude::HashMap::new();

        for decl in &self.declared_consts {
            let value = if let Some(val) = solver_model.get(decl.term) {
                self.format_value(val)
            } else if self.is_uninterpreted_sort(decl.sort) {
                // No direct model entry for an uninterpreted-sort constant:
                // synthesize a Z3-style `@uc_S_n` abstract witness.  Group by
                // EUF congruence class so equal constants share a witness;
                // never-equated constants key by their own term id (a disjoint
                // namespace via the high bit) so they stay distinct.  Always a
                // valid value, unlike the previous invalid `?`.
                let class_key: u64 = match self.solver.euf_class_representative(decl.term) {
                    Some(rep) => (1u64 << 32) | u64::from(rep),
                    None => u64::from(decl.term.0),
                };
                let idx = if let Some(&i) = class_witness.get(&(decl.sort, class_key)) {
                    i
                } else {
                    let next = per_sort_next.entry(decl.sort).or_insert(0);
                    let i = *next;
                    *next += 1;
                    class_witness.insert((decl.sort, class_key), i);
                    i
                };
                format!("@uc_{}_{}", self.format_sort_name(decl.sort), idx)
            } else {
                // Default value based on sort
                self.default_value(decl.sort)
            };
            let sort_name = self.format_sort_name(decl.sort);
            model.push((decl.name.clone(), sort_name, value));
        }

        Some(model)
    }

    /// Build a raw function interpretation for a declared uninterpreted function.
    ///
    /// Derives entries from the EUF congruence closure rather than from raw
    /// `Apply` terms alone.  For every application `f(a1, …, an)` interned in the
    /// E-graph, the arguments and the result are canonicalized through their
    /// equivalence-class representatives, so:
    ///
    /// - Two applications whose arguments are pairwise congruent (e.g. `f(a)` and
    ///   `f(b)` when `a = b` is implied by the assertions) collapse to a **single**
    ///   entry keyed by the shared argument class.
    /// - The reported argument and result strings are **model values** taken from
    ///   the class (resolving through the representative), not raw term ids.
    /// - When an application has no direct model value, the value of any congruent
    ///   member of its class is used.
    ///
    /// `else_value` is chosen as the most frequently occurring entry value (ties
    /// broken by first occurrence), mirroring how Z3 selects a default; if there
    /// are no entries it falls back to the return sort's default value.
    ///
    /// Returns `None` when:
    /// - the last check was not `Sat`, or
    /// - no model is available, or
    /// - `func_name` is not a declared function.
    ///
    /// The return type is `(entries, else_value_string, arity)` to avoid
    /// pulling `oxiz_core::model` types into this file.
    pub fn get_func_interp_raw(&self, func_name: &str) -> Option<RawFuncInterp> {
        if self.last_result != Some(SolverResult::Sat) {
            return None;
        }
        let solver_model = self.solver.model()?;

        // Find the declared function so we know its arity and default sort.
        let decl = self.declared_funs.iter().find(|d| d.name == func_name)?;
        let arity = decl.arg_sorts.len();
        let default_else = self.default_value(decl.ret_sort);

        // Resolve `func_name` to the EUF function-symbol id.  For an `Apply`
        // term the EUF id is the underlying value of the function-name `Spur`,
        // so we recover it from any matching application term (read-only — no
        // mutable interner access required).
        let mut func_id: Option<u32> = None;
        for idx in 0..(self.terms.len() as u32) {
            let tid = TermId(idx);
            let Some(term) = self.terms.get(tid) else {
                continue;
            };
            if let TermKind::Apply {
                func: func_spur, ..
            } = &term.kind
                && self.terms.resolve_str(*func_spur) == func_name
            {
                func_id = Some(func_spur.into_inner().get());
                break;
            }
        }

        // No application of this function exists in the E-graph: the function is
        // declared but never applied, so its interpretation is purely the default.
        let Some(func_id) = func_id else {
            return Some((Vec::new(), default_else, arity));
        };

        // Pull congruence-closed application entries from the EUF solver.  Each
        // entry already has its argument and result classes canonicalized, so
        // congruence (e.g. f(a) == f(b) when a == b) is applied for us.
        let euf_entries = self.solver.euf_function_entries(func_id);

        // Deduplicate on the canonical argument-class representative tuple so
        // congruent applications produce exactly one entry.  Because congruence
        // forces congruent applications into the same result class, the values
        // agree in a consistent model.
        let mut seen_arg_keys: crate::prelude::HashSet<smallvec::SmallVec<[u32; 4]>> =
            crate::prelude::HashSet::new();
        let mut entries: Vec<(Vec<String>, String)> = Vec::new();
        for entry in &euf_entries {
            // Resolve the result value first: skip applications whose class has
            // no concrete model value (an unconstrained application contributes
            // nothing observable beyond the else-branch).
            let Some(val_str) = self.class_value_string(&entry.result_class_terms, solver_model)
            else {
                continue;
            };

            if !seen_arg_keys.insert(entry.arg_reps.clone()) {
                continue; // already emitted this congruence class of arguments
            }

            // Resolve each argument to its canonical model value.  Falls back to
            // the default value for the corresponding argument sort when the
            // class carries no concrete value (rare: an unconstrained argument).
            let arg_strs: Vec<String> = entry
                .arg_class_terms
                .iter()
                .enumerate()
                .map(|(i, members)| {
                    self.class_value_string(members, solver_model)
                        .unwrap_or_else(|| {
                            decl.arg_sorts
                                .get(i)
                                .map_or_else(|| "?".to_string(), |&s| self.default_value(s))
                        })
                })
                .collect();
            entries.push((arg_strs, val_str));
        }

        // Pick `else_value`: the most common entry value (ties → first seen),
        // matching Z3's habit of reusing an existing value as the default.
        let else_value = Self::most_common_value(&entries).unwrap_or(default_else);

        Some((entries, else_value, arity))
    }

    /// Resolve an equivalence class (its member `TermId`s) to a formatted model
    /// value string, by finding the first member that carries either a direct
    /// model assignment or is itself a literal constant.
    ///
    /// Returns `None` when no member of the class has an observable value.
    fn class_value_string(
        &self,
        members: &[TermId],
        solver_model: &crate::solver::Model,
    ) -> Option<String> {
        for &member in members {
            // Direct model assignment (covers variables and applications whose
            // value was extracted from an equality constraint).
            if let Some(val_term) = solver_model.get(member) {
                return Some(self.format_value(val_term));
            }
            // The member may itself be a literal constant (e.g. the term `5` in
            // `f(a) = 5`), which has no separate model entry but is its own value.
            if let Some(term) = self.terms.get(member)
                && matches!(
                    term.kind,
                    TermKind::True
                        | TermKind::False
                        | TermKind::IntConst(_)
                        | TermKind::RealConst(_)
                        | TermKind::BitVecConst { .. }
                )
            {
                return Some(self.format_value(member));
            }
        }
        None
    }

    /// Choose the most frequently occurring value among the interpretation
    /// entries, breaking ties in favour of the earliest occurrence.  Returns
    /// `None` for an empty entry list.
    fn most_common_value(entries: &[(Vec<String>, String)]) -> Option<String> {
        let mut counts: crate::prelude::HashMap<&str, (usize, usize)> =
            crate::prelude::HashMap::new();
        for (order, (_, value)) in entries.iter().enumerate() {
            let slot = counts.entry(value.as_str()).or_insert((0, order));
            slot.0 += 1;
        }
        counts
            .into_iter()
            .max_by(|(_, (count_a, order_a)), (_, (count_b, order_b))| {
                // Higher count wins; on a tie the smaller insertion order wins,
                // so we reverse the order comparison.
                count_a.cmp(count_b).then_with(|| order_b.cmp(order_a))
            })
            .map(|(value, _)| value.to_string())
    }

    /// Format a sort ID to its SMT-LIB2 name.
    ///
    /// Handles every `SortKind` that [`Context::parse_sort_name`] can
    /// produce (its inverse), including compound `(Array ..)`/`(_
    /// BitVec ..)`/`(_ FloatingPoint ..)` forms and previously
    /// declared uninterpreted/datatype sorts by name, so
    /// `get-model`/`get-value` output reflects a declared constant's
    /// real sort instead of falling back to a generic placeholder.
    fn format_sort_name(&self, sort: SortId) -> String {
        let Some(s) = self.terms.sorts.get(sort) else {
            return "Unknown".to_string();
        };
        match &s.kind {
            SortKind::Bool => "Bool".to_string(),
            SortKind::Int => "Int".to_string(),
            SortKind::Real => "Real".to_string(),
            SortKind::String => "String".to_string(),
            SortKind::BitVec(w) => format!("(_ BitVec {w})"),
            SortKind::FloatingPoint { eb, sb } => format!("(_ FloatingPoint {eb} {sb})"),
            SortKind::Array { domain, range } => {
                let domain_str = self.format_sort_name(*domain);
                let range_str = self.format_sort_name(*range);
                format!("(Array {domain_str} {range_str})")
            }
            SortKind::Uninterpreted(spur) => self.terms.resolve_str(*spur).to_string(),
            SortKind::Datatype(_) => self
                .terms
                .sorts
                .datatype_name(sort)
                .map_or_else(|| "Unknown".to_string(), ToString::to_string),
            SortKind::Parameter(_) | SortKind::Parametric { .. } => "Unknown".to_string(),
        }
    }

    /// Whether `sort` is an uninterpreted (user-declared) sort.
    fn is_uninterpreted_sort(&self, sort: SortId) -> bool {
        self.terms
            .sorts
            .get(sort)
            .is_some_and(|s| matches!(s.kind, SortKind::Uninterpreted(_)))
    }

    /// Format a model value
    fn format_value(&self, term: TermId) -> String {
        match self.terms.get(term).map(|t| &t.kind) {
            Some(TermKind::True) => "true".to_string(),
            Some(TermKind::False) => "false".to_string(),
            Some(TermKind::IntConst(n)) => n.to_string(),
            Some(TermKind::RealConst(r)) => {
                if *r.denom() == 1 {
                    format!("{}.0", r.numer())
                } else {
                    format!("(/ {} {})", r.numer(), r.denom())
                }
            }
            Some(TermKind::BitVecConst { value, width }) => {
                format!(
                    "#b{:0>width$}",
                    format!("{:b}", value),
                    width = *width as usize
                )
            }
            // Floating-point constants, array store/const-array chains, and
            // string literals are structured values that the shared SMT-LIB
            // printer renders faithfully (`(fp ..)`, `(_ +zero eb sb)`,
            // `(store ..)`, `"..."`), so delegate rather than emitting an
            // invalid `?` placeholder.
            Some(
                TermKind::FpLit { .. }
                | TermKind::FpPlusInfinity { .. }
                | TermKind::FpMinusInfinity { .. }
                | TermKind::FpPlusZero { .. }
                | TermKind::FpMinusZero { .. }
                | TermKind::FpNaN { .. }
                | TermKind::Store(..)
                | TermKind::StringLit(_),
            ) => {
                let printer = oxiz_core::smtlib::Printer::new(&self.terms);
                printer.print_term(term)
            }
            _ => "?".to_string(),
        }
    }

    /// Get a default value for a sort.
    ///
    /// Used to complete `get-model` output for a declared constant that the
    /// model left unconstrained.  Every case yields a *valid* SMT-LIB value of
    /// the sort (never the invalid `?` placeholder), except datatypes with no
    /// nullary constructor, for which no ground witness can be synthesized
    /// without a recursive completion.
    fn default_value(&self, sort: SortId) -> String {
        if sort == self.terms.sorts.bool_sort {
            return "false".to_string();
        }
        if sort == self.terms.sorts.int_sort {
            return "0".to_string();
        }
        if sort == self.terms.sorts.real_sort {
            return "0.0".to_string();
        }
        let Some(s) = self.terms.sorts.get(sort) else {
            return "?".to_string();
        };
        match &s.kind {
            SortKind::String => "\"\"".to_string(),
            SortKind::BitVec(w) => format!("#b{:0>width$}", "0", width = *w as usize),
            // Positive zero is a canonical, valid ground FP value.
            SortKind::FloatingPoint { eb, sb } => format!("(_ +zero {eb} {sb})"),
            // A constant array whose every entry is the range's default value.
            SortKind::Array { range, .. } => {
                let range = *range;
                let sort_name = self.format_sort_name(sort);
                let range_default = self.default_value(range);
                format!("((as const {sort_name}) {range_default})")
            }
            // A datatype default is its first nullary constructor when one
            // exists (a valid ground value).
            SortKind::Datatype(_) => self.default_datatype_value(sort),
            // Uninterpreted-sort defaults are abstract witnesses.  `get_model`
            // assigns a distinct per-constant index; as a standalone fallback
            // emit the zero-th witness for the sort.
            SortKind::Uninterpreted(_) => {
                format!("@uc_{}_0", self.format_sort_name(sort))
            }
            _ => "?".to_string(),
        }
    }

    /// A ground default value for a datatype sort: the first nullary
    /// constructor if the datatype has one, else the honest `?` placeholder
    /// (a non-nullary constructor would require synthesizing default values
    /// for its fields, which can diverge for recursive datatypes).
    fn default_datatype_value(&self, sort: SortId) -> String {
        let Some(dt_name) = self.terms.sorts.datatype_name(sort) else {
            return "?".to_string();
        };
        let dt_name = dt_name.to_string();
        if let Some(def) = self.terms.sorts.get_datatype(&dt_name) {
            for ctor in &def.constructors {
                if ctor.selectors.is_empty() {
                    return self.terms.resolve_str(ctor.name).to_string();
                }
            }
        }
        "?".to_string()
    }

    /// Format the model as SMT-LIB2
    pub fn format_model(&self) -> String {
        match self.get_model() {
            None => "(error \"No model available\")".to_string(),
            Some(model) if model.is_empty() => "(model)".to_string(),
            Some(model) => {
                let mut lines = vec!["(model".to_string()];
                for (name, sort, value) in model {
                    lines.push(format!("  (define-fun {} () {} {})", name, sort, value));
                }
                lines.push(")".to_string());
                lines.join("\n")
            }
        }
    }
}
