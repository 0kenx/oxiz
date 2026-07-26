//! String theory constraint checking

#[allow(unused_imports)]
use crate::prelude::*;
use num_traits::ToPrimitive;
use oxiz_core::ast::{TermId, TermKind, TermManager};
use oxiz_theories::string::{GroundStringOutcome, solve_ground_string};

use super::Solver;

impl Solver {
    pub(super) fn check_string_constraints(&self, manager: &TermManager) -> bool {
        // Collect string variable assignments and length constraints
        let mut string_assignments: FxHashMap<TermId, String> = FxHashMap::default();
        let mut length_constraints: FxHashMap<TermId, i64> = FxHashMap::default();
        let mut concat_equalities: Vec<(Vec<TermId>, String)> = Vec::new();
        let mut replace_all_constraints: Vec<(TermId, TermId, String, String, String)> = Vec::new();

        // First pass: collect all string assignments and constraints from assertions
        for &assertion in &self.assertions {
            if self.collect_string_constraints(
                assertion,
                manager,
                &mut string_assignments,
                &mut length_constraints,
                &mut concat_equalities,
                &mut replace_all_constraints,
            ) {
                return true; // conflicting constant assignments
            }
        }

        // Second pass: Now that all variable assignments are collected, resolve replace_all constraints
        // where source was a variable that is now known
        for &assertion in &self.assertions {
            self.collect_replace_all_with_resolved_vars(
                assertion,
                manager,
                &string_assignments,
                &mut replace_all_constraints,
            );
        }

        // Check 1: Length vs concrete string conflicts (string_04 fix)
        for (&var, &declared_len) in &length_constraints {
            if let Some(value) = string_assignments.get(&var) {
                let actual_len = value.chars().count() as i64;
                if actual_len != declared_len {
                    return true;
                }
            }
        }

        // Check 2: Concatenation consistency against a concrete result.
        for (operands, result_str) in &concat_equalities {
            let result_len = result_str.chars().count() as i64;
            let mut total_known_len = 0i64;
            let mut all_known = true;
            let mut known_prefix = String::new();
            let mut prefix_broken = false;
            let mut known_suffix_parts: Vec<String> = Vec::new();

            for operand in operands {
                let concrete = string_assignments
                    .get(operand)
                    .cloned()
                    .or_else(|| self.get_string_literal(*operand, manager));
                if let Some(value) = concrete {
                    total_known_len += value.chars().count() as i64;
                    if !prefix_broken {
                        known_prefix.push_str(&value);
                    } else {
                        known_suffix_parts.push(value);
                    }
                } else if let Some(&len) = length_constraints.get(operand) {
                    total_known_len += len;
                    prefix_broken = true;
                    all_known = false;
                } else {
                    prefix_broken = true;
                    all_known = false;
                }
            }

            if all_known {
                let mut cat = String::new();
                for op in operands {
                    if let Some(v) = string_assignments.get(op) {
                        cat.push_str(v);
                    } else if let Some(lit) = self.get_string_literal(*op, manager) {
                        cat.push_str(&lit);
                    }
                }
                if cat != *result_str {
                    return true;
                }
            } else {
                // Leading concrete operands must form a prefix of the result
                // (e.g. "a" ++ s = "bcd" is unsat).
                if !known_prefix.is_empty() && !result_str.starts_with(&known_prefix) {
                    return true;
                }
                // Trailing concrete operands (after the first unknown) must form
                // a suffix when they are contiguous at the end.
                if !known_suffix_parts.is_empty() {
                    // Only treat as a firm suffix if the last operand(s) after the
                    // first unknown are all concrete with no further unknowns —
                    // already true by construction of known_suffix_parts only
                    // collecting after prefix_broken, but unknowns in the middle
                    // leave trailing parts that must still match if the trailing
                    // run reaches the end.  Rebuild trailing run from the end.
                    let mut trailing = String::new();
                    for op in operands.iter().rev() {
                        let concrete = string_assignments
                            .get(op)
                            .cloned()
                            .or_else(|| self.get_string_literal(*op, manager));
                        if let Some(v) = concrete {
                            trailing = format!("{v}{trailing}");
                        } else {
                            break;
                        }
                    }
                    if !trailing.is_empty() && !result_str.ends_with(&trailing) {
                        return true;
                    }
                }
                // Lower bound: sum of known pieces cannot exceed result length.
                if total_known_len > result_len {
                    return true;
                }
            }
        }

        // Check 3: Replace-all operation semantics (string_08 fix)
        // If we have replace_all(s, old, new) = result, with s, old, new, result all known,
        // verify that the operation produces the expected result
        for (result_var, source_var, source_val, pattern, replacement) in &replace_all_constraints {
            // Check if result is assigned to a concrete value
            if let Some(result_val) = string_assignments.get(result_var) {
                // If source contains the pattern and pattern != replacement,
                // then result cannot equal source
                if !pattern.is_empty() && source_val.contains(pattern) && pattern != replacement {
                    // Compute actual result
                    let actual_result = source_val.replace(pattern, replacement);
                    if &actual_result != result_val {
                        return true; // Conflict: replace_all result mismatch
                    }
                }
            }
            // Also check if source is concrete but has a length constraint
            // The source_var might not be concrete but the source_val is already collected
            if length_constraints.contains_key(source_var) {
                if let Some(result_val) = string_assignments.get(result_var) {
                    // Source is constrained but result is concrete - check pattern effects
                    if !pattern.is_empty() {
                        // Check if pattern exists in source - if so, result must be different
                        if source_val.contains(pattern) && pattern != replacement {
                            // If source and result are claimed to be equal, but replacement would change it
                            if source_val == result_val.as_str() {
                                return true; // Conflict
                            }
                        }
                    }
                }
            }
        }

        false // No conflict found
    }

    /// Recursively collect string constraints from a term.
    /// Returns `true` if a definite conflict is found during collection
    /// (e.g. the same variable equated to two different string literals).
    fn collect_string_constraints(
        &self,
        term: TermId,
        manager: &TermManager,
        string_assignments: &mut FxHashMap<TermId, String>,
        length_constraints: &mut FxHashMap<TermId, i64>,
        concat_equalities: &mut Vec<(Vec<TermId>, String)>,
        replace_all_constraints: &mut Vec<(TermId, TermId, String, String, String)>,
    ) -> bool {
        let Some(term_data) = manager.get(term) else {
            return false;
        };

        match &term_data.kind {
            // Handle equality: look for string-related equalities
            TermKind::Eq(lhs, rhs) => {
                // Variable = string literal (conflict if already assigned
                // a different value — issue #14).
                if let Some(lit) = self.get_string_literal(*rhs, manager) {
                    if self.is_string_variable(*lhs, manager) {
                        if let Some(prev) = string_assignments.get(lhs) {
                            if prev != &lit {
                                return true;
                            }
                        } else {
                            string_assignments.insert(*lhs, lit);
                        }
                    }
                } else if let Some(lit) = self.get_string_literal(*lhs, manager) {
                    if self.is_string_variable(*rhs, manager) {
                        if let Some(prev) = string_assignments.get(rhs) {
                            if prev != &lit {
                                return true;
                            }
                        } else {
                            string_assignments.insert(*rhs, lit);
                        }
                    }
                }

                // Check for length constraint: (= (str.len x) n)
                if let Some((var, len)) = self.extract_length_constraint(*lhs, *rhs, manager) {
                    length_constraints.insert(var, len);
                } else if let Some((var, len)) = self.extract_length_constraint(*rhs, *lhs, manager)
                {
                    length_constraints.insert(var, len);
                }

                // Check for concat equality: (= (str.++ a b c) "result")
                if let Some(result_str) = self.get_string_literal(*rhs, manager) {
                    if let Some(operands) = self.extract_concat_operands(*lhs, manager) {
                        concat_equalities.push((operands, result_str));
                    }
                } else if let Some(result_str) = self.get_string_literal(*lhs, manager) {
                    if let Some(operands) = self.extract_concat_operands(*rhs, manager) {
                        concat_equalities.push((operands, result_str));
                    }
                }

                // Check for replace_all: (= result (str.replace_all s old new))
                if let Some((source, pattern, replacement)) =
                    self.extract_replace_all(*rhs, manager)
                {
                    // Get source value either directly or via variable assignment
                    let source_val = self
                        .get_string_literal(source, manager)
                        .or_else(|| string_assignments.get(&source).cloned());
                    if let Some(source_val) = source_val {
                        if let Some(pattern_val) = self.get_string_literal(pattern, manager) {
                            if let Some(replacement_val) =
                                self.get_string_literal(replacement, manager)
                            {
                                replace_all_constraints.push((
                                    *lhs,
                                    source,
                                    source_val,
                                    pattern_val,
                                    replacement_val,
                                ));
                            }
                        }
                    }
                } else if let Some((source, pattern, replacement)) =
                    self.extract_replace_all(*lhs, manager)
                {
                    // Get source value either directly or via variable assignment
                    let source_val = self
                        .get_string_literal(source, manager)
                        .or_else(|| string_assignments.get(&source).cloned());
                    if let Some(source_val) = source_val {
                        if let Some(pattern_val) = self.get_string_literal(pattern, manager) {
                            if let Some(replacement_val) =
                                self.get_string_literal(replacement, manager)
                            {
                                replace_all_constraints.push((
                                    *rhs,
                                    source,
                                    source_val,
                                    pattern_val,
                                    replacement_val,
                                ));
                            }
                        }
                    }
                }

                // Recursively check children
                if self.collect_string_constraints(
                    *lhs,
                    manager,
                    string_assignments,
                    length_constraints,
                    concat_equalities,
                    replace_all_constraints,
                ) || self.collect_string_constraints(
                    *rhs,
                    manager,
                    string_assignments,
                    length_constraints,
                    concat_equalities,
                    replace_all_constraints,
                ) {
                    return true;
                }
            }

            // Handle And: recurse into all conjuncts
            TermKind::And(args) => {
                for &arg in args {
                    if self.collect_string_constraints(
                        arg,
                        manager,
                        string_assignments,
                        length_constraints,
                        concat_equalities,
                        replace_all_constraints,
                    ) {
                        return true;
                    }
                }
            }

            // Handle other compound terms
            TermKind::Or(args) => {
                for &arg in args {
                    if self.collect_string_constraints(
                        arg,
                        manager,
                        string_assignments,
                        length_constraints,
                        concat_equalities,
                        replace_all_constraints,
                    ) {
                        return true;
                    }
                }
            }

            TermKind::Not(inner) => {
                if self.collect_string_constraints(
                    *inner,
                    manager,
                    string_assignments,
                    length_constraints,
                    concat_equalities,
                    replace_all_constraints,
                ) {
                    return true;
                }
            }

            TermKind::Implies(lhs, rhs) => {
                if self.collect_string_constraints(
                    *lhs,
                    manager,
                    string_assignments,
                    length_constraints,
                    concat_equalities,
                    replace_all_constraints,
                ) || self.collect_string_constraints(
                    *rhs,
                    manager,
                    string_assignments,
                    length_constraints,
                    concat_equalities,
                    replace_all_constraints,
                ) {
                    return true;
                }
            }

            _ => {}
        }
        false
    }

    /// Get string literal value from a term
    fn get_string_literal(&self, term: TermId, manager: &TermManager) -> Option<String> {
        let term_data = manager.get(term)?;
        if let TermKind::StringLit(s) = &term_data.kind {
            Some(s.clone())
        } else {
            None
        }
    }

    /// Check if a term is a string variable (not a literal or operation)
    fn is_string_variable(&self, term: TermId, manager: &TermManager) -> bool {
        let Some(term_data) = manager.get(term) else {
            return false;
        };
        matches!(term_data.kind, TermKind::Var(_))
    }

    /// Extract length constraint: (str.len var) = n
    fn extract_length_constraint(
        &self,
        lhs: TermId,
        rhs: TermId,
        manager: &TermManager,
    ) -> Option<(TermId, i64)> {
        let lhs_data = manager.get(lhs)?;
        let rhs_data = manager.get(rhs)?;

        // Check if lhs is (str.len var) and rhs is an integer constant
        if let TermKind::StrLen(inner) = &lhs_data.kind {
            if let TermKind::IntConst(n) = &rhs_data.kind {
                return n.to_i64().map(|len| (*inner, len));
            }
        }

        None
    }

    /// Extract operands from a concat expression
    fn extract_concat_operands(&self, term: TermId, manager: &TermManager) -> Option<Vec<TermId>> {
        let term_data = manager.get(term)?;

        match &term_data.kind {
            TermKind::StrConcat(lhs, rhs) => {
                let mut operands = Vec::new();
                // Flatten nested concats
                self.flatten_concat(*lhs, manager, &mut operands);
                self.flatten_concat(*rhs, manager, &mut operands);
                Some(operands)
            }
            _ => None,
        }
    }

    /// Flatten a concat tree into a list of operands
    fn flatten_concat(&self, term: TermId, manager: &TermManager, operands: &mut Vec<TermId>) {
        let Some(term_data) = manager.get(term) else {
            operands.push(term);
            return;
        };

        match &term_data.kind {
            TermKind::StrConcat(lhs, rhs) => {
                self.flatten_concat(*lhs, manager, operands);
                self.flatten_concat(*rhs, manager, operands);
            }
            _ => {
                operands.push(term);
            }
        }
    }

    /// Extract replace_all operation: (str.replace_all source pattern replacement)
    fn extract_replace_all(
        &self,
        term: TermId,
        manager: &TermManager,
    ) -> Option<(TermId, TermId, TermId)> {
        let term_data = manager.get(term)?;
        if let TermKind::StrReplaceAll(source, pattern, replacement) = &term_data.kind {
            Some((*source, *pattern, *replacement))
        } else {
            None
        }
    }

    /// Second pass collection for replace_all with resolved variable assignments
    fn collect_replace_all_with_resolved_vars(
        &self,
        term: TermId,
        manager: &TermManager,
        string_assignments: &FxHashMap<TermId, String>,
        replace_all_constraints: &mut Vec<(TermId, TermId, String, String, String)>,
    ) {
        let Some(term_data) = manager.get(term) else {
            return;
        };

        match &term_data.kind {
            TermKind::Eq(lhs, rhs) => {
                // Check for replace_all with variable source that is now resolved
                if let Some((source, pattern, replacement)) =
                    self.extract_replace_all(*rhs, manager)
                {
                    // Try to resolve source from assignments
                    if let Some(source_val) = string_assignments.get(&source) {
                        if let Some(pattern_val) = self.get_string_literal(pattern, manager) {
                            if let Some(replacement_val) =
                                self.get_string_literal(replacement, manager)
                            {
                                // Only add if not already present
                                let entry = (
                                    *lhs,
                                    source,
                                    source_val.clone(),
                                    pattern_val,
                                    replacement_val,
                                );
                                if !replace_all_constraints.contains(&entry) {
                                    replace_all_constraints.push(entry);
                                }
                            }
                        }
                    }
                } else if let Some((source, pattern, replacement)) =
                    self.extract_replace_all(*lhs, manager)
                {
                    // Try to resolve source from assignments
                    if let Some(source_val) = string_assignments.get(&source) {
                        if let Some(pattern_val) = self.get_string_literal(pattern, manager) {
                            if let Some(replacement_val) =
                                self.get_string_literal(replacement, manager)
                            {
                                // Only add if not already present
                                let entry = (
                                    *rhs,
                                    source,
                                    source_val.clone(),
                                    pattern_val,
                                    replacement_val,
                                );
                                if !replace_all_constraints.contains(&entry) {
                                    replace_all_constraints.push(entry);
                                }
                            }
                        }
                    }
                }

                // Recursively check children
                self.collect_replace_all_with_resolved_vars(
                    *lhs,
                    manager,
                    string_assignments,
                    replace_all_constraints,
                );
                self.collect_replace_all_with_resolved_vars(
                    *rhs,
                    manager,
                    string_assignments,
                    replace_all_constraints,
                );
            }
            TermKind::And(args) => {
                for &arg in args {
                    self.collect_replace_all_with_resolved_vars(
                        arg,
                        manager,
                        string_assignments,
                        replace_all_constraints,
                    );
                }
            }
            TermKind::Or(args) => {
                for &arg in args {
                    self.collect_replace_all_with_resolved_vars(
                        arg,
                        manager,
                        string_assignments,
                        replace_all_constraints,
                    );
                }
            }
            TermKind::Not(inner) => {
                self.collect_replace_all_with_resolved_vars(
                    *inner,
                    manager,
                    string_assignments,
                    replace_all_constraints,
                );
            }
            _ => {}
        }
    }

    /// Returns `true` if `kind` is a string-theory operation or predicate whose
    /// value / truth the incomplete string checks above cannot certify.
    ///
    /// These atoms are mapped to fresh SAT variables by `encode.rs` and are
    /// never evaluated by a real string theory, so a positive `Sat` answer that
    /// relies on them is unsound.  Bare string literals are excluded — they only
    /// participate through structural equality, which the EUF core handles.
    fn is_string_theory_atom(kind: &TermKind) -> bool {
        matches!(
            kind,
            TermKind::StrConcat(_, _)
                | TermKind::StrLen(_)
                | TermKind::StrSubstr(_, _, _)
                | TermKind::StrAt(_, _)
                | TermKind::StrContains(_, _)
                | TermKind::StrPrefixOf(_, _)
                | TermKind::StrSuffixOf(_, _)
                | TermKind::StrIndexOf(_, _, _)
                | TermKind::StrReplace(_, _, _)
                | TermKind::StrReplaceAll(_, _, _)
                | TermKind::StrToInt(_)
                | TermKind::IntToStr(_)
                | TermKind::StrInRe(_, _)
        )
    }

    /// Attempt to decide the ground string fragment by constructing and
    /// *verifying* a concrete model with the string theory's ground solver
    /// ([`oxiz_theories::string::solve_ground_string`]).
    ///
    /// Returns `true` only when a concrete assignment to every string variable
    /// makes the whole assertion set evaluate to `true` — a sound `Sat`
    /// certificate. On success the witness is installed into `self.model` so
    /// `(get-model)` / `(get-value …)` work (issue #14). When no such witness
    /// is found it returns `false`, and the caller keeps the honest `Unknown`.
    pub(super) fn ground_string_model_sat(&mut self, manager: &mut TermManager) -> bool {
        match solve_ground_string(manager, &self.assertions) {
            GroundStringOutcome::Sat(assignment) => {
                let mut model = super::types::Model::new();
                for (term, value) in assignment {
                    let lit = manager.mk_string_lit(&value);
                    model.set(term, lit);
                }
                self.model = Some(model);
                true
            }
            GroundStringOutcome::Unknown => false,
        }
    }

    /// Returns `true` when the current assertion set contains any string-theory
    /// atom that the incomplete string conflict checks cannot decide.
    ///
    /// When this holds and no definite string conflict was found, the solver
    /// MUST answer `Unknown` rather than let the SAT core treat the atom as a
    /// free Boolean — the latter would report `Sat` for unsatisfiable formulas
    /// such as `(= s "abc") ∧ (str.contains s "xyz")`.
    pub(super) fn string_atoms_need_theory(&self, manager: &TermManager) -> bool {
        let mut visited: FxHashSet<TermId> = FxHashSet::default();
        let mut stack: Vec<TermId> = self.assertions.clone();
        while let Some(term) = stack.pop() {
            if !visited.insert(term) {
                continue;
            }
            let Some(term_data) = manager.get(term) else {
                continue;
            };
            if Self::is_string_theory_atom(&term_data.kind) {
                return true;
            }
            super::term_walk::collect_structural_children(&term_data.kind, &mut stack);
        }
        false
    }
}
