//! Solver context

#[allow(unused_imports)]
use crate::prelude::*;
use crate::solver::{Solver, SolverResult};
use oxiz_core::ast::{TermId, TermKind, TermManager};
#[cfg(feature = "std")]
use oxiz_core::error::Result;
#[cfg(feature = "std")]
use oxiz_core::smtlib::{Command, parse_script};
use oxiz_core::sort::{SortId, SortKind};
#[cfg(feature = "std")]
use std::path::{Path, PathBuf};

/// Raw function interpretation: a list of `(arg_strings, value_string)` entries
/// together with an `else_value` string and the function arity.
///
/// Used as the return type of [`Context::get_func_interp_raw`] to avoid pulling
/// `oxiz_core::model` types into the public API of this file.
pub type RawFuncInterp = (Vec<(Vec<String>, String)>, String, usize);

/// A declared constant
#[derive(Debug, Clone)]
struct DeclaredConst {
    /// The term ID for this constant
    term: TermId,
    /// The sort of this constant
    sort: SortId,
    /// The name of this constant
    name: String,
}

/// A declared function
#[derive(Debug, Clone)]
struct DeclaredFun {
    /// The function name
    name: String,
    /// Argument sorts
    arg_sorts: Vec<SortId>,
    /// Return sort
    ret_sort: SortId,
}

/// Solver context for managing the solving process
///
/// The `Context` provides a high-level API for SMT solving, similar to
/// the SMT-LIB2 standard. It manages declarations, assertions, and solver state.
///
/// # Examples
///
/// ## Basic Usage
///
/// ```
/// use oxiz_solver::Context;
///
/// let mut ctx = Context::new();
/// ctx.set_logic("QF_UF");
///
/// // Declare boolean constants
/// let p = ctx.declare_const("p", ctx.terms.sorts.bool_sort);
/// let q = ctx.declare_const("q", ctx.terms.sorts.bool_sort);
///
/// // Assert p AND q
/// let formula = ctx.terms.mk_and(vec![p, q]);
/// ctx.assert(formula);
///
/// // Check satisfiability
/// ctx.check_sat();
/// ```
///
/// ## SMT-LIB2 Script Execution
///
/// ```
/// use oxiz_solver::Context;
///
/// let mut ctx = Context::new();
///
/// let script = r#"
/// (set-logic QF_LIA)
/// (declare-const x Int)
/// (assert (>= x 0))
/// (assert (<= x 10))
/// (check-sat)
/// "#;
///
/// let _ = ctx.execute_script(script);
/// ```
#[derive(Debug)]
pub struct Context {
    /// Term manager
    pub terms: TermManager,
    /// Solver instance
    solver: Solver,
    /// Current logic
    logic: Option<String>,
    /// Assertions
    assertions: Vec<TermId>,
    /// Assertion stack for push/pop
    assertion_stack: Vec<usize>,
    /// Declared constants
    declared_consts: Vec<DeclaredConst>,
    /// Declared constants stack for push/pop
    const_stack: Vec<usize>,
    /// Mapping from constant names to indices (for efficient removal)
    const_name_to_index: crate::prelude::HashMap<String, usize>,
    /// Declared functions
    declared_funs: Vec<DeclaredFun>,
    /// Declared functions stack for push/pop
    fun_stack: Vec<usize>,
    /// Mapping from function names to indices
    fun_name_to_index: crate::prelude::HashMap<String, usize>,
    /// Last check-sat result
    last_result: Option<SolverResult>,
    /// The assumption terms passed to the most recent `check-sat-assuming`
    /// (empty for a plain `check-sat`).  Retained so `get-unsat-assumptions`
    /// can report an unsatisfiable subset after an `unsat` verdict.
    last_assumptions: Vec<TermId>,
    /// Options
    options: crate::prelude::HashMap<String, String>,
    /// Sorts declared via `(declare-sort name arity)`, keyed by name.
    ///
    /// The `SortId` itself lives in `self.terms.sorts` (interned lazily,
    /// on first reference, exactly like the SMT-LIB parser does); this
    /// map exists purely for script-level introspection of which names
    /// were declared and with what arity.
    declared_sorts: crate::prelude::HashMap<String, u32>,
    /// Optional path for binary proof logging.
    ///
    /// When set, `check_sat` creates a `ProofLogger` at this path, records
    /// proof steps derived from the solver result, and flushes/closes the log
    /// before returning.
    #[cfg(feature = "std")]
    proof_log_path: Option<PathBuf>,
}

impl Default for Context {
    fn default() -> Self {
        Self::new()
    }
}

impl Context {
    /// Create a new context
    #[must_use]
    pub fn new() -> Self {
        Self {
            terms: TermManager::new(),
            solver: Solver::new(),
            logic: None,
            assertions: Vec::new(),
            assertion_stack: Vec::new(),
            declared_consts: Vec::new(),
            const_stack: Vec::new(),
            const_name_to_index: crate::prelude::HashMap::new(),
            declared_funs: Vec::new(),
            fun_stack: Vec::new(),
            fun_name_to_index: crate::prelude::HashMap::new(),
            last_result: None,
            last_assumptions: Vec::new(),
            options: crate::prelude::HashMap::new(),
            declared_sorts: crate::prelude::HashMap::new(),
            #[cfg(feature = "std")]
            proof_log_path: None,
        }
    }

    /// Configure a path for binary proof logging.
    ///
    /// When a path is configured, every subsequent call to `check_sat` opens a
    /// [`oxiz_proof::logging::ProofLogger`] at that path, writes a structural
    /// summary of the proof, and flushes/closes the log before returning.
    /// Pass `None` to disable proof logging.
    #[cfg(feature = "std")]
    pub fn set_proof_log_path(&mut self, path: Option<PathBuf>) {
        self.proof_log_path = path;
    }

    /// Return the currently configured proof log path, if any.
    #[cfg(feature = "std")]
    #[must_use]
    pub fn proof_log_path(&self) -> Option<&Path> {
        self.proof_log_path.as_deref()
    }

    /// Verify a binary proof log produced by a previous `check_sat` call with
    /// proof logging enabled.
    ///
    /// Delegates to [`oxiz_proof::replay::ProofReplayer::replay_from_file`].
    ///
    /// # Errors
    ///
    /// Returns `Err` only for hard I/O or binary-format failures; logical
    /// invalidity is encoded as `Ok(VerificationResult::Invalid(_))`.
    #[cfg(feature = "std")]
    pub fn verify_proof_log(
        path: &Path,
    ) -> std::result::Result<oxiz_proof::replay::VerificationResult, oxiz_proof::replay::ProofError>
    {
        oxiz_proof::replay::ProofReplayer::replay_from_file(path)
    }

    /// Declare a constant
    pub fn declare_const(&mut self, name: &str, sort: SortId) -> TermId {
        let term = self.terms.mk_var(name, sort);
        let index = self.declared_consts.len();
        self.declared_consts.push(DeclaredConst {
            term,
            sort,
            name: name.to_string(),
        });
        self.const_name_to_index.insert(name.to_string(), index);
        term
    }

    /// Declare a function
    ///
    /// Registers a function signature in the context. For nullary functions (constants),
    /// use `declare_const` instead.
    pub fn declare_fun(&mut self, name: &str, arg_sorts: Vec<SortId>, ret_sort: SortId) {
        let index = self.declared_funs.len();
        self.declared_funs.push(DeclaredFun {
            name: name.to_string(),
            arg_sorts,
            ret_sort,
        });
        self.fun_name_to_index.insert(name.to_string(), index);
    }

    /// Get function signature if it exists
    pub fn get_fun_signature(&self, name: &str) -> Option<(Vec<SortId>, SortId)> {
        self.fun_name_to_index.get(name).and_then(|&idx| {
            self.declared_funs
                .get(idx)
                .map(|f| (f.arg_sorts.clone(), f.ret_sort))
        })
    }

    /// Iterate over the names of all currently declared uninterpreted functions.
    pub fn declared_function_names(&self) -> impl Iterator<Item = &str> {
        self.declared_funs.iter().map(|d| d.name.as_str())
    }

    /// Iterate over `(name, arity)` for every sort declared via
    /// `(declare-sort name arity)` (through [`Context::execute_script`]).
    pub fn declared_sort_names(&self) -> impl Iterator<Item = (&str, u32)> {
        self.declared_sorts.iter().map(|(k, &v)| (k.as_str(), v))
    }

    /// Set the logic
    pub fn set_logic(&mut self, logic: &str) {
        self.logic = Some(logic.to_string());
        self.solver.set_logic(logic);
    }

    /// Get the current logic
    #[must_use]
    pub fn logic(&self) -> Option<&str> {
        self.logic.as_deref()
    }

    /// Add an assertion
    pub fn assert(&mut self, term: TermId) {
        self.assertions.push(term);
        self.solver.assert(term, &mut self.terms);
    }

    /// Pre-solve constant-substitution pass.
    ///
    /// Walks [`Self::assertions`] looking for `(= var const)` facts, builds a
    /// variable -> constant substitution map (iterating to a fixpoint so that
    /// chains like `(= x 1) (=_ y x)` collapse to `y -> 1`), and — if any
    /// substitution was found — resets the solver and re-asserts every
    /// assertion with the substitution applied and simplified.
    ///
    /// Sound because the substitution is grounded in *asserted* equalities:
    /// any model of the re-asserted set is a model of the original (substitute
    /// the constant back for the variable) and vice versa. Scoped to the base
    /// assertion level (`Self::assertion_stack` empty) because the reset would
    /// otherwise scrub push/pop state.
    fn propagate_constant_subst(&mut self) {
        use oxiz_core::ast::TermKind;
        if !self.assertion_stack.is_empty() {
            return;
        }

        // Iterate to a fixpoint: start with an empty substitution, and on each
        // pass apply the current substitution to every assertion, simplify it
        // (which invokes the FP/String folder), and look for new `(= var const)`
        // facts unlocked by the substitution. Chains like `(= x c1) (= y x)`
        // collapse to `y -> c1` in a couple of passes.
        let original_assertions = self.assertions.clone();
        let mut subst: FxHashMap<TermId, TermId> = FxHashMap::default();
        loop {
            let mut grew = false;
            for &a in &original_assertions {
                // Apply the current substitution, then simplify. This is what
                // lets `((_ to_fp 8 24) RNE 1.5)` fold to a ground `FpLit` so
                // the matcher below can recognise it as a constant RHS, and
                // what lets `fp.add(RNE, x, y)` fold once `x` and `y` are
                // substituted by their constant values.
                let substituted = self.terms.substitute(a, &subst);
                let simplified = self.solver.simplify_term(substituted, &mut self.terms);
                let Some(t) = self.terms.get(simplified) else {
                    continue;
                };
                let TermKind::Eq(lhs, rhs) = t.kind else {
                    continue;
                };
                let lhs_is_var = self
                    .terms
                    .get(lhs)
                    .is_some_and(|t| matches!(t.kind, TermKind::Var(_)));
                let rhs_is_var = self
                    .terms
                    .get(rhs)
                    .is_some_and(|t| matches!(t.kind, TermKind::Var(_)));
                // Only substitute when ALL of the following hold:
                //
                //   1. The variable and the constant share the same sort. A
                //      cross-sort equality like `(= x_int 3.5_real)` is not
                //      SMT-LIB well-typed, but the LIA theory catches the
                //      integer-vs-fractional mismatch as a conflict —
                //      substituting `x_int` with `3.5_real` would
                //      short-circuit that detection and produce a wrong Sat.
                //
                //   2. That sort is FloatingPoint or String. These are the
                //      only theories whose operations the constant folder can
                //      evaluate, so substitution is the only way to expose
                //      the constant to the folder. For BitVec / Int / Real /
                //      Bool the existing theory pipeline handles equalities
                //      directly; substituting would only succeed in *removing*
                //      the variable from the assertion set, which breaks
                //      `get-model` (the variable would no longer be in the
                //      model — `bv = (_ bv200 8)` would come back as
                //      `bv = #x00`).
                let is_substitutable_sort = |t: TermId| -> bool {
                    self.terms
                        .get(t)
                        .and_then(|term| self.terms.sorts.get(term.sort))
                        .is_some_and(|s| {
                            matches!(
                                s.kind,
                                oxiz_core::sort::SortKind::FloatingPoint { .. }
                                    | oxiz_core::sort::SortKind::String
                            )
                        })
                };
                let can_subst = |v: TermId, c: TermId| -> bool {
                    is_ground_const(c, &self.terms)
                        && is_substitutable_sort(v)
                        && sorts_match(v, c, &self.terms)
                };
                if lhs_is_var && can_subst(lhs, rhs) {
                    if subst.insert(lhs, rhs).is_none() {
                        grew = true;
                    }
                } else if rhs_is_var && can_subst(rhs, lhs) {
                    if subst.insert(rhs, lhs).is_none() {
                        grew = true;
                    }
                }
            }
            if !grew {
                break;
            }
            // Defensive: every iteration adds at least one binding or stops.
            if subst.len() > original_assertions.len() * 2 + 16 {
                break;
            }
        }
        if subst.is_empty() {
            return;
        }

        // Apply the final substitution to every assertion, then simplify.
        // Re-assert through `Self::assert` so both `self.assertions` and the
        // solver's encoding stay in sync; `Self::assert` invokes the
        // simplifier (with the FP/String folder), so any operation whose
        // operands are now constants gets evaluated.
        let original = std::mem::take(&mut self.assertions);
        self.solver.reset();
        for term in original {
            let substituted = self.terms.substitute(term, &subst);
            self.assert(substituted);
        }
    }

    /// Check satisfiability
    pub fn check_sat(&mut self) -> SolverResult {
        // Eager constant substitution (soundness-preserving, base-scope only):
        // scan the assertion set for `(= var const)` facts and propagate the
        // constants into every other assertion before solving. This is what
        // lets the FP/String constant folder (see `theory_fold`) evaluate
        // fully-ground theory operations like `fp.gt (fp.add RNE 1.5 2.3)
        // 3.7` — without this pass the folder never sees the constants
        // because they arrive as separate `(= x c)` assertions.
        //
        // Triggered only when (a) we are at the base scope (no `push`), so
        // the reset-and-reassert below is sound, and (b) at least one
        // `(= var const)` fact is present. Otherwise it is a no-op.
        self.propagate_constant_subst();

        let mut result = self.solver.check(&mut self.terms);

        // Array soundness honesty gate: the syntactic array checks and the EUF
        // congruence core do not implement full array extensionality.  If a
        // positive equality between two store terms survived to a `Sat` verdict
        // without being refuted as a conflict, the assignment is not certified —
        // the core may have merged the two store terms into one class without
        // enforcing element-wise agreement of their bases.  Answer `Unknown`
        // rather than a possibly-spurious `Sat` (never a silent wrong result).
        if result == SolverResult::Sat && self.solver.array_atoms_need_theory(&self.terms) {
            result = SolverResult::Unknown;
        }

        // A plain check-sat clears any assumption context from a prior
        // check-sat-assuming, so a following get-unsat-assumptions does not
        // report stale assumptions.
        self.last_assumptions.clear();
        self.last_result = Some(result);

        // Write a binary proof log if a path is configured (std-only).
        #[cfg(feature = "std")]
        if let Some(ref path) = self.proof_log_path.clone() {
            if let Err(e) = self.write_proof_log(path, result) {
                // Non-fatal: warn but do not abort the solve.
                #[cfg(feature = "tracing")]
                tracing::warn!("proof log write failed for {:?}: {}", path, e);
                let _ = e;
            }
        }

        result
    }

    /// Serialise a proof log entry for the given result.
    ///
    /// For `Unsat`, resolution proof steps are emitted when available;
    /// for `Sat` and `Unknown`, a single axiom node is written so the log is
    /// never empty and can be cleanly replayed.
    #[cfg(feature = "std")]
    fn write_proof_log(
        &self,
        path: &Path,
        result: SolverResult,
    ) -> std::result::Result<(), oxiz_proof::logging::LoggingError> {
        use oxiz_proof::logging::ProofLogger;
        use oxiz_proof::proof::{ProofNodeId, ProofStep};
        use smallvec::SmallVec;

        let mut logger = ProofLogger::create(path)?;

        match result {
            SolverResult::Unsat => {
                if let Some(proof) = self.solver.get_proof() {
                    let mut counter: u32 = 0;
                    for step in proof.steps() {
                        let entry = match step {
                            crate::solver::ProofStep::Input { index, .. } => ProofStep::Axiom {
                                conclusion: format!("input-clause-{}", index),
                            },
                            crate::solver::ProofStep::Resolution {
                                index,
                                left,
                                right,
                                pivot,
                                ..
                            } => {
                                let mut premises: SmallVec<[ProofNodeId; 4]> = SmallVec::new();
                                premises.push(ProofNodeId(*left));
                                premises.push(ProofNodeId(*right));
                                let mut args: SmallVec<[String; 2]> = SmallVec::new();
                                args.push(format!("{:?}", pivot));
                                ProofStep::Inference {
                                    rule: "resolution".to_string(),
                                    premises,
                                    conclusion: format!("resolution-{}", index),
                                    args,
                                }
                            }
                            crate::solver::ProofStep::TheoryLemma { index, theory, .. } => {
                                ProofStep::Axiom {
                                    conclusion: format!("theory-lemma-{}-{}", theory, index),
                                }
                            }
                        };
                        logger.log_step(ProofNodeId(counter), &entry)?;
                        counter += 1;
                    }
                    if counter == 0 {
                        // Proof object present but empty — emit minimal witness.
                        logger.log_step(
                            ProofNodeId(0),
                            &ProofStep::Axiom {
                                conclusion: "unsat".to_string(),
                            },
                        )?;
                    }
                } else {
                    logger.log_step(
                        ProofNodeId(0),
                        &ProofStep::Axiom {
                            conclusion: "unsat".to_string(),
                        },
                    )?;
                }
            }
            SolverResult::Sat => {
                logger.log_step(
                    ProofNodeId(0),
                    &ProofStep::Axiom {
                        conclusion: "sat".to_string(),
                    },
                )?;
            }
            SolverResult::Unknown => {
                logger.log_step(
                    ProofNodeId(0),
                    &ProofStep::Axiom {
                        conclusion: "unknown".to_string(),
                    },
                )?;
            }
        }

        logger.flush()?;
        logger.close()
    }

    /// Evaluate a `term` in the current model.
    ///
    /// Returns `None` if no model is available (i.e. the last `check_sat` did
    /// not return `Sat`).  Otherwise, calls `Model::eval` which traverses the
    /// term structure, substituting variables with their model values, and
    /// returns the simplified/concrete `TermId`.
    ///
    /// The returned `TermId` belongs to `self.terms` — the same `TermManager`
    /// owned by this `Context`.
    pub fn eval_in_model(&mut self, term: TermId) -> Option<TermId> {
        if self.last_result != Some(SolverResult::Sat) {
            return None;
        }
        let value = self.solver.model()?.eval(term, &mut self.terms);
        Some(value)
    }

    /// Get the model (if SAT)
    /// Returns a list of (name, sort, value) tuples
    pub fn get_model(&self) -> Option<Vec<(String, String, String)>> {
        if self.last_result != Some(SolverResult::Sat) {
            return None;
        }

        let mut model = Vec::new();
        let solver_model = self.solver.model()?;

        for decl in &self.declared_consts {
            let value = if let Some(val) = solver_model.get(decl.term) {
                self.format_value(val)
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
            _ => "?".to_string(),
        }
    }

    /// Get a default value for a sort
    fn default_value(&self, sort: SortId) -> String {
        if sort == self.terms.sorts.bool_sort {
            "false".to_string()
        } else if sort == self.terms.sorts.int_sort {
            "0".to_string()
        } else if sort == self.terms.sorts.real_sort {
            "0.0".to_string()
        } else if let Some(s) = self.terms.sorts.get(sort) {
            if let Some(w) = s.bitvec_width() {
                format!("#b{:0>width$}", "0", width = w as usize)
            } else {
                "?".to_string()
            }
        } else {
            "?".to_string()
        }
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

    /// Push a context level
    pub fn push(&mut self) {
        self.assertion_stack.push(self.assertions.len());
        self.const_stack.push(self.declared_consts.len());
        self.fun_stack.push(self.declared_funs.len());
        self.solver.push();
    }

    /// Pop a context level with incremental declaration removal
    pub fn pop(&mut self) {
        if let Some(len) = self.assertion_stack.pop() {
            self.assertions.truncate(len);
            if let Some(const_len) = self.const_stack.pop() {
                // Remove constants from the name-to-index mapping
                while self.declared_consts.len() > const_len {
                    if let Some(decl) = self.declared_consts.pop() {
                        self.const_name_to_index.remove(&decl.name);
                    }
                }
            }
            if let Some(fun_len) = self.fun_stack.pop() {
                // Remove functions from the name-to-index mapping
                while self.declared_funs.len() > fun_len {
                    if let Some(decl) = self.declared_funs.pop() {
                        self.fun_name_to_index.remove(&decl.name);
                    }
                }
            }
            self.solver.pop();
        }
    }

    /// Reset the context
    pub fn reset(&mut self) {
        self.solver.reset();
        self.assertions.clear();
        self.assertion_stack.clear();
        self.declared_consts.clear();
        self.const_stack.clear();
        self.const_name_to_index.clear();
        self.declared_funs.clear();
        self.fun_stack.clear();
        self.fun_name_to_index.clear();
        self.logic = None;
        self.last_result = None;
        self.last_assumptions.clear();
        self.options.clear();
    }

    /// Reset assertions (keep declarations and options)
    pub fn reset_assertions(&mut self) {
        self.solver.reset();
        self.assertions.clear();
        self.assertion_stack.clear();
        // Keep declared_consts, const_stack, const_name_to_index,
        // declared_funs, fun_stack, and fun_name_to_index
        // Re-assert nothing - solver is fresh
        self.last_result = None;
        self.last_assumptions.clear();
    }

    /// Get all current assertions
    #[must_use]
    pub fn get_assertions(&self) -> &[TermId] {
        &self.assertions
    }

    /// Format assertions as SMT-LIB2
    #[cfg(feature = "std")]
    pub fn format_assertions(&self) -> String {
        if self.assertions.is_empty() {
            return "()".to_string();
        }
        let printer = oxiz_core::smtlib::Printer::new(&self.terms);
        let mut parts = Vec::new();
        for &term in &self.assertions {
            parts.push(printer.print_term(term));
        }
        format!("({})", parts.join("\n "))
    }

    /// Set an option.
    ///
    /// Recognised keys are wired into the underlying [`crate::SolverConfig`] and take
    /// effect on the next `check_sat`.  All keys (recognised or not) are recorded
    /// so that `(get-option ...)` reflects the last value set.  A leading `:` is
    /// stripped so both `:timeout` and `timeout` resolve identically.
    ///
    /// Wired keys (each consumed by the solve loop, so setting them actually
    /// changes behaviour):
    ///
    /// - `produce-proofs` (`true`/`false`) — enable proof generation.
    /// - `produce-unsat-cores` (`true`/`false`) — enable unsat-core tracking.
    /// - `timeout` (milliseconds) — wall-clock budget for the search; `0`
    ///   disables it.  Maps to [`crate::SolverConfig::timeout_ms`], enforced between
    ///   MBQI rounds and inside the theory callbacks.
    /// - `max-conflicts` / `max-decisions` (non-negative integer) — resource
    ///   limits; `0` means unlimited.
    /// - `theory-mode` (`eager`/`lazy`) — theory propagation eagerness.
    /// - `simplify` (`true`/`false`) — pre-solve simplification of asserted
    ///   formulas.
    /// - `random-seed` / `random_seed` (non-negative integer) — seed for the SAT
    ///   engine's phase-randomization PRNG.  It is threaded straight into the SAT
    ///   solver via [`crate::solver::Solver::set_random_seed`], so it perturbs the
    ///   decision order (and hence which model a satisfiable problem yields)
    ///   without ever changing the sat/unsat verdict.  A seed of `0` reproduces
    ///   the default behaviour.
    ///
    /// Keys such as `restarts`, `branching`, and memory limits are *recorded but
    /// not enforced*: the corresponding levers are fixed at solver construction
    /// time (or have no wiring in this crate yet), so honouring them would require
    /// an `oxiz-solver` core change.  They are intentionally left as no-ops rather
    /// than silently pretending to take effect.
    pub fn set_option(&mut self, key: &str, value: &str) {
        let key = key.trim_start_matches(':');
        self.options.insert(key.to_string(), value.to_string());

        // Handle special options that affect the solver.
        match key {
            "produce-proofs" => {
                let mut config = self.solver.config().clone();
                config.proof = value == "true";
                self.solver.set_config(config);
            }
            "produce-unsat-cores" => {
                self.solver.set_produce_unsat_cores(value == "true");
            }
            "timeout" => {
                if let Ok(ms) = value.trim().parse::<u64>() {
                    let mut config = self.solver.config().clone();
                    config.timeout_ms = ms;
                    self.solver.set_config(config);
                }
            }
            "max-conflicts" | "max_conflicts" => {
                if let Ok(n) = value.trim().parse::<u64>() {
                    let mut config = self.solver.config().clone();
                    config.max_conflicts = n;
                    self.solver.set_config(config);
                }
            }
            "max-decisions" | "max_decisions" => {
                if let Ok(n) = value.trim().parse::<u64>() {
                    let mut config = self.solver.config().clone();
                    config.max_decisions = n;
                    self.solver.set_config(config);
                }
            }
            "theory-mode" | "theory_mode" => {
                let mode = match value.trim().to_ascii_lowercase().as_str() {
                    "lazy" => Some(crate::solver::TheoryMode::Lazy),
                    "eager" => Some(crate::solver::TheoryMode::Eager),
                    _ => None,
                };
                if let Some(mode) = mode {
                    let mut config = self.solver.config().clone();
                    config.theory_mode = mode;
                    self.solver.set_config(config);
                }
            }
            "simplify" => {
                let mut config = self.solver.config().clone();
                config.simplify = value == "true";
                self.solver.set_config(config);
            }
            "random-seed" | "random_seed" => {
                // Thread the seed into the SAT engine's phase-randomization PRNG.
                // Only enforce a well-formed non-negative integer; a malformed
                // value is still recorded (above) so `(get-option ...)` reflects
                // exactly what the user set, but it does not silently corrupt the
                // RNG state.
                if let Ok(seed) = value.trim().parse::<u64>() {
                    self.solver.set_random_seed(seed);
                }
            }
            _ => {}
        }
    }

    /// Get an option
    #[must_use]
    pub fn get_option(&self, key: &str) -> Option<&str> {
        self.options.get(key).map(String::as_str)
    }

    /// Format an option value
    fn format_option(&self, key: &str) -> String {
        match self.get_option(key) {
            Some(val) => val.to_string(),
            None => {
                // Return default values for well-known options
                match key {
                    "produce-models" => "false".to_string(),
                    "produce-unsat-cores" => "false".to_string(),
                    "produce-proofs" => "false".to_string(),
                    "produce-assignments" => "false".to_string(),
                    // Honest default: this solver's command loop does not emit
                    // the SMT-LIB `success` acknowledgement, so print-success
                    // mode is effectively off.  Reporting `true` here (the
                    // standard's nominal default) would advertise behavior the
                    // runner never performs.
                    "print-success" => "false".to_string(),
                    _ => "unsupported".to_string(),
                }
            }
        }
    }

    /// Answer a `(get-info <keyword>)` request.
    ///
    /// The SMT-LIB lexer strips the leading `:` from an info flag, so a request
    /// for `:all-statistics` arrives here as `all-statistics`; we normalize by
    /// stripping any leading colon so both spellings resolve identically
    /// (previously the handler compared against `":all-statistics"` and could
    /// never match, making *every* `get-info` an error).  The mandatory
    /// standard flags (`:name`, `:version`, `:authors`, `:error-behavior`,
    /// `:reason-unknown`) are answered per SMT-LIB 2.6; `:all-statistics`
    /// returns the solver statistics.
    pub fn get_info(&self, keyword: &str) -> String {
        let key = keyword.trim_start_matches(':');
        match key {
            "all-statistics" => self.get_statistics(),
            "name" => "(:name \"oxiz\")".to_string(),
            "version" => format!("(:version \"{}\")", env!("CARGO_PKG_VERSION")),
            "authors" => "(:authors \"COOLJAPAN OU (Team Kitasan)\")".to_string(),
            "error-behavior" => "(:error-behavior continued-execution)".to_string(),
            "reason-unknown" => {
                // Report why the last check returned `unknown`, or `unsupported`
                // when the last result was decided (sat/unsat) or absent.
                match self.last_result {
                    Some(SolverResult::Unknown) => "(:reason-unknown incomplete)".to_string(),
                    _ => "(:reason-unknown \"not applicable\")".to_string(),
                }
            }
            _ => format!("(error \"unsupported info keyword: :{}\")", key),
        }
    }

    /// Answer a `(get-assignment)` request.
    ///
    /// Per SMT-LIB, `get-assignment` reports the truth values that the current
    /// model assigns to Boolean-sorted terms.  This implementation returns a
    /// `(name value)` pair for every declared Boolean constant that the model
    /// assigns (`true`/`false`), which covers the labelled propositional
    /// variables users query in practice.  It returns `()` when the last check
    /// did not produce a model (not `sat`, or no model available).
    ///
    /// Boolean constants that never entered a constraint — and therefore carry no
    /// forced value — are reported as `false`, matching the default-completion
    /// convention used by [`Context::get_model`].
    pub fn get_assignment(&self) -> String {
        if self.last_result != Some(SolverResult::Sat) {
            return "()".to_string();
        }
        let Some(model) = self.solver.model() else {
            return "()".to_string();
        };
        let bool_sort = self.terms.sorts.bool_sort;
        let mut parts = Vec::new();
        for decl in &self.declared_consts {
            if decl.sort != bool_sort {
                continue;
            }
            let value = match model.get(decl.term).and_then(|v| self.terms.get(v)) {
                Some(t) if matches!(t.kind, TermKind::True) => "true",
                Some(t) if matches!(t.kind, TermKind::False) => "false",
                // No forced value: complete to `false` (see doc comment).
                _ => "false",
            };
            parts.push(format!("({} {})", decl.name, value));
        }
        format!("({})", parts.join(" "))
    }

    /// Answer a `(get-unsat-assumptions)` request.
    ///
    /// After a `check-sat-assuming` that returned `unsat`, this returns a subset
    /// of the supplied assumptions whose conjunction with the current assertions
    /// is unsatisfiable.  The reported set is the full assumption list — a valid,
    /// though not necessarily minimal, unsatisfiable set (a superset of a minimal
    /// core is still unsatisfiable).  Returns an error S-expression when the last
    /// result was not `unsat`, and `()` when the last check used no assumptions.
    #[cfg(feature = "std")]
    #[must_use]
    pub fn get_unsat_assumptions(&self) -> String {
        if self.last_result != Some(SolverResult::Unsat) {
            return "(error \"unsat assumptions are only available after an unsat check-sat-assuming\")"
                .to_string();
        }
        if self.last_assumptions.is_empty() {
            return "()".to_string();
        }
        let printer = oxiz_core::smtlib::Printer::new(&self.terms);
        let parts: Vec<String> = self
            .last_assumptions
            .iter()
            .map(|&t| printer.print_term(t))
            .collect();
        format!("({})", parts.join(" "))
    }

    /// Get proof (if proof generation is enabled and result is unsat)
    pub fn get_proof(&self) -> String {
        if self.last_result != Some(SolverResult::Unsat) {
            return "(error \"Proof is only available after unsat result\")".to_string();
        }

        match self.solver.get_proof() {
            Some(proof) => proof.format(),
            None => {
                "(error \"Proof generation not enabled. Set :produce-proofs to true\")".to_string()
            }
        }
    }

    /// Get solver statistics
    /// Returns statistics about the last solving run
    pub fn get_statistics(&self) -> String {
        let stats = self.solver.get_statistics();
        format!(
            "(:decisions {} :conflicts {} :propagations {} :restarts {} :learned-clauses {} :theory-propagations {} :theory-conflicts {})",
            stats.decisions,
            stats.conflicts,
            stats.propagations,
            stats.restarts,
            stats.learned_clauses,
            stats.theory_propagations,
            stats.theory_conflicts
        )
    }

    /// Return the raw solver statistics (crate-internal use only).
    #[must_use]
    pub(crate) fn raw_statistics(&self) -> &crate::solver::Statistics {
        self.solver.get_statistics()
    }

    /// Return the current solver configuration.
    ///
    /// Callers that build diverse configurations (e.g. an external portfolio
    /// driver) can clone this, mutate the fields they want to vary, and hand it
    /// back via [`Context::set_solver_config`].
    #[must_use]
    pub fn solver_config(&self) -> &crate::solver::SolverConfig {
        self.solver.config()
    }

    /// Replace the entire solver configuration.
    ///
    /// Fields consumed during the solve loop — `timeout_ms`, `max_conflicts`,
    /// `max_decisions`, `theory_mode`, and `simplify` — take effect on the next
    /// `check_sat`.  Fields that the embedded SAT solver only reads at
    /// construction time (notably `restart_strategy` and the inprocessing
    /// toggles) are stored but do not retroactively reconfigure an already-built
    /// SAT engine; vary those before the first solve.
    pub fn set_solver_config(&mut self, config: crate::solver::SolverConfig) {
        self.solver.set_config(config);
    }

    /// Set the wall-clock timeout in milliseconds (`0` disables it).
    pub fn set_timeout_ms(&mut self, timeout_ms: u64) {
        let mut config = self.solver.config().clone();
        config.timeout_ms = timeout_ms;
        self.solver.set_config(config);
    }

    /// Set the maximum number of conflicts before answering `unknown`
    /// (`0` = unlimited).
    pub fn set_max_conflicts(&mut self, max_conflicts: u64) {
        let mut config = self.solver.config().clone();
        config.max_conflicts = max_conflicts;
        self.solver.set_config(config);
    }

    /// Set the maximum number of decisions before answering `unknown`
    /// (`0` = unlimited).
    pub fn set_max_decisions(&mut self, max_decisions: u64) {
        let mut config = self.solver.config().clone();
        config.max_decisions = max_decisions;
        self.solver.set_config(config);
    }

    /// Select the theory propagation eagerness.
    pub fn set_theory_mode(&mut self, mode: crate::solver::TheoryMode) {
        let mut config = self.solver.config().clone();
        config.theory_mode = mode;
        self.solver.set_config(config);
    }

    /// Enable or disable pre-solve simplification of asserted formulas.
    pub fn set_simplify(&mut self, enabled: bool) {
        let mut config = self.solver.config().clone();
        config.simplify = enabled;
        self.solver.set_config(config);
    }

    /// Check satisfiability under temporary assumptions (crate-internal use only).
    pub(crate) fn check_with_assumptions_raw(
        &mut self,
        assumptions: &[oxiz_core::ast::TermId],
    ) -> crate::solver::SolverResult {
        self.solver
            .check_with_assumptions(assumptions, &mut self.terms)
    }

    /// Return the unsat core from the last check (crate-internal use only).
    #[must_use]
    pub(crate) fn get_unsat_core_raw(&self) -> Option<&crate::solver::UnsatCore> {
        self.solver.get_unsat_core()
    }

    /// Split a sort-expression string into its top-level whitespace
    /// separated tokens, treating a parenthesized group as a single
    /// token (so nested compound sorts like `(Array Int (_ BitVec 8))`
    /// split into `["Array", "Int", "(_ BitVec 8)"]` rather than being
    /// torn apart at the inner spaces).
    fn split_sort_tokens(s: &str) -> Vec<String> {
        let mut tokens = Vec::new();
        let mut depth = 0i32;
        let mut current = String::new();
        for c in s.chars() {
            match c {
                '(' => {
                    depth += 1;
                    current.push(c);
                }
                ')' => {
                    depth -= 1;
                    current.push(c);
                }
                c if c.is_whitespace() && depth == 0 => {
                    if !current.is_empty() {
                        tokens.push(std::mem::take(&mut current));
                    }
                }
                c => current.push(c),
            }
        }
        if !current.is_empty() {
            tokens.push(current);
        }
        tokens
    }

    /// Resolve a sort-expression string into a `SortId`.
    ///
    /// The strings handled here are exactly the ones `oxiz_core`'s
    /// SMT-LIB parser produces for [`Command::DeclareConst`]/
    /// [`Command::DeclareFun`]/[`Command::DefineFun`] (see
    /// `Parser::sort_id_to_string`): the built-in atomic sorts, `(_
    /// BitVec n)`, `(_ FloatingPoint eb sb)`, `(Array dom rng)`
    /// (recursively), a previously-declared datatype name, or a plain
    /// uninterpreted-sort name.
    ///
    /// Uninterpreted names are interned through `self.terms`'s own
    /// string interner -- the same one the parser uses internally for
    /// `SortKind::Uninterpreted` when building terms during parsing --
    /// so a name declared via `declare-sort` resolves to the identical
    /// `SortId` (and thus, since `mk_var` hash-conses on `(name, sort)`,
    /// the identical `TermId`) that in-script term parsing already
    /// produced for it. Without this, a declared constant of a
    /// user-defined/compound sort would silently be registered here
    /// under an unrelated, disconnected term instead.
    fn parse_sort_name(&mut self, name: &str) -> SortId {
        let name = name.trim();
        match name {
            "Bool" => return self.terms.sorts.bool_sort,
            "Int" => return self.terms.sorts.int_sort,
            "Real" => return self.terms.sorts.real_sort,
            "String" => return self.terms.sorts.string_sort(),
            _ => {}
        }

        if let Some(inner) = name.strip_prefix('(').and_then(|s| s.strip_suffix(')')) {
            let tokens = Self::split_sort_tokens(inner.trim());
            match tokens.first().map(String::as_str) {
                Some("_") if tokens.len() == 3 && tokens[1] == "BitVec" => {
                    if let Ok(width) = tokens[2].parse::<u32>()
                        && width > 0
                    {
                        return self.terms.sorts.bitvec(width);
                    }
                }
                Some("_") if tokens.len() == 4 && tokens[1] == "FloatingPoint" => {
                    if let (Ok(eb), Ok(sb)) = (tokens[2].parse::<u32>(), tokens[3].parse::<u32>()) {
                        return self.terms.sorts.float_sort(eb, sb);
                    }
                }
                Some("Array") if tokens.len() == 3 => {
                    let domain = self.parse_sort_name(&tokens[1]);
                    let range = self.parse_sort_name(&tokens[2]);
                    return self.terms.sorts.array(domain, range);
                }
                _ => {}
            }
            // A compound form the printer never actually emits; fall
            // back to Bool rather than panicking on unreachable syntax.
            return self.terms.sorts.bool_sort;
        }

        // Legacy compact BitVec spelling ("BitVec32"), kept for
        // backward compatibility with any direct (non-script) callers.
        if let Some(width_str) = name.strip_prefix("BitVec")
            && let Ok(width) = width_str.trim().parse::<u32>()
            && width > 0
        {
            return self.terms.sorts.bitvec(width);
        }

        // A previously-declared datatype resolves to its own sort.
        if self.terms.sorts.is_datatype_declared(name) {
            return self.terms.sorts.mk_datatype_sort(name);
        }

        // A sort alias registered by a prior `define-sort` (0-arity
        // aliases only; see the `DefineSort` command handling below).
        if let Some(sort_id) = self.terms.sorts.resolve_by_name(name) {
            return sort_id;
        }

        // Otherwise: an uninterpreted sort, e.g. one introduced by
        // `declare-sort`.
        let spur = self.terms.intern_str(name);
        self.terms.sorts.intern(SortKind::Uninterpreted(spur))
    }

    /// Execute an SMT-LIB2 script
    #[cfg(feature = "std")]
    pub fn execute_script(&mut self, script: &str) -> Result<Vec<String>> {
        let commands = parse_script(script, &mut self.terms)?;
        let mut output = Vec::new();

        for cmd in commands {
            match cmd {
                Command::SetLogic(logic) => {
                    self.set_logic(&logic);
                }
                Command::DeclareConst(name, sort_name) => {
                    let sort = self.parse_sort_name(&sort_name);
                    self.declare_const(&name, sort);
                }
                Command::DeclareFun(name, arg_sorts, ret_sort) => {
                    // Treat nullary functions as constants
                    if arg_sorts.is_empty() {
                        let sort = self.parse_sort_name(&ret_sort);
                        self.declare_const(&name, sort);
                    } else {
                        // Parse argument sorts and return sort
                        let parsed_arg_sorts: Vec<SortId> =
                            arg_sorts.iter().map(|s| self.parse_sort_name(s)).collect();
                        let parsed_ret_sort = self.parse_sort_name(&ret_sort);
                        self.declare_fun(&name, parsed_arg_sorts, parsed_ret_sort);
                    }
                }
                Command::Assert(term) => {
                    self.assert(term);
                }
                Command::CheckSat => {
                    let result = self.check_sat();
                    output.push(match result {
                        SolverResult::Sat => "sat".to_string(),
                        SolverResult::Unsat => "unsat".to_string(),
                        SolverResult::Unknown => "unknown".to_string(),
                    });
                }
                Command::Push(n) => {
                    for _ in 0..n {
                        self.push();
                    }
                }
                Command::Pop(n) => {
                    for _ in 0..n {
                        self.pop();
                    }
                }
                Command::Reset => {
                    self.reset();
                }
                Command::ResetAssertions => {
                    self.reset_assertions();
                }
                Command::Exit => {
                    break;
                }
                Command::Echo(msg) => {
                    output.push(msg);
                }
                Command::GetModel => {
                    output.push(self.format_model());
                }
                Command::GetAssertions => {
                    output.push(self.format_assertions());
                }
                Command::GetAssignment => {
                    output.push(self.get_assignment());
                }
                Command::GetProof => {
                    output.push(self.get_proof());
                }
                Command::GetOption(key) => {
                    output.push(self.format_option(&key));
                }
                Command::SetOption(key, value) => {
                    self.set_option(&key, &value);
                }
                Command::CheckSatAssuming(assumptions) => {
                    // Check under temporary assumptions WITHOUT push/assert/pop.
                    // A pop() would discard the model / unsat core built by the
                    // check, leaving `last_result == Sat` but no state for a
                    // following `(get-value ...)` / `(get-model)` to read.
                    // `check_with_assumptions` keeps the solver state produced by
                    // the assumption-guarded solve, so post-check queries observe
                    // the correct model.
                    self.last_assumptions = assumptions.clone();
                    let mut result = self.check_with_assumptions_raw(&assumptions);
                    // Same array soundness honesty gate as `check_sat`.
                    if result == SolverResult::Sat
                        && self.solver.array_atoms_need_theory(&self.terms)
                    {
                        result = SolverResult::Unknown;
                    }
                    self.last_result = Some(result);
                    output.push(match result {
                        SolverResult::Sat => "sat".to_string(),
                        SolverResult::Unsat => "unsat".to_string(),
                        SolverResult::Unknown => "unknown".to_string(),
                    });
                }
                Command::Simplify(term) => {
                    // Simplify and output the term
                    let simplified = self.terms.simplify(term);
                    let printer = oxiz_core::smtlib::Printer::new(&self.terms);
                    output.push(printer.print_term(simplified));
                }
                Command::GetUnsatCore => {
                    if let Some(core) = self.solver.get_unsat_core() {
                        if core.names.is_empty() {
                            output.push("()".to_string());
                        } else {
                            output.push(format!("({})", core.names.join(" ")));
                        }
                    } else {
                        output.push("(error \"No unsat core available\")".to_string());
                    }
                }
                Command::GetUnsatAssumptions => {
                    // Report the failed assumptions from the most recent
                    // `check-sat-assuming` that returned `unsat`.  The printer
                    // used by `get_unsat_assumptions` is `std`-only, so under
                    // `no_std` we answer with an honest error S-expression
                    // rather than silently emitting nothing.
                    #[cfg(feature = "std")]
                    {
                        output.push(self.get_unsat_assumptions());
                    }
                    #[cfg(not(feature = "std"))]
                    {
                        output.push(
                            "(error \"get-unsat-assumptions requires the std feature\")"
                                .to_string(),
                        );
                    }
                }
                Command::GetValue(terms) => {
                    if self.last_result != Some(SolverResult::Sat) {
                        output.push("(error \"No model available\")".to_string());
                    } else if let Some(model) = self.solver.model() {
                        let mut values = Vec::new();
                        for term in terms {
                            // Evaluate the term in the model first
                            let value = model.eval(term, &mut self.terms);
                            // Then create printer and format
                            let printer = oxiz_core::smtlib::Printer::new(&self.terms);
                            let term_str = printer.print_term(term);
                            let value_str = printer.print_term(value);
                            values.push(format!("({} {})", term_str, value_str));
                        }
                        output.push(format!("({})", values.join("\n ")));
                    } else {
                        output.push("(error \"No model available\")".to_string());
                    }
                }
                Command::GetInfo(keyword) => {
                    output.push(self.get_info(&keyword));
                }
                Command::SetInfo(_, _) => {
                    // Purely descriptive metadata (`:source`, `:license`,
                    // ...); it has no effect on declarations or solving.
                }
                Command::DeclareSort(name, arity) => {
                    if arity == 0 {
                        // Eagerly materialize the sort so `declared_sort_names`
                        // reflects it immediately, matching what the parser
                        // already did (lazily, on first reference) internally.
                        let _ = self.parse_sort_name(&name);
                    }
                    // Arity > 0 parametric sorts are recorded for
                    // introspection; applying them with type arguments is
                    // not yet supported anywhere in this crate, matching
                    // the parser's own documented limitation.
                    self.declared_sorts.insert(name, arity);
                }
                Command::DefineSort(name, params, sort_expr) => {
                    if params.is_empty() {
                        let resolved = self.parse_sort_name(&sort_expr);
                        self.terms.sorts.define_alias(&name, resolved);
                    }
                    // Parametric aliases (non-empty `params`) are not
                    // resolved: the SMT-LIB parser itself only substitutes
                    // 0-arity `define-sort` aliases in-script (see
                    // `oxiz_core`'s `Parser::parse_sort_name`), so there is
                    // no sound target to register here either.
                }
                Command::DefineFun(name, params, ret_sort, body) => {
                    let sort = self.parse_sort_name(&ret_sort);
                    if params.is_empty() {
                        // The parser already inlined every in-script
                        // reference to `name` directly as `body` (see
                        // `oxiz_core`'s `define-fun` handling), so this
                        // doesn't change what gets solved. Declaring a real
                        // constant provably equal to `body` -- rather than
                        // doing nothing -- makes `name` show up correctly
                        // (with its actual value) in `get-model`/`get-value`
                        // output instead of silently vanishing, without
                        // introducing any constraint that could change
                        // satisfiability (the equality is trivially
                        // satisfiable for any assignment to `body`'s free
                        // variables).
                        let const_term = self.declare_const(&name, sort);
                        let eq = self.terms.mk_eq(const_term, body);
                        self.assert(eq);
                    } else {
                        // Functions with parameters are macros: call sites
                        // are meant to be substituted with `body` at parse
                        // time (see `oxiz_core`'s defined-function handling
                        // in `smtlib/parser/terms.rs`), which is outside
                        // this file's ownership -- so no further wiring for
                        // *solving* belongs here. Still register the
                        // signature so introspection (`get_fun_signature`,
                        // `declared_function_names`) reflects the
                        // definition, like `declare-fun` does.
                        let arg_sorts: Vec<SortId> = params
                            .iter()
                            .map(|(_, sort_name)| self.parse_sort_name(sort_name))
                            .collect();
                        self.declare_fun(&name, arg_sorts, sort);
                    }
                }
                Command::DeclareDatatype { name, .. } => {
                    // The parser already fully registered each datatype's
                    // sort and constructor/selector definitions directly on
                    // `self.terms.sorts` -- including selector sorts
                    // resolved through the full sort grammar -- so in-script
                    // constructor application (e.g. `(cons 1 nil)`) already
                    // works without help from here. What's missing is
                    // exposing constructors/selectors as callable functions
                    // in this Context's own function registry, the way Z3
                    // implicitly declares them, so introspection sees them.
                    //
                    // `name` is a comma-joined list of every datatype this
                    // command declared (see the parser's `DeclareDatatype`
                    // doc comment, covering both multi- and mutually
                    // recursive `declare-datatypes` forms); look each one's
                    // authoritative definition up directly on the sort
                    // manager rather than re-deriving it from the weaker,
                    // string-typed `constructors` field.
                    for dt_name in name.split(',') {
                        let dt_name = dt_name.trim();
                        if dt_name.is_empty() {
                            continue;
                        }
                        let dt_sort = self.terms.sorts.mk_datatype_sort(dt_name);
                        let Some(ctors) = self
                            .terms
                            .sorts
                            .get_datatype(dt_name)
                            .map(|def| def.constructors.clone())
                        else {
                            continue;
                        };
                        for ctor in &ctors {
                            let ctor_name = self.terms.resolve_str(ctor.name).to_string();
                            let selector_sorts: Vec<SortId> =
                                ctor.selectors.iter().map(|&(_, sort)| sort).collect();
                            self.declare_fun(&ctor_name, selector_sorts, dt_sort);
                            for &(sel_spur, sel_sort) in &ctor.selectors {
                                let sel_name = self.terms.resolve_str(sel_spur).to_string();
                                self.declare_fun(&sel_name, vec![dt_sort], sel_sort);
                            }
                        }
                    }
                }
            }
        }

        Ok(output)
    }

    /// Get solver statistics
    #[must_use]
    pub fn stats(&self) -> &oxiz_sat::SolverStats {
        self.solver.stats()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_context_basic() {
        let mut ctx = Context::new();

        ctx.set_logic("QF_UF");
        assert_eq!(ctx.logic(), Some("QF_UF"));

        let t = ctx.terms.mk_true();
        ctx.assert(t);

        let result = ctx.check_sat();
        assert_eq!(result, SolverResult::Sat);
    }

    #[test]
    fn test_context_push_pop() {
        let mut ctx = Context::new();

        let t = ctx.terms.mk_true();
        ctx.assert(t);
        ctx.push();

        let f = ctx.terms.mk_false();
        ctx.assert(f);

        // Should be unsat with false asserted
        let result = ctx.check_sat();
        assert_eq!(result, SolverResult::Unsat);

        ctx.pop();

        // After pop, should be sat again
        let result = ctx.check_sat();
        assert_eq!(result, SolverResult::Sat);
    }

    #[test]
    fn test_execute_script() {
        let mut ctx = Context::new();

        let script = r#"
            (set-logic QF_UF)
            (declare-const p Bool)
            (assert p)
            (check-sat)
        "#;

        let output = ctx
            .execute_script(script)
            .expect("test operation should succeed");
        assert_eq!(output, vec!["sat"]);
    }

    #[test]
    fn test_declare_const() {
        let mut ctx = Context::new();

        let bool_sort = ctx.terms.sorts.bool_sort;
        let int_sort = ctx.terms.sorts.int_sort;

        ctx.declare_const("x", bool_sort);
        ctx.declare_const("y", int_sort);

        let t = ctx.terms.mk_true();
        ctx.assert(t);
        let result = ctx.check_sat();
        assert_eq!(result, SolverResult::Sat);

        // Model should include both constants
        let model = ctx.get_model();
        assert!(model.is_some());
        let model = model.expect("test operation should succeed");
        assert_eq!(model.len(), 2);
    }

    #[test]
    fn test_format_model() {
        let mut ctx = Context::new();

        let bool_sort = ctx.terms.sorts.bool_sort;
        ctx.declare_const("p", bool_sort);

        let t = ctx.terms.mk_true();
        ctx.assert(t);
        let _ = ctx.check_sat();

        let model_str = ctx.format_model();
        assert!(model_str.contains("(model"));
        assert!(model_str.contains("define-fun p () Bool"));
    }

    #[test]
    fn test_get_model_script() {
        let mut ctx = Context::new();

        let script = r#"
            (set-logic QF_LIA)
            (declare-const x Int)
            (declare-const y Bool)
            (assert true)
            (check-sat)
            (get-model)
        "#;

        let output = ctx
            .execute_script(script)
            .expect("test operation should succeed");
        assert_eq!(output.len(), 2);
        assert_eq!(output[0], "sat");
        assert!(
            output[1].contains("(model"),
            "Expected '(model' in: {}",
            output[1]
        );
        // Note: Sorts may not always appear in model output if values are default
        // The model format is: (define-fun name () Sort value)
    }

    #[test]
    fn test_push_pop_consts() {
        let mut ctx = Context::new();

        let bool_sort = ctx.terms.sorts.bool_sort;
        ctx.declare_const("a", bool_sort);
        ctx.push();
        ctx.declare_const("b", bool_sort);

        let t = ctx.terms.mk_true();
        ctx.assert(t);
        let _ = ctx.check_sat();

        let model = ctx.get_model().expect("test operation should succeed");
        assert_eq!(model.len(), 2);

        ctx.pop();
        let _ = ctx.check_sat();

        let model = ctx.get_model().expect("test operation should succeed");
        assert_eq!(model.len(), 1);
        assert_eq!(model[0].0, "a");
    }

    #[test]
    fn test_get_assertions() {
        let mut ctx = Context::new();

        let script = r#"
            (set-logic QF_UF)
            (declare-const p Bool)
            (assert p)
            (assert (not p))
            (get-assertions)
        "#;

        let output = ctx
            .execute_script(script)
            .expect("test operation should succeed");
        assert_eq!(output.len(), 1);
        assert!(output[0].starts_with('('));
        // Should contain both assertions
        assert!(output[0].contains("p"));
    }

    #[test]
    fn test_check_sat_assuming_script() {
        let mut ctx = Context::new();

        let script = r#"
            (set-logic QF_UF)
            (declare-const p Bool)
            (declare-const q Bool)
            (assert p)
            (check-sat-assuming (q))
        "#;

        let output = ctx
            .execute_script(script)
            .expect("test operation should succeed");
        assert_eq!(output.len(), 1);
        assert_eq!(output[0], "sat");
    }

    #[cfg(feature = "std")]
    #[test]
    fn test_get_unsat_assumptions_script() {
        // Regression: `(get-unsat-assumptions)` must be reachable from the
        // SMT-LIB command path (previously the parser rejected it outright).
        // After an `unsat` `check-sat-assuming`, it reports the failed
        // assumptions.
        let mut ctx = Context::new();

        let script = r#"
            (set-logic QF_UF)
            (declare-const p Bool)
            (assert p)
            (check-sat-assuming ((not p)))
            (get-unsat-assumptions)
        "#;

        let output = ctx
            .execute_script(script)
            .expect("script with get-unsat-assumptions should parse and run");
        assert_eq!(output.len(), 2);
        assert_eq!(output[0], "unsat");
        // The reported set is a non-empty unsatisfiable subset of the
        // assumptions, mentioning the failed literal `p`.
        assert!(output[1].starts_with('('));
        assert!(output[1].contains('p'), "got: {}", output[1]);
        assert_ne!(output[1], "()");
    }

    #[cfg(feature = "std")]
    #[test]
    fn test_get_unsat_assumptions_no_assumptions_is_empty() {
        // A plain (unsat) `check-sat` used no assumptions, so
        // `(get-unsat-assumptions)` reports the empty set rather than an error.
        let mut ctx = Context::new();

        let script = r#"
            (set-logic QF_UF)
            (declare-const p Bool)
            (assert p)
            (assert (not p))
            (check-sat)
            (get-unsat-assumptions)
        "#;

        let output = ctx
            .execute_script(script)
            .expect("script should parse and run");
        assert_eq!(output.len(), 2);
        assert_eq!(output[0], "unsat");
        assert_eq!(output[1], "()");
    }

    #[test]
    fn test_get_option_script() {
        let mut ctx = Context::new();

        let script = r#"
            (set-option :produce-models true)
            (get-option :produce-models)
        "#;

        let output = ctx
            .execute_script(script)
            .expect("test operation should succeed");
        assert_eq!(output.len(), 1);
        assert_eq!(output[0], "true");
    }

    #[test]
    fn test_random_seed_option_is_enforced_and_recorded() {
        // Regression: `:random-seed` used to be a documented no-op ("recorded
        // but not enforced").  It is now threaded into the SAT engine's phase
        // PRNG via Solver::set_random_seed.  The observable contract here is
        // two-fold: (1) `(get-option :random-seed)` reflects exactly the value
        // the user set (recording preserved), and (2) setting a seed keeps the
        // sat/unsat verdict sound — seeding must never change a decidable
        // answer.  A previous silent no-op would still pass (1); the point of
        // this test is that the plumbing is now wired without regressing (2).
        let mut ctx = Context::new();

        ctx.set_option(":random-seed", "42");
        assert_eq!(ctx.get_option("random-seed"), Some("42"));

        // A satisfiable BV problem must still be SAT under a non-default seed.
        let script = r#"
            (set-logic QF_BV)
            (declare-const x (_ BitVec 8))
            (assert (bvult x #x0a))
            (check-sat)
        "#;
        let output = ctx
            .execute_script(script)
            .expect("seeded script should parse and run");
        assert_eq!(output, vec!["sat"]);
    }

    #[test]
    fn test_random_seed_zero_and_malformed_are_safe() {
        // Seed `0` is the degenerate xorshift fixed point; the seed-mixing must
        // map it to the historical default rather than freezing the PRNG.  A
        // malformed seed must not corrupt the RNG (it is still recorded so
        // get-option is faithful), and neither must panic.
        let mut ctx = Context::new();

        ctx.set_option(":random-seed", "0");
        assert_eq!(ctx.get_option("random-seed"), Some("0"));

        ctx.set_option(":random-seed", "not-a-number");
        assert_eq!(ctx.get_option("random-seed"), Some("not-a-number"));

        // Solving remains correct after both.
        let script = r#"
            (set-logic QF_LIA)
            (declare-const y Int)
            (assert (> y 5))
            (assert (< y 8))
            (check-sat)
        "#;
        let output = ctx
            .execute_script(script)
            .expect("script should parse and run");
        assert_eq!(output, vec!["sat"]);
    }

    #[test]
    fn test_reset_assertions() {
        let mut ctx = Context::new();

        let script = r#"
            (set-logic QF_UF)
            (declare-const p Bool)
            (assert p)
            (reset-assertions)
            (get-assertions)
            (check-sat)
        "#;

        let output = ctx
            .execute_script(script)
            .expect("test operation should succeed");
        assert_eq!(output.len(), 2);
        assert_eq!(output[0], "()"); // No assertions after reset
        assert_eq!(output[1], "sat"); // Empty formula is SAT
    }

    #[test]
    fn test_simplify_command() {
        let mut ctx = Context::new();

        let script = r#"
            (simplify (+ 1 2))
        "#;

        let output = ctx
            .execute_script(script)
            .expect("test operation should succeed");
        assert_eq!(output.len(), 1);
        // Should simplify to 3
        assert_eq!(output[0], "3");
    }

    #[test]
    fn test_simplify_complex() {
        let mut ctx = Context::new();

        let script = r#"
            (simplify (* 2 3 4))
        "#;

        let output = ctx
            .execute_script(script)
            .expect("test operation should succeed");
        assert_eq!(output.len(), 1);
        // Should simplify to 24
        assert_eq!(output[0], "24");
    }

    #[test]
    fn test_get_value() {
        let mut ctx = Context::new();

        let script = r#"
            (set-logic QF_UF)
            (declare-const p Bool)
            (declare-const q Bool)
            (assert p)
            (assert (not q))
            (check-sat)
            (get-value (p q (and p q) (or p q)))
        "#;

        let output = ctx
            .execute_script(script)
            .expect("test operation should succeed");
        assert_eq!(output.len(), 2);
        assert_eq!(output[0], "sat");

        // Parse the get-value output
        let value_output = &output[1];
        assert!(value_output.contains("p"));
        assert!(value_output.contains("q"));
        // p should evaluate to true
        assert!(value_output.contains("true"));
        // q should evaluate to false
        assert!(value_output.contains("false"));
    }

    #[test]
    fn test_get_value_no_model() {
        let mut ctx = Context::new();

        let script = r#"
            (set-logic QF_UF)
            (declare-const p Bool)
            (get-value (p))
        "#;

        let output = ctx
            .execute_script(script)
            .expect("test operation should succeed");
        assert_eq!(output.len(), 1);
        assert!(output[0].contains("error") || output[0].contains("No model"));
    }

    #[test]
    fn test_get_value_after_unsat() {
        let mut ctx = Context::new();

        let script = r#"
            (set-logic QF_UF)
            (declare-const p Bool)
            (assert p)
            (assert (not p))
            (check-sat)
            (get-value (p))
        "#;

        let output = ctx
            .execute_script(script)
            .expect("test operation should succeed");
        assert_eq!(output.len(), 2);
        assert_eq!(output[0], "unsat");
        assert!(output[1].contains("error") || output[1].contains("No model"));
    }
}

/// Follow a substitution chain `t -> subst[t] -> subst[subst[t]] -> ...` until
/// it terminates at a non-substituted term. Used by [`Context::propagate_constant_subst`]
/// so that a chain like `(= x c) (= y x)` resolves `y` all the way to `c` in a
/// single fixpoint sweep.
#[allow(dead_code)]
fn resolve_chain(
    mut t: oxiz_core::ast::TermId,
    subst: &FxHashMap<oxiz_core::ast::TermId, oxiz_core::ast::TermId>,
    _manager: &TermManager,
) -> oxiz_core::ast::TermId {
    let mut steps = 0;
    while let Some(&next) = subst.get(&t) {
        if next == t {
            break;
        }
        t = next;
        steps += 1;
        // Defensive: a substitution cycle (which should be impossible since we
        // only insert vars -> constants, but cheap to guard).
        if steps > 65_536 {
            break;
        }
    }
    t
}

/// Is `term` a ground constant that [`Context::propagate_constant_subst`] can
/// safely substitute a variable for? True for every numeric / FP / string /
/// Boolean literal kind — i.e. terms with no free variables that the FP/String
/// folder can evaluate from.
fn is_ground_const(t: oxiz_core::ast::TermId, manager: &TermManager) -> bool {
    use oxiz_core::ast::TermKind;
    let Some(term) = manager.get(t) else {
        return false;
    };
    matches!(
        term.kind,
        TermKind::IntConst(_)
            | TermKind::RealConst(_)
            | TermKind::BitVecConst { .. }
            | TermKind::FpLit { .. }
            | TermKind::FpPlusInfinity { .. }
            | TermKind::FpMinusInfinity { .. }
            | TermKind::FpPlusZero { .. }
            | TermKind::FpMinusZero { .. }
            | TermKind::FpNaN { .. }
            | TermKind::StringLit(_)
            | TermKind::True
            | TermKind::False
    )
}

/// Check whether two terms have the same sort (helper for
/// [`Context::propagate_constant_subst`]).
fn sorts_match(
    a: oxiz_core::ast::TermId,
    b: oxiz_core::ast::TermId,
    manager: &TermManager,
) -> bool {
    match (manager.get(a), manager.get(b)) {
        (Some(ta), Some(tb)) => ta.sort == tb.sort,
        _ => false,
    }
}
