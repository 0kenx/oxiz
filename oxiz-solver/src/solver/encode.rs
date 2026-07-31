//! Term encoding (Tseitin transformation) for the SMT solver

#[allow(unused_imports)]
use crate::prelude::*;
use num_rational::Rational64;
use num_traits::{One, ToPrimitive, Zero};
use oxiz_core::ast::{collect_subterms, TermId, TermKind, TermManager};
use oxiz_core::sort::SortId;
use oxiz_sat::{Lit, Var};
use smallvec::SmallVec;

use super::Solver;
use super::trail::TrailOp;
use super::types::{
    ArithConstraintType, Constraint, NamedAssertion, ParsedArithConstraint, Polarity, UnsatCore,
};

mod exists_skolem;
pub(crate) mod finite_expand;
mod skolem_candidates;
mod track_theory_vars;

#[cfg(test)]
mod tests;

impl Solver {
    pub(super) fn get_or_create_var(&mut self, term: TermId) -> Var {
        if let Some(&var) = self.term_to_var.get(&term) {
            return var;
        }

        let var = self.sat.new_var();
        self.term_to_var.insert(term, var);
        self.trail.push(TrailOp::VarCreated { var, term });

        while self.var_to_term.len() <= var.index() {
            self.var_to_term.push(TermId::new(0));
        }
        self.var_to_term[var.index()] = term;
        var
    }

    /// Remember that assertion `index` was `term`, under `name` if the caller
    /// gave one.
    ///
    /// # Why this is unconditional
    ///
    /// It used to be gated on `produce_unsat_cores`, which made unsat-core
    /// production silently order-dependent: a session that asserted first and
    /// set `:produce-unsat-cores` afterwards got `unsat` and an *empty* core,
    /// because the names were never written down — and nothing along the way
    /// reported that the option had arrived too late to be honoured.
    ///
    /// The gate belongs on *producing* a core, where it still is
    /// (`Solver::build_unsat_core`, `Solver::build_unsat_core_trivial_false`
    /// and `Solver::minimize_unsat_core` all check the flag), not on
    /// remembering what the caller asserted.  What it saved
    /// was one `Vec` push and one trail entry per assertion — the SAT-level work
    /// of core tracking was never behind this branch — so nothing is paid for
    /// the sessions that never ask for a core beyond the assertion names they
    /// themselves supplied.
    ///
    /// `named_assertions` is only ever searched by `index` (never assumed dense
    /// or aligned with `assertions`), so filling it in for every assertion
    /// changes no lookup.
    fn record_assertion_identity(&mut self, term: TermId, name: Option<String>, index: usize) {
        let na_index = self.named_assertions.len();
        self.named_assertions.push(NamedAssertion {
            term,
            name,
            index: index as u32,
        });
        self.trail
            .push(TrailOp::NamedAssertionAdded { index: na_index });
    }

    /// Record `term`'s Tseitin encoding in [`Solver::encoded_terms`], journalling
    /// the write so [`Solver::pop`] can take back exactly the entries whose
    /// defining clauses the matching `sat.pop()` retracts.
    ///
    /// The journal entry carries the displaced value, which is what makes the
    /// retraction *precise* rather than destructive: an entry widened from
    /// `Positive` to `Both` inside a scope has only the extra implication
    /// direction retracted with that scope, so `pop` must put the narrower
    /// pre-scope coverage back rather than forget the term altogether.
    ///
    /// A write that changes nothing is not journalled — re-encoding a term at
    /// the coverage it already has emits duplicate clauses but no new memo
    /// state, and a trail entry for it would only make `pop` do redundant work.
    fn memoize_encoding(&mut self, term: TermId, lit: Lit, polarity: Polarity) {
        let previous = self.encoded_terms.insert(term, (lit, polarity));
        if previous == Some((lit, polarity)) {
            return;
        }
        self.trail
            .push(TrailOp::EncodedTermAdded { term, previous });
    }

    /// Attach a theory constraint to `var`, journalling the write only when
    /// this scope is the one that introduced it.
    ///
    /// The encoder is re-entrant across assertion scopes: a term first encoded
    /// at an outer level keeps its SAT variable (`get_or_create_var` hits the
    /// cache), so asserting it again inside a `push` re-runs this code for a
    /// variable the outer scope already owns.  Journalling that repeat write
    /// would make the matching `pop` delete a constraint that is still active,
    /// leaving the atom without any theory meaning — the solver then loses the
    /// refutation that depends on it (`(or (= x 1) (= x 2)) ∧ (= x 5)` stopped
    /// being provably `unsat` after such a scope).  Recording only the first
    /// write keeps the trail entry paired with the scope that owns the fact.
    pub(super) fn record_constraint(&mut self, var: Var, constraint: Constraint) {
        if self.var_to_constraint.insert(var, constraint).is_none() {
            self.trail.push(TrailOp::ConstraintAdded { var });
        }
    }

    /// Register a compound Int/Real-sorted term as an opaque arithmetic atom.
    ///
    /// Used for `div`, `mod` and conditional values: the linear solver cannot
    /// express them as a combination of their operands, so each gets its own
    /// theory variable (and hence a model value), and its semantics arrive
    /// separately as the ground axioms asserted by
    /// [`Solver::instantiate_arith_axioms`].  Non-numeric terms are ignored.
    fn register_arith_atom(&mut self, term_id: TermId, sort: SortId, manager: &TermManager) {
        if sort != manager.sorts.int_sort && sort != manager.sorts.real_sort {
            return;
        }
        if self.arith_terms.contains(&term_id) {
            return;
        }
        self.arith_terms.insert(term_id);
        self.trail.push(TrailOp::ArithTermAdded { term: term_id });
        self.arith.intern(term_id);
    }

    /// Parse an arithmetic comparison and extract linear expression.
    /// Returns: (terms with coefficients, constant, constraint_type).
    ///
    /// Results are cached by `reason` (the comparison term id).
    /// `ParsedArithConstraint` is purely structural — it depends only on the
    /// term graph — so the cache is safe to retain across CDCL backtracks.
    pub(super) fn parse_arith_comparison(
        &mut self,
        lhs: TermId,
        rhs: TermId,
        constraint_type: ArithConstraintType,
        reason: TermId,
        manager: &TermManager,
    ) -> Option<ParsedArithConstraint> {
        // Fast path: return cached result if available.
        if let Some(cached) = self.arith_parse_cache.get(&reason) {
            return cached.clone();
        }

        let mut terms: SmallVec<[(TermId, Rational64); 4]> = SmallVec::new();
        let mut constant = Rational64::zero();

        // Parse LHS (add positive coefficients)
        let lhs_ok =
            self.extract_linear_terms(lhs, Rational64::one(), &mut terms, &mut constant, manager);
        if lhs_ok.is_none() {
            self.arith_parse_cache.insert(reason, None);
            return None;
        }

        // Parse RHS (subtract, so coefficients are negated)
        // For lhs OP rhs, we want lhs - rhs OP 0
        let rhs_ok =
            self.extract_linear_terms(rhs, -Rational64::one(), &mut terms, &mut constant, manager);
        if rhs_ok.is_none() {
            self.arith_parse_cache.insert(reason, None);
            return None;
        }

        // Combine like terms
        let mut combined: FxHashMap<TermId, Rational64> = FxHashMap::default();
        for (term, coef) in terms {
            *combined.entry(term).or_insert(Rational64::zero()) += coef;
        }

        // Remove zero coefficients
        let final_terms: SmallVec<[(TermId, Rational64); 4]> =
            combined.into_iter().filter(|(_, c)| !c.is_zero()).collect();

        let result = ParsedArithConstraint {
            terms: final_terms,
            constant: -constant, // Move constant to RHS
            constraint_type,
            reason_term: reason,
        };

        self.arith_parse_cache.insert(reason, Some(result.clone()));
        Some(result)
    }

    /// Extract linear terms from an arithmetic expression.
    /// Returns None if the term is not linear.
    ///
    /// # Explicit stack, not native recursion
    ///
    /// The walk uses an explicit work-stack.  The recursive version's frames
    /// stacked *on top of* [`Solver::encode_depth`]'s at the leaf (the encoder
    /// calls [`Solver::parse_arith_comparison`] from a comparison arm), so the
    /// true worst-case native stack was `encode_depth × cap + this walk × its
    /// own depth` — the encoder's depth cap never bounded it.  Worse, the
    /// encoder does not descend into arithmetic operands at all: a single
    /// shallow atom `(< deep-arith-chain 0)` reached this walk with the whole
    /// chain, and `parse_arith_comparison` is also called from theory paths
    /// (e.g. `TermKind::Eq`) on MBQI instantiation results that never pass the
    /// assert-time depth gate.  A stack overflow here is a fatal process abort
    /// no `Result` can report, and a depth cap would be dishonest: `None`
    /// means "not linear", so a capped deep-but-linear chain would silently
    /// drop the atom's theory meaning and gate the whole problem to `Unknown`.
    ///
    /// Only the `Mul` arm carries resume state: a product is linear iff at
    /// most one factor is non-constant, so each factor is evaluated into a
    /// *fresh* accumulation context and classified when it completes.  The
    /// suspended parent context travels inside the `Mul` frame itself, which
    /// makes the "stack empty at finalize" case unrepresentable — no `pop().
    /// expect(..)` is needed anywhere.
    ///
    /// On failure the caller's buffers are untouched (the recursive version
    /// left partial writes behind); the only caller,
    /// [`Solver::parse_arith_comparison`], discards the buffers on `None`, so
    /// this is unobservable.
    pub(super) fn extract_linear_terms(
        &self,
        term_id: TermId,
        scale: Rational64,
        terms: &mut SmallVec<[(TermId, Rational64); 4]>,
        constant: &mut Rational64,
        manager: &TermManager,
    ) -> Option<()> {
        /// One linear-accumulation context: the `(term, coefficient)` pairs
        /// and folded constant of the sub-expression currently being walked.
        struct Level {
            terms: SmallVec<[(TermId, Rational64); 4]>,
            constant: Rational64,
        }
        impl Level {
            fn new() -> Self {
                Level {
                    terms: SmallVec::new(),
                    constant: Rational64::zero(),
                }
            }
        }
        /// Resume state for one `Mul` node.  A product is linear iff at most
        /// one factor is non-constant; each factor is evaluated into a fresh
        /// [`Level`] and classified here when it completes.  The factor must
        /// be linear-as-a-whole (exactly one variable term, no additive
        /// constant) for the product to remain linear.
        struct MulFrame {
            args: SmallVec<[TermId; 4]>,
            /// Index of the next factor to evaluate; factors `..next-1` have
            /// been classified already, factor `next-1` (if `next > 0`) is the
            /// one whose result is sitting in the current level.
            next: usize,
            const_product: Rational64,
            /// The single non-constant factor seen so far, e.g. `x`, `(- x)`,
            /// `(* 2 x)`.  A second one makes the product nonlinear.
            var_factor: Option<(TermId, Rational64)>,
            /// The scale the whole product contributes at.
            scale: Rational64,
            /// The suspended accumulation context of the `Mul`'s parent,
            /// restored when the product finalizes.
            parent: Level,
        }
        enum Work {
            /// Fold `term` into the current level at the given scale.
            Visit(TermId, Rational64),
            /// Classify the factor that just finished (when `next > 0`) and
            /// either evaluate the next factor or finalize the product.
            Mul(MulFrame),
        }

        let mut cur = Level::new();
        let mut work: Vec<Work> = vec![Work::Visit(term_id, scale)];

        while let Some(item) = work.pop() {
            match item {
                Work::Visit(id, sc) => {
                    let term = manager.get(id)?;
                    match &term.kind {
                        // Integer constant
                        TermKind::IntConst(n) => {
                            // BigInt too large for i64 -> not linear (honest
                            // reject; the atom stays gated).
                            let val = n.to_i64()?;
                            cur.constant += sc * Rational64::from_integer(val);
                        }

                        // Rational constant
                        TermKind::RealConst(r) => {
                            cur.constant += sc * *r;
                        }

                        // Bitvector constant - treat as integer
                        TermKind::BitVecConst { value, .. } => {
                            let val = value.to_i64()?;
                            cur.constant += sc * Rational64::from_integer(val);
                        }

                        // Variable (or bitvector variable - treat as integer variable)
                        TermKind::Var(_) => {
                            cur.terms.push((id, sc));
                        }

                        // Uninterpreted function application whose sort is numeric -- treat
                        // as an opaque arithmetic variable.  This is the UFLIA / UFLRA case:
                        // e.g. `f(k)` in `(> (f k) 10)` where `f : Int -> Int`.  By
                        // representing `f(k)` as an arithmetic variable we ensure that
                        //   (a) the arithmetic solver tracks it and assigns it a model value,
                        //   (b) the constraint `f(k) > 10` is handled consistently with any
                        //       later instantiation that produces `f(k) <= 10`.
                        //
                        // Nested applications (`f(f(k))`) are opaque arithmetic variables
                        // exactly like flat ones.  Excluding them — the mirror of the old
                        // restriction in `track_theory_vars` — did not make the solver
                        // conservative, it made it *wrong*: failing the linear parse leaves
                        // the whole atom without a theory meaning, so it survives as a free
                        // boolean and the solver reports `sat` for formulas it never
                        // satisfied.  The Nelson-Oppen equality propagation the exclusion
                        // was waiting for is now in place and explained
                        // (`TheoryManager::assert_explained_equality`).
                        TermKind::Apply { .. } => {
                            let sort = term.sort;
                            let is_numeric =
                                sort == manager.sorts.int_sort || sort == manager.sorts.real_sort;
                            if !is_numeric {
                                // Non-numeric Apply (e.g. uninterpreted predicate) -- not linear.
                                return None;
                            }
                            cur.terms.push((id, sc));
                        }

                        // Array select with numeric sort: treat `(select a i) : Int/Real` as
                        // an opaque arithmetic atom with the given scale coefficient.  This
                        // allows expressions such as `(+ (select a 0) (select a 1))` to be
                        // parsed as linear arithmetic sums.
                        TermKind::Select(_, _) => {
                            let sort = term.sort;
                            let is_numeric =
                                sort == manager.sorts.int_sort || sort == manager.sorts.real_sort;
                            if !is_numeric {
                                // Select of non-numeric sort (e.g. Bool array) -- not linear.
                                return None;
                            }
                            cur.terms.push((id, sc));
                        }

                        // Datatype accessor with numeric sort: `(head l) : Int` is an opaque
                        // arithmetic atom, exactly like `(select a i)`.  Without this the
                        // linear parse of `(= (head l) 10)` failed, no constraint reached the
                        // tableau, and `(= (head l) 10) ∧ (= (head l) 11)` was answered `sat`
                        // — the accessor is one ground term and cannot hold two values.
                        // `dt_axioms` supplies the rest of the accessor's meaning; here it
                        // only has to be *a* variable so that two occurrences agree.
                        TermKind::DtSelector { .. } => {
                            let sort = term.sort;
                            let is_numeric =
                                sort == manager.sorts.int_sort || sort == manager.sorts.real_sort;
                            if !is_numeric {
                                // Accessor of a non-numeric field -- not a linear atom.
                                return None;
                            }
                            cur.terms.push((id, sc));
                        }

                        // Addition: fold every operand at the same scale.
                        // Children are pushed in reverse so they pop (and hence
                        // append to `cur.terms`) left-to-right, exactly like the
                        // recursive descent did.
                        TermKind::Add(args) => {
                            for &arg in args.iter().rev() {
                                work.push(Work::Visit(arg, sc));
                            }
                        }

                        // Subtraction
                        TermKind::Sub(lhs, rhs) => {
                            work.push(Work::Visit(*rhs, -sc));
                            work.push(Work::Visit(*lhs, sc));
                        }

                        // Negation
                        TermKind::Neg(arg) => {
                            work.push(Work::Visit(*arg, -sc));
                        }

                        // Multiplication of linear terms.  Suspend the current
                        // context inside the frame; each factor is evaluated
                        // into a fresh one (matching the recursive version's
                        // per-factor `sub_terms`/`sub_constant` buffers).
                        TermKind::Mul(args) => {
                            work.push(Work::Mul(MulFrame {
                                args: args.iter().copied().collect(),
                                next: 0,
                                const_product: Rational64::one(),
                                var_factor: None,
                                scale: sc,
                                parent: core::mem::replace(&mut cur, Level::new()),
                            }));
                        }

                        // Integer `div`/`mod` and Int/Real-sorted `ite`: opaque arithmetic
                        // atoms.  Their meaning is not expressible as a linear combination
                        // of their operands, so the linear solver gets a variable and the
                        // *definition* arrives separately as ground axioms — see
                        // [`Solver::instantiate_arith_axioms`].  Until those axioms are
                        // asserted the term stays in nobody's theory, which is exactly what
                        // the honesty gate in `encode_guards` watches for.
                        //
                        // Real-sorted `Div` is deliberately excluded: `(/ x y)` is exact
                        // rational division, whose defining identity `x = y * (x / y)` is
                        // nonlinear, so it keeps failing the parse and stays gated.
                        TermKind::Mod(_, _) if term.sort == manager.sorts.int_sort => {
                            cur.terms.push((id, sc));
                        }
                        TermKind::Div(_, _) if term.sort == manager.sorts.int_sort => {
                            cur.terms.push((id, sc));
                        }
                        TermKind::Ite(_, _, _)
                            if term.sort == manager.sorts.int_sort
                                || term.sort == manager.sorts.real_sort =>
                        {
                            cur.terms.push((id, sc));
                        }

                        // Not linear.  The catch-all is the honest reject
                        // channel here — "shape the linear solver cannot
                        // represent" — so a future `TermKind` variant fails
                        // the parse (and the atom stays gated) rather than
                        // being mis-folded.
                        _ => return None,
                    }
                }
                Work::Mul(mut frame) => {
                    if frame.next > 0 {
                        // Classify the factor whose evaluation just completed
                        // into the current (per-factor) level.
                        if cur.terms.is_empty() {
                            // Pure constant factor — absorb into product.
                            frame.const_product *= cur.constant;
                        } else if cur.terms.len() == 1 && cur.constant.is_zero() {
                            // Exactly one scaled variable with no additive constant,
                            // e.g. `x`, `(- x)`, `(* 2 x)`.  Record as the variable
                            // factor; if we already have one, the product is nonlinear.
                            if frame.var_factor.is_some() {
                                return None;
                            }
                            frame.var_factor = Some(cur.terms[0]);
                        } else {
                            // Either multi-variable (e.g. `(+ x y)`), or a linear
                            // expression with a constant offset (e.g. `(+ 1 x)`).
                            // Multiplying such a factor by another variable yields a
                            // nonlinear product.
                            return None;
                        }
                    }
                    if frame.next < frame.args.len() {
                        let arg = frame.args[frame.next];
                        frame.next += 1;
                        cur = Level::new();
                        work.push(Work::Mul(frame));
                        work.push(Work::Visit(arg, Rational64::one()));
                    } else {
                        // All factors classified: restore the parent context
                        // and contribute the product to it.
                        let new_scale = frame.scale * frame.const_product;
                        cur = frame.parent;
                        match frame.var_factor {
                            Some((v, coef)) => cur.terms.push((v, new_scale * coef)),
                            None => cur.constant += new_scale,
                        }
                    }
                }
            }
        }

        // The work stack is empty, so every `Mul` frame has finalized and
        // `cur` is the root-level context again.  Only now touch the caller's
        // buffers, preserving the recursive version's append order.
        for pair in cur.terms {
            terms.push(pair);
        }
        *constant += cur.constant;
        Some(())
    }

    /// Assert a term
    ///
    /// Strengthening the assertion stack invalidates the last verdict: a model
    /// found before this call need not satisfy `term`, so serving it afterwards
    /// would report a "model" of a formula it falsifies.  See
    /// `Solver::invalidate_results` (private) for the rule and for why the unsat
    /// core goes with it.
    pub fn assert(&mut self, term: TermId, manager: &mut TermManager) {
        // Replace inlined nullary define-fun bodies with their named consts
        // (parser expands bindings at parse time).  Prevents re-flattening
        // Discord/EM/R on every later assert that mentions them.
        let term = self.fold_unit_eq_reps(term, manager);
        // Alias before rewrite: nullary define-fun `(= name body)` must link the
        // pre-inline `body` TermId (which later asserts re-use via parser
        // bindings) to `name` for domain splits.
        self.note_unit_eq_alias(term, manager);
        // Collapse long `(ite (= x c_i) e_i …)` lookup spines into one result
        // var + flat implications before generic ite elimination (avoids O(n)
        // chained mux vars on tool-generated finite maps).
        let term = self.flatten_eq_ite_tables(term, manager);
        // Collapse 0/1 Discord/Fan nests to arithmetic before mux expansion.
        let term = self.fold_zero_one_nests(term, manager);
        // Eliminate non-Bool `ite` (mux) subterms into fresh constants plus
        // conditional side-conditions, so EUF sees the selected-branch equality
        // in every position (direct equality operand, nested in an app arg, …).
        let term = self.eliminate_nonbool_ite(term, manager);
        // Abstract compound Bool subterms used as UF arguments into fresh Bool
        // vars + defining equalities, so Bool completion can merge equal-valued
        // arguments and congruence over the application can fire.
        let term = self.abstract_compound_bool_args(term, manager);
        // Purify numeric (Int/Real) UF-application arguments into fresh shared
        // variables.  `track_theory_vars` does not intern UF arguments, so a
        // constant/compound argument like `f(3)` or `f(fmt1 + 1)` is never an
        // arithmetic interface term and arithmetic-derived equalities to it
        // never reach EUF (the QF_UFLIA/QF_UFIDL false-SAT root cause).
        let term = self.purify_numeric_uf_args(term, manager);

        let index = self.assertions.len();
        self.assertions.push(term);
        self.trail.push(TrailOp::AssertionAdded { index });
        self.invalidate_fp_cache();
        self.invalidate_results();

        // Check if this is a boolean constant first
        if let Some(t) = manager.get(term) {
            match t.kind {
                TermKind::False => {
                    // Mark that we have a false assertion
                    if !self.has_false_assertion {
                        self.has_false_assertion = true;
                        self.trail.push(TrailOp::FalseAssertionSet);
                    }
                    self.record_assertion_identity(term, None, index);
                    return;
                }
                TermKind::True => {
                    // True is always satisfied, no need to encode
                    self.record_assertion_identity(term, None, index);
                    return;
                }
                _ => {}
            }
        }

        // Overflow guard (soundness): a term nested far deeper than the encoder
        // can safely handle would overflow the native call stack in one of the
        // recursive passes below (simplification, polarity collection, or the
        // Tseitin encoder).  Detect excessive depth with an explicit-stack scan
        // and, when exceeded, skip every deep recursive pass for this assertion
        // and flag the incomplete encoding so `check` answers `Unknown` rather
        // than crashing the process.
        if self.term_exceeds_encode_depth(term, manager) {
            self.encode_depth_exceeded = true;
            self.record_assertion_identity(term, None, index);
            return;
        }

        // Apply simplification if enabled
        let simplified = if self.config.simplify {
            self.simplifier.simplify(term, manager)
        } else {
            term
        };

        // Replace bounded-integer quantifiers by their exactly equivalent
        // ground expansion so the ground solver decides them directly.
        let expanded = self
            .finite_expand_assertion(simplified, manager)
            .unwrap_or(simplified);

        // Replace the existentials this assertion states unconditionally by
        // their Skolemization, so the ground solver *searches* for a witness
        // instead of MBQI guessing one.
        let term_to_encode = self.skolemize_asserted_existentials(expanded, manager);

        // Check again if simplification produced a constant
        if let Some(t) = manager.get(term_to_encode) {
            match t.kind {
                TermKind::False => {
                    if !self.has_false_assertion {
                        self.has_false_assertion = true;
                        self.trail.push(TrailOp::FalseAssertionSet);
                    }
                    return;
                }
                TermKind::True => {
                    // Simplified to true, no need to encode
                    return;
                }
                _ => {}
            }
        }

        // Check for datatype constructor mutual exclusivity
        // If we see (= var Constructor), track it and check for conflicts
        if let Some(t) = manager.get(term_to_encode).cloned() {
            if let TermKind::Eq(lhs, rhs) = &t.kind {
                if let Some((var_term, constructor)) =
                    self.extract_dt_var_constructor(*lhs, *rhs, manager)
                {
                    if let Some(&existing_con) = self.dt_var_constructors.get(&var_term) {
                        if existing_con != constructor {
                            // Variable constrained to two different constructors - UNSAT
                            if !self.has_false_assertion {
                                self.has_false_assertion = true;
                                self.trail.push(TrailOp::FalseAssertionSet);
                            }
                            return;
                        }
                    } else {
                        self.dt_var_constructors.insert(var_term, constructor);
                        self.trail
                            .push(TrailOp::DtVarConstructorAdded { term: var_term });
                    }
                }
            }
        }

        // Collect polarity information if polarity-aware encoding is enabled
        if self.polarity_aware {
            self.collect_polarities(term_to_encode, Polarity::Positive, manager);
        }

        // Hand MBQI only the quantifiers this assertion actually entails.
        self.register_asserted_quantifiers(term_to_encode, manager);

        // Encode the assertion immediately
        let lit = self.encode(term_to_encode, manager);
        self.sat.add_clause([lit]);

        // Track unit `(= name body)` from nullary define-fun so table indices
        // that are inlined bodies inherit bounds on `name`.
        self.note_unit_eq_alias(term_to_encode, manager);

        // For Not(Eq(a,b)) assertions on arithmetic terms, eagerly add the
        // arithmetic disequality split (a<b OR a>b) so that ArithSolver assigns
        // distinct values from the very first SAT solve iteration.  Without this,
        // the ArithSolver may not enforce disequalities correctly.
        self.add_arith_diseq_split(term_to_encode, manager);

        self.record_assertion_identity(term, None, index);
    }

    /// z3-style "triangle" axiomatization of arithmetic↔EUF equality sharing.
    ///
    /// For every interned integer arithmetic term `t` and every integer
    /// constant `c` appearing in the formula, add the valid clauses
    ///
    /// ```text
    ///   (t = c)  ⟺  (t ≤ c) ∧ (t ≥ c)
    /// ```
    /// i.e. `(~eq ∨ le)`, `(~eq ∨ ge)`, `(eq ∨ ~le ∨ ~ge)`.
    ///
    /// This complements *model-based* equality merging with *axiom-based*
    /// combination: CDCL decides the equality atoms, the arithmetic solver
    /// **validates** each decision via `check()` (a plain consistency test, no
    /// reason extraction), and EUF merges with the equality atom — which carries
    /// a SAT variable — as the reason.  Soundness is thus structural: only
    /// logically-valid clauses are added, and every merge is justified by an
    /// assigned atom.
    ///
    /// This is what makes the deeply-nested `ite`/`Sum` chains of
    /// `EufLaArithmetic/hard` reduce: once CDCL sets `eq(ite_result, c)=true`
    /// for the value `c` the arithmetic constraints actually force, arith
    /// accepts it, EUF merges `ite_result` with `c`, and congruence closure
    /// collapses the rest of the chain.
    ///
    /// RESTRICTION: only the fresh `ite`-result constants (`__oxiz_ite_*`)
    /// introduced by `eliminate_nonbool_ite` are axiomatized.  Targeting exactly
    /// them keeps the added boolean structure tiny so CDCL is not disrupted on
    /// other benchmark families (e.g. WiSA), which would otherwise time out
    /// from the clause blow-up of axiomatizing every arith term.
    pub(super) fn axiomatize_arith_constant_equalities(
        &mut self,
        manager: &mut TermManager,
    ) {
        use rustc_hash::FxHashSet;

        // The triangle axiomatization is a *quantifier-free* theory-combination
        // technique: the non-convex LIA⇄EUF gaps it closes (EufLaArithmetic/hard)
        // are all QF_*.  On a quantified goal the fresh eq/le/ge Boolean
        // structure it introduces perturbs MBQI's model-based instantiation
        // (shifting convergence and risking spurious / missed instantiations),
        // so it is scoped out there — quantified combination falls back to the
        // existing model-based path.  This also keeps the axiomatization
        // idempotent across the repeated `check`s of an MBQI search.
        if self.has_quantifiers {
            return;
        }

        let int_sort = manager.sorts.int_sort;

        // Integer-sorted `ite`-result constants to axiomatize against constants.
        let terms: Vec<TermId> = self
            .ite_result_terms
            .iter()
            .copied()
            .filter(|&t| manager.get(t).is_some_and(|tm| tm.sort == int_sort))
            .collect();
        if terms.is_empty() {
            return;
        }

        // Distinct integer constants appearing in the original assertions.
        // Derived from `assertions` (fixed per scope) rather than
        // `var_to_parsed_arith` (which grows as MBQI / theory-axiom
        // instantiation add atoms across search rounds): a stable source keeps
        // the axiomatization idempotent across repeated `check`s on the same
        // goal.  Walking assertion subterms also reaches constants buried in
        // quantifier bodies, so they are axiomatized from the first `check`.
        let mut const_vals: FxHashSet<i64> = FxHashSet::default();
        for &assertion in &self.assertions {
            for st in collect_subterms(assertion, manager) {
                if let Some(tm) = manager.get(st) {
                    if let TermKind::IntConst(n) = &tm.kind {
                        if let Some(v) = n.to_i64() {
                            const_vals.insert(v);
                        }
                    }
                }
            }
        }
        if const_vals.is_empty() {
            return;
        }
        let mut consts: Vec<i64> = const_vals.into_iter().collect();
        consts.sort_unstable();

        // Bound the work: skip axiomatization on very large interfaces to
        // avoid clause blow-up (the model-based path still handles them).
        const MAX_PAIRS: usize = 4096;
        if terms.len().saturating_mul(consts.len()) > MAX_PAIRS {
            return;
        }

        for &t in &terms {
            for &c in &consts {
                let pair = (t, c);
                if !self.arith_const_axiom_pairs.insert(pair) {
                    // Already axiomatized this (term, const) pair in a prior
                    // `check` whose clauses survived (no retracting `pop`).
                    continue;
                }
                let c_term = manager.mk_int(c);
                if c_term == t {
                    self.arith_const_axiom_pairs.remove(&pair);
                    continue;
                }
                let eq_term = manager.mk_eq(t, c_term);
                let le_term = manager.mk_le(t, c_term);
                let ge_term = manager.mk_ge(t, c_term);
                let eq_lit = self.encode_depth(eq_term, manager, 0);
                let le_lit = self.encode_depth(le_term, manager, 0);
                let ge_lit = self.encode_depth(ge_term, manager, 0);
                // (t = c) -> (t <= c)
                self.sat.add_clause([eq_lit.negate(), le_lit]);
                // (t = c) -> (t >= c)
                self.sat.add_clause([eq_lit.negate(), ge_lit]);
                // (t <= c) ∧ (t >= c) -> (t = c)
                self.sat
                    .add_clause([eq_lit, le_lit.negate(), ge_lit.negate()]);
                // Record the pair so a later `check` does not re-emit these
                // clauses, and a retracting `pop` drops the mark so they are
                // re-axiomatized when needed again.
                self.trail
                    .push(TrailOp::ArithConstAxiomAdded { term: t, const_val: c });
                // No phase bias on `eq`: the z3-style theory propagation in
                // `final_check` deterministically forces the correct `le`/`ge`
                // (and thus `eq`) once arithmetic fixes the ite-result to a
                // constant.  Biasing `eq` toward `true` would instead make CDCL
                // wastefully try `eq=true` for the *wrong* constants first
                // (arith conflict → backtrack) before the propagation fires.
                let _ = eq_lit;
            }
        }
    }

    /// Static care-graph `ensureLiteral` (cvc5-style).  Before the search,
    /// create CDCL decision atoms `(= a b)` for undecided shared-term pairs so
    /// the solver can branch on the equality arrangement *during* the single
    /// search, instead of via post-Sat refinement rounds that each backtrack
    /// to root, reset every theory, rebuild the TheoryManager and re-solve.
    ///
    /// cvc5 adds the same literals incrementally via `ensureLiteral` inside
    /// `combineTheories` (called from the theory's final-check, mid-search, no
    /// restart).  oxiz's `TheoryCallback` cannot encode mid-search, so the
    /// faithful analog is a single up-front pass: the literals exist from the
    /// first decision, CDCL explores them with the rest of the formula, and no
    /// re-solve is ever paid.  The previous post-Sat `refine_care_graph_splits`
    /// restarted the whole solve per batch of atoms; on satisfiable instances
    /// that multiplied into 3-4 full re-solves adding 500+ atoms each, turning
    /// fast correct `sat` answers into timeouts for zero soundness gain (the
    /// atoms never actually surfaced the hidden conflict -- CDCL still returned
    /// `sat` even with every pair encoded).
    pub(super) fn pre_encode_care_graph_atoms(&mut self, manager: &mut TermManager) {
        if self.has_quantifiers { return; }
        const MAX_CARE_ATOMS: usize = 1024;
        // Shared interface = terms visible to BOTH EUF (as an application
        // argument) and arithmetic.  cvc5 builds its care graph from the
        // shared-terms set; oxiz has no purification so the interface is the
        // arith-interned terms that also appear under a function symbol.
        let interface = self.euf.app_argument_terms();
        let shared: Vec<TermId> = self.arith.interface_terms().iter().copied()
            .filter(|t| interface.contains(t)).collect();
        if shared.len() < 2 { return; }
        // cvc5's care graph is small (~10-50) thanks to tight purification.
        // oxiz has none, so a large shared interface yields O(n^2) care atoms
        // that bloat CDCL without helping (the equality arrangements that
        // matter are far fewer than the pairs).  Skip when the interface is
        // too large: the cost (timeouts on satisfiable hash/distinct instances
        // with dozens of shared terms) outweighs the convexity-completeness
        // benefit.  The remaining false-SAT is closed by UF-argument
        // purification, not by this enumeration.
        const MAX_CARE_INTERFACE: usize = 24;
        if shared.len() > MAX_CARE_INTERFACE {
            return;
        }
        let mut added = 0usize;
        'outer: for i in 0..shared.len() {
            let a = shared[i];
            let sa = manager.get(a).map(|t| t.sort);
            let na = match self.euf.term_to_node(a) { Some(n) => n, None => continue };
            let ra = self.euf.find(na);
            for j in (i + 1)..shared.len() {
                if added >= MAX_CARE_ATOMS { break 'outer; }
                let b = shared[j];
                if manager.get(b).map(|t| t.sort) != sa { continue; }
                let nb = match self.euf.term_to_node(b) { Some(n) => n, None => continue };
                if ra == self.euf.find(nb) { continue; }          // already EUF-equal
                // Cheap pre-filter: skip pairs already pinned by level-0 bounds.
                if !matches!(self.arith.equality_status(a, b),
                    oxiz_theories::arithmetic::ArithEqualityStatus::Unknown) { continue; }
                let pair = if a < b { (a, b) } else { (b, a) };
                if !self.care_split_pairs.insert(pair) { continue; }
                // ensureLiteral: create the equality atom so CDCL can decide it.
                let eq_term = manager.mk_eq(a, b);
                let eq_lit = self.encode_depth(eq_term, manager, 0);
                // cvc5 prefers the positive phase (try `a = b` first).
                self.sat.set_preferred_phase(eq_lit.var(), true);
                self.trail.push(TrailOp::CareSplitAdded { a: pair.0, b: pair.1 });
                added += 1;
            }
        }
    }

    /// Theory-aware decision hint: bump value atoms of `(or (= x v0) … (= x vn))`
    /// enumerations so CDCL decides them early (and prefers positive phase).
    pub(super) fn bump_finite_domain_enumerations(&mut self, manager: &TermManager) {
        use rustc_hash::FxHashSet;
        let mut atoms: Vec<oxiz_sat::Var> = Vec::new();
        let mut seen_or: FxHashSet<TermId> = FxHashSet::default();
        for &assertion in &self.assertions {
            for st in collect_subterms(assertion, manager) {
                let Some(t) = manager.get(st) else { continue };
                if !matches!(t.kind, TermKind::Or(_)) { continue; }
                if !seen_or.insert(st) { continue; }
                let mut leaves: Vec<TermId> = Vec::new();
                let mut stack: Vec<TermId> = vec![st];
                let mut the_var: Option<TermId> = None;
                let mut ok = true;
                while let Some(n) = stack.pop() {
                    let Some(nt) = manager.get(n) else { ok = false; break };
                    match &nt.kind {
                        TermKind::Or(args) => {
                            if leaves.len() + stack.len() + args.len() > 256 { ok = false; break; }
                            for &a in args { stack.push(a); }
                        }
                        TermKind::Eq(l, r) => {
                            let v = match (manager.get(*l), manager.get(*r)) {
                                (Some(lt), _) if matches!(lt.kind, TermKind::Var(_)) => *l,
                                (_, Some(rt)) if matches!(rt.kind, TermKind::Var(_)) => *r,
                                _ => { ok = false; break }
                            };
                            match the_var {
                                None => the_var = Some(v),
                                Some(p) if p == v => {}
                                _ => { ok = false; break }
                            }
                            leaves.push(n);
                        }
                        _ => { ok = false; break }
                    }
                }
                if !ok || !(2..=64).contains(&leaves.len()) { continue; }
                for &eq_term in &leaves {
                    if let Some(&v) = self.term_to_var.get(&eq_term) {
                        atoms.push(v);
                        self.sat.set_preferred_phase(v, true);
                    }
                }
            }
        }
        if !atoms.is_empty() { self.sat.bump_decision_hint(&atoms); }
    }

    /// Assert a named term (for unsat core tracking)
    ///
    /// Invalidates the last verdict for the same reason as [`Solver::assert`].
    /// Ensure arith trichotomy clauses for ALL numeric equalities/disequalities,
    /// including those nested inside `let` bindings or array `select` results
    /// that `add_arith_diseq_split`'s walk misses (swap/storecomm: `let`-bound
    /// `(not (= (select…) (select…)))` → `term_to_var=1`, opaque Boolean).
    ///
    /// Scans every assertion's subterms (collect_subterms handles `let`) for
    /// `Not(Eq(a,b))` and `Eq(a,b)` where both sides are Int/Real-sorted, and
    /// calls `add_arith_trichotomy_clause` for each.  This makes the arith
    /// solver SEE the equality, enabling the combination to reason about array
    /// select results.
    pub(super) fn ensure_numeric_equality_splits(&mut self, manager: &mut TermManager) {
        use rustc_hash::FxHashSet;
        let int_sort = manager.sorts.int_sort;
        let real_sort = manager.sorts.real_sort;
        let mut seen: FxHashSet<(TermId, TermId)> = FxHashSet::default();
        // Collect pairs first (avoids holding &self.assertions across &mut self).
        let assertions: Vec<TermId> = self.assertions.clone();
        let mut pairs: Vec<(TermId, TermId)> = Vec::new();
        for &assertion in &assertions {
            for st in collect_subterms(assertion, manager) {
                let Some(t) = manager.get(st) else { continue };
                let (a, b) = match &t.kind {
                    TermKind::Not(inner) => {
                        let Some(it) = manager.get(*inner) else { continue };
                        match &it.kind {
                            TermKind::Eq(a, b) => (*a, *b),
                            _ => continue,
                        }
                    }
                    TermKind::Eq(a, b) => (*a, *b),
                    _ => continue,
                };
                let na = manager.get(a).is_some_and(|t| t.sort == int_sort || t.sort == real_sort);
                let nb = manager.get(b).is_some_and(|t| t.sort == int_sort || t.sort == real_sort);
                if !na || !nb { continue; }
                let pair = if a < b { (a, b) } else { (b, a) };
                if seen.insert(pair) { pairs.push((a, b)); }
            }
        }
        for (a, b) in pairs {
            self.add_arith_trichotomy_clause(a, b, manager);
        }
    }

    pub fn assert_named(&mut self, term: TermId, name: &str, manager: &mut TermManager) {
        let index = self.assertions.len();
        self.assertions.push(term);
        self.trail.push(TrailOp::AssertionAdded { index });
        self.invalidate_fp_cache();
        self.invalidate_results();

        // Check if this is a boolean constant first
        if let Some(t) = manager.get(term) {
            match t.kind {
                TermKind::False => {
                    // Mark that we have a false assertion
                    if !self.has_false_assertion {
                        self.has_false_assertion = true;
                        self.trail.push(TrailOp::FalseAssertionSet);
                    }
                    self.record_assertion_identity(term, Some(name.to_string()), index);
                    return;
                }
                TermKind::True => {
                    // True is always satisfied, no need to encode
                    self.record_assertion_identity(term, Some(name.to_string()), index);
                    return;
                }
                _ => {}
            }
        }

        // Overflow guard (soundness): see `assert`.  Skip all deep recursive
        // passes for a pathologically deep term and flag the incomplete
        // encoding so `check` answers `Unknown` instead of overflowing.
        if self.term_exceeds_encode_depth(term, manager) {
            self.encode_depth_exceeded = true;
            self.record_assertion_identity(term, Some(name.to_string()), index);
            return;
        }

        // Replace bounded-integer quantifiers by their exactly equivalent
        // ground expansion so the ground solver decides them directly.
        let expanded = self.finite_expand_assertion(term, manager).unwrap_or(term);

        // Replace the existentials this assertion states unconditionally by
        // their Skolemization (see `assert`).
        let term_to_encode = self.skolemize_asserted_existentials(expanded, manager);

        // Collect polarity information if polarity-aware encoding is enabled
        if self.polarity_aware {
            self.collect_polarities(term_to_encode, Polarity::Positive, manager);
        }

        // Hand MBQI only the quantifiers this assertion actually entails.
        self.register_asserted_quantifiers(term_to_encode, manager);

        // Encode the assertion immediately
        let lit = self.encode(term_to_encode, manager);
        self.sat.add_clause([lit]);

        // Eagerly add arith diseq split for Not(Eq(a,b)) assertions
        self.add_arith_diseq_split(term_to_encode, manager);

        self.record_assertion_identity(term, Some(name.to_string()), index);
    }

    /// Get the unsat core (after check() returned Unsat)
    #[must_use]
    pub fn get_unsat_core(&self) -> Option<&UnsatCore> {
        self.unsat_core.as_ref()
    }

    /// Rewrite every bounded-integer quantifier of `term` into its exactly
    /// equivalent finite conjunction / disjunction, or `None` when nothing in
    /// `term` qualifies.
    ///
    /// The rewrite is an equivalence, not a strengthening (see
    /// [`finite_expand`]): the whole substituted body — guard included — is
    /// emitted for every point of the interval, and the interval provably
    /// contains the entire region where the guard (`forall`) or the body
    /// (`exists`) can be true.  So the expanded assertion is interchangeable
    /// with the original at any polarity, and the quantifier disappears
    /// altogether instead of being handed to MBQI.  That is exactly what lets
    /// the *ground* array / arithmetic solver decide it, which is how an
    /// `(exists ((i Int)) (and (<= 0 i) (<= i 9) (= (select a i) v)))` over a
    /// pinned array finds its witness.
    ///
    /// A quantifier that does not fit the fragment is left untouched and keeps
    /// its normal MBQI path, so declining costs completeness only.
    /// Replace the existentials `term` asserts unconditionally by their
    /// Skolemization, returning `term` unchanged when it has none.
    ///
    /// See [`exists_skolem`] for why the rewrite is an equisatisfiability
    /// (never a strengthening) and why it is confined to the positive
    /// top-level conjunct spine.
    fn skolemize_asserted_existentials(
        &mut self,
        term: TermId,
        manager: &mut TermManager,
    ) -> TermId {
        let mut next_id = self.next_skolem_id;
        let rewritten = exists_skolem::skolemize_asserted_existentials(term, manager, &mut next_id);
        self.next_skolem_id = next_id;
        rewritten.unwrap_or(term)
    }

    fn finite_expand_assertion(
        &mut self,
        term: TermId,
        manager: &mut TermManager,
    ) -> Option<TermId> {
        let budget = self.config.finite_expansion_budget;
        if budget == 0 || !finite_expand::contains_quantifier(term, manager) {
            return None;
        }
        self.refresh_entailed_int_constants(manager);
        let entailed = core::mem::take(&mut self.entailed_int_consts);
        let expanded = finite_expand::expand_finite_quantifiers(term, manager, budget, &entailed);
        self.entailed_int_consts = entailed;
        expanded
    }

    /// Bring [`Solver::entailed_int_consts`] up to date with the assertion
    /// stack: for every term some **top-level** assertion pins to an integer
    /// literal, record the value every model must give it.
    ///
    /// Each assertion's top-level `And` spine is walked, because a conjunct of
    /// an unconditionally asserted conjunction is itself unconditionally
    /// asserted.  Nothing below a disjunction, negation, implication or
    /// quantifier is collected — those equalities are conditional and would not
    /// hold in every model, so using one as a quantifier bound could expand
    /// over the wrong interval.
    ///
    /// Only the assertions added since the last call are folded in, and `pop`
    /// resets both the map and the watermark (see [`Solver::pop`]), so the map
    /// is always exactly "consequences of the live assertion set" and the total
    /// scanning cost stays linear in the number of assertions.
    ///
    /// This is what lets `(assert (= n 5))` make `(< i n)` a *concrete* bound
    /// for [`Solver::finite_expand_assertion`]; without it a symbolic bound
    /// would leave the quantifier unexpanded.
    fn refresh_entailed_int_constants(&mut self, manager: &TermManager) {
        if self.entailed_int_consts_upto >= self.assertions.len() {
            return;
        }
        let mut entailed = core::mem::take(&mut self.entailed_int_consts);
        let int_sort = manager.sorts.int_sort;
        let mut stack: Vec<TermId> = Vec::new();
        let mut visited: FxHashSet<TermId> = FxHashSet::default();

        for &assertion in &self.assertions[self.entailed_int_consts_upto..] {
            stack.push(assertion);
            while let Some(current) = stack.pop() {
                if !visited.insert(current) {
                    continue;
                }
                let Some(kind) = manager.get(current).map(|t| t.kind.clone()) else {
                    continue;
                };
                match kind {
                    TermKind::And(args) => stack.extend(args.iter().copied()),
                    TermKind::Eq(lhs, rhs) => {
                        let pinned = match (
                            manager.get(lhs).map(|t| t.kind.clone()),
                            manager.get(rhs).map(|t| t.kind.clone()),
                        ) {
                            (Some(TermKind::IntConst(value)), _) => Some((rhs, value)),
                            (_, Some(TermKind::IntConst(value))) => Some((lhs, value)),
                            _ => None,
                        };
                        if let Some((symbol, value)) = pinned
                            && manager.get(symbol).is_some_and(|t| t.sort == int_sort)
                        {
                            entailed.entry(symbol).or_insert(value);
                        }
                    }
                    _ => {}
                }
            }
        }
        self.entailed_int_consts = entailed;
        self.entailed_int_consts_upto = self.assertions.len();
    }

    /// Register with MBQI and the E-matching engine every quantifier that the
    /// assertion `term` asserts **unconditionally**.
    ///
    /// MBQI turns a registered universal into ground instances that it adds to
    /// the SAT core as hard unit clauses — and, when an instance evaluates to
    /// `false`, as the empty clause — so a quantifier the assertion set does not
    /// entail must never be registered. `(not (forall ((x Int)) (P x)))` is
    /// `∃x. ¬P(x)`, not a universal fact; registering it refuted the satisfiable
    /// `(not (forall ((x Int)) (P x))) ∧ (not (P 5))`. The same held for a
    /// quantifier inside a disjunct, an implication, an `ite` branch, or a
    /// Bool-sorted equality's operand.
    ///
    /// [`Solver::encode`] cannot make this call: it is the Tseitin transform and
    /// visits every sub-term at every polarity. So the decision is made here, on
    /// the asserted spine, with [`super::term_walk::asserted_children`] — the
    /// shared definition of "unconditionally asserted" also used by the
    /// `check_*.rs` definite-conflict collectors.
    ///
    /// Skipping a non-entailed quantifier costs only completeness: `check`
    /// still sees `has_quantifiers`, so it answers `Unknown` rather than
    /// guessing.
    fn register_asserted_quantifiers(&mut self, term: TermId, manager: &mut TermManager) {
        let mut stack: Vec<(TermId, bool)> = vec![(term, true)];
        let mut visited: FxHashSet<(TermId, bool)> = FxHashSet::default();

        while let Some((current, positive)) = stack.pop() {
            if !visited.insert((current, positive)) {
                continue;
            }
            let Some(kind) = manager.get(current).map(|t| t.kind.clone()) else {
                continue;
            };
            if positive {
                match &kind {
                    TermKind::Forall { patterns, body, .. } => {
                        let triggers: Vec<TermId> =
                            patterns.iter().flat_map(|p| p.iter().copied()).collect();
                        self.register_asserted_forall(current, *body, triggers, manager);
                    }
                    TermKind::Exists { patterns, .. } => {
                        let triggers: Vec<TermId> =
                            patterns.iter().flat_map(|p| p.iter().copied()).collect();
                        self.mbqi.add_quantifier(current, manager);
                        for trigger in triggers {
                            self.mbqi.collect_ground_terms(trigger, manager);
                        }
                    }
                    _ => {}
                }
            }
            stack.extend(super::term_walk::asserted_children(&kind, positive));
        }
    }

    /// Register one unconditionally asserted universal, Skolemizing a nested
    /// existential body (`∀x. ∃y. φ(x,y)` → `∀x. φ(x, sk(x))`) first so that
    /// MBQI sees a plain universal.
    fn register_asserted_forall(
        &mut self,
        term: TermId,
        body: TermId,
        triggers: Vec<TermId>,
        manager: &mut TermManager,
    ) {
        let body_is_exists = manager
            .get(body)
            .is_some_and(|t| matches!(t.kind, TermKind::Exists { .. }));

        if body_is_exists {
            #[cfg(feature = "std")]
            {
                // Seeded from the solver-wide counter: a fresh context always
                // starts at `sk!0` / `skf!0`, so two Skolemized quantifiers
                // would otherwise share one witness symbol — a strengthening
                // that can turn `sat` into `unsat`.
                let mut sk_ctx =
                    crate::skolemization::SkolemizationContext::with_first_id(self.next_skolem_id);
                let skolem_result = sk_ctx.skolemize(manager, term);
                self.next_skolem_id = sk_ctx.skolem_count();
                if let Ok(skolemized) = skolem_result {
                    self.mbqi.add_quantifier(skolemized, manager);
                    let _ = self.ematch_engine.register_quantifier(skolemized, manager);

                    // Also collect Skolem function application terms from the
                    // Skolemized body as MBQI candidates.  These terms (e.g.
                    // sk(x)) must appear in the candidate pool so that other
                    // universal quantifiers can be instantiated with them.
                    self.collect_skolem_candidates(skolemized, manager);
                } else {
                    // Skolemization failed — fall back to original
                    self.mbqi.add_quantifier(term, manager);
                    let _ = self.ematch_engine.register_quantifier(term, manager);
                }
            }
            #[cfg(not(feature = "std"))]
            {
                self.mbqi.add_quantifier(term, manager);
                let _ = self.ematch_engine.register_quantifier(term, manager);
            }
        } else {
            self.mbqi.add_quantifier(term, manager);
            // Register with E-matching engine for trigger-based instantiation
            let _ = self.ematch_engine.register_quantifier(term, manager);
        }

        // Collect ground terms from patterns as candidates
        for trigger in triggers {
            self.mbqi.collect_ground_terms(trigger, manager);
        }
    }

    /// Encode a term into SAT clauses using Tseitin transformation.
    ///
    /// Thin wrapper over [`Solver::encode_depth`] that starts the recursion at
    /// depth 0.  The depth counter guards against native-stack overflow on
    /// adversarially deep formulas (see [`ENCODE_DEPTH_LIMIT`](super::ENCODE_DEPTH_LIMIT)).
    pub(super) fn encode(&mut self, term: TermId, manager: &mut TermManager) -> Lit {
        self.encode_depth(term, manager, 0)
    }

    /// Depth-tracked recursive Tseitin encoder: memo check, depth guard, then
    /// the arm dispatch in [`Solver::encode_depth_uncached`].
    ///
    /// # Memoisation (`Solver::encoded_terms`)
    ///
    /// Each term's clauses are emitted at most once per polarity coverage:
    /// without the memo, a shared sub-term of the hash-consed DAG was
    /// re-descended once per *edge*, which is `2^n` re-encodes and `2^n`
    /// duplicate clauses on a doubling DAG (each level referencing the
    /// previous twice) — a hang at roughly depth 40.  The assert-time
    /// pre-check `term_exceeds_encode_depth` cannot catch that input: it
    /// measures depth and deliberately prunes shared nodes.
    ///
    /// A cached entry is only reused when the polarity it was encoded under
    /// covers the polarity the current occurrence needs (see the field doc on
    /// [`Solver::encoded_terms`]): `And`/`Or` under `polarity_aware` emit only
    /// one implication direction, every other arm is polarity-independent.  On
    /// a widening miss the term is re-encoded, which appends the missing
    /// direction; re-emitting the direction that already exists only
    /// duplicates clauses and cannot change the encoded semantics.
    ///
    /// The memo is consulted *before* the depth guard: a hit means the term's
    /// full encoding already exists in the SAT core, so returning it is always
    /// complete, whereas the pre-memo code would have set
    /// [`Solver::encode_depth_exceeded`] even for an already-encoded term.
    ///
    /// # Depth guard
    ///
    /// When the structural recursion exceeds [`ENCODE_DEPTH_LIMIT`](super::ENCODE_DEPTH_LIMIT) we stop
    /// descending, set [`Solver::encode_depth_exceeded`], and return a fresh
    /// Encode the conditional-equality semantics of a non-Bool `ite` that appears
    /// as an operand of a theory equality `(= a b)`.
    ///
    /// `(= a (ite c t e))` (non-Bool sort) holds iff `(c -> a=t) & (~c -> a=e)`.
    /// EUF has no built-in `ite`, so without these clauses the `ite` is interned
    /// as an opaque leaf and the conditional equality never reaches congruence
    /// closure — a false-SAT on mux-heavy QF_UF (e.g. firewire). Only the forward
    /// direction is added (soundness needs the theory to detect every conflict);
    /// each generated `(= a t)` / `(= a e)` atom recurses through `encode_depth`,
    /// so nested `ite`s are handled. Bool-sorted `ite`s are left to the gate
    /// encoder.
    fn encode_nonbool_ite_equality(
        &mut self,
        eq_var: Var,
        lhs: TermId,
        rhs: TermId,
        manager: &mut TermManager,
        depth: u32,
    ) {
        let eq_neg = Lit::neg(eq_var);
        for (a, b) in [(lhs, rhs), (rhs, lhs)] {
            let Some(bt) = manager.get(b) else {
                continue;
            };
            let TermKind::Ite(cond, then_br, else_br) = &bt.kind else {
                continue;
            };
            if bt.sort == manager.sorts.bool_sort {
                continue;
            }
            // Clone out of the immutable borrow before mutating `manager`.
            let (cond, then_br, else_br) = (*cond, *then_br, *else_br);
            let cond_lit = self.encode_depth(cond, manager, depth + 1);
            let lt = manager.mk_eq(a, then_br);
            let le = manager.mk_eq(a, else_br);
            let lt_lit = self.encode_depth(lt, manager, depth + 1);
            let le_lit = self.encode_depth(le, manager, depth + 1);
            // eq &  c -> a=t
            self.sat.add_clause([eq_neg, cond_lit.negate(), lt_lit]);
            // eq & ~c -> a=e
            self.sat.add_clause([eq_neg, cond_lit, le_lit]);
            break; // handled the (a,b) direction; no need to also do (b,a)
        }
    }

    /// Eliminate every non-Bool `ite` from `term`, returning an equivalent term
    /// with the side-conditions conjoined.
    ///
    /// Each non-Bool `(ite c t e)` of sort `s` is replaced everywhere it appears
    /// by a fresh constant `v` of sort `s`, with two side-conditions conjoined:
    /// `(=> c (= v t))` and `(=> (not c) (= v e))`. Once encoded, these pin
    /// `(= v t)` when `c` is true and `(= v e)` when `c` is false, so EUF merges
    /// the selected branch — recovering the conditional-equality semantics an
    /// opaque `ite` leaf would lose. Handles `ite` in every position,
    /// superseding the narrower [`encode_nonbool_ite_equality`] clauses (kept as
    /// a no-op backstop). Bool-sorted `ite`s are left for the gate encoder. The
    /// fresh constant is keyed by the `ite`'s `TermId` (hash-consed, so a
    /// structurally identical `ite` shares one var across assertions).
    pub(super) fn eliminate_nonbool_ite(
        &mut self,
        term: TermId,
        manager: &mut TermManager,
    ) -> TermId {
        use oxiz_core::ast::collect_subterms;
        use rustc_hash::FxHashMap;

        let bool_sort = manager.sorts.bool_sort;
        let mut map: FxHashMap<TermId, TermId> = FxHashMap::default();
        // First pass: assign a fresh var to each non-Bool ite subterm.
        for st in collect_subterms(term, manager) {
            let Some(t) = manager.get(st) else {
                continue;
            };
            if matches!(t.kind, TermKind::Ite(..)) && t.sort != bool_sort {
                let v = manager.mk_var(&format!("__oxiz_ite_{}", st.0), t.sort);
                self.ite_result_terms.insert(v);
                map.insert(st, v);
            }
        }
        if map.is_empty() {
            return term;
        }
        // Second pass: build side-conditions with inner ites already substituted.
        let mut side: Vec<TermId> = Vec::with_capacity(map.len() * 2);
        for (ite_term, v) in &map {
            let Some(t) = manager.get(*ite_term) else {
                continue;
            };
            let TermKind::Ite(c, tb, eb) = &t.kind else {
                continue;
            };
            let (c, tb, eb) = (*c, *tb, *eb);
            let c_sub = manager.substitute(c, &map);
            let t_sub = manager.substitute(tb, &map);
            let e_sub = manager.substitute(eb, &map);
            let eq_v_t = manager.mk_eq(*v, t_sub);
            let eq_v_e = manager.mk_eq(*v, e_sub);
            let not_c = manager.mk_not(c_sub);
            side.push(manager.mk_implies(c_sub, eq_v_t));
            side.push(manager.mk_implies(not_c, eq_v_e));
        }
        // Preserve define-fun body aliases / table-index keys across mux rewrite.
        self.rebind_aliases_through_map(manager, &map);
        self.rebind_table_indices_through_map(manager, &map);
        let rewritten = manager.substitute(term, &map);
        let mut parts = side;
        parts.insert(0, rewritten);
        manager.mk_and(parts)
    }

    /// Abstract compound Bool subterms that appear as (or under) uninterpreted-
    /// function arguments, replacing each with a fresh Bool variable plus a
    /// defining equality.
    ///
    /// EUF congruence compares applications by their arguments' classes, and Bool
    /// completion merges Bool *variables* with canonical true/false by SAT
    /// value. A compound Bool argument such as `(and a b)` is neither a variable
    /// (so not completed) nor encoded as a SAT atom when the application is a
    /// theory term the theory interns directly. Two such arguments that are
    /// logically equal but syntactically distinct never merge, and congruence
    /// over the application never fires — a false-SAT. Abstracting each to a
    /// fresh variable `v` with `(= v (and a b))` makes the argument a variable
    /// (now completed) while the defining equality ties `v` to the gate. Bool
    /// variables and Bool applications are left alone (already handled).
    pub(super) fn abstract_compound_bool_args(
        &mut self,
        term: TermId,
        manager: &mut TermManager,
    ) -> TermId {
        use oxiz_core::ast::collect_subterms;
        use rustc_hash::FxHashMap;

        let bool_sort = manager.sorts.bool_sort;
        let mut to_abstract: Vec<TermId> = Vec::new();
        // Identify compound Bool terms that are arguments of some Apply.
        for st in collect_subterms(term, manager) {
            let Some(t) = manager.get(st) else {
                continue;
            };
            if let TermKind::Apply { args, .. } = &t.kind {
                for &arg in args {
                    let Some(at) = manager.get(arg) else {
                        continue;
                    };
                    if at.sort == bool_sort
                        && !matches!(at.kind, TermKind::Var(_) | TermKind::Apply { .. })
                    {
                        to_abstract.push(arg);
                    }
                }
            }
        }
        if to_abstract.is_empty() {
            return term;
        }
        let mut map: FxHashMap<TermId, TermId> = FxHashMap::default();
        for arg in to_abstract {
            if map.contains_key(&arg) {
                continue;
            }
            let v = manager.mk_var(&format!("__oxiz_boolarg_{}", arg.0), bool_sort);
            map.insert(arg, v);
        }
        let mut side: Vec<TermId> = Vec::with_capacity(map.len());
        for (arg, v) in &map {
            side.push(manager.mk_eq(*v, *arg));
        }
        let rewritten = manager.substitute(term, &map);
        let mut parts = side;
        parts.insert(0, rewritten);
        manager.mk_and(parts)
    }

    /// Purify numeric (Int/Real) arguments of uninterpreted-function
    /// applications into fresh shared variables, mirroring
    /// [`Self::abstract_compound_bool_args`].
    ///
    /// `track_theory_vars` deliberately does not intern UF-application
    /// arguments, so a constant or arithmetic-compound argument such as
    /// `f(3)` or `f(fmt1 + 1)` is never an arithmetic interface term: an
    /// arithmetic-derived equality like `y = 3` (from `y = x+1, x = 2`) cannot
    /// propagate to EUF, and the congruence `f(y) = f(3)` never fires — the
    /// root cause of the QF_UFLIA / QF_UFIDL false-SAT.  Replacing `f(arg)`
    /// with `f(v)` plus the defining equality `v = arg` makes `v` a shared
    /// term (UF argument + arithmetic variable via the equality), so the
    /// Nelson-Oppen / model-based combination propagates `v = k` and EUF
    /// congruence closes.  This is the standard Nelson-Oppen purification step
    /// (cvc5's tight interface).
    ///
    /// Kinds already interned as shared arith terms by `track_theory_vars`
    /// (Var, Apply, Select, Ite, Div, Mod, DtSelector) are left in place; only
    /// constants and arithmetic compounds are abstracted.
    pub(super) fn purify_numeric_uf_args(&mut self, term: TermId, manager: &mut TermManager) -> TermId {
        use oxiz_core::ast::collect_subterms;
        use rustc_hash::FxHashMap;
        let int_sort = manager.sorts.int_sort;
        let real_sort = manager.sorts.real_sort;
        // Collect numeric constants that appear as a `Mul` factor: proxying one
        // of these would (via the global `substitute`) rewrite the coefficient
        // too, manufacturing spurious nonlinearity.  See the arg-scan note.
        let mut coefficient_consts: rustc_hash::FxHashSet<TermId> = rustc_hash::FxHashSet::default();
        for st in collect_subterms(term, manager) {
            let Some(t) = manager.get(st) else { continue };
            if let TermKind::Mul(args) = &t.kind {
                for &a in args {
                    if let Some(at) = manager.get(a) {
                        if matches!(at.kind, TermKind::IntConst(_) | TermKind::RealConst(_)) {
                            coefficient_consts.insert(a);
                        }
                    }
                }
            }
        }
        let mut to_abstract: Vec<TermId> = Vec::new();
        for st in collect_subterms(term, manager) {
            let Some(t) = manager.get(st) else { continue };
            // Soundness: a fresh proxy variable is necessarily *free*, so it
            // cannot replace a subterm under a true quantifier (`forall`/
            // `exists`) -- it would escape the quantifier's scope and turn a
            // satisfiable quantified formula unsatisfiable (observed on
            // UFLIA/division_property).  `let`/`match` are transparent local
            // bindings whose bound variables are already `Var`s (hence already
            // shared, not abstracted), and their compound arguments reference
            // only free declared variables, so purifying under them is sound;
            // guarding them too would skip the QF_UFLIA `let`-heavy Wisa cases
            // that most need purification.
            if matches!(t.kind, TermKind::Forall { .. } | TermKind::Exists { .. }) {
                return term;
            }
            if let TermKind::Apply { args, .. } = &t.kind {
                for &arg in args {
                    let Some(at) = manager.get(arg) else { continue };
                    let numeric = at.sort == int_sort || at.sort == real_sort;
                    let already_shared = matches!(
                        at.kind,
                        TermKind::Var(_)
                            | TermKind::Apply { .. }
                            | TermKind::Select(_, _)
                            | TermKind::Ite(_, _, _)
                            | TermKind::Div(_, _)
                            | TermKind::Mod(_, _)
                            | TermKind::DtSelector { .. }
                    );
                    // A constant that also appears as a `Mul` coefficient
                    // elsewhere in the term must NOT be proxied: the global
                    // `substitute` below would rewrite that coefficient too,
                    // turning a linear `(* 4 x)` into the nonlinear
                    // `(* proxy x)` and tripping the `arith_atoms_need_theory`
                    // honesty gate.  Such a constant is the same `TermId` in
                    // both roles (the interner dedups literals), so it cannot
                    // be substituted in only one position via the global map.
                    let is_const = matches!(at.kind, TermKind::IntConst(_) | TermKind::RealConst(_));
                    if numeric && !already_shared && !(is_const && coefficient_consts.contains(&arg)) {
                        to_abstract.push(arg);
                    }
                }
            }
        }
        if to_abstract.is_empty() {
            return term;
        }
        let mut map: FxHashMap<TermId, TermId> = FxHashMap::default();
        for arg in to_abstract {
            if map.contains_key(&arg) {
                continue;
            }
            let Some(at) = manager.get(arg) else { continue };
            let v = manager.mk_var(&format!("__oxiz_numarg_{}", arg.0), at.sort);
            map.insert(arg, v);
        }
        let mut side: Vec<TermId> = Vec::with_capacity(map.len());
        for (arg, v) in &map {
            side.push(manager.mk_eq(*v, *arg));
        }
        let rewritten = manager.substitute(term, &map);
        let mut parts = side;
        parts.insert(0, rewritten);
        manager.mk_and(parts)
    }

    /// literal for the sub-term.  The truncated encoding is deliberately
    /// incomplete: `check` observes the flag and answers `Unknown` rather than
    /// crashing the process with a stack overflow or trusting a partial model.
    /// Nothing is memoised on this path — the term was *not* encoded, and a
    /// later shallower occurrence must still get a real encoding.
    pub(super) fn encode_depth(
        &mut self,
        term: TermId,
        manager: &mut TermManager,
        depth: u32,
    ) -> Lit {
        // The polarity the And/Or arms would emit clauses under right now.
        // This must be the same lookup those arms perform; the map is not
        // mutated while an encode is in flight, so the two reads agree.
        let needed = if self.polarity_aware {
            self.polarities
                .get(&term)
                .copied()
                .unwrap_or(Polarity::Both)
        } else {
            Polarity::Both
        };
        if let Some(&(lit, cached)) = self.encoded_terms.get(&term) {
            if cached == Polarity::Both || cached == needed {
                return lit;
            }
        }
        if depth > super::ENCODE_DEPTH_LIMIT {
            self.encode_depth_exceeded = true;
            let var = self.get_or_create_var(term);
            return Lit::pos(var);
        }
        let lit = self.encode_depth_uncached(term, manager, depth);
        // The And/Or arms have already inserted their entry with the polarity
        // they actually used; every other arm's clause set is
        // polarity-independent, so `Both` is the correct coverage for it.
        if !self.encoded_terms.contains_key(&term) {
            self.memoize_encoding(term, lit, Polarity::Both);
        }
        lit
    }

    /// The arm dispatch of the Tseitin encoder.  Only called by
    /// [`Solver::encode_depth`], which owns the memo lookup and the depth
    /// guard; recursive descent goes back through `encode_depth` so every
    /// sub-term gets both.
    fn encode_depth_uncached(
        &mut self,
        term: TermId,
        manager: &mut TermManager,
        depth: u32,
    ) -> Lit {
        // Clone the term data to avoid borrowing issues
        let Some(t) = manager.get(term).cloned() else {
            let var = self.get_or_create_var(term);
            return Lit::pos(var);
        };

        match &t.kind {
            TermKind::True => {
                let var = self.get_or_create_var(manager.mk_true());
                self.sat.add_clause([Lit::pos(var)]);
                Lit::pos(var)
            }
            TermKind::False => {
                let var = self.get_or_create_var(manager.mk_false());
                self.sat.add_clause([Lit::neg(var)]);
                Lit::neg(var)
            }
            TermKind::Var(_) => {
                let var = self.get_or_create_var(term);
                // Bool completion: register Bool-sorted variables so EUF merges
                // them with the canonical true/false node by SAT value. Two Bool
                // variables with the same value ARE equal (Bool has two values),
                // and this is what lets congruence fire over UF applications that
                // take Bool arguments. Without it, distinct-but-equal Bool terms
                // stay in separate classes and f(b1)=f(b2) is never derived.
                if t.sort == manager.sorts.bool_sort {
                    self.record_constraint(var, Constraint::BoolApp(term));
                }
                // Track theory terms for model extraction
                let is_int = t.sort == manager.sorts.int_sort;
                let is_real = t.sort == manager.sorts.real_sort;

                if is_int || is_real {
                    // Track arithmetic terms
                    if !self.arith_terms.contains(&term) {
                        self.arith_terms.insert(term);
                        self.trail.push(TrailOp::ArithTermAdded { term });
                        // Register with arithmetic solver
                        self.arith.intern(term);
                    }
                } else if let Some(sort) = manager.sorts.get(t.sort)
                    && sort.is_bitvec()
                    && !self.bv_terms.contains(&term)
                {
                    self.bv_terms.insert(term);
                    self.trail.push(TrailOp::BvTermAdded { term });
                    // Register with BV solver if not already registered
                    if let Some(width) = sort.bitvec_width() {
                        self.bv.new_bv(term, width);
                    }
                }
                Lit::pos(var)
            }
            TermKind::Not(arg) => {
                let arg_lit = self.encode_depth(*arg, manager, depth + 1);
                arg_lit.negate()
            }
            TermKind::And(args) => {
                let result_var = self.get_or_create_var(term);
                let result = Lit::pos(result_var);

                let mut arg_lits: Vec<Lit> = Vec::new();
                for &arg in args {
                    arg_lits.push(self.encode_depth(arg, manager, depth + 1));
                }

                // Get polarity for optimization
                let polarity = if self.polarity_aware {
                    self.polarities
                        .get(&term)
                        .copied()
                        .unwrap_or(Polarity::Both)
                } else {
                    Polarity::Both
                };

                // result => all args (needed when result is positive)
                // ~result or arg1, ~result or arg2, ...
                if polarity != Polarity::Negative {
                    for &arg in &arg_lits {
                        self.sat.add_clause([result.negate(), arg]);
                    }
                }

                // all args => result (needed when result is negative)
                // ~arg1 or ~arg2 or ... or result
                if polarity != Polarity::Positive {
                    let mut clause: Vec<Lit> = arg_lits.iter().map(|l| l.negate()).collect();
                    clause.push(result);
                    self.sat.add_clause(clause);
                }

                // Record the polarity these clauses were emitted under; a later
                // occurrence needing the other direction must re-encode (see
                // `encode_depth`).  An overwriting write (not `or_insert`) so a
                // widening re-encode upgrades a previously narrower entry.
                self.memoize_encoding(term, result, polarity);

                result
            }
            TermKind::Or(args) => {
                let result_var = self.get_or_create_var(term);
                let result = Lit::pos(result_var);

                let mut arg_lits: Vec<Lit> = Vec::new();
                for &arg in args {
                    arg_lits.push(self.encode_depth(arg, manager, depth + 1));
                }

                // Get polarity for optimization
                let polarity = if self.polarity_aware {
                    self.polarities
                        .get(&term)
                        .copied()
                        .unwrap_or(Polarity::Both)
                } else {
                    Polarity::Both
                };

                // result => some arg (needed when result is positive)
                // ~result or arg1 or arg2 or ...
                if polarity != Polarity::Negative {
                    let mut clause: Vec<Lit> = vec![result.negate()];
                    clause.extend(arg_lits.iter().copied());
                    self.sat.add_clause(clause);
                }

                // some arg => result (needed when result is negative)
                // ~arg1 or result, ~arg2 or result, ...
                if polarity != Polarity::Positive {
                    for &arg in &arg_lits {
                        self.sat.add_clause([arg.negate(), result]);
                    }
                }

                // Same polarity bookkeeping as the `And` arm above.
                self.memoize_encoding(term, result, polarity);

                result
            }
            TermKind::Xor(lhs, rhs) => {
                let lhs_lit = self.encode_depth(*lhs, manager, depth + 1);
                let rhs_lit = self.encode_depth(*rhs, manager, depth + 1);

                let result_var = self.get_or_create_var(term);
                let result = Lit::pos(result_var);

                // result <=> (lhs xor rhs)
                // result <=> (lhs and ~rhs) or (~lhs and rhs)

                // result => (lhs or rhs)
                self.sat.add_clause([result.negate(), lhs_lit, rhs_lit]);
                // result => (~lhs or ~rhs)
                self.sat
                    .add_clause([result.negate(), lhs_lit.negate(), rhs_lit.negate()]);

                // (lhs and ~rhs) => result
                self.sat.add_clause([lhs_lit.negate(), rhs_lit, result]);
                // (~lhs and rhs) => result
                self.sat.add_clause([lhs_lit, rhs_lit.negate(), result]);

                result
            }
            TermKind::Implies(lhs, rhs) => {
                let lhs_lit = self.encode_depth(*lhs, manager, depth + 1);
                let rhs_lit = self.encode_depth(*rhs, manager, depth + 1);

                let result_var = self.get_or_create_var(term);
                let result = Lit::pos(result_var);

                // result <=> (~lhs or rhs)
                // result => ~lhs or rhs
                self.sat
                    .add_clause([result.negate(), lhs_lit.negate(), rhs_lit]);

                // (~lhs or rhs) => result
                // lhs or result, ~rhs or result
                self.sat.add_clause([lhs_lit, result]);
                self.sat.add_clause([rhs_lit.negate(), result]);

                result
            }
            TermKind::Ite(cond, then_br, else_br) => {
                let cond_lit = self.encode_depth(*cond, manager, depth + 1);
                let then_lit = self.encode_depth(*then_br, manager, depth + 1);
                let else_lit = self.encode_depth(*else_br, manager, depth + 1);

                let result_var = self.get_or_create_var(term);
                let result = Lit::pos(result_var);

                // result <=> (cond ? then : else)
                // cond and result => then
                self.sat
                    .add_clause([cond_lit.negate(), result.negate(), then_lit]);
                // cond and then => result
                self.sat
                    .add_clause([cond_lit.negate(), then_lit.negate(), result]);

                // ~cond and result => else
                self.sat.add_clause([cond_lit, result.negate(), else_lit]);
                // ~cond and else => result
                self.sat.add_clause([cond_lit, else_lit.negate(), result]);

                result
            }
            TermKind::Eq(lhs, rhs) => {
                // Check if this is a boolean equality or theory equality
                let lhs_term = manager.get(*lhs);
                let is_bool_eq = lhs_term.is_some_and(|t| t.sort == manager.sorts.bool_sort);

                if is_bool_eq {
                    // Boolean equality: encode as iff
                    let lhs_lit = self.encode_depth(*lhs, manager, depth + 1);
                    let rhs_lit = self.encode_depth(*rhs, manager, depth + 1);

                    let result_var = self.get_or_create_var(term);
                    let result = Lit::pos(result_var);

                    // result <=> (lhs <=> rhs)
                    // result => (lhs => rhs) and (rhs => lhs)
                    self.sat
                        .add_clause([result.negate(), lhs_lit.negate(), rhs_lit]);
                    self.sat
                        .add_clause([result.negate(), rhs_lit.negate(), lhs_lit]);

                    // (lhs <=> rhs) => result
                    self.sat.add_clause([lhs_lit, rhs_lit, result]);
                    self.sat
                        .add_clause([lhs_lit.negate(), rhs_lit.negate(), result]);

                    // ALSO register this equality as a theory constraint so EUF
                    // learns `lhs = rhs` and propagates congruence to Bool-sorted
                    // function applications. The iff gate handles pure-boolean
                    // propagation but cannot express congruence: `a = a'` (a Bool
                    // equality) must force `f(a) = f(a')` for a Bool-returning f.
                    // Without this EUF never merges the operands, that congruence
                    // is lost, and QF_UF problems over Bool-sorted UF go false-SAT.
                    // Both the iff gate and the theory constraint are sound and
                    // complementary: when `result` is true the iff clauses force
                    // equal SAT values *and* EUF merges them; when false EUF
                    // records the disequality.
                    self.record_constraint(result_var, Constraint::Eq(*lhs, *rhs));
                    self.track_theory_vars(*lhs, manager);
                    self.track_theory_vars(*rhs, manager);

                    result
                } else {
                    // Theory equality: create a fresh boolean variable
                    // Store the constraint for theory propagation
                    let var = self.get_or_create_var(term);
                    self.record_constraint(var, Constraint::Eq(*lhs, *rhs));

                    // Track theory variables for model extraction
                    self.track_theory_vars(*lhs, manager);
                    self.track_theory_vars(*rhs, manager);

                    // Pre-parse arithmetic equality for ArithSolver
                    // Only for Int/Real sorts, not BitVec
                    let is_arith = lhs_term.is_some_and(|t| {
                        t.sort == manager.sorts.int_sort || t.sort == manager.sorts.real_sort
                    });
                    if is_arith {
                        // We use Le type as placeholder since equality will be asserted
                        // as both Le and Ge
                        if let Some(parsed) = self.parse_arith_comparison(
                            *lhs,
                            *rhs,
                            ArithConstraintType::Le,
                            term,
                            manager,
                        ) {
                            self.var_to_parsed_arith.insert(var, parsed);
                        }
                    }

                    // Non-Bool `ite` in either operand: `(= a (ite c t e))` is
                    // equivalent to `(c -> a=t) & (~c -> a=e)`. EUF otherwise
                    // treats the `ite` as an opaque leaf and misses the
                    // conditional equality, yielding false-SAT on mux-heavy
                    // benchmarks (e.g. firewire). Add the forward implication
                    // clauses so that, once the SAT core pins `c`, the
                    // corresponding `(= a t)` / `(= a e)` atom is forced and EUF
                    // merges them. Nested `ite`s are handled by recursing through
                    // `encode_depth` on those atoms.
                    self.encode_nonbool_ite_equality(var, *lhs, *rhs, manager, depth);

                    Lit::pos(var)
                }
            }
            TermKind::Distinct(args) => {
                // Encode distinct as pairwise disequalities
                // distinct(a,b,c) <=> (a!=b) and (a!=c) and (b!=c)
                if args.len() <= 1 {
                    // trivially true
                    let var = self.get_or_create_var(manager.mk_true());
                    return Lit::pos(var);
                }

                let result_var = self.get_or_create_var(term);
                let result = Lit::pos(result_var);

                let mut diseq_lits = Vec::new();
                for i in 0..args.len() {
                    for j in (i + 1)..args.len() {
                        let eq = manager.mk_eq(args[i], args[j]);
                        let eq_lit = self.encode_depth(eq, manager, depth + 1);
                        diseq_lits.push(eq_lit.negate());
                    }
                }

                // result => all disequalities
                for &diseq in &diseq_lits {
                    self.sat.add_clause([result.negate(), diseq]);
                }

                // all disequalities => result
                let mut clause: Vec<Lit> = diseq_lits.iter().map(|l| l.negate()).collect();
                clause.push(result);
                self.sat.add_clause(clause);

                result
            }
            TermKind::Let { bindings, body } => {
                // For encoding, we can substitute the bindings into the body
                // This is a simplification - a more sophisticated approach would
                // memoize the bindings
                let substituted = *body;
                for (name, value) in bindings.iter().rev() {
                    // In a full implementation, we'd perform proper substitution
                    // For now, just encode the body directly
                    let _ = (name, value);
                }
                self.encode_depth(substituted, manager, depth + 1)
            }
            // Theory atoms (arithmetic, bitvec, arrays, UF)
            // These get fresh boolean variables - the theory solver handles the semantics
            TermKind::IntConst(_) | TermKind::RealConst(_) | TermKind::BitVecConst { .. } => {
                // Constants are theory terms, not boolean formulas
                // Should not appear at top level in boolean context
                let var = self.get_or_create_var(term);
                Lit::pos(var)
            }
            TermKind::Neg(_)
            | TermKind::Add(_)
            | TermKind::Sub(_, _)
            | TermKind::Mul(_)
            | TermKind::Div(_, _)
            | TermKind::Mod(_, _) => {
                // Arithmetic terms - should not appear at boolean top level
                let var = self.get_or_create_var(term);
                Lit::pos(var)
            }
            TermKind::Lt(lhs, rhs) => {
                // Arithmetic predicate: lhs < rhs
                let var = self.get_or_create_var(term);
                self.record_constraint(var, Constraint::Lt(*lhs, *rhs));
                // Parse and store linear constraint for ArithSolver
                if let Some(parsed) =
                    self.parse_arith_comparison(*lhs, *rhs, ArithConstraintType::Lt, term, manager)
                {
                    self.var_to_parsed_arith.insert(var, parsed);
                }
                // Track theory variables for model extraction
                self.track_theory_vars(*lhs, manager);
                self.track_theory_vars(*rhs, manager);
                Lit::pos(var)
            }
            TermKind::Le(lhs, rhs) => {
                // Arithmetic predicate: lhs <= rhs
                let var = self.get_or_create_var(term);
                self.record_constraint(var, Constraint::Le(*lhs, *rhs));
                // Parse and store linear constraint for ArithSolver
                if let Some(parsed) =
                    self.parse_arith_comparison(*lhs, *rhs, ArithConstraintType::Le, term, manager)
                {
                    self.var_to_parsed_arith.insert(var, parsed);
                }
                // Track theory variables for model extraction
                self.track_theory_vars(*lhs, manager);
                self.track_theory_vars(*rhs, manager);
                Lit::pos(var)
            }
            TermKind::Gt(lhs, rhs) => {
                // Arithmetic predicate: lhs > rhs
                let var = self.get_or_create_var(term);
                self.record_constraint(var, Constraint::Gt(*lhs, *rhs));
                // Parse and store linear constraint for ArithSolver
                if let Some(parsed) =
                    self.parse_arith_comparison(*lhs, *rhs, ArithConstraintType::Gt, term, manager)
                {
                    self.var_to_parsed_arith.insert(var, parsed);
                }
                // Track theory variables for model extraction
                self.track_theory_vars(*lhs, manager);
                self.track_theory_vars(*rhs, manager);
                Lit::pos(var)
            }
            TermKind::Ge(lhs, rhs) => {
                // Arithmetic predicate: lhs >= rhs
                let var = self.get_or_create_var(term);
                self.record_constraint(var, Constraint::Ge(*lhs, *rhs));
                // Parse and store linear constraint for ArithSolver
                if let Some(parsed) =
                    self.parse_arith_comparison(*lhs, *rhs, ArithConstraintType::Ge, term, manager)
                {
                    self.var_to_parsed_arith.insert(var, parsed);
                }
                // Track theory variables for model extraction
                self.track_theory_vars(*lhs, manager);
                self.track_theory_vars(*rhs, manager);
                Lit::pos(var)
            }
            TermKind::BvConcat(_, _)
            | TermKind::BvExtract { .. }
            | TermKind::BvNot(_)
            | TermKind::BvAnd(_, _)
            | TermKind::BvOr(_, _)
            | TermKind::BvXor(_, _)
            | TermKind::BvAdd(_, _)
            | TermKind::BvSub(_, _)
            | TermKind::BvMul(_, _)
            | TermKind::BvShl(_, _)
            | TermKind::BvLshr(_, _)
            | TermKind::BvAshr(_, _) => {
                // Bitvector terms - should not appear at boolean top level
                let var = self.get_or_create_var(term);
                Lit::pos(var)
            }
            TermKind::BvUdiv(_, _)
            | TermKind::BvSdiv(_, _)
            | TermKind::BvUrem(_, _)
            | TermKind::BvSrem(_, _) => {
                // Bitvector arithmetic terms (division/remainder)
                // Mark that we have arithmetic BV ops for conflict checking
                self.has_bv_arith_ops = true;
                let var = self.get_or_create_var(term);
                Lit::pos(var)
            }
            TermKind::BvUlt(lhs, rhs) => {
                // Bitvector unsigned less-than: treat as integer comparison
                let var = self.get_or_create_var(term);
                self.record_constraint(var, Constraint::Lt(*lhs, *rhs));
                // Parse as arithmetic constraint (bitvector as bounded integer)
                if let Some(parsed) =
                    self.parse_arith_comparison(*lhs, *rhs, ArithConstraintType::Lt, term, manager)
                {
                    self.var_to_parsed_arith.insert(var, parsed);
                }
                // Track theory variables for model extraction
                self.track_theory_vars(*lhs, manager);
                self.track_theory_vars(*rhs, manager);
                Lit::pos(var)
            }
            TermKind::BvUle(lhs, rhs) => {
                // Bitvector unsigned less-than-or-equal: treat as integer comparison
                let var = self.get_or_create_var(term);
                self.record_constraint(var, Constraint::Le(*lhs, *rhs));
                if let Some(parsed) =
                    self.parse_arith_comparison(*lhs, *rhs, ArithConstraintType::Le, term, manager)
                {
                    self.var_to_parsed_arith.insert(var, parsed);
                }
                // Track theory variables for model extraction
                self.track_theory_vars(*lhs, manager);
                self.track_theory_vars(*rhs, manager);
                Lit::pos(var)
            }
            TermKind::BvSlt(lhs, rhs) => {
                // Bitvector *signed* less-than.  The `Constraint::Lt` recorded
                // here is consumed by the BV theory path in
                // `TheoryManager::process_constraint`, which recovers the
                // signedness from this term's `TermKind` and asserts a proper
                // two's-complement `assert_slt` into the BV solver.
                //
                // We deliberately do NOT populate `var_to_parsed_arith`: that
                // path parses BV operands as plain *unsigned* non-negative
                // integers and asserts them into the linear ArithSolver.  For a
                // signed comparison that is wrong — mixing signed and unsigned
                // orders over the same shared integer variable yields spurious
                // UNSAT (e.g. `(bvslt x #b0000) ∧ (bvult #b0100 x)` is SAT with
                // x = 9, but the unsigned arith parse derives x < 0 ∧ x > 4).
                // Signed BV comparisons therefore stay purely in the BV solver.
                let var = self.get_or_create_var(term);
                self.record_constraint(var, Constraint::Lt(*lhs, *rhs));
                // Track theory variables for model extraction
                self.track_theory_vars(*lhs, manager);
                self.track_theory_vars(*rhs, manager);
                Lit::pos(var)
            }
            TermKind::BvSle(lhs, rhs) => {
                // Bitvector *signed* less-than-or-equal.  As for `BvSlt`, the
                // recorded `Constraint::Le` is handled with correct signed
                // (two's-complement) semantics by the BV theory path.  We do NOT
                // create a `var_to_parsed_arith` entry, because the linear-arith
                // parse treats BV operands as unsigned non-negative integers and
                // would mix signed/unsigned orders in one integer space,
                // producing spurious UNSAT.  Signed BV comparisons stay purely
                // in the BV solver.
                let var = self.get_or_create_var(term);
                self.record_constraint(var, Constraint::Le(*lhs, *rhs));
                // Track theory variables for model extraction
                self.track_theory_vars(*lhs, manager);
                self.track_theory_vars(*rhs, manager);
                Lit::pos(var)
            }
            TermKind::Select(_, _) | TermKind::Store(_, _, _) => {
                // Array operations - theory terms
                self.has_array_ops = true;
                let var = self.get_or_create_var(term);
                Lit::pos(var)
            }
            TermKind::Apply { .. } => {
                // Uninterpreted function application - theory term
                let var = self.get_or_create_var(term);
                // Register Bool-valued function applications as theory
                // constraints so that EUF congruence closure can detect
                // conflicts when the SAT solver assigns opposite polarities
                // to congruent applications (e.g., t(m)=true, t(co)=false,
                // but m=co implies t(m)=t(co)).
                if t.sort == manager.sorts.bool_sort {
                    self.record_constraint(var, Constraint::BoolApp(term));
                }
                Lit::pos(var)
            }
            // Quantifiers are *registered* with MBQI / E-matching by
            // `register_asserted_quantifiers`, which runs on the asserted spine
            // before this encoder does.  This pass is the Tseitin transform and
            // is polarity-blind by construction, so it must not decide which
            // quantifiers are facts: MBQI turns a registered universal into
            // ground unit clauses, and registering one that sits behind a
            // polarity boundary refuted satisfiable formulas such as
            // `(not (forall ((x Int)) (P x))) ∧ (not (P 5))`.
            TermKind::Forall { .. } | TermKind::Exists { .. } => {
                self.has_quantifiers = true;
                // Create a boolean variable for the quantifier
                let var = self.get_or_create_var(term);
                Lit::pos(var)
            }
            // String operations - theory terms and predicates
            TermKind::StringLit(_)
            | TermKind::StrConcat(_, _)
            | TermKind::StrLen(_)
            | TermKind::StrSubstr(_, _, _)
            | TermKind::StrAt(_, _)
            | TermKind::StrReplace(_, _, _)
            | TermKind::StrReplaceAll(_, _, _)
            | TermKind::StrReplaceRe(_, _, _)
            | TermKind::StrReplaceReAll(_, _, _)
            | TermKind::StrToInt(_)
            | TermKind::IntToStr(_)
            | TermKind::StrToCode(_)
            | TermKind::StrFromCode(_)
            | TermKind::StrInRe(_, _) => {
                // String terms - theory solver handles these
                let var = self.get_or_create_var(term);
                Lit::pos(var)
            }
            TermKind::StrContains(_, _)
            | TermKind::StrPrefixOf(_, _)
            | TermKind::StrSuffixOf(_, _)
            | TermKind::StrLt(_, _)
            | TermKind::StrLe(_, _)
            | TermKind::StrIndexOf(_, _, _) => {
                // String predicates - theory atoms
                let var = self.get_or_create_var(term);
                Lit::pos(var)
            }
            // Floating-point constants and special values
            TermKind::FpLit { .. }
            | TermKind::FpPlusInfinity { .. }
            | TermKind::FpMinusInfinity { .. }
            | TermKind::FpPlusZero { .. }
            | TermKind::FpMinusZero { .. }
            | TermKind::FpNaN { .. } => {
                // FP constants - theory terms
                let var = self.get_or_create_var(term);
                Lit::pos(var)
            }
            // Floating-point operations
            TermKind::FpAbs(_)
            | TermKind::FpNeg(_)
            | TermKind::FpSqrt(_, _)
            | TermKind::FpRoundToIntegral(_, _)
            | TermKind::FpAdd(_, _, _)
            | TermKind::FpSub(_, _, _)
            | TermKind::FpMul(_, _, _)
            | TermKind::FpDiv(_, _, _)
            | TermKind::FpRem(_, _)
            | TermKind::FpMin(_, _)
            | TermKind::FpMax(_, _)
            | TermKind::FpFma(_, _, _, _) => {
                // FP operations - theory terms
                let var = self.get_or_create_var(term);
                Lit::pos(var)
            }
            // Floating-point predicates
            TermKind::FpLeq(_, _)
            | TermKind::FpLt(_, _)
            | TermKind::FpGeq(_, _)
            | TermKind::FpGt(_, _)
            | TermKind::FpEq(_, _)
            | TermKind::FpIsNormal(_)
            | TermKind::FpIsSubnormal(_)
            | TermKind::FpIsZero(_)
            | TermKind::FpIsInfinite(_)
            | TermKind::FpIsNaN(_)
            | TermKind::FpIsNegative(_)
            | TermKind::FpIsPositive(_) => {
                // FP predicates - theory atoms that return bool
                let var = self.get_or_create_var(term);
                Lit::pos(var)
            }
            // Floating-point conversions
            TermKind::FpToFp { .. }
            | TermKind::FpToSBV { .. }
            | TermKind::FpToUBV { .. }
            | TermKind::FpToReal(_)
            | TermKind::RealToFp { .. }
            | TermKind::SBVToFp { .. }
            | TermKind::UBVToFp { .. } => {
                // FP conversions - theory terms
                let var = self.get_or_create_var(term);
                Lit::pos(var)
            }
            // Datatype operations
            TermKind::DtConstructor { .. }
            | TermKind::DtTester { .. }
            | TermKind::DtSelector { .. } => {
                // Datatype operations - theory terms
                let var = self.get_or_create_var(term);
                Lit::pos(var)
            }
            // Match expressions on datatypes
            TermKind::Match { .. } => {
                // Match expressions - theory terms
                let var = self.get_or_create_var(term);
                Lit::pos(var)
            }
        }
    }

    /// Scan all Constraint::Eq entries in var_to_constraint that are currently
    /// assigned False by the SAT model and add arithmetic splits `(lhs < rhs)
    /// OR (lhs > rhs)` for each.  This ensures ArithSolver knows about
    /// disequalities that arise from SAT-level implication propagation (e.g.
    /// from MBQI-generated instantiations like `(=> (= f(a) f(b)) (= a b))`).
    #[allow(dead_code)]
    pub(super) fn add_arith_diseq_splits_for_sat_model(&mut self, manager: &mut TermManager) {
        use super::types::Constraint;
        use oxiz_sat::LBool;

        let pairs: Vec<(TermId, TermId)> = self
            .var_to_constraint
            .iter()
            .filter_map(|(&var, constraint)| {
                if let Constraint::Eq(lhs, rhs) = constraint {
                    // Only Int or Real sorts
                    let lhs_is_numeric = manager.get(*lhs).is_some_and(|lt| {
                        lt.sort == manager.sorts.int_sort || lt.sort == manager.sorts.real_sort
                    });
                    if lhs_is_numeric && self.sat.model_value(var) == LBool::False {
                        Some((*lhs, *rhs))
                    } else {
                        None
                    }
                } else {
                    None
                }
            })
            .collect();

        for (lhs, rhs) in pairs {
            let lt_term = manager.mk_lt(lhs, rhs);
            let gt_term = manager.mk_gt(lhs, rhs);
            // Only add if the clause isn't already a tautology or unit-forced
            let lt_lit = self.encode(lt_term, manager);
            let gt_lit = self.encode(gt_term, manager);
            self.sat.add_clause([lt_lit, gt_lit]);
        }
    }

    /// Add the arithmetic trichotomy clause `(a = b) OR (a < b) OR (a > b)` for
    /// an Int/Real operand pair, so that a disequality forced by the Boolean
    /// structure reaches the `ArithSolver` as a strict ordering constraint.
    ///
    /// No-op for non-numeric operands (EUF/BV disequalities are handled by their
    /// own theory).  The clause is valid for every total order, hence safe to
    /// add unconditionally; the three literals reuse the atoms `encode` already
    /// created, so nothing new is asserted about the problem.
    fn add_arith_trichotomy_clause(&mut self, lhs: TermId, rhs: TermId, manager: &mut TermManager) {
        let is_numeric = manager
            .get(lhs)
            .is_some_and(|t| t.sort == manager.sorts.int_sort || t.sort == manager.sorts.real_sort);
        if !is_numeric {
            return;
        }
        let eq_term = manager.mk_eq(lhs, rhs);
        // `mk_eq` folds a syntactically identical pair to `true`; the clause is
        // then trivially satisfied and carries no information.
        if manager
            .get(eq_term)
            .is_some_and(|t| matches!(t.kind, TermKind::True | TermKind::False))
        {
            return;
        }
        let lt_term = manager.mk_lt(lhs, rhs);
        let gt_term = manager.mk_gt(lhs, rhs);
        let eq_lit = self.encode(eq_term, manager);
        let lt_lit = self.encode(lt_term, manager);
        let gt_lit = self.encode(gt_term, manager);
        self.sat.add_clause([eq_lit, lt_lit, gt_lit]);
    }

    /// Walk a term and give every arithmetic disequality source —
    /// `Not(Eq(a, b))` and `Distinct(a, b, ...)` — the trichotomy clause
    /// `(a = b) OR (a < b) OR (a > b)`, so the ArithSolver knows about the
    /// disequality and doesn't assign both sides equal values.
    ///
    /// The clause is a *tautology* over a totally ordered sort, so it can be
    /// added regardless of the Boolean context the disequality sits in.  When
    /// the context forces `a = b` to false (an asserted `not (= a b)` or a
    /// pairwise disequality of an asserted `distinct`), unit propagation leaves
    /// `(a < b) OR (a > b)` and the `ArithSolver` receives a genuine strict
    /// ordering constraint instead of silently ignoring the disequality.
    ///
    /// Emitting the *unguarded* split `(a < b) OR (a > b)` instead would be
    /// unsound: for `(or p (not (= x 0)))` it forces `x != 0` even when the
    /// formula is satisfied through `p`.
    ///
    /// The walk is an explicit-stack DFS preorder (children left-to-right),
    /// never native recursion: it runs on MBQI instantiation results, which
    /// are produced *during* `check` and never pass the assert-time
    /// `term_exceeds_encode_depth` gate, and instantiation can compose depth
    /// round over round — so the reachable depth is input-controlled and the
    /// `()` return type leaves no honest way to cap it.  The visited set
    /// bounds re-expansion of shared DAG nodes (work), not chain depth.
    pub(super) fn add_arith_diseq_split(&mut self, term: TermId, manager: &mut TermManager) {
        let mut visited: FxHashSet<TermId> = FxHashSet::default();
        let mut stack: Vec<TermId> = vec![term];

        while let Some(current) = stack.pop() {
            if !visited.insert(current) {
                continue;
            }

            let Some(t) = manager.get(current).cloned() else {
                continue;
            };

            match &t.kind {
                TermKind::Not(inner) => {
                    let inner_id = *inner;
                    if let Some(inner_t) = manager.get(inner_id).cloned()
                        && let TermKind::Eq(lhs, rhs) = &inner_t.kind
                    {
                        self.add_arith_trichotomy_clause(*lhs, *rhs, manager);
                    }
                    // Also descend into the inner term.
                    stack.push(inner_id);
                }
                TermKind::Distinct(args) => {
                    // `distinct` expands to pairwise disequalities in `encode`; the
                    // theory layer only learns about each pair through the strict
                    // ordering atoms introduced here.
                    let args_clone: Vec<TermId> = args.iter().copied().collect();
                    for i in 0..args_clone.len() {
                        for j in (i + 1)..args_clone.len() {
                            self.add_arith_trichotomy_clause(args_clone[i], args_clone[j], manager);
                        }
                    }
                }
                TermKind::And(args) | TermKind::Or(args) => {
                    // Reverse push so children pop — and their clauses are
                    // emitted — left-to-right, as the recursive DFS did.
                    for &arg in args.iter().rev() {
                        stack.push(arg);
                    }
                }
                TermKind::Implies(_, rhs) => {
                    // Descend into the consequent -- that's where the disequality
                    // typically lives in quantifier instantiation lemmas
                    stack.push(*rhs);
                }
                TermKind::Ite(_, then_br, else_br) => {
                    stack.push(*else_br);
                    stack.push(*then_br);
                }
                _ => {}
            }
        }
    }

    /// Add trichotomy clauses `Eq(a,b) OR Lt(a,b) OR Gt(a,b)` for every
    /// arithmetic `Eq(a,b)` sub-term in the given MBQI instantiation result.
    ///
    /// This ensures that when the SAT solver assigns an arithmetic Eq to false
    /// (disequality), the ArithSolver learns a strict ordering constraint
    /// (Lt or Gt) and doesn't assign equal values.
    ///
    /// Only called for MBQI instantiation results, not for all assertions,
    /// to avoid blowing up the clause database on non-quantified problems.
    ///
    /// Explicit-stack DFS preorder for the same reason as
    /// [`Solver::add_arith_diseq_split`]: instantiation results never pass the
    /// assert-time depth gate, and `()` has no honest cap channel.
    pub(super) fn add_arith_eq_trichotomy(&mut self, term: TermId, manager: &mut TermManager) {
        let mut visited: FxHashSet<TermId> = FxHashSet::default();
        let mut stack: Vec<TermId> = vec![term];

        while let Some(current) = stack.pop() {
            if !visited.insert(current) {
                continue;
            }

            let Some(t) = manager.get(current).cloned() else {
                continue;
            };

            match &t.kind {
                TermKind::Eq(lhs, rhs) => {
                    let lhs_is_numeric = manager.get(*lhs).is_some_and(|lt| {
                        lt.sort == manager.sorts.int_sort || lt.sort == manager.sorts.real_sort
                    });
                    // Only add trichotomy when at least one side is an
                    // uninterpreted function application (Apply). This is the
                    // pattern that appears in injectivity / congruence axioms
                    // where f(a)=f(b) needs to be split into f(a)<f(b) or
                    // f(a)>f(b) when the equality is false.
                    // Avoid Select terms -- the array theory handles those.
                    let lhs_is_apply = manager
                        .get(*lhs)
                        .is_some_and(|lt| matches!(lt.kind, TermKind::Apply { .. }));
                    let rhs_is_apply = manager
                        .get(*rhs)
                        .is_some_and(|rt| matches!(rt.kind, TermKind::Apply { .. }));
                    if lhs_is_numeric && (lhs_is_apply || rhs_is_apply) {
                        let (l, r) = (*lhs, *rhs);
                        // Add trichotomy: Eq(a,b) OR Lt(a,b) OR Gt(a,b)
                        let eq_var = self.get_or_create_var(current);
                        let eq_lit = Lit::pos(eq_var);
                        let lt_term = manager.mk_lt(l, r);
                        let gt_term = manager.mk_gt(l, r);
                        let lt_lit = self.encode(lt_term, manager);
                        let gt_lit = self.encode(gt_term, manager);
                        self.sat.add_clause([eq_lit, lt_lit, gt_lit]);
                    }
                }
                TermKind::Not(arg) => {
                    stack.push(*arg);
                }
                TermKind::And(args) | TermKind::Or(args) => {
                    // Reverse push so children pop left-to-right, preserving
                    // the recursive version's clause-emission order.
                    for &arg in args.iter().rev() {
                        stack.push(arg);
                    }
                }
                TermKind::Implies(lhs, rhs) => {
                    stack.push(*rhs);
                    stack.push(*lhs);
                }
                TermKind::Ite(_, then_br, else_br) => {
                    stack.push(*else_br);
                    stack.push(*then_br);
                }
                _ => {}
            }
        }
    }
}
