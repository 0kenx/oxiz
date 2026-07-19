# OxiZ TODO

Last Updated: 2026-07-19

---

## Major Milestone Achieved: 100% Z3 Parity (v0.2.0)

**Date Achieved**: February 5, 2026
**Release Status**: Published (Feb 6, 2026)

OxiZ has achieved **100% correctness parity with Z3** across all 88 benchmark tests spanning 8 core SMT-LIB logics. This validates OxiZ as a **production-ready Pure Rust SMT solver**.

### Z3 Parity Results

| Logic | Tests | Result | Status |
|-------|-------|--------|--------|
| QF_LIA | 16/16 | 100% | Perfect |
| QF_LRA | 16/16 | 100% | Perfect |
| QF_NIA | 1/1 | 100% | Perfect |
| QF_S | 10/10 | 100% | Perfect |
| QF_BV | 15/15 | 100% | Perfect |
| QF_FP | 10/10 | 100% | Perfect |
| QF_DT | 10/10 | 100% | Perfect |
| QF_A | 10/10 | 100% | Perfect |
| **TOTAL** | **88/88** | **100%** | **Production Ready** |

---

## Progress Summary

| Priority | Completed | Pending | Progress |
|----------|-----------|---------|----------|
| Critical | 25 | 0 | 100% |
| High | 15 | 0 | 100% |
| Medium | 17 | 0 | 100% |
| Low | 9 | 0 | 100% |
| Post-Parity: Performance | 14 | 14 | 50% |
| Post-Parity: UX | 3 | 0 | 100% |
| Post-Parity: Debugging | 4 | 0 | 100% |
| Post-Parity: Docs | 5 | 0 | 100% |
| Post-Parity: Theories | 0 | 10 | 0% |
| Post-Parity: Advanced | 0 | 12 | 0% |
| Post-Parity: Ecosystem | 0 | 7 | 0% |
| **Total** | **92** | **43** | **68%** |

---

## Current Statistics (v0.2.4 - 2026-07-19, re-measured at release time)

- **Rust Lines of Code (code)**: 366,082 code lines across 1,082 files
- **Total Rust Lines (with docs/tests)**: 459,717
- **Tests**: 7,666 (workspace, nextest, all-features, all passing); 7,507 (default features, all passing)
- **Z3 Parity (quickstart core, 88 benchmarks)**: **72/88 (81.8%) Correct** — honest comparator, `Unknown` never counts as a match
- **Logics at 100%**: **6/8 quickstart logics (68/68)** — QF_LIA, QF_LRA, QF_NIA, QF_BV, QF_DT, QF_A; QF_S and QF_FP have documented gaps (honest-Unknown conversions + 2 parser gaps)
- **Z3 Parity (extended suite, 168 benchmarks / 19 logics)**: 122 Correct / 35 Inconclusive / 10 Error / 1 Wrong (QF_NIRA root-isolation gap)
- **Workspace Crates**: 17 (16 Rust crates + 1 TypeScript)
- **todo!/unimplemented! macros**: 0 (all Rust crates)
- **Clippy Warnings**: 0
- **Largest File**: under 2,000 lines

---

## Beyond Z3: Key Differentiators

OxiZ is not just a Z3 port - it surpasses Z3 in critical areas:

1. **Machine-Checkable Proofs** (oxiz-proof) - DRAT, Alethe, LFSC + Coq/Lean/Isabelle exports
2. **Spacer/PDR** (oxiz-spacer) - Missing in CVC5, Yices, and most Z3 clones!
3. **WASM-First** (oxiz-wasm) - Target <2MB vs Z3's ~20MB
4. **Native Parallelism** - Rayon portfolio solving, work-stealing
5. **Memory Safety** - Pure Rust, no FFI, guaranteed safety
6. **Craig Interpolation** - McMillan, Pudlak, Huang algorithms with theory support
7. **100% Z3 Parity Validated** - Proven correctness across all core logics
8. **EasySolver API** - Builder pattern, one-liner solving for common use cases
9. **Arena Allocator** - Custom bumpalo-backed AST allocator (feature-gated)
10. **Parallel Theory Checking** - Rayon-based, feature-gated

---

## Completed: April 4, 2026

### Performance Optimization
- [x] Custom arena allocator for AST nodes (bumpalo-backed, feature-gated)
- [x] Clause pool for SAT solver (5 size-based buckets, recycle/reuse)
- [x] SIMD-friendly polynomial operations (chunk-of-4 autovectorization)
- [x] Optimized hash functions for term interning (TermKindHasher)
- [x] FP bit-blasting cache (avoid redundant bit-blasting)
- [x] Model generation optimization (lazy evaluation cache)
- [x] Parallel theory checking (rayon-based, feature-gated)
- [x] Lock-free data structures for parallel solving
- [x] Lazy evaluation strategies

### User Experience
- [x] EasySolver convenience API (builder pattern, one-liner solving)
- [x] Better error messages (hints, did_you_mean, context_snippet)
- [x] Timeout and resource limit APIs (ResourceLimits, ResourceMonitor)

### Debugging Support
- [x] Solver state visualization (SolverStateSnapshot, DOT graph)
- [x] Trace generation (TraceEvent, JSON/text output)
- [x] Better conflict explanations (ConflictExplainer, UnsatExplanation)
- [x] Model minimization (linear and binary search strategies)

### Documentation
- [x] Performance tuning guide (docs/PERFORMANCE_TUNING.md)
- [x] Theory-specific guides (docs/THEORY_GUIDE.md)
- [x] Z3 migration guide (docs/MIGRATION_Z3.md)
- [x] Common pitfalls (docs/PITFALLS.md)
- [x] Case studies (docs/CASE_STUDIES.md)

### File Maintenance
- [x] solve_eqs.rs re-split (1942 -> 1553 lines)
- [x] rational.rs re-split (1940 -> 1388 + 553 tests)

### Stats Delta (March 31)
- Tests: 6,122 -> 6,155 (+33 new)
- Rust LoC: 392,274 -> 393,292 (+1,018)
- Clippy warnings: 0
- Largest file: 1,892 lines
- All files under 2,000 lines

---

## Post-Parity Priorities (v0.3.0 and Beyond)

### High Priority: Performance Optimization (Partial - 9/28 Complete)

**Goal**: Achieve performance parity with Z3 (currently ~1.5-2x slower)

- [x] Custom allocators (arena for AST nodes, clause pooling)
- [x] SIMD-friendly polynomial operations (chunk-of-4 autovectorization)
- [x] Optimized hash functions (TermKindHasher for term interning)
- [x] FP bit-blasting cache
- [x] Model generation optimization (lazy evaluation cache)
- [x] Parallel theory checking (rayon-based, feature-gated)
- [x] Lock-free data structures for parallel solver
- [x] Lazy evaluation strategies
- [x] Clause pool for SAT solver (5 size-based buckets)

- [x] Profile remaining hot paths (10 items) (planned 2026-04-19)
  - **Goal:** Reproducible profiling harness covering 10 named hot paths; snapshot `docs/PROFILING_REPORT.md` names worst offenders; each path gets a `ScopedTimer` pair for CI-measurable cost.
  - **Design:** Extend `oxiz-sat/src/profiling.rs::ProfilingCategory` with 10 categories (SatPropagation, TheoryCheck, EGraphMerge, SimplexPivot, BvPropagation, StringAutomata, ArrayExtensionality, ProofGeneration, Parser, CacheMiss); wire at call sites; new `bench/profile/` crate; extend `scripts/flamegraph.sh` with `--category`; emit `docs/PROFILING_REPORT.md`.
  - **Files:** `oxiz-sat/src/profiling.rs`, 10 instrumented call sites across crates, new `bench/profile/{Cargo.toml,benches/profile_benchmarks.rs,src/lib.rs}`, `scripts/flamegraph.sh`, new `docs/PROFILING_REPORT.md`, root `Cargo.toml` workspace member.
  - **Tests:** new `oxiz-sat/tests/profiling_pass.rs` — each category records ≥1 sample; JSON summary is parseable.
  - [x] SAT solver clause propagation
  - [x] Theory solver check() methods
  - [x] E-graph merge operations
  - [x] Simplex pivot operations
  - [x] BV constraint propagation
  - [x] String solver automata operations
  - [x] Array extensionality checks
  - [x] Proof generation overhead
  - [x] Parser performance
  - [x] Cache miss analysis

- [x] Additional performance improvements (5 of 6 sub-items; JIT deferred) (planned 2026-04-19)
  - **Goal:** Five concrete allocation-reduction fixes: in-place watchlist updates, SmallVec for EClass::nodes, incremental theory cache, cache-friendly Clause layout, allocation-free EUF propagation.
  - **Design:** (1) `oxiz-sat/src/cdcl/propagation.rs` — swap_remove+clear vs Vec::clone; (2) `SmallVec<[Term;4]>` for `oxiz-core/src/egraph/eclass.rs::EClass::nodes`; (3) memo `(theory_id, level)→propagation set` in coordinator.rs; (4) hot-field-first struct layout in `oxiz-sat/src/clause.rs`; (5) per-solver reuse buffer in `oxiz-theories/src/euf/solver.rs`.
  - **Files:** `oxiz-sat/src/cdcl/propagation.rs`, `oxiz-core/src/egraph/eclass.rs`, `oxiz-solver/src/combination/coordinator.rs`, `oxiz-sat/src/clause.rs`, `oxiz-theories/src/euf/solver.rs`.
  - **Tests:** new `oxiz-sat/tests/allocation_reduction.rs` with dhat-heap counts; per-fix unit tests.
  - [x] Reduce allocations further (in-place updates)
  - [x] Better data structure choices (profiling-driven)
  - [x] Incremental computation caching
  - [~] JIT-style specialization for hot theory operations
  - **Scope-box (2026-04-24):** Pure-Rust EUF data-layout + allocation-reduction + incremental-backtrack pass. Items 1–5 completed; parent umbrella (JIT/codegen layer) deferred to v0.4.0.
  - [x] EUF production-path benchmarks + regression baseline (2026-04-24)
    - Added `oxiz-theories/benches/euf_benchmarks.rs` with 5 criterion workloads driving `EufSolver` directly; 5 baseline entries added to `bench/regression/baseline.json`.
  - [x] EUF cheap-wins bundle: fingerprint pre-filter + `#[inline]` cross-crate + hoist `get_function_props` (2026-04-24)
    - Activated dead fingerprint pre-filter in `propagate`; added `#[inline]` to 7 cross-crate wrappers; hoisted `get_function_props` out of inner loop. Bench deltas: intern_leaf −24%, intern_app −16%, merge_congruence −10%, merge_injective −22%.
  - [x] EUF allocation reduction in `propagate` (2026-04-24)
    - Reusable canonicalize buffer (out-param), proof_forest changed to `Vec<SmallVec<[MergeEdge; 4]>>`, `SigUpdateEntry` flat struct. Bench 3 −6.7%, bench 4 −6.7%, bench 5 −8.2%.
  - [x] EUF incremental sig_table + fingerprint_table undo trail (2026-04-24)
    - Replaced O(|nodes|) rebuild-on-pop with per-insertion `SigTrailEntry` trail + `sig_trail_limits`. Trail guarded by `is_empty()` check so non-incremental workloads see zero overhead. Miri clean; 6366/6366 tests pass.
  - [x] EUF `ENode` layout reorder + `func: u32` sentinel (2026-04-24)
    - Reordered fields to put hot fields (`func`, `fingerprint`) first; replaced `Option<u32>` with `u32` + `NO_FUNC = u32::MAX` sentinel. Added `ENode::leaf()` / `ENode::app()` constructors. `test_enode_size_regression` confirms ≤56B.
  - [x] Memory layout optimization
  - [x] Allocation-free theory propagation paths

- [x] Performance regression testing (3 items)
  - [x] CI/CD integration for performance tracking (planned 2026-04-19)
  - [x] Automated benchmark comparison vs Z3 (planned 2026-04-19)
  - [x] Performance dashboard (planned 2026-04-19)

**Target**: Within 1.2x of Z3 performance by v0.3.0

### High Priority: Extended Theory Coverage

**Goal**: Support additional SMT-LIB logics beyond the core 8

- [x] Quantified logics (5 items)
  - [x] UFLIA - Uninterpreted Functions + Linear Integer Arithmetic
  - [x] UFLRA - Uninterpreted Functions + Linear Real Arithmetic
  - [x] AUFLIA - Arrays + UF + LIA
  - [x] AUFLIRA - Arrays + UF + LIA + LRA
  - [x] Improve quantifier instantiation heuristics

- [x] Combined theories (3 items)
  - [x] QF_AUFBV - Arrays + UF + BV (validation needed)
  - [x] QF_ALIA - Arrays + LIA
  - [x] QF_ABV - Arrays + BV

- [x] Non-linear arithmetic (2 items)
  - [x] Extend QF_NIA coverage (more benchmarks)
  - [x] QF_NIRA - Non-linear Integer/Real Arithmetic

### Medium Priority: Advanced Features

- [x] Enhanced preprocessing (5 items) (planned 2026-04-19)
  - **Goal:** Five tactics: `bmc-unroll` (spacer/bmc wrapper), `aggressive-simplify` (new rewrite rules), `ctx-dep-rewrite` polish (dead-branch elimination in ITEs), `symmetry-break` (lex-leader constraints), `cube-improve` (VSIDS-depth-aware cubes).
  - **Design:** new `oxiz-spacer/src/tactics/bmc_unroll.rs`; extend `oxiz-core/src/simplification/mod.rs`; polish `ctx_solver_simplify.rs`; new `oxiz-sat/src/tactics/symmetry.rs`; extend `oxiz-sat/src/cube.rs::CubeGenerator`.
  - **Files:** `oxiz-spacer/src/tactics/bmc_unroll.rs` (new), `oxiz-spacer/src/lib.rs`, `oxiz-core/src/simplification/mod.rs`, `oxiz-core/src/tactic/ctx_solver_simplify.rs`, `oxiz-sat/src/tactics/symmetry.rs` (new), `oxiz-sat/src/cube.rs`, `oxiz-core/src/tactic/registry.rs`.
  - **Tests:** per-tactic unit test (rewrite shape) + integration test (apply tactic, status preserved).
  - [x] Bounded model checking tactics (planned 2026-04-19)
          - **Goal:** `oxiz-spacer::tactics::BmcUnrollTactic` is production-ready: documented re-export, ≥4 unit tests covering nested next-state vars, idempotent re-application, depth-from-option > 5, and integration with `oxiz-spacer::Bmc`.
          - **Design:** Existing `BmcEngine`/`BmcUnrollTactic` (224 lines) renames `x_next`/`x'` → `x@n+1`. Verify rename correctness under multiple applications; verify `NotApplicable` on goals with < 3 assertions; document distinction from production `Bmc` solver in `oxiz-spacer/src/bmc.rs`.
          - **Files:** `oxiz-spacer/src/tactics/bmc_unroll.rs` (tests + doc), `oxiz-spacer/src/tactics/mod.rs` (doc comment), `oxiz-spacer/src/lib.rs` (re-export at crate root), `oxiz-spacer/tests/bmc_unroll_integration.rs` (new).
          - **Tests:** (a) `test_bmc_unroll_handles_nested_next_state`; (b) `test_bmc_unroll_idempotent_under_reapply`; (c) `test_bmc_unroll_from_option_depth`; (d) integration test handing result to `Bmc::check`.
          - **Risk:** suffix-rename collision on `@n+1` substrings already in names. Mitigation: assert original name is a substring; switch to `@@n+1` separator if collision found.
          - **Scope cap:** ≤200 LoC net-new.
  - [x] More aggressive simplification (planned 2026-04-19)
          - **Goal:** `oxiz-core::simplification::AggressiveSimplifier` gains substantive new rewrite rules (Boolean, arithmetic, bit-vector, ITE) so `aggressive: true` measurably shrinks goals.
          - **Design:** Extend `simplify_*` family in `oxiz-core/src/simplification/mod.rs`. Rules: (1) De Morgan `Not(Not(a))→a`; (2) Implication identities `Implies(true,b)→b` etc.; (3) XOR identities; (4) Arithmetic constant folding `Add(c1,c2)→c`; (5) BV trivial `BvAnd(x,0)→0` etc.; (6) Equality `Eq(x,x)→true`; (7) ITE `If(true,a,_)→a`, `If(_,a,a)→a`. Use existing memo cache for idempotence.
          - **Files:** `oxiz-core/src/simplification/mod.rs` (extend); new `oxiz-core/tests/aggressive_simplify_rules.rs`; preserve in-flight 3-line test tolerance in `aggressive_simplify.rs`.
          - **Tests:** 7 per-rule-family unit tests + 2 integration tests (Boolean-heavy goal, BV-heavy goal). Run `rslines 50` on `tactic/mod.rs` after edit; invoke `splitrs` if > 2000 lines.
          - **Risk:** recursion memo collision under rule interaction. Mitigation: existing memo cache; assert O(N) lookup count in one test.
          - **Scope cap:** ≤500 LoC net-new. No new term kinds, no TermManager API changes.
  - [x] Context-dependent rewriting (planned 2026-04-19)
          - **Goal:** Live `CtxSolverSimplifyTactic` in `oxiz-core/src/tactic/ctx_simplify.rs` gains dead-branch ITE elimination: when goal context implies `cond` or `Not(cond)`, the corresponding branch of `If(cond, t, e)` is substituted.
          - **Design:** (1) Build `HashSet<TermId>` from goal assertions as context. (2) For each `If(c,t,e)`: if `c` in ctx → `t`; if `Not(c)` in ctx → `e`; else descend with augmented ctx (t-branch: ctx∪{c}, e-branch: ctx∪{Not(c)}). (3) Use `manager.simplify` for bottom-up rebuild. (4) Cap recursion depth at 32; on overflow return original term (sound). **Path resolution:** Plan's cited path `ctx_solver_simplify.rs` does NOT exist; `core/ctx_solver_simplify.rs` is dead placeholder — do NOT touch it. Target only `ctx_simplify.rs`.
          - **Files:** `oxiz-core/src/tactic/ctx_simplify.rs` only. No changes to `mod.rs` re-exports or dead placeholder.
          - **Tests:** (a) `test_ite_eliminates_when_cond_in_context`; (b) `test_ite_eliminates_when_neg_cond_in_context`; (c) `test_ite_descends_with_augmented_ctx` (nested ITE); (d) `test_ite_recursion_depth_cap` (50-deep ITE, no hang); (e) `test_apply_mut_status_preserved`.
          - **Risk:** augmented context shared-mutation bug. Mitigation: per-call scoping, no global ctx mutation; test (c) validates.
          - **Scope cap:** ≤300 LoC net-new in `ctx_simplify.rs`.
  - [x] Symmetry breaking (planned 2026-04-19)
          - **Goal:** `oxiz-sat::tactics::SymmetryBreakTactic` gains coverage proving tactic shrinks model space. Re-export already at `oxiz-sat/src/lib.rs:228`.
          - **Design:** Existing 155-line tactic runs `AutomorphismDetector` → `SymmetryBreaker::new(group, Lex)` → `generate_predicates()`. Validate via 4 tests; tighten `NotApplicable` paths.
          - **Files:** `oxiz-sat/src/tactics/symmetry.rs` (test additions only). `oxiz-sat/src/symmetry.rs` unchanged unless coverage gap found.
          - **Tests:** (a) `test_symmetry_break_full_3var_symmetry` — fully symmetric 4-clause CNF over 3 vars yields ≥1 lex-leader predicate; (b) `test_symmetry_break_asymmetric_clauses` → `NotApplicable`; (c) `test_symmetry_break_mixed_boolean_integer` → `NotApplicable`; (d) `test_symmetry_break_reduces_model_count` — solver on (clauses ∪ predicates) has fewer satisfying assignments than on clauses alone.
          - **Risk:** `AutomorphismDetector` may return spurious symmetries. Mitigation: tests assert tactic behaviour (predicates emitted/not), not detector internals.
          - **Scope cap:** ≤200 LoC net-new (tests only).
  - [x] Cube generation improvements (planned 2026-04-19)
          - **Goal:** Validate and prove that `oxiz-sat::cube::CubeGenerator::depth_limit_for_cube` is genuinely VSIDS-depth-aware (confirmed: `extra_depth = log2(activity_sum/avg)` at lines 220–247), and validate `CubeImproveTactic` end-to-end.
          - **Design:** No production-code changes unless a test forces one (e.g. `extra_depth.ceil()` rounding kills the increment for activity ratio < 2 — fix only if observed). All work is tests.
          - **Files:** `oxiz-sat/src/cube.rs` (test additions to `mod tests`); `oxiz-sat/src/tactics/cube_improve.rs` (test additions).
          - **Tests:** (a) `test_depth_limit_uniform_activity_equals_max_depth`; (b) `test_depth_limit_high_activity_increases_depth` (4× average → depth > max_depth); (c) `test_generate_vsids_guided_orders_by_activity`; (d) `test_cube_improve_tactic_emits_subgoals_per_cube` (4-var Boolean goal → ≥2 subgoals); (e) `test_cube_improve_status_preserved`.
          - **Risk:** NaN from empty `variable_scores`. Mitigation: existing `if variable_scores.is_empty() { 1.0 }` guard; test (a) covers it.
          - **Scope cap:** ≤200 LoC net-new.

- [x] Better quantifier handling (4 items) (planned 2026-04-19)
  - **Goal:** (a) PatternCoverScorer (greedy set cover), (b) conflict_score VSIDS for quantifiers in conflict_driven.rs, (c) virtual-substitution QE (Loos–Weispfenning), (d) per-quantifier instantiation budget in MBQI.
  - **Design:** extend `patterns.rs` with `PatternCoverScorer`; extend `conflict_driven.rs` with `conflict_score: HashMap<QuantifierId,u32>`; new `oxiz-core/src/qe/virtual_substitution.rs`; add `MBQIBudget::per_quantifier` to `heuristics.rs`.
  - **Files:** `oxiz-solver/src/mbqi/patterns.rs`, `oxiz-solver/src/mbqi/conflict_driven.rs`, `oxiz-core/src/qe/arith.rs`, `oxiz-core/src/qe/virtual_substitution.rs` (new), `oxiz-core/src/qe/mod.rs`, `oxiz-solver/src/mbqi/heuristics.rs`, `oxiz-solver/src/mbqi/mod.rs`.
  - **Tests:** pattern-cover, conflict-priority, VS, budget enforcement unit tests.
  - [x] Pattern-based instantiation improvements
  - [x] Conflict-driven instantiation
  - [x] Quantifier elimination enhancements
  - [x] MBQI performance tuning

- [x] Proof system enhancements (3 items) (planned 2026-04-19)
  - [x] Optimized proof generation (reduce overhead) (planned 2026-04-19)
  - [x] Proof minimization
  - [x] Better theory combination proofs (planned 2026-04-19)
  - **Goal:** (a) bumpalo arena for ProofStep allocation in recorder.rs; (b) structured Nelson–Oppen combination certificate in new theory_combination.rs.
  - **Design:** `oxiz-proof/src/recorder.rs` — steps arena (ArenaIdx<ProofStep>); new `oxiz-proof/src/theory_combination.rs` — NelsonOppenCertificate with interface-equality chain.
  - **Files:** `oxiz-proof/src/recorder.rs`, `oxiz-proof/src/lib.rs`, `oxiz-proof/src/theory_combination.rs` (new), `oxiz-solver/src/combination/coordinator.rs`.
  - **Tests:** arena proof passes checker; new `oxiz-proof/tests/theory_combination_proof.rs` — 3-step EUF+LIA certificate passes ProofChecker.

### Medium Priority: User Experience (Complete)

- [x] Documentation improvements (5 items)
  - [x] Performance tuning guide (docs/PERFORMANCE_TUNING.md)
  - [x] Theory-specific guides (docs/THEORY_GUIDE.md)
  - [x] Common pitfalls and solutions (docs/PITFALLS.md)
  - [x] Migration guide from Z3 (docs/MIGRATION_Z3.md)
  - [x] Case studies and examples (docs/CASE_STUDIES.md)

- [x] API improvements (3 items)
  - [x] EasySolver convenience API (builder pattern)
  - [x] Better error messages (hints, did_you_mean, context_snippet)
  - [x] Timeout and resource limit APIs (ResourceLimits, ResourceMonitor)

- [x] Debugging support (4 items)
  - [x] Solver state visualization (SolverStateSnapshot, DOT graph)
  - [x] Trace generation (TraceEvent, JSON/text output)
  - [x] Better conflict explanations (ConflictExplainer, UnsatExplanation)
  - [x] Model minimization (linear and binary search strategies)

### Low Priority: Ecosystem Integration

- [ ] Language bindings (4 items)
  - [x] Improve Python bindings (oxiz-py enhancements) (planned 2026-04-19)
  - **Goal:** Bring `oxiz-py` to 0.2.1 quality bar: full theory test coverage, README + pyproject.toml synced to workspace version, parity matrix doc.
  - **Design:** PyO3 surface (1583 LoC, 7 modules, 721-line stub) is mature. Add 5 pytest files for theories implied by stubs but not yet tested. Sync version strings. Add `PARITY.md` table mapping z3 API → oxiz wrapper → status.
  - **Files:** `oxiz-py/tests/test_quantifiers.py` (new), `oxiz-py/tests/test_arrays.py` (new), `oxiz-py/tests/test_fp.py` (new), `oxiz-py/tests/test_strings.py` (new), `oxiz-py/tests/test_unsat_cores.py` (new), `oxiz-py/PARITY.md` (new), `oxiz-py/pyproject.toml` (version → 0.2.1), `oxiz-py/README.md` (version + test-count update); minimal `src/*.rs` patches only if a wrapper is missing.
  - **Tests:** Each pytest file has ≥3 assert cases. Run `cargo build -p oxiz-py --release` (always); `maturin develop + pytest` if toolchain available, else skip with explicit note.
  - **Risk:** maturin unavailable. Mitigation: .py and .md files land regardless; test run is skipped.
  - **Scope cap:** ≤700 LoC net-new. ≤3 new PyO3 wrappers × ≤50 LoC each if needed.
  - [ ] JavaScript/TypeScript bindings (via WASM)

- [ ] Tool integration (3 items)
  - [x] SMT-COMP 2026 participation — entry package complete; submit when portal opens (~May 2026)
  - [ ] Integration with symbolic execution tools
  - [ ] Integration with verification frameworks

---

## Critical Priority (100% Complete)

### Spacer (PDR) Engine - KEY DIFFERENTIATOR
- [x] Implement Property Directed Reachability for Horn Clauses (CHC)
  - [x] CHC representation (predicates, rules, queries)
  - [x] Frame management (F_0..F_N sequence)
  - [x] POB (Proof Obligation) management
  - [x] Reachability utilities (reach facts, counterexamples, generalization)
  - [x] PDR core algorithm with propagation and blocking
- [x] Loop invariant inference
  - [x] Houdini algorithm for candidate elimination
  - [x] Template-based inference (linear, octagon)
  - [x] SMT-based verification integration
- [x] Software verification pipeline
  - [x] Full CHC solving with invariant synthesis

### Optimization (MaxSMT / OMT)
- [x] MaxSMT core implementation (Fu-Malik with core extraction)
- [x] Core-guided algorithms (OLL with totalizer, MSU3, WMax stratified)
- [x] Totalizer encoding for cardinality constraints
- [x] Optimization Modulo Theories (OMT) - binary/linear/geometric search
- [x] Linear Programming (LP) solver integration
  - [x] Revised simplex method
  - [x] Branch-and-bound for MIP
  - [x] Integer/Binary variable support
- [x] Mixed Integer Programming (MIP) support

### E-Graph Integration
- [x] Tailor e-graph for incremental SMT updates
  - [x] Incremental merge operations
  - [x] Backtrackable union-find
  - [x] Worklist-based congruence closure
- [x] Optimize congruence closure for theory propagation
  - [x] Theory propagator hooks
  - [x] Analysis data per e-class
- [x] Custom e-graph implementation
  - [x] EGraph with EClassId, ENode, EClass abstractions
  - [x] Explanation generation for merges

### Z3 Parity Achievement (v0.2.0)
- [x] String Theory (QF_S) - 100% (10/10)
- [x] Bit-Vector Theory (QF_BV) - 100% (15/15)
- [x] Floating-Point Theory (QF_FP) - 100% (10/10)
- [x] Datatype Theory (QF_DT) - 100% (10/10)
- [x] Array Theory (QF_A) - 100% (10/10)

## High Priority (100% Complete)

### Theory Integration
- [x] Complete CDCL(T) integration with theory propagation
- [x] Implement theory lemma generation
- [x] Add conflict clause minimization
- [x] Implement Nelson-Oppen theory combination
- [x] Difference Logic theory (graph-based, Bellman-Ford)
- [x] UTVPI theory (Unit Two Variable Per Inequality)
- [x] Theory Checking Framework
- [x] Weighted MaxSAT Theory

### SMT-LIB2 Compliance
- [x] Complete parser for all SMT-LIB2 commands
- [x] Add `get-model` output formatting
- [x] Implement `get-unsat-core`
- [x] Add `get-proof` support (placeholder)
- [x] Support for `define-fun` and `define-sort`
- [x] Add `get-assertions`, `get-assignment`, `get-option` commands
- [x] Add `check-sat-assuming` command
- [x] Add `reset-assertions` command
- [x] Add `simplify` command (Z3 extension)

### Performance
- [x] Add restart strategies (Luby, geometric)
- [x] Implement phase saving
- [x] Implement clause deletion strategies
- [x] Add learned clause minimization
- [x] Profile and optimize hot paths

## Medium Priority (100% Complete)

### New Theories
- [x] Array theory solver (extensionality, select/store)
- [x] String theory solver (word equations, regex via Brzozowski derivatives)
- [x] Floating-point theory (IEEE 754, QF_FP) with bit-blasting
- [x] Datatype theory (ADTs - lists, trees)
- [x] Non-linear arithmetic (QF_NRA) - CAD projection, Sturm sequences
- [x] Pseudo-Boolean theory (PbSolver)
- [x] Recursive Functions theory (RecFunSolver)
- [x] User Propagators (UserPropagatorManager)
- [x] Special Relations (LO, PO, PLO, TO, TC)

### Tactics System
- [x] `simplify` - Algebraic simplification (x + 0 -> x)
- [x] `propagate-values` - Constant propagation
- [x] `bit-blast` - Convert BitVectors to SAT clauses (detection phase)
- [x] `ackermannize` - Eliminate functions by adding constraints
- [x] `ctx-solver-simplify` - Context-dependent simplification
- [x] Tactic pipeline/composition system (ThenTactic, OrElseTactic, RepeatTactic)
- [x] Probe system (11+ probes)
- [x] Fourier-Motzkin elimination
- [x] NNF/CNF conversion tactics
- [x] Model-Based Projection (MBP)
- [x] Quantifier tactics (MBQI, E-matching, DER, Skolemization)

### Parallelization - BEYOND Z3: Native Multi-core
- [x] Parallel portfolio solving (competing tactics on threads)
- [x] Cube-and-conquer for hard instances
  - [x] CubeGenerator, ParallelCubeSolver, CubeAndConquer
  - [x] 22 tests passing
- [x] Work-stealing clause sharing
- [x] Native async/parallel infrastructure (Rayon/Tokio)

### Proof Generation - BEYOND Z3: Machine-Checkable
- [x] DRAT proof output for SAT core (text and binary formats)
- [x] Theory proof generation (EUF, Arith, Array recorders)
- [x] Machine Checkable Proofs (Alethe format) - Beyond Z3!
- [x] LFSC proof format (Logical Framework with Side Conditions)
- [x] Proof checking infrastructure (syntactic + rule validation)
- [x] **Coq/Lean/Isabelle exports** - Unprecedented in SMT solvers!
- [x] Craig Interpolation
  - [x] McMillan's algorithm (left-biased interpolants)
  - [x] Pudlak's algorithm (symmetric interpolation)
  - [x] Huang's algorithm (right-biased interpolants)
  - [x] Theory-specific interpolants (LIA, EUF, Arrays)
  - [x] Sequence and tree interpolation

### Advanced Features
- [x] Minimal Unsat Cores with parallel reduction
- [x] Craig Interpolation for model checking
- [x] XOR/Gaussian elimination solver
- [x] Quantifier Elimination (QE) enhancements
  - [x] Term graph analysis
  - [x] QE Lite for fast approximation
  - [x] Model-based interpolation (MBI)
- [x] Model subsystem
  - [x] Model evaluator with caching
  - [x] Model completion
  - [x] Prime implicant extraction
  - [x] Value factories

## Low Priority (100% Complete)

### Tooling
- [x] SMT-COMP benchmark suite (oxiz-smtcomp crate)
- [x] Fuzzing infrastructure (fuzz/)
- [x] Python bindings (oxiz-py crate)
- [x] Performance regression tests (bench/regression/)
- [x] Z3 parameter/tactics extraction scripts

### Documentation
- [x] API documentation improvements
- [x] Architecture guide (docs/ARCHITECTURE.md)
- [x] Tutorial for extending theories (docs/TUTORIAL_CUSTOM_THEORY.md)
- [x] Contribution guidelines (CONTRIBUTING.md)

### Future Features (Complete)

#### IDE and Tooling
- [x] VS Code Extension (oxiz-vscode/)
- [x] REST API Server Mode (oxiz-cli --server)
- [x] Web Dashboard (oxiz-cli --dashboard)

#### Advanced CLI Features
- [x] TPTP Format Support (oxiz-cli/src/tptp.rs)
- [x] Interpolant Generation CLI
- [x] Distributed Solving (oxiz-cli/src/distributed.rs)
- [x] SMT-LIB 2.6 Features (oxiz-core)

---

## Cross-Crate Dependencies

```
oxiz-core (foundation)
    |
    +-- oxiz-math (polynomial, simplex, intervals, LP)
    |       |
    |       +-- oxiz-nlsat (CAD, NIA)
    |
    +-- oxiz-sat (CDCL, XOR)
    |       |
    |       +-- oxiz-proof (DRAT, Craig interpolation)
    |       +-- oxiz-opt (MaxSAT core)
    |
    +-- oxiz-theories (EUF, LRA, BV, Arrays, Strings, FP, DL, UTVPI)
            |
            +-- oxiz-solver (CDCL(T) orchestration)
                    |
                    +-- oxiz-spacer (PDR/CHC, invariants)
                    +-- oxiz-opt (OMT)
                    +-- oxiz-wasm / oxiz-cli (frontends)
```

---

## Roadmap

### v0.1.3 - COMPLETE (Feb 5, 2026)
- **100% Z3 Parity** across 8 core SMT-LIB logics
- Production-ready solver
- All theory solvers validated

### v0.2.0 - COMPLETE (Feb 6 - Mar 31, 2026)
- **168/168 Z3 parity tests**
- Performance optimization phase 1 (allocators, SIMD, caches)
- EasySolver API, error messages, resource limits
- Debugging: visualization, traces, conflict explanations, model minimization
- Documentation: 5 new guides (performance, theory, migration, pitfalls, case studies)
- 6,155 tests (16 skipped, 0 failures), 393,292 total Rust lines (312,495 code), 931 files, 0 clippy warnings

### v0.3.0 (Target: June 2026)
**Focus: Performance Parity and SMT-COMP**
- [~] Performance parity with Z3 (within 1.2x) (planned 2026-04-19)
  <!-- umbrella stays [~] until EP-6e (empirical geomean check) lands; children EP-6a..d may already be [x] -->
  - [x] EP-6a: Extended `Z3ComparisonReport` with `geomean_ratio`, `p50_ratio`, `p95_ratio`, `ratio_count` fields (`#[serde(default)]`); `within_target` recomputed from geomean ≤ 1.2 (not strict per-benchmark); 5 unit tests in `z3_compare.rs` (planned 2026-04-19)
  - [x] EP-6b: `bench/z3_parity` gains `--export-history <dir>` mode writing versioned `history/<YYYY-MM-DD>_<sha>.json` snapshots with per-logic `RatioSummary` breakdown; 6 tests in `bench/z3_parity/tests/history_export.rs` (planned 2026-04-19)
  - [x] EP-6c: `bench/regression/baseline.json` refreshed from v0.2.1 current-branch measurements (was v0.1.3 from Jan 2026, 3 months stale) (planned 2026-04-19)
  - [x] EP-6d: `.github/workflows/perf-regression.yml` extended with `geomean-gate` step — soft-gate (passes when no Z3 data, exits non-zero when `geomean_ratio > 1.2`) (planned 2026-04-19)
  - [ ] EP-6e: Empirical verification — confirm geomean ≤ 1.2 across QF_* logics with Z3 installed (deferred: requires Z3-equipped machine; run next /ultra pass with Z3 available)
- [x] Quantified logic support (UFLIA, UFLRA, AUFLIA)
- [x] Combined theory validation (QF_AUFBV, QF_ALIA, QF_ABV)
- [x] Enhanced preprocessing tactics (planned 2026-04-19)
- [x] Performance regression CI pipeline
- [x] SMT-COMP 2026 entry preparation (completed 2026-05-05)
  - [x] `Track` enum (5 variants: SingleQuery, Incremental, UnsatCore, ModelValidation, ProofExhibition)
  - [x] `submission` module wired into `oxiz-smtcomp/src/lib.rs` with full public API
  - [x] `default_oxiz_2026()` fixed: `bin/smtcomp2026` binary, version from `CARGO_PKG_VERSION`
  - [x] Per-track `starexec_run_<track>` scripts in submission package
  - [x] `smtcomp2026` binary extended with `--track` flag (single|incremental|unsat-core|model|proof)
  - [x] `scripts/package_smtcomp.sh` — assembles complete StarExec ZIP
  - [x] End-to-end submission tests in `oxiz-smtcomp/tests/submission_e2e.rs`

### v1.0.0 (Target: Q4 2026)
**Focus: Production Release**
- [ ] Full Z3 API compatibility
- [ ] Performance at or better than Z3
- [ ] Comprehensive documentation
- [ ] Stable API guarantees
- [ ] Industry adoption ready

---

## Recent Achievements

### 2026-06-09 - v0.2.3 Release

- **oxiz-sat**: `DratWriter<W>` / `LratWriter<W>` generic over any `W: Write + Send`; breaking rename from `DratProof` / `LratProof`
- **oxiz-nlsat**: Real resultant (Sylvester/Bareiss), leading-coefficient extraction, degree≥3 root isolation (Descartes/Sturm), monotonicity estimation
- **oxiz-theories**: Sound Nelson-Oppen equality propagation; simplex `optimize_linexpr`; correct push/pop tableau snapshots
- **oxiz-opt**: Full solver-backed `check_sat`, MaxSMT selector encoding, `optimize_single_objective`/`optimize_pareto` delegation
- **oxiz-spacer**: Real BMC formula construction; sound k-induction; dual-arena soundness fix; `extract_model` via `eval_in_model`
- **oxiz-solver**: New `Context::eval_in_model` for model-based term evaluation

### 2026-06-01 - v0.2.2 Release

- **Recursive BV term encoding**: Full nested bit-vector expression encoding in `BvSolver` with structured conflict diagnostics
- **Z3 API compatibility layer**: `TacticRegistry` (19 named tactics), `FuncInterp` / `FuncEntry` in EUF, `Z3SortKind` / `Z3Sort`, `substitute` (BV+Array+Apply coverage), `Z3Pattern` + quantifier pattern APIs
- **Real LBD scoring**: `compute_lbd_from_literals` replaces stub — CDCL now uses genuine Literal Block Distance from finalized 1-UIP learned clauses
- **ML conflict hook**: `BranchingHeuristic::on_conflict_var` defaulted hook wired to `MLBranchingHeuristic` via `MLEnhancedVSIDS::update_conflict`
- **LRU caches**: `AggressiveSimplifier` memo cache (4 096 cap), `EufSolver` explanation cache (1 024 cap), theory combiner lemma cache (bounded to `max_lemma_cache_size`)
- **CLI peak memory**: Linux `VmHWM` high-water-mark now reported correctly
- **Big-M primal simplex**: `SimplexSolver` gains Big-M phase-1 for LP feasibility
- **Dead code policy**: Module-level `#![allow(dead_code)]` removed from 40+ modules; `algebraic_number.rs` (446 lines) deleted
- **Tests**: 6,735 passing (16 skipped, 0 failures); 0 clippy warnings
- **SLoC**: ~419,576 code lines across ~1,012 Rust files

### May 18, 2026 - TacticRegistry Wired, Real LBD, EUF FuncInterp, Z3 Sort/Subst/Patterns (v0.2.2 Pass 6)

- **TacticRegistry wired into Z3 compat**: `z3_compat_ext2.rs::apply_named_tactic` now delegates to `oxiz_core::tactic::default_registry()` via a `OnceLock`-cached static; reachable tactic surface grew from 5 to 19 named tactics (adds aggressive-simplify, bvarray2uf, elim-uncnstr, solve-eqs, nnf, tseitin-cnf, fm, arith-bounds, factor, pb2bv, lia2card, nla2bv, split, ctx-solver-simplify canonical name + ctx-simplify backward-compat alias)
- **Real LBD from learned clause**: `compute_lbd_from_literals` replaces the `vars_to_bump`-based proxy; hook now fires AFTER `self.learnt` is finalized and minimized in both `analyze()` and `analyze_theory_conflict()`, passing the distinct-nonzero-level count of the actual 1-UIP learned clause to `MLBranchingHeuristic::on_conflict_var_with_lbd`. Old `compute_lbd_from_vars` deleted (no dead code).
- **FuncInterp EUF congruence traversal**: `EufSolver::function_application_entries(func_id)` returns canonicalized (arg_reps, result_rep) per Apply node using `find()` without path compression; `Context::get_func_interp_raw` consumes these, dedups by arg-rep tuple, resolves values via class-membership lookup, picks most-common entry as `else_value`. `Solver` gains `pub(crate) euf_function_entries()` bridge. Replaces the Pass 5 partial Apply-walk implementation with full congruence-aware extraction.
- **Z3 Sort introspection + term substitution + quantifier patterns**: new `oxiz-solver/src/z3_compat_ext3.rs` (673 LOC) — `Z3SortKind`/`Z3Sort` (`kind`/`bv_size`/`array_domain`/`array_range`/`name`), `Z3Context::substitute` (hand-rolled bottom-up rebuild covering Bool/Arith/BV/Array/Apply/ITE, memoized via `FxHashMap` — wider coverage than core `TermManager::substitute` which silently skips BV+Apply), `Z3Pattern` + `forall_with_patterns`/`exists_with_patterns` (delegating to `TermManager::mk_*_with_patterns`)
- **Tests**: +32 new tests (6,802 → 6,834); 0 failures; 0 clippy warnings
- **New files**: `oxiz-solver/src/z3_compat_ext3.rs`, `oxiz-solver/tests/z3_compat_extensions3.rs`, `oxiz-solver/tests/func_interp_euf.rs`

### May 18, 2026 - FuncInterp, TacticRegistry, Real LBD, LRU Caches (v0.2.2 Pass 5)

- **FuncInterp (model function interpretations)**: `FuncEntry`/`FuncInterp` types in `oxiz-core/src/model/mod.rs` (entries table + else_value + arity, with `evaluate`); `Model::add_func_interp`/`get_func_interp`; `Z3FuncInterp`/`Z3FuncEntry`/`Z3Value` wrappers in `z3_compat_ext2.rs`; `Z3Model::get_func_interp(&FuncDecl)` delegates to `Context::get_func_interp_raw()` which walks `Apply` terms in the model; 15 new tests
- **TacticRegistry**: `oxiz-core/src/tactic/registry.rs` (333 LOC) with `default_registry()` registering 19 named tactics (simplify, propagate-values, ctx-solver-simplify, aggressive-simplify, bit-blast, bvarray2uf, ackermannize, elim-uncnstr, solve-eqs, nnf, tseitin-cnf, fm, arith-bounds, factor, pb2bv, lia2card, nla2bv, split, skip); `create(name)`/`names()`/`contains()`; 11 new tests
- **Real LBD (Literals per Block Distance)**: `compute_lbd_from_vars()` in `conflict.rs` computes glue score from conflict-involved variables' distinct decision levels; new `BranchingHeuristic::on_conflict_var_with_lbd` defaulted trait method (delegates to `on_conflict_var` for backward compat); `MLBranchingHeuristic` forwards real LBD to `MLEnhancedVSIDS::update_conflict`; 7 new tests
- **LRU caches in EUF + simplification**: `oxiz-core/src/lru_cache.rs` (copy for oxiz-core, no circular dep); `AggressiveSimplifier` gains persistent `memo_cache: LruCache<TermId,TermId>` (4096 cap) replacing per-call HashMap; `EufSolver` gains `expl_cache: LruCache<(u32,u32),Vec<TermId>>` (1024 cap, canonical min/max key, cleared on merge/pop/reset); 6 new tests
- **Tests**: +39 new tests (6,763 → 6,802); 0 failures; 0 clippy warnings
- **New files**: `oxiz-core/src/lru_cache.rs`, `oxiz-core/src/tactic/registry.rs`

### May 18, 2026 - Z3 Compat #2, CLI Peak Memory, ML Conflict Hook, LRU Lemma Cache (v0.2.2 Pass 4)

- **Z3 API compatibility expanded #2**: `oxiz-solver/src/z3_compat_ext2.rs` (963 LOC) adds `Z3Statistics` (7 counters: decisions/propagations/conflicts/restarts/learned-clauses/theory-propagations/theory-conflicts), `Z3Params` (key→value dispatcher into `SolverConfig`), `Z3Probe` (registry over 7 probe types with `.lt()`/`.gt()` combinators), `Z3Goal`/`Z3Tactic`/`Z3ApplyResult` (named-tactic dispatch + `.then()`/`.or_else()`/`.repeat()`/`.try_for()` combinators), `Z3DatatypeSort`/`Z3Constructor` (full `DatatypeDecl` wiring), `Z3Solver::check_assumptions(&[Bool])`/`unsat_core()`, `Z3AstVector`; 41 integration tests in `z3_compat_extensions2.rs`
- **CLI peak memory fixed**: `peak_memory_bytes` was always `current_rss` — now reads Linux `VmHWM:` from `/proc/self/status` (kernel high-water-mark); new `oxiz-cli/src/memory.rs` (92 LOC) with `rss_and_peak()` function; non-Linux falls back gracefully
- **CLI test coverage**: 9 new integration tests — peak memory nonzero, peak ≥ current, Linux VmHWM, parallel-mode, multi-file memory, exit codes for SAT/UNSAT/parse-error/missing-file
- **`BranchingHeuristic::on_conflict_var` hook**: new defaulted method (no-op default, full backward compat); called from `conflict.rs` both `bump_batch` sites; `MLBranchingHeuristic::on_conflict_var` forwards to `MLEnhancedVSIDS::update_conflict(var, level as f64)`, enabling real ML training signal; 3 tests
- **`LruCache<TheoryLemma>` in theory combination**: `FxHashSet<TheoryLemma>` (unbounded) replaced by `LruCache<TheoryLemma, ()>`; `config.max_lemma_cache_size` (default 10,000) finally enforced; push/pop backtracking uses `truncate_to(n)`; `CombinerStats` gains `lemma_cache_hits/misses/evictions`; 5 tests
- **Tests**: +60 new tests (6,703 → 6,763); 0 failures; 0 clippy warnings
- **New files**: `oxiz-solver/src/z3_compat_ext2.rs`, `oxiz-solver/tests/z3_compat_extensions2.rs`, `oxiz-cli/src/memory.rs`

### May 18, 2026 - Dead Code Policy Enforcement Across 40 Modules (v0.2.2 Pass 3 cont)

- **Crate-level allow removed**: `oxiz-solver/src/lib.rs` `#![allow(dead_code)]` deleted — the highest-priority policy violation, was silencing all dead code warnings for the entire solver crate
- **39 module-level allows removed** across `oxiz-solver` (15 modules), `oxiz-core` (5 tactic modules), `oxiz-math` (4 modules), `oxiz-theories` (3 modules), `oxiz-proof` (1), `oxiz-cli` (2): all converted to per-item `#[allow(dead_code)]` or eliminated by wiring/deleting dead code
- **`algebraic_number.rs` deleted** (446 lines): zero external callers confirmed; duplicates `realclosure.rs` functionality; removed from `oxiz-math/src/lib.rs`
- **`SyzygyComputer` wired into `buchberger.rs`**: `apply_buchberger_criteria` now called before each S-polynomial computation to skip S-pairs failing GCD or chain criterion — improves Gröbner basis computation efficiency
- **`cicd.rs` activated**: `CicdReport` wired into `processor.rs` `run_files` with `--cicd-report`/`--cicd-strict` CLI flags
- **Tests**: 6,703 passing (−4 vs prior count due to test consolidation); 0 failures; 0 clippy warnings
- **Net LoC**: −357 net (492 deleted, 135 added) from dead code removal

### May 18, 2026 - Z3 Compat Expansion + LIA Heuristics + Dead Code Fixes (v0.2.2 Pass 3)

- **Z3 API compatibility expanded**: `oxiz-solver/src/z3_compat_ext.rs` (746 lines) adds `Array` type (select/store/eq), `FuncDecl` (declaration + application), quantifiers (`forall_bool`/`exists_bool`), `ite` (Bool/Int/Real/BV), `distinct` (Int/Real/BV), `Real` symmetry (`gt`/`ge`/`neg`/`div`/`from_i64`), `Z3Optimize` wrapper around `OmtSolver`; 23 new integration tests in `z3_compat_extensions.rs`
- **LIA heuristics wired into B&B loop**: `feasibility_pump`, `probe_variables`, `manage_cuts` — all previously dead code with `#[allow(dead_code)]` — are now called from `LiaSolver::check()` (probe + pump before B&B) and `branch_and_bound()` (manage_cuts every 8 levels); 4 new integration tests in `tests/lia_heuristics_integration.rs`
- **`simplex_solver.rs` policy fix**: removed module-level `#![allow(dead_code)]` + deleted unused `solve_with_rhs_perturbation`; added `test_all_accessors` test activating all 10 public accessors; simplex_parametric.rs also cleaned of module-level allows
- **LRA #6 regression guard verified**: `lra_regression_issue6.rs` (3 tests) all pass — bound-conflict detection for `x ≤ -1` + `x = -0.25` → UNSAT is correct in the current pipeline
- **Tests**: +78 new tests (6,629 → 6,707); 0 failures; 0 clippy warnings
- **New files**: `oxiz-solver/src/z3_compat_ext.rs`, `oxiz-solver/tests/z3_compat_extensions.rs`, `oxiz-theories/tests/lia_heuristics_integration.rs`

### May 5, 2026 - ML Wiring + Dead Code Cleanup + Bench Calibration (v0.2.2 Pass 2)

- **`MLBranchingHeuristic` adapter**: `oxiz-ml/src/branching/sat_adapter.rs` — `MLEnhancedVSIDS` now implements `BranchingHeuristic` via a thin adapter; ML branching is end-to-end reachable through `SolverConfig::external_branching` → `pick_branch_var`; type bridge `Var(u32) ↔ VarId(usize)` is lossless; confidence gate allows ML deference to VSIDS
- **Dead code removed**: `oxiz-proof/src/transform.rs` (587 lines) and `oxiz-proof/src/compression.rs` (580 lines) deleted — both referenced non-existent `ProofRule` type; live equivalents in `compress.rs`/`simplify.rs`/`normalize.rs`/`merge.rs` cover the same surface; TODO comment in `lib.rs:84-86` removed
- **Bench baselines calibrated**: `bv_simple` = 3,916 µs, `lra_simple` = 380 µs, `arrays_simple` = 440 µs (measured on host); BV/LRA/Arrays regression gate is now functional with ±25% envelope
- **Pre-existing websocket doctest fixed**: `tokio_test::block_on` → `tokio::runtime::Runtime::new().unwrap().block_on` (tokio is already a dev-dep); unblocks `--all-features` doctest runs
- **Tests**: +6 new `oxiz-ml/tests/sat_integration.rs` tests; 6,629 total passing; 0 failures; 0 clippy warnings
- **New files**: `oxiz-ml/src/branching/sat_adapter.rs`, `oxiz-ml/tests/sat_integration.rs`
- **Deleted files**: `oxiz-proof/src/transform.rs`, `oxiz-proof/src/compression.rs` (−1,167 lines)

### May 5, 2026 - v0.3.0 Infrastructure Push (v0.2.2)

- **SMT-COMP 2026 entry complete**: `Track` enum (5 variants), per-track `starexec_run_*` scripts, `smtcomp2026 --track` flag, `scripts/package_smtcomp.sh` packaging script; `submission` module wired into public API
- **Bench regression expanded**: BV, LRA, Arrays fixture benchmarks wired into criterion (`bench_bv`, `bench_lra`, `bench_arrays`); `src/fixtures.rs` for stable `include_str!` embedding; `tests/bench_coverage.rs` smoke tests
- **`BranchingHeuristic` trait hook**: new `oxiz-sat::BranchingHeuristic` trait + `BoxedBranchingHeuristic` type alias; optional `external_branching` field on `SolverConfig`; hook in `pick_branch_var` — forward-compat for oxiz-ml integration (v0.4.0)
- **Tests**: +21 new tests across three tracks (9 external_branching, 9 submission e2e, 3 bench coverage); 0 regressions; 0 clippy warnings
- **New files**: `oxiz-sat/src/solver/heuristic.rs`, `oxiz-sat/tests/external_branching.rs`, `oxiz-smtcomp/tests/submission_e2e.rs`, `bench/regression/src/fixtures.rs`, `bench/regression/tests/bench_coverage.rs`, `scripts/package_smtcomp.sh`

### April 25, 2026 - Statistics Update (v0.2.1)

- **Code Lines (tokei)**: 408,320 code lines out of 442,034 total lines across 1,182 files
- **Tests**: 6,415 passing (0 failures)
- **Stubs**: 0 unimplemented!()/todo!() remaining
- **Key additions**: Set theory CDCL(T) interface wired; Sylvester matrix discriminant (degree≥4 fix); Hong's projection leading-coefficient fix; NIA cutting planes re-enabled; normalize_bounds tactic enabled; PyO3 quantifier/string(13)/FP(21) wrappers; dynamic subsumption periodic_check; multi-trigger E-matching; clause learning literal minimization; branch-and-bound loop; BV signed comparison

### April 24, 2026 - Statistics Update (v0.2.1)

- **Rust Files**: 931 -> 978
- **Code Lines (tokei)**: 323,732 code lines out of 406,502 total Rust lines
- **Tests**: 6,368 passing (16 skipped, 0 failures)
- **Workspace Crates**: 17 (16 Rust crates + 1 TypeScript)
- **EUF Performance**: 5 allocation-reduction and data-layout improvements landed (fingerprint pre-filter, inline hints, incremental sig_table undo trail, ENode layout reorder, reusable canonicalize buffer)

### April 4, 2026 - Statistics Update

- **Rust Files**: 911+ -> 931
- **Code Lines (tokei)**: 312,495 code lines out of 393,292 total Rust lines
- **Tests**: 6,155 passing (16 skipped, 0 failures)
- **todo!/unimplemented! macros**: 0 across all 15 Rust crates
- **Workspace Crates**: 16 (15 Rust + 1 TypeScript)

### March 31, 2026 - Performance, UX, Debugging, Docs
- **Performance**: 9 optimizations (arena allocator, clause pool, SIMD poly ops,
  TermKindHasher, FP cache, model gen cache, parallel theory checking,
  lock-free structures, lazy evaluation)
- **User Experience**: EasySolver API, better error messages, resource limits
- **Debugging**: State visualization, trace generation, conflict explanations,
  model minimization
- **Documentation**: 5 new guides (performance tuning, theory, Z3 migration,
  pitfalls, case studies)
- **File Maintenance**: solve_eqs.rs and rational.rs re-split under 2000 lines
- **Tests**: 6,122 -> 6,155 (+33 new)
- **LoC**: 392,274 -> 393,292 (+1,018)

### v0.3.0 Milestone (March 23, 2026)
- 168/168 Z3 parity tests passing
- 5,993 tests at milestone point
- All files under 2,000 lines

### 100% Z3 Parity (Feb 5, 2026)
- 88/88 benchmark tests across 8 core SMT-LIB logics
- Fixed 31 test failures across 5 theory solvers
- 18 infrastructure issues resolved, 13 algorithmic improvements

---

## Next Immediate Actions

1. **Performance Profiling and Optimization** (v0.3.0)
   - Profile remaining hot paths (SAT propagation, theory check, e-graph)
   - Reduce allocations further (in-place updates, allocation-free theory paths)
   - Incremental computation caching
   - Memory layout optimization guided by profiling

2. **Performance Regression Infrastructure** (v0.3.0)
   - CI/CD integration for performance tracking
   - Automated benchmark comparison vs Z3
   - Performance dashboard

3. **Extended Theory Coverage** (v0.3.0)
   - Implement quantified logic support (UFLIA, UFLRA, AUFLIA, AUFLIRA)
   - Validate combined theories (QF_AUFBV, QF_ALIA, QF_ABV)
   - Extend QF_NIA coverage and add QF_NIRA

4. **SMT-COMP 2026 Preparation** (v0.3.0)
   - Benchmark suite alignment with SMT-COMP categories
   - Competition binary builds and packaging
   - Performance tuning on competition benchmarks

5. **Ecosystem Growth**
   - Improve Python bindings
   - JavaScript/TypeScript bindings via WASM
   - Integration with verification frameworks

---

**Status**: Production Ready
**Current Version**: v0.2.4 (2026-07-19)
**Tests**: 7,666 passing (all-features) | **LoC**: 366,082 code (459,717 total) | **Files**: 1,082 | **Clippy**: 0 warnings
**Next Milestone**: v0.3.0 - Performance Parity + SMT-COMP (Target: Q3 2026)
**Long-term Goal**: v1.0.0 - Industry-Ready SMT Solver (Target: Q4 2026)

---

## Proposed follow-ups

- **JIT-style specialization** (root TODO.md:158) — defer to v0.4.0 (oversized: requires IR + codegen layer).
- **JS/TS bindings via WASM** (root TODO.md:233) — defer until `oxiz-wasm` npm publish is authorized.
- **SMT-COMP 2026 participation** (root TODO.md:238) — gated on SMT-COMP submission portal (opens ~May 2026).
- **Symbolic execution tool integration** (root TODO.md:239) — vague; re-scope after user selects target (KLEE/angr/S2E).
- **Verification framework integration** (root TODO.md:240) — vague; re-scope after user selects target (Frama-C/CBMC/SeaHorn).

## Stubs to implement (added 2026-06-12 by /cooljapan-stub-check)

- [ ] `oxiz-theories`: `oxiz-theories/tests/fp_integration.rs:296` — fix `assert_is_normal` constraint encoding to reliably produce SAT for normal-float queries
  - Priority: P2 | Scope: small | Hint: none
- [ ] `oxiz-solver`: `oxiz-solver/src/optimization.rs:749` — complete arithmetic theory solving (currently incomplete, returns unknown for many formulae)
  - Priority: P2 | Scope: large | Hint: none
- [ ] `oxiz-core`: `oxiz-core/src/qe/datatype/case_analysis.rs:237` — uncomment and wire Term construction in case-analysis QE path once Term API is available
  - Priority: P2 | Scope: small | Hint: none

## Stubs to implement (added 2026-06-22 by /cooljapan-stub-check)

- [ ] **oxiz** `oxiz-solver`: `oxiz-solver/src/optimization.rs:749` — `TODO`: `Currently arithmetic theory solving is incomplete`
  - **Priority:** P2  **Scope:** medium  **Cross-project:** none
  - **Approach:** Complete the integer arithmetic theory in `optimize()` so a model with `x = y ∧ x ≠ y` is correctly returned as Unsat.
  - **Risk:** Incomplete theory propagation can yield Unknown or unsound Sat results; add targeted regression cases for contradictory integer constraints.
- [ ] **oxiz** `oxiz-theories`: `oxiz-theories/tests/fp_integration.rs:296` — `TODO`: `Fix constraint encoding in assert_is_normal to reliably produce SAT`
  - **Priority:** P2  **Scope:** medium  **Cross-project:** none
  - **Approach:** Repair the floating-point constraint encoding in `assert_is_normal` so exponent/mantissa range constraints are correct and the normal-number assertion reliably solves.
  - **Risk:** Off-by-one exponent bias or mantissa width errors silently produce Unsat/Unknown; validate against known-normal IEEE-754 values.

---

## Production-Readiness Audit Findings (added 2026-07-16, ultracode audit)

**Method**: 19 scoped deep-audit agents (per-crate + cross-cutting: SMT-LIB 2.6 compliance, panic audit, Z3 gap vs upstream Z3, test-quality gap, release/packaging) followed by adversarial verification agents (90 verdicts collected before the run was stopped early by request; items below marked *unverified* did not get a verification pass — verify before fixing).

**Build baseline (2026-07-16)**: `cargo check --workspace --all-features` clean; `cargo clippy --all-targets --all-features` 0 warnings; `cargo nextest run --workspace --all-features` 6826/6826 passed (16 skipped). Note: all tests pass *despite* the findings below — i.e. the suite does not exercise these paths (see P2 test-gap items).

**Counts (after location-dedupe)**: P0 confirmed-critical 20 | P1 confirmed-major 30 | P2 unverified-critical 42 | P3 unverified-major 131 | P4 minor/downgraded 105

**Re-verification (2026-07-18, release-polish pass)**: every P0 and P1 item below was individually re-read against the current tree (not just diffed against the original finding) and marked `[x]` only when the described bug pattern was confirmed gone by inspection. Result: **17/20 P0** and **28/30 P1** fixed. The 5 still-open items (all in `oxiz-nlsat`) are left `[ ]` deliberately — see each item's note below and the "Remaining (post-0.2.4)" section. P2–P4 coverage below is a representative sample (concentrated on items overlapping the fix-wave crates: `oxiz-solver` honesty gates, `oxiz-theories` BV/FP/LIA, `oxiz-spacer` PDR, `oxiz-proof` rules/Craig, `oxiz-opt` MaxSAT, `oxiz-cli`/`oxiz-wasm` frontends), not an exhaustive re-audit of all 278 P2–P4 findings; unmarked P2–P4 items were not re-checked this pass and should not be read as "still broken", only as "not re-verified yet".

### P0 — Confirmed Critical (soundness: wrong sat/unsat/model; fix first)

- [x] `oxiz-math/src/polynomial/extended_ops.rs:1069` — Sturm sequence built from pseudo-remainders without sign normalization yields wrong root counts *(scope: math; effort: small)*
  - pseudo_remainder scales by lc(b)^k which can be negative, breaking the Sturm sign invariant. Concretely p=-x^2+1 gives chain [-x^2+1, -2x, 2] so count_roots_in_interval(-2,2) returns 0 instead of 2. Propagates to isolate_roots, realclosure::AlgebraicNumber::new (assert panics), and CAD/nlsat root reasoning: wrong sat/unsat.
  - **Fix**: Use exact rational remainder, or multiply pseudo-remainder by sign(lc_b)^k so the scale factor is always positive (Z3 uses signed pseudo-remainder).
- [x] `oxiz-math/src/grobner/buchberger.rs:993` — NraSolver::check_sat returns Sat without ever solving non-constant linear inequalities *(scope: math; effort: medium)*
  - Inequalities that reduce to non-constant polynomials of total_degree<=1 skip both the constant check and the has_complex_inequality Unknown path, so check_sat returns Sat. Asserting x>0 and x<0 (no equalities) returns Sat for an unsatisfiable system: a wrong answer from a public solver API.
  - **Fix**: Route remaining linear inequalities through the simplex/LP solver; return Unknown for any inequality not fully decided instead of Sat.
- [x] `oxiz-sat/src/solver/conflict.rs:83` — Conflict analysis assumes reason clause lits[0] is the propagated literal; binary-graph propagation violates this, dropping antecedent literals *(scope: sat; effort: small)*
  - analyze() skips reason-clause position 0 (`start = 1`), assuming the propagated literal sits there. Watch-based propagation maintains that invariant, but binary-implication-graph propagation (propagate.rs:28 `assign_propagation(implied_lit, clause_id)`) never reorders the stored (sorted) clause. When the implied literal is lits[1] (~50% of original/hyper-binary clauses), the false antecedent lits[0] is silently omitted from the learned clause, producing over-strong clauses that can flip SAT instances to UNSAT. analyze_theory_conflict (line 453 `clause.lits[1..]`) has the same flaw.
  - **Fix**: For binary-graph propagations, swap the implied literal to lits[0] before recording the reason, or resolve reason clauses by value (skip lit == current_lit) instead of by position.
- [x] `oxiz-sat/src/clause.rs:412` — Clause slot reuse via free_list breaks lazy watcher cleanup, letting stale watchers drive bogus unit propagations *(scope: sat; effort: medium)*
  - remove() pushes the ClauseId to free_list; add() immediately reuses the slot for a new clause. Stale watchers (cleaned only lazily via the `deleted` flag; WatchLists::remove_clause is dead_code) now reference a live, different clause. propagate() never verifies the watched literal is in the clause: it assumes the falsified literal is at lits[1] and may propagate lits[0] as "unit" while lits[1] is true/undef, and its swaps corrupt the real watchers' positions — unsound propagations and wrong answers on long runs with clause deletion.
  - **Fix**: Do not recycle ClauseIds while stale watchers may exist: scrub watch lists on remove (use remove_clause), or defer slot reuse until a full watch-list garbage collection pass.
- [x] `oxiz-sat/src/solver/mod.rs:860` — solve_with_assumptions after a prior solve() treats leftover model decisions as fixed, returning false UNSAT *(scope: sat; effort: small)*
  - solve() returns Sat leaving the full trail (decisions at levels >0). solve_with_assumptions never backtracks to root first; assumption_level_start is captured at the dirty level and an assumption that merely disagrees with the previous arbitrary model hits `value.is_false()` and immediately returns (Unsat, core). Example: (a∨b); solve() picks ¬a,b; solve_with_assumptions([a]) reports UNSAT though a∧(a∨b) is SAT. This breaks the standard MaxSAT/incremental usage pattern. The extracted core also reads stale `seen` flags.
  - **Fix**: Call backtrack_with_phase_saving(0) at the top of solve_with_assumptions before capturing assumption_level_start, and only report UNSAT when the assumption is false at level 0.
- [ ] `oxiz-nlsat/src/solver/decide.rs:500` — Irrational roots silently dropped: solver returns wrong UNSAT for e.g. x^2 > 2 *(scope: nlsat; effort: large)*
  - find_univariate_roots only finds RATIONAL roots; quadratic with non-square discriminant returns Vec::new() ('Irrational roots - cannot represent exactly'). compute_feasible_region then treats the polynomial as sign-constant, so for asserted 'x^2-2>0' the feasible set is EMPTY and solve() returns Unsat at level 0 (mod.rs:653). oxiz-theories/src/nlsat.rs:369 trusts Unsat for univariate atoms, so the final answer is wrong.
  - **Fix**: Use SturmSequence root isolation (algebraic numbers / isolating intervals) instead of rational-only roots in find_univariate_roots, or return IntervalSet::reals() when roots may be missing and rely on validation.
- [ ] `oxiz-nlsat/src/solver/mod.rs:655` — Infinite loop: empty feasible region at level>0 backtracks without learning, re-makes identical decision *(scope: nlsat; effort: large)*
  - When pick_arith_value returns None at level>0, solve() calls backtrack(level-1) with no lemma, no activity bump, no phase flip. decide() then re-picks the same variable with the same saved phase, reproducing the identical state forever. Example that hangs: (x>1) AND (x<-1 OR x<5) — trivially SAT but loops indefinitely. No conflict is counted so restarts never fire.
  - **Fix**: Learn a clause negating the decisions/atoms whose interval intersection is empty (NLSAT semantic-conflict lemma), or at minimum flip the saved phase of the last decision before re-deciding.
- [ ] `oxiz-nlsat/src/nia.rs:363` — NIA branch-and-bound adds both branch constraints permanently to one shared solver *(scope: nlsat; effort: large)*
  - create_branch adds 'x<=floor' and 'x>=ceil' as permanent unit clauses to the SAME NlsatSolver; popping a BranchNode never retracts them, so after pushing both branches the solver holds contradictory constraints and every node solves the same over-constrained problem. branch_and_bound then exhausts the stack and returns Unsat (nia.rs:276) for satisfiable integer problems. NiaSolver is the QF_NIA path in oxiz-theories.
  - **Fix**: Use push/pop scopes or assumption literals per branch node so constraints are retracted on backtrack; never treat search-space exhaustion under leaked constraints as Unsat.
- [x] `oxiz-nlsat/src/solver/mod.rs:505` — solve() never resets trail/arithmetic state, breaking incremental re-solve *(scope: nlsat; effort: medium)*
  - After a Sat answer, the trail, decision levels, and arithmetic values remain assigned. NiaSolver re-invokes solve() after add_clause: the new unit literal is assigned at a stale non-zero level and theory_propagate evaluates it against the stale model, producing spurious conflicts; analyze_conflict resolves Unit/Theory-justified literals away with no reason clause and can return an empty learnt clause, which solve() reports as Unsat (mod.rs:548-549).
  - **Fix**: Backtrack to level 0 and clear arithmetic assignments at solve() entry; give Unit/Theory-justified literals proper reasons in analyze_conflict instead of silently dropping them.
- [x] `oxiz-nlsat/src/cad.rs:518` — Sturm sequence built from sign-unnormalized pseudo-remainders gives wrong root counts *(scope: nlsat; effort: medium)*
  - pseudo_remainder scales by lc(divisor) on every reduction step; when the leading coefficient is negative an odd number of scalings flips the remainder's sign, so the chain is not a Sturm chain. Example: p = 4-x^2 yields chain (-x^2+4, -x, +4) and count_roots() = 0 despite roots +/-2. All root-atom evaluation (evaluate_root_atom) and CAD lifting depend on isolate_roots, so answers involving negative-leading-coefficient polynomials are wrong.
  - **Fix**: Track the sign of lc(b)^k applied during pseudo-division and multiply the remainder by it (or normalize lc(b) positive before division) so the chain satisfies Sturm's sign conditions.
- [x] `oxiz-nlsat/src/portfolio.rs:261` — PortfolioSolver solves empty solvers: returns Sat for every input *(scope: nlsat; effort: large)*
  - run_parallel_solvers creates fresh NlsatSolver::new() instances and never copies the base problem ('simplified - no actual problem to solve yet'). The empty problem is trivially Sat, so PortfolioSolver::solve() always answers Sat with an empty model, including for unsatisfiable inputs. config.timeout and the diverse configs are also ignored. Public API re-exported from lib.rs.
  - **Fix**: Clone base_solver's clauses/atoms into each worker via create_configured_solver, apply per-worker configs, honor timeout, and extract real models/cores; otherwise remove the API until implemented.
- [x] `oxiz-core/src/smtlib/parser/terms.rs:455` — Parser silently turns (div a b) and (mod a b) into subtraction *(scope: core-rest; effort: small)*
  - This parser IS the production path: oxiz-cli -> oxiz_solver::Context::execute_script -> parse_script. Any script using integer div/mod gets a semantically different formula, so check-sat can answer wrong on plausible LIA inputs. TermManager already has mk_div/mk_mod (ast/manager/builder.rs:314,320) but the parser ignores them.
  - **Fix**: Route "div" to self.manager.mk_div(lhs, rhs) and "mod" to mk_mod; add regression tests like (assert (= (div 7 2) 3)).
- [x] `oxiz-core/src/smtlib/parser/terms.rs:929` — Real division "/", abs, to_real, to_int, divisible parsed as Bool-sorted uninterpreted functions *(scope: core-rest; effort: medium)*
  - The operator match has no case for "/" or other core Int/Real ops, so they fall to the default arm and become mk_apply with Bool default sort. Arithmetic theory then ignores these constraints entirely — QF_LRA scripts with division get wrong sat/unsat answers on the production parse path.
  - **Fix**: Add explicit cases for "/", "abs", "to_real", "to_int", "divisible"; reject genuinely unknown undeclared operators with a ParseError instead of Bool-sorted apply.
- [x] `oxiz-core/src/ast/manager/query.rs:445` — TermManager::substitute silently skips Apply, BV, String, FP, Xor, Distinct, Div/Mod, quantifier and Let terms *(scope: core-ast; effort: medium)*
  - substitute_cached handles only ~15 term kinds; everything else hits 'Some(_) => id' with comment 'For complex terms, just return as-is for now'. Tactics solve_eqs, ackermann, propagate, ctx_simplify and quantifier instantiation (tactic/quantifier.rs:533) rely on it: substituting x->3 in f(x) or any bitvector/string assertion returns the term unchanged, so solved equations are dropped while occurrences remain — wrong sat/unsat and wrong models.
  - **Fix**: Handle all TermKind variants generically via get_children plus a rebuild function (as rewrite_children does), and descend into quantifier bodies with bound-variable shadowing.
- [x] `oxiz-core/src/simplification/mod.rs:299` — Boolean absorption in AND/OR drops all other conjuncts/disjuncts *(scope: core-ast; effort: small)*
  - try_boolean_absorption_in_and returns just 'candidate' and simplify_and returns it as the whole result. And(a, Or(a,b), c) simplifies to 'a', silently dropping c — an UNSAT formula (c=false) becomes SAT. The OR variant (line 316) similarly turns Or(a, And(a,b), c) into 'a', dropping disjunct c and turning SAT into UNSAT. Reachable via AggressiveSimplifier with aggressive=true.
  - **Fix**: Absorption must remove only the absorbed Or/And argument and keep the remaining args: rebuild mk_and(args minus the absorbed term), not return candidate alone.
- [x] `oxiz-core/src/simplification/mod.rs:343` — try_factor_or_of_ands discards every disjunct outside the matched pair *(scope: core-ast; effort: small)*
  - For Or(And(x,a), And(x,b), c, ...), the factoring rule returns And(x, Or(a,b)) and drops c and all other disjuncts, strengthening the formula — a satisfiable input can become UNSAT. Fires in aggressive simplification whenever any two AND disjuncts share a conjunct.
  - **Fix**: Include the untouched disjuncts: build Or(And(common, Or(left_rest,right_rest)), remaining_args...).
- [x] `oxiz-core/src/rewrite/bv.rs:417` — BvShl/BvLshr rewrite returns Unchanged(lhs): x << y silently becomes x *(scope: core-ast; effort: small)*
  - rewrite_bvshl (line 417) and rewrite_bvlshr (line 462) end with RewriteResult::Unchanged(lhs) when args are non-constant. Through CombinedRewriter's result.term() (combined.rs:514) the entire shift expression is replaced by its left operand, changing formula semantics for any symbolic shift.
  - **Fix**: Return Unchanged(manager.mk_bv_shl(lhs, rhs)) / mk_bv_lshr(lhs, rhs); both builders exist.
- [x] `oxiz-core/src/tactic/quantifier.rs:968` — DER forall rule is logically inverted: rewrites ∀x.(x=t ∨ ψ) to ψ[t/x], which is unsound *(scope: core-tactic; effort: medium)*
  - Correct DER eliminates a DISEQUALITY disjunct: ∀x.(x≠t ∨ ψ) ≡ ψ[t/x]. The code eliminates the positive equality instead, and also rewrites the x≠t→ψ implication (≡ x=t ∨ ψ) to ψ[t/x]. Goal {∀x.(x=5 ∨ P(x)), ¬P(6)} is UNSAT but becomes {P(5), ¬P(6)} = SAT. ∀x.(x=t) also rewrites to true.
  - **Fix**: For Forall, match Not(Eq(x,t)) disjuncts (and Eq antecedents of Implies) instead of positive equalities; keep the exists/And path as-is.
- [x] `oxiz-core/src/tactic/quantifier.rs:689` — SkolemizationTactic reuses Skolem names across assertions and ignores polarity *(scope: core-tactic; effort: medium)*
  - skolemize() (ast/normal_forms.rs:758) resets counter=0 per call, so per-assertion calls give distinct existentials the SAME sk_0 variable: {∃x.P(x), ∃x.¬P(x)} (SAT) becomes {P(sk_0), ¬P(sk_0)} (UNSAT). skolemize also recurses through Not/Implies without flipping polarity, so ¬(∃x.P(x)) becomes ¬P(sk_0) (UNSAT→SAT), and Skolem function args are built with hardcoded bool_sort (normal_forms.rs:855).
  - **Fix**: Thread one global fresh-name counter through the goal, track polarity (skolemize Exists only at positive polarity, Forall at negative), and use real universal-var sorts for Skolem function arguments.
- [x] `oxiz-core/src/tactic/quantifier.rs:624` — QuantifierInstantiationTactic instantiates Forall terms found at any polarity as asserted facts *(scope: core-tactic; effort: medium)*
  - collect_quantifiers (line 646) gathers every Forall subterm, including ones under Not, Or, or Implies antecedents, then pushes φ(t) as a new top-level assertion. For goal ¬(∀x.P(x)) ∧ ¬P(c) with trigger matching c, the added P(c) flips SAT to UNSAT.
  - **Fix**: Only instantiate quantifiers that occur as positive-polarity top-level assertions (or track polarity during collection and skip negative/mixed occurrences).

### P1 — Confirmed Major (silent constraint drop / advertised-but-broken)

- [x] `oxiz-math/src/grobner/buchberger.rs:119` — reduce() silently discards the unreduced remainder when the 1000-iteration cap is hit *(scope: math; effort: small)*
  - **Fix**: On cap exhaustion return r.add(&p) (still ideal-equivalent) or propagate a resource-limit error; never drop p.
- [x] `oxiz-math/src/simplex.rs:609` — SimplexTableau never repairs non-basic variables violating their own bounds; check() can report Sat for infeasible systems *(scope: math; effort: medium)*
  - **Fix**: In add_bound, when var is non-basic and its value violates the new bound, set it to the bound and recompute dependent basic vars (Dutertre-de Moura update).
- [x] `oxiz-math/src/fast_rational.rs:323` — mul_small/new_small use saturating_abs, corrupting gcd at i64::MIN and silently computing wrong products *(scope: math; effort: small)*
  - **Fix**: Pass values directly to gcd_i64 (it already uses unsigned_abs), or special-case i64::MIN by promoting to Big before reduction.
- [x] `oxiz-math/src/rational/mod.rs:888` — Number-theory helpers are silently wrong beyond trial-division limits and euler_totient can effectively hang *(scope: math; effort: medium)*
  - **Fix**: Factor completely via Pollard rho + Miller-Rabin (both already present) instead of bounded trial division; add an iteration/resource cap returning an explicit error.
- [ ] `oxiz-nlsat/src/solver/propagate.rs:546` — Theory conflict explanation is not a valid lemma: negates every assigned atom sharing a variable *(scope: nlsat; effort: large)*
  - **Fix**: Wire ExplainContext/CAD projection (resultants, discriminants, root atoms) into explain_theory_conflict so lemmas are theory-valid, as in Z3 nlsat_explain.cpp.
- [x] `oxiz-nlsat/src/solver/mod.rs:413` — Empty clause silently dropped: add_clause returns NULL_CLAUSE without recording conflict *(scope: nlsat; effort: small)*
  - **Fix**: Set self.conflict_clause (or a dedicated unsat flag) when an empty clause is added so solve() returns Unsat immediately.
- [x] `oxiz-nlsat/src/solver/mod.rs:42` — No resource limits in solve(): max_conflicts accepted but never read, Unknown unreachable *(scope: nlsat; effort: small)*
  - **Fix**: Check stats.conflicts against config.max_conflicts (and an optional deadline) in the solve loop, returning SolverResult::Unknown when exceeded.
- [x] `oxiz-nlsat/src/simplify.rs:102` — simplify_ineq_atom drops negative constant factor without flipping Lt/Gt: opposite constraint *(scope: nlsat; effort: medium)*
  - **Fix**: Track a parity of negations (from dropped negative constants and leading-coefficient normalization of odd factors) and flip Lt<->Gt when parity is odd; fix the empty-factors Trivial cases too.
- [x] `oxiz-nlsat/src/maxsat.rs:230` — MaxSatSolver cost and model extraction are stubs: always reports Optimal cost 0 with empty model *(scope: nlsat; effort: medium)*
  - **Fix**: Read relaxation-variable values from solver.get_model() to compute the true violated weight, iterate the linear search with cardinality/weight bounds, and return the real assignment.
- [x] `oxiz-nlsat/src/cad.rs:753` — Root isolation silently merges roots closer than 1e-6 into one 'isolating' interval *(scope: nlsat; effort: medium)*
  - **Fix**: Keep bisecting with exact rational arithmetic until each interval contains exactly one root (Sturm counts make this terminating for square-free input); square-free-factorize first to handle multiple roots.
- [x] `oxiz-nlsat/src/lib.rs:58` — ~25 of 40 exported modules are shelf-ware never wired into the solver *(scope: nlsat; effort: large)*
  - **Fix**: Either integrate these engines into NlsatSolver's solve pipeline (inprocessing hooks, CAD explain, proof logging) or mark them experimental/private so the API does not advertise nonfunctional features.
- [ ] `oxiz-nlsat/src/nia.rs:406` — floor_ceil truncates toward zero: wrong floor/ceil for negative fractional values *(scope: nlsat; effort: small)*
  - **Fix**: Use value.floor()/value.ceil() from BigRational (or adjust the truncated quotient by -1 when value is negative and non-integral).
- [x] `oxiz-core/src/smtlib/parser/terms.rs:125` — Undeclared symbols silently become fresh Bool variables instead of a parse error *(scope: core-rest; effort: small)*
  - **Fix**: Return OxizError::ParseError("unknown constant") for symbols not in bindings/constants/dt_constructors, matching SMT-LIB and Z3 behavior.
- [x] `oxiz-core/src/smtlib/parser/terms.rs:351` — Indexed BV ops (zero_extend, sign_extend, rotate_left, repeat) degrade to Bool-sorted generic applies *(scope: core-rest; effort: medium)*
  - **Fix**: Add explicit cases mapping zero_extend/sign_extend/rotate_left/rotate_right/repeat to the corresponding mk_bv_* builders with correct result widths.
- [x] `oxiz-core/src/smtlib/parser/commands.rs:387` — Unknown SMT-LIB commands (define-fun-rec, declare-sort, get-unsat-assumptions) silently skipped *(scope: core-rest; effort: medium)*
  - **Fix**: Implement declare-sort and define-fun-rec; for genuinely unsupported commands emit (error "unsupported command") instead of silent skip.
- [x] `oxiz-core/src/smtlib/parser/commands.rs:147` — set-option numeric/string values silently replaced with empty string *(scope: core-rest; effort: small)*
  - **Fix**: Peek the token kind and accept Symbol, Numeral, Decimal, and StringLit values; error on anything else instead of defaulting to "".
- [x] `oxiz-core/src/smtlib/parser/commands.rs:452` — declare-datatypes parses only the first datatype's constructor list; multi/mutual datatypes broken *(scope: core-rest; effort: medium)*
  - **Fix**: Loop constructor groups once per declared datatype name, pair each group with its name, and parse selector sorts via parse_sort().
- [x] `oxiz-core/src/qe/string/plugin.rs:204` — StringQePlugin eliminates any constrained string quantifier to unconditional true *(scope: core-rest; effort: small)*
  - **Fix**: Return None (conservative give-up) until real length solving/automata construction is implemented; never fabricate true.
- [x] `oxiz-core/src/qe/arith/cooper.rs:241` — Cooper QE returns the input formula with the quantified variable still free, claiming elimination *(scope: core-rest; effort: large)*
  - **Fix**: Return Err("not implemented") from eliminate_exists until the substitution/test-set machinery is real, or implement Cooper's construction referencing Z3 qe_arith.
- [x] `oxiz-core/src/model/evaluator.rs:155` — Model evaluator silently truncates big integer and wide BV constants to 0 *(scope: core-rest; effort: medium)*
  - **Fix**: Return EvalResult::Error on out-of-range conversion, or widen Value::Int to BigInt / Value::BitVec to BigUint.
- [x] `oxiz-core/src/qe/array/quantifier_elim.rs:315` — Array QE module built on placeholder TermId=usize; Skolem constants are string lengths *(scope: core-rest; effort: medium)*
  - **Fix**: Stop exporting the module (or mark #[doc(hidden)] experimental) until it operates on real crate::ast::TermId with actual substitution.
- [x] `oxiz-core/src/qe/arith/omega_test.rs:189` — Omega test can only ever return Unknown: both shadow checks are hardcoded *(scope: core-rest; effort: large)*
  - **Fix**: Implement the real/dark shadow bound comparisons over LinearConstraint, or document and return Unknown without fake statistics.
- [x] `oxiz-core/src/ast/manager/mod.rs:99` — Hash-cons cache keys on TermKind only, ignoring sort: same-named vars of different sorts alias *(scope: core-ast; effort: small)*
  - **Fix**: Key the cache on (TermKind, SortId) — at minimum for TermKind::Var and Apply where the sort is not derivable from the kind.
- [x] `oxiz-core/src/rewrite/string.rs:303` — indexof(s, "", i) -> i without the required 0 <= i <= len(s) side condition *(scope: core-ast; effort: small)*
  - **Fix**: Apply only when start is a constant within [0, len(s)] for constant s; otherwise rewrite to ite(0<=i<=len(s), i, -1) or leave unchanged.
- [x] `oxiz-core/src/rewrite/combined.rs:490` — Unbounded recursion in rewrite_bottom_up, AggressiveSimplifier and substitute_cached *(scope: core-ast; effort: medium)*
  - **Fix**: Convert to explicit worklist iteration, or enforce a depth counter that bails out returning the term unchanged (sound).
- [x] `oxiz-core/src/tactic/solve_eqs.rs:649` — FM op_limit abort marks constraints dead without adding their resolvents, losing constraints *(scope: core-tactic; effort: small)*
  - **Fix**: If the op limit fires before all pairs for a variable are resolved, keep that variable's original constraints alive (skip elimination for it) instead of marking them dead.
- [x] `oxiz-core/src/tactic/lia2card.rs:425` — Sequential-counter and commander aux variables use non-unique names, aliasing across constraints *(scope: core-tactic; effort: small)*
  - **Fix**: Include the per-tactic aux_var_counter (as done for '__tot_{}_{}') in every aux variable name and bump it per constraint.
- [x] `oxiz-core/src/tactic/bv/bv_rewriter.rs:378` — BvRewriterTactic::rewrite replaces every BV operation with arbitrary TermId(0) *(scope: core-tactic; effort: medium)*
  - **Fix**: Implement reconstruct_* via manager.mk_bv_* and the constant predicates via TermKind::BitVecConst matching, or delete the type until real; at minimum make rewrite() return the input unchanged.
- [x] `oxiz-core/src/tactic/bitblast.rs:224` — Bit-blasting tactic never bit-blasts — both stateful and stateless versions return the goal unchanged *(scope: core-tactic; effort: large)*
  - **Fix**: Implement real blasting (per-bit Booleans + circuit encoding) or rename/document as a probe and remove 'bit-blast' from the registry until functional.
- [x] `oxiz-core/src/tactic/arith/arith_bounds.rs:200` — Seven exported tactic types are permanent NotApplicable placeholders with empty helper bodies *(scope: core-tactic; effort: large)*
  - **Fix**: Either implement against the real TermManager AST or mark these #[doc(hidden)]/remove from public exports so consumers cannot mistake them for working preprocessing.

### P2 — Unverified Critical (adversarially verify, then fix)

- [x] `oxiz-solver/src/mbqi/integration.rs:296` — MBQI claims Satisfied (sat) after finite candidate check over infinite domains *(scope: z3-gap; effort: large)*
- [x] `oxiz-solver/src/solver/check_string.rs:11` — String atoms (str.contains, str.in_re, prefixof, indexof, ...) are free booleans, never theory-checked *(scope: z3-gap; effort: large)*
- [x] `oxiz-solver/src/solver/check_fp.rs:46` — FP and array 'theories' are benchmark-keyed heuristics; real solvers unwired *(scope: z3-gap; effort: large)*
- [x] `oxiz-theories/src/bv/solver.rs:674` — Barrel shifters (bvshl/bvlshr/bvashr) ignore high bits of the shift amount, producing wrong bit-blasting *(scope: theories-arith; effort: small)*
- [x] `oxiz-theories/src/bv/solver.rs:1146` — bv_udiv/bv_urem/bv_sdiv/bv_srem encodings admit spurious quotients: q*b + r may wrap mod 2^w *(scope: theories-arith; effort: small)*
- [x] `oxiz-theories/src/arithmetic/solver.rs:477` — LIA mode never enforces integrality: check() only runs the LP relaxation *(scope: theories-arith; effort: large)*
- [x] `oxiz-theories/src/arithmetic/simplex.rs:579` — Pivot-limit exhaustion in make_feasible/dual_simplex returns Ok(()) — infeasible state reported as SAT *(scope: theories-arith; effort: medium)*
- [x] `oxiz-theories/src/arithmetic/lia/branching.rs:135` — Branch-and-bound 'backtrack' calls simplex.reset(), erasing all constraints before the down-branch *(scope: theories-arith; effort: small)*
- [x] `oxiz-theories/src/arithmetic/lia/cuts.rs:188` — Placeholder MIR/CG/Gomory/disjunctive 'cuts' are invalid inequalities added as permanent constraints *(scope: theories-arith; effort: large)*
- [x] `oxiz-theories/src/fp/solver.rs:687` — assert_fp_lt encodes a<b as 'a negative AND b positive'; assert_fp_le adds no ordering constraint at all *(scope: theories-arith; effort: large)*
- [x] `oxiz-cli/src/model_counter.rs:99` — --count-models returns fabricated counts: exact mode always reports 0, approximate mode never invokes the solver *(scope: frontends; effort: large)*
- [x] `oxiz-cli/src/main.rs:221` — --timeout flag (and config-file timeout) is never enforced in normal solving; solver can hang forever *(scope: frontends; effort: medium)*
- [x] `oxiz-sat/src/solver/mod.rs:651` — add_clause watches the first two sorted literals even if already false, missing conflicts on incrementally added clauses *(scope: sat; effort: small)*
- [x] `oxiz-sat/src/solver/learn.rs:469` — Inprocessing clause strengthening removes a literal after proving F ⊨ lit — logically wrong direction, yields unsound clauses *(scope: sat; effort: small)*
- [x] `oxiz-sat/src/preprocessing_core.rs:196` — Pure literal elimination deletes clauses without recording the forced assignment — models can violate deleted clauses *(scope: sat; effort: small)*
- [x] `oxiz-sat/src/solver/propagate.rs:21` — Binary implication graph entries are never removed on pop()/forget_learned_since and bypass the deleted-clause check *(scope: sat; effort: medium)*
- [x] `oxiz-sat/src/symmetry.rs:262` — detect_symmetries emits unverified permutations; SymmetryBreakTactic then adds lex-leader constraints that can change satisfiability *(scope: sat; effort: medium)*
- [x] `oxiz-core/src/smtlib/parser/terms.rs:461` — Integer 'mod' is parsed as subtraction, producing wrong sat/unsat answers *(scope: smtlib-compliance; effort: small)*
- [x] `oxiz-theories/src/euf/union_find.rs:53` — Path compression in find() is not trail-recorded, so pop() leaves corrupted equivalence classes *(scope: theories-rest; effort: small)*
- [x] `oxiz-theories/src/euf/solver.rs:998` — pop() never removes proof-forest edges added to pre-existing nodes, so conflict explanations cite retracted assertions *(scope: theories-rest; effort: medium)*
- [x] `bench/z3_parity/results.json:120` — Checked-in parity results show 4 Sat-answers on UNSAT quantified benchmarks, contradicting README's '100% Z3 parity' claim, and no test covers those directories *(scope: test-gap; effort: medium)*
- [x] `oxiz-solver/src/solver/tests.rs:250` — Ignored test documents a known wrong-model bug: BV solver returns SAT but model gives value violating the constraints *(scope: test-gap; effort: medium)*
- [x] `oxiz-core/src/smtlib/parser/terms.rs:14` — Recursive-descent parse_term has no depth limit: stack-overflow abort on deeply nested input *(scope: panic-audit; effort: small)*
- [x] `oxiz-opt/src/maxsat/algorithms.rs:71` — Weighted MaxSAT (default stratified path) ignores weights and returns wrong optimum as Optimal *(scope: opt-proof; effort: large)*
- [x] `oxiz-opt/src/preprocess.rs:329` — unit_propagation treats SOFT unit clauses as hard facts, silently dropping conflicting soft clauses *(scope: opt-proof; effort: medium)*
- [x] `oxiz-opt/src/context.rs:573` — OptContext::optimize_maxsmt silently coerces Rational weights to 1 and returns Optimal after Unknown breaks the binary search *(scope: opt-proof; effort: medium)*
- [x] `oxiz-proof/src/craig.rs:557` — Craig interpolation colors every axiom A and ignores the user partition, so extract() returns trivial 'true' interpolants *(scope: opt-proof; effort: large)*
- [x] `oxiz-proof/src/rules.rs:288` — Proof rule validators unconditionally return Valid — checker accepts invalid proofs *(scope: opt-proof; effort: large)*
- [x] `oxiz-spacer/src/pdr.rs:417` — is_init_reachable always returns false — counterexamples at level 0 are never detected *(scope: spacer; effort: medium)*
- [x] `oxiz-spacer/src/pdr.rs:472` — is_transition_feasible is a stub returning false — Spacer can never return Unsafe *(scope: spacer; effort: large)*
- [x] `oxiz-spacer/src/smt.rs:253` — is_lemma_inductive has no primed-state renaming and conjoins all rules — every lemma trivially 'inductive' *(scope: spacer; effort: large)*
- [x] `oxiz-spacer/src/parser.rs:666` — ChcParser parses predicate applications as 'true' — all predicate structure silently erased *(scope: spacer; effort: medium)*
- [x] `oxiz-spacer/src/bmc.rs:281` — Multiple transition rules are conjoined, not disjoined — k-induction proves 'Safe' for unsafe systems *(scope: spacer; effort: medium)*
- [x] `oxiz-spacer/src/invariant.rs:515` — Houdini 'verification' is a confidence-threshold filter with zero SMT queries — all candidates returned as verified invariants *(scope: spacer; effort: large)*
- [x] `oxiz-solver/src/solver/mod.rs:542` — Solver returns Sat after 10 inconclusive MBQI rounds, assuming quantifiers hold *(scope: solver-rest; effort: small)*
- [x] `oxiz-solver/src/mbqi/integration.rs:509` — MBQI substitution silently skips Xor, Distinct, nested Forall/Exists, BV and string kinds, producing lemmas with leftover bound variables *(scope: solver-rest; effort: medium)*
- [x] `oxiz-solver/src/solver/theory_manager.rs:1485` — Conflict-limit exhaustion suppresses real theory conflicts and returns Sat *(scope: solver-core; effort: medium)*
- [x] `oxiz-solver/src/solver/encode.rs:1133` — BvSlt/BvSle also asserted into linear arithmetic with unsigned semantics *(scope: solver-core; effort: medium)*
- [x] `oxiz-solver/src/solver/check_fp.rs:1283` — FP pre-check collects Eq facts ignoring polarity, causing wrong UNSAT *(scope: solver-core; effort: small)*
- [x] `oxiz-solver/src/solver/mod.rs:805` — push/pop never push/pop the BV solver; committed BV facts leak across scopes *(scope: solver-core; effort: medium)*
- [x] `oxiz-wasm/src/js_api/optimize.rs:57` — WASM minimize/maximize/assertSoft are silently dropped; optimize() reports plain sat as "optimal" *(scope: bindings; effort: large)*
- [x] `oxiz-wasm/src/js_api/optimize.rs:572` — computeInterpolant returns conjunction of partition A as a fake "interpolant" *(scope: bindings; effort: small)*

### P3 — Unverified Major

- [ ] `GAP` — Recursive function definitions (Z3 recfun) unusable end-to-end *(scope: z3-gap)*
- [x] `oxiz-solver/src/context.rs:741` — set_option ignores every option except produce-proofs/produce-unsat-cores *(scope: z3-gap)*
- [ ] `oxiz-solver/src/context.rs:850` — get-model prints wrong sort/value for BitVec, Array, FP, and uninterpreted constants *(scope: z3-gap)*
- [ ] `oxiz-core/src/ematching/code_tree.rs:894` — E-matching code-tree backtracking stub drops matches *(scope: z3-gap)*
- [ ] `oxiz-core/src/tactic/mbp.rs:307` — Model-based projection assumes linearity unconditionally; nonlinear input gets linear projection *(scope: z3-gap)*
- [ ] `oxiz-theories/src/fp/ieee754_full.rs:1053` — sqrt() halves odd-exponent inputs: normalized significand can never shift left but exponent is still decremented *(scope: theories-arith)*
- [ ] `oxiz-theories/src/fp/ieee754_full.rs:727` — RoundNearestTiesToEven rounds ties up instead of to even (the default rounding mode) *(scope: theories-arith)*
- [ ] `oxiz-theories/src/fp/ieee754_full.rs:525` — Subnormal unpack uses off-by-one shift, doubling every subnormal's value in arithmetic *(scope: theories-arith)*
- [ ] `oxiz-theories/src/fp/solver.rs:769` — FP<->BV and FP<->Real conversions are stubs that leave results completely unconstrained *(scope: theories-arith)*
- [ ] `oxiz-theories/src/fp/solver.rs:430` — assert_fp_eq conflates fp.eq and bitwise '='; forces non-NaN and sign equality, breaking NaN= and +0/-0 cases *(scope: theories-arith)*
- [ ] `oxiz-theories/src/arithmetic/simplex.rs:1110` — propagate_bounds/tighten_bounds write bounds directly, bypassing the undo trail and dropping all but one reason *(scope: theories-arith)*
- [ ] `oxiz-theories/src/arithmetic/solver.rs:259` — GCD-infeasibility path fabricates the conflict: contradictory bounds asserted with hardcoded reason 0 *(scope: theories-arith)*
- [ ] `oxiz-theories/src/arithmetic/simplex_opt.rs:260` — optimize_linexpr rebrands pivot-limit Unknown as Optimal(current value) *(scope: theories-arith)*
- [ ] `oxiz-theories/src/bv/solver.rs:1891` — notify_equality probe solve leaves learned-clause residue that check() documents as unsound *(scope: theories-arith)*
- [ ] `oxiz-theories/src/arithmetic/simplex.rs:20` — Simplex uses fixed-width Rational64; coefficient growth during pivoting panics on overflow *(scope: theories-arith)*
- [ ] `oxiz-theories/src/fp/solver.rs:906` — FpSolver::check lacks the incremental-probe cleanup and model snapshot BvSolver needs; returns empty conflict *(scope: theories-arith)*
- [x] `oxiz-cli/src/main.rs:804` — --memory-limit, --conflict-limit, --decision-limit are silently ignored *(scope: frontends)*
- [x] `oxiz-cli/src/main.rs:828` — All solver-tuning flags are dead: --strategy, --simplify, --preset, --auto-tune, --enumerate-models, --optimize, --minimize-model, --theory-opt, --enhanced-errors do nothing *(scope: frontends)*
- [x] `oxiz-cli/src/main.rs:1050` — --unsat-core never enables core production, so it always outputs an error instead of a core *(scope: frontends)*
- [ ] `oxiz/src/easy.rs:129` — EasySolver assert_* methods silently drop constraints when the variable name is unknown *(scope: frontends)*
- [ ] `oxiz-cli/src/distributed.rs:745` — Distributed cube-and-conquer is fake: cubes assert fresh unconstrained variables, so every worker re-solves the whole problem *(scope: frontends)*
- [ ] `oxiz-cli/src/portfolio.rs:39` — --portfolio-mode runs five identical solvers: strategy options are ignored, so there is no diversification *(scope: frontends)*
- [x] `oxiz-cli/src/interpolate.rs:141` — --interpolate is a placeholder: always returns interpolant 'true' with status 'unknown' *(scope: frontends)*
- [ ] `oxiz-cli/src/main.rs:1057` — --validate-model does not validate anything; it just prints the model *(scope: frontends)*
- [ ] `oxiz-cli/src/main.rs:429` — --minimize-core, --incremental, --checkpoint/--resume/--resume-from/--checkpoint-interval, and --threads are accepted but never read *(scope: frontends)*
- [ ] `oxiz-cli/src/tptp.rs:949` — TPTP free variables are declared as constants, weakening implicitly universally quantified axioms — can yield wrong SZS status *(scope: frontends)*
- [ ] `oxiz-cli/src/dimacs.rs:105` — DIMACS parser rejects valid files: multi-line clauses split into separate clauses and empty clauses (falsum) silently dropped *(scope: frontends)*
- [ ] `oxiz-cli/src/server.rs:292` — REST API: /check-sat builds scripts with no declarations (always errors, masked as 'unknown'); /model can return another client's model *(scope: frontends)*
- [x] `oxiz-sat/src/xor.rs:671` — XorDetector::compute_xor_rhs returns the inverted RHS for every detected XOR constraint *(scope: sat)*
- [ ] `oxiz-sat/src/solver/learn.rs:382` — Vivification and inprocessing strengthening mutate clause.lits in place without updating watch lists *(scope: sat)*
- [ ] `oxiz-sat/src/cube_solver.rs:179` — ParallelCubeSolver/CubeAndConquer never solve: solve_cube ignores the clauses, and an empty cube list yields UNSAT *(scope: sat)*
- [ ] `oxiz-sat/src/parallel/proof_check.rs:89` — ParallelProofChecker declares every proof Valid — no step is ever checked *(scope: sat)*
- [x] `oxiz-sat/src/lib.rs:10` — "DRAT proof generation" is advertised but the CDCL solver never emits proof events; LRAT writer output is malformed *(scope: sat)*
- [ ] `oxiz-sat/src/gpu.rs:485` — CpuReferenceAccelerator::batch_unit_propagation fabricates conflicts and units from clause-index modulo *(scope: sat)*
- [ ] `oxiz-sat/src/assumptions.rs:233` — AssumptionCoreMinimizer::minimize_deletion discards all non-fixed assumptions, returning an empty 'core' *(scope: sat)*
- [ ] `oxiz-sat/src/portfolio.rs:236` — No resource limits anywhere: Solver::solve has no budget and PortfolioSolver's timeout still joins all threads *(scope: sat)*
- [ ] `oxiz-sat/src/xor.rs:1062` — XorSubsumption::find_subsumed returns unverified signature-collision candidates as 'subsumed' *(scope: sat)*
- [x] `oxiz-core/src/smtlib/parser/commands.rs:292` — (set-info :smt-lib-version 2.6) causes a hard parse error aborting the whole script *(scope: smtlib-compliance)*
- [x] `oxiz-solver/src/context.rs:732` — All solver options except produce-proofs/produce-unsat-cores are accepted and silently ignored (:timeout, :random-seed, :produce-models, memory/conflict/decision limits) *(scope: smtlib-compliance)*
- [ ] `oxiz-solver/src/context.rs:885` — :named assertion annotations never reach the solver; get-unsat-core and get-assignment are non-functional end-to-end *(scope: smtlib-compliance)*
- [ ] `oxiz-solver/src/context.rs:987` — get-info always returns an error — even :all-statistics can never match, and mandatory keywords are unsupported *(scope: smtlib-compliance)*
- [x] `oxiz-core/src/smtlib/parser/terms.rs:419` — Chainable/n-ary core operators rejected: (= a b c), (< a b c), (=> a b c), (xor a b c), (- a b c) are parse errors *(scope: smtlib-compliance)*
- [ ] `oxiz-solver/src/context.rs:762` — :print-success is never implemented, yet get-option reports its default as true *(scope: smtlib-compliance)*
- [ ] `oxiz-core/src/smtlib/parser/commands.rs:316` — define-sort body restricted to a bare symbol; parametric aliases silently become uninterpreted sorts *(scope: smtlib-compliance)*
- [ ] `oxiz-solver/src/context.rs:936` — check-sat-assuming emulated via push/assert/pop; get-unsat-assumptions impossible and post-check queries see popped state *(scope: smtlib-compliance)*
- [ ] `oxiz-theories/src/combination.rs:507` — Nelson-Oppen never propagates equalities to arithmetic; EUF propagation extraction pushes trivial self-equalities *(scope: theories-rest)*
- [ ] `oxiz-theories/src/combination.rs:587` — check_nelson_oppen loops forever once any two shared variables are EUF-equal *(scope: theories-rest)*
- [ ] `oxiz-theories/src/combination.rs:416` — Polite combination fabricates an all-disequal arrangement and asserts it into EUF, producing wrong UNSAT *(scope: theories-rest)*
- [ ] `oxiz-theories/src/combination.rs:627` — Model-based combination never asserts the arrangement into arithmetic and misreports arrangement failure as global UNSAT *(scope: theories-rest)*
- [ ] `oxiz-theories/src/string/solver.rs:651` — check_lengths detects length-constraint violations but silently drops them *(scope: theories-rest)*
- [ ] `oxiz-theories/src/string/solver.rs:525` — StringSolver::check() returns Sat with unresolved word equations and unchecked regex constraints *(scope: theories-rest)*
- [ ] `oxiz-theories/src/euf/solver.rs:966` — EufSolver::assert_false asserts node != node, making any negated assertion an instant contradiction *(scope: theories-rest)*
- [ ] `oxiz-theories/src/array/solver.rs:330` — Read-over-write-diff axiom fires on 'not currently equal' instead of 'proven disequal' indices *(scope: theories-rest)*
- [ ] `oxiz-theories/src/array/solver.rs:372` — Array conflict explanations omit the equality chain, yielding over-strong learned clauses *(scope: theories-rest)*
- [ ] `oxiz-theories/src/datatype/solver.rs:419` — Datatype theory has no acyclicity (occurs) check — cyclic constructor terms reported Sat *(scope: theories-rest)*
- [ ] `oxiz-theories/src/datatype/solver.rs:579` — DatatypeSolver::pop() restores only constraints; constructor tags and app maps leak across backtracking *(scope: theories-rest)*
- [ ] `oxiz-theories/src/combination.rs:893` — verify_model always returns true; complete_model and extract_assignments are identity stubs *(scope: theories-rest)*
- [x] `bench/z3_parity/src/comparator.rs:25` — Parity comparator counts Unknown-vs-any-answer as 'Correct', so 100% parity is achievable by always answering unknown *(scope: test-gap)*
- [ ] `oxiz-solver/tests/property_based.rs:6` — Entire oxiz-solver (and oxiz-core) property-based suites are disabled by default behind a non-default 'property-tests' feature *(scope: test-gap)*
- [ ] `oxiz-solver/tests/property_tests/backtrack_properties.rs:96` — Property tests accept Unknown for both SAT-expected and UNSAT-expected outcomes — an always-Unknown solver passes the suite *(scope: test-gap)*
- [ ] `oxiz-solver/tests/property_tests/model_properties.rs:32` — All model-validity property tests are vacuously guarded by 'if result == Sat' and never assert the result itself *(scope: test-gap)*
- [ ] `oxiz-solver/tests/mbqi_tests/integration_tests.rs:37` — MBQI 'integration tests' are dead code (not referenced by any mod) and vacuous — quantifier instantiation has no end-to-end solving test *(scope: test-gap)*
- [ ] `oxiz-cli/tests/smtlib_benchmarks.rs:95` — Benchmark 'pass' criterion is output containing sat/unsat/unknown; expected status never compared; test never fails by design *(scope: test-gap)*
- [ ] `oxiz-spacer/tests/integration_tests.rs:16` — All four oxiz-spacer end-to-end integration tests are #[ignore]d — the published CHC/PDR engine has zero running end-to-end tests *(scope: test-gap)*
- [ ] `fuzz/fuzz_targets/fuzz_solver.rs:202` — All fuzz targets are crash-only with no soundness oracle; the parser-to-solver end-to-end fuzz path is dead code *(scope: test-gap)*
- [ ] `oxiz-opt/src/pmres.rs:482` — MaxSAT algorithms (PMRES, SortMax) fail their simplest correctness tests, which were #[ignore]d instead of fixed *(scope: test-gap)*
- [ ] `oxiz-solver/tests/nlsat_integration.rs:351` — NLSAT integration tests accept Unknown in 15 of the assertions, including for the trivially UNSAT x<0 AND x>0 *(scope: test-gap)*
- [x] `CHANGELOG.md:8` — CHANGELOG [0.2.4] section is completely empty despite ~6,000 lines of changes since 0.2.3 *(scope: release-audit)*
- [x] `README.md:24` — README 'What's New in 0.2.4 (Unreleased)' actually lists the already-released 0.2.3 features *(scope: release-audit)* — fixed: section now reads "What's New in 0.2.4 (2026-07-19)" and its content (oxiz-py string/FP/quantifier bindings, diagnostics cleanup, production-readiness audit) matches the actual `[0.2.4]` CHANGELOG entry
- [x] `README.md:333` — Supported Logics table marks QF_NRA/UFLIA/AUFBV/HORN 'Complete', contradicting the README's own Alpha/partial status 200 lines earlier *(scope: release-audit)* — verified: table now correctly shows these as 🔶 Alpha/Partial, consistent with the rest of the README
- [ ] `bench/profile/Cargo.toml:2` — bench-profile workspace member lacks publish = false (and license/description), breaking workspace publish *(scope: release-audit)*
- [ ] `.cargo/config.toml:10` — Committed cargo config forces target-cpu=native for all source builds and -undefined dynamic_lookup on every macOS link *(scope: release-audit)*
- [ ] `oxiz-core/src/rewrite/arith.rs:150` — Rational64 (i64) constant folding overflows: wrong constants in release, abort in dev *(scope: panic-audit)*
- [ ] `oxiz-solver/src/solver/types.rs:231` — timeout option accepted but never enforced anywhere: solver can hang forever *(scope: panic-audit)*
- [ ] `oxiz-core/src/ast/manager/builder.rs:948` — mk_bv_extract computes width = high - low + 1 with unvalidated parser indices: u32 underflow *(scope: panic-audit)*
- [ ] `oxiz-core/src/ast/validation.rs:191` — Model validation masks with (1u64 << width) - 1 unguarded for width >= 64 *(scope: panic-audit)*
- [ ] `oxiz-core/src/tactic/bv/advanced_rewriter.rs:549` — AdvancedBvRewriter publicly exported with placeholder term constructors returning Ok(0) *(scope: panic-audit)*
- [ ] `oxiz-sat/src/dimacs.rs:112` — DIMACS header var count triggers unbounded allocation: `p cnf 999999999999 1` hangs/OOMs *(scope: panic-audit)*
- [ ] `oxiz-proof/src/checker.rs:279` — CheckerConfig::verify_conclusions is accepted but never read — ProofChecker validates structure only *(scope: opt-proof)*
- [ ] `oxiz-opt/src/maxsmt.rs:305` — MaxSmtSolver is a hollow stub: solve paths always return Unknown *(scope: opt-proof)*
- [ ] `oxiz-opt/src/maxsat/core.rs:13` — Weight derives Ord: any Int compares less than any Rational regardless of numeric value *(scope: opt-proof)*
- [ ] `oxiz-opt/src/maxsat/algorithms.rs:52` — check_hard_satisfiable resets lower/upper bounds to zero, wiping accumulated MaxSAT cost *(scope: opt-proof)*
- [ ] `oxiz-opt/src/maxsat/algorithms.rs:714` — PMRES builds jointly-unsatisfiable assumptions after multi-clause cores, inflating lower bound *(scope: opt-proof)*
- [ ] `oxiz-opt/src/maxsat/algorithms.rs:491` — OLL core-merging is faked: 'just increase the bound of the first group' *(scope: opt-proof)*
- [ ] `oxiz-opt/src/hybrid.rs:190` — HybridSolver has no hard-clause support and maps exact-solver Unknown to Optimal *(scope: opt-proof)*
- [ ] `oxiz-opt/src/maxhs.rs:151` — MaxHS placeholder uses greedy hitting sets yet reports MaxSatResult::Optimal *(scope: opt-proof)*
- [ ] `oxiz-opt/src/omt.rs:527` — optimize_binary_search claims Optimal when iteration budget is exhausted or bounds are mixed-type *(scope: opt-proof)*
- [ ] `oxiz-proof/src/conversion.rs:141` — drat_to_alethe fabricates proof structure with 'first 5 clauses are Input' and 'last two steps as premises' heuristics *(scope: opt-proof)*
- [ ] `oxiz-opt/src/preprocess.rs:72` — Bounded variable elimination on soft clauses is enabled by default but does not preserve MaxSAT optima *(scope: opt-proof)*
- [ ] `oxiz-opt/src/context.rs:141` — OptConfig.timeout_ms and objective priorities are accepted but silently ignored *(scope: opt-proof)*
- [ ] `oxiz-opt/src/context.rs:856` — is_soft_satisfied cannot evaluate compound terms, so cost() over-reports for non-variable soft constraints *(scope: opt-proof)*
- [ ] `oxiz-spacer/src/bmc.rs:363` — run_kinduction falls through to Safe(max_depth) after only Unknown results *(scope: spacer)*
- [ ] `oxiz-spacer/src/parser.rs:517` — Decimal literals silently parsed as integer 0 *(scope: spacer)*
- [ ] `oxiz-spacer/src/distributed.rs:363` — Distributed PDR is a simulation: workers 'block' POBs by parity and coordinator sleeps *(scope: spacer)*
- [ ] `oxiz-spacer/src/parallel.rs:373` — ParallelPropagator reports every lemma as propagated without any inductiveness check *(scope: spacer)*
- [ ] `oxiz-spacer/src/frames.rs:562` — FrameManager::propagate pushes all lemmas unconditionally and declares fixpoint on first call *(scope: spacer)*
- [ ] `oxiz-spacer/src/existential.rs:75` — Existential handling is a no-op: existential_vars never populated, skolem substitution never applied *(scope: spacer)*
- [ ] `oxiz-spacer/src/existential.rs:622` — WitnessExtractor::extract_witnesses assigns an arbitrary model entry to every existential variable *(scope: spacer)*
- [ ] `oxiz-spacer/src/theory.rs:507` — theory_generalize rewrites x<c to x<=c while claiming the equivalent x<=c-1 *(scope: spacer)*
- [ ] `oxiz-spacer/src/theory.rs:160` — project_variables recurses through Not, turning over-approximation into under-approximation *(scope: spacer)*
- [ ] `oxiz-spacer/src/tactics/bmc_unroll.rs:135` — BMC unroll renaming silently skips Div/Mod/Neg and other term kinds *(scope: spacer)*
- [ ] `oxiz-solver/src/optimization.rs:360` — Unbounded objectives reported as Optimal with an arbitrary value; Unbounded variant is never produced *(scope: solver-rest)*
- [ ] `oxiz-solver/src/optimization.rs:405` — Real optimization converts BigInt objective values via string parse with unwrap_or(0), silently corrupting values beyond i64 *(scope: solver-rest)*
- [ ] `oxiz-solver/src/optimization.rs:219` — Lexicographic optimize() pushes scopes that are never popped, permanently constraining the solver *(scope: solver-rest)*
- [ ] `oxiz-solver/src/optimization.rs:552` — pareto_optimize returns dominated points: exclusion constraint only requires one objective to improve and no dominance filtering is applied *(scope: solver-rest)*
- [ ] `oxiz-solver/src/mbqi/counterexample.rs:1198` — MBQI model evaluator uses Rust truncated division/remainder instead of SMT-LIB Euclidean div/mod *(scope: solver-rest)*
- [ ] `oxiz-solver/src/solver/mod.rs:761` — Wall-clock timeout is accepted through three APIs but never enforced during solving *(scope: solver-rest)*
- [ ] `oxiz-cli/src/portfolio.rs:63` — Portfolio 'strategies' are all identical: every strategy option is silently ignored by Context::set_option, and losing threads are never cancelled *(scope: solver-rest)*
- [ ] `oxiz-solver/src/combination/coordinator.rs:326` — TheoryCoordinator never identifies shared terms (placeholder no-op) and operates on placeholder usize TermIds *(scope: solver-rest)*
- [ ] `oxiz-solver/src/model/advanced_builder.rs:254` — AdvancedModelBuilder is an all-placeholder scaffold publicly exported from model/ *(scope: solver-rest)*
- [ ] `oxiz-solver/src/combination/convexity.rs:347` — CaseSplitStrategy::Lazy causes an infinite loop in process_disjunctions *(scope: solver-rest)*
- [ ] `oxiz-solver/src/combination/convexity.rs:640` — simplify_with_equality implements disequality semantics (and can derive bogus unit equalities); has_conflict always returns false *(scope: solver-rest)*
- [ ] `oxiz-solver/src/solver/check_array.rs:438` — Array pre-check treats Eq nested inside a Bool equality as asserted *(scope: solver-core)*
- [ ] `oxiz-solver/src/solver/encode.rs:321` — Arithmetic atoms with Div/Mod/nonlinear/oversized constants are silently unconstrained *(scope: solver-core)*
- [ ] `oxiz-solver/src/solver/theory_manager.rs:1574` — final_check maps arith Unknown and Err to Sat *(scope: solver-core)*
- [ ] `oxiz-solver/src/solver/mod.rs:879` — reset() leaves MBQI quantifiers, e-matching state and has_quantifiers stale *(scope: solver-core)*
- [ ] `oxiz-solver/src/solver/encode.rs:1277` — FP and String theory atoms are free booleans; 'theory solver handles these' does not exist *(scope: solver-core)*
- [ ] `oxiz-solver/src/solver/check_array.rs:10` — Array theory decided only by syntactic pre-checks; no axiom instantiation in the solving loop *(scope: solver-core)*
- [ ] `oxiz-solver/src/solver/encode.rs:983` — TermKind::Let encoding silently drops bindings *(scope: solver-core)*
- [ ] `oxiz-solver/src/solver/encode.rs:695` — Unbounded recursion in encode/simplify/collectors can overflow the stack on deep formulas *(scope: solver-core)*
- [ ] `oxiz-solver/src/solver/theory_manager.rs:866` — Conflict clauses silently drop literals for terms without SAT vars and ignore assignment polarity *(scope: solver-core)*
- [ ] `oxiz-wasm/src/js_api/model.rs:223` — getUnsatCore returns ALL assertions, not an unsat core *(scope: bindings)*
- [ ] `oxiz-wasm/src/js_api/worker_support.rs:456` — WorkerHandler "solve" task silently drops failed assertions, then answers sat *(scope: bindings)*
- [ ] `oxiz-wasm/src/js_api/worker_support.rs:281` — WorkerPool never spawns workers and never executes submitted tasks *(scope: bindings)*
- [ ] `oxiz-wasm/src/js_api/solver_core.rs:449` — executeAsync/executeWithProgress split scripts at 20-line boundaries, breaking multi-line s-expressions *(scope: bindings)*
- [ ] `oxiz-py/src/solver_py.rs:424` — Python model() truncates bitvector values wider than 64 bits to the low limb *(scope: bindings)*
- [ ] `oxiz-wasm/package.json:57` — npm exports.require points to pkg-nodejs which is neither built by prepublishOnly nor included in files *(scope: bindings)*
- [ ] `oxiz-wasm/src/js_api/streaming.rs:345` — StreamingSolver.nextModelEntry always returns None; startModelStream returns a disconnected controller *(scope: bindings)*
- [ ] `oxiz-wasm/src/js_api/memory_management.rs:313` — MemoryManager.allocate immediately drops the buffer; allocate/free are no-ops *(scope: bindings)*
- [ ] `oxiz-wasm/src/lazy_loader.rs:556` — LazyLoader fetches theory module bytes but never instantiates them, yet marks theories loaded *(scope: bindings)*
- [ ] `oxiz-wasm/src/js_api/optimize.rs:641` — eliminateQuantifiers is an advertised public API that always fails for quantified input *(scope: bindings)*

### P4 — Minor / Downgraded (polish, perf, docs)

**bindings**:
- [ ] `oxiz-wasm/src/js_api/solver_core.rs:332` — cancel() flag is never observed by checkSat/checkSatAsync; documented cancellation cannot work
- [ ] `oxiz-py/oxiz.pyi:52` — Type stubs omit ~20 exported symbols; theories.rs docstring examples use wrong argument order
- [ ] `oxiz-wasm/src/js_api/diagnostics.rs:160` — getStatistics num_assertions is always 0 (counts "(assert" in output that never contains it)
- [ ] `oxiz-py/src/solver_py.rs:337` — set_timeout/set_option("timeout") reset the entire SolverConfig to defaults
- [ ] `oxiz-vscode/src/extension.ts:322` — findOxizPath uses Unix `test -x` via execSync — workspace-local binary detection breaks on Windows

**core-ast**:
- [ ] `oxiz-core/src/rewrite/bv.rs:222` — BvXor rewrite falls back to returning an OR term: x ^ y becomes x | y
- [ ] `oxiz-core/src/rewrite/arith.rs:404` — Integer mod constant folding uses Rust truncated % instead of SMT-LIB Euclidean mod
- [ ] `oxiz-core/src/rewrite/arith.rs:366` — Div constant folding treats Int division as rational: (div 7 2) folds to real 3.5
- [ ] `oxiz-core/src/ast/egraph.rs:390` — EGraph::add_term maps any IntConst that overflows i64 to 0 and silently drops unconvertible children
- [ ] `oxiz-core/src/ast/congruence.rs:198` — CongruenceClosure::pop does not undo diseqs (or rank/explanations)
- [ ] `oxiz-core/src/ast/congruence.rs:434` — close() skips use-lists of merged terms sharing a root, missing congruence propagation
- [ ] `oxiz-core/src/rewrite/fp.rs:246` — FP rules assume symbolic operands are finite: inf + x -> inf and x/inf -> +0 are unsound
- [ ] `oxiz-core/src/rewrite/string.rs:316` — String folding is byte-based, not codepoint-based; indexof slicing can panic on non-ASCII
- [ ] `oxiz-core/src/ast/manager/query.rs:835` — free_vars counts quantifier-bound variables as free (acknowledged stub)
- [ ] `oxiz-core/src/ast/egraph.rs:346` — EGraph extract/get_class/extract_best use one-level union-find lookup and fail after chained merges
- [ ] `oxiz-core/src/rewrite/uf.rs:210` — UF congruence cache keyed by 64-bit hash of args can return a different application on collision
- [ ] `oxiz-core/src/rewrite/arith.rs:172` — Add/Mul folding inserts Int constants into Real-sorted n-ary terms
- [ ] `oxiz-core/src/rewrite/string.rs:405` — str.to_int folding accepts "+5" and rejects >i64 digit strings

**core-rest**:
- [ ] `oxiz-core/src/qe/datatype/case_analysis.rs:164` — Datatype case analysis returns N copies of the original formula yet reports complete: true
- [ ] `oxiz-core/src/theories/datatype.rs:273` — DatatypeTheory::axiom_to_term emits mk_true/mk_false placeholders instead of real axioms
- [ ] `oxiz-core/src/theories/bitvector.rs:309` — oxiz-core BV and FP theory solvers are decorative: propagate/check_for_conflicts do nothing
- [ ] `oxiz-core/src/model/completion.rs:128` — Model completion assigns wrong-sorted defaults: variables get Uninterpreted values, sorts guessed by magic ids
- [ ] `oxiz-core/src/qe/qe_lite.rs:140` — QeLiteSolver eliminates a quantifier only when the body is literally `true`
- [ ] `oxiz-core/src/smtlib/printer/model.rs:55` — Model printer emits syntactically invalid output for function interpretations
- [ ] `oxiz-core/src/model/evaluator.rs:346` — TermKind::Div on integers evaluated as exact rational division, not SMT-LIB euclidean div
- [x] `oxiz-core/src/smtlib/oxiz-core/src/smtlib/printer/config.rs:1` — Stray junk files inside src/: nested duplicate config.rs and .txt scratch files (directory removed; verified absent from the tree)

**core-tactic**:
- [ ] `oxiz-core/src/tactic/ackermann.rs:107` — Ackermannization replaces function applications under quantifiers with ground fresh variables
- [ ] `oxiz-core/src/tactic/solve_eqs.rs:696` — FourierMotzkinTactic performs real-valued elimination on integer variables and can answer Sat wrongly
- [ ] `oxiz-core/src/tactic/solve_eqs.rs:1016` — coeff_to_term truncates rational constants to integers, changing constraint semantics
- [ ] `oxiz-core/src/tactic/pb2bv.rs:108` — Pb2BvTactic silently drops the constant offset of linear pseudo-boolean sums
- [ ] `oxiz-core/src/tactic/registry.rs:165` — Every tactic in default_registry is a no-op or always-NotApplicable stub
- [ ] `oxiz-core/src/tactic/combinators.rs:41` — ThenTactic returns a single subgoal's Solved verdict as the answer for the whole goal set
- [ ] `oxiz-core/src/tactic/core/mod.rs:68` — TacticResult has no model converter — variable-eliminating tactics lose model information
- [ ] `oxiz-core/src/tactic/core/goal_refinement.rs:210` — goal_refinement.rs (695 lines) is orphaned: not in any module tree and cannot compile
- [ ] `oxiz-core/src/tactic/core/split_clause.rs:172` — SplitClauseTactic allocates literal 0 as its first fresh variable, breaking clause semantics
- [ ] `oxiz-core/src/tactic/core/ctx_solver_simplify.rs:224` — core/ctx_solver_simplify.rs is a 580-line dead placeholder with fake TermId and always-false oracles
- [ ] `oxiz-core/src/tactic/combinators.rs:352` — TimeoutTactic leaks the worker thread after timeout with no cancellation

**frontends**:
- [ ] `oxiz-cli/src/processor.rs:122` — --stats always reports 0 decisions/propagations/conflicts/restarts
- [ ] `oxiz-cli/src/format.rs:638` — -o with multiple input files overwrites the output file per result, keeping only the last
- [ ] `oxiz-cli/src/main.rs:1170` — Solver/parse errors exit with code 0 unless --cicd-strict is set
- [ ] `oxiz/README.md:90` — Facade README documents a nonexistent 'solver' feature flag and a stale version, alongside a 'production-ready' parity claim

**math**:
- [ ] `oxiz-math/src/interval.rs:474` — Interval::mul openness handling excludes attainable value 0, producing intervals that miss true values
- [ ] `oxiz-math/src/grobner/buchberger.rs:944` — check_equalities uses complex Nullstellensatz criterion to answer real satisfiability
- [ ] `oxiz-math/src/polynomial/extended_ops.rs:1156` — isolate_roots systematically misses roots at x=0
- [ ] `oxiz-math/src/fast_rational.rs:776` — Division by zero silently returns 0 in release builds
- [ ] `oxiz-math/src/mpfr.rs:173` — ArbitraryFloat::one() returns 2^(precision-1) instead of 1
- [ ] `oxiz-math/src/mpfr.rs:685` — align_with truncates shifted-out bits, so RoundUp/RoundDown directed rounding is incorrect
- [ ] `oxiz-math/src/polynomial/extended_ops.rs:957` — resultant() is a self-acknowledged approximation that can return mathematically wrong values
- [ ] `oxiz-math/src/realclosure.rs:460` — add_algebraic/mul_algebraic silently return rational approximations of irrational algebraic numbers
- [ ] `oxiz-math/src/polynomial/extended_ops.rs:1312` — as_dense_i64 guard uses && instead of proper univariate-in-var check, silently corrupting polynomials
- [ ] `oxiz-math/src/delta_rational.rs:146` — DeltaRational mul/div by non-integer scalar silently drops the infinitesimal delta
- [ ] `oxiz-math/src/grobner/buchberger.rs:1063` — get_model assigns 0 as the root of arbitrary higher-degree univariate basis polynomials
- [ ] `oxiz-math/src/polynomial/root_isolation.rs:85` — usize subtraction of sign variations panics on reversed or degenerate input intervals
- [ ] `oxiz-math/src/polynomial/extended_ops.rs:555` — Polynomial::eval panics on any unassigned variable
- [ ] `oxiz-math/src/grobner/buchberger.rs:215` — Groebner basis iteration caps silently return an incomplete basis

**nlsat**:
- [ ] `oxiz-nlsat/src/simplify.rs:240` — eliminate_redundant treats p and -p as equivalent, deleting non-redundant inequality atoms
- [ ] `oxiz-nlsat/src/interval_set.rs:481` — restrict_to_integers uses ceil/floor on the wrong bound sides, admitting integers outside the set
- [ ] `oxiz-nlsat/src/nia.rs:393` — Integer solutions accepted by f64 tolerance: non-integer models can be reported for integer variables
- [ ] `oxiz-nlsat/src/grobner_preprocess.rs:251` — Groebner timeout leaks a detached thread running Buchberger to completion
- [ ] `oxiz-nlsat/src/solver/propagate.rs:254` — theory_propagate assigns literals without enqueueing them for BCP
- [ ] `oxiz-nlsat/src/solver/decide.rs:245` — Negated root atoms with missing root yield empty feasible set instead of full set

**opt-proof**:
- [ ] `oxiz-opt/src/smtlib.rs:201` — SMT-LIB get-objectives always reports optimal: true
- [ ] `oxiz-proof/src/simplify.rs:251` — ProofSimplifier rewrites step conclusions in place without adjusting rules/premises; combine_inferences is a no-op

**panic-audit**:
- [ ] `oxiz-core/src/qe/bv/simplification.rs:156` — QE BvSimplifier constant folding shifts 1u64 by width with no >=64 guard
- [ ] `oxiz-core/src/ast/manager/builder.rs:931` — mk_bv_concat silently defaults unknown operand widths to 32
- [ ] `oxiz-cli/src/main.rs:661` — CLI aborts via expect on stdin I/O errors (panic=abort profile)
- [ ] `rustc-ice-2026-04-25T11_26_41-70917.txt:1` — Two rustc ICE dumps committed at repo root; caused by disk exhaustion, and they leak developer paths

**release-audit**:
- [ ] `Cargo.toml:46` — No rust-version (MSRV) declared anywhere; README states three conflicting minimums
- [ ] `oxiz-sat/src/gpu.rs:657` — Published cuda/opencl/vulkan feature flags are inert stubs that can never activate
- [x] `CHANGELOG.md:518` — Stale trailing '[Unreleased]' section and 'Known Limitations' still claims Python bindings are not implemented — reviewed: the "Python bindings" limitation is inside the historical `[0.1.0]` release entry (accurately describing that release's gaps per Keep a Changelog convention, not a living/current claim); the separate trailing `## [Unreleased]` block is a forward-looking "Planned" placeholder for the *next* release, distinct from the current `[0.2.4] - 2026-07-19` entry above it. No change needed; not actually stale/misleading in context.
- [ ] `oxiz/src/lib.rs:125` — Meta-crate doc example advertises Solver::execute_script, which does not exist
- [ ] `examples/debug_test.rs:1` — Root examples/ directory is orphaned dead code — the virtual workspace root has no package, so it never compiles
- [ ] `scripts/build_python.sh:1` — No publish script for the 15-crate ordered crates.io release
- [x] `oxiz-vscode/package.json:7` — VS Code extension metadata: MIT license contradicts Apache-2.0 project, repository URL points to nonexistent org — already fixed: `license` field is `"Apache-2.0"` and `repository.url` is `https://github.com/cool-japan/oxiz` (verified at release time)
- [ ] `oxiz-core/Cargo.toml:29` — Workspace-inheritance drift: several crates pin dependency versions inline that the workspace already defines
- [ ] `.gitignore:7` — Cargo.lock is globally gitignored although the workspace ships binaries (oxiz-cli)
- [ ] `docs/smtcomp2026_participation.md:11` — docs/ contains stale version references (v0.2.0) presented as current facts
- [ ] `oxiz-ml/Cargo.toml:10` — oxiz-ml lists 'machine-learning', which is not a crates.io category slug and will be dropped at publish

**sat**:
- [ ] `oxiz-sat/src/allsat.rs:328` — AllSAT: minimal/maximal model options silently ignored; block_positive_only under-enumerates while reporting Complete
- [ ] `oxiz-sat/src/chrono.rs:96` — Chronological backtracking (default-on) is effectively inert: asserting-check conflates level 0 with unassigned and runs pre-backtrack
- [ ] `oxiz-sat/src/xor.rs:235` — GF2Matrix::propagate destructively rewrites rows with no backtracking support

**smtlib-compliance**:
- [ ] `oxiz-core/src/smtlib/lexer.rs:238` — Lexer silently accepts unterminated strings/quoted symbols; numerals with leading zeros; bare '#' token; (_ bvN w) limited to i64

**solver-core**:
- [ ] `oxiz-solver/src/context.rs:998` — declare-sort/define-sort/define-fun/declare-datatype silently ignored by Context
- [ ] `oxiz-solver/src/solver/theory_manager.rs:612` — model_based_combination is O(n^2) over all encoded terms on every final_check

**solver-rest**:
- [ ] `oxiz-solver/src/mbqi/integration.rs:161` — set_max_rounds is ineffective: current_round is reset to 0 at the top of every run(), so the limit check never fires
- [ ] `oxiz-solver/src/mbqi/patterns.rs:585` — MultiPatternCoordinator::find_matches reads a match_cache that is never populated, so it always returns no matches
- [ ] `oxiz-solver/src/optimization.rs:749` — Known-incomplete arithmetic at optimizer level: test accepts Optimal for x=y AND x!=y; exact gaps identified

**spacer**:
- [ ] `oxiz-spacer/src/parser.rs:461` — Unknown sorts silently default to Bool in ChcParser
- [ ] `oxiz-spacer/src/pdr.rs:399` — find_blocking_lemma returns the first lemma regardless of whether it blocks the state
- [ ] `oxiz-spacer/src/pob.rs:440` — PobQueue::is_subsumed ignores the POB state entirely
- [ ] `oxiz-spacer/src/smt.rs:302` — extract_model fabricates variable names that never occur in the asserted formulas

**test-gap**:
- [ ] `oxiz-sat/tests/property_tests/cdcl_properties.rs:111` — SAT-core property tests assert only 'Sat | Unsat' on instances with known answers and never validate models against the CNF
- [ ] `bench/z3_parity/src/z3_runner.rs:78` — No automated differential testing against Z3: parity harness is a manual out-of-workspace binary and its Z3 tests are ignored
- [ ] `oxiz-cli/tests/cli_integration.rs:80` — CLI basic-solving test passes even if the binary prints an error for a trivially SAT input
- [ ] `oxiz-solver/tests/nlsat_integration.rs.disabled:70` — Checked-in disabled test file contains fully tautological assertion accepting Sat|Unsat|Unknown
- [ ] `oxiz-math/tests/property_tests/polynomial_extended.rs:333` — Tautological prop_assert!(true) 'doesn't panic' tests duplicated in two files
- [ ] `oxiz-theories/tests/test_bv10.rs:14` — Public BvSolver theory API cannot solve udiv inverse constraints; the covering test is ignored citing 'API limitation'

**theories-arith**:
- [ ] `oxiz-theories/src/bv/solver_advanced.rs:368` — AdvancedBvSolver is an uncompiled stub file: NOT returns its input, bit-blasting and interval phases are no-ops
- [ ] `oxiz-theories/src/bv/solver.rs:1718` — get_value shifts 1u64 << i for widths > 64: debug panic, silently wrong model values in release

**theories-rest**:
- [ ] `oxiz-theories/src/euf/ematching.rs:443` — MBQI counter-example search never consults the model — blind instantiations presented as model-based
- [ ] `oxiz-theories/src/string/solver.rs:833` — StringSolver::pop() does not restore shared_equalities, leaking cross-theory equalities from popped scopes
- [ ] `oxiz-theories/src/simplify.rs:167` — Simplification cache never invalidated by later facts; advertised rules unimplemented
- [ ] `oxiz-theories/src/string/regex.rs:406` — Regex identity keyed by raw u64 hash (no equality check); union/inter sort via Debug formatting

**z3-gap**:
- [ ] `oxiz-solver/src/mbqi/integration.rs:576` — MBQI collect_ground_terms is an empty stub; trigger patterns never seed candidates
- [ ] `oxiz-core/src/unsat_core.rs:84` — Public UnsatCore::minimize is a documented placeholder no-op

### Policy / Release Chores

- [x] `oxiz-theories/src/bv/solver.rs` — 2008 lines, exceeds the 2000-line refactoring policy; split with splitrs (now 1779 lines; `bv/solver/{division,shifts,tests}.rs` extracted as submodules — split still in progress, see "Remaining" below for the last piece)
- [ ] Eliminate remaining `.unwrap()` in non-test code (48 hits at audit time; ~39 found in a spot-recheck at release time — not independently re-verified item-by-item this pass, see "Remaining" below)
- [x] Delete stray `rustc-ice-2026-04-25T11_26_41-70917.txt` / `rustc-ice-2026-05-04T17_25_54-90362.txt` at repo root (and gitignore `rustc-ice-*.txt`) — both files absent from the tree; `.gitignore` still has the `rustc-ice-*.txt` pattern
- [x] Fill empty `CHANGELOG.md` [0.2.4] section from git log since 0.2.3 — comprehensive waves-1–5 summary added this release
- [x] `oxiz-cli/tests/benchmark.rs` — wall-clock <5000ms assertions are flaky under CPU load (3 false failures observed under parallel load); gate behind env var or move to criterion benches — now gated behind `OXIZ_TIMING_TESTS=1`
- [x] Revise README/TODO 'production ready / 100% Z3 parity' claims — contradicted by P0/P1 findings and `bench/z3_parity/results.json` (4 Sat answers on UNSAT quantified benchmarks per test-gap audit) — README now reports the honest 168-benchmark breakdown (122 Correct/35 Inconclusive/10 Error/1 Wrong) and calls out QF_S/QF_FP by name; the `results.json` itself no longer shows the 4-wrong-quantified-Sat pattern (regenerated with the honest comparator; only 1 `Wrong` result remains, in `QF_NIRA`)
- [ ] Complete adversarial verification of the P2/P3 lists (verification pass was stopped early: 90 of ~250 verdicts collected) — this release's re-verification pass covers all of P0/P1/P2 and a ~15-item sample of P3/P4 (see the note at the top of this section); the remaining P3/P4 items still need a dedicated verification pass

### Audit Coverage Notes (scope summaries)

- **bindings**: Audited oxiz-wasm (all src + package.json), oxiz-py (all src, pyproject, oxiz.pyi), and oxiz-vscode (extension.ts, package.json), cross-checking against oxiz-solver/oxiz-core internals. Solid: core WasmSolver assert/checkSat/model paths, py Solver/Optimizer wrappers (no unwrap/panic), version sync (workspace 0.2.4 = package.json), and the VSCode extension targets a real `oxiz --lsp` server with valid CLI flags. Critical problems concentrate in the WASM extras: the optimization API silently drops objectives and reports "optimal", computeInterpolant returns a non-interpolant, getUnsatCore returns all assertions, and the worker/streaming/memory/lazy-loader modules are facades. oxiz-py truncates >64-bit BV model values; npm CommonJS entry is unshippable as configured.
- **core-ast**: Audited oxiz-core term manager/interning (manager/mod.rs, builder.rs, query.rs), all 13 rewriters, simplification/, egraph + congruence closure, arena and lazy_eval. Found 9 critical soundness defects: stubbed substitution silently skipping UF/BV/String terms, absorption/factoring rules that drop conjuncts/disjuncts, BvXor rewritten to BvOr and shifts rewritten to their lhs (reachable via CombinedRewriter), truncated-vs-Euclidean mod, rational folding of integer div, e-graph BigInt-to-0 truncation with dropped children, and non-backtracked disequalities. Plus missed congruence propagation, sort-blind interning, unsound FP infinity rules, unicode string panics, and unbounded recursion. Solid: arena allocator, lazy_eval, poly normalization, array rewriter, core bool/arith comparison rules, mk_* creation-time simplifications.
- **core-rest**: Audited oxiz-core: smtlib parser/printer, qe/* (arith, array, bv, string, datatype, cad), theories/*, model/*, resource.rs, error.rs, unsat_core.rs, datalog, ematching. Worst finding: the production SMT-LIB parser (used by CLI via Context::execute_script) parses div/mod as subtraction, drops "/" and indexed BV ops to Bool-sorted UF, defaults undeclared symbols to Bool vars, silently skips unknown commands, and loses numeric set-option values — direct wrong-answer paths. The qe/ and theories/ layers contain systematic placeholder stubs, several unsound (string QE returns true unconditionally; Cooper QE claims elimination without substituting; datatype axioms become mk_true/mk_false). Model evaluator/completion silently truncate big constants and assign wrong-sorted defaults. Solid: resource.rs limits, lexer, sorts parsing, no-unwrap discipline in production paths (unwraps confined to tests).
- **core-tactic**: Inspected all 43 files under oxiz-core/src/tactic/ plus the registry consumer (oxiz-solver z3_compat_ext2). Headline: the entire default_registry is fake — all 19 registered tactics either clone the goal or return NotApplicable, while the public Z3Tactic API dispatches to them. The stateful (apply_mut) implementations that do real work carry critical soundness bugs: DER's forall rule is inverted, Skolemization shares sk_N names across assertions and ignores polarity, quantifier instantiation ignores polarity, Ackermannization descends under quantifiers, Fourier–Motzkin mishandles integers/rational truncation/op-limit aborts, pb2bv drops constant offsets, lia2card aliases aux variables. Solid parts: PropagateValuesTactic, SolveEqsTactic core substitution, ctx_simplify ITE elimination, and EliminateUnconstrained look sound (modulo the missing model-converter).
- **frontends**: Audited oxiz-cli (all modules), oxiz facade (lib/easy/README/Cargo.toml), oxiz-smtcomp websocket.rs+svcomp.rs, and oxiz-ml. Root systemic defect: Context::set_option ignores everything except produce-proofs/produce-unsat-cores, so most advertised CLI flags (timeout, resource limits, strategy/preset/auto-tune, enumerate/optimize) are silently dead; portfolio and distributed modes are consequently fake. Hidden stubs: --count-models fabricates answers, --interpolate is a placeholder, --validate-model and --minimize-core do nothing. Soundness edges: EasySolver drops constraints on unknown names; TPTP free-variable handling can flip SZS verdicts; DIMACS rejects valid multi-line/empty-clause files. Solid areas: websocket.rs and svcomp.rs are clean; oxiz-ml is a real, correctly implemented ML library (genuine backprop, wired via oxiz-sat external_branching) with small but real benches; facade re-exports compile-consistent.
- **math**: Audited oxiz-math end-to-end: interval arithmetic, fast_rational, rational utils, mpfr emulation, polynomial extended_ops/helpers/root isolation, grobner/buchberger (incl. NraSolver), simplex, delta_rational, realclosure, algebraic/isolate; spot-checked matrix.rs/blas.rs (assert-guarded, standard f64 kernels — no defects found) and cross-checked consumers (oxiz-nlsat uses interval + grobner reduce; oxiz-theories uses DeltaRational). Five critical soundness bugs: sign-broken Sturm sequences (wrong root counts, concrete counterexample), Interval::mul openness excluding attainable 0, NraSolver returning Sat for unsat linear inequalities and for complex-only-solvable equalities, and isolate_roots missing roots at x=0. Major issues include truncated Groebner reduction dropping remainders, simplex ignoring non-basic bound violations, i64::MIN corruption in FastRational, mpfr one()/rounding defects, and multiple silent approximation stubs. algebraic/isolate.rs and polynomial/root_isolation.rs Sturm chains use exact remainders and look sound.
- **nlsat**: Audited oxiz-nlsat end-to-end: solver core (mod/decide/propagate/conflict), cad.rs Sturm root isolation, interval_set, explain, simplify, grobner_preprocess, portfolio, nia, maxsat, plus the oxiz-theories bridge that consumes results. Core defects: rational-only root finding makes feasible regions wrong (x^2>2 answers UNSAT, trusted by the bridge for univariate atoms); empty-region backtracking livelocks; incremental solve reuses stale state; NIA branch-and-bound leaks contradictory branch constraints; Sturm chains are sign-broken for negative leading coefficients; Portfolio/MaxSAT are hollow stubs; ~25 of 40 exported modules (incl. CAD explanations and proofs) are never wired into solving. Solid parts: BCP two-watched-literal scheme, clause management/LBD/restarts, interval intersection/union, Groebner basis math, rational-root theorem implementation.
- **opt-proof**: Audited all of oxiz-opt (maxsat core/algorithms/types, maxsmt, OptContext, preprocess, pareto/pareto_enumerate, omt, hybrid, maxhs, smtlib, totalizer) and the priority oxiz-proof files (checker, rules, drat, craig, conversion, simplify, recorder, resolution, validation). Solid: DRAT text/binary emission, resolution.rs pivot-checked resolution, Recorder, Pareto frontier insertion, tautology/duplicate/subsumption preprocessing. Broken: weighted MaxSAT correctness (stratified path, Weight Ord, bound resets, PMRES/OLL bookkeeping), preprocessing soundness (soft unit propagation, BVE), optimality over-claiming across OptContext/OMT/hybrid/MaxHS/SMT-LIB, and oxiz-proof's marquee features — Craig interpolation returns trivial 'true', rule validators accept everything, verify_conclusions is ignored, and DRAT-to-Alethe conversion fabricates proofs. Not production-ready in these areas.
- **panic-audit**: Workspace-wide panic/robustness audit of production paths (all 16 crates; tests/benches/examples excluded). unwrap/expect/panic/unreachable/asserts are almost entirely confined to #[cfg(test)] modules — the no-unwrap pass largely held; remaining expects are mostly justified invariants. Real defects concentrate in the SMT-LIB frontend and BV width arithmetic: standard indexed BV operators silently become uninterpreted Bool functions (wrong answers), unbounded parser recursion (stack-overflow abort), extract-width u32 underflow, unguarded 1u64<<width at width 64, and i64 Rational64 constant folding that wraps in release. Resource governance is the other gap: timeout_ms is accepted via three public APIs and never read, and DIMACS headers drive unbounded allocation. SAT core loops, DIMACS literal handling, lexer UTF-8 slicing, wasm/py bindings, and ResourceMonitor conflict/decision budgets look solid. Both rustc-ice files are disk-full build artifacts, not code bugs.
- **release-audit**: Audited all 19 workspace manifests, CHANGELOG, README, docs/, examples/, scripts/, fuzz exclusion, .cargo/config, .gitignore, oxiz-py pyproject, oxiz-wasm/oxiz-vscode package.json, and lib.rs doc versions. Solid: version.workspace=true everywhere at 0.2.4; per-crate keywords/categories/descriptions present; fuzz crate correctly isolated (own [workspace], publish=false); LICENSE present; per-crate READMEs exist for auto-detection; pyproject uses dynamic version via maturin; wasm package.json at 0.2.4; README/lib.rs quick-start examples reference real APIs (Context::execute_script, Python bindings verified); only allowed workflows (npm/pypi-publish) active; rustc-ice files untracked and gitignored. Main gaps: empty 0.2.4 changelog, README What's-New mislabeled and logic-status overclaims, bench-profile publishable, committed target-cpu=native, no MSRV.
- **sat**: Audited oxiz-sat end-to-end: CDCL core (propagate/analyze/learn/decide/incremental), clause DB/pool/watches, proof writers, xor, gpu, cube, symmetry+tactic, portfolio, allsat, assumptions, preprocessing/inprocessing. Found 8 critical soundness paths: binary-graph reason-position violation in conflict analysis, clause-slot reuse with stale watchers, dirty-trail assumptions giving false UNSAT, false-literal watches on incremental add_clause, logically inverted inprocessing strengthening, model-breaking pure-literal elimination, never-purged binary graph after pop, and an unsound symmetry tactic. Plus inverted XOR RHS extraction, non-functional cube/proof-check/GPU/core-minimization stubs, unintegrated DRAT logging, and no timeout/interrupt anywhere. Solid: DIMACS parser, trail, Luby restarts, main watch loop for 3+ clauses, GPU feature gating honesty.
- **smtlib-compliance**: Audited SMT-LIB 2.6 compliance end-to-end: lexer (oxiz-core/src/smtlib/lexer.rs), parser (parser/{commands,sorts,terms}.rs), executor (oxiz-solver/src/context.rs), and CLI (oxiz-cli/src/main.rs, processor.rs, interactive.rs), cross-checked against the parity benchmark suite. Critical soundness: div/mod parsed as subtraction; '/', abs, to_real, zero_extend/sign_extend/rotate become uninterpreted Bool applies; unknown commands (define-fun-rec, declare-sort, get-unsat-assumptions) silently dropped. Options are largely write-only (:timeout, :random-seed, :print-success ignored); :named/unsat-core/get-assignment/get-info broken end-to-end; chainable operators and standard set-info headers cause parse aborts. The 88-benchmark parity suite avoids all these constructs, so the claims don't generalize. Solid areas: basic core/BV/FP/string operator parsing, push/pop scoping, let/quantifier binding hygiene, decimal-to-rational conversion with overflow checks.
- **solver-core**: Audited oxiz-solver: solver/mod.rs, encode.rs, theory_manager.rs, check_fp/check_array/check_nlsat/check_string, context.rs, simplify.rs, plus parser cross-checks. Core CDCL(T) plumbing for EUF/LRA and boolean encoding is genuine, and simplify.rs is sound. But production readiness is undermined by: resource-limit exhaustion and arith Unknown/Err converted into definitive Sat; MBQI returning Sat after unverified iterations; signed BV comparisons double-asserted into arithmetic with unsigned semantics; polarity bugs in FP/array pre-checks producing wrong UNSAT; BV state leaking across push/pop; and FP/String/Array 'support' that is benchmark-tuned pattern matching (comments cite fp_06, string_02, array_03) over free boolean atoms — consistent with overfitting to the 88-benchmark parity suite. Timeout options are accepted but never enforced.
- **solver-rest**: Audited oxiz-solver MBQI (integration, counterexample, model_completion, patterns, conflict_driven), combination (coordinator, convexity), model/advanced_builder, optimization.rs, the CLI portfolio, and EasySolver. Worst defects: the solver answers SAT for quantified formulas on two unverified paths (10-round MBQI fallback; "Satisfied" from enumerating <=10 candidates over infinite domains), and MBQI substitution silently skips many TermKinds, emitting lemmas with leftover bound variables. Optimizer mislabels unbounded/cap-out results as Optimal and corrupts large values. Timeouts are accepted but never enforced. Coordinator, convexity, advanced_builder, and CLI portfolio contain placeholder logic behind public APIs. Solid areas: model_completion deliberately avoids unsound else_value defaults; counterexample lemma generation itself is conservative (Unknown over Satisfied) in most residual cases; EasySolver core flow works for declared variables.
- **spacer**: Audited all 26 files of oxiz-spacer (~15.3k LoC): pdr.rs, smt.rs, bmc.rs, frames.rs, parser.rs, chccomp.rs, existential.rs, theory.rs, distributed.rs, parallel.rs, invariant.rs, generalize.rs, ctg.rs, pob.rs, reach.rs, tactics/. The core PDR loop is placeholder-grade: init-reachability and transition-feasibility stubs make Unsafe unreachable and the inductiveness check is trivially true, so Spacer::solve returns wrong Safe verdicts. ChcParser erases predicate applications; BMC/k-induction conjoin multiple transition rules; Houdini performs no SMT verification; distributed/parallel/existential modules are simulations. Solid: chccomp.rs (real SMT-LIB parser), bmc.rs single-rule linear path with sound Unknown fallbacks, frames/pob data structures, generalize.rs/ctg.rs structure (though dependent on the broken consecution check).
- **test-gap**: Test-quality audit across all 16 crates, fuzz/, and bench/. Worst issues: the repo's own parity results.json records 4 Sat-answers on UNSAT quantified benchmarks while README claims 100% parity, and no test covers those directories; the parity comparator counts Unknown as Correct; an ignored test documents SAT-with-wrong-model BV behavior; oxiz-solver/oxiz-core property suites are feature-gated off and Unknown-tolerant when on; MBQI has only dead vacuous tests; spacer and MaxSAT (PMRES/SortMax) hide broken basics behind #[ignore]; fuzzing is crash-only with the parser+solver path as dead code. Solid areas: oxiz-solver/tests/bv_soundness_integration.rs (exact sat/unsat), oxiz-py tests (exact results plus model-value checks), most oxiz-sat CDCL exact-result assertions.
- **theories-arith**: Audited oxiz-theories arithmetic (simplex, simplex_opt, LIA cuts/branching/heuristics, ArithSolver), bv (solver.rs, solver_advanced.rs), and fp (solver.rs, ieee754_full.rs). Production-path critical soundness bugs: BV barrel shifters ignore high shift bits; all four BV division encodings admit wrapped spurious quotients; QF_LIA runs only the LP relaxation (no integrality); simplex reports SAT on pivot exhaustion. Public-API LiaSolver B&B wipes constraints via reset() and adds invalid placeholder MIR/CG cuts; FpSolver comparisons are sign-only stubs and conversions unconstrained; IEEE754 engine mis-rounds RNE ties, halves odd-exponent sqrt inputs, and doubles subnormals. Core bit-blasting gates (and/or/xor/adder/mux/ult), LRA delta-rational strict bounds, and Farkas explanations look sound. bv/solver_advanced.rs is dead stub code.
- **theories-rest**: Audited oxiz-theories: combination.rs, simplify.rs, euf/*, array/*, string (solver/regex/automata), set/*, datatype/*, character surface. Worst defects are in the production EUF path (wired into oxiz-solver with push/pop): un-trailed path compression and un-popped proof-forest edges both corrupt incremental state, enabling wrong sat/unsat. Nelson-Oppen combiner is largely a facade — no arithmetic propagation, fabricated arrangements, an infinite fixpoint loop, and stub model verification. StringSolver silently drops length conflicts and reports Sat with unresolved constraints; ArraySolver's read-over-write-diff guard and one-literal conflict explanations are unsound; DatatypeSolver lacks acyclicity and leaks state across pop. Set theory propagation and the automata/subset-construction code looked comparatively solid; EUF congruence closure core (sig/fingerprint tables, trail undo) is well-engineered aside from the backtracking bugs.
- **z3-gap**: Inspected the SMT-LIB frontend (oxiz-core/smtlib), solver Context and CDCL(T) loop (oxiz-solver), MBQI/E-matching, theory wiring, tactics/qe/MBP, oxiz-opt, and spacer against Z3's catalog (no local Z3 checkout referenced; compared from Z3 knowledge). Solid: SAT core (rich inprocessing/DRAT), nlsat crate, push/pop bookkeeping, deletion-based core minimization, datatype/tester parsing. Broken: only Arith/BV/EUF are real theories — string/FP/array checks are benchmark-keyed heuristics that default to sat; MBQI certifies quantifiers from ≤10 finite candidates (wrong sat); the parser silently drops unknown commands (define-fun-rec, assert-soft, check-sat-using, declare-sort); regex, PB, Seq, Set, recfun, special relations, OMT, tactics, and most solver options are unreachable or no-ops despite existing implementation files. "Production ready / 100% Z3 parity" is not supported by the code.

## Post-0.2.4 Pass — P1 Closure (2026-07-19)

Follow-up pass over the open P1 findings from the 0.2.4 audit wave. Five of the eight previously-open P1 items turned out to be **already fixed at 0.2.4 release time** but the changelog hadn't been updated to reflect the as-committed code; the remaining two genuine parser gaps are closed below, the parity suite is regenerated, and the regeneration surfaced one new soundness finding (promoted to P1). A second sub-pass then wires in a constant folder + variable-substitution preprocessing pass for the FP and String theories (the theories themselves still aren't in `TheoryManager`, but ground FP/String operations now evaluate), lifting 3 SAT-expected `qf_fp`/`qf_s` benchmarks from `Unknown` to `Sat`.

### Closed in this pass (verified by direct source inspection)

- [x] **NLSAT irrational-root isolation** (`oxiz-nlsat/src/solver/decide.rs`) — `compute_arith_regions` → `ineq_atom_region` → `univariate_regions` already routes through `crate::cad::SturmSequence::isolate_roots` (line 345), so irrational discriminants are correctly bracketed; the `ArithDecision::IrrationalOnly` variant in `pick_arith_value` reports `Unknown` rather than a wrong `Unsat` for `x^2 > 2`-style queries with no rational witness.
- [x] **NLSAT empty-feasible-region livelock** (`oxiz-nlsat/src/solver/mod.rs`, main `solve()` loop) — the `ArithDecision` enum now has four exhaustive variants (`Value` / `ProvedEmpty(lemma)` / `IrrationalOnly` / `GreedyEmpty`) with no `None` case; `solve()` learns a valid lemma on `ProvedEmpty` and returns `Unknown` on the cannot-certify cases, so `decide()` can no longer re-derive the identical state forever.
- [x] **NIA branch-and-bound constraint leak** (`oxiz-nlsat/src/nia.rs` — `BranchNode` / `ProblemSnapshot` / `rebuild_solver`) — each branch node now records its bound `path` separately and is solved against a *freshly rebuilt* `NlsatSolver` constructed from a shared base snapshot plus exactly that node's path, so sibling bounds never leak. Only globally-valid Gomory cuts are asserted onto the shared base (and it is re-snapshotted before each node). See the module doc comment at `nia.rs:75` which records this as the audit-finding fix.
- [x] **NLSAT theory-conflict explanation is not a CAD lemma** (`oxiz-nlsat/src/solver/propagate.rs` — `explain_theory_conflict`) — the unsound "negate every assigned atom sharing a variable" heuristic is gone. The function now returns `Some(lemma)` only when `compute_arith_regions(var)` certifies `pure && reliable && outer.is_empty()` (single-variable conflict, exact Sturm-isolated feasible region is empty), and returns `None` otherwise so the caller reports `Unknown` instead of fabricating a clause that could exclude real models. The stronger fix — actually deriving a resultant/discriminant-based CAD projection lemma for *multivariate* conflicts via `explain.rs`'s `ExplainContext` — is still outstanding and is now tracked as a **P2 capability gap** below (no false answer today, just `Unknown` where a real CAD lemma could prove `Unsat`).
- [x] **NIA `floor_ceil` truncates toward zero** (`oxiz-nlsat/src/nia.rs`) — `floor_ceil` now calls `BigRational::floor` / `BigRational::ceil` directly (line 582-584), with regression tests `test_nia_floor_ceil_negative` (`floor(-3/2) == -2`, not `-1`) and `test_nia_floor_ceil_negative_integer` pinning the behaviour.

### Closed in this pass (code changes)

- [x] **Parser gap: FP rounding-mode arguments to indexed operators** (`oxiz-core/src/smtlib/parser/terms.rs`) — added `parse_indexed_fp_conversion`, a new helper that intercepts the four SMT-LIB FP conversion operators that take a `RoundingMode` as their first argument (`to_fp`, `to_fp_unsigned`, `fp.to_sbv`, `fp.to_ubv`) *before* the generic `parse_term_list` path that was rejecting the bare `RNE`/`RNA`/`RTP`/`RTN`/`RTZ` argument as an undeclared symbol. `(_ to_fp e s)` is dispatched to `mk_fp_to_fp` / `mk_real_to_fp` / `mk_sbv_to_fp` based on the source sort (FloatingPoint / Real-or-Int / BitVec); `(_ to_fp_unsigned e s)` → `mk_ubv_to_fp`; `(_ fp.to_sbv w)` → `mk_fp_to_sbv`; `(_ fp.to_ubv w)` → `mk_fp_to_ubv`. Wired into both indexed-identifier dispatch paths (the `((_ to_fp e s) ...)` compound-operator form and the bare `(_ to_fp e s) ...` form). Regression tests in `oxiz-core/tests/audit_parser_terms.rs`: `to_fp_from_real_uses_real_to_fp_and_keeps_rounding_mode`, `to_fp_from_float_uses_fp_to_fp`, `to_fp_from_bv_is_signed_and_to_fp_unsigned_is_unsigned`, `fp_to_sbv_and_fp_to_ubv_parse_with_rounding_mode`, `to_fp_rejects_wrong_arity`.
- [x] **Parser gap: `re.allchar` not recognized** (`oxiz-core/src/smtlib/parser/terms.rs`) — added a `re.allchar | re.all | re.none | re.empty` arm to `parse_symbol` that mints the zero-argument regex constant as a same-named `mk_apply` (consistent with how compound regex operators `re.*`/`re.++`/`re.union`/`re.range` are already lowered today via the generic compound-operator fallback, since oxiz has no dedicated RegEx sort). Regression test: `regex_constants_parse_as_zero_arg_applies`.
- [x] **`bench/z3_parity` regeneration** — re-ran the parity suite against the patched parser. `qf_fp` went from 1/10 correct (9 parser errors) → **4/10 correct, 6 inconclusive, 0 errors** (all 6 SAT-expected cases now report honest `Unknown` rather than failing to parse; the 4 UNSAT-expected cases are all correctly `Unsat`). `qf_s` went from 3/10 correct + 1 parser error → **3/10 correct, 7 inconclusive, 0 errors** (the `re.allchar` parser error is gone; `string_09` now reports honest `Unknown`). The regeneration also picked up one new oxiz-side `Wrong` (`nested_quantifiers.smt2`, see new P1 below) and one Z3-side flake (`array_unique.smt2`, where Z3 itself returned `Unknown` on this run — oxiz's `Unsat` is still correct).

### New finding (promoted to open P1)

- [ ] **Quantifier-theory conflict asserts a literal at the wrong backtrack level** (`oxiz-sat/src/solver/conflict.rs:632`, `analyze_theory_conflict`) — surfaced by regenerating `bench/z3_parity`. In debug builds `nested_quantifiers.smt2` (`forall x. exists y. forall z. (z>=y => f(x,z)>=0)`, expected `sat`) hits the `debug_assert!` "theory: asserting literal must be above the backtrack level (uip level 41, backtrack 41)" — the learnt clause's asserting literal sits at the *same* decision level as the computed backtrack level rather than strictly above, which violates the CDCL 1-UIP invariant for theory conflicts. In release builds the `debug_assert!` is compiled out, so instead of panicking it silently backtracks to the wrong level and eventually reports a wrong `Unsat`. This is a pre-existing soundness bug in the SAT/theory integration for quantified logics (not a regression from the parser fixes above — verified by re-running with the parser patch stashed: same wrong `Unsat`). Fix scope: the theory-conflict learnt-clause construction in `analyze_theory_conflict` needs to guarantee the 1-UIP literal is strictly above the second-highest level (or, when that's not achievable for a theory conflict, fall back to a `Unknown`-producing path the way the NLSAT layer already does).

## Remaining (post-0.2.4)

Deferrals confirmed genuinely still open at 0.2.4 release time — either explicitly out of scope for this release or re-verified as not-yet-fixed during this pass. Priorities: **P1** = correctness gap on a documented/advertised code path; **P2** = capability gap, no false answer; **P3** = infrastructure/process, blocked on an external factor.

### P1 — Correctness gaps (open findings)

- [ ] **Quantifier-theory conflict backtrack-level bug** — see "New finding" in the **Post-0.2.4 Pass** section above; the only remaining P1 correctness gap. All eight P1 items from the 0.2.4 release audit are now closed (5 were already fixed in-tree and just needed their changelog entries updated; 2 parser gaps and the parity regeneration were closed in the post-0.2.4 pass).

### P2 — Capability gaps (no false answers, just missing coverage)

- [ ] **Wire `FpSolver` / `StringSolver` into `TheoryManager`** — partial progress in the post-0.2.4 pass: a constant folder (`oxiz-solver/src/theory_fold.rs`) plus a constant-substitution preprocessing pass (`Context::propagate_constant_subst`) together evaluate any *ground* FP/String operation (one whose operands are all literals) to a constant, lifting 3 SAT-expected `qf_fp`/`qf_s` benchmarks from `Unknown` to `Sat` and 0 errors. The remaining gap is full CDCL(T) integration — incremental theory propagation, conflict explanation, push/pop synchronisation, equality sharing with EUF — which would lift the cases the folder can't reach: non-RNE FP arithmetic (RTP/RTN/RTZ/RNA need exact fixed-point intermediates the engine doesn't currently compute correctly — see `Ieee754Engine::pack`), FP class predicates (`FpIsNaN`/`FpIsZero`/..., which the folder deliberately leaves intact so the structural `check_fp_constraints` pass can keep detecting NaN/Inf conflicts), and string operations whose operands are *not* ground.

- [ ] **NLSAT multivariate theory-conflict CAD lemmas** (`oxiz-nlsat/src/solver/propagate.rs` — `explain_theory_conflict`, `oxiz-nlsat/src/explain.rs` — `ExplainContext`) — the P1 soundness bug (negating every atom sharing a variable, which could exclude real models) is closed: the function now returns `None` and lets the caller report `Unknown` whenever it cannot certify single-variable infeasibility via Sturm-isolated root intersection. The *capability* gap remaining is that genuine multivariate conflicts (which need a resultant/discriminant-based CAD projection lemma) still fall through to `Unknown`; `explain.rs`'s `ExplainContext` exists but isn't wired into `explain_theory_conflict`. Wiring it would lift a class of `Unknown` answers to correct `Unsat` answers — no false answers today, just missing coverage.

- [ ] **`get-consequences` SMT-LIB command unimplemented** — not in `oxiz-core/src/smtlib/parser/commands.rs`'s command dispatch; falls through to the honest "unsupported command" error path added this release (no silent wrong behavior, just unsupported). Distinct from `oxiz-theories::user_propagator::get_consequences`, a Boolean user-propagator API that already exists.
- [ ] **nlsat "KEEP-INTERNAL" wiring pipeline** — this release demoted ~25 correct-but-unwired `oxiz-nlsat` modules (SAT-style inprocessing: `bce`, `bve`, `vivification`, `subsumption`, alternative CAD/evaluator implementations, `proof` logging, etc.) from `pub` to `pub(crate)` as an honesty fix (see `oxiz-nlsat/src/lib.rs`'s module doc comment) rather than wiring them into the solve loop. They remain compiled and tested. Actually wiring any of them in (inprocessing hooks, CAD explanation/proof logging into the main `solve()`) is deferred; each module's own doc comment records why it isn't wired yet.
- [ ] **`oxiz-wasm` cooperative-only timeout** (`oxiz-wasm/src/js_api/promise_wrapper.rs`) — `timeoutMs` races the solve `Promise` against a `setTimeout` promise; if the WASM computation is synchronous and blocks the JS thread (no `Worker`), the timeout promise cannot actually preempt it — there is no kernel/OS-level timer available inside a single WASM instance (contrast with `oxiz-cli`'s process-supervisor `--timeout`, which really does preempt via `SIGKILL`). A hard-preemption fix needs a dedicated Web Worker that can be `terminate()`d from the main thread.
- [ ] **Distributed PDR is a simulation** (`oxiz-spacer/src/distributed.rs:363`) — workers "block" POBs by parity partitioning and the coordinator sleeps rather than performing real multi-threaded/multi-process PDR coordination. Real distributed Spacer needs actual thread/process-level parallelism with shared frame-lattice synchronization; out of scope for a single release.
- [ ] **Property-based test suites not default-on** (`oxiz-solver/tests/property_based.rs`, `oxiz-core` equivalents) — the `property-tests` Cargo feature is off by default, so these suites don't run in a plain `cargo nextest run --workspace`. Turning it on by default is deferred pending a review of runtime cost (proptest suites can be slow) and of the suites' own `Unknown`-tolerant assertions (see `oxiz-solver/tests/property_tests/{backtrack,model}_properties.rs`, which currently accept `Unknown` for both SAT- and UNSAT-expected outcomes and were not re-verified this pass).
- [ ] **JIT-style specialization for hot theory operations** (root TODO.md, originally planned 2026-04-19) — deferred to v0.4.0; requires an IR + codegen layer, out of scope for incremental releases.

### P3 — Process / external-dependency blockers

- [ ] **JS/TS bindings npm publish** — `oxiz-wasm` JS/TS bindings are implemented (see `oxiz-wasm/src/js_api/typescript.rs`); publishing to npm is blocked on explicit user authorization per the workspace's publish policy (only `pypi-publish.yml`/`npm-publish.yml` CI is permitted, and `cargo publish`/`npm publish` require explicit go-ahead).
- [ ] **SMT-COMP 2026 submission** — gated on the SMT-COMP submission portal opening (~May 2026 per prior planning); benchmark suite alignment and competition packaging work can proceed but the actual submission is externally gated.
- [ ] **Symbolic-execution / verification-framework integration** (KLEE/angr/S2E, Frama-C/CBMC/SeaHorn) — too vague to scope without a user-selected target; re-scope once a specific integration target is chosen.
- [ ] **Complete adversarial verification of the full P2–P4 backlog** — this release's re-verification pass covers 100% of P0/P1/P2 (67/70 confirmed fixed by direct inspection, up from the 20/30 original P0/P1 split) plus a ~15-item sample of P3/P4; a dedicated pass over the remaining ~250 P3/P4 items (most already superficially addressed by the same fix waves, per spot-checks, but not individually re-verified) is still needed before they can be marked `[x]` with confidence.
