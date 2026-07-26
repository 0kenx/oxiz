# Findings

Discrepancies found by `oxiz-grammar-fuzzer` (differential testing of oxiz
against z3 4.16.0), with minimized reproductions in [`cases/`](cases/) and
filed upstream at `cool-japan/oxiz`.

> The fuzzer generates **grammar-valid SMT-LIB2** for 9 logics and, beyond
> sat/unsat parity, runs a **model-validity oracle**: whenever oxiz reports
> `sat` over a scalar-valued logic, it queries oxiz's `get-value` model,
> grounds the assertions against that assignment, and asks z3 whether the
> conjunction still holds. A model z3 calls unsatisfiable (or can't even
> parse — e.g. the malformed `#x-1`) is flagged as an **InvalidModel**
> discrepancy.

## Run against the fixed build (oxiz @ `8e930b3`)

200 cases per logic × 9 logics = 1800 cases (timeout 4 s/case):

| logic      | total | agree | soundness | invalid-model | one-error | inconclusive | timeout |
|------------|------:|------:|----------:|--------------:|----------:|-------------:|--------:|
| QF_LIA     |   200 |     3 |         0 |             0 |         0 |          197 |       0 |
| QF_LRA     |   200 |     2 |         0 |             0 |         0 |          198 |       0 |
| QF_NIA     |   200 |     5 |         0 |             0 |         0 |          195 |       0 |
| QF_NRA     |   200 |     2 |         0 |             0 |         0 |          198 |       0 |
| QF_BV      |   200 |   138 |        **59** |          0 |         0 |            0 |       3 |
| QF_UF      |   200 |   200 |         0 |             0 |         0 |            0 |       0 |
| QF_AUFLIA  |   200 |    61 |        **3**  |          0 |         0 |          127 |       9 |
| QF_S       |   200 |    10 |        **1**  |          0 |         0 |          188 |       1 |
| LIA        |   200 |     2 |         0 |             0 |         0 |          196 |       2 |

## Bug status

| # | theory | status | reproducer |
|---|--------|--------|-----------|
| [#17](https://github.com/cool-japan/oxiz/issues/17) | QF_BV | **fix incomplete** — strict-bounds patch handles only bare `(bvslt var min)`, not compound LHS | [`cases/bv01`](cases/bv01_bvult_x_zero.smt2) [`cases/bv02`](cases/bv02_bvslt_vs_min.smt2) [`cases/bv03`](cases/bv03_reduced_assertion.smt2) [`cases/bv04`](cases/bv04_compound_lhs_strict.smt2) |
| [#18](https://github.com/cool-japan/oxiz/issues/18) | QF_UF | **fixed** ✓ — 200/200 now agree, no crashes | [`cases/uf01`](cases/uf01_stack_overflow.smt2) |
| [#22](https://github.com/cool-japan/oxiz/issues/22) | QF_AUFLIA | **open** — `unsat` for a satisfiable read-over-write formula (indices become arithmetic compounds) | [`cases/arr01`](cases/arr01_read_over_write_unsat.smt2) |
| [#23](https://github.com/cool-japan/oxiz/issues/23) | QF_S | **open** — `unsat` for a trivially-true implication (false premise via out-of-range `str.substr`) | [`cases/str01`](cases/str01_false_premise_implication.smt2) |

### #17 — QF_BV strict bounds (fix incomplete)

After `ef3f985`, `(bvslt x #b10000000)` correctly returns `unsat`, but any
arithmetic left-hand side still returns spurious `sat`:

| assertion | z3 | oxiz |
|-----------|-----|------|
| [`cases/bv04`](cases/bv04_compound_lhs_strict.smt2) `(bvslt (bvadd x1 x3) #b10000000)` | `unsat` | `sat` |
| `(bvslt (bvand (bvudiv x1 #b11110110) x3) #b10000000)` | `unsat` | `sat` |

### #22 — QF_AUFLIA arrays (new)

`z3=sat`, `oxiz=unsat`. The bare read-over-write axioms are handled; divergence
appears once the index/value position becomes an arithmetic compound (`div`,
`mod`, `abs`, `ite`), so the array theory seems not to propagate read-over-write
when the `(= i j)` test is non-trivial.

### #23 — QF_S strings (new, distinct from #14)

`z3=sat`, `oxiz=unsat` on an implication whose premise is provably false (and
thus vacuously true). oxiz evaluates `(str.substr "aba" 3 1)` correctly in
isolation, so the bug is in implication/`str.++`/`distinct` reasoning, not the
substring evaluator.

## Non-bugs worth noting

- The large `inconclusive` counts for the arithmetic logics (QF_LIA/LRA/NIA/NRA
  and quantified LIA) are **not** discrepancies: oxiz returns `unknown` on
  essentially all of them while z3 decides — honest incompleteness, not
  unsoundness. The harness treats `unknown` as inconclusive.
- `invalid-model = 0` across the run: in every case where oxiz said `sat` and
  z3 agreed (or was unknown), oxiz's grounded model was confirmed by z3. (The
  sat/unsat-disagree cases are caught as `SoundnessDisagree` before the model
  check surfaces, so an invalid model there is already implied.)
