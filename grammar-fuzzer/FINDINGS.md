# Findings

Discrepancies found by `oxiz-grammar-fuzzer` (differential testing of oxiz 0.3.0
@ `cc28ee2` against z3 4.16.0), with minimized reproductions in [`cases/`](cases/)
and filed upstream at `cool-japan/oxiz`.

## Run summary

200 cases per logic × 5 logics (1000 total), default config (`--max-depth 3`,
`--max-vars 5`, `--max-asserts 6`, 5 s/case timeout):

| logic   | total | agree | soundness | one-error | inconclusive | timeout |
|---------|------:|------:|----------:|----------:|-------------:|--------:|
| QF_LIA  |   200 |     3 |         0 |         0 |          197 |       0 |
| QF_LRA  |   200 |     2 |         0 |         0 |          198 |       0 |
| QF_BV   |   200 |   114 |        **81** |     0 |            0 |       5 |
| QF_UF   |   199 |   199 |         0 |     **1** |          0  |       0 |
| LIA     |   200 |     4 |         0 |         0 |          194 |       2 |

## Bug #1 — QF_BV soundness (filed as [#17](https://github.com/cool-japan/oxiz/issues/17))

oxiz reports `sat` (with a malformed model `#x-1`) for assertions that are
trivially **unsatisfiable** — strict bit-vector comparisons against a bound no
value can meet, e.g. `(bvult x #b0)` ("x is unsigned-less-than zero") or
`(bvslt x #b10000000)` ("x < −128"). Reproduces at widths 4/8/16/32 and across
the strict signed-comparison family; z3 returns `unsat`.

Root cause (isolated via [`reduce.sh`](reduce.sh)): the always-false strict atoms
are not propagated/constrained, so oxiz defaults to `sat`. This is the bit-vector
analog of the strings bug in [#14](https://github.com/cool-japan/oxiz/issues/14).

| reproducer | z3 | oxiz |
|------------|-----|------|
| [`cases/bv01_bvult_x_zero.smt2`](cases/bv01_bvult_x_zero.smt2) | `unsat` | `sat` (+ model `#x-1`) |
| [`cases/bv02_bvslt_vs_min.smt2`](cases/bv02_bvslt_vs_min.smt2) | `unsat` | `sat` |
| [`cases/bv03_reduced_assertion.smt2`](cases/bv03_reduced_assertion.smt2) | `unsat` | `sat` |

## Bug #2 — QF_UF crash (filed as [#18](https://github.com/cool-japan/oxiz/issues/18))

oxiz **aborts with a stack overflow** (`SIGABRT`, exit 134) on a satisfiable EUF
formula that z3 solves instantly. Suggests unbounded recursion in term traversal
/ congruence closure on nested `f`/`g` applications.

| reproducer | z3 | oxiz |
|------------|-----|------|
| [`cases/uf01_stack_overflow.smt2`](cases/uf01_stack_overflow.smt2) | `sat` | aborted (stack overflow) |

## Non-bugs worth noting

The large `inconclusive` counts for QF_LIA / QF_LRA / LIA are **not**
discrepancies: oxiz returns `unknown` on essentially all of them (honest "I
don't know"), while z3 decides. This indicates oxiz's arithmetic decision
procedures are very incomplete for these instances, but that is not a soundness
violation — the harness correctly treats `unknown` as inconclusive.
