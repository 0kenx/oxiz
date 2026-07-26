# oxiz-grammar-fuzzer

Grammar-driven **differential fuzzer** that compares the `oxiz` SMT solver
against `z3`.

Unlike the existing byte-mutation fuzzers under `fuzz/` (which feed arbitrary
bytes to the parser), this tool generates **well-typed SMT-LIB2 scripts from a
fixed grammar**, runs each one through both `z3` and the `oxiz` CLI as isolated
subprocesses (killed on timeout), and reports every discrepancy. Because the
input is grammar-valid by construction, a **sat/unsat disagreement** is always a
genuine solver soundness bug, never "you fed me garbage".

It is deliberately **decoupled**: it has zero dependencies on any `oxiz-*` crate
and drives both solvers as black-box subprocesses, so it keeps building and
stays reproducible no matter how oxiz's internal API changes. Contrast this with
`bench/z3_parity`, whose generator is smaller (depth 2, 4 logics) and whose
oxiz runner is in-process (and therefore breaks whenever oxiz's library API
drifts).

## The oracle

| z3 | oxiz | classification |
|----|------|----------------|
| sat | sat / unsat / unsat / sat | **`Agree`** / **`SoundnessDisagree`** (headline bug) |
| sat/unsat | error | **`OneError`** (potential parser/crash bug) |
| unknown (either side) | * | `Inconclusive` (honest, not a bug) |
| timeout (either side) | * | `Timeout` (not a bug) |
| error | error | `BothError` (malformed input; shouldn't happen) |

A `SoundnessDisagree` (one solver says `sat`, the other `unsat`) is the only
thing that fails the run (exit code 1).

## Logics

`QF_LIA`, `QF_LRA`, `QF_BV`, `QF_UF`, and quantified `LIA` (`forall`/`exists`).
Arithmetic is kept linear (constant·variable only); `div`/`mod` only ever take a
non-zero numeral divisor; bit-vector scripts use a single fixed width; division
semantics noise (divide-by-zero, Int-vs-Real `div`/`/`) is avoided by
construction. See [`src/grammar.rs`](src/grammar.rs).

Every generated case is a **pure function of `(logic, seed)`** (dependency-free
SplitMix64 PRNG in [`src/rng.rs`](src/rng.rs)), so any discrepancy is
reproducible from its seed alone.

## Quick start

```bash
# 1. build oxiz (the harness shells out to it)
cargo build --release -p oxiz-cli

# 2. run the fuzzer (it is NOT in default-members, so name it explicitly)
cargo run --release -p oxiz-grammar-fuzzer -- --iterations 2000
```

The fuzzer auto-detects `target/release/oxiz`; `z3` must be on `PATH`.

### Options

```
--iterations N     Cases per logic        [default: 1000]
--logics LIST      Comma-separated        [default: QF_LIA,QF_LRA,QF_BV,QF_UF,LIA]
--base-seed N      Starting seed          [default: 0]
--timeout SECS     Per-case budget        [default: 10]
--oxiz PATH        oxiz binary            [default: target/release/oxiz, then PATH]
--z3 PATH          z3 binary              [default: z3]
--outdir DIR       Report directory       [default: grammar-fuzz-report]
--save-all         Dump every script to <outdir>/corpus/
--max-depth N      Formula/term depth     [default: 3]
--max-vars N       Max declared vars      [default: 5]
--max-asserts N    Max assertions         [default: 6]
```

### Output

- `grammar-fuzz-report/report.md` — full per-logic table + every discrepancy with
  its script inline.
- `grammar-fuzz-report/discrepancies/seed-<LOGIC>-<SEED>.smt2` — one reproducer
  per discrepancy (written as soon as it's found, so a mid-run crash never loses
  it).
- `grammar-fuzz-report/corpus/` — all generated scripts (with `--save-all`).
- A concise summary table on stderr, plus exit code `1` if any soundness
  discrepancy was found.

## Reducing a discrepancy

[`reduce.sh`](reduce.sh) delta-debugs a discrepancy file down to a minimal set of
assertions that still reproduces the sat/unsat disagreement:

```bash
./grammar-fuzzer/reduce.sh grammar-fuzz-report/discrepancies/seed-QF_BV-1234.smt2
```

## Reproducing a case

A discrepancy is fully determined by `(logic, seed)`:

```bash
z3 -in < grammar-fuzz-report/discrepancies/seed-QF_BV-1234.smt2
target/release/oxiz --quiet < grammar-fuzz-report/discrepancies/seed-QF_BV-1234.smt2
```

## Committed reproducers

[`cases/`](cases/) holds minimized reproductions for discrepancies already filed
upstream — see [`FINDINGS.md`](FINDINGS.md).

## Tests

```bash
cargo test -p oxiz-grammar-fuzzer
```

Covers PRNG determinism, generator determinism + paren-balance + the
"stays-inside-the-logic" invariants (no var·var in QF_LIA, no Int-only ops in
QF_LRA, no zero divisor in QF_BV), and the verdict classifier.
