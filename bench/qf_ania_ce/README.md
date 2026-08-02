# QF_ANIA fixtures

Nonlinear integer products over array `select` (and store-defined arrays).

Solved via **assert-time arithmetic purification** (`solver/purify_arith.rs`):
under `+,-,*,div,mod` and arith comparisons, non-arith numeric subterms
(`select`, UF apps, …) become fresh constants with interface equalities
`c = select(...)`. NIA decides the pure polynomial fragment; array theory
owns store/select structure.

```bash
cargo test -p oxiz-solver --test qf_ania_ce -- --nocapture
```
