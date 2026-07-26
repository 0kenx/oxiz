; Minimal QF_BV soundness discrepancy (found by grammar-fuzzer).
; (bvult x #b0) is FALSE for every x (nothing is unsigned-less-than zero),
; so this assertion is UNSATISFIABLE. oxiz incorrectly reports `sat` and a
; malformed model `#x-1`. Reproduces at widths 4/8/16/32.
;
; Expected: unsat   oxiz (bug): sat
(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(assert (bvult x #b00000000))
(check-sat)
(exit)
