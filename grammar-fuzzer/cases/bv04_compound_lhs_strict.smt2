; QF_BV soundness STILL present after the strict-bounds fix (#17).
; `(bvslt (bvadd x1 x3) #b10000000)` is "compound < signed-min", which is
; impossible (nothing is below -128) -> UNSAT. The fix only handled the bare
; `(bvslt var min)` case; any arithmetic LHS still returns sat.
;
; Expected: unsat   oxiz (bug): sat
(set-logic QF_BV)
(declare-const x1 (_ BitVec 8))
(declare-const x3 (_ BitVec 8))
(assert (bvslt (bvadd x1 x3) #b10000000))
(check-sat)
(exit)
