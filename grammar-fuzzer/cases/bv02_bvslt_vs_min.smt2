; QF_BV: (bvslt x #b10000000) means "x < -128" (signed), which is impossible
; -> UNSAT. oxiz reports `sat`.
;
; Expected: unsat   oxiz (bug): sat
(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(assert (bvslt x #b10000000))
(check-sat)
(exit)
