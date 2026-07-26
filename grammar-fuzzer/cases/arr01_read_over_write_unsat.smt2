; QF_AUFLIA (arrays) soundness: a satisfiable read-over-write formula oxiz
; reports `unsat`. z3 returns `sat`.
;
; Expected: sat   oxiz (bug): unsat
(set-logic QF_AUFLIA)
(declare-const a0 (Array Int Int))
(declare-const a1 (Array Int Int))
(declare-const i0 Int)
(declare-const i1 Int)
(declare-const i2 Int)
(assert (not (distinct (select (store a1 (div 7 7) (mod (- 3) (- 5))) (+ 2 i1)) (select (store a0 (ite (<= (mod (abs 7) 2) (- 3)) (- 9) i0) (div i1 8)) (div i2 10)))))
(check-sat)
(exit)
