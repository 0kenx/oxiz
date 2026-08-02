;; expected: unsat
; Store-defined A,B; i,j in {1,2}; (select A i)*(select B j)=7 has no model
; (possible products: 6,8,9,12). Regression: pure-arith relaxation is sat.
(set-logic QF_ANIA)
(declare-const i Int)
(declare-const j Int)
(declare-const A (Array Int Int))
(declare-const B (Array Int Int))
(assert (= A (store (store ((as const (Array Int Int)) 0) 1 3) 2 4)))
(assert (= B (store (store ((as const (Array Int Int)) 0) 1 2) 2 3)))
(assert (and (>= i 1) (<= i 2) (>= j 1) (<= j 2)
             (= (* (select A i) (select B j)) 7)))
(check-sat)
