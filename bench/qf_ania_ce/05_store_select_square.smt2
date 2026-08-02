;; expected: sat
; Constant array via store; (select A 1)^2 = 9
(set-logic QF_ANIA)
(declare-const A (Array Int Int))
(assert (= A (store ((as const (Array Int Int)) 0) 1 3)))
(assert (= (* (select A 1) (select A 1)) 9))
(check-sat)
