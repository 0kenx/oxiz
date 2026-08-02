;; expected: sat
; (select A i) * 2 = 10
(set-logic QF_ANIA)
(declare-const A (Array Int Int))
(declare-const i Int)
(assert (= (* (select A i) 2) 10))
(check-sat)
