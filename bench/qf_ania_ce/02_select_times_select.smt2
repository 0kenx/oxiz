;; expected: sat
; (select A i) * (select B j) = 6
(set-logic QF_ANIA)
(declare-const A (Array Int Int))
(declare-const B (Array Int Int))
(declare-const i Int)
(declare-const j Int)
(assert (= (* (select A i) (select B j)) 6))
(check-sat)
