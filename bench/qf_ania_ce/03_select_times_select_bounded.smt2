;; expected: sat
; product of selects = 6 with bounded indices
(set-logic QF_ANIA)
(declare-const A (Array Int Int))
(declare-const B (Array Int Int))
(declare-const i Int)
(declare-const j Int)
(assert (and (>= i 1) (<= i 3) (>= j 1) (<= j 3)
             (= (* (select A i) (select B j)) 6)))
(check-sat)
