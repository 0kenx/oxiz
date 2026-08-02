;; expected: sat
; Nullary define-fun whose body is a product of two array-selects.
; Controls: inline product (no define-fun) and nullary define-fun over
; select*const both succeed; this combination previously returned unknown.
(set-logic QF_ANIA)
(declare-const i Int)
(declare-const A (Array Int Int))
(declare-const B (Array Int Int))
(assert (= A (store ((as const (Array Int Int)) 0) 1 3)))
(assert (= B (store ((as const (Array Int Int)) 0) 1 2)))
(define-fun P () Int (* (select A i) (select B i)))
(assert (and (>= i 1) (<= i 1) (= P 6)))
(check-sat)
