; Reduced (via grammar-fuzzer/reduce.sh) from a fuzzer-generated QF_BV case.
; z3=unsat, oxiz=sat. Conjunct (bvslt (bvand (bvudiv x1 #b11110110) x3) #b10000000)
; alone reproduces (see bv02 for the principle).
(set-logic QF_BV)
(declare-const x0 (_ BitVec 8))
(declare-const x1 (_ BitVec 8))
(declare-const x2 (_ BitVec 8))
(declare-const x3 (_ BitVec 8))
(assert (and (bvslt (bvand (bvudiv x1 #b11110110) x3) #b10000000) (xor (bvsle (bvadd #b11010011 x2) (bvand x3 #b01001000)) (bvugt #b01101110 x2))))
(check-sat)
(exit)
