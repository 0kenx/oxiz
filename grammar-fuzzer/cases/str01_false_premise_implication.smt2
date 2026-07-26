; QF_S soundness: an implication whose premise is provably false is trivially
; TRUE, so the assertion is satisfiable. `(str.substr "aba" 3 1)` is
; out-of-range -> "" (SMT-LIB), hence `(str.++ "" "bb")` = "bb" != "".
; oxiz reports `unsat`.
;
; Expected: sat   oxiz (bug): unsat
(set-logic QF_S)
(declare-const s0 String)
(assert (=> (= (str.++ (str.substr "aba" 3 1) "bb") "") (distinct "b" (str.++ s0 "b"))))
(check-sat)
(exit)
