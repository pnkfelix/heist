; lockpick timeout: Gomory cuts with growing coefficients led away from the solution 0, 0, 0
; reduced by hand from fuzz_smt.py --logic QF_LIA, seed 3912
(declare-const v1 Int)(declare-const v3 Int)(declare-const v4 Int)(assert (= (abs v4) (* 39 (* (- 3) (+ v4 (* v1 2) (* v3 3))))))(check-sat)(get-value (v1 v3 v4))
