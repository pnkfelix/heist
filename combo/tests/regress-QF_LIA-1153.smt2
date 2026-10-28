; lockpick timeout
; found by fuzz_smt.py, seed 1153
(declare-const v1 Int)
(declare-const v2 Int)
(assert (= (abs (* 2 (+ v1 v2))) 3))
(check-sat)
