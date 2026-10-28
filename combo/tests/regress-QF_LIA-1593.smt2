; lockpick timeout
; found by fuzz_smt.py, seed 1593
(declare-const v1 Bool)
(declare-const v2 Int)
(declare-const v3 Bool)
(declare-const v4 Int)
(declare-const v5 Int)
(assert (not (not (= v4 (- v5 v2)))))
(assert (= 1 (+ v5 v2 v4)))
(check-sat)
