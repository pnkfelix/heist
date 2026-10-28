; lockpick timeout
; found by fuzz_smt.py, seed 22050
(declare-const v1 Int)
(declare-const v2 Int)
(declare-const v3 Int)
(declare-const v4 Bool)
(declare-const v5 Bool)
(declare-const v6 Int)
(assert (and (< (+ (+ v1 v2 (* v1 2)) v1) (div (- v3) 7)) true (distinct (+ v3 v6 (* 5 v3)) (* 10 (- v2)) v1)))
(check-sat)
(assert (=> (= (* (* (+ v6 v1 v3) (- 2)) 5) v2) (distinct (+ (+ v6 v6) v3 v3) (ite v4 (+ v2 (+ v2 v3)) v2) (* 10 (ite v4 v1 v6)))))
(check-sat)
