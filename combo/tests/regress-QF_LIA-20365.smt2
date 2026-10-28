; lockpick timeout
; found by fuzz_smt.py, seed 20365
(declare-const v1 Int)
(declare-const v2 Bool)
(declare-const v3 Int)
(declare-const v4 Int)
(declare-const v5 Int)
(declare-const v6 Bool)
(declare-const v7 Int)
(declare-const v8 Bool)
(assert (= (ite (= v4 v5) (+ (+ v3 v5 7) (ite v8 v4 (ite v6 v1 v4)) (abs (* v4 5))) (* (- 3) (- 10))) (+ v1 (* 10 (- (ite v8 v1 v7)))) (* 7 (+ (+ v3 (* (- 1) v4)) (+ (+ v4 v5) v3 (+ v7 v3)) (mod (abs v1) 3)))))
(assert (> (ite (= (- v7 v7) (+ v7 v3)) 5 (div v7 (- 2))) v7))
(check-sat)
