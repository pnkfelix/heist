; lockpick timeout
; found by fuzz_smt.py, seed 22298
(declare-const v1 Bool)
(declare-const v2 Int)
(declare-const v3 Bool)
(declare-const v4 Int)
(declare-const v5 Bool)
(declare-const v6 Int)
(declare-const v7 Int)
(declare-const v8 Int)
(define-fun f9 () Int (+ (* 37 v8) (+ v2 (* v6 (- 6)))))
(assert (= (+ (* (+ v4 v2) (- 10)) v6 f9) (ite v1 (+ v7 (+ v4 v8)) (ite (< v8 v7) v7 (+ (+ v8 v4) (- v7 1) f9)))))
(check-sat)
