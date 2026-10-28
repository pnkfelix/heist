; lockpick timeout
; found by fuzz_smt.py, seed 22852
(declare-const v1 Int)
(declare-const v2 Int)
(declare-const v3 Int)
(declare-const v4 Bool)
(declare-const v5 Int)
(declare-const v6 Int)
(declare-const v7 Bool)
(declare-const v8 Int)
(define-fun f9 ((a10 Int) (a11 Int)) Bool (= (* 4 (+ v2 a10 a11)) (- (* (- 32) a10) (mod a11 3)) (abs (ite v7 a11 v5))))
(assert (= (= 5 v8) (f9 (* v2 (- 34)) (* (- 2) v8))))
(check-sat)
