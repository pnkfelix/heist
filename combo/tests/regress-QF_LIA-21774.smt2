; lockpick timeout
; found by fuzz_smt.py, seed 21774
(declare-const v1 Int)
(declare-const v2 Int)
(declare-const v3 Int)
(define-fun f4 ((a5 Int) (a6 Int)) Bool (= (>= a5 (let ((l7 v2)) v2) (+ v3 v1 v3)) (ite (let ((l8 false)) false) (>= v1 a5) (> v3 v1)) (<= (- a6 a5) (let ((l9 a5)) a5))))
(assert (> (- (* v1 14)) v2))
(assert (f4 (+ v3 (div v1 7) 39) 1))
(assert (= (div (* (+ (+ v3 5 v2) (let ((l11 v1)) l11)) 7) (- 2)) (let ((l12 (+ (- (div v3 3) (abs (- 10))) (- v3) (- 10)))) (+ (div l12 7) (- (div l12 2) (ite true v1 l12)) (- (+ l12 v2))))))
(check-sat)
