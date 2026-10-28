; lockpick timeout
; found by fuzz_smt.py, seed 42435
(declare-const v1 Int)
(declare-const v2 Int)
(declare-const v3 Int)
(declare-const v4 Int)
(define-fun f5 () Int (+ (- (- v2)) (* 2 (- 10)) (+ (mod v4 (- 2)) (- v4) (* 0 v1))))
(assert (= (+ v2 v2 0) (* (- f5 (+ 28 v3 (- v2))) 5)))
(assert (let ((l6 (+ (+ (+ (* v1 7) (+ v2 v1) (* 7 v1)) (* (+ (- 0) 5) 1)) (+ (ite (distinct v3 v1 v3) (- v3 v1) v4) (abs v3) (+ (abs v3) v4))))) (distinct (- (- (+ l6 v3 v4)) (* (* 5 l6) (- 8))) (* (- 3) (- (+ v1 l6 v3))) v3)))
(check-sat)
