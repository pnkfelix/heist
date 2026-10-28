; lockpick timeout: parity behind an ite (68 v2 + 77 = v1 + |v1|), before the integer equality solver
; found by fuzz_smt.py --logic QF_LIA, seed 5208
(set-logic QF_LIA)
(declare-const v1 Int)
(declare-const v2 Int)
(assert (xor (not (= (let ((l3 v2)) v2) (+ (* 2 (- 2)) (let ((l4 v2)) l4)))) (distinct (ite false (- (- v2) (+ v2 v1)) (* 35 (+ v2 2 v2))) (+ (+ v2 (+ v2 v2 v1)) (+ (- v2) (- v1 7)) (+ (abs v1) (- v1))))))
(assert (or (> (+ v2 v2 v1) (* (- 1) v2))))
(assert (ite (or true) true (= (- v1 0) (+ v1 v2 v1))))
(check-sat)
