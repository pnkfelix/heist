;; Integers. Arithmetic is exact: nothing wraps and nothing overflows. Int's
;; atoms are -8 … 7 (bitwidth 4, the default), but an expression's value
;; may be any integer; only an Int atom must be in range. +%, -%, *% and
;; neg% wrap to the bitwidth, and only they.
(assert succ (all ((i Int)) (> (+ i 1) i)))
(check succ)
(assert succ-wrapping (all ((i Int)) (> (+% i 1) i)))
(check succ-wrapping)
;; 7 + 1 is 8, which no atom is: as a set, it is none
(assert no-atom (and (= (+ 7 1) 8) (no (+ 7 1)) (= (+ 6 1) (int 7))))
(check no-atom)

(assert arith (and (= (* 6 7) 42) (= (- 3 5) -2) (= (neg -8) 8)
                   (= (div -7 2) -3) (= (rem -7 2) -1) (= (mod -7 2) 1)
                   (= (*% 6 7) -6) (= (neg% -8) -8)))
(check arith)
(assert divides (all ((a b Int)) (implies (!= b 0) (= a (+ (* (div a b) b) (rem a b))))))
(check divides (Int 3))
(assert mod-range (all ((a b Int)) (implies (!= b 0) (and (<= 0 (mod a b)) (< (mod a b) (if (< b 0) (neg b) b))))))
(check mod-range (Int 3))
;; dividing by 0 gives whatever the solver picks: a model that relies on
;; its value has a counterexample that shows it
(assert by-zero (= (div 1 0) 0))
(check by-zero)

;; fields of Int, and sums, which may pass 7
(sig Item (price Int))
(run (> (sum ((t Item)) (join t price)) 20) (exactly Item 3))
(assert sum-nonneg (implies (all ((t Item)) (>= (join t price) 0)) (>= (sum ((t Item)) (join t price)) 0)))
(check sum-nonneg)
;; a set's integer is the sum of its Int atoms (Alloy's int[e])
(assert prices (= (int (join Item price)) (sum ((p (join Item price))) p)))
(check prices)
