; Exact rationals, and how they meet floats.
(define (show . xs) (for-each (lambda (x) (write x) (display " ")) xs) (newline))
(show (/ 1 3) (/ 6 4) (/ -6 4) (/ 4 2) (+ 1/2 1/3) (* 2/3 3/2) (- 1/2) (/ 1/2) (exact->inexact 1/3))
(show 1/2 -3/6 #e1.1 #e1e-3 #e-2.5 #i1/4 (exact 0.5) (exact 0.1) (inexact 7/2))
(show (< 1/3 0.34 1/2) (= 1/2 0.5) (max 1/2 1/3) (min 1/2 0.25) (abs -7/3))
(show (floor 7/2) (ceiling 7/2) (truncate -7/2) (round 7/2) (round 5/2) (round -5/2))
(show (numerator 6/4) (denominator 6/4) (numerator 0.5) (denominator 0.5) (expt 2/3 3) (expt 2 -2) (sqrt 4/9) (sqrt 1/2))
(show (exact? 1/2) (integer? 1/2) (rational? 1/2) (number->string 3/4 2) (string->number "6/8") (eqv? 1/2 2/4) (equal? (list 1/2) (list 2/4)))
(show (exact (expt 10. 20)) (exact->inexact (/ (expt 10 400) (+ (expt 10 399) 1))))
