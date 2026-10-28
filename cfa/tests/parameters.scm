;;; Parameters: what each holds, its initial value and what parameterize gives it.
(define (inc n) (+ n 1))
(define (dbl n) (* n 2))
(define op (make-parameter inc))
(define a ((op) 1))
(define b (parameterize ((op dbl)) ((op) 2)))
(define limit (make-parameter 10 (lambda (x) (* x 1))))
(define c (+ (limit) 1))
