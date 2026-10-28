;;; A field some store writes is not narrowed: a call between the test and
;;; the use could change it.
(define (inc n) (+ n 1))
(define (first-proc x) (if (procedure? (car x)) ((car x) 1) 0))
(define g (first-proc (list inc)))
(define h (first-proc (list 2)))
(define (clobber! x) (set-car! x 3))
