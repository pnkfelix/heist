;;; Small procedures are called in a context of their call site: what
;;; each context sees, where they differ (bin/cfa --contexts).
;;; options: --contexts
(define (inc n) (+ n 1))
(define (dbl n) (* n 2))
(define (twice f x) (f (f x)))
(define a (twice inc 1))
(define b (twice dbl 2))
(define (wrap g) (lambda (y) (g y)))
(define c ((wrap inc) 3))
(define d ((wrap dbl) 4))
