;;; From editor/tests/flow-test.fx: which lambdas reach which calls,
;;; through parameters, fields, refs and sums; and `apply`, its list's
;;; elements given.
(define twice (lambda (f x) (f (f x))))
(define inc (lambda (n) (+ n 1)))
(define dbl (lambda (n) (* n 2)))
(twice inc 1)
(define table (product (op dbl)))
((extract table op) 5)
(define r (new inc))
((get r) 3)
(tagcase (sum some dbl) (some g (g 1)) (else y 0))
(define esc (lambda (k) (k 0)))
(apply esc (list 1))
