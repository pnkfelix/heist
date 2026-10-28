;;; A library for linked.scm: its world has this too.
(define-library (cfa-test util)
  (import (scheme base))
  (export apply-twice make-counter)
  (begin
    (define (apply-twice f x) (f (f x)))
    (define (make-counter) (let ((n 0)) (lambda () (set! n (+ n 1)) n)))))
