;;; A program and a library it imports (cfa-test/util.sld, found under the
;;; program's own directory): one world.
(import (scheme base) (cfa-test util))
(define (inc n) (+ n 1))
(define a (apply-twice inc 1))
(define tick (make-counter))
(define b (tick))
