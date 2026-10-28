; A library in a file of its own, for libraries.scm to import.
(define-library (geometry point)
  (export make-point point-x point-y (rename distance-squared dist2) origin swap-coords!)
  (import (scheme base))
  (begin
    (define-record-type point (make-point x y) point? (x point-x set-x!) (y point-y set-y!))
    (define (square n) (* n n))
    (define (distance-squared a b)
      (+ (square (- (point-x a) (point-x b))) (square (- (point-y a) (point-y b)))))
    (define origin (make-point 0 0))
    ;; A macro that uses a name the library does not export.
    (define-syntax swap-coords!
      (syntax-rules () ((_ p) (let ((t (point-x p))) (set-x! p (point-y p)) (set-y! p t)))))))
