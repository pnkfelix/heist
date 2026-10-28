; A syntax error is reported where it is, before its form runs.
(display "ran")
(newline)
(define (f x)
  (let ((y))
    (if x)))
(display "never")
