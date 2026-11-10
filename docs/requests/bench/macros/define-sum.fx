;; => define-sum.fx:5:25: `(sum tag expression)`
;; `sum` is a form's name, yet `(define sum …)` is accepted; a call of it
;; is read as the form, and the refusal shows the form's shape, not that.
(define sum (subr pure ((listof int)) int) (lambda (l) 0))
(write-out (int->string (sum (list 1 2 3))))
