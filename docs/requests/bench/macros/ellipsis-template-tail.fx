;; => `(((string=? v k) e) ... (else d))` is of none of the shapes this
;;    part may have; `string-case`'s signature, inferred, is
;;    `(data data (data data) ...)`
;; The template puts (else d) after an ellipsis, which R7RS allows; the
;; message does not say that is what is wrong.
(define-syntax string-case
  (syntax-rules () ((_ s d (k e) ...) (let ((v s)) (cond ((string=? v k) e) ... (else d))))))
(write-out (string-case "b" "?" ("a" "A") ("b" "B")))
