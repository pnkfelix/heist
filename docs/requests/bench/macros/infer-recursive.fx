;; => a `mu`'s variable is used where no pair is around it (Herman's
;;    types are contractive); `string-cases`'s signature, inferred, is
;;    `((many expr) expr (mu m1 (union (expr expr) m1)) ...)`
;; Written, `((many expr) expr (expr expr) ...)` works (=> "B").
(define-syntax-rec
  (string-cases (syntax-rules ()
                  ((_ v d) d)
                  ((_ v d (k e) c ...) (if (string=? v k) e (string-cases v d c ...))))))
(define-syntax string-case (syntax-rules () ((_ s d c ...) (let ((v s)) (string-cases v d c ...)))))
(write-out (string-case "b" "?" ("a" "A") ("b" "B")))
