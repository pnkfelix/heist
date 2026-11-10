;; => a `union`'s members must be told apart by their shapes in the
;;    source; `string-cases`'s signature, inferred, is
;;    `(data ((union (literal else) data) expr) data ...)`
;; `else` is a literal; R7RS tries clauses in order.
(define-syntax-rec
  (string-cases (syntax-rules (else)
                  ((_ v (else d)) d)
                  ((_ v (k e) c ...) (if (string=? v k) e (string-cases v c ...))))))
(write-out (let ((v "b")) (string-cases v ("a" "A") ("b" "B") (else "?"))))
