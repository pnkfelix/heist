;; => `((x a) (y b))` is of none of the shapes this part may have;
;;    `mk`'s signature, inferred, is `(data data)`
;; With `(product (#:x a) (#:y b))` it works; `extract`'s refusal says so
;; ("a tag or label in a template is a keyword: `#:x`, not `x`"), this
;; one does not.
(define-type pt (productof (x int) (y int)))
(define-syntax mk (syntax-rules () ((_ a b) (product (x a) (y b)))))
(write-out (int->string (extract (mk 1 2) y)))
