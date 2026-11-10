;; => `(tag v body)` could be of more than one of this part's shapes;
;;    `sw`'s signature, inferred, is `(data (data data data) ...)`
;; A macro cannot pass its use's tagcase clauses through.
(define-syntax sw (syntax-rules () ((_ e (tag v body) ...) (tagcase e (tag v body) ...))))
(write-out (sw (write-out "") (done u "d") (failed e "f")))
