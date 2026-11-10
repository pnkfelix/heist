(define-type (nestof (l type)) (mu n (listof (oneof l n) acyclic)))
(define-type atom (oneof int f64 char bool string symbol keyword))
(define* depth (poly ((l type)) (subr spin ((nestof l)) int)) (lambda (n) 0))
(write-out (int->string ((inst depth atom) (list 1 (list 2 3)))))
