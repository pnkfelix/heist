(define lib (load-module "lib.fx"))
(import-with-syntax lib)
(define g (subr pure (int) int) (lambda (n) (twice n)))
