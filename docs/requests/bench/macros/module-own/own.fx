(define-syntax twice (syntax-rules () ((_ e) (let ((x e)) (+ x x)))))
(define f (subr pure (int) int) (lambda (n) (twice n)))
