(module-parameters ((m-base (load-moduleof "base.fx"))))
(define-syntax twice (syntax-rules () ((_ e) (let ((x e)) (+ x x)))))
(define g (subr pure (int) int) (lambda (n) (twice (+ n one))))
