(define-syntax twice (syntax-rules () ((_ e) (let ((x e)) (+ x x)))))
