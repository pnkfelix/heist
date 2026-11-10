;; fixpt run main.fx
;; => in `uses.fx`, 1:46: unbound variable `twice`
(define-syntax twice (syntax-rules () ((_ e) (let ((x e)) (+ x x)))))
(define m (load-module "uses.fx"))
(import m f)
(write-out (int->string (f 5)))
