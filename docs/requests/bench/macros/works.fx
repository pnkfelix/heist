;; => 6 B first=5 -=2
;; What works today, in a program: a typed loop (effects and types pass
;; through), `when`, a string case with its signature written, and a
;; family of registrations built on another macro.
(define-syntax when (syntax-rules () ((_ c e ...) (if c (begin e ...) #u))))
(define-syntax loop
  (syntax-rules ()
    ((_ go eff ((x t i) ...) r body) (letrec ((go (subr eff (t ...) r) (lambda (x ...) body))) (go i ...)))))
(define-syntax-rec
  (string-cases ((many expr) expr (expr expr) ...)
    (syntax-rules ()
      ((_ v d) d)
      ((_ v d (k e) c ...) (if (string=? v k) e (string-cases v d c ...))))))
(define-syntax string-case (syntax-rules () ((_ s d c ...) (let ((v s)) (string-cases v d c ...)))))
(define-type vals (listof int acyclic))
(define* reg! (subr (io stdout) (string int int (subr pure (vals) int)) unit)
  (lambda (n lo hi f) (tagcase (write-out (string-append " " n "=" (int->string (f (list 5 3))))) (done u #u) (failed e #u))))
(define-syntax prim (syntax-rules () ((_ name lo hi (a) body) (reg! name lo hi (lambda ((a vals)) body)))))
(define-syntax prim-binop (syntax-rules () ((_ name op) (prim name 2 2 (a) (op (car a) (car (cdr a)))))))
(define total (subr (maxeff spin (read @a)) ((listof int @a)) int)
  (lambda (l) (loop go (maxeff spin (read @a)) ((l (listof int @a) l) (acc int 0)) int
                (if (null? l) acc (go (cdr l) (+ acc (car l)))))))
(when #t (write-out (int->string (total (list 1 2 3)))) #u)
(write-out (string-append " " (string-case "b" "?" ("a" "A") ("b" "B"))))
(prim "first" 1 1 (args) (car args))
(prim-binop "-" -)
