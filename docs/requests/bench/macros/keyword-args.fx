;; fixpt run keyword-args.fx
;; => on eed406e0: a use of `loop`: `((fields int 3))` is of none of the
;;    shapes this part may have. Each `(define …)` below is refused alone
;;    (comment out the others to see each): a keyword is taken as the
;;    loop's name (`keyword-names.fx` prints 10), and inside a part's list,
;;    `(+ 0 fields)`, but not as a binder in the pattern's list, `x` of
;;    `((x t i) ...)`, nor alone as an expression, as `i` or as `when`'s
;;    `c`: `fields` is a form's name, not an expression. The code each
;;    stands for binds and uses `fields` (`plain`). Heist's rewrite leaves
;;    such uses alone; the CFA, ratfink and casing have loops that pass
;;    `fields` or bind `region`.
(define-syntax loop
  (syntax-rules ()
    ((_ go eff ((x t i) ...) r body) (letrec ((go (subr eff (t ...) r) (lambda (x ...) body))) (go i ...)))))
(define-syntax when (syntax-rules () ((_ c e ...) (if c (begin e ...) 0))))
(define plain (letrec ((go (subr spin (int) int) (lambda (fields) fields))) (go 3)))
(define as-binder (loop go spin ((fields int 3)) int fields))
(define as-init (let ((fields 3)) (loop go spin ((a int fields)) int a)))
(define as-test (let ((fields #t)) (when fields 1)))
(write-out (int->string (+ plain as-binder as-init as-test)))
