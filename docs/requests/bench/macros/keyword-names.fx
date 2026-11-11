;; fixpt run keyword-names.fx
;; => 10 on eed406e0. On 5983942d: a use of `loop`: `fields` is not a
;;    name that may be bound. `fields` is an FX-26 keyword (bloblets'), but the
;;    `letrec` the macro stands for binds it, as `plain` shows; as a loop's
;;    first value, `((l strings fields))`, it is refused too: `is of none
;;    of the shapes this part may have`; still so on eed406e0
;;    (`keyword-args.fx`).
(define-syntax loop
  (syntax-rules ()
    ((_ go eff ((x t i) ...) r body) (letrec ((go (subr eff (t ...) r) (lambda (x ...) body))) (go i ...)))))
(define plain (subr spin (int) int)
  (lambda (n) (letrec ((fields (subr spin (int int) int) (lambda (i a) (if (= i 0) a (fields (- i 1) (+ a i)))))) (fields n 0))))
(define looped (subr spin (int) int)
  (lambda (n) (loop fields spin ((i int n) (a int 0)) int (if (= i 0) a (fields (- i 1) (+ a i))))))
(write-out (int->string (looped 4)))
