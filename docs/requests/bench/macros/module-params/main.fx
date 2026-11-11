;; fixpt run main.fx
;; => the checkers disagree: the Rust checker takes
;;    `%shared:input:user.fx`'s definition, and the one written in FX-26
;;    refuses it: in `user.fx`, 2:36: not an expression in the FX-26 kernel
;;    (5983942d; without the module parameter, `module-own/`, it works)
(define b (load-module "base.fx"))
(define u ((load-module "user.fx") b))
(import u g)
(write-out (int->string (g 4)))
