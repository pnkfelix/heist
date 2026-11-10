;; fixpt run main.fx
;; => in `user.fx`, 2:2: unbound variable `import-with-syntax`
(define m (load-module "user.fx"))
(import m g)
(write-out (int->string (g 5)))
