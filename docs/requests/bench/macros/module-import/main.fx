;; fixpt run main.fx
;; => on eed406e0, refused: in `user.fx`, 2:1: `import-with-syntax` in a
;;    module file: not yet (request item 1(b)); on 5983942d, a panic: parse.rs:1971:21: index out of bounds: the len
;;    is 0 but the index is 0 (with or without a use of `twice`); on
;;    07b0d743: in `user.fx`, 2:2: unbound variable `import-with-syntax`
(define m (load-module "user.fx"))
(import m g)
(write-out (int->string (g 5)))
