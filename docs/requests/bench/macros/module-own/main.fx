;; fixpt run main.fx
;; => 10 (since Fixpt 5983942d; on 07b0d743: `twice` is a macro of this
;;    file: one is used where its file is imported (`import-with-syntax`),
;;    not in its file, for now)
(define m (load-module "own.fx"))
(import m f)
(write-out (int->string (f 5)))
