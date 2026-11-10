;; fixpt run main.fx
;; => `twice` is a macro of this file: one is used where its file is
;;    imported (`import-with-syntax`), not in its file, for now
(define m (load-module "own.fx"))
(import m f)
(write-out (int->string (f 5)))
