;;; ratfink.fx: the ratfink program, each file made once, in order, from
;;; those before it (as combo/combo.fx makes combo).
(define m-core ((load-module "core.fx")))
(define m-term ((load-module "term.fx") m-core))
(define m-value ((load-module "value.fx") m-core m-term))
(define m-print ((load-module "print.fx") m-core))
(define m-syntax ((load-module "syntax.fx") m-core m-print))
(define m-numbers ((load-module "numbers.fx") m-core))
(define m-reader ((load-module "reader.fx") m-core m-numbers))
(define m-machine ((load-module "machine.fx") m-core m-term m-value))
(define m-prims ((load-module "prims.fx") m-core m-term m-value m-print m-syntax m-numbers m-reader m-machine))
