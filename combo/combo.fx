;;; combo.fx: the combo program, each file made once, in order, from those
;;; before it (as editor/editor.fx makes the editor). Another program
;;; links combo in by loading its files so too.
(define m-sat (load-module "sat.fx"))
(define m-dimacs ((load-module "dimacs.fx") m-sat))
(define m-main ((load-module "main.fx") m-sat m-dimacs))
(define main (with m-main main))
