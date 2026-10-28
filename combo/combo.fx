;;; combo.fx: the combo program, each file made once, in order, from those
;;; before it (as editor/editor.fx makes the editor). A program that links
;;; combo in loads the files it needs so too: through smt.fx for the solver
;;; on terms, through smtlib.fx for SMT-LIB2 sessions.
(define m-sat (load-module "sat.fx"))
(define m-rat (load-module "rat.fx"))
(define m-dimacs ((load-module "dimacs.fx") m-sat))
(define m-elim ((load-module "elim.fx") m-sat))
(define m-term ((load-module "term.fx") m-sat m-rat))
(define m-bv ((load-module "bv.fx") m-sat m-rat m-term))
(define m-arith ((load-module "arith.fx") m-sat m-rat m-term))
(define m-eval ((load-module "eval.fx") m-sat m-rat m-term))
(define m-simplex ((load-module "simplex.fx") m-sat m-rat))
(define m-blast ((load-module "blast.fx") m-sat m-rat m-term m-bv m-arith m-eval m-simplex))
(define m-sexp ((load-module "sexp.fx") m-sat m-rat))
(define m-smt ((load-module "smt.fx") m-sat m-rat m-term m-bv m-arith m-eval m-simplex m-blast))
(define m-smtlib ((load-module "smtlib.fx") m-sat m-rat m-term m-bv m-arith m-eval m-simplex m-blast m-sexp m-smt))
(define m-serve ((load-module "serve.fx") m-sat m-rat m-term m-bv m-arith m-eval m-simplex m-blast m-sexp m-smt m-smtlib))
(define m-main ((load-module "main.fx") m-sat m-rat m-dimacs m-elim m-term m-bv m-arith m-eval m-simplex m-blast m-sexp m-smt m-smtlib m-serve))
(define main (with m-main main))
