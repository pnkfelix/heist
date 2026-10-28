;;; linked.fx: combo linked into a program as a library -- its module files
;;; loaded, as combo.fx loads them -- and its solver used on terms directly
;;; (smt.fx's interface), no SMT-LIB2 in between.
(define m-sat (load-module "../sat.fx"))
(define m-rat (load-module "../rat.fx"))
(define m-term ((load-module "../term.fx") m-sat m-rat))
(define m-bv ((load-module "../bv.fx") m-sat m-rat m-term))
(define m-arith ((load-module "../arith.fx") m-sat m-rat m-term))
(define m-eval ((load-module "../eval.fx") m-sat m-rat m-term))
(define m-simplex ((load-module "../simplex.fx") m-sat m-rat))
(define m-blast ((load-module "../blast.fx") m-sat m-rat m-term m-bv m-arith m-eval m-simplex))
(define m-smt ((load-module "../smt.fx") m-sat m-rat m-term m-bv m-arith m-eval m-simplex m-blast))
(import m-sat sat-sat sat-unsat (effect cb-eff))
(import m-rat int->rat rat->string)
(import m-term make-var int-sort bool-sort mk-and2 mk-not)
(import m-bv bv-const mk-bvadd mk-bvult)
(import m-arith num mk-add mk-le mk-ge mk-arith-eq)
(import m-smt make-smt smt-assert! smt-check smt-value smt-push! smt-pop!)

(define* say (subr (io stdout) (string) unit) (lambda (s) (tagcase (write-out s) (done u #u) (failed e #u))))
(define* answer (subr pure (int) string) (lambda (a) (cond ((= a sat-sat) "sat") ((= a sat-unsat) "unsat") (else "unknown"))))

(define main (subr (maxeff cb-eff (io stdout)) () int)
  (lambda ()
    (let* ((c (make-smt))
           (x (make-var "x" int-sort)) (y (make-var "y" int-sort))
           (b (make-var "b" 8)))
      (begin
        ;; x + y = 10, x >= 7, y >= 2
        (smt-assert! c (mk-arith-eq (mk-add (list x y)) (num (int->rat 10) int-sort)))
        (smt-assert! c (mk-ge x (num (int->rat 7) int-sort)))
        (smt-assert! c (mk-ge y (num (int->rat 2) int-sort)))
        (let ((a (smt-check c nil)))
          (say (string-append (answer a) " x=" (rat->string (smt-value c x)) " y=" (rat->string (smt-value c y)) "\n")))
        ;; and, at a level of its own, x <= 7: then y = 3
        (smt-push! c)
        (smt-assert! c (mk-le x (num (int->rat 7) int-sort)))
        (let ((a (smt-check c nil)))
          (say (string-append (answer a) " x=" (rat->string (smt-value c x)) " y=" (rat->string (smt-value c y)) "\n")))
        (smt-pop! c)
        ;; assuming y >= 4, which x >= 7 leaves no room for
        (say (string-append (answer (smt-check c (list (mk-ge y (num (int->rat 4) int-sort))))) "\n"))
        ;; a bitvector: b + 1 < b holds only for b = #xff
        (smt-assert! c (mk-bvult (mk-bvadd b (bv-const 1 8)) b))
        (let ((a (smt-check c nil)))
          (say (string-append (answer a) " b=" (rat->string (smt-value c b)) "\n")))
        0))))
