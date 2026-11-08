;;; casing.fx: casing's command line. `casing FILE` reads a model and runs
;;; its commands in order, saying what each found. Its module files are
;;; made once, in order, from those before them (as combo/combo.fx makes
;;; combo).
(define m-sat (load-module "../combo/sat.fx"))
(define m-circuit ((load-module "circuit.fx") m-sat))
(define m-matrix ((load-module "matrix.fx") m-sat m-circuit))
(define m-model ((load-module "model.fx") m-sat m-circuit m-matrix))
(import m-sat (effect cb-eff) (type strings))
(import m-model read-model run-model (type datums))

"Fixpt's own reader of FX-26, which keeps its state in its regions and
leaves a form it cannot read by an escape."
(define fx-reader ((proj (load-module "fx26:eager-reader.fx") @s @e @m @c)))
(import fx-reader eager-start-fx26 eager-feed-string eager-feed eager-status eager-state-message eager-state-data)
(define-effect reader-eff
  (maxeff (read @s) (write @s) (alloc @s) (read @m) (write @m) (alloc @m)
          (read @c) (write @c) (alloc @c) (read @e) (goto @e) (comefrom @e)))
(define-effect main-eff (maxeff cb-eff reader-eff (io stdout) (io stderr) (io fs-read) (io args) (alloc @a) (read @a)))

(define* say (subr (io stdout) (string) unit) (lambda (s) (tagcase (write-out s) (done u #u) (failed e #u))))
(define* say-err (subr (io stderr) (string) unit) (lambda (s) (tagcase (write-err s) (done u #u) (failed e #u))))

"A file's forms, or why they could not be read."
(define* read-forms (subr main-eff (string) (sumof (forms datums) (failed string)))
  (lambda (file)
    (tagcase (the (sumof (data (bytevectorof @cb)) (failed io-error)) (read-file file))
      (failed e (sum failed (string-append "casing: cannot read " file)))
      (data b
        (tagcase (utf8->string b)
          (bad k (sum failed (string-append "casing: not UTF-8: " file)))
          (text t
            (let ((st (eager-feed (eager-feed-string (eager-start-fx26) t) #\newline)))
              (case (eager-status st)
                ((complete)
                 (sum forms (letrec ((go (subr spin ((listof datum acyclic)) datums)
                                           (lambda (l) (if (null? l) nil (cons (car l) (go (cdr l)))))))
                              (go (eager-state-data st)))))
                ((error) (sum failed (string-append file (string-append ": " (eager-state-message st)))))
                (else (sum failed (string-append file ": a form is not closed")))))))))))

(define* main (subr main-eff () int)
  (lambda ()
    (let ((as (the (listof string @a) (args))))
      (if (or (null? as) (pair? (cdr as))) (begin (say-err "usage: casing FILE\n") 2)
          (tagcase (read-forms (car as))
            (failed why (begin (say-err (string-append why "\n")) 1))
            (forms ds
              (begin
                (letrec ((go (subr main-eff (strings) unit)
                           (lambda (l) (if (null? l) #u (begin (say (string-append (car l) "\n")) (go (cdr l)))))))
                  (go (run-model (read-model ds))))
                0)))))))
