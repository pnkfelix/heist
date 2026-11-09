;;; casing.fx: casing's command line. `casing FILE` reads a model and runs
;;; its commands in order, saying what each found. Options, for every
;;; command (a command's own `#:instances` and so on win):
;;;   --instances N   show up to N instances (or counterexamples) of each
;;;   --count         count them all
;;;   --limit N       find no more than N
;;;   --symmetry N    break symmetry with lex-leader predicates N cells long
;;;                   (20 if not said; 0, none) Its module files are
;;; made once, in order, from those before them (as combo/combo.fx makes
;;; combo).
(define m-sat (load-module "../combo/sat.fx"))
(define m-circuit ((load-module "circuit.fx") m-sat))
(define m-matrix ((load-module "matrix.fx") m-sat m-circuit))
(define m-model ((load-module "model.fx") m-sat m-circuit m-matrix))
(import m-sat (effect cb-eff) (type strings))
(import m-model read-model run-model-with default-settings with-instances with-count with-limit with-symmetry (type datums) (type settings))

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

"A whole number written in decimal, or -1."
(define* whole (subr spin (string) int)
  (lambda (s)
    (letrec ((go (subr spin (int int) int)
               (lambda (i acc)
                 (if (>= i (string-length s)) acc
                     (let ((d (- (char->integer (string-ref s i)) 48)))
                       (if (and (>= d 0) (<= d 9)) (go (+ i 1) (+ (* acc 10) d)) -1))))))
      (if (= (string-length s) 0) -1 (go 0 0)))))

"The command line: its settings and its one file, or why not."
(define-type invocation (productof (settings settings) (file string) (bad string)))
(define* invoked (subr (maxeff spin (read @a) (read @globals)) ((listof string @a)) invocation)
  (lambda (as)
    (letrec ((go (subr (maxeff spin (read @a) (read @globals)) ((listof string @a) settings string) invocation)
               (lambda (l s file)
                 (let ((bad (lambda ((why string)) (product (settings s) (file file) (bad why)))))
                   (cond ((null? l) (if (string=? file "") (bad "no model named") (product (settings s) (file file) (bad ""))))
                         ((string=? (car l) "--count") (go (cdr l) (with-count s) file))
                         ((or (string=? (car l) "--instances") (string=? (car l) "--symmetry") (string=? (car l) "--limit"))
                          (if (null? (cdr l)) (bad (string-append (car l) " needs a number"))
                              (let ((n (whole (car (cdr l)))))
                                (cond ((< n 0) (bad (string-append (car l) " needs a whole number")))
                                      ((string=? (car l) "--instances") (go (cdr (cdr l)) (with-instances s n) file))
                                      ((string=? (car l) "--limit") (go (cdr (cdr l)) (with-limit s n) file))
                                      (else (go (cdr (cdr l)) (with-symmetry s n) file))))))
                         ((and (> (string-length (car l)) 1) (char=? (string-ref (car l) 0) #\-))
                          (bad (string-append "what option is this? " (car l))))
                         ((not (string=? file "")) (bad "one model at a time"))
                         (else (go (cdr l) s (car l))))))))
      (go as default-settings ""))))

(define* main (subr main-eff () int)
  (lambda ()
    (let ((inv (invoked (the (listof string @a) (args)))))
      (if (not (string=? (extract inv bad) ""))
          (begin (say-err (string-append "casing: " (string-append (extract inv bad)
                            "\nusage: casing [--instances N] [--count] [--limit N] [--symmetry N] FILE\n"))) 2)
          (tagcase (read-forms (extract inv file))
            (failed why (begin (say-err (string-append why "\n")) 1))
            (forms ds
              (begin
                (letrec ((go (subr main-eff (strings) unit)
                           (lambda (l) (if (null? l) #u (begin (say (string-append (car l) "\n")) (go (cdr l)))))))
                  (go (run-model-with (read-model ds) (extract inv settings))))
                0)))))))
