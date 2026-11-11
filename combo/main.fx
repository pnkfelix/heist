;;; main.fx: the combo program (`bin/combo`), as lockpick's `(lockpick main)`:
;;;   combo --dimacs FILE [--proof PROOF] [--stats] [--no-elim]
;;;                                   solve a CNF, after eliminating variables
;;;                                   (elim.fx) unless --no-elim; write a DRAT
;;;                                   proof; exits with status 10 for
;;;                                   satisfiable, 20 for unsatisfiable (as
;;;                                   SAT solvers do), 0 otherwise
;;;   combo --icnf FILE               incremental CNF: answer each "a" line
;;;   combo [-in] [-smt2] [FILE]      SMT-LIB2 commands from FILE or the
;;;                                   standard input, answered as z3 does;
;;;                                   exits with status 1 after an error
;;;   combo --serve                   a server, for a client such as the
;;;                                   editor: serve.fx says its requests

(module-parameters ((m-sat (load-moduleof "sat.fx")) (m-rat (load-moduleof "rat.fx"))
                    (m-dimacs (load-moduleof "dimacs.fx" m-sat))
                    (m-elim (load-moduleof "elim.fx" m-sat))
                    (m-term (load-moduleof "term.fx" m-sat m-rat))
                    (m-bv (load-moduleof "bv.fx" m-sat m-rat m-term))
                    (m-arith (load-moduleof "arith.fx" m-sat m-rat m-term))
                    (m-eval (load-moduleof "eval.fx" m-sat m-rat m-term))
                    (m-simplex (load-moduleof "simplex.fx" m-sat m-rat))
                    (m-blast (load-moduleof "blast.fx" m-sat m-rat m-term m-bv m-arith m-eval m-simplex))
                    (m-sexp (load-moduleof "sexp.fx" m-sat m-rat))
                    (m-smt (load-moduleof "smt.fx" m-sat m-rat m-term m-bv m-arith m-eval m-simplex m-blast))
                    (m-smtlib (load-moduleof "smtlib.fx" m-sat m-rat m-term m-bv m-arith m-eval m-simplex m-blast m-sexp m-smt))
                    (m-serve (load-moduleof "serve.fx" m-sat m-rat m-term m-bv m-arith m-eval m-simplex m-blast m-sexp m-smt m-smtlib))))

;; Macros: each file defines its own, for now (docs/macros.md).
(define-syntax loop
  (syntax-rules ()
    ((_ go eff ((x t i) ...) r body) (letrec ((go (subr eff (t ...) r) (lambda (x ...) body))) (go i ...)))))
(hide (define kit-strings (load-module "../kit/strings.fx"))
      (import kit-strings string-concatenate))

(define-effect main-eff (maxeff cb-eff (io stdout) (io stderr) (io stdin) (io fs-read) (io fs-write) (io args) (io exit) (alloc @a) (read @a)))

(define* say (subr (io stdout) (string) unit) (lambda (s) (tagcase (write-out s) (done u #u) (failed e #u))))
(define* say-err (subr (io stderr) (string) unit) (lambda (s) (tagcase (write-err s) (done u #u) (failed e #u))))

(define* usage (subr main-eff () int)
  (lambda () (begin (say-err "usage: combo --dimacs FILE [--proof PROOF] [--stats] [--no-elim] | --icnf FILE | --serve | [-in] [FILE.smt2]\n") 2)))

"The text of file `f` (\"-\": not read from here), as bytes."
(define* file-bytes (subr main-eff (string) (sumof (bytes bytes) (failed string)))
  (lambda (f)
    (tagcase (the (sumof (data (bytevectorof @cb)) (failed io-error)) (read-file f))
      (data d (sum bytes d))
      (failed e (sum failed (string-append "combo: cannot read " f))))))

"A CNF solved: read into a new solver, after eliminating variables if
`elim?`, its proof written to `proof-file` (\"\": none)."
(define* run-dimacs (subr main-eff (string string bool bool) int)
  (lambda (file proof-file stats? elim?)
    (tagcase (file-bytes file)
      (failed why (begin (say-err (string-append why "\n")) 2))
      (bytes b
        (tagcase (read-dimacs b)
          (dimacs-bad (why) (begin (say-err (string-append why "\n")) 2))
          (dimacs-ok (nvars items)
            (let* ((s (make-solver)) (proof? (not (string=? proof-file "")))
                   (clauses (loop go main-eff ((l dimacs-items items)) (listof ints acyclic)
                              (if (null? l) nil
                                  (tagcase (car l) (d-clause (lits) (cons lits (go (cdr l)))) (d-assume (lits) (go (cdr l)))))))
                   (nvars (loop go main-eff ((cs (listof ints acyclic) clauses) (m int nvars)) int
                            (if (null? cs) m (go (cdr cs) (loop mx spin ((l ints (car cs)) (m int m)) int
                                                            (if (null? l) m (mx (cdr l) (max m (lit-var (car l))))))))))
                   (add-all (lambda ((cs (listof ints acyclic)))
                              (loop go main-eff ((l (listof ints acyclic) cs)) unit
                                (if (null? l) #u (begin (sat-add-clause! s (car l)) (go (cdr l))))))))
              (begin
                (if proof? (sat-keep-proof! s) #u)
                (let* ((el (if elim? (eliminate nvars clauses proof?) (the eliminated (product (ok #t) (clauses clauses) (stack nil) (proof nil)))))
                       (answer (begin
                                 (ensure-vars! s nvars)
                                 (if (extract el ok) (add-all (extract el clauses)) (begin (sat-add-clause! s nil) #u))
                                 (loop go main-eff ((l ints (eliminated-vars (extract el stack)))) unit
                                   (if (null? l) #u (begin (sat-remove-var! s (car l)) (go (cdr l)))))
                                 (sat-solve s nil))))
                  (begin
                    (if (= answer sat-sat) (extend-model! (extract el stack) (sat-model s)) #u)
                    (if proof?
                        (tagcase (write-file proof-file (the (bytevectorof @cb) (string->utf8 (string-concatenate (append (reverse (extract el proof)) (reverse (sat-proof-lines s)))))))
                          (done u #u)
                          (failed e (say-err (string-append "combo: cannot write " (string-append proof-file "\n")))))
                        #u)
                    (if stats?
                        (loop go main-eff ((l (listof stat acyclic) (sat-stats s))) unit
                          (if (null? l) #u
                              (begin (say (string-append "c " (string-append (extract (car l) name) (string-append " " (string-append (int->string (extract (car l) value)) "\n")))))
                                     (go (cdr l)))))
                        #u)
                    (say (dimacs-result s answer))
                    answer))))))))))

(define* run-icnf (subr main-eff (string) int)
  (lambda (file)
    (tagcase (file-bytes file)
      (failed why (begin (say-err (string-append why "\n")) 2))
      (bytes b
        (tagcase (read-dimacs b)
          (dimacs-bad (why) (begin (say-err (string-append why "\n")) 2))
          (dimacs-ok (nvars items)
            (let ((s (make-solver)))
              (loop go main-eff ((l dimacs-items items)) int
                (if (null? l) 0
                    (begin
                      (tagcase (car l)
                        (d-clause (lits) (begin (sat-add-clause! s lits) #u))
                        (d-assume (lits)
                          (let ((answer (sat-solve s lits)))
                            (begin (say (dimacs-result s answer))
                                   (if (= answer sat-unsat) (say (dimacs-failed s)) #u)))))
                      (go (cdr l))))))))))))

"The value of option `name` in `as`, or \"\"."
(define* option (subr (maxeff spin (read @a)) (string (listof string @a)) string)
  (lambda (name as)
    (cond ((null? as) "")
          ((and (string=? (car as) name) (pair? (cdr as))) (car (cdr as)))
          (else (option name (cdr as))))))
(define* flag? (subr (maxeff spin (read @a)) (string (listof string @a)) bool)
  (lambda (name as) (and (pair? as) (or (string=? (car as) name) (flag? name (cdr as))))))

"Run a session's commands, writing its answers. Where the run stopped."
(define* run-and-say! (subr main-eff (session sexp-reader) int)
  (lambda (s r)
    (let ((status (smtlib-run! s r)))
      (begin (say (session-take-output! s))
             (let ((e (session-take-errors! s))) (if (string=? e "") #u (say-err e)))
             status))))

"SMT-LIB2 commands from a file, all at once."
(define* run-smtlib-file (subr main-eff (string) int)
  (lambda (file)
    (tagcase (file-bytes file)
      (failed why (begin (say-err (string-append why "\n")) 1))
      (bytes b
        (tagcase (utf8->string b)
          (bad k (begin (say-err (string-append "combo: not UTF-8: " file "\n")) 1))
          (text t
            (let ((s (make-session)) (r (make-sexp-reader)))
              (begin (sexp-feed! r t) (sexp-close! r) (run-and-say! s r)
                     (if (session-errors? s) 1 0)))))))))

"SMT-LIB2 commands from the standard input, a line at a time: each
command is answered as soon as it is read whole."
(define* run-smtlib-stdin (subr main-eff () int)
  (lambda ()
    (let ((s (make-session)) (r (make-sexp-reader)))
      (loop go main-eff () int
        (tagcase (read-line)
          (line l (begin (sexp-feed! r (string-append l "\n"))
                         (if (= (run-and-say! s r) run-more) (go) (if (session-errors? s) 1 0))))
          (else y (begin (sexp-close! r) (run-and-say! s r) (if (session-errors? s) 1 0))))))))

(define* main (subr main-eff () int)
  (lambda ()
    (let ((as (the (listof string @a) (args))))
      (cond ((not (string=? (option "--dimacs" as) ""))
             (run-dimacs (option "--dimacs" as) (option "--proof" as) (flag? "--stats" as) (not (flag? "--no-elim" as))))
            ((not (string=? (option "--icnf" as) "")) (run-icnf (option "--icnf" as)))
            ((flag? "--serve" as) (serve))
            (else
             ;; z3's -in and -smt2 are taken and ignored, so that combo can be
             ;; run as z3 is.
             (let ((files (loop go main-eff ((l (listof string @a) as)) (listof string acyclic)
                            (cond ((null? l) nil)
                                  ((or (string=? (car l) "-in") (string=? (car l) "-smt2")) (go (cdr l)))
                                  (else (cons (car l) (go (cdr l))))))))
               (cond ((null? files) (run-smtlib-stdin))
                     ((and (null? (cdr files)) (not (char=? (string-ref (car files) 0) #\-))) (run-smtlib-file (car files)))
                     (else (usage)))))))))
