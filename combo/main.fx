;;; main.fx: the combo program (`bin/combo`), as lockpick's `(lockpick main)`:
;;;   combo --dimacs FILE [--stats]   solve a CNF
;;;   combo --icnf FILE               incremental CNF: answer each "a" line
;;; Exits with status 10 for satisfiable, 20 for unsatisfiable (as SAT
;;; solvers do), 0 otherwise.

(module-parameters ((m-sat (load-moduleof "sat.fx")) (m-dimacs (load-moduleof "dimacs.fx" m-sat))))

(define-effect main-eff (maxeff cb-eff (io stdout) (io stderr) (io fs-read) (io args) (io exit) (alloc @a) (read @a)))

(define* say (subr (io stdout) (string) unit) (lambda (s) (tagcase (write-out s) (done u #u) (failed e #u))))
(define* say-err (subr (io stderr) (string) unit) (lambda (s) (tagcase (write-err s) (done u #u) (failed e #u))))

(define* usage (subr main-eff () int)
  (lambda () (begin (say-err "usage: combo --dimacs FILE [--stats] | --icnf FILE\n") 2)))

"The text of file `f` (\"-\": not read from here), as bytes."
(define* file-bytes (subr main-eff (string) (sumof (bytes bytes) (failed string)))
  (lambda (f)
    (tagcase (the (sumof (data (bytevectorof @cb)) (failed io-error)) (read-file f))
      (data d (sum bytes d))
      (failed e (sum failed (string-append "combo: cannot read " f))))))

(define* run-dimacs (subr main-eff (string bool) int)
  (lambda (file stats?)
    (tagcase (file-bytes file)
      (failed why (begin (say-err (string-append why "\n")) 2))
      (bytes b
        (tagcase (read-dimacs b)
          (dimacs-bad (why) (begin (say-err (string-append why "\n")) 2))
          (dimacs-ok (nvars items)
            (let ((s (make-solver)))
              (begin
                (ensure-vars! s nvars)
                (letrec ((add (subr main-eff (dimacs-items) unit)
                           (lambda (l) (if (null? l) #u
                                           (begin (tagcase (car l) (d-clause (lits) (begin (sat-add-clause! s lits) #u)) (d-assume (lits) #u))
                                                  (add (cdr l)))))))
                  (add items))
                (let ((answer (sat-solve s nil)))
                  (begin
                    (if stats?
                        (letrec ((go (subr main-eff ((listof stat acyclic)) unit)
                                   (lambda (l) (if (null? l) #u
                                                   (begin (say (string-append "c " (string-append (extract (car l) name) (string-append " " (string-append (int->string (extract (car l) value)) "\n")))))
                                                          (go (cdr l)))))))
                          (go (sat-stats s)))
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
              (letrec ((go (subr main-eff (dimacs-items) int)
                         (lambda (l)
                           (if (null? l) 0
                               (begin
                                 (tagcase (car l)
                                   (d-clause (lits) (begin (sat-add-clause! s lits) #u))
                                   (d-assume (lits)
                                     (let ((answer (sat-solve s lits)))
                                       (begin (say (dimacs-result s answer))
                                              (if (= answer sat-unsat) (say (dimacs-failed s)) #u)))))
                                 (go (cdr l)))))))
                (go items)))))))))

"The value of option `name` in `as`, or \"\"."
(define* option (subr (maxeff spin (read @a)) (string (listof string @a)) string)
  (lambda (name as)
    (cond ((null? as) "")
          ((and (string=? (car as) name) (pair? (cdr as))) (car (cdr as)))
          (else (option name (cdr as))))))
(define* flag? (subr (maxeff spin (read @a)) (string (listof string @a)) bool)
  (lambda (name as) (and (pair? as) (or (string=? (car as) name) (flag? name (cdr as))))))

(define* main (subr main-eff () int)
  (lambda ()
    (let ((as (the (listof string @a) (args))))
      (cond ((not (string=? (option "--dimacs" as) "")) (run-dimacs (option "--dimacs" as) (flag? "--stats" as)))
            ((not (string=? (option "--icnf" as) "")) (run-icnf (option "--icnf" as)))
            (else (usage))))))
