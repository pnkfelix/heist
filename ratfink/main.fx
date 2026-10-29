;;; main.fx: the command line of ratfink, which checks the proofs in the
;;; files it names: shakedown's `(shakedown main)`.
;;;
;;;   ratfink [--unwind N] [--split] [--max-calls N] [--timeout SECONDS] [--playback DIR]
;;;           [--library-path DIR]... [--proof NAME]... [--solver z3|combo]
;;;           [--verbose] file.scm ...
;;;
;;; bin/ratfink passes what shakedown reads from the environment as
;;; options: --solver-command (RATFINK_SOLVER), --smt-log (RATFINK_SMT_LOG),
;;; --larceny (LARCENY, for playback). Exits with status 0 if every proof
;;; passed, 1 if one failed, and 2 if a file could not be checked.

(module-parameters ((m-core (load-moduleof "core.fx")) (m-term (load-moduleof "term.fx" m-core))
                    (m-value (load-moduleof "value.fx" m-core m-term))
                    (m-print (load-moduleof "print.fx" m-core))
                    (m-syntax (load-moduleof "syntax.fx" m-core m-print))
                    (m-numbers (load-moduleof "numbers.fx" m-core))
                    (m-reader (load-moduleof "reader.fx" m-core m-numbers))
                    (m-machine (load-moduleof "machine.fx" m-core m-term m-value))
                    (m-prims (load-moduleof "prims.fx" m-core m-term m-value m-print m-syntax m-numbers m-reader m-machine))
                    (m-hashtables (load-moduleof "hashtables.fx" m-core m-term m-value m-print m-syntax m-numbers m-reader m-machine m-prims))
                    (m-ports (load-moduleof "ports.fx" m-core m-term m-value m-print m-syntax m-numbers m-reader m-machine m-prims m-hashtables))
                    (m-prelude (load-moduleof "prelude.fx" m-core m-numbers m-reader))
                    (m-library (load-moduleof "library.fx" m-core m-print m-syntax m-numbers m-reader))
                    (m-smt (load-moduleof "smt.fx" m-core m-term m-print m-numbers m-reader))
                    (m-eval (load-moduleof "eval.fx" m-core m-term m-value m-print m-syntax m-numbers m-reader m-machine m-prims m-hashtables m-ports m-prelude m-library))
                    (m-playback (load-moduleof "playback.fx" m-core m-term m-value m-print m-syntax m-numbers m-reader m-machine m-prims m-hashtables m-ports m-prelude m-library m-eval))
                    (m-check (load-moduleof "check.fx" m-core m-term m-value m-print m-syntax m-numbers m-reader m-machine m-prims m-hashtables m-ports m-prelude m-library m-smt m-eval m-playback))
                    (m-fx26 (load-moduleof "fx26.fx" m-core m-print m-syntax m-numbers m-reader m-library))))

(define say (subr rf-eff (string) unit) (lambda (s) (tagcase (write-out s) (done u #u) (failed e #u))))

(define usage-text string
  "usage: ratfink [--unwind N] [--split] [--max-calls N] [--timeout SECONDS] [--playback DIR] [--library-path DIR]... [--proof NAME]... [--solver z3|combo] [--verbose] file.scm ...\n")

"An error's text: its message and irritants, as shakedown describes a
condition."
(define describe-signal (subr rf-eff (rf-signal) string)
  (lambda (s)
    (tagcase s
      (err e (string-append (extract e message) (strings-concat (map (lambda ((i rf-value)) (string-append " " (datum->string i))) (extract e irritants)))))
      (else x "path aborted"))))

(define parse-count (subr rf-st (string) int)
  (lambda (s) (tagcase (parse-number s) (some v (if (and (rf-exact-integer? v) (>= (rf-int-of v) 0)) (rf-int-of v) -1)) (none u -1))))

"The files and options of a command line; or none, for usage."
(define-type parsed (productof (files strings) (options check-options) (library-dirs strings)))
(define parse-arguments (subr rf-eff (strings) (sumof (usage unit) (ok parsed)))
  (lambda (arguments)
    (letrec ((loop (subr rf-eff (strings strings check-options strings) (sumof (usage unit) (ok parsed)))
               (lambda (args files o dirs)
                 (let ((next-value (lambda ((k (subr rf-eff (string) (sumof (usage unit) (ok parsed)))))
                               (if (pair? (cdr args)) (k (car (cdr args))) (sum usage #u)))))
                   (cond ((null? args) (sum ok (product (files (the strings (reverse files))) (options o) (library-dirs (the strings (reverse dirs))))))
                         ((string=? (car args) "--verbose") (loop (cdr args) files (set-verbose o) dirs))
                         ((string=? (car args) "--split") (loop (cdr args) files (set-split o) dirs))
                         ((or (string=? (car args) "--unwind") (string=? (car args) "--timeout") (string=? (car args) "--max-calls"))
                          (next-value (lambda ((v string))
                                  (let ((n (parse-count v)))
                                    (if (< n 0) (sum usage #u)
                                        (loop (cdr (cdr args)) files
                                              (cond ((string=? (car args) "--unwind") (set-unwind o n))
                                                    ((string=? (car args) "--timeout") (set-timeout o n))
                                                    (else (set-max-calls o n)))
                                              dirs))))))
                         ((string=? (car args) "--playback") (next-value (lambda ((v string)) (loop (cdr (cdr args)) files (set-playback o v) dirs))))
                         ((string=? (car args) "--proof")
                          (next-value (lambda ((v string)) (loop (cdr (cdr args)) files (add-proof o (string->symbol v)) dirs))))
                         ((string=? (car args) "--solver")
                          (next-value (lambda ((v string))
                                  (cond ((string=? v "z3") (loop (cdr (cdr args)) files (set-solver o 'z3) dirs))
                                        ((or (string=? v "combo") (string=? v "lockpick")) (loop (cdr (cdr args)) files (set-solver o 'combo) dirs))
                                        (else (sum usage #u))))))
                         ((string=? (car args) "--library-path") (next-value (lambda ((v string)) (loop (cdr (cdr args)) files o (cons v dirs)))))
                         ((string=? (car args) "--solver-command") (next-value (lambda ((v string)) (begin (set-solver-command! v) (loop (cdr (cdr args)) files o dirs)))))
                         ((string=? (car args) "--smt-log") (next-value (lambda ((v string)) (begin (set-smt-log-file! v) (loop (cdr (cdr args)) files o dirs)))))
                         ((string=? (car args) "--trace-terms") (begin (set-trace-terms! #t) (loop (cdr args) files o dirs)))
                         ((string=? (car args) "--environment")
                          (next-value (lambda ((v string)) (begin (tagcase (file-text v) (some t (set-environment! t)) (none u #u)) (loop (cdr (cdr args)) files o dirs)))))
                         ((string=? (car args) "--larceny") (next-value (lambda ((v string)) (begin (set-larceny! v) (loop (cdr (cdr args)) files o dirs)))))
                         ((and (> (string-length (car args)) 0) (char=? (string-ref (car args) 0) #\-)) (sum usage #u))
                         (else (loop (cdr args) (cons (car args) files) o dirs)))))))
      (loop arguments nil default-options nil))))

(define set-verbose (subr rf-st (check-options) check-options)
  (lambda (o) (product (unwind (extract o unwind)) (timeout (extract o timeout)) (verbose #t) (playback (extract o playback)) (library-path (extract o library-path))
                       (proofs (extract o proofs)) (split (extract o split)) (max-calls (extract o max-calls)) (solver (extract o solver)))))
(define set-split (subr rf-st (check-options) check-options)
  (lambda (o) (product (unwind (extract o unwind)) (timeout (extract o timeout)) (verbose (extract o verbose)) (playback (extract o playback)) (library-path (extract o library-path))
                       (proofs (extract o proofs)) (split #t) (max-calls (extract o max-calls)) (solver (extract o solver)))))
(define set-unwind (subr rf-st (check-options int) check-options)
  (lambda (o n) (product (unwind n) (timeout (extract o timeout)) (verbose (extract o verbose)) (playback (extract o playback)) (library-path (extract o library-path))
                         (proofs (extract o proofs)) (split (extract o split)) (max-calls (extract o max-calls)) (solver (extract o solver)))))
(define set-timeout (subr rf-st (check-options int) check-options)
  (lambda (o n) (product (unwind (extract o unwind)) (timeout n) (verbose (extract o verbose)) (playback (extract o playback)) (library-path (extract o library-path))
                         (proofs (extract o proofs)) (split (extract o split)) (max-calls (extract o max-calls)) (solver (extract o solver)))))
(define set-max-calls (subr rf-st (check-options int) check-options)
  (lambda (o n) (product (unwind (extract o unwind)) (timeout (extract o timeout)) (verbose (extract o verbose)) (playback (extract o playback)) (library-path (extract o library-path))
                         (proofs (extract o proofs)) (split (extract o split)) (max-calls n) (solver (extract o solver)))))
(define set-playback (subr rf-st (check-options string) check-options)
  (lambda (o d) (product (unwind (extract o unwind)) (timeout (extract o timeout)) (verbose (extract o verbose)) (playback d) (library-path (extract o library-path))
                         (proofs (extract o proofs)) (split (extract o split)) (max-calls (extract o max-calls)) (solver (extract o solver)))))
(define add-proof (subr rf-st (check-options symbol) check-options)
  (lambda (o p) (product (unwind (extract o unwind)) (timeout (extract o timeout)) (verbose (extract o verbose)) (playback (extract o playback)) (library-path (extract o library-path))
                         (proofs (sum some (cons p (tagcase (extract o proofs) (some ps ps) (none u nil))))) (split (extract o split)) (max-calls (extract o max-calls)) (solver (extract o solver)))))
(define set-solver (subr rf-st (check-options symbol) check-options)
  (lambda (o s) (product (unwind (extract o unwind)) (timeout (extract o timeout)) (verbose (extract o verbose)) (playback (extract o playback)) (library-path (extract o library-path))
                         (proofs (extract o proofs)) (split (extract o split)) (max-calls (extract o max-calls)) (solver s))))
(define with-library-path (subr rf-st (check-options strings) check-options)
  (lambda (o dirs) (product (unwind (extract o unwind)) (timeout (extract o timeout)) (verbose (extract o verbose)) (playback (extract o playback)) (library-path dirs)
                            (proofs (extract o proofs)) (split (extract o split)) (max-calls (extract o max-calls)) (solver (extract o solver)))))

"A file's forms: an FX-26 program's (.fx) through fx26.fx, which also
makes FX-26's forms known to the compiler; a Scheme program's as read."
(define fx26-file? (subr rf-st (string) bool)
  (lambda (f) (and (>= (string-length f) 3) (string=? (substring f (- (string-length f) 3) (string-length f)) ".fx"))))
(define program-forms (subr rf-eff (string) rf-vals)
  (lambda (file)
    (begin (set-fx26! (fx26-file? file))
           (if (fx26-file? file) (fx26-program file) (read-file-data file #f)))))

"Check the files; the exit status."
(define check-files (subr rf-eff (strings check-options strings) int)
  (lambda (files options dirs)
    (letrec ((loop (subr rf-eff (strings int) int)
               (lambda (fs status)
                 (if (null? fs) status
                     (let* ((file (car fs))
                            (code (the (ref int @rf) (new 0))))
                       (begin
                         (rf-catch
                          (lambda ()
                            (begin
                              (if (pair? (cdr fs)) (say (string-append "== " file "\n")) #u)
                              (let ((failed (check-forms (program-forms file) say
                                                         (with-library-path options (append dirs (list (directory-of file)))))))
                                (begin (set code (if (> failed 0) 1 0)) rf-unspecified))))
                          (lambda ((s rf-signal))
                            (begin (say (string-append "ratfink: " file ": " (describe-signal s) "\n"))
                                   (set code 2)
                                   rf-unspecified)))
                         (loop (cdr fs) (max status (get code)))))))))
      (loop files 0))))

"Check the files the arguments name: the exit status."
(define ratfink-main (subr rf-eff (strings) int)
  (lambda (arguments)
    (tagcase (parse-arguments arguments)
      (usage u (begin (say usage-text) 2))
      (ok p (if (null? (extract p files)) (begin (say usage-text) 2)
                (check-files (extract p files) (extract p options) (extract p library-dirs)))))))
