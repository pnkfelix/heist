;;; main.fx: the CFA from the command line (bin/cfa).
;;;
;;;   bin/cfa [-L DIR]… [--progress] [--collapse] [-m N] FILE …
;;;                           the files analysed as one world, of the
;;;                           language their names say (.fx: FX-26), with
;;;                           the libraries Scheme files import (found in
;;;                           each DIR, and where the files' own libraries
;;;                           are), at
;;;                           depth N (0, 0CFA, if not said); each note
;;;                           written, `FILE:START-END: TEXT`; with
;;;                           --collapse, a set holding unknown drops its
;;;                           sites (engine.fx's `collapse`); with
;;;                           --progress, every 2000 tasks a line on the
;;;                           standard error: ms, then `cf-status`
;;;   bin/cfa --serve         a server, for a client such as the editor:
;;;                           serve.fx says its requests and answers

(define* cf-say-line (subr (io stdout) (string) unit) (lambda (s) (begin (write-out (string-append s "\n")) #u)))

(define* cf-filter (subr spin (strings bool) strings)
  (lambda (l scheme) (cond ((null? l) nil)
                           ((eq? (cf-scheme-file? (car l)) scheme) (cons (car l) (cf-filter (cdr l) scheme)))
                           (else (cf-filter (cdr l) scheme)))))
(define* cf-texts (subr (maxeff (io fs-read) spin) (strings) strings)
  (lambda (l) (if (null? l) nil (cons (cf-text-of-file (car l)) (cf-texts (cdr l))))))

"The world read (core.fx) analysed, of `lang`, at depth `m`, to the end;
the notes of its files `paths` written."
"Whether to say the analysis's progress on the standard error (`--progress`)."
(define cf-progress (ref bool @cf) (new #f))
(define* cf-run-world (subr (maxeff cf-eff (io stdout) (io stderr) (io clock) spin) (cf-lang cores strings int) unit)
  (lambda (lang tops paths m)
    (let ((t0 (clock)))
      (begin
        (cf-start! lang tops m)
        (letrec ((run (subr (maxeff cf-eff (io stderr) (io clock)) () unit)
                   (lambda () (let ((done (cf-step! 2000)))
                                (begin
                                  (if (get cf-progress)
                                      (begin (write-err (string-append "cfa: " (int->string (i64->int (i64-quotient (i64- (clock) t0) (int->i64 1000000))))
                                                                       " ms " (cf-status) "\n"))
                                        #u)
                                      #u)
                                  (if done #u (run)))))))
          (run))
        (if (get cf-progress)
            (begin (write-err (string-append "cfa: " (cf-escape-report 12) "\n"))
              (write-err (string-append "cfa: defined nowhere: " (cf-concat (reverse (get sc-undefined)) " ") "\n"))
              (write-err (string-append "cfa: unknown first in: " (cf-concat (get cf-unknown-firsts) "; ") "\n"))
              #u)
            #u)
      (letrec ((files (subr (maxeff cf-eff (io stdout)) (strings) unit)
                 (lambda (ps)
                   (if (null? ps) #u
                       (begin
                         (letrec ((say (subr (maxeff cf-eff (io stdout)) (cf-notes) unit)
                                    (lambda (ns) (if (null? ns) #u
                                                     (begin (cf-say-line (string-append (car ps) ":" (int->string (extract (car ns) start)) "-"
                                                                                         (int->string (extract (car ns) end)) ": " (extract (car ns) text)))
                                                       (say (cdr ns)))))))
                           (say (cf-file-notes (cf-file (car ps)))))
                         (files (cdr ps)))))))
          (files paths))))))

(define* main (subr (maxeff fx-eff sc-eff s7-drive-eff (io fs-read) (io stdout) (io stderr) (io clock) (io stdin) (io args) (alloc @a) (read @a) spin) () int)
  (lambda ()
    (let* ((as (letrec ((go (subr (maxeff (read @a) spin) ((listof string @a)) strings) (lambda (l) (if (null? l) nil (cons (car l) (go (cdr l)))))))
                 (go (the (listof string @a) (args)))))
           (dirs (letrec ((go (subr (maxeff s7-eff spin) (strings) strings)
                                (lambda (l) (if (and (pair? l) (string=? (car l) "-L") (pair? (cdr l)))
                                                (begin (s7-add-library-directory! (let ((d (car (cdr l))))
                                                                                    (if (char=? (string-ref d (- (string-length d) 1)) #\/) d (string-append d "/"))))
                                                  (go (cdr (cdr l))))
                                                l))))
                   (go as)))
           (as dirs)
           (progress (and (pair? as) (string=? (car as) "--progress")))
           (as (if progress (cdr as) as))
           (collapse (and (pair? as) (string=? (car as) "--collapse")))
           (as (if collapse (cdr as) as))
           (m (if (and (pair? as) (string=? (car as) "-m") (pair? (cdr as))) (cf-decimal (car (cdr as))) 0))
           (files (begin (set cf-collapse collapse) (set cf-progress progress)
                    (if (and (pair? as) (string=? (car as) "-m") (pair? (cdr as))) (cdr (cdr as)) as)))
           (fx (cf-filter files #f))
           (sc (cf-filter files #t)))
      (if (and (pair? as) (string=? (car as) "--serve"))
          (let ((why (s7-init!))) (begin (cf-answer "ready" (list why)) (cf-serve)))
      (begin
        (if (null? fx) #u (cf-run-world cf-fx26 (fx-world fx (cf-texts fx)) fx m))
        (if (null? sc) #u
            (let ((why (s7-init!)))
              (if (string=? why "")
                  ;; The libraries the files import are of their world, but only
                  ;; the files' notes are said.
                  (let* ((ws (sc-world-files sc (cf-texts sc)))
                         (ps (letrec ((go (subr spin ((listof sc-world-file acyclic)) strings)
                                            (lambda (l) (if (null? l) nil (cons (extract (car l) path) (go (cdr l)))))))
                               (go ws)))
                         (ts (letrec ((go (subr spin ((listof sc-world-file acyclic)) strings)
                                            (lambda (l) (if (null? l) nil (cons (extract (car l) text) (go (cdr l)))))))
                               (go ws))))
                    (cf-run-world cf-scheme (sc-world ps ts) sc m))
                  (cf-say-line (string-append "cfa: s7st: " why)))))
        0)))))
