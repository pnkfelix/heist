;;; main.fx: the CFA from the command line (bin/cfa).
;;;
;;;   bin/cfa [-m N] FILE …   the files analysed as one world, of the
;;;                           language their names say (.fx: FX-26), at
;;;                           depth N (0, 0CFA, if not said); each note
;;;                           written, `FILE:START-END: TEXT`
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
(define* cf-run-world (subr (maxeff cf-eff (io stdout) spin) (cf-lang cores strings int) unit)
  (lambda (lang tops paths m)
    (begin
      (cf-start! lang tops m)
      (letrec ((run (subr cf-eff () unit) (lambda () (if (cf-step! 100000) #u (run)))))
        (run))
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
        (files paths)))))

(define* main (subr (maxeff fx-eff sc-eff s7-drive-eff (io fs-read) (io stdout) (io stdin) (io args) (alloc @a) (read @a) spin) () int)
  (lambda ()
    (let* ((as (letrec ((go (subr (maxeff (read @a) spin) ((listof string @a)) strings) (lambda (l) (if (null? l) nil (cons (car l) (go (cdr l)))))))
                 (go (the (listof string @a) (args)))))
           (m (if (and (pair? as) (string=? (car as) "-m") (pair? (cdr as))) (cf-decimal (car (cdr as))) 0))
           (files (if (and (pair? as) (string=? (car as) "-m") (pair? (cdr as))) (cdr (cdr as)) as))
           (fx (cf-filter files #f))
           (sc (cf-filter files #t)))
      (if (and (pair? as) (string=? (car as) "--serve"))
          (let ((why (s7-init!))) (begin (cf-answer "ready" (list why)) (cf-serve)))
      (begin
        (if (null? fx) #u (cf-run-world cf-fx26 (fx-world fx (cf-texts fx)) fx m))
        (if (null? sc) #u
            (let ((why (s7-init!)))
              (if (string=? why "") (cf-run-world cf-scheme (sc-world sc (cf-texts sc)) sc m)
                  (cf-say-line (string-append "cfa: s7st: " why)))))
        0)))))
