;;; main.fx: s7st from the command line (bin/s7st).
;;;
;;;   bin/s7st FILE …   each file run, as `load` runs it; exit 1 if one fails
;;;   bin/s7st          a REPL: each line read until the data are whole,
;;;                     then run, each value written

(define* s7-say (subr (io stdout) (string) unit)
  (lambda (s) (if (string=? s "") #u (begin (write-out s) #u))))

"What runs, run to its end, its output written as it comes. Whether it
ended well."
(define* s7-drive (subr (maxeff s7-eff (io stdout)) () bool)
  (lambda ()
    (tagcase (s7-continue! 20000)
      (running u (begin (s7-say (s7-take-output!)) (s7-drive)))
      (done v (begin (s7-say (s7-take-output!)) #t))
      (failed m (begin (s7-say (s7-take-output!)) (s7-say (string-append (s7-fresh-line) "Error: " m "\n")) #f)))))

(define* s7-run-files (subr (maxeff s7-eff (io stdout) (read @a)) ((listof string @a)) int)
  (lambda (files)
    (if (null? files) 0
        (tagcase (s7-file-text (car files))
          (failed m (begin (s7-say (string-append "s7st: " m "\n")) 1))
          (text t (tagcase (s7-start! t (car files) #f)
                    (bad m (begin (s7-say (string-append "Error: " m "\n")) 1))
                    (none u (if (s7-drive) (s7-run-files (cdr files)) 1))))))))

(define* s7-repl (subr (maxeff s7-eff (io stdout) (io stdin)) (string) int)
  ;; `pending`: lines read and not yet whole data.
  (lambda (pending)
    (begin
      (s7-say (if (string=? pending "") "s7st> " "  ... "))
      (tagcase (read-line)
        (line l (let ((text (string-append pending l "\n")))
                  (tagcase (s7-input-state text)
                    (incomplete u (s7-repl text))
                    (bad m (begin (s7-say (string-append "Error: " m "\n")) (s7-repl "")))
                    (complete u (begin
                                  (tagcase (s7-start! text "" #t)
                                    (bad m (s7-say (string-append "Error: " m "\n")))
                                    (none u (begin (s7-drive) #u)))
                                  (s7-repl ""))))))
        (else y (begin (s7-say "\n") 0))))))

(define* main (subr (maxeff s7-eff (io stdout) (io stdin) (io args) (alloc @a) (read @a)) () int)
  (lambda ()
    (let ((as (the (listof string @a) (args)))
          (why (s7-init!)))
      (cond ((not (string=? why "")) (begin (s7-say (string-append "s7st: " why "\n")) 2))
            ((null? as) (s7-repl ""))
            (else (s7-run-files as))))))
