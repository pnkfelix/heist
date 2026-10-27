;;; main.fx: s7st from the command line (bin/s7st).
;;;
;;;   bin/s7st FILE …   each file run, as `load` runs it; exit 1 if one fails
;;;   bin/s7st          a REPL: each line read until the data are whole,
;;;                     then run, each value written
;;;   bin/s7st --serve  a server, for a client such as the editor
;;;                     (editor/scheme.fx): requests on standard input,
;;;                     answers on standard output, a line each
;;;
;;; The server's lines. Each is a word, a space, then fields separated by
;;; tabs, each with its backslashes, newlines and tabs escaped (\\, \n, \t).
;;; Requests:
;;;   run MODE DIR FILE TEXT  TEXT run (of FILE; relative file names
;;;                           relative to DIR). MODE `repl`: only if its data
;;;                           are whole, each value written; `quiet`: not
;;;   describe NAME OPERATOR  what NAME is, else OPERATOR (eldoc)
;;;   interrupt               what runs, stopped
;;; Answers:
;;;   ready WHY               started: WHY empty, or why it did not
;;;   started                 a `run` began
;;;   incomplete              a `run` in `repl` mode whose data are not whole
;;;   busy                    a `run` refused: one is running
;;;   out TEXT                output
;;;   value TEXT              what ran ended, its last value written (or empty)
;;;   error MESSAGE           what ran ended with an error
;;;   interrupted             what ran was stopped
;;;   describe TEXT           a `describe`'s answer (empty: nothing known)

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
          (text t (tagcase (begin (s7-add-library-directory! (s7-directory-of (car files))) (s7-start! t (car files) #f))
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

"`s` with backslashes, newlines and tabs escaped; and back."
(define* s7-escape (subr spin (string) string)
  (lambda (s)
    (letrec ((go (subr spin (int (listof string acyclic)) (listof string acyclic))
               (lambda (i acc)
                 (if (>= i (string-length s)) acc
                     (let ((c (string-ref s i)))
                       (go (+ i 1) (cons (cond ((char=? c #\\) "\\\\") ((char=? c #\newline) "\\n") ((char=? c #\tab) "\\t")
                                               (else (char->string c)))
                                         acc)))))))
      (s7-concat (reverse (go 0 nil))))))
(define* s7-unescape (subr spin (string) string)
  (lambda (s)
    (let ((n (string-length s)))
      (letrec ((go (subr spin (int (listof char acyclic)) (listof char acyclic))
                 (lambda (i acc)
                   (cond ((>= i n) acc)
                         ((and (char=? (string-ref s i) #\\) (< (+ i 1) n))
                          (let ((c (string-ref s (+ i 1))))
                            (go (+ i 2) (cons (cond ((char=? c #\n) #\newline) ((char=? c #\t) #\tab) (else c)) acc))))
                         (else (go (+ i 1) (cons (string-ref s i) acc)))))))
        (list->string (reverse (go 0 nil)))))))
"A request's word, and its fields, unescaped."
(define* s7-request (subr spin (string) (productof (word string) (fields s7-strings)))
  (lambda (line)
    (let* ((sp (string-search line " " 0))
           (word (if (< sp 0) line (substring line 0 sp)))
           (rest (if (< sp 0) "" (substring line (+ sp 1) (string-length line)))))
      (letrec ((split (subr spin (int int s7-strings) s7-strings)
                 (lambda (i start acc)
                   (cond ((>= i (string-length rest)) (reverse (the s7-strings (cons (s7-unescape (substring rest start i)) acc))))
                         ((char=? (string-ref rest i) #\tab) (split (+ i 1) (+ i 1) (cons (s7-unescape (substring rest start i)) acc)))
                         (else (split (+ i 1) start acc))))))
        (product (word word) (fields (if (< sp 0) nil (split 0 0 nil))))))))
(define* s7-answer (subr (maxeff spin (io stdout)) (string string) unit)
  (lambda (word text) (s7-say (string-append word " " (s7-escape text) "\n"))))
(define* s7-field (subr spin (s7-strings int) string)
  (lambda (l i) (cond ((null? l) "") ((= i 0) (car l)) (else (s7-field (cdr l) (- i 1))))))

"Output so far answered; then, if what ran has ended, how. A newline
first, if output did not end its line, so that what comes after starts one."
(define* s7-serve-slice! (subr (maxeff s7-eff (io stdout)) () unit)
  (lambda ()
    (let* ((status (s7-continue! 20000))
           (out (s7-take-output!))
           (fresh (lambda () (if (get s7-console-fresh) #u (begin (s7-answer "out" "\n") (set s7-console-fresh #t))))))
      (begin
        (if (string=? out "") #u (s7-answer "out" out))
        (tagcase status
          (running u #u)
          (done v (begin (fresh) (s7-answer "value" (if (s7-shown? v) (s7-show v #t) ""))))
          (failed m (begin (fresh) (s7-answer "error" m))))))))
"Request `line` done."
(define* s7-serve-request! (subr (maxeff s7-eff (io stdout)) (string) unit)
  (lambda (line)
    (let* ((r (s7-request line)) (w (extract r word)) (f (extract r fields)))
      (cond
        ((string=? w "run")
         (if (s7-busy?) (s7-answer "busy" "")
             (let ((repl (string=? (s7-field f 0) "repl"))
                   (text (s7-field f 3)))
               (begin
                 (set s7-directory (s7-field f 1))
                 (if (and repl (tagcase (s7-input-state text) (incomplete u #t) (else y #f)))
                     (s7-answer "incomplete" "")
                     (tagcase (s7-start! text (s7-field f 2) repl)
                       (bad m (begin (s7-answer "started" "") (s7-answer "error" m)))
                       (none u (s7-answer "started" ""))))))))
        ((string=? w "describe")
         (let ((d (s7-describe (s7-field f 0))))
           (s7-answer "describe" (if (string=? d "") (s7-describe (s7-field f 1)) d))))
        ((string=? w "interrupt")
         (if (s7-busy?)
             (begin (s7-interrupt!)
               (let ((out (s7-take-output!))) (if (string=? out "") #u (s7-answer "out" out)))
               (if (get s7-console-fresh) #u (s7-answer "out" "\n"))
               (s7-answer "interrupted" ""))
             #u))
        (else #u)))))
"The server: requests read, and what they run run, a slice at a time,
requests read between slices. Its exit status, when its input ends."
(define* s7-serve (subr (maxeff s7-eff (io stdout) (io stdin)) () int)
  (lambda ()
    (let ((next (lambda ()
                  (tagcase (read-line)
                    (line l (begin (s7-serve-request! l) #t))
                    (else y #f)))))
      (if (s7-busy?)
          (begin (s7-serve-slice!)
            (if (stdin-ready?) (if (next) (s7-serve) 0) (s7-serve)))
          (if (next) (s7-serve) 0)))))

(define* main (subr (maxeff s7-eff (io stdout) (io stdin) (io args) (alloc @a) (read @a)) () int)
  (lambda ()
    (let ((as (the (listof string @a) (args)))
          (why (s7-init!)))
      (cond ((and (pair? as) (string=? (car as) "--serve")) (begin (s7-answer "ready" why) (s7-serve)))
            ((not (string=? why "")) (begin (s7-say (string-append "s7st: " why "\n")) 2))
            ((null? as) (s7-repl ""))
            (else (s7-run-files as))))))
