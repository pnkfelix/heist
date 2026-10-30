;;; main.fx: s7st from the command line (bin/s7st).
;;;
;;;   bin/s7st FILE …   each file run, as `load` runs it; exit 1 if one fails
;;;   bin/s7st -L DIR … DIR a directory libraries are looked for in, too
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
;;;   analyze KEY FILE TEXT   what TEXT is (analyze.fx), never run; KEY is
;;;                           given back
;;;   complete PREFIX         the names the top level sees that begin so
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
;;;   analysis KEY FACES DEFINITIONS REFERENCES PROBLEM AT
;;;                           an `analyze`'s answer, each list's items
;;;                           separated by spaces: FACES `start end f` (f:
;;;                           k keyword, f function-name, s string, c
;;;                           comment); DEFINITIONS `name start end`;
;;;                           REFERENCES `start end binder-start binder-end`;
;;;                           PROBLEM the read's error (empty: none), at AT.
;;;                           (What reaches a variable, what a call can call:
;;;                           the CFA's, ../cfa/.)
;;;   completions NAME …       a `complete`'s answer, sorted

(define* s7-say (subr (io stdout) (string) unit)
  (lambda (s) (if (string=? s "") #u (begin (write-out s) #u))))

"What runs, run to its end, its output written as it comes. Whether it
ended well."
(define* s7-drive (subr (maxeff s7-drive-eff (io stdout)) () bool)
  (lambda ()
    (tagcase (s7-continue! 20000)
      (running u (begin (s7-say (s7-take-output!)) (s7-drive)))
      (done v (begin (s7-say (s7-take-output!)) #t))
      (failed m (begin (s7-say (s7-take-output!)) (s7-say (string-append (s7-fresh-line) "Error: " m "\n")) #f)))))

(define* s7-run-files (subr (maxeff s7-drive-eff (io stdout) (read @a)) ((listof string @a)) int)
  (lambda (files)
    (if (null? files) 0
        (tagcase (s7-file-text (car files))
          (failed m (begin (s7-say (string-append "s7st: " m "\n")) 1))
          (text t (tagcase (begin (s7-add-library-directory! (s7-directory-of (car files))) (s7-start! t (car files) #f))
                    (bad m (begin (s7-say (string-append "Error: " m "\n")) 1))
                    (none u (if (s7-drive) (s7-run-files (cdr files)) 1))))))))

(define* s7-repl (subr (maxeff s7-drive-eff (io stdout) (io stdin)) (string) int)
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
      (string-concatenate (reverse (go 0 nil))))))
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
"An answer whose fields are `fields`, each escaped, separated by tabs."
(define* s7-answer-fields (subr (maxeff spin (io stdout)) (string s7-strings) unit)
  (lambda (word fields)
    (letrec ((join (subr spin (s7-strings) string)
               (lambda (l) (cond ((null? l) "") ((null? (cdr l)) (s7-escape (car l)))
                                 (else (string-append (s7-escape (car l)) "\t" (join (cdr l))))))))
      (s7-say (string-append word " " (join fields) "\n")))))
(define* s7-field (subr spin (s7-strings int) string)
  (lambda (l i) (cond ((null? l) "") ((= i 0) (car l)) (else (s7-field (cdr l) (- i 1))))))

"Output so far answered; then, if what ran has ended, how. A newline
first, if output did not end its line, so that what comes after starts one."
(define* s7-serve-slice! (subr (maxeff s7-drive-eff (io stdout)) () unit)
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
(define* s7-serve-request! (subr (maxeff s7-drive-eff (io stdout)) (string) unit)
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
        ((string=? w "analyze")
         (let* ((a (s7-analyze (s7-field f 2) (s7-field f 1)))
                (ints (lambda ((l (listof int acyclic)))
                        (letrec ((go (subr spin ((listof int acyclic)) (listof string acyclic))
                                   (lambda (l) (if (null? l) nil (cons (int->string (car l)) (if (null? (cdr l)) nil (cons " " (go (cdr l)))))))))
                          (string-concatenate (go l))))))
           (s7-answer-fields "analysis"
                             (list (s7-field f 0)
                                   (ints (letrec ((go (subr spin (s7-face-spans) (listof int acyclic))
                                                        (lambda (l) (if (null? l) nil
                                                                        (cons (extract (car l) start)
                                                                              (cons (extract (car l) end)
                                                                                    (cons (let ((fc (extract (car l) face)))
                                                                                            (cond ((eq? fc 'keyword) 0) ((eq? fc 'function-name) 1)
                                                                                                  ((eq? fc 'string) 2) ((eq? fc 'comment) 3) (else 4)))
                                                                                          (go (cdr l)))))))))
                                           (go (extract a faces))))
                                   (string-concatenate (letrec ((go (subr spin ((listof s7-def acyclic)) (listof string acyclic))
                                                             (lambda (l) (if (null? l) nil
                                                                             (cons (string-append (extract (car l) name) " " (int->string (extract (car l) start))
                                                                                                  " " (int->string (extract (car l) end)) (if (null? (cdr l)) "" " "))
                                                                                   (go (cdr l)))))))
                                                (go (extract a defs))))
                                   (ints (letrec ((go (subr spin ((listof s7-aref acyclic)) (listof int acyclic))
                                                        (lambda (l) (if (null? l) nil
                                                                        (cons (extract (car l) start) (cons (extract (car l) end)
                                                                              (cons (extract (car l) binder-start) (cons (extract (car l) binder-end) (go (cdr l))))))))))
                                           (go (extract a refs))))
                                   (extract a problem)
                                   (int->string (extract a problem-at))))))
        ((string=? w "complete")
         (let* ((prefix (s7-field f 0))
                (k (string-length prefix))
                (names (letrec ((go (subr s7-drive-eff ((listof s7-ns-entry acyclic) s7-strings) s7-strings)
                                  (lambda (l acc)
                                    (if (null? l) acc
                                        (let ((n (symbol->string (extract (car l) name))))
                                          (go (cdr l)
                                              (if (and (>= (string-length n) k) (string=? (substring n 0 k) prefix)
                                                       (not (char=? (string-ref n 0) #\space)) (not (char=? (string-ref n 0) #\%))
                                                       (tagcase (get (extract (extract (car l) cell) value)) (undef u (tagcase (get (extract (extract (car l) cell) syntax)) (none v #f) (else z #t))) (else y #t))
                                                       (not (member? n acc string=?)))
                                                  (cons n acc) acc)))))))
                         (go (append (s7-ns-entries s7-toplevel) (s7-ns-entries s7-builtins)) nil))))
           (s7-answer-fields "completions" (list-sort string<? names))))
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
(define* s7-serve (subr (maxeff s7-drive-eff (io stdout) (io stdin)) () int)
  (lambda ()
    (let ((next (lambda ()
                  (tagcase (read-line)
                    (line l (begin (s7-serve-request! l) #t))
                    (else y #f)))))
      (if (s7-busy?)
          (begin (s7-serve-slice!)
            (if (stdin-ready?) (if (next) (s7-serve) 0) (s7-serve)))
          (if (next) (s7-serve) 0)))))

"Options first -- `-L DIR`, a directory libraries are looked for in --
then the files; or the REPL, if there are none."
(define* s7-options (subr (maxeff s7-drive-eff (io stdout) (io stdin) (read @a)) ((listof string @a)) int)
  (lambda (as)
    (cond ((null? as) (s7-repl ""))
          ((and (string=? (car as) "-L") (pair? (cdr as)))
           (begin (s7-add-library-directory! (let ((d (car (cdr as))))
                                                (if (char=? (string-ref d (- (string-length d) 1)) #\/) d (string-append d "/"))))
             (s7-options (cdr (cdr as)))))
          (else (s7-run-files as)))))

(define* main (subr (maxeff s7-drive-eff (io stdout) (io stdin) (io args) (alloc @a) (read @a)) () int)
  (lambda ()
    (let ((as (the (listof string @a) (args)))
          (why (s7-init!)))
      (cond ((and (pair? as) (string=? (car as) "--serve")) (begin (s7-answer "ready" why) (s7-serve)))
            ((not (string=? why "")) (begin (s7-say (string-append "s7st: " why "\n")) 2))
            (else (s7-options as))))))
