;;; serve.fx: combo as a server (`bin/combo --serve`), for a client such as
;;; the editor: requests on standard input, answers on standard output, a
;;; line each, as s7st's and the CFA's servers have them: a word, a space,
;;; then fields separated by tabs, each with its backslashes, newlines and
;;; tabs escaped (\\, \n, \t).
;;;
;;; A server keeps SMT-LIB2 sessions by name, each with its own assertions,
;;; declarations and solver; terms are shared by all.
;;;
;;; Requests:
;;;   smt NAME TEXT       TEXT, SMT-LIB2 commands, for session NAME (made if
;;;                       there is none); its commands are run as far as
;;;                       TEXT completes them
;;;   close NAME          session NAME forgotten
;;; Answers:
;;;   ready               the server has started
;;;   smt NAME OUTPUT STATUS
;;;                       a `smt`'s answer: what the commands answered, as
;;;                       z3 would; STATUS `more` (it waits for more text),
;;;                       `exit` (an exit command ran: the session is
;;;                       forgotten), or `stop` (a syntax error: it is too)
;;;   closed NAME         a `close`'s answer

(module-parameters ((m-sat (load-moduleof "sat.fx")) (m-rat (load-moduleof "rat.fx"))
                    (m-term (load-moduleof "term.fx" m-sat m-rat))
                    (m-bv (load-moduleof "bv.fx" m-sat m-rat m-term))
                    (m-arith (load-moduleof "arith.fx" m-sat m-rat m-term))
                    (m-eval (load-moduleof "eval.fx" m-sat m-rat m-term))
                    (m-simplex (load-moduleof "simplex.fx" m-sat m-rat))
                    (m-blast (load-moduleof "blast.fx" m-sat m-rat m-term m-bv m-arith m-eval m-simplex))
                    (m-sexp (load-moduleof "sexp.fx" m-sat m-rat))
                    (m-smt (load-moduleof "smt.fx" m-sat m-rat m-term m-bv m-arith m-eval m-simplex m-blast))
                    (m-smtlib (load-moduleof "smtlib.fx" m-sat m-rat m-term m-bv m-arith m-eval m-simplex m-blast m-sexp m-smt))))
(hide (define kit-strings (load-module "../kit/strings.fx"))
      (import kit-strings reverse-list->string))

(define-effect serve-eff (maxeff cb-eff (io stdout) (io stdin)))

(define* serve-say (subr (io stdout) (string) unit) (lambda (s) (tagcase (write-out s) (done u #u) (failed e #u))))

"`s` with backslashes, newlines and tabs escaped."
(define* escape (subr spin (string) string)
  (lambda (s)
    (list->string (letrec ((go (subr spin (int (listof char acyclic)) (listof char acyclic))
                (lambda (i acc)
                  (if (< i 0) acc
                      (let ((c (string-ref s i)))
                        (go (- i 1) (cond ((char=? c #\\) (cons #\\ (cons #\\ acc)))
                                          ((char=? c #\newline) (cons #\\ (cons #\n acc)))
                                          ((char=? c #\tab) (cons #\\ (cons #\t acc)))
                                          (else (cons c acc)))))))))
       (go (- (string-length s) 1) nil)))))
(define* unescape (subr spin (string) string)
  (lambda (s)
    (let ((n (string-length s)))
      (letrec ((go (subr spin (int (listof char acyclic)) (listof char acyclic))
                 (lambda (i acc)
                   (cond ((>= i n) acc)
                         ((and (char=? (string-ref s i) #\\) (< (+ i 1) n))
                          (let ((c (string-ref s (+ i 1))))
                            (go (+ i 2) (cons (cond ((char=? c #\n) #\newline) ((char=? c #\t) #\tab) (else c)) acc))))
                         (else (go (+ i 1) (cons (string-ref s i) acc)))))))
        (reverse-list->string (go 0 nil))))))

"A request's word, and its fields, unescaped."
(define-type request (productof (word string) (fields strings)))
(define* parse-request (subr spin (string) request)
  (lambda (line)
    (let* ((n (string-length line))
           (sp (letrec ((go (subr spin (int) int) (lambda (i) (cond ((>= i n) -1) ((char=? (string-ref line i) #\space) i) (else (go (+ i 1)))))))
                 (go 0)))
           (word (if (< sp 0) line (substring line 0 sp)))
           (rest (if (< sp 0) "" (substring line (+ sp 1) n))))
      (letrec ((split (subr spin (int int strings) strings)
                 (lambda (i start acc)
                   (cond ((>= i (string-length rest)) (reverse (cons (unescape (substring rest start i)) acc)))
                         ((char=? (string-ref rest i) #\tab) (split (+ i 1) (+ i 1) (cons (unescape (substring rest start i)) acc)))
                         (else (split (+ i 1) start acc))))))
        (product (word word) (fields (if (< sp 0) nil (split 0 0 nil))))))))
(define* field (subr spin (strings int) string)
  (lambda (l i) (cond ((null? l) "") ((= i 0) (car l)) (else (field (cdr l) (- i 1))))))
"An answer whose fields are `fields`, each escaped, separated by tabs."
(define* answer (subr (maxeff spin (io stdout)) (string strings) unit)
  (lambda (word fields)
    (letrec ((join (subr spin (strings) string)
               (lambda (l) (cond ((null? l) "") ((null? (cdr l)) (escape (car l)))
                                 (else (string-append (escape (car l)) (string-append "\t" (join (cdr l)))))))))
      (serve-say (string-append word (string-append " " (string-append (join fields) "\n")))))))

;;; ------------------------------------------------------------ sessions

(define-type named-session (productof (name string) (session session) (reader sexp-reader)))
(hide (define sessions (ref (listof named-session acyclic) @cb) (new nil)))

(define* find-session (subr cb-eff (string) named-session)
  (lambda (name)
    (letrec ((go (subr cb-eff ((listof named-session acyclic)) named-session)
               (lambda (l)
                 (cond ((null? l)
                        (let ((ns (product (name name) (session (make-session)) (reader (make-sexp-reader)))))
                          (begin (set sessions (cons ns (get sessions))) ns)))
                       ((string=? (extract (car l) name) name) (car l))
                       (else (go (cdr l)))))))
      (go (get sessions)))))
(define* forget-session! (subr cb-eff (string) unit)
  (lambda (name)
    (set sessions (letrec ((go (subr cb-eff ((listof named-session acyclic)) (listof named-session acyclic))
                             (lambda (l) (cond ((null? l) nil) ((string=? (extract (car l) name) name) (cdr l)) (else (cons (car l) (go (cdr l))))))))
                    (go (get sessions))))))

"Request `line` done."
(define* serve-request! (subr serve-eff (string) unit)
  (lambda (line)
    (let* ((r (parse-request line)) (w (extract r word)) (f (extract r fields)))
      (cond
       ((string=? w "smt")
        (let* ((name (field f 0)) (ns (find-session name)) (s (extract ns session)))
          (begin
            (sexp-feed! (extract ns reader) (field f 1))
            (let* ((status (smtlib-run! s (extract ns reader))) (out (session-take-output! s)))
              (begin
                (session-take-errors! s)
                (if (= status run-more) #u (forget-session! name))
                (answer "smt" (list name out (cond ((= status run-more) "more") ((= status run-end) "exit") (else "stop")))))))))
       ((string=? w "close") (begin (forget-session! (field f 0)) (answer "closed" (list (field f 0)))))
       (else #u)))))

"The server: requests read and answered until the input ends."
(define* serve (subr serve-eff () int)
  (lambda ()
    (begin
      (answer "ready" nil)
      (letrec ((go (subr serve-eff () int)
                 (lambda () (tagcase (read-line) (line l (begin (serve-request! l) (go))) (else y 0)))))
        (go)))))
