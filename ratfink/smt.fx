;;; smt.fx: talking to an SMT solver in SMT-LIB2: shakedown's
;;; `(shakedown smt)`.
;;;
;;; The solver runs as a separate process (z3 -in by default; --solver-command
;;; gives another command, as shakedown's SHAKEDOWN_SOLVER does, and
;;; bin/ratfink passes RATFINK_SOLVER so). If a log file is given
;;; (RATFINK_SMT_LOG, through bin/ratfink), what is sent is copied to it.
;;; shakedown talks to the process through two FIFOs; FX-26 starts one with
;;; pipes, its output (standard output and error, one stream) read as it
;;; comes.
;;;
;;; Terms are sent as a DAG: each compound term is defined once, with
;;; define-fun, and referred to by name after that. A pop forgets the
;;; definitions made since the push, so the solver keeps a list of them for
;;; each push.
;;;
;;; z3 does not always keep to its :timeout. shakedown's watchdog stops the
;;; process when a check goes on 5 seconds past the timeout; here the wait
;;; for the answer has that deadline, and stops the process itself.
;;;
;;; A solver, to check.fx, is a record of procedures (`solver`), so that
;;; the in-process one (combo, solver-combo.fx) is one too.

(module-parameters ((m-core (load-moduleof "core.fx")) (m-term (load-moduleof "term.fx" m-core))
                    (m-print (load-moduleof "print.fx" m-core))
                    (m-numbers (load-moduleof "numbers.fx" m-core))
                    (m-reader (load-moduleof "reader.fx" m-core m-numbers))))

"A solver: what check.fx asks of one. check answers 'sat, 'unsat or
'unknown; values, after sat, the value of each term."
(define-type solver
  (productof (declare! (subr rf-eff (rf-value) unit))
             (assert! (subr rf-eff (rf-value) unit))
             (push! (subr rf-eff () unit))
             (pop! (subr rf-eff () unit))
             (check (subr rf-eff () symbol))
             (values (subr rf-eff (rf-vals) rf-vals))
             (reset! (subr rf-eff () unit))
             (stop! (subr rf-eff () unit))))

;;; ------------------------------------------------------------ the process

(define-type history-entry (productof (assert? bool) (term rf-value)))
(define-type z3-state
  (productof (command strings) (z3? bool) (options strings) (timeout int)
             (pid (ref int @rf)) (buffer (ref string @rf))
             (defined (ref (table int bool @rf) @rf))
             (scopes (ref (listof ints acyclic) @rf))
             (history (ref (listof history-entry acyclic) @rf))
             (lost-scopes (ref int @rf))
             (checks (ref int @rf))
             (log (ref strings @rf)) (log-file string)))

(define solver-command (ref string @rf) (new "z3 -in"))
(define smt-log-file (ref string @rf) (new ""))
(define set-solver-command! (subr rf-st (string) unit) (lambda (c) (set solver-command c)))
(define set-smt-log-file! (subr rf-st (string) unit) (lambda (f) (set smt-log-file f)))

(define smt-fail (subr rf-eff (string) void) (lambda (m) (rf-error m nil)))
(define stopped-message string "The SMT solver stopped (is z3 installed? see RATFINK_SOLVER)")

(define smt-send (subr rf-eff (z3-state string) unit)
  (lambda (s text)
    (begin
      (tagcase (process-write (get (extract s pid)) (string-append text "\n")) (done u #u) (failed e #u))
      (if (string=? (extract s log-file) "") #u
          (set (extract s log) (cons (string-append text "\n") (get (extract s log))))))))

"Write the log so far (the file is written whole)."
(define flush-log (subr rf-eff (z3-state) unit)
  (lambda (s)
    (if (string=? (extract s log-file) "") #u
        (tagcase (write-file (extract s log-file) (the (bytevectorof @rf) (string->utf8 (strings-concat (the strings (reverse (get (extract s log))))))))
          (done u #u) (failed e #u)))))

(define now-ms (subr rf-eff () int) (lambda () (quotient (i64->int (clock)) 1000000)))
(define pause (subr rf-eff (int) unit) (lambda (us) (sleep-until (i64+ (clock) (int->i64 (* us 1000))))))

"The end of the first datum of text, or -1 if text has no complete one
(only blanks are -2)."
(define datum-end (subr rf-st (string) int)
  (lambda (text)
    (let ((n (string-length text)))
      (letrec ((skip (subr rf-st (int) int) (lambda (i) (if (and (< i n) (char-whitespace? (string-ref text i))) (skip (+ i 1)) i)))
               (atom (subr rf-st (int) int)
                 (lambda (i) (cond ((>= i n) -1)
                                   ((or (char-whitespace? (string-ref text i)) (char=? (string-ref text i) #\() (char=? (string-ref text i) #\))) i)
                                   (else (atom (+ i 1))))))
               (str (subr rf-st (int) int)
                 (lambda (i) (cond ((>= i n) -1)
                                   ((char=? (string-ref text i) #\") (if (and (< (+ i 1) n) (char=? (string-ref text (+ i 1)) #\")) (str (+ i 2)) (+ i 1)))
                                   (else (str (+ i 1))))))
               (lst (subr rf-st (int int) int)
                 (lambda (i depth)
                   (cond ((>= i n) -1)
                         ((char=? (string-ref text i) #\() (lst (+ i 1) (+ depth 1)))
                         ((char=? (string-ref text i) #\)) (if (= depth 1) (+ i 1) (lst (+ i 1) (- depth 1))))
                         ((char=? (string-ref text i) #\") (let ((j (str (+ i 1)))) (if (< j 0) -1 (lst j depth))))
                         (else (lst (+ i 1) depth))))))
        (let ((i (skip 0)))
          (cond ((>= i n) -2)
                ((char=? (string-ref text i) #\() (lst i 0))
                ((char=? (string-ref text i) #\") (str (+ i 1)))
                (else (atom i))))))))

"The process has ended (and its output is read)."
(define exited? (subr rf-eff (int) bool)
  (lambda (pid) (tagcase (process-status pid) (running u #f) (else x #t))))

"The next response; eof (rf-eof) if the process ended; `stopped` (the
symbol) if the deadline (ms, or -1) passed first."
(define read-response (subr rf-eff (z3-state int) rf-value)
  (lambda (s deadline)
    (letrec ((loop (subr rf-eff (int) rf-value)
               (lambda (wait)
                 (let* ((more (process-output (get (extract s pid))))
                        (text (string-append (get (extract s buffer)) more))
                        (end (datum-end text)))
                   (begin
                     (set (extract s buffer) text)
                     (if (>= end 0)
                         (let ((forms (read-text* (substring text 0 end) "z3" #f #f)))
                           (begin (set (extract s buffer) (substring text end (string-length text)))
                                  (if (null? forms) rf-eof (car forms))))
                         (cond ((and (string=? more "") (exited? (get (extract s pid)))) rf-eof)
                               ((and (>= deadline 0) (> (now-ms) deadline)) (rf-sym 'stopped))
                               (else (begin (pause wait) (loop (if (< wait 2000) (* wait 2) wait)))))))))))
      (loop 20))))

"The next response; an error from the solver is signalled."
(define smt-receive (subr rf-eff (z3-state) rf-value)
  (lambda (s)
    (let ((r (read-response s -1)))
      (cond ((rf-eof? r) (begin (smt-fail stopped-message) r))
            ((and (rf-pair? r) (rf-eqv? (rf-car r) (rf-sym 'error)))
             (begin (rf-error "The SMT solver reported an error:" (list (rf-cadr r))) r))
            (else r)))))

(define split-words (subr rf-st (string) strings)
  (lambda (s)
    (letrec ((go (subr rf-st (int int strings) strings)
               (lambda (i start acc)
                 (cond ((>= i (string-length s)) (the strings (reverse (if (> i start) (the strings (cons (substring s start i) acc)) acc))))
                       ((char=? (string-ref s i) #\space) (go (+ i 1) (+ i 1) (if (> i start) (the strings (cons (substring s start i) acc)) acc)))
                       (else (go (+ i 1) start acc))))))
      (go 0 0 nil))))

(define start-process! (subr rf-eff (z3-state) unit)
  (lambda (s)
    (begin
      (tagcase (process-start (extract s command) "")
        (started id (set (extract s pid) id))
        (failed e (smt-fail stopped-message)))
      (set (extract s buffer) "")
      (set (extract s defined) (the (table int bool @rf) (make-table id-hash id-same?)))
      (set (extract s scopes) nil)
      (set (extract s history) nil)
      (set (extract s lost-scopes) 0)
      (for-each (lambda ((o string)) (smt-send s o)) (extract s options)))))

(define stop-process! (subr rf-eff (z3-state) unit)
  (lambda (s) (process-signal (get (extract s pid)) 9)))

"A new process in place of one that was stopped, told what the old one
was told outside any push."
(define replace-process! (subr rf-eff (z3-state) unit)
  (lambda (s)
    (let ((history (the (listof history-entry acyclic) (reverse (get (extract s history)))))
          (open (list-length (get (extract s scopes)))))
      (begin
        (process-close-input (get (extract s pid)))
        (start-process! s)
        (for-each (lambda ((h history-entry)) (if (extract h assert?) (z3-assert! s (extract h term)) (z3-declare! s (extract h term))))
                  history)
        (set (extract s lost-scopes) open)))))

(define remember! (subr rf-st (z3-state history-entry) unit)
  (lambda (s entry)
    (if (and (null? (get (extract s scopes))) (= 0 (get (extract s lost-scopes))))
        (set (extract s history) (cons entry (get (extract s history))))
        #u)))

(define note-defined! (subr rf-st (z3-state rf-value) unit)
  (lambda (s t)
    (begin
      (table-set! (get (extract s defined)) (tid t) #t)
      (let ((scopes (get (extract s scopes))))
        (if (pair? scopes) (set (extract s scopes) (cons (cons (tid t) (car scopes)) (cdr scopes))) #u)))))
(define defined? (subr rf-st (z3-state rf-value) bool) (lambda (s t) (table-ref (get (extract s defined)) (tid t) #f)))

;;; ------------------------------------------------------------ terms in SMT-LIB

(define literal (subr rf-st (rf-value) string)
  (lambda (x)
    (tagcase x
      (bool b (if b "true" "false"))
      (int i (if (< i 0) (string-append "(- " (int->string (- 0 i)) ")") (int->string i)))
      (else y "?"))))
(define term-name (subr rf-st (rf-value) string)
  (lambda (t) (string-append (if (constant? t) "k" "t") (int->string (tid t)))))

"The SMT-LIB text for x, after defining the terms it needs."
(define reference! (subr rf-eff (z3-state rf-value) string)
  (lambda (s x) (if (rf-term? x) (begin (define! s x) (term-name x)) (literal x))))

"Iterative over the DAG, so that a long chain of terms does not nest
deeply."
(define define! (subr rf-eff (z3-state rf-value) unit)
  (lambda (s t)
    (letrec ((loop (subr rf-eff (rf-vals) unit)
               (lambda (stack)
                 (if (null? stack) #u
                     (let ((t (car stack)))
                       (cond ((defined? s t) (loop (cdr stack)))
                             ((constant? t)
                              (begin
                                (note-defined! s t)
                                (if (and (>= (constant-range t) 0) (extract s z3?))
                                    (declare-index! s t (constant-range t))
                                    (smt-send s (string-append "(declare-const " (term-name t) " " (sort-name (term-sort (term-of t))) ")")))
                                (loop (cdr stack))))
                             (else
                              (let ((pending (filter (lambda ((a rf-value)) (and (rf-term? a) (not (defined? s a)))) (targs t))))
                                (if (pair? pending)
                                    (loop (vals-append pending stack))
                                    (begin
                                      (note-defined! s t)
                                      (smt-send s (string-append
                                               "(define-fun " (term-name t) " () " (sort-name (term-sort (term-of t))) " "
                                               (let ((atom (index-atom s t)))
                                                 (if (string=? atom "")
                                                     (string-append "(" (op-name (term-op (term-of t)))
                                                                    (strings-concat (map (lambda ((a rf-value)) (string-append " " (reference! s a))) (targs t)))
                                                                    ")")
                                                     atom))
                                               ")"))
                                      (loop (cdr stack))))))))))))
      (loop (list t)))))

(define index-name (subr rf-st (rf-value int) string)
  (lambda (k i) (string-append (term-name k) "_" (int->string i))))

"An index constant k in [0, n), for z3: n booleans k_0 … of which exactly
one is true, and k defined from them."
(define declare-index! (subr rf-eff (z3-state rf-value int) unit)
  (lambda (s k n)
    (let ((names (letrec ((loop (subr rf-st (int strings) strings) (lambda (i acc) (if (< i 0) acc (loop (- i 1) (cons (index-name k i) acc))))))
                   (loop (- n 1) nil))))
      (begin
        (for-each (lambda ((b string)) (smt-send s (string-append "(declare-const " b " Bool)"))) names)
        (smt-send s (string-append "(assert ((_ pbeq 1" (strings-concat (map (lambda ((b string)) " 1") names)) ")"
                               (strings-concat (map (lambda ((b string)) (string-append " " b)) names)) "))"))
        (smt-send s (string-append "(define-fun " (term-name k) " () Int "
                               (letrec ((loop (subr rf-st (int string) string)
                                          (lambda (i acc) (if (< i 0) acc
                                                              (loop (- i 1) (string-append "(ite " (index-name k i) " " (int->string i) " " acc ")"))))))
                                 (loop (- n 2) (int->string (- n 1))))
                               ")"))))))

"The text for t, a comparison of an index constant with a number, when
declare-index! declared it; else \"\"."
(define index-atom (subr rf-eff (z3-state rf-value) string)
  (lambda (s t)
    (let* ((index? (lambda ((a rf-value)) (and (constant? a) (>= (constant-range a) 0) (extract s z3?))))
           (a (targ1 t)) (b (targ2 t)) (op (term-op (term-of t))))
      (cond ((= op op-eq)
             (if (and (rf-exact-integer? a) (index? b))
                 (if (and (< -1 (rf-int-of a)) (< (rf-int-of a) (constant-range b))) (index-name b (rf-int-of a)) "false")
                 ""))
            ((= op op-le) (if (and (rf-eqv? a (rf-int 0)) (index? b)) "true" ""))
            ((= op op-lt) (if (and (index? a) (rf-exact-integer? b) (>= (rf-int-of b) (constant-range a))) "true" ""))
            (else "")))))

;;; ------------------------------------------------------------ commands

(define z3-declare! (subr rf-eff (z3-state rf-value) unit)
  (lambda (s t) (begin (remember! s (product (assert? #f) (term t))) (reference! s t) #u)))
(define z3-assert! (subr rf-eff (z3-state rf-value) unit)
  (lambda (s f) (begin (remember! s (product (assert? #t) (term f)))
                       (let ((ref (reference! s f))) (smt-send s (string-append "(assert " ref ")"))))))
(define z3-push! (subr rf-eff (z3-state) unit)
  (lambda (s) (begin (smt-send s "(push 1)") (set (extract s scopes) (cons nil (get (extract s scopes)))))))
(define z3-pop! (subr rf-eff (z3-state) unit)
  (lambda (s)
    (if (> (get (extract s lost-scopes)) 0)
        (set (extract s lost-scopes) (- (get (extract s lost-scopes)) 1))
        (begin
          (smt-send s "(pop 1)")
          (for-each (lambda ((i int)) (table-set! (get (extract s defined)) i #f)) (car (get (extract s scopes))))
          (set (extract s scopes) (cdr (get (extract s scopes))))))))
(define z3-reset! (subr rf-eff (z3-state) unit)
  (lambda (s)
    (begin
      (smt-send s "(reset)")
      (for-each (lambda ((o string)) (smt-send s o)) (extract s options))
      (set (extract s defined) (the (table int bool @rf) (make-table id-hash id-same?)))
      (set (extract s scopes) nil)
      (set (extract s history) nil)
      (set (extract s lost-scopes) 0))))

(define string-search? (subr rf-st (string string) bool)
  (lambda (part s)
    (let ((n (string-length part)))
      (letrec ((loop (subr rf-st (int) bool)
                 (lambda (i) (and (<= (+ i n) (string-length s)) (or (string=? (substring s i (+ i n)) part) (loop (+ i 1)))))))
        (loop 0)))))

"Whether the check that answered unknown was stopped by the timeout."
(define interrupted? (subr rf-eff (z3-state) bool)
  (lambda (s)
    (begin
      (smt-send s "(get-info :reason-unknown)")
      (let ((r (smt-receive s)))
        (and (rf-pair? r) (rf-pair? (rf-cdr r)) (rf-string? (rf-cadr r))
             (or (string-search? "timeout" (rf-str-of (rf-cadr r))) (string-search? "cancel" (rf-str-of (rf-cadr r)))))))))

(define z3-check (subr rf-eff (z3-state) symbol)
  (lambda (s)
    (begin
      (set (extract s checks) (+ 1 (get (extract s checks))))
      (smt-send s "(check-sat)")
      (let ((r (read-response s (if (>= (extract s timeout) 0) (+ (now-ms) (* 1000 (+ (extract s timeout) 5))) -1))))
        (cond ((rf-eqv? r (rf-sym 'stopped))
               ;; As shakedown's watchdog: the process stopped, and replaced.
               (begin (stop-process! s) (replace-process! s) 'unknown))
              ((rf-eqv? r (rf-sym 'sat)) 'sat)
              ((rf-eqv? r (rf-sym 'unsat)) 'unsat)
              ;; A z3 that ran out of time cancels the next command too.
              ((rf-eqv? r (rf-sym 'unknown))
               (begin (if (interrupted? s) (begin (stop-process! s) (replace-process! s)) #u) 'unknown))
              ((and (rf-pair? r) (rf-eqv? (rf-car r) (rf-sym 'error)) (rf-string? (rf-cadr r)) (string-search? "canceled" (rf-str-of (rf-cadr r))))
               (begin (stop-process! s) (replace-process! s) 'unknown))
              ((rf-eof? r) (begin (smt-fail stopped-message) 'unknown))
              ((and (rf-pair? r) (rf-eqv? (rf-car r) (rf-sym 'error)))
               (begin (rf-error "The SMT solver reported an error:" (list (rf-cadr r))) 'unknown))
              (else (begin (rf-error "Unexpected answer to check-sat:" (list r)) 'unknown)))))))

(define parse-value (subr rf-st (rf-value) rf-value)
  (lambda (v)
    (cond ((rf-eqv? v (rf-sym 'true)) rf-true)
          ((rf-eqv? v (rf-sym 'false)) rf-false)
          ((rf-exact-integer? v) v)
          ((and (rf-pair? v) (rf-eqv? (rf-car v) (rf-sym '-)) (rf-exact-integer? (rf-cadr v))) (rf-int (- 0 (rf-int-of (rf-cadr v)))))
          (else v))))

(define z3-values (subr rf-eff (z3-state rf-vals) rf-vals)
  (lambda (s terms)
    (if (null? terms) nil
        (let ((names (map (lambda ((t rf-value)) (reference! s t)) terms)))
          (begin
            (smt-send s (string-append "(get-value (" (strings-concat (map (lambda ((n string)) (string-append " " n)) names)) "))"))
            (map2 (lambda ((t rf-value) (entry rf-value)) (parse-value (rf-cadr entry))) terms (rf-elements (smt-receive s))))))))

"Start the solver process. timeout: the limit on each check, in seconds,
or -1."
(define start-z3 (subr rf-eff (int) solver)
  (lambda (timeout)
    (let* ((command (get solver-command))
           (z3? (and (>= (string-length command) 2) (string=? (substring command 0 2) "z3")))
           (options (the strings (append (list "(set-option :print-success false)" "(set-option :produce-models true)")
                            (if (and (>= timeout 0) z3?)
                                (list (string-append "(set-option :timeout " (int->string (* 1000 timeout)) ")"))
                                nil))))
           (s (the z3-state
                (product (command (if (string=? command "z3 -in") (the strings (list "z3" "-in")) (the strings (list "sh" "-c" (string-append "exec " command)))))
                         (z3? z3?) (options options) (timeout timeout)
                         (pid (new -1)) (buffer (new "")) (defined (new (the (table int bool @rf) (make-table id-hash id-same?))))
                         (scopes (new nil)) (history (new nil)) (lost-scopes (new 0)) (checks (new 0))
                         (log (new nil)) (log-file (get smt-log-file))))))
      (begin
        (start-process! s)
        (product (declare! (lambda ((t rf-value)) (z3-declare! s t)))
                 (assert! (lambda ((f rf-value)) (z3-assert! s f)))
                 (push! (lambda () (z3-push! s)))
                 (pop! (lambda () (z3-pop! s)))
                 (check (lambda () (z3-check s)))
                 (values (lambda ((ts rf-vals)) (z3-values s ts)))
                 (reset! (lambda () (z3-reset! s)))
                 (stop! (lambda () (begin (smt-send s "(exit)") (process-close-input (get (extract s pid))) (flush-log s)))))))))
