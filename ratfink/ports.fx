;;; ports.fx: textual ports, for checked programs: shakedown's
;;; `(shakedown ports)`.
;;;
;;; Ports are of concrete text. An input port is the text and a cell
;;; holding the position; a string output port, a cell holding the strings
;;; written, latest first; the console writes to standard output as
;;; evaluation goes (so on every path it runs on). The cells are stored
;;; into as the store logs (so joins undo and merge them) but not watched:
;;; a contract or a loop may read and write ports. A file opened for input
;;; is read whole when opened, relative to the current directory; files are
;;; not written. Reading at a symbolic position is unsupported, and so is
;;; writing a symbolic value to a string port.

(module-parameters ((m-core (load-moduleof "core.fx")) (m-term (load-moduleof "term.fx" m-core))
                    (m-value (load-moduleof "value.fx" m-core m-term))
                    (m-print (load-moduleof "print.fx" m-core))
                    (m-syntax (load-moduleof "syntax.fx" m-core m-print))
                    (m-numbers (load-moduleof "numbers.fx" m-core))
                    (m-reader (load-moduleof "reader.fx" m-core m-numbers))
                    (m-machine (load-moduleof "machine.fx" m-core m-term m-value))
                    (m-prims (load-moduleof "prims.fx" m-core m-term m-value m-print m-syntax m-numbers m-reader m-machine))
                    (m-hashtables (load-moduleof "hashtables.fx" m-core m-term m-value m-print m-syntax m-numbers m-reader m-machine m-prims))))

(hide (define kit-lists (load-module "../kit/lists.fx"))
      (import kit-lists map))

(define make-port (subr rf-st (symbol string rf-slots) rf-value)
  (lambda (kind text cell) (sum port (product (kind kind) (text text) (cell cell)))))
(define new-cell2 (subr rf-st (rf-value rf-value) rf-slots)
  (lambda (a b) (let ((c (the rf-slots (make-array 2 a)))) (begin (array-set! c 1 b) c))))
(define console rf-value (make-port 'console "" (new-cell2 rf-nil rf-true)))
(define input-port (subr rf-st (string) rf-value)
  (lambda (text) (make-port 'input text (note-allocation! (new-cell2 (rf-int 0) rf-true)))))
(define output-port (subr rf-st () rf-value)
  (lambda () (make-port 'output "" (note-allocation! (new-cell2 rf-nil rf-true)))))
(define port-of (subr rf-st (rf-value) rf-port)
  (lambda (v) (tagcase v (port p p) (else x (product (kind 'none) (text "") (cell no-slots))))))
(define port-kind-is? (subr rf-st (rf-value symbols) bool)
  (lambda (v kinds) (tagcase v (port p (symbols-member? (extract p kind) kinds)) (else x #f))))

"Whether v is concrete through and through, so Larceny can write it."
(define concrete? (subr rf-st (rf-value) bool)
  (lambda (v)
    (tagcase v
      (term t #f) (union u #f) (choice c #f) (closure c #f) (prim p #f) (unspec u #f) (multiple m #f) (inst i #f)
      (pair p (and (concrete? (array-ref p 0)) (concrete? (array-ref p 1))))
      (vec a (letrec ((loop (subr rf-st (int) bool) (lambda (i) (or (= i (array-length a)) (and (concrete? (array-ref a i)) (loop (+ i 1)))))))
               (loop 0)))
      (else x #t))))

"The text of v as display (display? true) or write writes it."
(define render (subr rf-eff (rf-value bool) string)
  (lambda (v display?)
    (if (concrete? v)
        (datum-text v display? #t host-record-text)
        (show v))))

"The text of a file, or none."
(define whole-file (subr rf-eff (string) (sumof (none unit) (some string))) (lambda (f) (file-text f)))

"The primitives, newest first; apply-value applies a procedure value."
(define port-primitives (subr rf-st (applier) prim-entries)
  (lambda (apply-value)
    (let ((prims (the (ref prim-entries @rf) (new nil)))
          ;; The current input and output ports: cells.
          (current-input (the rf-slots (make-array 1 (input-port ""))))
          (current-output (the rf-slots (make-array 1 console))))
      (letrec ((define! (subr rf-st (symbol arity prim-body) unit)
                 (lambda (name arity proc)
                   (set prims (cons (product (name name) (value (make-checked-prim name arity proc))) (get prims)))))
               ;; (k ctx port) for the port argument (args' nth, or the
               ;; current one of current), of one of the kinds and open.
               (with-port (subr rf-eff (rf-ctx rf-value rf-vals int rf-slots symbols (subr rf-eff (rf-ctx rf-value) rf-value)) rf-value)
                 (lambda (ctx src args n current kinds k)
                   (lift ctx (if (> (list-length args) n) (list (vals-ref args n)) (list (array-ref current 0)))
                         (lambda ((ctx rf-ctx) (ps rf-vals))
                           (let ((p (car ps)))
                             (begin
                               (if (port-kind-is? p kinds) #u
                                   (fail! ctx 'error (describe-call src (if (symbols-member? 'input kinds)
                                                                            "argument is not an input port"
                                                                            "argument is not an output port"))))
                               (if (rf-true? (array-ref (extract (port-of p) cell) 1)) #u
                                   (fail! ctx 'error (describe-call src "the port is closed")))
                               (k ctx p)))))))
               ;; The position of input port p, which must be concrete.
               (position (subr rf-eff (rf-ctx rf-value rf-value) int)
                 (lambda (ctx src p)
                   (let ((i (array-ref (extract (port-of p) cell) 0)))
                     (begin (if (rf-exact-integer? i) #u (fail! ctx 'unsupported (describe-call src "reading a port at a symbolic position")))
                            (rf-int-of i)))))
               (advance! (subr rf-st (rf-value int) unit) (lambda (p i) (store! (extract (port-of p) cell) 0 (rf-int i))))
               (emit! (subr rf-eff (rf-value string) rf-value)
                 (lambda (p text)
                   (begin
                     (if (eq? (extract (port-of p) kind) 'console)
                         (tagcase (write-out text) (done u #u) (failed e #u))
                         (store! (extract (port-of p) cell) 0 (rf-cons (rf-str text) (array-ref (extract (port-of p) cell) 0))))
                     rf-unspecified)))
               ;; (k ctx text) for each string a string argument can be.
               (text-of (subr rf-eff (rf-ctx rf-value rf-value string (subr rf-eff (rf-ctx string) rf-value)) rf-value)
                 (lambda (ctx src v what k)
                   (lift ctx (list v)
                         (lambda ((ctx rf-ctx) (vs rf-vals))
                           (begin (if (rf-string? (car vs)) #u (fail! ctx 'error (describe-call src (string-append "argument is not " what))))
                                  (k ctx (rf-str-of (car vs))))))))
               ;; (k ctx text) with the text of the file a name argument names.
               (read-file-text (subr rf-eff (rf-ctx rf-value rf-value (subr rf-eff (rf-ctx string) rf-value)) rf-value)
                 (lambda (ctx src name k)
                   (text-of ctx src name "a file name"
                            (lambda ((ctx rf-ctx) (file string))
                              (tagcase (whole-file file)
                                (some text (k ctx text))
                                (none u (begin (fail! ctx 'error (describe-call src (string-append "no such file: " file))) rf-unspecified)))))))
               ;; (thunk) with cell (a current port) holding p.
               (with-current (subr rf-eff (rf-slots rf-value (subr rf-eff () rf-value)) rf-value)
                 (lambda (cell p thunk)
                   (let ((old (array-ref cell 0)))
                     (begin
                       (store! cell 0 p)
                       (let ((r (rf-protect (lambda () (rewinding cell 0 old thunk)) (lambda () (store! cell 0 old)))))
                         (begin (store! cell 0 old) r))))))
               (char-at (subr rf-eff (rf-ctx rf-value rf-vals bool) rf-value)
                 (lambda (ctx src args advance?)
                   (with-port ctx src args 0 current-input (list 'input)
                              (lambda ((ctx rf-ctx) (p rf-value))
                                (let ((i (position ctx src p)) (text (extract (port-of p) text)))
                                  (if (>= i (string-length text)) rf-eof
                                      (begin (if advance? (advance! p (+ i 1)) #u)
                                             (sum char (string-ref text i)))))))))
               ;; (name x [port]) writing (render x).
               (writer (subr rf-st (symbol bool bool) unit)
                 (lambda (name display? char-only?)
                   (define! name (between 1 2)
                     (lambda ((ctx rf-ctx) (src rf-value) (args rf-vals))
                       (with-port ctx src args 1 current-output (list 'output 'console)
                                  ;; A union is written as one (see show).
                                  (lambda ((ctx rf-ctx) (p rf-value))
                                    (let ((v (car args)))
                                      (begin
                                        (if (and char-only? (not (rf-char? v)))
                                            (fail! ctx 'error (describe-call src "argument is of the wrong type"))
                                            #u)
                                        (if (and (eq? (extract (port-of p) kind) 'output) (not (concrete? v)))
                                            (fail! ctx 'unsupported (describe-call src "a symbolic value written to a string port"))
                                            #u)
                                        (emit! p (render v display?))))))))))
               (closer (subr rf-st (symbol symbols) unit)
                 (lambda (name kinds)
                   (define! name (exactly 1)
                     (lambda ((ctx rf-ctx) (src rf-value) (args rf-vals))
                       (lift ctx args
                             (lambda ((ctx rf-ctx) (ps rf-vals))
                               (let ((p (car ps)))
                                 (begin
                                   (if (port-kind-is? p kinds) #u (fail! ctx 'error (describe-call src "argument is not a port")))
                                   (if (eq? (extract (port-of p) kind) 'console) #u (store! (extract (port-of p) cell) 1 rf-false))
                                   rf-unspecified))))))))
               (predicate (subr rf-st (symbol (subr rf-st (rf-value) bool)) unit)
                 (lambda (name p)
                   (define! name (exactly 1)
                     (lambda ((ctx rf-ctx) (src rf-value) (args rf-vals))
                       (merge-members (map (lambda ((m rf-member)) (member (extract m g) (rf-bool (p (extract m v)))))
                                           (guarded-members rf-true (car args)))))))))
        (begin
          ;;; Input
          (define! 'open-input-string (exactly 1)
            (lambda ((ctx rf-ctx) (src rf-value) (args rf-vals))
              (text-of ctx src (car args) "a string" (lambda ((ctx rf-ctx) (text string)) (input-port text)))))
          (define! 'open-input-file (exactly 1)
            (lambda ((ctx rf-ctx) (src rf-value) (args rf-vals))
              (read-file-text ctx src (car args) (lambda ((ctx rf-ctx) (text string)) (input-port text)))))
          (define! 'call-with-input-file (exactly 2)
            (lambda ((ctx rf-ctx) (src rf-value) (args rf-vals))
              (read-file-text ctx src (car args)
                              (lambda ((ctx rf-ctx) (text string)) (apply-value ctx (car (cdr args)) (list (input-port text)) src)))))
          (define! 'with-input-from-file (exactly 2)
            (lambda ((ctx rf-ctx) (src rf-value) (args rf-vals))
              (read-file-text ctx src (car args)
                              (lambda ((ctx rf-ctx) (text string))
                                (with-current current-input (input-port text)
                                              (lambda () (apply-value ctx (car (cdr args)) nil src)))))))
          (define! 'current-input-port (exactly 0) (lambda ((ctx rf-ctx) (src rf-value) (args rf-vals)) (array-ref current-input 0)))
          (define! 'read-char (between 0 1) (lambda ((ctx rf-ctx) (src rf-value) (args rf-vals)) (char-at ctx src args #t)))
          (define! 'peek-char (between 0 1) (lambda ((ctx rf-ctx) (src rf-value) (args rf-vals)) (char-at ctx src args #f)))
          (define! 'char-ready? (between 0 1)
            (lambda ((ctx rf-ctx) (src rf-value) (args rf-vals))
              (with-port ctx src args 0 current-input (list 'input) (lambda ((ctx rf-ctx) (p rf-value)) rf-true))))
          (define! 'read-line (between 0 1)
            (lambda ((ctx rf-ctx) (src rf-value) (args rf-vals))
              (with-port ctx src args 0 current-input (list 'input)
                         (lambda ((ctx rf-ctx) (p rf-value))
                           (let* ((i (position ctx src p)) (text (extract (port-of p) text)) (n (string-length text)))
                             (if (>= i n) rf-eof
                                 (letrec ((loop (subr rf-eff (int) rf-value)
                                            (lambda (j)
                                              (cond ((= j n) (begin (advance! p j) (rf-str (substring text i j))))
                                                    ((char=? (string-ref text j) #\newline) (begin (advance! p (+ j 1)) (rf-str (substring text i j))))
                                                    (else (loop (+ j 1)))))))
                                   (loop i))))))))
          (define! 'read-string (between 1 2)
            (lambda ((ctx rf-ctx) (src rf-value) (args rf-vals))
              (let ((k (car args)))
                (begin
                  (if (rf-exact-integer? k) #u (fail! ctx 'unsupported (describe-call src "a symbolic count")))
                  (with-port ctx src args 1 current-input (list 'input)
                             (lambda ((ctx rf-ctx) (p rf-value))
                               (let* ((i (position ctx src p)) (text (extract (port-of p) text))
                                      (j (min (string-length text) (+ i (rf-int-of k)))))
                                 (if (and (= i j) (> (rf-int-of k) 0)) rf-eof
                                     (begin (advance! p j) (rf-str (substring text i j)))))))))))
          ;;; Output
          (define! 'open-output-string (exactly 0) (lambda ((ctx rf-ctx) (src rf-value) (args rf-vals)) (output-port)))
          (define! 'get-output-string (exactly 1)
            (lambda ((ctx rf-ctx) (src rf-value) (args rf-vals))
              (lift ctx args
                    (lambda ((ctx rf-ctx) (ps rf-vals))
                      (let ((p (car ps)))
                        (begin
                          (if (port-kind-is? p (list 'output)) #u (fail! ctx 'error (describe-call src "argument is not a string output port")))
                          ;; After joins, the list may be a union, in its tail and its elements.
                          (spine ctx src (array-ref (extract (port-of p) cell) 0)
                                 (lambda ((ctx rf-ctx) (strings rf-vals))
                                   (lift ctx strings
                                         (lambda ((ctx rf-ctx) (ss rf-vals))
                                           (rf-str (strings-concat (map (lambda ((s rf-value)) (rf-str-of s)) (vals-reverse ss))))))))))))))
          (define! 'current-output-port (exactly 0) (lambda ((ctx rf-ctx) (src rf-value) (args rf-vals)) (array-ref current-output 0)))
          (define! 'current-error-port (exactly 0) (lambda ((ctx rf-ctx) (src rf-value) (args rf-vals)) console))
          (writer 'display #t #f)
          (writer 'write #f #f)
          (writer 'write-shared #f #f)
          (writer 'write-simple #f #f)
          (writer 'write-char #t #t)
          (define! 'write-string (between 1 4)
            (lambda ((ctx rf-ctx) (src rf-value) (args rf-vals))
              (text-of ctx src (car args) "a string"
                       (lambda ((ctx rf-ctx) (s string))
                         (with-port ctx src args 1 current-output (list 'output 'console)
                                    (lambda ((ctx rf-ctx) (p rf-value))
                                      (emit! p (if (> (list-length args) 2)
                                                   (substring s (rf-int-of (vals-ref args 2))
                                                              (if (> (list-length args) 3) (rf-int-of (vals-ref args 3)) (string-length s)))
                                                   s))))))))
          (define! 'newline (between 0 1)
            (lambda ((ctx rf-ctx) (src rf-value) (args rf-vals))
              (with-port ctx src args 0 current-output (list 'output 'console) (lambda ((ctx rf-ctx) (p rf-value)) (emit! p "\n")))))
          (define! 'flush-output-port (between 0 1)
            (lambda ((ctx rf-ctx) (src rf-value) (args rf-vals))
              (with-port ctx src args 0 current-output (list 'output 'console) (lambda ((ctx rf-ctx) (p rf-value)) rf-unspecified))))
          ;;; Either
          (closer 'close-port (list 'input 'output 'console))
          (closer 'close-input-port (list 'input))
          (closer 'close-output-port (list 'output 'console))
          (define! 'call-with-port (exactly 2)
            (lambda ((ctx rf-ctx) (src rf-value) (args rf-vals))
              (let ((r (apply-value ctx (car (cdr args)) (list (car args)) src)))
                (begin
                  (lift ctx (list (car args))
                        (lambda ((ctx rf-ctx) (ps rf-vals))
                          (begin
                            (if (and (port-kind-is? (car ps) (list 'input 'output)))
                                (store! (extract (port-of (car ps)) cell) 1 rf-false)
                                #u)
                            rf-unspecified)))
                  r))))
          (predicate 'port? (lambda ((v rf-value)) (port-kind-is? v (list 'input 'output 'console))))
          (predicate 'input-port? (lambda ((v rf-value)) (port-kind-is? v (list 'input))))
          (predicate 'output-port? (lambda ((v rf-value)) (port-kind-is? v (list 'output 'console))))
          (predicate 'textual-port? (lambda ((v rf-value)) (port-kind-is? v (list 'input 'output 'console))))
          (predicate 'binary-port? (lambda ((v rf-value)) #f))
          (predicate 'input-port-open? (lambda ((v rf-value)) (and (port-kind-is? v (list 'input)) (rf-true? (array-ref (extract (port-of v) cell) 1)))))
          (predicate 'output-port-open? (lambda ((v rf-value)) (and (port-kind-is? v (list 'output 'console)) (rf-true? (array-ref (extract (port-of v) cell) 1)))))
          (predicate 'eof-object? rf-eof?)
          (define! 'eof-object (exactly 0) (lambda ((ctx rf-ctx) (src rf-value) (args rf-vals)) rf-eof))
          (get prims))))))
