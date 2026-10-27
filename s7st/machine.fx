;;; machine.fx: the machine -- core run one step at a time.
;;;
;;; A CEK machine (Felleisen and Friedman's; Van Horn and Might's
;;; "Abstracting Abstract Machines" is why it is written so): a state is a
;;; node to evaluate, in an environment, with a continuation; or a value
;;; returned to a continuation; or a procedure applied. The continuation is
;;; data (s7-k), so:
;;;   - every call in tail position runs in constant space;
;;;   - `call/cc` captures it, and a continuation may be resumed any number
;;;     of times, `dynamic-wind`'s thunks run on the way;
;;;   - a client runs the machine in slices (`s7-run`), so a long
;;;     computation does not stop it, and one may be interrupted.
;;; The same states, abstracted, are what a flow analysis would explore
;;; (docs/s7st.md, "Openings").

(define* s7-return-state (subr pure (s7-value s7-k s7-dyn) s7-state)
  (lambda (v k dyn) (sum s-return (product (value v) (k k) (dyn dyn)))))
(define* s7-eval-state (subr pure (s7-node s7-env s7-k s7-dyn) s7-state)
  (lambda (n env k dyn) (sum s-eval (product (node n) (env env) (k k) (dyn dyn)))))
(define* s7-apply-state (subr pure (s7-value s7-values s7-k s7-dyn) s7-state)
  (lambda (f args k dyn) (sum s-apply (product (proc f) (args args) (k k) (dyn dyn)))))
(define* s7-raise-state (subr pure (s7-value bool s7-k s7-dyn) s7-state)
  (lambda (obj continuable k dyn) (sum s-raise (product (obj obj) (continuable continuable) (k k) (dyn dyn)))))
"An error raised: `message`, with `irritants`."
(define* s7-error-state (subr s7-eff (string s7-values s7-k s7-dyn) s7-state)
  (lambda (message irritants k dyn) (s7-raise-state (s7-error-value message irritants) #f k dyn)))
(define* s7-push-k (subr pure (s7-kframe s7-k) s7-k) (lambda (f k) (cons f k)))

"The slots of the frame `depth` out from `env`."
(define* s7-frame-slots (subr spin (s7-env int) (sumof (none unit) (some (arrayof s7-value @sc))))
  (lambda (env depth)
    (tagcase env
      (top u (sum none #u))
      (frame f (if (= depth 0) (sum some (extract f slots)) (s7-frame-slots (extract f up) (- depth 1)))))))
"A fresh frame of `size` slots, undefined, in `env`."
(define* s7-new-frame (subr (alloc @sc) (int s7-env) (productof (slots (arrayof s7-value @sc)) (env s7-env)))
  (lambda (size env)
    (let ((slots (the (arrayof s7-value @sc) (make-array size s7-undefined))))
      (product (slots slots) (env (sum frame (product (slots slots) (up env))))))))

"The value of node `n`, if it can be had with no step of its own: a
constant, a defined variable, a lambda. #f: it needs steps."
(define* s7-simple (subr s7-eff (s7-node s7-env) (union false s7-value))
  (lambda (n env)
    (tagcase (extract n form)
      (n-const v v)
      (n-local l (tagcase (s7-frame-slots env (extract l depth))
                   (some slots (if (< (extract l index) (array-length slots))
                                   (let ((v (array-ref slots (extract l index))))
                                     (tagcase v (undef u #f) (else y y)))
                                   #f))
                   (none u #f)))
      (n-global c (let ((v (get (extract c value)))) (tagcase v (undef u #f) (else y y))))
      (n-lambda cs (sum proc (product (clauses cs) (env env)
                                      (name (the (ref string @sc) (new (if (null? cs) "" (extract (car cs) name))))))))
      (else y #f))))

"A call's operator and arguments evaluated, from `rest` on, as far as
they are simple; then the call made, or the first that is not evaluated."
(define* s7-args (subr s7-eff (s7-values s7-nodes s7-env s7-k s7-dyn) s7-state)
  (lambda (done rest env k dyn)
    (if (null? rest)
        (let ((all (the s7-values (reverse done))))
          (s7-apply-state (car all) (cdr all) k dyn))
        (typecase (s7-simple (car rest) env)
          (bool b (s7-eval-state (car rest) env (s7-push-k (sum k-args (product (done done) (rest (cdr rest)) (env env))) k) dyn))
          (else v (s7-args (cons v done) (cdr rest) env k dyn))))))

"Where an error is, from a span and the text it is in: `file:line:col: `."
(define* s7-where (subr spin (s7-span string) string)
  (lambda (span text)
    (let ((at (extract span start)))
      (if (or (< at 0) (> at (string-length text))) ""
          (letrec ((go (subr spin (int int int) string)
                     ;; From `i`, at line `line`, the line starting at `start`.
                     (lambda (i line start)
                       (cond ((>= i at)
                              (string-append (if (string=? (extract span file) "") "" (string-append (extract span file) ":"))
                                             (int->string line) ":" (int->string (+ 1 (- at start))) ": "))
                             ((char=? (string-ref text i) #\newline) (go (+ i 1) (+ line 1) (+ i 1)))
                             (else (go (+ i 1) line start))))))
            (go 0 1 0))))))

"Top-level form `x` expanded and run, the forms after it then, as `k-top`
says; or, if it has syntax errors, the first raised."
(define* s7-run-form (subr s7-eff (s7-value s7-values bool string s7-k s7-dyn) s7-state)
  (lambda (x more echo text k dyn)
    (begin
      (set s7-syntax-errors nil)
      (let* ((node (s7-expand-top x))
             (errors (reverse (get s7-syntax-errors)))
             (k2 (s7-push-k (sum k-top (product (forms more) (echo echo) (text text))) k)))
        (if (pair? errors)
            (s7-raise-state (sum errobj (product (kind 'syntax)
                                                 (message (string-append (s7-where (extract (car errors) span) text)
                                                                         (extract (car errors) message)))
                                                 (irritants s7-nil)))
                            #f k2 dyn)
            (s7-eval-state node (sum top #u) k2 dyn))))))

(define* s7-drop-winds (subr spin (s7-winds int) s7-winds)
  (lambda (l n) (if (or (<= n 0) (null? l)) l (s7-drop-winds (cdr l) (- n 1)))))
"Each step's thunk run, then `v` returned to `k` in `dyn`."
(define* s7-rewind (subr s7-eff ((listof s7-step acyclic) s7-k s7-dyn s7-value) s7-state)
  (lambda (steps k dyn v)
    (if (null? steps) (s7-return-state v k dyn)
        (s7-apply-state (extract (car steps) thunk) nil
                        (list (sum k-rewind (product (steps (cdr steps)) (k k) (dyn dyn) (value v))))
                        (extract (car steps) dyn)))))

"`v` given to continuation `c`, from the dynamic state `dyn`: each
`dynamic-wind` left run its `after`, each entered its `before`."
(define* s7-throw (subr s7-eff (s7-cont s7-value s7-dyn) s7-state)
  (lambda (c v dyn)
    (let* ((from (extract dyn winds))
           (to (extract (extract c dyn) winds))
           (nf (list-length from))
           (nt (list-length to)))
      (letrec ((common (subr s7-eff (s7-winds s7-winds) int)
                 ;; How many winds `a` and `b`, of a length, share at their ends.
                 (lambda (a b)
                   (cond ((null? a) 0)
                         ((eq? (extract (car a) id) (extract (car b) id)) (list-length a))
                         (else (common (cdr a) (cdr b))))))
               (afters (subr s7-eff (s7-winds int) (listof s7-step acyclic))
                 ;; The `after` of each of `ws` but the last `keep`, innermost first.
                 (lambda (ws keep)
                   (if (<= (list-length ws) keep) nil
                       (cons (product (thunk (extract (car ws) after))
                                      (dyn (product (winds (cdr ws)) (handlers (extract dyn handlers)))))
                             (afters (cdr ws) keep)))))
               (befores (subr s7-eff (s7-winds int (listof s7-step acyclic)) (listof s7-step acyclic))
                 ;; The `before` of each of `ws` but the last `keep`, outermost first.
                 (lambda (ws keep acc)
                   (if (<= (list-length ws) keep) acc
                       (befores (cdr ws) keep
                                (cons (product (thunk (extract (car ws) before))
                                               (dyn (product (winds (cdr ws)) (handlers (extract (extract c dyn) handlers)))))
                                      acc))))))
        (let* ((shared (common (s7-drop-winds from (- nf nt)) (s7-drop-winds to (- nt nf))))
               (steps (append (afters from shared) (befores to shared nil))))
          (s7-rewind steps (extract c k) (extract c dyn) v))))))
"What `values` gives of `l`: the one value, or several."
(define* s7-values-of (subr pure (s7-values) s7-value)
  (lambda (l) (if (and (pair? l) (null? (cdr l))) (car l) (sum multi l))))
"The values a value stands for: several, or itself."
(define* s7-values-in (subr pure (s7-value) s7-values)
  (lambda (v) (tagcase v (multi l l) (else y (list v)))))

"The machine's own operation `op` (prims.fx), on `args`."
(define* s7-control (subr s7-eff (int s7-values s7-k s7-dyn) s7-state)
  (lambda (op args k dyn)
    (let ((a1 (if (pair? args) (car args) s7-undefined))
          (a2 (s7-arg2 args))
          (a3 (s7-arg3 args)))
      (cond
        ((= op s7-op-apply)
         (letrec ((spread (subr s7-eff (s7-values) (sumof (ok s7-values) (bad unit)))
                    ;; The arguments but the last, then the last's items.
                    (lambda (l)
                      (cond ((null? l) (sum ok nil))
                            ((null? (cdr l)) (tagcase (s7-list-items (car l)) (some items (sum ok items)) (none u (sum bad #u))))
                            (else (tagcase (spread (cdr l)) (ok rest (sum ok (cons (car l) rest))) (bad u (sum bad #u))))))))
           (tagcase (spread (cdr args))
             (ok l (s7-apply-state a1 l k dyn))
             (bad u (s7-error-state "apply: its last argument is no list" (list (s7-list args)) k dyn)))))
        ((= op s7-op-call/cc)
         (s7-apply-state a1 (list (sum cont (product (k k) (dyn dyn) (id (the (ref unit @sc) (new #u)))))) k dyn))
        ((= op s7-op-values) (s7-return-state (s7-values-of args) k dyn))
        ((= op s7-op-call-with-values) (s7-apply-state a1 nil (s7-push-k (sum k-cwv a2) k) dyn))
        ((= op s7-op-dynamic-wind)
         (s7-apply-state a1 nil (s7-push-k (sum k-dw-before (product (before a1) (thunk a2) (after a3))) k) dyn))
        ((= op s7-op-with-exception-handler)
         (s7-apply-state a2 nil (s7-push-k (sum k-restore dyn) k)
                         (product (winds (extract dyn winds)) (handlers (cons a1 (extract dyn handlers))))))
        ((= op s7-op-raise) (s7-raise-state a1 #f k dyn))
        ((= op s7-op-raise-continuable) (s7-raise-state a1 #t k dyn))
        ((= op s7-op-eval) (s7-run-form a1 nil #f "" k dyn))
        ((= op s7-op-load)
         (tagcase a1
           (str s (tagcase (s7-file-text (get s))
                    (text t (tagcase (s7-read-all t (get s))
                              (data forms (s7-return-state s7-unspecified
                                                           (s7-push-k (sum k-top (product (forms forms) (echo #f) (text t))) k) dyn))
                              (stop r (s7-raise-state (sum errobj (product (kind 'read) (message (string-append "load: cannot read " (get s)))
                                                                           (irritants s7-nil)))
                                                      #f k dyn))))
                    (failed m (s7-raise-state (sum errobj (product (kind 'file) (message (string-append "load: " m)) (irritants s7-nil))) #f k dyn))))
           (else y (s7-error-state "load: not a file name" (list y) k dyn))))
        ((= op s7-op-exit) (sum s-done (if (pair? args) a1 s7-unspecified)))
        (else (s7-error-state "no such operation" nil k dyn))))))

"Arguments `args` put in `slots` from `i`: `r` of them, then the rest as a
list if `rest`."
(define* s7-fill-params (subr s7-eff ((arrayof s7-value @sc) s7-values int int bool) unit)
  (lambda (slots args i r rest)
    (cond ((< i r) (if (pair? args) (begin (array-set! slots i (car args)) (s7-fill-params slots (cdr args) (+ i 1) r rest)) #u))
          (rest (if (< i (array-length slots)) (array-set! slots i (s7-list args)) #u))
          (else #u))))
(define* s7-proc-name (subr (read @sc) (s7-value) string)
  (lambda (f)
    (tagcase f
      (proc c (let ((n (get (extract c name)))) (if (string=? n "") "a procedure" n)))
      (prim p (extract p name))
      (else y "a procedure"))))

"Procedure `f` applied to `args`."
(define* s7-apply (subr s7-eff (s7-value s7-values s7-k s7-dyn) s7-state)
  (lambda (f args k dyn)
    (let ((n (list-length args)))
      (tagcase f
        (proc c
          (letrec ((pick (subr s7-eff ((listof s7-lambda acyclic)) s7-state)
                     (lambda (cs)
                       (if (null? cs)
                           (s7-error-state (string-append "wrong number of arguments to " (s7-proc-name f) ": " (int->string n) " given")
                                           nil k dyn)
                           (let* ((l (car cs)) (r (extract l required)))
                             (if (or (= n r) (and (extract l rest) (> n r)))
                                 (let ((fr (s7-new-frame (extract l size) (extract c env))))
                                   (begin (s7-fill-params (extract fr slots) args 0 r (extract l rest))
                                     (s7-eval-state (extract l body) (extract fr env) k dyn)))
                                 (pick (cdr cs))))))))
            (pick (extract c clauses))))
        (prim p
          (cond ((or (< n (extract p min)) (and (>= (extract p max) 0) (> n (extract p max))))
                 (s7-error-state (string-append "wrong number of arguments to " (extract p name) ": " (int->string n) " given") nil k dyn))
                (else (tagcase (extract p op)
                        (fn code (tagcase (code args)
                                   (ok v (s7-return-state v k dyn))
                                   (raise e (s7-raise-state e #f k dyn))))
                        (ctl op (s7-control op args k dyn))))))
        (cont c (s7-throw c (s7-values-of args) dyn))
        (else y (s7-error-state "not a procedure" (list f) k dyn))))))
"Whether the REPL shows value `v`: not if it is unspecified, or no values,
or a definition's name."
(define* s7-shown? (subr pure (s7-value) bool)
  (lambda (v) (tagcase v (unspec u #f) (multi l (pair? l)) (sym s #t) (else y #t))))

"A value returned to frame `f`, `k` the frames after it."
(define* s7-continue (subr s7-eff (s7-value s7-kframe s7-k s7-dyn) s7-state)
  (lambda (v f k dyn)
    (tagcase f
      (k-if x (s7-eval-state (if (s7-true? v) (extract x then) (extract x else)) (extract x env) k dyn))
      (k-seq x (let ((rest (extract x rest)))
                 (s7-eval-state (car rest) (extract x env)
                                (if (null? (cdr rest)) k (s7-push-k (sum k-seq (product (rest (cdr rest)) (env (extract x env)))) k))
                                dyn)))
      (k-args x (s7-args (cons v (extract x done)) (extract x rest) (extract x env) k dyn))
      (k-set-local x (tagcase (s7-frame-slots (extract x env) (extract x depth))
                       (some slots (begin (if (< (extract x index) (array-length slots)) (array-set! slots (extract x index) v) #u)
                                     (s7-return-state s7-unspecified k dyn)))
                       (none u (s7-return-state s7-unspecified k dyn))))
      (k-set-global c (tagcase (get (extract c value))
                        (undef u (s7-error-state "set!: unbound variable" (list (sum sym (extract c name))) k dyn))
                        (else y (begin (set (extract c value) v) (s7-return-state s7-unspecified k dyn)))))
      (k-define c (begin (set (extract c value) v) (s7-return-state (sum sym (extract c name)) k dyn)))
      (k-cwv consumer (s7-apply-state consumer (s7-values-in v) k dyn))
      (k-restore d (s7-return-state v k d))
      (k-dw-before x (let ((w (product (before (extract x before)) (after (extract x after)) (id (the (ref unit @sc) (new #u))))))
                       (s7-apply-state (extract x thunk) nil
                                       (s7-push-k (sum k-dw-body (product (after (extract x after)) (dyn dyn))) k)
                                       (product (winds (cons w (extract dyn winds))) (handlers (extract dyn handlers))))))
      (k-dw-body x (s7-apply-state (extract x after) nil (s7-push-k (sum k-then-return v) k) (extract x dyn)))
      (k-then-return w (s7-return-state w k dyn))
      (k-rewind x (s7-rewind (extract x steps) (extract x k) (extract x dyn) (extract x value)))
      (k-raise obj (s7-error-state "a handler returned from a non-continuable raise" (list obj) k dyn))
      (k-top x (begin
                 (if (and (extract x echo) (s7-shown? v))
                     (begin (s7-port-write "" s7-console (s7-string (string-append (s7-fresh-line) (s7-show v #t) "\n"))) #u)
                     #u)
                 (if (null? (extract x forms))
                     (s7-return-state v k dyn)
                     (s7-run-form (car (extract x forms)) (cdr (extract x forms)) (extract x echo) (extract x text) k dyn)))))))
"One step."
(define* s7-step (subr s7-eff (s7-state) s7-state)
  (lambda (st)
    (tagcase st
      (s-eval e
        (let ((n (extract e node)) (env (extract e env)) (k (extract e k)) (dyn (extract e dyn)))
          (tagcase (extract n form)
            (n-const v (s7-return-state v k dyn))
            (n-local l (typecase (s7-simple n env)
                         (bool b (s7-error-state (string-append "variable used before its definition: " (s7-symbol-name (extract l name))) nil k dyn))
                         (else v (s7-return-state v k dyn))))
            (n-global c (tagcase (get (extract c value))
                          (undef u (s7-error-state (string-append "unbound variable: " (s7-symbol-name (extract c name))) nil k dyn))
                          (else v (s7-return-state v k dyn))))
            (n-set-local x (s7-eval-state (extract x value) env
                                          (s7-push-k (sum k-set-local (product (depth (extract x depth)) (index (extract x index)) (env env))) k) dyn))
            (n-set-global x (s7-eval-state (extract x value) env (s7-push-k (sum k-set-global (extract x cell)) k) dyn))
            (n-define x (s7-eval-state (extract x value) env (s7-push-k (sum k-define (extract x cell)) k) dyn))
            (n-if x (typecase (s7-simple (extract x test) env)
                      (bool b (s7-eval-state (extract x test) env
                                             (s7-push-k (sum k-if (product (then (extract x then)) (else (extract x else)) (env env))) k) dyn))
                      (else v (s7-eval-state (if (s7-true? v) (extract x then) (extract x else)) env k dyn))))
            (n-lambda cs (typecase (s7-simple n env)
                           (bool b (s7-return-state s7-unspecified k dyn))
                           (else v (s7-return-state v k dyn))))
            (n-seq ns (s7-eval-state (car ns) env
                                     (if (null? (cdr ns)) k (s7-push-k (sum k-seq (product (rest (cdr ns)) (env env))) k))
                                     dyn))
            (n-call x (s7-args nil (cons (extract x op) (extract x args)) env k dyn))
            (n-scope x (let ((fr (s7-new-frame (extract x size) env)))
                         (s7-eval-state (extract x body) (extract fr env) k dyn)))
            (n-fail m (s7-raise-state (sum errobj (product (kind 'syntax) (message m) (irritants s7-nil))) #f k dyn)))))
      (s-return r (let ((k (extract r k)))
                    (if (null? k) (sum s-done (extract r value))
                        (s7-continue (extract r value) (car k) (cdr k) (extract r dyn)))))
      (s-apply a (s7-apply (extract a proc) (extract a args) (extract a k) (extract a dyn)))
      (s-raise r (let ((hs (extract (extract r dyn) handlers)))
                   (if (null? hs)
                       (sum s-failed (product (obj (extract r obj)) (k (extract r k))))
                       (let ((outer (product (winds (extract (extract r dyn) winds)) (handlers (cdr hs)))))
                         (s7-apply-state (car hs) (list (extract r obj))
                                         (if (extract r continuable)
                                             (s7-push-k (sum k-restore (extract r dyn)) (extract r k))
                                             (s7-push-k (sum k-raise (extract r obj)) (extract r k)))
                                         outer)))))
      (s-done v st)
      (s-failed f st))))

"Whether the machine has stopped."
(define* s7-stopped? (subr pure (s7-state) bool)
  (lambda (st) (tagcase st (s-done v #t) (s-failed f #t) (else y #f))))
"At most `fuel` steps from `st`: where the machine got to."
(define* s7-run (subr s7-eff (s7-state int) s7-state)
  (lambda (st fuel)
    (if (or (<= fuel 0) (s7-stopped? st)) st (s7-run (s7-step st) (- fuel 1)))))
