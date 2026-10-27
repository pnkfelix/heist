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
(define* s7-run-state (subr pure (s7-code s7-env s7-k s7-dyn) s7-state)
  (lambda (c env k dyn) (sum s-run (product (code c) (env env) (k k) (dyn dyn)))))
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

"The value of slot `index` of the frame `depth` out from `env`;
undefined if there is none."
(define* s7-local-ref (subr (maxeff spin (read @sc)) (s7-env int int) s7-value)
  (lambda (env depth index)
    (tagcase env
      (top u s7-undefined)
      (frame f (if (= depth 0)
                   (let ((s (extract f slots))) (if (< index (array-length s)) (array-ref s index) s7-undefined))
                   (s7-local-ref (extract f up) (- depth 1) index))))))

"Whether `v` is undefined: a quick evaluation that could not finish."
(define* s7-undef? (subr pure (s7-value) bool) (lambda (v) (tagcase v (undef u #t) (else y #f))))
"Slot `index` of frame `depth` out, got for a node once: depths 0 and 1, the
most used, with no loop."
(define* s7-local-getter (subr pure (int int) (subr (maxeff spin (read @sc) (read @globals)) (s7-env) s7-value))
  (lambda (d i)
    (let ((slot (lambda ((s (arrayof s7-value @sc))) (if (< i (array-length s)) (array-ref s i) s7-undefined))))
      (cond ((= d 0) (lambda ((env s7-env)) (tagcase env (frame f (slot (extract f slots))) (else y s7-undefined))))
            ((= d 1) (lambda ((env s7-env))
                       (tagcase env
                         (frame f (tagcase (extract f up) (frame g (slot (extract g slots))) (else y s7-undefined)))
                         (else y s7-undefined))))
            (else (lambda ((env s7-env)) (s7-local-ref env d i)))))))

"How a procedure is applied: `s7-apply`, defined after the compiler, whose
code calls it through this."
(define-type s7-applier (subr s7-eff (s7-value s7-values s7-k s7-dyn) s7-state))
(define s7-apply-hook (ref (listof s7-applier acyclic) @sc) (new nil))
(define* s7-call (subr s7-eff (s7-value s7-values s7-k s7-dyn) s7-state)
  (lambda (f args k dyn)
    (let ((h (get s7-apply-hook))) (if (null? h) (s7-apply-state f args k dyn) ((car h) f args k dyn)))))

"A call's operator and arguments evaluated, from `rest` on, as far as
they evaluate quickly; then the call made, or the first that does not run
as code, a frame pushed to come back for the rest."
(define* s7-run-args (subr s7-eff (s7-values s7-compileds s7-env s7-k s7-dyn) s7-state)
  (lambda (done rest env k dyn)
    (if (null? rest)
        (let ((all (the s7-values (reverse done)))) (s7-call (car all) (cdr all) k dyn))
        (let* ((c (car rest))
               (slow (lambda () ((extract c code) env (s7-push-k (sum k-args (product (done done) (rest (cdr rest)) (env env))) k) dyn))))
          (if (null? (extract c quick)) (slow)
              (let ((v ((car (extract c quick)) env)))
                (if (s7-undef? v) (slow) (s7-run-args (cons v done) (cdr rest) env k dyn))))))))
"A sequence's forms run, from the first of `cs`: those before the last
quickly if they can be, the last in the sequence's place."
(define* s7-run-seq (subr s7-eff (s7-compileds s7-env s7-k s7-dyn) s7-state)
  (lambda (cs env k dyn)
    (let ((c (car cs)))
      (if (null? (cdr cs)) ((extract c code) env k dyn)
          (let ((slow (lambda () ((extract c code) env (s7-push-k (sum k-seq (product (rest (cdr cs)) (env env))) k) dyn))))
            (if (null? (extract c quick)) (slow)
                (if (s7-undef? ((car (extract c quick)) env)) (slow) (s7-run-seq (cdr cs) env k dyn))))))))
"Whether each of `cs` has a quick evaluation."
(define* s7-all-quick? (subr spin (s7-compileds) bool)
  (lambda (cs) (or (null? cs) (and (pair? (extract (car cs) quick)) (s7-all-quick? (cdr cs))))))
"The values of `cs`, quickly; or, if one cannot be had, a list whose first
is undefined."
(define* s7-quick-all (subr s7-eff (s7-compileds s7-env) s7-values)
  (lambda (cs env)
    (if (null? cs) nil
        (let ((v ((car (extract (car cs) quick)) env)))
          (if (s7-undef? v) (cons v nil)
              (let ((l (s7-quick-all (cdr cs) env)))
                (if (and (pair? l) (s7-undef? (car l))) l (cons v l))))))))
"The value of the last of `cs`, the others evaluated quickly before it; or
undefined."
(define* s7-quick-seq (subr s7-eff (s7-compileds s7-env) s7-value)
  (lambda (cs env)
    (let ((v ((car (extract (car cs) quick)) env)))
      (if (or (null? (cdr cs)) (s7-undef? v)) v (s7-quick-seq (cdr cs) env)))))
"The values of `cs`, quickly, put in `slots` from `i`: whether all were."
(define* s7-quick-into (subr s7-eff (s7-compileds s7-env (arrayof s7-value @sc) int) bool)
  (lambda (cs env slots i)
    (or (null? cs)
        (let ((v ((car (extract (car cs) quick)) env)))
          (and (not (s7-undef? v))
               (begin (array-set! slots i v) (s7-quick-into (cdr cs) env slots (+ i 1))))))))

"Node `n` compiled: its code, and its quick evaluation if it has one (a
constant, a variable, a lambda, an `if` or a sequence of such, or a call of
a pure procedure written in FX-26 on such: the calls a program makes most)."
(define* s7-compile (subr s7-eff (s7-node) s7-compiled)
  (lambda (n)
    (let ((compiled (lambda ((c s7-code) (q (listof s7-quick acyclic))) (product (code c) (quick q))))
          (each (lambda ((ns s7-nodes))
                  (letrec ((go (subr s7-eff (s7-nodes) s7-compileds)
                             (lambda (ns) (if (null? ns) nil (cons (s7-compile (car ns)) (go (cdr ns)))))))
                    (go ns)))))
      (tagcase (extract n form)
        (n-const v
          (compiled (lambda ((env s7-env) (k s7-k) (dyn s7-dyn)) (s7-return-state v k dyn))
                    (list (lambda ((env s7-env)) v))))
        (n-local l
          (let ((d (extract l depth)) (i (extract l index))
                (why (string-append "variable used before its definition: " (s7-symbol-name (extract l name)))))
            (let ((get (s7-local-getter d i)))
              (compiled (lambda ((env s7-env) (k s7-k) (dyn s7-dyn))
                          (let ((v (get env)))
                            (tagcase v (undef u (s7-error-state why nil k dyn)) (else y (s7-return-state v k dyn)))))
                        (list get)))))
        (n-global c
          (let ((cell (extract c value))
                (why (string-append "unbound variable: " (s7-symbol-name (extract c name)))))
            (compiled (lambda ((env s7-env) (k s7-k) (dyn s7-dyn))
                        (let ((v (get cell)))
                          (tagcase v (undef u (s7-error-state why nil k dyn)) (else y (s7-return-state v k dyn)))))
                      (list (lambda ((env s7-env)) (get cell))))))
        (n-lambda ls
          (let* ((clauses (letrec ((go (subr s7-eff ((listof s7-lambda acyclic)) (listof s7-clause acyclic))
                                         (lambda (ls) (if (null? ls) nil
                                                          (cons (product (info (car ls)) (code (extract (s7-compile (extract (car ls) body)) code)))
                                                                (go (cdr ls)))))))
                            (go ls)))
                 (name (if (null? ls) "" (extract (car ls) name)))
                 (make (lambda ((env s7-env)) (sum proc (product (clauses clauses) (env env) (name (the (ref string @sc) (new name))))))))
            (compiled (lambda ((env s7-env) (k s7-k) (dyn s7-dyn)) (s7-return-state (make env) k dyn))
                      (list make))))
        (n-if x
          (let* ((t (s7-compile (extract x test))) (th (s7-compile (extract x then))) (el (s7-compile (extract x else)))
                 (tc (extract t code)) (thc (extract th code)) (elc (extract el code)))
            (compiled (if (pair? (extract t quick))
                          (let ((tq (car (extract t quick))))
                            (lambda ((env s7-env) (k s7-k) (dyn s7-dyn))
                              (let ((v (tq env)))
                                (cond ((s7-undef? v) (tc env (s7-push-k (sum k-if (product (then thc) (else elc) (env env))) k) dyn))
                                      ((s7-true? v) (thc env k dyn))
                                      (else (elc env k dyn))))))
                          (lambda ((env s7-env) (k s7-k) (dyn s7-dyn))
                            (tc env (s7-push-k (sum k-if (product (then thc) (else elc) (env env))) k) dyn)))
                      (if (s7-all-quick? (list t th el))
                          (let ((tq (car (extract t quick))) (thq (car (extract th quick))) (elq (car (extract el quick))))
                            (list (lambda ((env s7-env))
                                    (let ((v (tq env)))
                                      (cond ((s7-undef? v) v) ((s7-true? v) (thq env)) (else (elq env)))))))
                          nil))))
        (n-seq ns
          (let ((cs (each ns)))
            (compiled (lambda ((env s7-env) (k s7-k) (dyn s7-dyn)) (s7-run-seq cs env k dyn))
                      (if (s7-all-quick? cs)
                          (list (lambda ((env s7-env)) (s7-quick-seq cs env)))
                          nil))))
        (n-call x
          (let* ((op (s7-compile (extract x op)))
                 (args (each (extract x args)))
                 (cs (the s7-compileds (cons op args)))
                 (n (list-length args))
                 (all-quick (s7-all-quick? cs))
                 ;; Built-in `p` called quickly: by its fast entry, if it
                 ;; has one for `n` arguments, else by its list of them.
                 (prim-quick
                  (let ((slow (lambda ((p s7-prim) (env s7-env))
                                (if (and (extract p pure) (>= n (extract p min)) (or (< (extract p max) 0) (<= n (extract p max))))
                                    (tagcase (extract p op)
                                      (fn code (let ((vs (s7-quick-all args env)))
                                                 (if (and (pair? vs) (s7-undef? (car vs))) s7-undefined
                                                     (tagcase (code vs) (ok v v) (raise e s7-undefined)))))
                                      (ctl c s7-undefined))
                                    s7-undefined))))
                    (cond ((not all-quick) slow)
                          ((= n 1)
                           (let ((aq (car (extract (car args) quick))))
                             (lambda ((p s7-prim) (env s7-env))
                               (tagcase (extract p fast)
                                 (f1 g (let ((a (aq env))) (if (s7-undef? a) a (g a))))
                                 (else y (slow p env))))))
                          ((= n 2)
                           (let ((aq (car (extract (car args) quick))) (bq (car (extract (car (cdr args)) quick))))
                             (lambda ((p s7-prim) (env s7-env))
                               (tagcase (extract p fast)
                                 (f2 g (let ((a (aq env)))
                                         (if (s7-undef? a) a (let ((b (bq env))) (if (s7-undef? b) b (g a b))))))
                                 (else y (slow p env))))))
                          (else slow))))
                 ;; Whether the operator is a global holding a pure
                 ;; built-in now: only then is a quick evaluation tried,
                 ;; since one of a closure's call is undone and done again.
                 (prim-op? (tagcase (extract (extract x op) form)
                             (n-global c (tagcase (get (extract c value)) (prim p (extract p pure)) (else y #f)))
                             (else y #f))))
            (compiled (if all-quick
                          ;; A closure of one clause, called with the number it
                          ;; takes, gets its frame filled in place; a built-in
                          ;; that answers quickly, its answer returned.
                          (let ((opq (car (extract op quick))))
                            (lambda ((env s7-env) (k s7-k) (dyn s7-dyn))
                              (let ((f (opq env)))
                                (tagcase f
                                  (proc c (let ((cls (extract c clauses)))
                                            (if (and (pair? cls) (null? (cdr cls))
                                                     (not (extract (extract (car cls) info) rest))
                                                     (= n (extract (extract (car cls) info) required)))
                                                (let ((fr (s7-new-frame (extract (extract (car cls) info) size) (extract c env))))
                                                  (if (s7-quick-into args env (extract fr slots) 0)
                                                      (s7-run-state (extract (car cls) code) (extract fr env) k dyn)
                                                      (s7-run-args nil cs env k dyn)))
                                                (s7-run-args nil cs env k dyn))))
                                  (prim p (let ((v (prim-quick p env)))
                                            (if (s7-undef? v) (s7-run-args nil cs env k dyn) (s7-return-state v k dyn))))
                                  (else y (s7-run-args nil cs env k dyn))))))
                          (lambda ((env s7-env) (k s7-k) (dyn s7-dyn)) (s7-run-args nil cs env k dyn)))
                      (if (and all-quick prim-op?)
                          (let ((opq (car (extract op quick))))
                            (list (lambda ((env s7-env))
                                    (let ((f (opq env)))
                                      (tagcase f (prim p (prim-quick p env)) (else y s7-undefined))))))
                          nil))))
        (n-set-local x
          (let* ((v (s7-compile (extract x value))) (vc (extract v code)) (d (extract x depth)) (i (extract x index))
                 (push (lambda ((env s7-env) (k s7-k) (dyn s7-dyn))
                         (vc env (s7-push-k (sum k-set-local (product (depth d) (index i) (env env))) k) dyn))))
            (compiled (if (pair? (extract v quick))
                          (let ((vq (car (extract v quick))))
                            (lambda ((env s7-env) (k s7-k) (dyn s7-dyn))
                              (let ((w (vq env)))
                                (if (s7-undef? w) (push env k dyn)
                                    (tagcase (s7-frame-slots env d)
                                      (some slots (begin (if (< i (array-length slots)) (array-set! slots i w) #u)
                                                    (s7-return-state s7-unspecified k dyn)))
                                      (none u (s7-return-state s7-unspecified k dyn)))))))
                          push)
                      nil)))
        (n-set-global x
          (let ((vc (extract (s7-compile (extract x value)) code)) (cell (extract x cell)))
            (compiled (lambda ((env s7-env) (k s7-k) (dyn s7-dyn)) (vc env (s7-push-k (sum k-set-global cell) k) dyn)) nil)))
        (n-define x
          (let ((vc (extract (s7-compile (extract x value)) code)) (cell (extract x cell)))
            (compiled (lambda ((env s7-env) (k s7-k) (dyn s7-dyn)) (vc env (s7-push-k (sum k-define cell) k) dyn)) nil)))
        (n-scope x
          (let ((bc (extract (s7-compile (extract x body)) code)) (size (extract x size)))
            (compiled (lambda ((env s7-env) (k s7-k) (dyn s7-dyn))
                        (let ((fr (s7-new-frame size env))) (bc (extract fr env) k dyn)))
                      nil)))
        (n-fail m
          (compiled (lambda ((env s7-env) (k s7-k) (dyn s7-dyn))
                      (s7-raise-state (sum errobj (product (kind 'syntax) (message m) (irritants s7-nil))) #f k dyn))
                    nil))))))

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

"A condition: a syntax error, `message`."
(define* s7-syntax-error (subr pure (string) s7-value)
  (lambda (message) (sum errobj (product (kind 'syntax) (message message) (irritants s7-nil)))))

"Library `name` (missing), loaded from its file, then the top-level forms
`forms` run (in `ns`), the first of which wanted it; or why not."
(define* s7-load-library-then (subr s7-eff (s7-value s7-values bool string s7-ns s7-k s7-dyn) s7-state)
  (lambda (name forms echo text ns k dyn)
    (let ((k2 (s7-push-k (sum k-top (product (forms forms) (echo echo) (text text) (ns ns))) k)))
      (tagcase (s7-library-file name)
        (none u (s7-raise-state (s7-syntax-error (string-append "no library named " (s7-library-name name)
                                                                ", and no file " (s7-library-relative-file name) " where libraries are looked for"))
                                #f k2 dyn))
        (found f
          (if (s7-member-string? (extract f path) (get s7-library-files))
              (s7-raise-state (s7-syntax-error (string-append (extract f path) " does not define " (s7-library-name name))) #f k2 dyn)
              (begin
                (set s7-library-files (cons (extract f path) (get s7-library-files)))
                (s7-add-library-directory! (extract f root))
                (tagcase (s7-read-all (extract f text) (extract f path))
                  (data fs (s7-return-state s7-unspecified
                                            (s7-push-k (sum k-top (product (forms fs) (echo #f) (text (extract f text)) (ns s7-toplevel))) k2)
                                            dyn))
                  (stop r (s7-raise-state (sum errobj (product (kind 'read) (message (string-append "cannot read " (extract f path))) (irritants s7-nil)))
                                          #f k2 dyn))))))))))

"`(import set …)` at top level: the sets' names bound in `ns`; a library
not defined loaded first."
(define* s7-run-import (subr s7-eff (s7-value s7-values bool string s7-ns s7-k s7-dyn) s7-state)
  (lambda (x more echo text ns k dyn)
    (let ((k2 (s7-push-k (sum k-top (product (forms more) (echo echo) (text text) (ns ns))) k)))
      (tagcase (s7-import-sets (s7-value->values (s7-cdr x)))
        (bindings bs (begin (s7-bind-all! ns bs) (s7-return-state s7-unspecified k2 dyn)))
        (plain u (s7-return-state s7-unspecified k2 dyn))
        (missing name (s7-load-library-then name (cons x more) echo text ns k dyn))
        (bad m (s7-raise-state (s7-syntax-error (string-append "import: " m)) #f k2 dyn))))))

"`(define-library name decl …)`: a namespace made for it, what it imports
bound there (a library not defined loaded first), it registered, and its
body run there."
(define* s7-run-library (subr s7-eff (s7-value s7-values bool string s7-ns s7-k s7-dyn) s7-state)
  (lambda (x more echo text ns k dyn)
    (let* ((k2 (s7-push-k (sum k-top (product (forms more) (echo echo) (text text) (ns ns))) k))
           (name (s7-cadr x))
           (decls (s7-library-decls (s7-value->values (s7-cddr x)))))
      (tagcase (s7-import-sets (s7-decl-items decls "import"))
        (missing m (s7-load-library-then m (cons x more) echo text ns k dyn))
        (bad m (s7-raise-state (s7-syntax-error (string-append "define-library: " m)) #f k2 dyn))
        (else imported
          (let ((lib (s7-make-ns (s7-library-name name) 256 (list s7-builtins))))
            (begin
              (tagcase imported (bindings bs (s7-bind-all! lib bs)) (else y #u))
              (s7-register-library! (product (name (s7-library-name name)) (ns lib) (exports (s7-exports-of (s7-decl-items decls "export")))))
              (s7-return-state s7-unspecified
                               (s7-push-k (sum k-top (product (forms (s7-library-body decls)) (echo #f) (text text) (ns lib))) k2)
                               dyn))))))))

"Top-level form `x` run in namespace `ns`, the forms after it then, as
`k-top` says. An `import` or a `define-library` is done here; anything
else is expanded and run, or, if it has syntax errors, the first raised."
(define* s7-run-form (subr s7-eff (s7-value s7-values bool string s7-ns s7-k s7-dyn) s7-state)
  (lambda (x more echo text ns k dyn)
    (begin
      (set s7-current-ns ns)
      (set s7-syntax-errors nil)
      (let ((kind (tagcase (s7-head-kind x nil) (b-special s s) (else y (string->symbol " none")))))
        (cond
          ((eq? kind 'import) (s7-run-import x more echo text ns k dyn))
          ((eq? kind 'define-library) (s7-run-library x more echo text ns k dyn))
          (else
           (let* ((node (s7-expand-top x))
                  (errors (reverse (get s7-syntax-errors)))
                  (k2 (s7-push-k (sum k-top (product (forms more) (echo echo) (text text) (ns ns))) k)))
             (if (pair? errors)
                 (s7-raise-state (s7-syntax-error (string-append (s7-where (extract (car errors) span) text)
                                                                 (extract (car errors) message)))
                                 #f k2 dyn)
                 (s7-run-state (extract (s7-compile node) code) (sum top #u) k2 dyn)))))))))

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
        ((= op s7-op-eval) (s7-run-form a1 nil #f "" (tagcase a2 (env n n) (else y (get s7-current-ns))) k dyn))
        ((= op s7-op-load)
         (tagcase a1
           (str s (tagcase (s7-file-text (get s))
                    (text t (tagcase (s7-read-all t (get s))
                              (data forms (s7-return-state s7-unspecified
                                                           (s7-push-k (sum k-top (product (forms forms) (echo #f) (text t)
                                                                                          (ns (tagcase a2 (env n n) (else y s7-toplevel)))))
                                                                      k)
                                                           dyn))
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
          (letrec ((pick (subr s7-eff ((listof s7-clause acyclic)) s7-state)
                     (lambda (cs)
                       (if (null? cs)
                           (s7-error-state (string-append "wrong number of arguments to " (s7-proc-name f) ": " (int->string n) " given")
                                           nil k dyn)
                           (let* ((l (extract (car cs) info)) (r (extract l required)))
                             (if (or (= n r) (and (extract l rest) (> n r)))
                                 (let ((fr (s7-new-frame (extract l size) (extract c env))))
                                   (begin (s7-fill-params (extract fr slots) args 0 r (extract l rest))
                                     (s7-run-state (extract (car cs) code) (extract fr env) k dyn)))
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
(set s7-apply-hook (list s7-apply))
"Whether the REPL shows value `v`: not if it is unspecified, or no values,
or a definition's name."
(define* s7-shown? (subr pure (s7-value) bool)
  (lambda (v) (tagcase v (unspec u #f) (multi l (pair? l)) (sym s #t) (else y #t))))

"A value returned to frame `f`, `k` the frames after it."
(define* s7-continue (subr s7-eff (s7-value s7-kframe s7-k s7-dyn) s7-state)
  (lambda (v f k dyn)
    (tagcase f
      (k-if x ((if (s7-true? v) (extract x then) (extract x else)) (extract x env) k dyn))
      (k-seq x (s7-run-seq (extract x rest) (extract x env) k dyn))
      (k-args x (s7-run-args (cons v (extract x done)) (extract x rest) (extract x env) k dyn))
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
                     (s7-run-form (car (extract x forms)) (cdr (extract x forms)) (extract x echo) (extract x text) (extract x ns) k dyn)))))))
"One step."
(define* s7-step (subr s7-eff (s7-state) s7-state)
  (lambda (st)
    (tagcase st
      (s-run r ((extract r code) (extract r env) (extract r k) (extract r dyn)))
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
