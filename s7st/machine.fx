;;; machine.fx: what Scheme's code, lowered to FX-26 (lower.fx), runs on.
;;;
;;; Lowered code is FX-26 in direct style: a Scheme procedure is an FX-26
;;; procedure, its locals FX-26's (a box each, if assigned), its calls
;;; FX-26's, through `s7-call0` … `s7-calln` here. FX-26's calls in tail
;;; position take no stack, so neither do Scheme's. What a stack does not
;;; give is done with FX-26's delimited control, a prompt about each run
;;; (lower.fx's `s7-run-in`), with tag `s7-tag`:
;;;   - `call/cc` captures the rest of the run up to it (a composable
;;;     continuation), so a continuation may be resumed any number of
;;;     times; resumed, the run is aborted to the prompt, which resumes it
;;;     in a prompt of its own, `dynamic-wind`'s thunks run on the way;
;;;   - each procedure's entry spends fuel (`s7-tick!`); with none left, the
;;;     rest of the run is captured and the run paused, so a client runs
;;;     s7st in slices, and may interrupt it;
;;;   - a condition nothing handles aborts the run.
;;; The dynamic state (winds, handlers) is a global, `s7-dyn-now`, which a
;;; continuation keeps and puts back.

"A procedure of no arguments, as lowered code makes one."
(define-type s7-thunk (subr s7-eff () s7-value))
"What a run's prompt is given by an abort: code to run in its place (a
continuation resumed), the run paused (its rest), a condition nothing
handled, or `exit`'s value."
(define-type s7-jump (sumof (go s7-thunk) (pause s7-thunk) (fail s7-value) (exit s7-value)))
(define s7-tag (prompt-tag s7-value s7-jump s7-base-eff @sk) (make-continuation-prompt-tag))
"The dynamic state now."
(define s7-dyn-now (ref s7-dyn @sc) (new s7-no-dyn))

"Procedure entries left in the slice that runs: at none, it pauses."
(define s7-fuel (ref int @sc) (new 0))
"A procedure entered: fuel spent, or, with none left, the run paused, the
rest of it kept to resume."
(define* s7-tick! (subr s7-eff () unit)
  (lambda ()
    (let ((f (get s7-fuel)))
      (if (> f 0)
          (set s7-fuel (- f 1))
          ((proj (proj call-with-composable-continuation @sk) s7-value s7-jump s7-base-eff unit s7-eff)
           (lambda ((k (composable unit s7-value s7-base-eff @sk)))
             (abort-current-continuation s7-tag (sum pause (lambda () (k #u)))))
           s7-tag)))))

;;; ------------------------------------------------------------ conditions

"How a procedure is called where it cannot be named yet (raising,
rewinding): `s7-calln`, set when it is defined."
(define-type s7-caller (subr s7-eff (s7-value s7-values) s7-value))
(define s7-call-hook (ref (listof s7-caller acyclic) @sc) (new nil))
(define* s7-call-late (subr s7-eff (s7-value s7-values) s7-value)
  (lambda (f args) (let ((h (get s7-call-hook))) (if (null? h) s7-unspecified ((car h) f args)))))

"Condition `obj` raised: the innermost handler called with it, in the
dynamic state outside it; if `continuable`, what the handler returns is
`raise-continuable`'s value, else a handler that returns is an error,
raised there. With no handler, the run aborted."
(define* s7-raise (subr s7-eff (s7-value bool) s7-value)
  (lambda (obj continuable)
    (let* ((dyn (get s7-dyn-now)) (hs (extract dyn handlers)))
      (if (null? hs)
          (abort-current-continuation s7-tag (sum fail obj))
          (begin
            (set s7-dyn-now (product (winds (extract dyn winds)) (handlers (cdr hs))))
            (let ((v (s7-call-late (car hs) (list obj))))
              (if continuable
                  (begin (set s7-dyn-now dyn) v)
                  (s7-raise (s7-error-value "a handler returned from a non-continuable raise" (list obj)) #f))))))))
"An error raised: `message`, with `irritants`."
(define* s7-error (subr s7-eff (string s7-values) s7-value)
  (lambda (message irritants) (s7-raise (s7-error-value message irritants) #f)))
"A condition: a syntax error, `message`."
(define* s7-syntax-error (subr pure (string) s7-value)
  (lambda (message) (sum errobj (product (kind 'syntax) (message message) (irritants s7-nil)))))

;;; ------------------------------------------------------------ calls

(define* s7-proc-name (subr (read @sc) (s7-value) string)
  (lambda (f)
    (tagcase f
      (proc c (let ((n (get (extract c name)))) (if (string=? n "") "a procedure" n)))
      (prim p (extract p name))
      (else y "a procedure"))))
(define* s7-wrong-args (subr s7-eff (string int) s7-value)
  (lambda (name n) (s7-error (string-append "wrong number of arguments to " name ": " (int->string n) " given") nil)))
"Built-in `p` applied to `args`, `n` of them."
(define* s7-prim-apply (subr s7-eff (s7-prim s7-values int) s7-value)
  (lambda (p args n)
    (if (or (< n (extract p min)) (and (>= (extract p max) 0) (> n (extract p max))))
        (s7-wrong-args (extract p name) n)
        (tagcase (extract p op)
          (fn code (tagcase (code args) (ok v v) (raise e (s7-raise e #f))))))))
"What `values` gives of `l`: the one value, or several."
(define* s7-values-of (subr pure (s7-values) s7-value)
  (lambda (l) (if (and (pair? l) (null? (cdr l))) (car l) (sum multi l))))
"The values a value stands for: several, or itself."
(define* s7-values-in (subr pure (s7-value) s7-values)
  (lambda (v) (tagcase v (multi l l) (else y (list v)))))
(define* s7-not-procedure (subr s7-eff (s7-value) s7-value)
  (lambda (f) (s7-error "not a procedure" (list f))))

;;; ------------------------------------------------------------ continuations

(define* s7-drop-winds (subr spin (s7-winds int) s7-winds)
  (lambda (l n) (if (or (<= n 0) (null? l)) l (s7-drop-winds (cdr l) (- n 1)))))
"The thunks run going from dynamic state `from` to `to`: each
`dynamic-wind` left, its `after`, innermost first; then each entered, its
`before`, outermost first; each with the state to run it in."
(define* s7-wind-steps (subr s7-eff (s7-dyn s7-dyn) (listof s7-step acyclic))
  (lambda (dyn to-dyn)
    (let* ((from (extract dyn winds))
           (to (extract to-dyn winds))
           (nf (list-length from))
           (nt (list-length to)))
      (letrec ((common (subr s7-eff (s7-winds s7-winds) int)
                 ;; How many winds `a` and `b`, of a length, share at their ends.
                 (lambda (a b)
                   (cond ((null? a) 0)
                         ((eq? (extract (car a) id) (extract (car b) id)) (list-length a))
                         (else (common (cdr a) (cdr b))))))
               (afters (subr s7-eff (s7-winds int) (listof s7-step acyclic))
                 (lambda (ws keep)
                   (if (<= (list-length ws) keep) nil
                       (cons (product (thunk (extract (car ws) after))
                                      (dyn (product (winds (cdr ws)) (handlers (extract dyn handlers)))))
                             (afters (cdr ws) keep)))))
               (befores (subr s7-eff (s7-winds int (listof s7-step acyclic)) (listof s7-step acyclic))
                 (lambda (ws keep acc)
                   (if (<= (list-length ws) keep) acc
                       (befores (cdr ws) keep
                                (cons (product (thunk (extract (car ws) before))
                                               (dyn (product (winds (cdr ws)) (handlers (extract to-dyn handlers)))))
                                      acc))))))
        (let ((shared (common (s7-drop-winds from (- nf nt)) (s7-drop-winds to (- nt nf)))))
          (append (afters from shared) (befores to shared nil)))))))
(define* s7-run-steps! (subr s7-eff ((listof s7-step acyclic)) unit)
  (lambda (steps)
    (unless (null? steps)
      (set s7-dyn-now (extract (car steps) dyn))
 (s7-call-late (extract (car steps) thunk) nil)
 (s7-run-steps! (cdr steps)))))
"`v` given to continuation `c`: the run aborted to its prompt, which runs
the `dynamic-wind` thunks on the way, then the continuation."
(define* s7-throw (subr s7-eff (s7-cont s7-value) s7-value)
  (lambda (c v)
    (let ((steps (s7-wind-steps (get s7-dyn-now) (extract c dyn))))
      (abort-current-continuation s7-tag
        (sum go (lambda () (begin (s7-run-steps! steps) (set s7-dyn-now (extract c dyn)) ((extract c k) v))))))))
"`f` applied to `args`: any procedure, any number."
(define* s7-calln (subr s7-eff (s7-value s7-values) s7-value)
  (lambda (f args)
    (tagcase f
      (proc c (let ((n (list-length args))
                    (wrong (lambda () (s7-wrong-args (s7-proc-name f) (list-length args)))))
                (tagcase (extract c code)
                  (an g (g args))
                  (a0 g (if (= n 0) (g) (wrong)))
                  (a1 g (if (= n 1) (g (car args)) (wrong)))
                  (a2 g (if (= n 2) (g (car args) (car (cdr args))) (wrong)))
                  (a3 g (if (= n 3) (g (car args) (car (cdr args)) (car (cdr (cdr args)))) (wrong)))
                  (a4 g (if (= n 4) (g (car args) (car (cdr args)) (car (cdr (cdr args))) (car (cdr (cdr (cdr args))))) (wrong))))))
      (prim p (s7-prim-apply p args (list-length args)))
      (cont c (s7-throw c (s7-values-of args)))
      (else y (s7-not-procedure f)))))
(define* s7-call0 (subr s7-eff (s7-value) s7-value)
  (lambda (f)
    (tagcase f
      (proc c (tagcase (extract c code) (a0 g (g)) (else y (s7-calln f nil))))
      (else y (s7-calln f nil)))))
"The same of one argument; a built-in by its fast entry, if it has one."
(define* s7-call1 (subr s7-eff (s7-value s7-value) s7-value)
  (lambda (f a)
    (tagcase f
      (proc c (tagcase (extract c code) (a1 g (g a)) (else y (s7-calln f (list a)))))
      (prim p (tagcase (extract p fast)
                (f1 g (let ((v (g a))) (tagcase v (undef u (s7-prim-apply p (list a) 1)) (else y v))))
                (else y (s7-prim-apply p (list a) 1))))
      (else y (s7-calln f (list a))))))
(define* s7-call2 (subr s7-eff (s7-value s7-value s7-value) s7-value)
  (lambda (f a b)
    (tagcase f
      (proc c (tagcase (extract c code) (a2 g (g a b)) (else y (s7-calln f (list a b)))))
      (prim p (tagcase (extract p fast)
                (f2 g (let ((v (g a b))) (tagcase v (undef u (s7-prim-apply p (list a b) 2)) (else y v))))
                (else y (s7-prim-apply p (list a b) 2))))
      (else y (s7-calln f (list a b))))))
(define* s7-call3 (subr s7-eff (s7-value s7-value s7-value s7-value) s7-value)
  (lambda (f a b c)
    (tagcase f
      (proc d (tagcase (extract d code) (a3 g (g a b c)) (else y (s7-calln f (list a b c)))))
      (else y (s7-calln f (list a b c))))))
(define* s7-call4 (subr s7-eff (s7-value s7-value s7-value s7-value s7-value) s7-value)
  (lambda (f a b c d)
    (tagcase f
      (proc e (tagcase (extract e code) (a4 g (g a b c d)) (else y (s7-calln f (list a b c d)))))
      (else y (s7-calln f (list a b c d))))))

(set s7-call-hook (list s7-calln))

"A closure of lambdas `ls`, its code `code`."
(define* s7-make-proc (subr s7-eff ((listof s7-lambda acyclic) s7-entry) s7-value)
  (lambda (ls code)
    (sum proc (product (infos ls) (name (the (ref string @sc) (new (if (null? ls) "" (extract (car ls) name))))) (code code)))))
"The same, of code of so many arguments, or of their list."
(define* s7-make-proc0 (subr s7-eff ((listof s7-lambda acyclic) (subr s7-eff () s7-value)) s7-value)
  (lambda (ls f) (s7-make-proc ls (sum a0 f))))
(define* s7-make-proc1 (subr s7-eff ((listof s7-lambda acyclic) (subr s7-eff (s7-value) s7-value)) s7-value)
  (lambda (ls f) (s7-make-proc ls (sum a1 f))))
(define* s7-make-proc2 (subr s7-eff ((listof s7-lambda acyclic) (subr s7-eff (s7-value s7-value) s7-value)) s7-value)
  (lambda (ls f) (s7-make-proc ls (sum a2 f))))
(define* s7-make-proc3 (subr s7-eff ((listof s7-lambda acyclic) (subr s7-eff (s7-value s7-value s7-value) s7-value)) s7-value)
  (lambda (ls f) (s7-make-proc ls (sum a3 f))))
(define* s7-make-proc4 (subr s7-eff ((listof s7-lambda acyclic) (subr s7-eff (s7-value s7-value s7-value s7-value) s7-value)) s7-value)
  (lambda (ls f) (s7-make-proc ls (sum a4 f))))
(define* s7-make-procn (subr s7-eff ((listof s7-lambda acyclic) (subr s7-eff (s7-values) s7-value)) s7-value)
  (lambda (ls f) (s7-make-proc ls (sum an f))))
"Whether `args` are what a clause takes: `r`, or more if `rest`."
(define* s7-args-fit? (subr spin (s7-values int bool) bool)
  (lambda (args r rest)
    (cond ((= r 0) (or rest (null? args)))
          ((null? args) #f)
          (else (s7-args-fit? (cdr args) (- r 1) rest)))))
"The `i`th of `args`, there."
(define* s7-arg (subr spin (s7-values int) s7-value)
  (lambda (args i) (cond ((null? args) s7-undefined) ((= i 0) (car args)) (else (s7-arg (cdr args) (- i 1))))))
"Those after the first `r` of `args`, a list."
(define* s7-args-rest (subr s7-eff (s7-values int) s7-value)
  (lambda (args r) (if (or (= r 0) (null? args)) (s7-list args) (s7-args-rest (cdr args) (- r 1)))))
"No clause of lambdas `ls` takes `args`."
(define* s7-no-clause (subr s7-eff ((listof s7-lambda acyclic) s7-values) s7-value)
  (lambda (ls args)
    (s7-wrong-args (if (or (null? ls) (string=? (extract (car ls) name) "")) "a procedure" (extract (car ls) name))
                   (list-length args))))

;;; ------------------------------------------------------------ variables

"Whether every global that held a built-in when s7st was made ready still
holds it (`s7-init!` sets it then): assigning or defining one that holds
one clears it, and the fused calls below then call as any call does."
(define s7-builtins-intact (ref bool @sc) (new #t))
(define* s7-builtin-changed! (subr (maxeff (read @sc) (write @sc)) (s7-global) unit)
  (lambda (c) (tagcase (get (extract c value)) (prim p (set s7-builtins-intact #f)) (else y #u))))

"Global `c`'s value; an error if it has none."
(define* s7-global-ref (subr s7-eff (s7-global) s7-value)
  (lambda (c)
    (let ((v (get (extract c value))))
      (tagcase v
        (undef u (s7-error (string-append "unbound variable: " (s7-symbol-name (extract c name))) nil))
        (else y v)))))
(define* s7-global-set! (subr s7-eff (s7-global s7-value) s7-value)
  (lambda (c v)
    (tagcase (get (extract c value))
      (undef u (s7-error "set!: unbound variable" (list (sum sym (extract c name)))))
      (else y (begin (s7-builtin-changed! c) (set (extract c value) v) s7-unspecified)))))
(define* s7-global-define! (subr s7-eff (s7-global s7-value) s7-value)
  (lambda (c v) (begin (s7-builtin-changed! c) (set (extract c value) v) (sum sym (extract c name)))))
"A local's value, from its box; an error if it has none yet (`name`, a\nsymbol, says which)."
(define* s7-local-ref (subr s7-eff ((ref s7-value @sc) s7-value) s7-value)
  (lambda (box name)
    (let ((v (get box)))
      (tagcase v
        (undef u (s7-error (string-append "variable used before its definition: "
                                          (tagcase name (sym s (s7-symbol-name s)) (else y "?")))
                           nil))
        (else y v)))))
(define* s7-fail-syntax (subr s7-eff (string) s7-value)
  (lambda (m) (s7-raise (s7-syntax-error m) #f)))

"`call/cc`: `f` called with the rest of the run."
(define* s7-call/cc (subr s7-eff (s7-value) s7-value)
  (lambda (f)
    ((proj (proj call-with-composable-continuation @sk) s7-value s7-jump s7-base-eff s7-value s7-eff)
     (lambda ((k (composable s7-value s7-value s7-base-eff @sk)))
       (s7-call1 f (sum cont (product (k k) (dyn (get s7-dyn-now)) (id (the (ref unit @sc) (new #u)))))))
     s7-tag)))
"`dynamic-wind`: `before`, `thunk` and `after` called, `thunk` within a
wind, which a continuation's resumption passes through."
(define* s7-dynamic-wind (subr s7-eff (s7-value s7-value s7-value) s7-value)
  (lambda (before thunk after)
    (begin
      (s7-call0 before)
      (let ((dyn (get s7-dyn-now)))
        (begin
          (set s7-dyn-now (product (winds (cons (product (before before) (after after) (id (the (ref unit @sc) (new #u))))
                                                (extract dyn winds)))
                                   (handlers (extract dyn handlers))))
          (let ((v (s7-call0 thunk)))
            (begin (set s7-dyn-now dyn) (s7-call0 after) v)))))))
"`with-exception-handler`: `thunk` called with `handler` the innermost."
(define* s7-with-handler (subr s7-eff (s7-value s7-value) s7-value)
  (lambda (handler thunk)
    (let ((dyn (get s7-dyn-now)))
      (begin
        (set s7-dyn-now (product (winds (extract dyn winds)) (handlers (cons handler (extract dyn handlers)))))
        (let ((v (s7-call0 thunk))) (begin (set s7-dyn-now dyn) v))))))

;;; ------------------------------------------------------------ fused calls

"A global's call with its value got here, not first by `s7-global-ref`."
(define* s7-unbound (subr s7-eff (s7-global) s7-value)
  (lambda (c) (s7-error (string-append "unbound variable: " (s7-symbol-name (extract c name))) nil)))
(define* s7-gcall0 (subr s7-eff (s7-global) s7-value)
  (lambda (c)
    (let ((f (get (extract c value))))
      (tagcase f
        (proc p (tagcase (extract p code) (a0 g (g)) (else y (s7-calln f nil))))
        (undef u (s7-unbound c))
        (else y (s7-calln f nil))))))
(define* s7-gcall1 (subr s7-eff (s7-global s7-value) s7-value)
  (lambda (c a)
    (let ((f (get (extract c value))))
      (tagcase f
        (proc p (tagcase (extract p code) (a1 g (g a)) (else y (s7-calln f (list a)))))
        (prim p (tagcase (extract p fast)
                  (f1 g (let ((v (g a))) (tagcase v (undef u (s7-prim-apply p (list a) 1)) (else y v))))
                  (else y (s7-prim-apply p (list a) 1))))
        (undef u (s7-unbound c))
        (else y (s7-calln f (list a)))))))
(define* s7-gcall2 (subr s7-eff (s7-global s7-value s7-value) s7-value)
  (lambda (c a b)
    (let ((f (get (extract c value))))
      (tagcase f
        (proc p (tagcase (extract p code) (a2 g (g a b)) (else y (s7-calln f (list a b)))))
        (prim p (tagcase (extract p fast)
                  (f2 g (let ((v (g a b))) (tagcase v (undef u (s7-prim-apply p (list a b) 2)) (else y v))))
                  (else y (s7-prim-apply p (list a b) 2))))
        (undef u (s7-unbound c))
        (else y (s7-calln f (list a b)))))))
(define* s7-gcall3 (subr s7-eff (s7-global s7-value s7-value s7-value) s7-value)
  (lambda (c a b d)
    (let ((f (get (extract c value))))
      (tagcase f
        (proc p (tagcase (extract p code) (a3 g (g a b d)) (else y (s7-calln f (list a b d)))))
        (undef u (s7-unbound c))
        (else y (s7-calln f (list a b d)))))))
(define* s7-gcall4 (subr s7-eff (s7-global s7-value s7-value s7-value s7-value) s7-value)
  (lambda (c a b d e)
    (let ((f (get (extract c value))))
      (tagcase f
        (proc p (tagcase (extract p code) (a4 g (g a b d e)) (else y (s7-calln f (list a b d e)))))
        (undef u (s7-unbound c))
        (else y (s7-calln f (list a b d e)))))))
"Built-ins called by name, two ints done here while the built-ins hold
(`s7-builtins-intact`); else as `s7-gcall2` calls. A test's own (`?`)
gives a `bool`, for an `if`."
(define* s7-fadd (subr s7-eff (s7-global s7-value s7-value) s7-value)
  (lambda (c a b)
    (tagcase a
      (int i (tagcase b (int j (if (get s7-builtins-intact) (sum int (+ i j)) (s7-gcall2 c a b))) (else y (s7-gcall2 c a b))))
      (else y (s7-gcall2 c a b)))))
(define* s7-fsub (subr s7-eff (s7-global s7-value s7-value) s7-value)
  (lambda (c a b)
    (tagcase a
      (int i (tagcase b (int j (if (get s7-builtins-intact) (sum int (- i j)) (s7-gcall2 c a b))) (else y (s7-gcall2 c a b))))
      (else y (s7-gcall2 c a b)))))
(define* s7-fmul (subr s7-eff (s7-global s7-value s7-value) s7-value)
  (lambda (c a b)
    (tagcase a
      (int i (tagcase b (int j (if (get s7-builtins-intact) (sum int (* i j)) (s7-gcall2 c a b))) (else y (s7-gcall2 c a b))))
      (else y (s7-gcall2 c a b)))))
(define* s7-flt (subr s7-eff (s7-global s7-value s7-value) s7-value)
  (lambda (c a b)
    (tagcase a
      (int i (tagcase b (int j (if (get s7-builtins-intact) (if (< i j) s7-true s7-false) (s7-gcall2 c a b))) (else y (s7-gcall2 c a b))))
      (else y (s7-gcall2 c a b)))))
(define* s7-flt? (subr s7-eff (s7-global s7-value s7-value) bool)
  (lambda (c a b)
    (tagcase a
      (int i (tagcase b (int j (if (get s7-builtins-intact) (< i j) (s7-true? (s7-gcall2 c a b)))) (else y (s7-true? (s7-gcall2 c a b)))))
      (else y (s7-true? (s7-gcall2 c a b))))))
(define* s7-fgt (subr s7-eff (s7-global s7-value s7-value) s7-value)
  (lambda (c a b)
    (tagcase a
      (int i (tagcase b (int j (if (get s7-builtins-intact) (if (> i j) s7-true s7-false) (s7-gcall2 c a b))) (else y (s7-gcall2 c a b))))
      (else y (s7-gcall2 c a b)))))
(define* s7-fgt? (subr s7-eff (s7-global s7-value s7-value) bool)
  (lambda (c a b)
    (tagcase a
      (int i (tagcase b (int j (if (get s7-builtins-intact) (> i j) (s7-true? (s7-gcall2 c a b)))) (else y (s7-true? (s7-gcall2 c a b)))))
      (else y (s7-true? (s7-gcall2 c a b))))))
(define* s7-fle (subr s7-eff (s7-global s7-value s7-value) s7-value)
  (lambda (c a b)
    (tagcase a
      (int i (tagcase b (int j (if (get s7-builtins-intact) (if (<= i j) s7-true s7-false) (s7-gcall2 c a b))) (else y (s7-gcall2 c a b))))
      (else y (s7-gcall2 c a b)))))
(define* s7-fle? (subr s7-eff (s7-global s7-value s7-value) bool)
  (lambda (c a b)
    (tagcase a
      (int i (tagcase b (int j (if (get s7-builtins-intact) (<= i j) (s7-true? (s7-gcall2 c a b)))) (else y (s7-true? (s7-gcall2 c a b)))))
      (else y (s7-true? (s7-gcall2 c a b))))))
(define* s7-fge (subr s7-eff (s7-global s7-value s7-value) s7-value)
  (lambda (c a b)
    (tagcase a
      (int i (tagcase b (int j (if (get s7-builtins-intact) (if (>= i j) s7-true s7-false) (s7-gcall2 c a b))) (else y (s7-gcall2 c a b))))
      (else y (s7-gcall2 c a b)))))
(define* s7-fge? (subr s7-eff (s7-global s7-value s7-value) bool)
  (lambda (c a b)
    (tagcase a
      (int i (tagcase b (int j (if (get s7-builtins-intact) (>= i j) (s7-true? (s7-gcall2 c a b)))) (else y (s7-true? (s7-gcall2 c a b)))))
      (else y (s7-true? (s7-gcall2 c a b))))))
(define* s7-fnum= (subr s7-eff (s7-global s7-value s7-value) s7-value)
  (lambda (c a b)
    (tagcase a
      (int i (tagcase b (int j (if (get s7-builtins-intact) (if (= i j) s7-true s7-false) (s7-gcall2 c a b))) (else y (s7-gcall2 c a b))))
      (else y (s7-gcall2 c a b)))))
(define* s7-fnum=? (subr s7-eff (s7-global s7-value s7-value) bool)
  (lambda (c a b)
    (tagcase a
      (int i (tagcase b (int j (if (get s7-builtins-intact) (= i j) (s7-true? (s7-gcall2 c a b)))) (else y (s7-true? (s7-gcall2 c a b)))))
      (else y (s7-true? (s7-gcall2 c a b))))))
(define* s7-fcar (subr s7-eff (s7-global s7-value) s7-value)
  (lambda (c a) (tagcase a (pair p (if (get s7-builtins-intact) (get (extract p car)) (s7-gcall1 c a))) (else y (s7-gcall1 c a)))))
(define* s7-fcdr (subr s7-eff (s7-global s7-value) s7-value)
  (lambda (c a) (tagcase a (pair p (if (get s7-builtins-intact) (get (extract p cdr)) (s7-gcall1 c a))) (else y (s7-gcall1 c a)))))
(define* s7-fnull (subr s7-eff (s7-global s7-value) s7-value)
  (lambda (c a) (if (get s7-builtins-intact) (tagcase a (null u s7-true) (else y s7-false)) (s7-gcall1 c a))))
(define* s7-fnull? (subr s7-eff (s7-global s7-value) bool)
  (lambda (c a) (if (get s7-builtins-intact) (tagcase a (null u #t) (else y #f)) (s7-true? (s7-gcall1 c a)))))
(define* s7-fpair (subr s7-eff (s7-global s7-value) s7-value)
  (lambda (c a) (if (get s7-builtins-intact) (tagcase a (pair u s7-true) (else y s7-false)) (s7-gcall1 c a))))
(define* s7-fpair? (subr s7-eff (s7-global s7-value) bool)
  (lambda (c a) (if (get s7-builtins-intact) (tagcase a (pair u #t) (else y #f)) (s7-true? (s7-gcall1 c a)))))
(define* s7-fnot (subr s7-eff (s7-global s7-value) s7-value)
  (lambda (c a) (if (get s7-builtins-intact) (tagcase a (bool b (if b s7-false s7-true)) (else y s7-false)) (s7-gcall1 c a))))
(define* s7-fnot? (subr s7-eff (s7-global s7-value) bool)
  (lambda (c a) (if (get s7-builtins-intact) (tagcase a (bool b (not b)) (else y #f)) (s7-true? (s7-gcall1 c a)))))
(define* s7-fzero (subr s7-eff (s7-global s7-value) s7-value)
  (lambda (c a) (tagcase a (int i (if (get s7-builtins-intact) (if (= i 0) s7-true s7-false) (s7-gcall1 c a))) (else y (s7-gcall1 c a)))))
(define* s7-fzero? (subr s7-eff (s7-global s7-value) bool)
  (lambda (c a) (if (get s7-builtins-intact) (tagcase a (int i (= i 0)) (else y (s7-true? (s7-gcall1 c a)))) (s7-true? (s7-gcall1 c a)))))
(define* s7-feq (subr s7-eff (s7-global s7-value s7-value) s7-value)
  (lambda (c a b) (if (get s7-builtins-intact) (if (s7-eqv? a b) s7-true s7-false) (s7-gcall2 c a b))))
(define* s7-feq? (subr s7-eff (s7-global s7-value s7-value) bool)
  (lambda (c a b) (if (get s7-builtins-intact) (s7-eqv? a b) (s7-true? (s7-gcall2 c a b)))))
(define* s7-fcons (subr s7-eff (s7-global s7-value s7-value) s7-value)
  (lambda (c a b) (if (get s7-builtins-intact) (s7-cons a b) (s7-gcall2 c a b))))
;;; ------------------------------------------------------------ end of fused calls


;;; ------------------------------------------------------------ promises

"The record type of promises (prelude.scm's `promise`), once the prelude
says it (`%promise-type!`)."
(define s7-promise-rtd (ref (listof s7-rtd acyclic) @sc) (new nil))
"The fields of `v`, if it is a promise."
(define* s7-promise-fields (subr (read @sc) (s7-value) (sumof (none unit) (some (arrayof s7-value @sc))))
  (lambda (v)
    (tagcase v
      (record r (let ((t (get s7-promise-rtd)))
                  (if (and (pair? t) (eq? (extract (extract r rtd) id) (extract (car t) id)))
                      (sum some (extract r fields))
                      (sum none #u))))
      (else y (sum none #u)))))
"`force`, as R7RS 7.3's reference does it, written here, not in the
prelude: a promise's box, `(done? . value-or-thunk)`, shared by the
promises a `delay-force` chain makes, so that forcing one runs in constant
space."
(define* s7-force (subr s7-eff (s7-value) s7-value)
  (lambda (p)
    (tagcase (s7-promise-fields p)
      (none u p)
      (some fs
        (iterate loop s7-eff () s7-value
          (tagcase (array-ref fs 0)
            (pair b
              (if (s7-true? (get (extract b car)))
                  (get (extract b cdr))
                  (let* ((v (s7-call0 (get (extract b cdr))))
                         (fs2 (tagcase (s7-promise-fields v)
                                (some f f)
                                (none u (the (arrayof s7-value @sc) (make-array 1 (s7-cons s7-true v)))))))
                    ;; Read again: forcing the thunk may have forced this.
                    (begin
                      (tagcase (array-ref fs 0)
                        (pair b1 (unless (s7-true? (get (extract b1 car)))
                                   (tagcase (array-ref fs2 0)
                                     (pair b2 (begin (set (extract b1 car) (get (extract b2 car)))
                                                (set (extract b1 cdr) (get (extract b2 cdr)))
                                                (array-set! fs2 0 (array-ref fs 0))))
                                     (else y #u))))
                        (else y #u))
                      (loop)))))
            (else y (s7-error "force: not a promise's box" (list p)))))))))

"Whether the REPL shows value `v`: not if it is unspecified, or no values,
or a definition's name."
(define* s7-shown? (subr pure (s7-value) bool)
  (lambda (v) (tagcase v (unspec u #f) (multi l (pair? l)) (sym s #t) (else y #t))))
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

"The operations that move control, as built-ins (prims.fx has the rest):
`apply`, `call/cc`, `values`, `dynamic-wind`, the handlers, `force`;
`eval` and `load` are lower.fx's."
(define* s7-init-control! (subr s7-eff () unit)
  (lambda ()
    (begin
      (def-prim "apply" 1 -1 (a)
        (letrec ((spread (subr s7-eff (s7-values) (sumof (ok s7-values) (bad unit)))
                   ;; The arguments but the last, then the last's items.
                   (lambda (l)
                     (cond ((null? l) (sum ok nil))
                           ((null? (cdr l)) (tagcase (s7-list-items (car l)) (some items (sum ok items)) (none u (sum bad #u))))
                           (else (tagcase (spread (cdr l)) (ok rest (sum ok (cons (car l) rest))) (bad u (sum bad #u))))))))
          (tagcase (spread (cdr a))
            (ok l (sum ok (s7-calln (car a) l)))
            (bad u (s7-fail "apply: its last argument is no list" (list (s7-list a)))))))
      (def-prim "call-with-current-continuation" 1 1 (a) (sum ok (s7-call/cc (car a))))
      (s7-alias! "call/cc" "call-with-current-continuation")
      (def-prim "values" 0 -1 (a) (sum ok (s7-values-of a)))
      (def-prim "call-with-values" 2 2 (a) (sum ok (s7-calln (s7-arg2 a) (s7-values-in (s7-call0 (car a))))))
      (def-prim "dynamic-wind" 3 3 (a) (sum ok (s7-dynamic-wind (car a) (s7-arg2 a) (s7-arg3 a))))
      (def-prim "with-exception-handler" 2 2 (a) (sum ok (s7-with-handler (car a) (s7-arg2 a))))
      (def-prim "raise" 1 1 (a) (sum ok (s7-raise (car a) #f)))
      (def-prim "raise-continuable" 1 1 (a) (sum ok (s7-raise (car a) #t)))
      (def-prim "exit" 0 1 (a) (sum ok (abort-current-continuation s7-tag (sum exit (if (pair? a) (car a) s7-unspecified)))))
      (s7-alias! "emergency-exit" "exit")
      (s7-alias! " call-with-values" "call-with-values")
      (def-prim "force" 1 1 (a) (sum ok (s7-force (car a))))
      (def-prim "%promise-type!" 1 1 (a)
        (tagcase (car a)
          (rtd t (begin (set s7-promise-rtd (list t)) (sum ok s7-unspecified)))
          (else y (s7-wrong "%promise-type!" "a record type" y)))))))
