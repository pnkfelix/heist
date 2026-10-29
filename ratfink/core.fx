;;; core.fx: ratfink's types -- the values of checked programs, their terms,
;;; the compile-time environments, the context evaluation runs under --
;;; and the prompt tag that path aborts and errors go to.
;;;
;;; ratfink is shakedown (~/Dev/LangPlay/shakedown, at 80ed588), a bounded
;;; model checker written in Scheme for Larceny, in FX-26: docs/ratfink.md.
;;; Its files are module files, each made once, in order, from those before
;;; it (ratfink/program lists them; ratfink.fx makes them).
;;;
;;; shakedown's values are Larceny's own, a checked program's data and its
;;; text alike; here they are one type, `rf-value`. What differs:
;;;   - A mutable place is a slot of an array (`rf-slots`): a frame of
;;;     variables (slot 0 its enclosing frame), a global's cell (one slot),
;;;     a vector, a record's fields, and a pair (slot 0 its car, 1 its cdr).
;;;     So the store treats them alike, as shakedown's `slot-ref` does.
;;;   - A term is a product of its id, operator (a small int), arguments and
;;;     sort; its arguments are values (integers, booleans, terms).
;;;   - Where shakedown raises (a path's end, an error of its own), ratfink
;;;     aborts to `rf-tag`, with an `rf-signal`.
;;;
;;; State: everything at region @rf; control at @rk.

(module-parameters ())

(hide (define kit-lists (load-module "../kit/lists.fx"))
      (import kit-lists map for-each))

"What ratfink does: its state at @rf, control on @rk (aborts, and the
continuations splits capture), combo's state at @cb (`--solver combo`),
and the I/O of a checker: the clock, the standard output and error, files,
processes (z3, playback), the command line."
"What working on ratfink's own data does."
(define-effect rf-st (maxeff spin (read @globals) (read @rf) (write @rf) (alloc @rf) (io stderr)))
(define-effect rf-eff
  (maxeff spin (read @globals) (read @rf) (write @rf) (alloc @rf) (goto @rk) (comefrom @rk)
          (read @cb) (write @cb) (alloc @cb)
          (io clock) (io stdout) (io stderr) (io process) (io fs-read) (io fs-write) (io args)))

(define tables (load-module "fx26:table.fx"))
(import tables make-table table-ref table-set! table-has? table-count symbol-hash (type table))

(define-type strings (listof string acyclic))
(define-type symbols (listof symbol acyclic))
(define-type ints (listof int acyclic))

;;; ------------------------------------------------------------ values

"A value of a checked program, or a datum of its text."
(define-type rf-value
  (sumof (null unit)                    ; ()
         (unspec unit)                  ; shakedown's `unspecified`
         (eof unit)
         (unbound unit)                 ; a global not yet defined
         (unassigned unit)              ; a local not yet assigned
         (deleted unit)                 ; a hash table's deleted entry
         (bool bool)
         (int int)                      ; exact: FX-26's ints are bignums
         (ratio (productof (num int) (den int)))  ; exact, in lowest terms, den > 1
         (real f64)                     ; inexact
         (char char)
         (str string)
         (sym symbol)
         (pair rf-slots)                ; [car cdr]
         (vec rf-slots)
         (frame rf-slots)               ; [enclosing-frame var …]
         (term rf-term)                 ; an Int or Bool term
         (choice rf-term)               ; one of several symbols: an Int term of their indexes
         (union rf-members)             ; one of several values, each under a guard
         (multiple rf-vals)             ; (values v …), but for one
         (closure rf-closure)
         (prim rf-prim)
         (rtd rf-rtd)
         (inst rf-inst)
         (port rf-port)
         (table rf-table)))
(define-type rf-vals (listof rf-value acyclic))
(define-type rf-slots (arrayof rf-value @rf))
"A union's member: its guard (a Bool term) and value."
(define-type rf-member (productof (g rf-value) (v rf-value)))
(define-type rf-members (listof rf-member acyclic))

"A term: hash-consed, so terms of one id are one. `op`: see the op-
constants; `sort`: `sort-int` or `sort-bool`."
(define-type rf-term (productof (id int) (op int) (args rf-vals) (sort int)))

"A compiled lambda: `body` computes its value from a frame and a context.
`name` is for messages."
(define-type rf-proc (subr rf-eff (rf-slots rf-ctx) rf-value))
(define-type rf-code (productof (name symbol) (required int) (rest bool) (size int) (body rf-proc)))
(define-type rf-closure (productof (code rf-code) (env rf-slots)))
"A primitive: its procedure takes the context, the arguments and the call's
source (a datum)."
(define-type rf-pproc (subr rf-eff (rf-ctx rf-vals rf-value) rf-value))
(define-type rf-prim (productof (name symbol) (proc rf-pproc)))
"A record type of the checked program's, and an instance."
(define-type rf-rtd (productof (name symbol) (fields symbols) (id (ref unit @rf))))
(define-type rf-inst (productof (rtd rf-rtd) (fields rf-slots)))
"A textual port: `kind` input, output (a string port) or console; an input
port's text; its cell, #(position-or-strings open?)."
(define-type rf-port (productof (kind symbol) (text string) (cell rf-slots)))
"A hash table of the checked program's: its equivalence (the symbol eqv or
equal, or a procedure), a cell holding its entries, and whether it may be
changed."
(define-type rf-table (productof (equiv rf-value) (cell rf-slots) (mutable bool)))

"The context of evaluation: the path condition, how many symbolic
branches it is inside, and the unwinding alist (closures to the depth and
count of their activations)."
(define-type rf-unwind (productof (f rf-closure) (depth int) (count int)))
(define-type rf-unwinds (listof rf-unwind acyclic))
(define-type rf-ctx (productof (pc rf-value) (depth int) (unwind rf-unwinds)))
(define* make-ctx (subr pure (rf-value int rf-unwinds) rf-ctx)
  (lambda (pc depth unwind) (product (pc pc) (depth depth) (unwind unwind))))
(define* ctx-pc (subr pure (rf-ctx) rf-value) (lambda (c) (extract c pc)))
(define* ctx-depth (subr pure (rf-ctx) int) (lambda (c) (extract c depth)))
(define* ctx-unwind (subr pure (rf-ctx) rf-unwinds) (lambda (c) (extract c unwind)))

;;; ------------------------------------------------------------ compile-time environments

"A global environment: its variables' cells and its macros by name, and the
environment it inherits the rest from. A macro removed is `none`."
(define-type rf-genv
  (productof (cells (table symbol rf-slots @rf)) (macros (table symbol rf-maybe-macro @rf))
             (parent (sumof (none unit) (some rf-genv)))))
(define-type rf-maybe-macro (sumof (none unit) (some rf-macro)))
"A compile-time environment: frames, innermost first."
(define-type rf-cenv (listof rf-cframe acyclic))
(define-type rf-cframe (sumof (vframe rf-vframe) (sframe rf-sframe)))
"A frame of variables, and the loops with invariants named by them (by
index)."
(define-type rf-vframe (productof (vars (ref symbols @rf)) (loops (ref (listof rf-loop-at acyclic) @rf))))
(define-type rf-loop-at (productof (index int) (loop rf-loop)))
"A frame of macros (a body's, a let-syntax's): name to macro."
(define-type rf-sframe (ref (listof (productof (name symbol) (macro rf-macro)) acyclic) @rf))
"A syntax-rules macro: its ellipsis, literals, rules (pattern without its
keyword, and template), and where it was defined; `lib`, for playback's
macros, the library it is of (where shakedown keeps a library's name in
place of the global environment), else #f."
(define-type rf-rule (productof (pattern rf-value) (template rf-value)))
(define-type rf-macro
  (productof (ellipsis symbol) (literals symbols) (rules (listof rf-rule acyclic))
             (cenv rf-cenv) (genv rf-genv) (lib rf-value)))

"A loop with an invariant (eval.fx): its name and arity; its invariants and
measure, each an expression and its code (of a frame of the variables);
and while its body runs, the measure at its head and the frame holding its
name."
(define-type rf-expr-code (productof (expr rf-value) (code rf-proc)))
(define-type rf-loop
  (productof (name string) (arity int)
             (invariants (ref (listof rf-expr-code acyclic) @rf))
             (decreases (ref (sumof (none unit) (some rf-expr-code)) @rf))
             (state (ref (sumof (none unit) (some (productof (measure rf-value) (frame rf-slots)))) @rf))))

;;; ------------------------------------------------------------ aborts

"Where shakedown raises: the end of a path, a split's arm done, or an error
of ratfink's own (a message and irritants, as Scheme's `error` takes)."
(define-type rf-signal
  (sumof (abort unit)
         (finished rf-value)
         (err (productof (message string) (irritants rf-vals)))))
(define rf-tag (prompt-tag rf-value rf-signal rf-eff @rk) (make-continuation-prompt-tag))
"A split's continuation: the rest of a proof, up to its prompt."
(define-type rf-kont (composable rf-value rf-value rf-eff @rk))

(define* rf-signal! (subr rf-eff (rf-signal) void)
  (lambda (s) ((proj (proj abort-current-continuation @rk) rf-value rf-signal rf-eff) rf-tag s)))
"Scheme's `error`, as shakedown's own code calls it."
(define* rf-error (subr rf-eff (string rf-vals) void)
  (lambda (message irritants) (rf-signal! (sum err (product (message message) (irritants irritants))))))
"(thunk), and if it signals, (handler signal)."
(define* rf-catch (subr rf-eff ((subr rf-eff () rf-value) (subr rf-eff (rf-signal) rf-value)) rf-value)
  (lambda (thunk handler) (prompt rf-tag (thunk) handler)))
"(thunk); if it signals, (cleanup) and the signal again: shakedown's
`(guard (e (#t (cleanup) (raise e))) …)`."
(define* rf-protect (subr rf-eff ((subr rf-eff () rf-value) (subr rf-eff () unit)) rf-value)
  (lambda (thunk cleanup) (prompt rf-tag (thunk) (lambda ((s rf-signal)) (begin (cleanup) (rf-signal! s))))))
(define* rf-abort? (subr pure (rf-signal) bool) (lambda (s) (tagcase s (abort u #t) (else x #f))))

;;; ------------------------------------------------------------ small values

(define rf-nil rf-value (sum null #u))
(define rf-unspecified rf-value (sum unspec #u))
(define rf-eof rf-value (sum eof #u))
(define rf-true rf-value (sum bool #t))
(define rf-false rf-value (sum bool #f))
(define rf-unbound rf-value (sum unbound #u))
(define rf-unassigned rf-value (sum unassigned #u))
(define rf-deleted rf-value (sum deleted #u))
(define* rf-bool (subr pure (bool) rf-value) (lambda (b) (if b rf-true rf-false)))
(define* rf-int (subr pure (int) rf-value) (lambda (i) (sum int i)))
(define* rf-sym (subr pure (symbol) rf-value) (lambda (s) (sum sym s)))
(define* rf-str (subr pure (string) rf-value) (lambda (s) (sum str s)))

(define* rf-null? (subr pure (rf-value) bool) (lambda (v) (tagcase v (null u #t) (else x #f))))
(define* rf-pair? (subr pure (rf-value) bool) (lambda (v) (tagcase v (pair p #t) (else x #f))))
(define* rf-symbol? (subr pure (rf-value) bool) (lambda (v) (tagcase v (sym s #t) (else x #f))))
(define* rf-string? (subr pure (rf-value) bool) (lambda (v) (tagcase v (str s #t) (else x #f))))
(define* rf-vector? (subr pure (rf-value) bool) (lambda (v) (tagcase v (vec a #t) (else x #f))))
(define* rf-exact-integer? (subr pure (rf-value) bool) (lambda (v) (tagcase v (int i #t) (else x #f))))
(define* rf-boolean? (subr pure (rf-value) bool) (lambda (v) (tagcase v (bool b #t) (else x #f))))
(define* rf-false? (subr pure (rf-value) bool) (lambda (v) (tagcase v (bool b (not b)) (else x #f))))
(define* rf-true? (subr pure (rf-value) bool) (lambda (v) (tagcase v (bool b b) (else x #f))))
(define* rf-term? (subr pure (rf-value) bool) (lambda (v) (tagcase v (term t #t) (else x #f))))
(define* rf-union? (subr pure (rf-value) bool) (lambda (v) (tagcase v (union u #t) (else x #f))))
(define* rf-choice? (subr pure (rf-value) bool) (lambda (v) (tagcase v (choice t #t) (else x #f))))
(define* rf-closure? (subr pure (rf-value) bool) (lambda (v) (tagcase v (closure c #t) (else x #f))))
(define* rf-prim? (subr pure (rf-value) bool) (lambda (v) (tagcase v (prim p #t) (else x #f))))
(define* rf-multiple? (subr pure (rf-value) bool) (lambda (v) (tagcase v (multiple m #t) (else x #f))))
(define* rf-unspecified? (subr pure (rf-value) bool) (lambda (v) (tagcase v (unspec u #t) (else x #f))))
(define* rf-inst? (subr pure (rf-value) bool) (lambda (v) (tagcase v (inst i #t) (else x #f))))
(define* rf-char? (subr pure (rf-value) bool) (lambda (v) (tagcase v (char c #t) (else x #f))))
(define* rf-unbound? (subr pure (rf-value) bool) (lambda (v) (tagcase v (unbound u #t) (else x #f))))
(define* rf-unassigned? (subr pure (rf-value) bool) (lambda (v) (tagcase v (unassigned u #t) (else x #f))))
(define* rf-eof? (subr pure (rf-value) bool) (lambda (v) (tagcase v (eof u #t) (else x #f))))
(define* rf-deleted? (subr pure (rf-value) bool) (lambda (v) (tagcase v (deleted u #t) (else x #f))))
"A number: exact or inexact, concrete."
(define* rf-number? (subr pure (rf-value) bool)
  (lambda (v) (tagcase v (int i #t) (ratio q #t) (real r #t) (else x #f))))

"The int of an exact integer value (0 for anything else)."
(define* rf-int-of (subr pure (rf-value) int) (lambda (v) (tagcase v (int i i) (else x 0))))
(define* rf-sym-of (subr pure (rf-value) symbol) (lambda (v) (tagcase v (sym s s) (else x '||))))
(define* rf-str-of (subr pure (rf-value) string) (lambda (v) (tagcase v (str s s) (else x ""))))
(define no-slots rf-slots (the rf-slots (make-array 0 rf-unspecified)))
"The slots of a pair, vector or frame (none for anything else)."
(define* rf-slots-of (subr pure (rf-value) rf-slots)
  (lambda (v) (tagcase v (pair a a) (vec a a) (frame a a) (else x no-slots))))

;;; ------------------------------------------------------------ pairs and lists

(define* rf-cons (subr rf-st (rf-value rf-value) rf-value)
  (lambda (a d) (let ((s (the rf-slots (make-array 2 a)))) (begin (array-set! s 1 d) (sum pair s)))))
"The car and cdr of what is a pair (unspecified for anything else)."
(define* rf-car (subr rf-st (rf-value) rf-value)
  (lambda (v) (tagcase v (pair s (array-ref s 0)) (else x rf-unspecified))))
(define* rf-cdr (subr rf-st (rf-value) rf-value)
  (lambda (v) (tagcase v (pair s (array-ref s 1)) (else x rf-unspecified))))
(define* rf-cadr (subr rf-st (rf-value) rf-value) (lambda (v) (rf-car (rf-cdr v))))
(define* rf-cddr (subr rf-st (rf-value) rf-value) (lambda (v) (rf-cdr (rf-cdr v))))
(define* rf-caddr (subr rf-st (rf-value) rf-value) (lambda (v) (rf-car (rf-cddr v))))
(define* rf-cdddr (subr rf-st (rf-value) rf-value) (lambda (v) (rf-cdr (rf-cddr v))))
(define* rf-cadddr (subr rf-st (rf-value) rf-value) (lambda (v) (rf-car (rf-cdddr v))))
(define* rf-caar (subr rf-st (rf-value) rf-value) (lambda (v) (rf-car (rf-car v))))
(define* rf-cdar (subr rf-st (rf-value) rf-value) (lambda (v) (rf-cdr (rf-car v))))
(define* rf-cddddr (subr rf-st (rf-value) rf-value) (lambda (v) (rf-cdr (rf-cdddr v))))

"A list of FX-26's as a Scheme list."
(define* rf-list (subr rf-st (rf-vals) rf-value)
  (lambda (l) (if (null? l) rf-nil (rf-cons (car l) (rf-list (cdr l))))))
"The elements of a Scheme list, as far as it is one."
(define* rf-elements (subr rf-st (rf-value) rf-vals)
  (lambda (v) (tagcase v (pair s (cons (array-ref s 0) (rf-elements (array-ref s 1)))) (else x nil))))
"Whether v is a proper list."
(define* rf-list? (subr rf-st (rf-value) bool)
  (lambda (v) (tagcase v (null u #t) (pair s (rf-list? (array-ref s 1))) (else x #f))))
(define* rf-length (subr rf-st (rf-value) int)
  (lambda (v) (letrec ((go (subr rf-st (rf-value int) int)
                         (lambda (v n) (tagcase v (pair s (go (array-ref s 1) (+ n 1))) (else x n)))))
                (go v 0))))
(define* rf-append2 (subr rf-st (rf-value rf-value) rf-value)
  (lambda (a b) (tagcase a (pair s (rf-cons (array-ref s 0) (rf-append2 (array-ref s 1) b))) (else x b))))
(define* rf-reverse (subr rf-st (rf-value) rf-value)
  (lambda (v) (letrec ((go (subr rf-st (rf-value rf-value) rf-value)
                         (lambda (v acc) (tagcase v (pair s (go (array-ref s 1) (rf-cons (array-ref s 0) acc))) (else x acc)))))
                (go v rf-nil))))
(define* rf-list-tail (subr rf-st (rf-value int) rf-value)
  (lambda (v k) (if (<= k 0) v (rf-list-tail (rf-cdr v) (- k 1)))))
(define* rf-list-ref (subr rf-st (rf-value int) rf-value)
  (lambda (v k) (rf-car (rf-list-tail v k))))
(define* rf-list1 (subr rf-st (rf-value) rf-value) (lambda (a) (rf-cons a rf-nil)))
(define* rf-list2 (subr rf-st (rf-value rf-value) rf-value) (lambda (a b) (rf-cons a (rf-cons b rf-nil))))
(define* rf-list3 (subr rf-st (rf-value rf-value rf-value) rf-value)
  (lambda (a b c) (rf-cons a (rf-cons b (rf-cons c rf-nil)))))
"The symbol `s` as a value: for building forms."
(define* q (subr pure (symbol) rf-value) (lambda (s) (sum sym s)))

(define* vals-length (subr spin (rf-vals) int) (lambda (l) (list-length l)))
(define* vals-reverse (subr spin (rf-vals) rf-vals)
  (lambda (l) (letrec ((go (subr spin (rf-vals rf-vals) rf-vals) (lambda (l acc) (if (null? l) acc (go (cdr l) (cons (car l) acc))))))
                (go l nil))))
(define* vals-append (subr spin (rf-vals rf-vals) rf-vals)
  (lambda (a b) (if (null? a) b (cons (car a) (vals-append (cdr a) b)))))
(define* vals-ref (subr spin (rf-vals int) rf-value)
  (lambda (l k) (cond ((null? l) rf-unspecified) ((= k 0) (car l)) (else (vals-ref (cdr l) (- k 1))))))
(define* vals-tail (subr spin (rf-vals int) rf-vals)
  (lambda (l k) (if (or (null? l) (<= k 0)) l (vals-tail (cdr l) (- k 1)))))
(define* vals-head (subr spin (rf-vals int) rf-vals)
  (lambda (l k) (if (or (null? l) (<= k 0)) nil (cons (car l) (vals-head (cdr l) (- k 1))))))
(define* symbols-member? (subr spin (symbol symbols) bool)
  (lambda (s l) (cond ((null? l) #f) ((eq? s (car l)) #t) (else (symbols-member? s (cdr l))))))
(define* symbols-reverse (subr spin (symbols) symbols)
  (lambda (l) (letrec ((go (subr spin (symbols symbols) symbols) (lambda (l acc) (if (null? l) acc (go (cdr l) (cons (car l) acc))))))
                (go l nil))))

;;; ------------------------------------------------------------ identity

"eqv? of two values, as Larceny's on shakedown's: by value for numbers,
characters and the like, by identity for the rest. (A term is
hash-consed: one id, one term.)"
(define* rf-eqv? (subr pure (rf-value rf-value) bool)
  (lambda (a b)
    (tagcase a
      (null u (rf-null? b))
      (unspec u (rf-unspecified? b))
      (eof u (rf-eof? b))
      (unbound u (rf-unbound? b))
      (unassigned u (rf-unassigned? b))
      (deleted u (rf-deleted? b))
      (bool x (tagcase b (bool y (eq? x y)) (else z #f)))
      (int x (tagcase b (int y (= x y)) (else z #f)))
      (ratio x (tagcase b (ratio y (and (= (extract x num) (extract y num)) (= (extract x den) (extract y den)))) (else z #f)))
      (real x (tagcase b (real y (= (f64->bits x) (f64->bits y))) (else z #f)))
      (char x (tagcase b (char y (char=? x y)) (else z #f)))
      (str x (tagcase b (str y (eq? x y)) (else z #f)))
      (sym x (tagcase b (sym y (eq? x y)) (else z #f)))
      (pair x (tagcase b (pair y (eq? x y)) (else z #f)))
      (vec x (tagcase b (vec y (eq? x y)) (else z #f)))
      (frame x (tagcase b (frame y (eq? x y)) (else z #f)))
      (term x (tagcase b (term y (= (extract x id) (extract y id))) (else z #f)))
      (choice x (tagcase b (choice y (= (extract x id) (extract y id))) (else z #f)))
      (union x (tagcase b (union y (eq? x y)) (else z #f)))
      (multiple x (tagcase b (multiple y (eq? x y)) (else z #f)))
      (closure x (tagcase b (closure y (eq? x y)) (else z #f)))
      (prim x (tagcase b (prim y (eq? x y)) (else z #f)))
      (rtd x (tagcase b (rtd y (eq? (extract x id) (extract y id))) (else z #f)))
      (inst x (tagcase b (inst y (eq? (extract x fields) (extract y fields))) (else z #f)))
      (port x (tagcase b (port y (eq? (extract x cell) (extract y cell))) (else z #f)))
      (table x (tagcase b (table y (eq? (extract x cell) (extract y cell))) (else z #f))))))

;;; ------------------------------------------------------------ hash tables of any keys
;;;
;;; FX-26's tables (fx26:table.fx) need a pure hash and equality; a key
;;; compared by walking a list needs more (it may loop, as far as a type
;;; can say). These take any.

(define-type (htentry (k type) (v type)) (productof (key k) (val v)))
(define-type (htable (k type) (v type))
  (productof (hash (subr rf-st (k) int)) (same (subr rf-st (k k) bool))
             (buckets (ref (arrayof (listof (htentry k v) acyclic) @rf) @rf))
             (count (ref int @rf))))
(define* ht-make
  (poly ((k type) (v type)) (subr rf-st ((subr rf-st (k) int) (subr rf-st (k k) bool)) (htable k v)))
  (plambda ((k type) (v type))
    (lambda (hash same)
      (product (hash hash) (same same)
               (buckets (new (the (arrayof (listof (htentry k v) acyclic) @rf) (make-array 64 (the (listof (htentry k v) acyclic) nil)))))
               (count (new 0))))))
(define* ht-index
  (poly ((k type) (v type)) (subr rf-st ((htable k v) k) int))
  (plambda ((k type) (v type))
    (lambda (t key) (modulo ((extract t hash) key) (array-length (get (extract t buckets)))))))
(define* ht-find
  (poly ((k type) (v type)) (subr rf-st ((htable k v) k) (sumof (none unit) (some (htentry k v)))))
  (plambda ((k type) (v type))
    (lambda (t key)
      (letrec ((go (subr rf-st ((listof (htentry k v) acyclic)) (sumof (none unit) (some (htentry k v))))
                 (lambda (l) (cond ((null? l) (sum none #u))
                                   (((extract t same) (extract (car l) key) key) (sum some (car l)))
                                   (else (go (cdr l)))))))
        (go (array-ref (get (extract t buckets)) ((proj ht-index k v) t key)))))))
(define* ht-ref
  (poly ((k type) (v type)) (subr rf-st ((htable k v) k v) v))
  (plambda ((k type) (v type))
    (lambda (t key default) (tagcase ((proj ht-find k v) t key) (some e (extract e val)) (none u default)))))
(define* ht-has?
  (poly ((k type) (v type)) (subr rf-st ((htable k v) k) bool))
  (plambda ((k type) (v type))
    (lambda (t key) (tagcase ((proj ht-find k v) t key) (some e #t) (none u #f)))))
(define* ht-set!
  (poly ((k type) (v type)) (subr rf-st ((htable k v) k v) unit))
  (plambda ((k type) (v type))
    (lambda (t key val)
      (let* ((bs (get (extract t buckets)))
             (i ((proj ht-index k v) t key))
             (l (array-ref bs i)))
        (if (tagcase ((proj ht-find k v) t key) (some e #t) (none u #f))
            (array-set! bs i (map
                              (lambda ((e (htentry k v))) (if ((extract t same) (extract e key) key) (product (key key) (val val)) e))
                              l))
            (begin
              (array-set! bs i (cons (product (key key) (val val)) l))
              (set (extract t count) (+ 1 (get (extract t count))))
              (if (> (get (extract t count)) (* 2 (array-length bs))) ((proj ht-grow! k v) t) #u)))))))
(define* ht-grow!
  (poly ((k type) (v type)) (subr rf-st ((htable k v)) unit))
  (plambda ((k type) (v type))
    (lambda (t)
      (let* ((old (get (extract t buckets)))
             (n (* 2 (array-length old)))
             (new-bs (the (arrayof (listof (htentry k v) acyclic) @rf) (make-array n (the (listof (htentry k v) acyclic) nil)))))
        (letrec ((each (subr rf-st (int) unit)
                   (lambda (i)
                     (if (>= i (array-length old)) #u
                         (begin
                           (for-each
                            (lambda ((e (htentry k v)))
                              (let ((j (modulo ((extract t hash) (extract e key)) n)))
                                (array-set! new-bs j (cons e (array-ref new-bs j)))))
                            (array-ref old i))
                           (each (+ i 1)))))))
          (begin (each 0) (set (extract t buckets) new-bs)))))))

"An array's elements as a list."
(define slots-list (subr rf-st (rf-slots) rf-vals) (lambda (a) (the rf-vals (array->list a))))

"Whether x is eqv? to an element of l."
(define memq-val? (subr rf-st (rf-value rf-vals) bool)
  (lambda (x l) (cond ((null? l) #f) ((rf-eqv? x (car l)) #t) (else (memq-val? x (cdr l))))))
