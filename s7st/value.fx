;;; value.fx: s7st's values, its core syntax, and its machine's state.
;;;
;;; s7st is an interpreter of R7RS Scheme written in FX-26. Its files, in
;;; order (`s7st/program` lists them), each seeing the globals of those
;;; before it:
;;;
;;;   value.fx    what a Scheme value is; the core a program is expanded to;
;;;               the machine's continuations and state; the global table
;;;   read.fx     text to data, each list's span kept
;;;   print.fx    `display` and `write`
;;;   expand.fx   data to core: special forms, `syntax-rules`, bodies
;;;   prims.fx    the procedures written in FX-26
;;;   machine.fx  the machine: one step at a time, so a caller runs it in
;;;               slices, and interrupts it between them
;;;   prelude.fx  what is written in Scheme (`map`, `guard`, `parameterize`, …)
;;;   session.fx  what a client calls: input given, run, output taken
;;;
;;; The editor (editor/scheme.fx) and the command-line REPL (s7st/main.fx)
;;; are such clients. docs/s7st.md says what it does, and the openings left
;;; for a flow analysis and a compiler.
;;;
;;; Every name s7st defines begins `s7-`, so that the files can be read
;;; into a program before another's (the editor's) without either seeing
;;; the other's names. Its state is at region @sc.

"What the reader does: reads, writes and allocates at @sc (its spans,
what it makes), and loops."
(define-effect s7-read-eff (maxeff spin (read @globals) (read @sc) (write @sc) (alloc @sc)))
"What the machine does: reads and writes its own state, loops, reads and
writes files (`load`, `open-input-file`, `open-output-file`), reads the
clock (`current-jiffy`) and the command line, and runs `rm` (`delete-file`:
FX-26 has no primitive for it)."
(define-effect s7-eff (maxeff spin (read @globals) (read @sc) (write @sc) (alloc @sc) (io fs-read) (io fs-write) (io clock)
                              (io args) (io process)))
"What drives the machine may do besides: make kernels between slices
(native.fx), by Fixpt's encoder (`@k`) and `seal-code`. Kept out of
`s7-eff`, the effect of the code the machine runs, which never makes one."
(define-effect s7-drive-eff (maxeff s7-eff (io native) (read @k) (alloc @k)))

"kit's (../kit/, Heist's library), whose names do not begin `s7-`."
(define s7-kit-numbers (load-module "../kit/numbers.fx"))
(import s7-kit-numbers gcd expt exact-integer-sqrt floor-quotient number->string ratio->f64)
(define s7-kit-lists (load-module "../kit/lists.fx"))
(import s7-kit-lists map every any list-index member? take list-tail list-sort)
(define s7-kit-strings (load-module "../kit/strings.fx"))
(import s7-kit-strings string-concatenate)

;;; ------------------------------------------------------------ values

"A Scheme value. A pair, string, vector or bytevector is mutable, so it is
at @sc; a procedure has an identity (its `name` cell), as `eq?` needs."
(define-type s7-value
  (sumof (null unit)                    ; ()
         (unspec unit)                  ; what `set!` and its kin return
         (undef unit)                   ; a variable not yet defined
         (eof unit)                     ; the end-of-file object
         (bool bool)
         (int int)                      ; exact: FX-26's ints are bignums
         (ratio (productof (num int) (den int)))  ; exact, in lowest terms, den > 1
         (real f64)                     ; inexact
         (char char)
         (str (ref string @sc))
         (sym symbol)
         (pair s7-pair)
         (vec (arrayof s7-value @sc))
         (bytes (arrayof int @sc))      ; a bytevector, each 0 to 255
         (proc s7-closure)
         (prim s7-prim)
         (cont s7-cont)
         (multi s7-values)              ; `(values)` of other than one value
         (record s7-record)
         (rtd s7-rtd)
         (port s7-port)
         (table s7-table)               ; a hash table (table.fx)
         (env s7-ns)                    ; an environment, for `eval`: a namespace
         (errobj s7-errobj)))
(define-type s7-values (listof s7-value acyclic))
(define-type s7-symbols (listof symbol acyclic))
(define-type s7-strings (listof string acyclic))
(define-type s7-pair (productof (car (ref s7-value @sc)) (cdr (ref s7-value @sc)) (src s7-src)))
"Where a pair the reader made came from: the span of the list it begins
(if it begins one), and of the item it holds -- kept in the pair, so that
finding it is a field's read, and it goes when the pair goes. A pair
`cons` makes has none."
(define-type s7-src (sumof (none unit) (read (productof (list s7-span) (item s7-span)))))
"A closure: its lambda's clauses (one, but for `case-lambda`), each with its
body compiled; where it was made; and its name, which is also its identity."
(define-type s7-closure (productof (clauses (listof s7-clause acyclic)) (env s7-env) (name (ref string @sc))))
(define-type s7-clause (productof (info s7-lambda) (code s7-code) (kernel (ref (listof s7-kernel acyclic) @sc))))
"A clause's body as machine code (native.fx), if it has one: a loop over
integers. `frees`: the free variables it reads, after its parameters;
`self`: the variable through which it calls itself; `prims`: the globals
whose built-ins it does in line, by name, which must hold them still;
`consts`: the values it may return besides an integer."
(define-type s7-scratch (bloblet (fields) @sc))
(define-type s7-kernel-code (subr (conv native) (maxeff spin (read @sc) (write @sc)) (s7-scratch) int))
(define-type s7-kernel
  (productof (code s7-kernel-code)
             (frees (listof (productof (depth int) (index int)) acyclic))
             (self (sumof (none unit) (local (productof (depth int) (index int))) (global s7-global)))
             (prims (listof (productof (cell s7-global) (name string)) acyclic))
             (consts s7-values)))
"A procedure written in FX-26: a function of its arguments, or an operation
of the machine's own (`call/cc`, `apply`, …), numbered."
(define-type s7-prim (productof (name string) (min int) (max int) (op s7-op) (pure bool) (fast s7-fast)))   ; max -1: any
;; `pure`: it changes nothing another could see (no `!`, no I/O), so a quick
;; evaluation may call it, and call it again.
;; `fast`: for a pure one, the same of one or two arguments, called with no
;; list made; undefined where it cannot say (an error, a case not covered),
;; and `op` then asked.
(define-type s7-op (sumof (fn (subr s7-eff (s7-values) s7-out)) (ctl int)))
(define-type s7-fast (sumof (none unit) (f1 (subr s7-eff (s7-value) s7-value)) (f2 (subr s7-eff (s7-value s7-value) s7-value))))
"What a procedure written in FX-26 gives: a value, or a condition raised."
(define-type s7-out (sumof (ok s7-value) (raise s7-value)))
(define-type s7-cont (productof (k s7-k) (dyn s7-dyn) (id (ref unit @sc))))
(define-type s7-record (productof (rtd s7-rtd) (fields (arrayof s7-value @sc))))
(define-type s7-rtd (productof (name string) (fields s7-symbols) (id (ref unit @sc))))
"A port: of input, a text and where reading has reached; of output, what
was written, last first, and the file it goes to when flushed (\"\": none)."
(define-type s7-port
  (productof (id (ref unit @sc)) (input bool) (text string) (pos (ref int @sc))
             (out (ref (listof string acyclic) @sc)) (open (ref bool @sc)) (file string)
             ;; Binary: its characters are bytes, 0 to 255.
             (binary bool)))
"A library defined: its name, as written; its namespace; and what it
exports, each by the name importers see and its own."
(define-type s7-export (productof (external symbol) (internal symbol)))
(define-type s7-library (productof (name string) (ns s7-ns) (exports (listof s7-export acyclic))))
"A hash table (table.fx): its kind, its entries in order, and their index."
(define-type s7-ids
  (productof (pairs (eqtable (ref s7-value @sc) int @sc @sc))
             (cells (eqtable (ref string @sc) int @sc @sc))
             (arrays (eqtable (arrayof s7-value @sc) int @sc @sc))
             (bytes (eqtable (arrayof int @sc) int @sc @sc))
             (units (eqtable (ref unit @sc) int @sc @sc))))
(define-type s7-table
  (productof (id (ref unit @sc))
             (kind symbol)                                         ; eqv, equal, string or string-ci
             (keys (ref (arrayof s7-value @sc) @sc))               ; a deleted entry's key: undefined
             (vals (ref (arrayof s7-value @sc) @sc))
             (used (ref int @sc))                                  ; entries used, deleted or not
             (count (ref int @sc))                                 ; entries not deleted
             (buckets (ref (arrayof (listof int acyclic) @sc) @sc))
             (ids (ref s7-ids @sc))))

"A condition `error` makes (`kind`: error, read, file), or the machine."
(define-type s7-errobj (productof (kind symbol) (message string) (irritants s7-value)))

;;; ------------------------------------------------------------ the core

"Where a form came from: a file (\"\": typed, or made), and its span in
characters. Start -1: not known."
(define-type s7-span (productof (file string) (start int) (end int)))
"A form of the core, numbered: every node of a session has a number of its
own, for an analysis to key its facts by (docs/s7st.md, \"Openings\")."
(define-type s7-node (productof (id int) (span s7-span) (form s7-form)))
(define-type s7-nodes (listof s7-node acyclic))
"A variable at top level: its name, value, and the syntax the name is
bound to there (a special form, a macro), if any."
(define-type s7-global (productof (name symbol) (value (ref s7-value @sc)) (syntax (ref s7-syntax @sc))))
"A lambda: its number; its name, if it was given one; how many parameters
it requires, and whether the rest are a list; the size of its frame (its
parameters, then its body's definitions); its body; its parameters' names
and its definitions', in frame order."
(define-type s7-lambda
  (productof (id int) (name string) (required int) (rest bool) (size int) (body s7-node)
             (span s7-span) (names s7-symbols)))
"The core. A variable is a global's cell, or a frame slot by depth and
index -- resolved once, when expanded."
(define-type s7-form
  (sumof (n-const s7-value)
         (n-local (productof (depth int) (index int) (name symbol)))
         (n-global s7-global)
         (n-set-local (productof (depth int) (index int) (value s7-node)))
         (n-set-global (productof (cell s7-global) (value s7-node)))
         (n-define (productof (cell s7-global) (value s7-node)))
         (n-if (productof (test s7-node) (then s7-node) (else s7-node)))
         (n-lambda (listof s7-lambda acyclic))           ; more than one: case-lambda
         (n-seq s7-nodes)                                ; at least one
         (n-call (productof (op s7-node) (args s7-nodes)))
         (n-scope (productof (size int) (body s7-node) (names s7-symbols)))  ; letrec*, internal definitions
         (n-fail string)))                               ; a syntax error, raised if run

;;; ------------------------------------------------------------ syntax

"What a name is bound to as syntax: nothing, a special form (by its name),
or a macro."
(define-type s7-syntax (sumof (none unit) (special symbol) (macro s7-macro)))
"A `syntax-rules` macro: its literals, its ellipsis, its rules, and the
scopes and namespace it was defined in (where the free names its
templates bring in mean what they mean)."
(define-type s7-macro (productof (literals s7-symbols) (ellipsis symbol) (rules (listof s7-rule acyclic)) (scopes s7-scopes) (ns s7-ns)))
(define-type s7-rule (productof (pattern s7-value) (template s7-value)))
"A scope of the expander: a frame's names, last first, and how many; and
the macros bound in it (`let-syntax`, internal `define-syntax`)."
(define-type s7-scope
  (productof (names (ref s7-symbols @sc)) (count (ref int @sc))
             (macros (ref (listof (productof (name symbol) (macro s7-macro)) acyclic) @sc))))
(define-type s7-scopes (listof s7-scope acyclic))

;;; ------------------------------------------------------------ the machine

"Compiled code (machine.fx's `s7-compile`): what evaluating a node does,
given its environment, continuation and dynamic state -- the machine's next
state. And, for a node that allows it, a quick evaluation: its value got
with no step of the machine's, or undefined if it cannot be (it needs
steps, or has an error to report). A quick evaluation that gives undefined
has done nothing another could see, so the node may then be run as code,
which reports the error if there is one. (No wrapper is made for a value:
in Fixpt every sum is an object allocated.)"
(define-type s7-code (subr s7-eff (s7-env s7-k s7-dyn) s7-state))
(define-type s7-quick (subr s7-eff (s7-env) s7-value))
(define-type s7-compiled (productof (code s7-code) (quick (listof s7-quick acyclic))))   ; quick: none, or one
(define-type s7-compileds (listof s7-compiled acyclic))
"An environment: frames of slots, innermost first."
(define-type s7-env (sumof (top unit) (frame s7-frame)))
(define-type s7-frame (productof (slots (arrayof s7-value @sc)) (up s7-env)))
"The dynamic state: the `dynamic-wind`s entered, innermost first, and the
exception handlers installed."
(define-type s7-wind (productof (before s7-value) (after s7-value) (id (ref unit @sc))))
(define-type s7-winds (listof s7-wind acyclic))
(define-type s7-dyn (productof (winds s7-winds) (handlers s7-values)))
"A thunk to call, and the dynamic state to call it in (on the way to a
continuation's)."
(define-type s7-step (productof (thunk s7-value) (dyn s7-dyn)))
"A continuation's frames, innermost first. Immutable, so a continuation
may be resumed any number of times."
(define-type s7-kframe
  (sumof (k-if (productof (then s7-code) (else s7-code) (env s7-env)))
         (k-seq (productof (rest s7-compileds) (env s7-env)))
         ;; A call's operator and arguments evaluated so far, last first.
         (k-args (productof (done s7-values) (rest s7-compileds) (env s7-env)))
         (k-set-local (productof (depth int) (index int) (env s7-env)))
         (k-set-global s7-global)
         (k-define s7-global)
         (k-cwv s7-value)                                 ; call-with-values' consumer
         (k-restore s7-dyn)                               ; the dynamic state put back
         (k-dw-before (productof (before s7-value) (thunk s7-value) (after s7-value)))
         (k-dw-body (productof (after s7-value) (dyn s7-dyn)))
         (k-then-return s7-value)                         ; this value, not the one given
         (k-rewind (productof (steps (listof s7-step acyclic)) (k s7-k) (dyn s7-dyn) (value s7-value)))
         (k-raise s7-value)                               ; a handler returned from `raise`
         ;; Top-level forms still to run; whether each value is shown; the
         ;; text they were read from (for where an error is); the namespace
         ;; they are in.
         (k-top (productof (forms s7-values) (echo bool) (text string) (ns s7-ns)))))
(define-type s7-k (listof s7-kframe acyclic))
"The machine's state between steps."
(define-type s7-state
  (sumof (s-run (productof (code s7-code) (env s7-env) (k s7-k) (dyn s7-dyn)))
         (s-return (productof (value s7-value) (k s7-k) (dyn s7-dyn)))
         (s-apply (productof (proc s7-value) (args s7-values) (k s7-k) (dyn s7-dyn)))
         (s-raise (productof (obj s7-value) (continuable bool) (k s7-k) (dyn s7-dyn)))
         (s-done s7-value)
         (s-failed (productof (obj s7-value) (k s7-k)))))

;;; ------------------------------------------------------------ making values

(define s7-nil s7-value (sum null #u))
(define s7-unspecified s7-value (sum unspec #u))
(define s7-undefined s7-value (sum undef #u))
(define s7-true s7-value (sum bool #t))
(define s7-false s7-value (sum bool #f))
(define s7-no-span s7-span (product (file "") (start -1) (end -1)))
(define s7-no-dyn s7-dyn (product (winds nil) (handlers nil)))

(define s7-no-src s7-src (sum none #u))
(define* s7-cons (subr (alloc @sc) (s7-value s7-value) s7-value)
  (lambda (a d) (sum pair (product (car (new a)) (cdr (new d)) (src s7-no-src)))))
"A pair the reader makes: holding an item read at `item`, and beginning a
list read at `list` (no span if it begins none)."
(define* s7-cons-read (subr (alloc @sc) (s7-value s7-value s7-span s7-span) s7-value)
  (lambda (a d list item) (sum pair (product (car (new a)) (cdr (new d)) (src (sum read (product (list list) (item item))))))))
(define* s7-string (subr (alloc @sc) (string) s7-value)
  (lambda (s) (sum str (new s))))
(define* s7-symbol (subr pure (string) s7-value)
  (lambda (s) (sum sym (string->symbol s))))
"The exact number `n/d` (d not 0), in lowest terms: an int if it is one."
(define* s7-make-ratio (subr spin (int int) s7-value)
  (lambda (n d)
    (let* ((g (gcd n d))
           (sign (if (< d 0) -1 1))
           (nn (* sign (quotient n g)))
           (dd (* sign (quotient d g))))
      (if (= dd 1) (sum int nn) (sum ratio (product (num nn) (den dd)))))))
"Float `r` (finite) exactly, as an int or a ratio: a float is a binary
fraction, so doubling it enough makes it whole."
(define* s7-f64->exact (subr spin (f64) s7-value)
  (lambda (r)
    (letrec ((go (subr spin (f64 int) s7-value)
               (lambda (x k)
                 (if (or (f64= x (f64-floor x)) (> k 1100))
                     (s7-make-ratio (f64->int (f64-floor x)) (arithmetic-shift 1 k))
                     (go (f64* x 2.0) (+ k 1))))))
      (go r 0))))

"`l`'s items, last first, before `tail`: a loop, so that a long list takes
no native stack (a frame an item, which every collection would walk)."
(define* s7-reverse-onto (subr (maxeff spin (alloc @sc)) (s7-values s7-value) s7-value)
  (lambda (l tail) (if (null? l) tail (s7-reverse-onto (cdr l) (s7-cons (car l) tail)))))
"Whether `v` counts as true: all but #f."
(define* s7-true? (subr pure (s7-value) bool)
  (lambda (v) (tagcase v (bool b b) (else x #t))))
(define* s7-list (subr (maxeff spin (alloc @sc)) (s7-values) s7-value)
  (lambda (l) (s7-reverse-onto (reverse l) s7-nil)))
"`l`'s items before `tail`."
(define* s7-list* (subr (maxeff spin (alloc @sc)) (s7-values s7-value) s7-value)
  (lambda (l tail) (s7-reverse-onto (reverse l) tail)))
"Whether `a` and `b` are the same pair (their car cells are one cell)."
(define* s7-same-pair? (subr pure (s7-value s7-value) bool)
  (lambda (a b)
    (tagcase a
      (pair p (tagcase b (pair q (eq? (extract p car) (extract q car))) (else y #f)))
      (else y #f))))

"A proper list's items, or (none) if `v` is no proper list. A cycle is
found (the tortoise and the hare), so this ends."
(define* s7-list-items (subr (maxeff spin (read @sc)) (s7-value) (sumof (none unit) (some s7-values)))
  (lambda (v)
    (letrec ((go (subr (maxeff spin (read @sc)) (s7-value s7-value bool s7-values) (sumof (none unit) (some s7-values)))
               (lambda (fast slow step acc)
                 (tagcase fast
                   (null u (sum some (reverse acc)))
                   (pair p (let ((next (get (extract p cdr)))
                                 (slow2 (if step (tagcase slow (pair q (get (extract q cdr))) (else y slow)) slow)))
                             (if (and step (s7-same-pair? next slow2))
                                 (sum none #u)
                                 (go next slow2 (not step) (cons (get (extract p car)) acc)))))
                   (else y (sum none #u))))))
      (go v v #f nil))))
"An error object raised as a condition."
(define* s7-error-value (subr (maxeff spin (alloc @sc)) (string s7-values) s7-value)
  (lambda (message irritants)
    (sum errobj (product (kind 'error) (message message) (irritants (s7-list irritants))))))
(define* s7-fail (subr (maxeff spin (alloc @sc)) (string s7-values) s7-out)
  (lambda (message irritants) (sum raise (s7-error-value message irritants))))

;;; ------------------------------------------------------------ symbols

"A symbol a macro's template brings in is renamed, `name N`, with a space
no symbol read has, so that it binds nothing the macro's user wrote; where
it is free it means what `name` means (expand.fx). Its name, unrenamed."
(define* s7-unrename (subr spin (symbol) symbol)
  (lambda (s)
    (let* ((n (symbol->string s)) (len (string-length n)))
      (letrec ((go (subr spin (int) symbol)
                 (lambda (i)
                   (cond ((< i 1) s)
                         ((char=? (string-ref n i) #\space)
                          (if (< (+ i 1) len) (string->symbol (substring n 0 i)) s))
                         ((char-numeric? (string-ref n i)) (go (- i 1)))
                         (else s)))))
        (go (- len 1))))))
"Whether `s` is a renamed symbol."
(define* s7-renamed? (subr spin (symbol) bool)
  (lambda (s) (not (eq? (s7-unrename s) s))))
"The name a symbol shows: unrenamed, wholly."
(define* s7-symbol-name (subr spin (symbol) string)
  (lambda (s) (let ((u (s7-unrename s))) (if (eq? u s) (symbol->string s) (s7-symbol-name u)))))

;;; ------------------------------------------------------------ namespaces

"A namespace: names bound to global cells, by name's hash; and the
namespaces looked in after it (the built-ins'). There are three kinds: the
built-ins' (special forms, procedures written in FX-26, the prelude's), the
top level's (what a program or the REPL defines), and each library's.
Importing binds a name to the cell of the library that exports it, so a
name may be bound in more than one."
(define-type s7-ns-entry (productof (name symbol) (cell s7-global)))
(define-type s7-ns
  (productof (name string) (buckets (arrayof (listof s7-ns-entry acyclic) @sc)) (base (listof s7-ns acyclic))))
(define* s7-make-ns (subr (alloc @sc) (string int (listof s7-ns acyclic)) s7-ns)
  (lambda (name size base)
    (product (name name) (buckets (the (arrayof (listof s7-ns-entry acyclic) @sc) (make-array size (the (listof s7-ns-entry acyclic) nil))))
             (base base))))
(define s7-builtins s7-ns (s7-make-ns "builtins" 4096 nil))
(define s7-toplevel s7-ns (s7-make-ns "top level" 1024 (list s7-builtins)))
"The namespace forms are expanded in now."
(define s7-current-ns (ref s7-ns @sc) (new s7-builtins))
(define* s7-new-cell (subr (alloc @sc) (symbol) s7-global)
  (lambda (name)
    (product (name name) (value (the (ref s7-value @sc) (new s7-undefined)))
             (syntax (the (ref s7-syntax @sc) (new (the s7-syntax (sum none #u))))))))
"The cell `name` is bound to in `ns` itself (not its base)."
(define* s7-ns-own (subr (maxeff spin (read @sc)) (s7-ns symbol) (sumof (none unit) (found s7-global)))
  (lambda (ns name)
    (letrec ((find (subr spin ((listof s7-ns-entry acyclic)) (sumof (none unit) (found s7-global)))
               (lambda (l) (cond ((null? l) (sum none #u))
                                 ((eq? (extract (car l) name) name) (sum found (extract (car l) cell)))
                                 (else (find (cdr l)))))))
      (let ((bs (extract ns buckets)))
        (find (array-ref bs (modulo (symbol-name-hash name) (array-length bs))))))))
"The cell `name` is bound to in `ns`, or in its base."
(define* s7-ns-find (subr (maxeff spin (read @sc)) (s7-ns symbol) (sumof (none unit) (found s7-global)))
  (lambda (ns name)
    (tagcase (s7-ns-own ns name)
      (found c (sum found c))
      (none u (letrec ((bases (subr (maxeff spin (read @sc)) ((listof s7-ns acyclic)) (sumof (none unit) (found s7-global)))
                         (lambda (l) (if (null? l) (sum none #u)
                                         (tagcase (s7-ns-find (car l) name) (found c (sum found c)) (none u (bases (cdr l))))))))
                (bases (extract ns base)))))))
"`name` bound to `cell` in `ns`, in place of what it was bound to there."
(define* s7-ns-bind! (subr (maxeff spin (read @sc) (write @sc) (alloc @sc)) (s7-ns symbol s7-global) unit)
  (lambda (ns name cell)
    (let* ((bs (extract ns buckets))
           (h (modulo (symbol-name-hash name) (array-length bs))))
      (letrec ((drop (subr spin ((listof s7-ns-entry acyclic)) (listof s7-ns-entry acyclic))
                 (lambda (l) (cond ((null? l) nil) ((eq? (extract (car l) name) name) (cdr l)) (else (cons (car l) (drop (cdr l))))))))
        (array-set! bs h (cons (product (name name) (cell cell)) (drop (array-ref bs h))))))))
"The cell `name` is bound to in `ns` itself, made (undefined) if it is not
bound there: what a definition there defines."
(define* s7-ns-own-cell! (subr (maxeff spin (read @sc) (write @sc) (alloc @sc)) (s7-ns symbol) s7-global)
  (lambda (ns name)
    (tagcase (s7-ns-own ns name)
      (found c c)
      (none u (let ((c (s7-new-cell name))) (begin (s7-ns-bind! ns name c) c))))))
"The cell `name` means in `ns`: bound there or in its base, else made
there (a name defined later, or never)."
(define* s7-ns-cell! (subr (maxeff spin (read @sc) (write @sc) (alloc @sc)) (s7-ns symbol) s7-global)
  (lambda (ns name)
    (tagcase (s7-ns-find ns name)
      (found c c)
      (none u (s7-ns-own-cell! ns name)))))
"The names bound in `ns` itself, and their cells."
(define* s7-ns-entries (subr (maxeff spin (read @sc)) (s7-ns) (listof s7-ns-entry acyclic))
  (lambda (ns)
    (let ((bs (extract ns buckets)))
      (letrec ((go (subr (maxeff spin (read @sc)) (int (listof s7-ns-entry acyclic)) (listof s7-ns-entry acyclic))
                 (lambda (i acc)
                   (if (< i 0) acc
                       (go (- i 1) (letrec ((add (subr spin ((listof s7-ns-entry acyclic) (listof s7-ns-entry acyclic)) (listof s7-ns-entry acyclic))
                                                   (lambda (l acc) (if (null? l) acc (add (cdr l) (cons (car l) acc))))))
                                     (add (array-ref bs i) acc)))))))
        (go (- (array-length bs) 1) nil)))))

"The built-in cell of `name`, made if there is none."
(define* s7-global-cell (subr (maxeff spin (read @sc) (write @sc) (alloc @sc)) (symbol) s7-global)
  (lambda (name) (s7-ns-own-cell! s7-builtins name)))
"Built-in `name` defined as `v`, by its name in FX-26 strings."
(define* s7-define-global! (subr (maxeff spin (read @sc) (write @sc) (alloc @sc)) (string s7-value) unit)
  (lambda (name v) (set (extract (s7-global-cell (string->symbol name)) value) v)))

"A counter, for numbering nodes and lambdas."
(define s7-next-id (ref int @sc) (new 0))
(define* s7-fresh-id (subr (maxeff (read @sc) (write @sc)) () int)
  (lambda () (let ((n (get s7-next-id))) (begin (set s7-next-id (+ n 1)) n))))
