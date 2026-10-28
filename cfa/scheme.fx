;;; scheme.fx: Scheme for the CFA -- its texts expanded by s7st's own
;;; expander (../s7st/expand.fx), so that macros are expanded as they would
;;; be when run, into a namespace of the world's, never run; then turned
;;; into the core (core.fx). And Scheme as a language (`cf-scheme`).
;;;
;;; s7st's expanded core resolves a local to a frame slot (depth and index:
;;; a lambda's frame, or a scope's); each slot here is a variable. A global
;;; the world defines is a global variable; one it does not, a built-in of
;;; s7st, is a primitive. The built-ins that make or take apart pairs and
;;; vectors are allocation sites and fields, as FX-26's are, so that what a
;;; list holds is known.

(define-effect sc-eff (maxeff cf-eff s7-eff))

;;; ------------------------------------------------------------ Scheme data and built-ins
;;; (from s7st/flow.fx, s7st's own analysis, which the CFA replaced)

"Kinds of data, as abstract values."
(define s7-fv-unknown int 0)
(define s7-fv-number int 1)
(define s7-fv-string int 2)
(define s7-fv-char int 3)
(define s7-fv-boolean int 4)
(define s7-fv-symbol int 5)
(define s7-fv-null int 6)
(define s7-fv-unspec int 7)
(define s7-fv-eof int 8)
(define s7-fv-vector int 9)
(define s7-fv-bytevector int 10)
(define s7-fv-record int 11)
(define s7-fv-port int 12)
(define s7-fv-table int 13)
(define s7-fv-pair int 14)
(define s7-fv-values int 15)
(define s7-fv-other int 16)
(define s7-fv-kinds s7-strings
  (list "unknown" "number" "string" "char" "boolean" "symbol" "()" "unspecified" "eof" "vector" "bytevector"
        "record" "port" "hash-table" "pair" "values" "other"))
"The kind of a value the session has."
"A set of kinds, by number."
(define-type s7-fset (listof int acyclic))
(define* s7-fv-kind (subr pure (s7-value) int)
  (lambda (v)
    (tagcase v
      (int i s7-fv-number) (ratio q s7-fv-number) (real r s7-fv-number)
      (str s s7-fv-string) (char c s7-fv-char) (bool b s7-fv-boolean) (sym s s7-fv-symbol)
      (null u s7-fv-null) (unspec u s7-fv-unspec) (eof u s7-fv-eof) (vec a s7-fv-vector) (bytes b s7-fv-bytevector)
      (record r s7-fv-record) (port p s7-fv-port) (table t s7-fv-table) (pair p s7-fv-pair) (multi l s7-fv-values)
      (else y s7-fv-other))))

"What a built-in procedure returns, by its name: kinds; or unknown."
(define* s7-builtin-result (subr spin (string) s7-fset)
  (lambda (n)
    (let* ((k (string-length n))
           (ends (lambda ((x string)) (and (>= k (string-length x)) (string=? (substring n (- k (string-length x)) k) x))))
           (starts (lambda ((x string)) (and (>= k (string-length x)) (string=? (substring n 0 (string-length x)) x))))
           (is (lambda ((l s7-strings)) (letrec ((go (subr spin (s7-strings) bool) (lambda (l) (and (pair? l) (or (string=? (car l) n) (go (cdr l)))))))
                                          (go l)))))
      (cond ((ends "?") (list s7-fv-boolean))
            ((ends "!") (list s7-fv-unspec))
            ((is (list "+" "-" "*" "/" "abs" "max" "min" "quotient" "remainder" "modulo" "expt" "sqrt" "exact" "inexact"
                       "floor" "ceiling" "round" "truncate" "length" "string-length" "vector-length" "char->integer"
                       "string->number" "gcd" "lcm" "square" "exp" "log" "sin" "cos" "tan" "atan" "numerator" "denominator"
                       "exact->inexact" "inexact->exact" "bytevector-length" "bytevector-u8-ref" "hash-table-count" "digit-value"
                       "floor-quotient" "floor-remainder" "truncate-quotient" "truncate-remainder" "current-jiffy" "current-second"))
             (list s7-fv-number))
            ((or (starts "string") (is (list "substring" "number->string" "symbol->string" "list->string" "get-output-string")))
             (if (is (list "string->list")) (list s7-fv-pair s7-fv-null)
                 (if (is (list "string->symbol")) (list s7-fv-symbol)
                     (if (is (list "string->vector")) (list s7-fv-vector)
                         (if (is (list "string-ref")) (list s7-fv-char) (list s7-fv-string))))))
            ((or (starts "char-") (is (list "integer->char"))) (list s7-fv-char))
            ((is (list "cons" "list" "append" "reverse" "map" "list-copy" "list-tail" "vector->list" "make-list" "filter"
                       "remove" "delete" "iota" "sort" "list-sort" "hash-table-keys" "hash-table-values" "hash-table->alist"))
             (list s7-fv-pair s7-fv-null))
            ((is (list "member" "memq" "memv" "assoc" "assq" "assv")) (list s7-fv-pair s7-fv-boolean))
            ((or (starts "vector") (starts "make-vector") (is (list "list->vector"))) (list s7-fv-vector))
            ((is (list "display" "write" "newline" "write-char" "write-string" "for-each" "vector-for-each" "string-for-each"))
             (list s7-fv-unspec))
            ((is (list "not" "eq?" "eqv?" "equal?" "=" "<" ">" "<=" ">=")) (list s7-fv-boolean))
            ((is (list "read-char" "peek-char")) (list s7-fv-char s7-fv-eof))
            ((is (list "read-line")) (list s7-fv-string s7-fv-eof))
            ((or (starts "make-hash-table") (starts "make-eq") (starts "make-equal") (is (list "make-hashtable" "make-string-hashtable")))
             (list s7-fv-table))
            ((is (list "error" "raise" "exit")) nil)
            (else (list s7-fv-unknown))))))

"The data of `text`, as far as they read: those before an error."
(define* s7-read-lenient (subr s7-eff (string string) s7-values)
  (lambda (text file)
    (letrec ((go (subr s7-eff (int s7-values) s7-values)
               (lambda (i acc)
                 (tagcase (s7-read-at text i file)
                   (datum d (go (extract d end) (cons (extract d value) acc)))
                   (else y (reverse acc))))))
      (go 0 nil))))

;;; ------------------------------------------------------------ the language

"Built-ins that call a procedure on the elements of lists they are given."
(define sc-mapping strings (list "map" "for-each" "vector-map" "vector-for-each" "string-for-each" "string-map"))
"Built-ins whose result is part of what they are given."
(define sc-passing strings
  (list "append" "reverse" "list-copy" "list-tail" "list-ref" "memq" "memv" "member" "assq" "assv" "assoc"
        "last-pair" "values" "car" "cdr" "cadr" "cddr" "caar" "cdar" "vector-ref"))
"Built-ins that keep nothing they are given, and call none of it: their
result is data of the kinds `s7-builtin-result` says."
(define sc-first-order-kinds strings (list "number" "boolean" "string" "char" "symbol"))
(define sc-first-order strings
  (list "display" "write" "newline" "write-char" "write-string" "write-u8" "error" "exit" "length"))

(define* sc-kind-names (subr spin (s7-fset) strings)
  (lambda (s) (if (null? s) nil
                  (cons (letrec ((nth (subr spin (s7-strings int) string) (lambda (l k) (cond ((null? l) "unknown") ((= k 0) (car l)) (else (nth (cdr l) (- k 1)))))))
                          (nth s7-fv-kinds (car s)))
                        (sc-kind-names (cdr s))))))
(define* sc-all-in? (subr spin (strings strings) bool)
  (lambda (l in) (or (null? l) (and (cf-member? (car l) in) (sc-all-in? (cdr l) in)))))

(define cf-scheme cf-lang
  (product (name "scheme")
           (model (lambda ((n string))
                    (let ((kinds (sc-kind-names (s7-builtin-result n))))
                      (cond ((string=? n "apply") (m-apply))
                            ((cf-member? n sc-mapping) (m-map kinds))
                            ((cf-member? n sc-passing) (m-pass))
                            ((or (cf-member? n sc-first-order)
                                 (and (not (cf-member? "unknown" kinds)) (sc-all-in? kinds sc-first-order-kinds)
                                      (not (cf-member? n (list "string-for-each" "string-map")))))
                             (m-data #f kinds))
                            ;; It may keep or call what it is given.
                            (else (m-data #t kinds))))))))

;;; ------------------------------------------------------------ the core

"The frames around a node, innermost first: each a slot's variable by index."
(define-type sc-frames (listof (arrayof int @cf) acyclic))

(define* sc-span (subr cf-eff (s7-span) cf-span)
  (lambda (s) (product (file (cf-file (extract s file))) (start (extract s start)) (end (extract s end)))))
(define* sc-slot (subr cf-eff (sc-frames int int) int)
  (lambda (fs depth index)
    (cond ((null? fs) -1)
          ((> depth 0) (sc-slot (cdr fs) (- depth 1) index))
          ((< index (array-length (car fs))) (array-ref (car fs) index))
          (else -1))))
(define* sc-new-frame (subr cf-eff (int) (arrayof int @cf))
  (lambda (n) (let ((a (the (arrayof int @cf) (make-array n 0))))
                (letrec ((go (subr cf-eff (int) (arrayof int @cf)) (lambda (i) (if (>= i n) a (begin (array-set! a i (cf-new-var)) (go (+ i 1)))))))
                  (go 0)))))
(define* sc-kind-of (subr cf-eff (s7-value) int)
  (lambda (v) (cf-kind (letrec ((nth (subr spin (s7-strings int) string) (lambda (l k) (cond ((null? l) "other") ((= k 0) (car l)) (else (nth (cdr l) (- k 1)))))))
                         (nth s7-fv-kinds (s7-fv-kind v))))))

"The name of a global the world does not define, if it is a built-in."
(define* sc-builtin? (subr s7-eff (s7-global) bool)
  (lambda (g) (tagcase (get (extract g value)) (prim p #t) (proc p #t) (else y #f))))

(define-rec
  (sc-core (subr sc-eff (s7-node sc-frames) core)
    (lambda (n fs)
      (let ((sp (sc-span (extract n span))))
        (tagcase (extract n form)
          (n-const v (k-const (sc-kind-of v)))
          (n-local l (let ((v (sc-slot fs (extract l depth) (extract l index))))
                       (if (< v 0) (k-escape nil) (cf-ref v (s7-symbol-name (extract l name)) sp))))
          (n-global g (sc-global g sp))
          (n-set-local x (let ((v (sc-slot fs (extract x depth) (extract x index))))
                           (if (< v 0) (sc-core (extract x value) fs) (k-bind v (sc-core (extract x value) fs)))))
          (n-set-global x (k-bind (cf-global-var (s7-symbol-name (extract (extract x cell) name))) (sc-core (extract x value) fs)))
          (n-define x (let ((name (s7-symbol-name (extract (extract x cell) name))))
                        (begin (if (null? fs) (set cf-definition name) #u)
                          (k-bind (cf-global-var name) (sc-core (extract x value) fs)))))
          (n-if x (k-seq (list (sc-core (extract x test) fs) (k-alt (list (sc-core (extract x then) fs) (sc-core (extract x else) fs))))))
          (n-lambda ls (let ((cs (sc-lambdas ls fs))) (if (and (pair? cs) (null? (cdr cs))) (car cs) (k-alt cs))))
          (n-seq ns (k-seq (sc-all ns fs)))
          (n-call x (sc-call n (extract x op) (extract x args) fs))
          (n-scope x (sc-core (extract x body) (cons (sc-new-frame (extract x size)) fs)))
          (n-fail m (k-none nil))))))
  (sc-all (subr sc-eff (s7-nodes sc-frames) cores)
    (lambda (ns fs) (if (null? ns) nil (let ((c (sc-core (car ns) fs))) (cons c (sc-all (cdr ns) fs))))))
  (sc-global (subr sc-eff (s7-global cf-span) core)
    (lambda (g sp)
      (let ((name (s7-symbol-name (extract g name))))
        (cond ((cf-global-defined? name) (cf-ref (cf-global-var name) name sp))
              ((sc-builtin? g) (k-prim name))
              ;; Defined nowhere known: whatever it will be.
              (else (k-escape nil))))))
  ;; Each clause a lambda, its frame its parameters then its definitions.
  (sc-lambdas (subr sc-eff ((listof s7-lambda acyclic) sc-frames) cores)
    (lambda (ls fs)
      (if (null? ls) nil
          (let* ((l (car ls))
                 (frame (sc-new-frame (max (extract l size) (+ (extract l required) (if (extract l rest) 1 0)))))
                 (params (letrec ((go (subr cf-eff (int) ints) (lambda (i) (if (>= i (extract l required)) nil (cons (array-ref frame i) (go (+ i 1)))))))
                           (go 0)))
                 (body (sc-core (extract l body) (cons frame fs)))
                 (c (k-lam (cf-add-lambda (product (span (sc-span (extract l span)))
                                                   (name (if (string=? (extract l name) "") (cf-anonymous) (extract l name)))
                                                   (params params)
                                                   (rest (if (extract l rest) (array-ref frame (extract l required)) -1))
                                                   (body body))))))
            (cons c (sc-lambdas (cdr ls) fs))))))
  ;; A call: of a built-in that makes or takes apart pairs and vectors, as
  ;; sites and fields; else a call.
  (sc-call (subr sc-eff (s7-node s7-node s7-nodes sc-frames) core)
    (lambda (n op args fs)
      (let* ((sp (sc-span (extract n span)))
             (prim (tagcase (extract op form)
                     (n-global g (let ((name (s7-symbol-name (extract g name))))
                                   (if (and (not (cf-global-defined? name)) (sc-builtin? g)) name "")))
                     (else y "")))
             (as (sc-all args fs))
             (nargs (length as))
             (site (lambda ((kind string)) (cf-add-site (product (span sp) (kind kind) (tag ""))))))
        (cond
          ((and (string=? prim "cons") (= nargs 2))
           (k-alloc (site "pair") (list (product (label "car") (value (car as))) (product (label "cdr") (value (car (cdr as)))))))
          ((and (string=? prim "car") (= nargs 1)) (k-field (car as) "car"))
          ((and (string=? prim "cdr") (= nargs 1)) (k-field (car as) "cdr"))
          ((and (string=? prim "set-car!") (= nargs 2)) (k-seq (list (k-store (car as) "car" (car (cdr as))) (k-const (cf-kind "unspecified")))))
          ((and (string=? prim "set-cdr!") (= nargs 2)) (k-seq (list (k-store (car as) "cdr" (car (cdr as))) (k-const (cf-kind "unspecified")))))
          ;; A list of its elements: one pair site, its cdr itself or ().
          ((string=? prim "list")
           (let ((s (site "pair")))
             (if (null? as) (k-const (cf-kind "()"))
                 (k-alloc s (list (product (label "car") (value (k-alt as)))
                                  (product (label "cdr") (value (k-alt (list (k-const (cf-kind "()")) (k-alloc s nil))))))))))
          ((string=? prim "vector") (k-alloc (site "vector") (list (product (label "car") (value (k-alt as))))))
          ((and (string=? prim "make-vector") (>= nargs 1))
           (k-seq (list (car as) (k-alloc (site "vector") (list (product (label "car") (value (k-alt (cdr as)))))))))
          ((and (string=? prim "vector-ref") (= nargs 2)) (k-seq (list (car (cdr as)) (k-field (car as) "car"))))
          ((and (string=? prim "vector-set!") (= nargs 3))
           (k-seq (list (car (cdr as)) (k-store (car as) "car" (car (cdr (cdr as)))) (k-const (cf-kind "unspecified")))))
          (else
           (k-app (cf-add-call (product (span sp) (operator (sc-span (extract op span))))) (sc-core op fs) as)))))))

"The names a world's top level defines, each a global."
(define* sc-declare! (subr sc-eff (s7-nodes) unit)
  (lambda (ns)
    (if (null? ns) #u
        (begin
          (tagcase (extract (car ns) form)
            (n-define x (begin (cf-global-var (s7-symbol-name (extract (extract x cell) name))) #u))
            (n-seq l (sc-declare! l))
            (else y #u))
          (sc-declare! (cdr ns))))))

"Text `text` of `file`, its forms expanded in the current namespace, as
far as they read: libraries' bodies spliced, imports passed over."
(define* sc-expand (subr s7-eff (string string) s7-nodes)
  (lambda (text file)
    (letrec ((go (subr s7-eff (s7-values) s7-nodes)
               (lambda (fs)
                 (if (null? fs) nil
                     (let ((f (car fs)))
                       (cond ((s7-sym-named? (s7-car f) "import") (go (cdr fs)))
                             ((s7-sym-named? (s7-car f) "define-library")
                              (append (go (s7-library-body (s7-library-decls (s7-value->values (s7-cddr f))))) (go (cdr fs))))
                             (else (begin (set s7-syntax-errors nil) (let ((n (s7-expand-top f))) (cons n (go (cdr fs))))))))))))
      (go (s7-read-lenient text file)))))

"A world of Scheme files (`paths` and their `texts`), read as core: its
top levels, a core each, in order. They are expanded in a namespace of
their own, thrown away after, with what its renaming made."
(define* sc-world (subr sc-eff (strings strings) cores)
  (lambda (paths texts)
    (let* ((mark (s7-rename-mark))
           (ns (s7-make-ns "cfa" 256 (list s7-builtins)))
           (saved (get s7-current-ns))
           (nodes (begin (set s7-current-ns ns)
                    (letrec ((go (subr s7-eff (strings strings) (listof s7-nodes acyclic))
                               (lambda (ps ts) (if (null? ps) nil (let ((n (sc-expand (car ts) (car ps)))) (cons n (go (cdr ps) (cdr ts))))))))
                      (go paths texts)))))
      (begin
        (set s7-current-ns saved)
        (cf-reset!)
        (set cf-null-kind "()")
        (letrec ((go (subr sc-eff (strings) unit) (lambda (ps) (if (null? ps) #u (begin (cf-file (car ps)) (go (cdr ps)))))))
          (go paths))
        (letrec ((go (subr sc-eff ((listof s7-nodes acyclic)) unit) (lambda (l) (if (null? l) #u (begin (sc-declare! (car l)) (go (cdr l)))))))
          (go nodes))
        (cf-globals-declared!)
        (let ((tops (letrec ((go (subr sc-eff ((listof s7-nodes acyclic)) cores)
                               (lambda (l) (if (null? l) nil (let ((c (k-seq (sc-all (car l) nil)))) (cons c (go (cdr l))))))))
                      (go nodes))))
          (begin (s7-rename-release! mark) tops))))))
