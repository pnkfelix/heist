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
  (list "append" "reverse" "list-copy" "list-tail" "list-ref" "memq" "memv" "assq" "assv"
        "last-pair" "values" "car" "cdr" "cadr" "cddr" "caar" "cdar" "vector-ref" "last" "list-sort" "sort" "vector-sort"))

"A call a built-in makes, of its argument `proc`, given `args`."
(define* sc-c (subr pure (int (listof cf-arg acyclic)) cf-callspec) (lambda (proc args) (product (proc proc) (args args))))
(define sc-unknown cf-arg (a-kinds (list "unknown")))
"Built-ins that call what they are given, as they do: s7st's control
operations (prims.fx) and the prelude's procedures (prelude.scm) that take
one. (none) for another."
(define* sc-calls-model (subr spin (string) (sumof (none unit) (model cf-model)))
  (lambda (n)
    (let ((m (lambda ((specs (listof cf-callspec acyclic)) (result cf-arg) (escapes (listof cf-arg acyclic)))
               (the (sumof (none unit) (model cf-model)) (sum model (m-calls specs result escapes))))))
      (cond
        ((or (string=? n "call-with-current-continuation") (string=? n "call/cc"))
         ;; The continuation is code not known: what it is given escapes.
         (m (list (sc-c 0 (list sc-unknown))) (a-union (list (a-result 0) sc-unknown)) nil))
        ((string=? n "dynamic-wind") (m (list (sc-c 0 nil) (sc-c 1 nil) (sc-c 2 nil)) (a-result 1) nil))
        ((string=? n "call-with-values") (m (list (sc-c 0 nil) (sc-c 1 (list (a-many (a-result 0))))) (a-result 1) nil))
        ((string=? n "with-exception-handler")
         (m (list (sc-c 1 nil) (sc-c 0 (list sc-unknown))) (a-union (list (a-result 0) (a-result 1))) nil))
        ((or (string=? n "filter") (string=? n "remove")) (m (list (sc-c 0 (list (a-elems 1)))) (a-arg 1) nil))
        ((or (string=? n "member") (string=? n "assoc") (string=? n "delete"))
         (m (list (sc-c 2 (list (a-arg 0) (a-elems 1)))) (a-union (list (a-arg 1) (a-kinds (list "boolean")))) nil))
        ((string=? n "delete-duplicates") (m (list (sc-c 1 (list (a-elems 0) (a-elems 0)))) (a-arg 0) nil))
        ((or (string=? n "fold") (string=? n "fold-right"))
         ;; Twice: the second given what the first returned too; again as that grows.
         (m (list (sc-c 0 (list (a-elems 2) (a-arg 1)))
                  (sc-c 0 (list (a-elems 2) (a-union (list (a-arg 1) (a-result 0))))))
            (a-union (list (a-arg 1) (a-result 1))) nil))
        ((string=? n "reduce")
         (m (list (sc-c 0 (list (a-elems 2) (a-union (list (a-elems 2) (a-arg 1)))))
                  (sc-c 0 (list (a-elems 2) (a-union (list (a-elems 2) (a-arg 1) (a-result 0))))))
            (a-union (list (a-arg 1) (a-elems 2) (a-result 1))) nil))
        ((or (string=? n "any") (string=? n "every"))
         (m (list (sc-c 0 (list (a-elems 1)))) (a-union (list (a-result 0) (a-kinds (list "boolean")))) nil))
        ((or (string=? n "count") (string=? n "list-index"))
         (m (list (sc-c 0 (list (a-elems 1)))) (a-kinds (list "number" "boolean")) nil))
        ((string=? n "append-map") (m (list (sc-c 0 (list (a-elems 1)))) (a-result 0) nil))
        ((string=? n "filter-map") (m (list (sc-c 0 (list (a-elems 1)))) (a-kinds (list "pair" "()")) (list (a-result 0))))
        ((string=? n "list-sort") (m (list (sc-c 0 (list (a-elems 1) (a-elems 1)))) (a-arg 1) nil))
        ((string=? n "sort") (m (list (sc-c 1 (list (a-elems 0) (a-elems 0)))) (a-arg 0) nil))
        ((string=? n "hash-table-ref")
         (m (list (sc-c 2 nil) (sc-c 3 (list sc-unknown))) (a-union (list sc-unknown (a-result 0) (a-result 1))) nil))
        ((string=? n "hash-table-update!") (m (list (sc-c 3 nil) (sc-c 2 (list sc-unknown))) (a-kinds (list "unspecified")) (list (a-result 1))))
        ((string=? n "hash-table-update!/default")
         (m (list (sc-c 2 (list sc-unknown))) (a-kinds (list "unspecified")) (list (a-result 0) (a-arg 3))))
        ((string=? n "hash-table-intern!") (m (list (sc-c 2 nil)) (a-union (list sc-unknown (a-result 0))) (list (a-result 0))))
        ((string=? n "hash-table-walk") (m (list (sc-c 1 (list sc-unknown sc-unknown))) (a-kinds (list "unspecified")) nil))
        ((string=? n "hash-table-fold")
         (m (list (sc-c 1 (list sc-unknown sc-unknown sc-unknown))) (a-union (list (a-arg 2) (a-result 0))) (list (a-arg 2))))
        ((or (string=? n "call-with-port") (string=? n "call-with-input-file") (string=? n "call-with-output-file"))
         (m (list (sc-c 1 (list (a-kinds (list "port"))))) (a-result 0) nil))
        ((or (string=? n "with-input-from-file") (string=? n "with-output-to-file")) (m (list (sc-c 1 nil)) (a-result 0) nil))
        ((string=? n "call-with-output-string") (m (list (sc-c 0 (list (a-kinds (list "port"))))) (a-kinds (list "string")) nil))
        ((string=? n "with-output-to-string") (m (list (sc-c 0 nil)) (a-kinds (list "string")) nil))
        (else (sum none #u))))))
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
                      (cond ((tagcase (sc-calls-model n) (model x #t) (else y #f))
                             (tagcase (sc-calls-model n) (model x x) (else y (m-apply))))
                            ((string=? n "apply") (m-apply))
                            ((cf-member? n sc-mapping) (m-map kinds))
                            ((cf-member? n sc-passing) (m-pass))
                            ((or (cf-member? n sc-first-order)
                                 (and (not (cf-member? "unknown" kinds)) (sc-all-in? kinds sc-first-order-kinds)
                                      (not (cf-member? n (list "string-for-each" "string-map")))))
                             (m-data #f kinds))
                            ;; It may keep or call what it is given.
                            (else (m-data #t kinds))))))))

;;; ------------------------------------------------------------ narrowing

"What a predicate says of what it is given: the classes it is true of
(`cf-narrowing`), and whether only of them (\"full\": false of all
else), or of some of them only (\"partial\": `integer?` is false of some
numbers). (none) if it is no predicate known."
(define-type sc-pred (productof (classes strings) (full bool)))
(define* sc-predicate (subr spin (string) (sumof (none unit) (pred sc-pred)))
  (lambda (n)
    (let ((full (lambda ((cs strings)) (the (sumof (none unit) (pred sc-pred)) (sum pred (product (classes cs) (full #t))))))
          (partial (lambda ((cs strings)) (the (sumof (none unit) (pred sc-pred)) (sum pred (product (classes cs) (full #f)))))))
      (cond ((string=? n "pair?") (full (list "pair")))
            ((string=? n "null?") (full (list "()")))
            ((string=? n "procedure?") (full (list "procedure")))
            ((string=? n "number?") (full (list "number")))
            ((string=? n "string?") (full (list "string")))
            ((string=? n "symbol?") (full (list "symbol")))
            ((string=? n "char?") (full (list "char")))
            ((string=? n "boolean?") (full (list "#t" "#f" "boolean")))
            ((string=? n "vector?") (full (list "vector")))
            ((string=? n "bytevector?") (full (list "bytevector")))
            ((string=? n "eof-object?") (full (list "eof")))
            ((string=? n "port?") (full (list "port")))
            ((string=? n "hash-table?") (full (list "hash-table")))
            ((string=? n "list?") (partial (list "pair" "()")))
            ((cf-member? n (list "integer?" "rational?" "real?" "complex?" "exact?" "inexact?" "exact-integer?" "exact-rational?"
                                 "zero?" "positive?" "negative?" "odd?" "even?" "nan?" "infinite?" "finite?"))
             (partial (list "number")))
            ((cf-member? n (list "input-port?" "output-port?" "textual-port?" "binary-port?")) (partial (list "port")))
            (else (sum none #u))))))
"The globals that are records' predicates (define-record-type's), by
name, and the type each is of."
(define sc-record-preds (ref (listof (productof (name string) (type string)) acyclic) @cf) (new nil))
(define* sc-record-pred (subr (maxeff spin (read @cf)) (string) string)
  (lambda (n) (letrec ((go (subr spin ((listof (productof (name string) (type string)) acyclic)) string)
                         (lambda (l) (cond ((null? l) "") ((string=? (extract (car l) name) n) (extract (car l) type)) (else (go (cdr l)))))))
                (go (get sc-record-preds)))))

"The globals that are records' accessors and modifiers, by name: the
field each is of; and the program's own procedures of one parameter, which
a test may call as a predicate (read as a formula of its body)."
(define-type sc-field-proc (productof (name string) (field string) (modifier bool)))
(define sc-record-fields (ref (listof sc-field-proc acyclic) @cf) (new nil))
(define* sc-record-field (subr (maxeff spin (read @cf)) (string bool) string)
  (lambda (n modifier)
    (letrec ((go (subr spin ((listof sc-field-proc acyclic)) string)
               (lambda (l) (cond ((null? l) "")
                                 ((and (string=? (extract (car l) name) n) (eq? (extract (car l) modifier) modifier)) (extract (car l) field))
                                 (else (go (cdr l)))))))
      (go (get sc-record-fields)))))
(define sc-user-preds (ref (listof (productof (name string) (lambda s7-lambda)) acyclic) @cf) (new nil))
(define* sc-user-pred (subr (maxeff spin (read @cf)) (string) (listof s7-lambda acyclic))
  (lambda (n) (letrec ((go (subr spin ((listof (productof (name string) (lambda s7-lambda)) acyclic)) (listof s7-lambda acyclic))
                         (lambda (l) (cond ((null? l) nil) ((string=? (extract (car l) name) n) (list (extract (car l) lambda))) (else (go (cdr l)))))))
                (go (get sc-user-preds)))))

"A constant node's value, if it is one."
(define* sc-const-of (subr spin (s7-node) (sumof (none unit) (const s7-value)))
  (lambda (n) (tagcase (extract n form) (n-const v (sum const v)) (else y (sum none #u)))))
"A constant's class (`cf-narrowing`): `'foo` for a symbol, `#t`, `#f`,
`()`, else its kind; and whether `eq?` to it says all (a symbol, a
boolean, ()), not only its kind."
(define* sc-const-class (subr spin (s7-value) string)
  (lambda (v) (tagcase v
                (bool b (if b "#t" "#f"))
                (sym s (string-append "'" (s7-symbol-name s)))
                (else y (letrec ((nth (subr spin (s7-strings int) string) (lambda (l k) (cond ((null? l) "other") ((= k 0) (car l)) (else (nth (cdr l) (- k 1)))))))
                          (nth s7-fv-kinds (s7-fv-kind v)))))))
(define* sc-exact-const? (subr spin (s7-value) bool)
  (lambda (v) (tagcase v (bool b #t) (sym s #t) (null u #t) (else y #f))))
(define* sc-all-exact? (subr spin (s7-values) bool)
  (lambda (l) (or (null? l) (and (sc-exact-const? (car l)) (sc-all-exact? (cdr l))))))
(define* map-strings (subr spin (s7-values) strings)
  (lambda (l) (if (null? l) nil (cons (sc-const-class (car l)) (map-strings (cdr l))))))
"A frame of `n` slots, none a variable known: for reading a body's tests."
(define* sc-blank-frame (subr (alloc @cf) (int) (arrayof int @cf))
  (lambda (n) (the (arrayof int @cf) (make-array (max n 1) -1))))
"A body's last form (its value)."
(define* sc-last-form (subr spin (s7-node) s7-node)
  (lambda (n) (tagcase (extract n form)
                (n-seq ns (if (pair? ns) (sc-last-form (car (reverse ns))) n))
                (else y n))))
"Whether `(lambda (t) (if t t b))` applied to one argument: `or`'s shape."
(define* sc-or-shape? (subr spin ((listof s7-lambda acyclic) s7-nodes) bool)
  (lambda (ls args)
    (and (pair? ls) (null? (cdr ls)) (pair? args) (null? (cdr args))
         (= (extract (car ls) required) 1) (not (extract (car ls) rest))
         (tagcase (extract (sc-last-form (extract (car ls) body)) form)
           (n-if i (and (tagcase (extract (extract i test) form) (n-local l (and (= (extract l depth) 0) (= (extract l index) 0))) (else y #f))
                        (tagcase (extract (extract i then) form) (n-local l (and (= (extract l depth) 0) (= (extract l index) 0))) (else y #f))))
           (else y #f)))))
"Whether a node cannot return: a call of `error`, `raise` or `exit`; a body
ending in one; an `if` neither branch of which can."
(define* sc-noreturn? (subr cf-eff (s7-node) bool)
  (lambda (n)
    (tagcase (extract n form)
      (n-call x (tagcase (extract (extract x op) form)
                  (n-global g (let ((name (s7-symbol-name (extract g name))))
                                (and (cf-member? name (list "error" "raise" "exit")) (not (cf-global-defined? name)))))
                  (else y #f)))
      (n-seq ns (and (pair? ns) (sc-noreturn? (car (reverse ns)))))
      (n-if x (and (sc-noreturn? (extract x then)) (sc-noreturn? (extract x else))))
      (else y #f))))

"What a test tells each branch of a local variable (`cf-narrowing`): what
the `then` branch knows, and what the `else` one does."
(define-type sc-told (productof (yes (listof cf-narrowing acyclic)) (no (listof cf-narrowing acyclic))))
(define sc-nothing-told sc-told (product (yes nil) (no nil)))
"A `let`'s variable bound to another variable, or a field of one (`case`'s
key, `or`'s temporary): what a test says of it, it says of that too; and
the subjects a lambda about to be read is applied to (`let`'s)."
(define sc-aliases (ref (listof (productof (var int) (source cf-path)) acyclic) @cf) (new nil))
(define sc-pending-args (ref (listof cf-path acyclic) @cf) (new nil))
"Narrowings `ns`, and each again of what its variable aliases."
(define* sc-with-aliases (subr (maxeff spin (read @cf)) ((listof cf-narrowing acyclic)) (listof cf-narrowing acyclic))
  (lambda (ns)
    (if (null? ns) nil
        (let* ((n (car ns))
               (src (letrec ((go (subr spin ((listof (productof (var int) (source cf-path)) acyclic)) (listof cf-path acyclic))
                                   (lambda (l) (cond ((null? l) nil) ((= (extract (car l) var) (extract n var)) (list (extract (car l) source))) (else (go (cdr l)))))))
                      (go (get sc-aliases))))
               (rest (sc-with-aliases (cdr ns))))
          (cons n (if (null? src) rest
                      (cons (product (var (extract (car src) var)) (path (append (extract (car src) path) (extract n path)))
                                     (classes (extract n classes)) (keep (extract n keep)))
                            rest)))))))
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
  (lambda (v) (tagcase v (sym s (cf-symbol-kind (s7-symbol-name s))) (else z (cf-kind (tagcase v (bool b (if b "#t" "#f")) (else y (letrec ((nth (subr spin (s7-strings int) string) (lambda (l k) (cond ((null? l) "other") ((= k 0) (car l)) (else (nth (cdr l) (- k 1)))))))
                         (nth s7-fv-kinds (s7-fv-kind v))))))))))

"The name of a global the world does not define, if it is a built-in."
(define* sc-builtin? (subr s7-eff (s7-global) bool)
  (lambda (g) (tagcase (get (extract g value)) (prim p #t) (proc p #t) (else y #f))))

"A symbol a constant is (\"\": none); the symbols a constant list is."
(define* sc-const-symbol (subr spin (s7-node) string)
  (lambda (n) (tagcase (extract n form) (n-const v (tagcase v (sym s (s7-symbol-name s)) (else y ""))) (else y ""))))
(define* sc-const-symbols (subr s7-eff (s7-node) strings)
  (lambda (n) (tagcase (extract n form)
                (n-const v (letrec ((go (subr s7-eff (s7-values) strings)
                                          (lambda (l) (if (null? l) nil
                                                          (cons (tagcase (car l) (sym s (s7-symbol-name s)) (else y "")) (go (cdr l)))))))
                             (go (s7-value->values v))))
                (else y nil))))
"What `define-record-type` defines (expand.fx's `s7-derive-record`), as
lambdas: `(record-constructor T '(f …))` one making a record site of those
fields, `(record-accessor T 'f)` one taking field f, `(record-modifier T 'f)`
one setting it, `(record-predicate T)` one saying a boolean; (none) for
another definition. `name`: the definition's."
(define* sc-record-proc (subr sc-eff (s7-node string) (sumof (none unit) (made core)))
  (lambda (n name)
    (tagcase (extract n form)
      (n-call x
        (let* ((op0 (tagcase (extract (extract x op) form) (n-global g (s7-symbol-name (extract g name))) (else y "")))
               ;; s7st's record procedures are named with a space first, so that no program names them.
               (op (if (and (> (string-length op0) 0) (char=? (string-ref op0 0) #\space)) (substring op0 1 (string-length op0)) op0))
               (args (extract x args))
               (type (if (pair? args) (tagcase (extract (car args) form) (n-global g (s7-symbol-name (extract g name))) (else y "")) ""))
               (sp (sc-span (extract n span)))
               (lam (lambda ((params ints) (body core))
                      (the (sumof (none unit) (made core))
                           (sum made (k-lam (cf-add-lambda (product (span sp) (name name) (params params) (rest -1) (body body)))))))))
          (cond
            ((cf-global-defined? op0) (sum none #u))
            ((and (string=? op "record-constructor") (pair? args) (pair? (cdr args)))
             (let* ((fields (sc-const-symbols (car (cdr args))))
                    (ps (letrec ((go (subr cf-eff (strings) ints) (lambda (l) (if (null? l) nil (cons (cf-new-var) (go (cdr l)))))))
                          (go fields))))
               (lam ps (k-alloc (cf-add-site (product (span sp) (kind "record") (tag type)))
                                (letrec ((go (subr spin (strings ints) (listof field-init acyclic))
                                               (lambda (fs ps) (if (or (null? fs) (null? ps)) nil
                                                                   (cons (product (label (car fs)) (value (k-var (car ps) -1))) (go (cdr fs) (cdr ps)))))))
                                  (go fields ps))))))
            ((and (string=? op "record-accessor") (pair? args) (pair? (cdr args)))
             (let ((r (cf-new-var))) (lam (list r) (k-field (k-var r -1) (sc-const-symbol (car (cdr args)))))))
            ((and (string=? op "record-modifier") (pair? args) (pair? (cdr args)))
             (let ((r (cf-new-var)) (v (cf-new-var)))
               (lam (list r v) (k-seq (list (k-store (k-var r -1) (sc-const-symbol (car (cdr args))) (k-var v -1))
                                            (k-const (cf-kind "unspecified")))))))
            ((string=? op "record-predicate")
             (let ((r (cf-new-var))) (lam (list r) (k-seq (list (k-var r -1) (k-const (cf-kind "boolean")))))))
            (else (sum none #u)))))
      (else y (sum none #u)))))

"The local variable a node reads, or a field of one: `(car (cdr x))`, x's
cdr then car, through built-in `car` and `cdr` and records' accessors (var
-1: none)."
(define* sc-subject (subr cf-eff (s7-node sc-frames) cf-path)
  (lambda (n fs)
    (tagcase (extract n form)
      (n-local l (product (var (sc-slot fs (extract l depth) (extract l index))) (path nil)))
      (n-call x
        (let* ((args (extract x args))
               (name (tagcase (extract (extract x op) form) (n-global g (s7-symbol-name (extract g name))) (else y "")))
               (label (cond ((string=? name "") "")
                            ((and (cf-member? name (list "car" "cdr")) (not (cf-global-defined? name))) name)
                            ((cf-global-defined? name) (sc-record-field name #f))
                            (else ""))))
          (if (or (string=? label "") (not (pair? args)) (pair? (cdr args))) (product (var -1) (path nil))
              (let ((p (sc-subject (car args) fs)))
                (if (< (extract p var) 0) p (product (var (extract p var)) (path (append (extract p path) (list label)))))))))
      (else y (product (var -1) (path nil))))))

"The field of the record's accessor (modifier) `op` names, if it does."
(define* sc-op-record-field (subr cf-eff (s7-node bool) string)
  (lambda (op modifier)
    (tagcase (extract op form)
      (n-global g (let ((n (s7-symbol-name (extract g name)))) (if (cf-global-defined? n) (sc-record-field n modifier) "")))
      (else y ""))))

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
                           (if (< v 0) (sc-core (extract x value) fs)
                               (begin (set cf-assigned (cons v (get cf-assigned))) (k-bind v (sc-core (extract x value) fs))))))
          (n-set-global x (k-bind (cf-global-var (s7-symbol-name (extract (extract x cell) name))) (sc-core (extract x value) fs)))
          (n-define x (let ((name (s7-symbol-name (extract (extract x cell) name))))
                        (begin (if (null? fs) (set cf-definition name) #u)
                          (k-bind (cf-global-var name)
                                  (tagcase (sc-record-proc (extract x value) name)
                                    (made c c)
                                    (else y (sc-core (extract x value) fs)))))))
          (n-if x (let* ((told (sc-told-by (extract x test) fs))
                         (t (sc-core (extract x test) fs))
                         (a (sc-core (extract x then) fs))
                         (b (sc-core (extract x else) fs)))
                    (k-if t (sc-with-aliases (extract told yes)) a (sc-with-aliases (extract told no)) b)))
          (n-lambda ls (let ((cs (sc-lambdas ls fs))) (if (and (pair? cs) (null? (cdr cs))) (car cs) (k-alt cs))))
          (n-seq ns (k-seq (sc-seq ns fs)))
          (n-call x (sc-call n (extract x op) (extract x args) fs))
          (n-scope x (sc-core (extract x body) (cons (sc-new-frame (extract x size)) fs)))
          (n-fail m (k-none nil))))))
  ;; What test `t` tells each branch (yank's occurrence typing): of a local
  ;; variable, or a field of one (`sc-subject`), its truth; a predicate of
  ;; one -- built-in, a record's, or the program's own, read as a formula --
  ;; or its comparison with a constant; `not` of a test the other way round;
  ;; `and` (`(if a b #f)`) both in its `then`; `or` (`(let ((t a)) (if t t
  ;; b))`) both in its `else`.
  (sc-told-by (subr sc-eff (s7-node sc-frames) sc-told)
    (lambda (t fs)
      (let* ((subj (sc-subject t fs))
             (both (lambda ((p cf-path) (cs strings) (full bool))
                     (the sc-told
                          (product (yes (the (listof cf-narrowing acyclic) (list (product (var (extract p var)) (path (extract p path)) (classes cs) (keep #t)))))
                                   (no (the (listof cf-narrowing acyclic)
                                            (if full (list (product (var (extract p var)) (path (extract p path)) (classes cs) (keep #f))) nil))))))))
        (if (>= (extract subj var) 0)
            (product (yes (list (product (var (extract subj var)) (path (extract subj path)) (classes (list "#f")) (keep #f))))
                     (no (list (product (var (extract subj var)) (path (extract subj path)) (classes (list "#f" "boolean")) (keep #t)))))
            (tagcase (extract t form)
              ;; `and`.
              (n-if x (if (tagcase (sc-const-of (extract x else)) (const v (tagcase v (bool b (not b)) (else y #f))) (else y #f))
                          (the sc-told (product (yes (append (extract (sc-told-by (extract x test) fs) yes) (extract (sc-told-by (extract x then) fs) yes)))
                                                (no (the (listof cf-narrowing acyclic) nil))))
                          sc-nothing-told))
              (n-call x
                (let* ((args (extract x args))
                       (name0 (tagcase (extract (extract x op) form) (n-global g (s7-symbol-name (extract g name))) (else y "")))
                       ;; Built-ins the expander calls are named with a space first (`case`'s ` memv`).
                       (name (if (and (> (string-length name0) 1) (char=? (string-ref name0 0) #\space)) (substring name0 1 (string-length name0)) name0))
                       (builtin (and (not (string=? name0 "")) (not (cf-global-defined? name0)))))
                  (cond
                    ;; `or`: a lambda of one parameter, called on `a`, whose body is (if t t b).
                    ((tagcase (extract (extract x op) form) (n-lambda ls (sc-or-shape? ls args)) (else y #f))
                     (tagcase (extract (extract x op) form)
                       (n-lambda ls (let ((l (car ls)))
                                      (tagcase (extract (sc-last-form (extract l body)) form)
                                        (n-if i (product (yes (the (listof cf-narrowing acyclic) nil))
                                                         (no (append (extract (sc-told-by (car args) fs) no)
                                                                     (extract (sc-told-by (extract i else) (cons (sc-blank-frame (extract l size)) fs)) no)))))
                                        (else y sc-nothing-told))))
                       (else y sc-nothing-told)))
                    ((and (pair? args) (null? (cdr args)))
                     (let ((s1 (sc-subject (car args) fs)))
                       (cond
                         ((and builtin (string=? name "not"))
                          (let ((inner (sc-told-by (car args) fs))) (product (yes (extract inner no)) (no (extract inner yes)))))
                         ((< (extract s1 var) 0) sc-nothing-told)
                         ((not (string=? (sc-record-pred name) "")) (both s1 (the strings (list (string-append "record:" (sc-record-pred name)))) #t))
                         ((and (not builtin) (pair? (sc-user-pred name)) (null? (extract s1 path)))
                          (let ((l (car (sc-user-pred name))))
                            (sc-told-by (sc-last-form (extract l body))
                                        (cons (let ((f (sc-blank-frame (max 1 (extract l size))))) (begin (array-set! f 0 (extract s1 var)) f)) fs))))
                         ((not builtin) sc-nothing-told)
                         (else (tagcase (sc-predicate name)
                                 (pred p (both s1 (extract p classes) (extract p full)))
                                 (else y sc-nothing-told))))))
                    ;; A comparison with a constant, or membership in a constant list.
                    ((and builtin (pair? args) (pair? (cdr args)) (null? (cdr (cdr args))))
                     (let* ((a (car args)) (b (car (cdr args)))
                            (sa (sc-subject a fs)) (sb (sc-subject b fs)))
                       (cond
                         ((cf-member? name (list "eq?" "eqv?" "equal?"))
                          (let ((pick (lambda ((s cf-path) (k s7-node))
                                        (tagcase (sc-const-of k)
                                          (const v (both s (the strings (list (sc-const-class v))) (sc-exact-const? v)))
                                          (else y sc-nothing-told)))))
                            (cond ((>= (extract sa var) 0) (pick sa b)) ((>= (extract sb var) 0) (pick sb a)) (else sc-nothing-told))))
                         ((and (cf-member? name (list "memq" "memv" "member")) (>= (extract sa var) 0))
                          (tagcase (sc-const-of b)
                            (const v (let ((vs (s7-value->values v)))
                                       (both sa (map-strings vs) (sc-all-exact? vs))))
                            (else y sc-nothing-told)))
                         (else sc-nothing-told))))
                    (else sc-nothing-told))))
              (else y sc-nothing-told))))))
  ;; A body's forms: after an `if` one of whose branches cannot return, the
  ;; rest evaluated knowing what the test told the other.
  (sc-seq (subr sc-eff (s7-nodes sc-frames) cores)
    (lambda (ns fs)
      (if (null? ns) nil
          (let ((c (sc-core (car ns) fs)))
            (tagcase (extract (car ns) form)
              (n-if x (let ((told (cond ((null? (cdr ns)) sc-nothing-told)
                                        ((sc-noreturn? (extract x then)) (the sc-told (product (yes (extract (sc-told-by (extract x test) fs) no)) (no (the (listof cf-narrowing acyclic) nil)))))
                                        ((sc-noreturn? (extract x else)) (sc-told-by (extract x test) fs))
                                        (else sc-nothing-told))))
                        (if (null? (extract told yes)) (cons c (sc-seq (cdr ns) fs))
                            (list c (k-narrow (sc-with-aliases (extract told yes)) (k-seq (sc-seq (cdr ns) fs)))))))
              (else y (cons c (sc-seq (cdr ns) fs))))))))
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
                 (aliased (let ((pending (get sc-pending-args)))
                            (begin (set sc-pending-args nil)
                              (letrec ((go (subr cf-eff ((listof cf-path acyclic) int) unit)
                                             (lambda (ps i) (if (or (null? ps) (>= i (extract l required))) #u
                                                                (begin (if (>= (extract (car ps) var) 0)
                                                                           (set sc-aliases (cons (product (var (array-ref frame i)) (source (car ps))) (get sc-aliases)))
                                                                           #u)
                                                                  (go (cdr ps) (+ i 1)))))))
                                (go pending 0)))))
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
          ((and (string=? prim "set-car!") (= nargs 2))
           (begin (set cf-stored (cons "car" (get cf-stored))) (k-seq (list (k-store (car as) "car" (car (cdr as))) (k-const (cf-kind "unspecified"))))))
          ((and (string=? prim "set-cdr!") (= nargs 2))
           (begin (set cf-stored (cons "cdr" (get cf-stored))) (k-seq (list (k-store (car as) "cdr" (car (cdr as))) (k-const (cf-kind "unspecified"))))))
          ;; A list of its elements: one pair site, its cdr itself or ().
          ((string=? prim "list")
           (let ((s (site "pair")))
             (if (null? as) (k-const (cf-kind "()"))
                 (k-alloc s (list (product (label "car") (value (k-alt as)))
                                  (product (label "cdr") (value (k-alt (list (k-const (cf-kind "()")) (k-alloc s nil))))))))))
          ;; A vector's elements: field `elt`.
          ((string=? prim "vector") (k-alloc (site "vector") (list (product (label "elt") (value (k-alt as))))))
          ((and (string=? prim "make-vector") (>= nargs 1))
           (k-seq (list (car as) (k-alloc (site "vector") (list (product (label "elt") (value (k-alt (cdr as)))))))))
          ((and (string=? prim "vector-ref") (= nargs 2)) (k-seq (list (car (cdr as)) (k-field (car as) "elt"))))
          ((and (string=? prim "vector-set!") (= nargs 3))
           (k-seq (list (car (cdr as)) (k-store (car as) "elt" (car (cdr (cdr as)))) (k-const (cf-kind "unspecified")))))
          ;; A record's accessor or modifier: its field, read or written.
          ((and (string=? prim "") (= nargs 1) (not (string=? (sc-op-record-field op #f) "")))
           (k-field (car as) (sc-op-record-field op #f)))
          ((and (string=? prim "") (= nargs 2) (not (string=? (sc-op-record-field op #t) "")))
           (k-seq (list (k-store (car as) (sc-op-record-field op #t) (car (cdr as))) (k-const (cf-kind "unspecified")))))
          (else
           ;; A `let` (a lambda applied where it is made): its variables bound to
           ;; others alias them.
           (let ((opc (begin (tagcase (extract op form)
                               (n-lambda ls (if (and (pair? ls) (null? (cdr ls)))
                                                (set sc-pending-args (letrec ((go (subr cf-eff (s7-nodes) (listof cf-path acyclic))
                                                                                    (lambda (l) (if (null? l) nil (cons (sc-subject (car l) fs) (go (cdr l)))))))
                                                                       (go args)))
                                                #u))
                               (else y #u))
                             (sc-core op fs))))
             (k-app (cf-add-call (product (span sp) (operator (sc-span (extract op span))))) opc as))))))))

"The names a world's top level defines, each a global."
(define* sc-declare! (subr sc-eff (s7-nodes) unit)
  (lambda (ns)
    (if (null? ns) #u
        (begin
          (tagcase (extract (car ns) form)
            (n-define x (let ((name (s7-symbol-name (extract (extract x cell) name))))
                          (begin
                            (cf-global-var name)
                            ;; A record's predicate, accessor or modifier; a procedure of one parameter.
                            (tagcase (extract (extract x value) form)
                              (n-call c (let ((op (tagcase (extract (extract c op) form) (n-global g (s7-symbol-name (extract g name))) (else y "")))
                                              (args (extract c args)))
                                          (cond
                                            ((and (string=? op " record-predicate") (pair? args))
                                             (tagcase (extract (car args) form)
                                               (n-global g (set sc-record-preds (cons (product (name name) (type (s7-symbol-name (extract g name))))
                                                                                      (get sc-record-preds))))
                                               (else y #u)))
                                            ((and (or (string=? op " record-accessor") (string=? op " record-modifier")) (pair? args) (pair? (cdr args)))
                                             (let ((field (sc-const-symbol (car (cdr args)))) (modifier (string=? op " record-modifier")))
                                               (begin
                                                 (set sc-record-fields (cons (product (name name) (field field) (modifier modifier)) (get sc-record-fields)))
                                                 (if modifier (set cf-stored (cons field (get cf-stored))) #u))))
                                            (else #u))))
                              (n-lambda ls (if (and (pair? ls) (null? (cdr ls)) (= (extract (car ls) required) 1) (not (extract (car ls) rest)))
                                               (set sc-user-preds (cons (product (name name) (lambda (car ls))) (get sc-user-preds)))
                                               #u))
                              (else y #u))
                            #u)))
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
        (set sc-record-preds nil) (set sc-record-fields nil) (set sc-user-preds nil) (set sc-aliases nil) (set sc-pending-args nil)
        (letrec ((go (subr sc-eff (strings) unit) (lambda (ps) (if (null? ps) #u (begin (cf-file (car ps)) (go (cdr ps)))))))
          (go paths))
        (letrec ((go (subr sc-eff ((listof s7-nodes acyclic)) unit) (lambda (l) (if (null? l) #u (begin (sc-declare! (car l)) (go (cdr l)))))))
          (go nodes))
        (cf-globals-declared!)
        (let ((tops (letrec ((go (subr sc-eff ((listof s7-nodes acyclic)) cores)
                               (lambda (l) (if (null? l) nil (let ((c (k-seq (sc-all (car l) nil)))) (cons c (go (cdr l))))))))
                      (go nodes))))
          (begin (s7-rename-release! mark) tops))))))
