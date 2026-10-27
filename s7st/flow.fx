;;; flow.fx: what can reach each variable, and what each call can call -- a
;;; flow analysis of a Scheme text, at 0CFA, as yank's `(yank analysis cfa)`
;;; is in its simplest form, and as editor/flow.fx is for FX-26.
;;;
;;; The text is expanded by s7st's own expander (expand.fx) -- so its
;;; macros are expanded as they would be when it runs -- into a namespace
;;; of its own, so that nothing it defines is defined in the session; and
;;; it is not run. Then the abstract values that can reach each variable
;;; and each lambda's result are found by evaluating every lambda's body,
;;; and the top level, against a store that only grows, until it stops
;;; growing.
;;;
;;; An abstract value is a kind of data (a number, a string, a pair, …), a
;;; lambda of the text (its clause), or a procedure the session has (a
;;; built-in, by name). A lambda given to a built-in escapes: it may be
;;; called with anything. Not yet: allocation sites (what a pair holds),
;;; contexts (1CFA), narrowing by the tests a variable is under.

;;; ------------------------------------------------------------ abstract values

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
"A lambda clause of the text, `i`th: value 1000 + i; a built-in, `i`th
seen: 1000000 + i."
(define s7-fv-lambda0 int 1000)
(define s7-fv-builtin0 int 1000000)
(define-type s7-fset (listof int acyclic))

(define* s7-fset-has? (subr spin (int s7-fset) bool)
  (lambda (x s) (and (pair? s) (or (= (car s) x) (s7-fset-has? x (cdr s))))))
"Value `x` added to set `s`, if it is not in it."
(define* s7-fset-add (subr spin (int s7-fset) s7-fset)
  (lambda (x s) (if (s7-fset-has? x s) s (cons x s))))
(define* s7-fset-union (subr spin (s7-fset s7-fset) s7-fset)
  (lambda (a b) (if (null? a) b (s7-fset-union (cdr a) (s7-fset-add (car a) b)))))
"Whether `a` holds everything `b` does."
(define* s7-fset-covers? (subr spin (s7-fset s7-fset) bool)
  (lambda (a b) (or (null? b) (and (s7-fset-has? (car b) a) (s7-fset-covers? a (cdr b))))))

"The kind of a value the session has."
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

;;; ------------------------------------------------------------ the analysis

"A lambda clause of the text: itself, and the frames around it (their
numbers, innermost first)."
(define-type s7-flam (productof (lambda s7-lambda) (outer (listof int acyclic))))
"What the analysis finds of a text: notes, each a span and what is said
there (what reaches a variable; what a call can call)."
(define-type s7-fnote (productof (start int) (end int) (text string)))

"The analysis's state, while it runs."
(define-type s7-fstate
  (productof (lambdas (arrayof s7-flam @sc))                     ; by index
             (rets (arrayof s7-fset @sc))                       ; each lambda's results
             (escaped (arrayof bool @sc))                       ; each lambda's, given to code not known
             (slots (arrayof s7-fset @sc))                      ; frame slots: a frame's base + index
             (bases (arrayof int @sc))                          ; frame number - first, to its base
             (lindex (arrayof int @sc))                         ; lambda number - first, to its index
             (first int)                                        ; the first node number of the text's
             (globals (ref (listof (productof (name symbol) (values s7-fset)) acyclic) @sc))
             (builtins (ref s7-strings @sc))                    ; the built-ins seen, last first
             (calls (ref (listof (productof (start int) (end int) (callees s7-fset)) acyclic) @sc))
             (changed (ref bool @sc))))

(define* s7-fl-slot (subr (maxeff spin (read @sc)) (s7-fstate (listof int acyclic) int int) int)
  ;; The slot of frame `depth` out in `frames`, at `index`; -1 if none.
  (lambda (st frames depth index)
    (letrec ((nth (subr spin ((listof int acyclic) int) int)
               (lambda (l d) (cond ((null? l) -1) ((= d 0) (car l)) (else (nth (cdr l) (- d 1)))))))
      (let ((f (nth frames depth)))
        (if (< f 0) -1
            (let ((i (- f (extract st first))))
              (if (or (< i 0) (>= i (array-length (extract st bases)))) -1
                  (let ((b (array-ref (extract st bases) i)))
                    (if (< b 0) -1 (+ b index))))))))))
"Values `vs` flowed into slot `k`: whether that added any."
(define* s7-fl-flow-slot! (subr s7-eff (s7-fstate int s7-fset) unit)
  (lambda (st k vs)
    (if (or (< k 0) (>= k (array-length (extract st slots)))) #u
        (let ((old (array-ref (extract st slots) k)))
          (if (s7-fset-covers? old vs) #u
              (begin (array-set! (extract st slots) k (s7-fset-union vs old)) (set (extract st changed) #t)))))))
(define* s7-fl-global (subr s7-eff (s7-fstate symbol) (sumof (none unit) (some s7-fset)))
  (lambda (st name)
    (letrec ((go (subr spin ((listof (productof (name symbol) (values s7-fset)) acyclic)) (sumof (none unit) (some s7-fset)))
               (lambda (l) (cond ((null? l) (sum none #u)) ((eq? (extract (car l) name) name) (sum some (extract (car l) values))) (else (go (cdr l)))))))
      (go (get (extract st globals))))))
(define* s7-fl-flow-global! (subr s7-eff (s7-fstate symbol s7-fset) unit)
  (lambda (st name vs)
    (let ((old (tagcase (s7-fl-global st name) (some s s) (none u nil))))
      (if (and (pair? old) (s7-fset-covers? old vs)) #u
          (letrec ((drop (subr spin ((listof (productof (name symbol) (values s7-fset)) acyclic)) (listof (productof (name symbol) (values s7-fset)) acyclic))
                     (lambda (l) (cond ((null? l) nil) ((eq? (extract (car l) name) name) (cdr l)) (else (cons (car l) (drop (cdr l))))))))
            (begin (set (extract st globals) (cons (product (name name) (values (s7-fset-union vs old))) (drop (get (extract st globals)))))
              (set (extract st changed) #t)))))))
"The abstract value of a built-in named `n`."
(define* s7-fl-builtin (subr s7-eff (s7-fstate string) int)
  (lambda (st n)
    (letrec ((index (subr spin (s7-strings int) int)
               (lambda (l i) (cond ((null? l) -1) ((string=? (car l) n) i) (else (index (cdr l) (- i 1)))))))
      (let* ((l (get (extract st builtins))) (i (index l (- (list-length l) 1))))
        (if (>= i 0) (+ s7-fv-builtin0 i)
            (begin (set (extract st builtins) (cons n l)) (+ s7-fv-builtin0 (list-length l))))))))
(define* s7-fl-builtin-name (subr s7-eff (s7-fstate int) string)
  (lambda (st v)
    (let* ((l (get (extract st builtins))) (k (- (- (list-length l) 1) (- v s7-fv-builtin0))))
      (letrec ((nth (subr spin (s7-strings int) string) (lambda (l k) (cond ((null? l) "?") ((= k 0) (car l)) (else (nth (cdr l) (- k 1)))))))
        (nth l k)))))

"The index of the lambda numbered `id`, or -1."
(define* s7-fl-lambda-index (subr (maxeff spin (read @sc)) (s7-fstate int) int)
  (lambda (st id)
    (let ((i (- id (extract st first))))
      (if (or (< i 0) (>= i (array-length (extract st lindex)))) -1 (array-ref (extract st lindex) i)))))
"Each of `vs` that is a lambda: escaped (called by code not known)."
(define* s7-fl-escape! (subr s7-eff (s7-fstate s7-fset) unit)
  (lambda (st vs)
    (if (null? vs) #u
        (let ((j (- (car vs) s7-fv-lambda0)))
          (begin
            (if (and (>= j 0) (< j (array-length (extract st lambdas))) (not (array-ref (extract st escaped) j)))
                (begin (array-set! (extract st escaped) j #t) (set (extract st changed) #t))
                #u)
            (s7-fl-escape! st (cdr vs)))))))

"A global's abstract value: what the text defines it to be, else what the
session has."
(define* s7-fl-global-value (subr s7-eff (s7-fstate s7-global) s7-fset)
  (lambda (st c)
    (tagcase (s7-fl-global st (extract c name))
      (some vs vs)
      (none u (tagcase (get (extract c value))
                (prim p (list (s7-fl-builtin st (extract p name))))
                (proc p (list (s7-fl-builtin st (s7-symbol-name (extract c name)))))
                (undef u (list s7-fv-unknown))
                (else v (list (s7-fv-kind v))))))))

(define-rec
  ;; Node `n`'s abstract value, evaluated in the frames `frames`.
  (s7-fl-eval (->* (s7-fstate s7-node (listof int acyclic)) s7-fset)
    (lambda (st n frames)
      (tagcase (extract n form)
        (n-const v (list (s7-fv-kind v)))
        (n-local l (let ((k (s7-fl-slot st frames (extract l depth) (extract l index))))
                     (if (< k 0) (list s7-fv-unknown) (array-ref (extract st slots) k))))
        (n-global c (s7-fl-global-value st c))
        (n-set-local x (let ((vs (s7-fl-eval st (extract x value) frames)))
                         (begin (s7-fl-flow-slot! st (s7-fl-slot st frames (extract x depth) (extract x index)) vs)
                           (list s7-fv-unspec))))
        (n-set-global x (let ((vs (s7-fl-eval st (extract x value) frames)))
                          (begin (s7-fl-flow-global! st (extract (extract x cell) name) vs) (list s7-fv-unspec))))
        (n-define x (let ((vs (s7-fl-eval st (extract x value) frames)))
                      (begin (s7-fl-flow-global! st (extract (extract x cell) name) vs) (list s7-fv-symbol))))
        (n-if x (begin (s7-fl-eval st (extract x test) frames)
                  (s7-fset-union (s7-fl-eval st (extract x then) frames) (s7-fl-eval st (extract x else) frames))))
        (n-lambda ls (letrec ((go (->* ((listof s7-lambda acyclic)) s7-fset)
                                (lambda (ls) (if (null? ls) nil
                                                 (let ((j (s7-fl-lambda-index st (extract (car ls) id))))
                                                   (if (< j 0) (go (cdr ls)) (s7-fset-add (+ s7-fv-lambda0 j) (go (cdr ls)))))))))
                       (go ls)))
        (n-seq ns (letrec ((go (->* (s7-nodes) s7-fset)
                             (lambda (ns) (if (null? (cdr ns)) (s7-fl-eval st (car ns) frames)
                                              (begin (s7-fl-eval st (car ns) frames) (go (cdr ns)))))))
                    (go ns)))
        (n-call x (let* ((ops (s7-fl-eval st (extract x op) frames))
                         (args (s7-fl-eval-all st (extract x args) frames))
                         (sp (extract (extract x op) span)))
                    (begin
                      (if (< (extract sp start) 0) #u
                          (set (extract st calls) (cons (product (start (extract sp start)) (end (extract sp end)) (callees ops))
                                                        (get (extract st calls)))))
                      (s7-fl-apply st ops args))))
        (n-scope x (s7-fl-eval st (extract x body) (cons (extract n id) frames)))
        (n-fail m (list s7-fv-unknown)))))
  (s7-fl-eval-all (->* (s7-fstate s7-nodes (listof int acyclic)) (listof s7-fset acyclic))
    (lambda (st ns frames)
      (if (null? ns) nil (cons (s7-fl-eval st (car ns) frames) (s7-fl-eval-all st (cdr ns) frames)))))
  ;; Each of `ops` applied to arguments `args`: what they can give.
  (s7-fl-apply (->* (s7-fstate s7-fset (listof s7-fset acyclic)) s7-fset)
    (lambda (st ops args)
      (if (null? ops) nil
          (let* ((op (car ops))
                 (here (the s7-fset (cond
                         ((and (>= op s7-fv-lambda0) (< op s7-fv-builtin0))
                          (let* ((j (- op s7-fv-lambda0))
                                 (fl (array-ref (extract st lambdas) j))
                                 (l (extract fl lambda))
                                 (n (list-length args)))
                            (if (or (= n (extract l required)) (and (extract l rest) (> n (extract l required))))
                                (begin (s7-fl-params! st j args) (array-ref (extract st rets) j))
                                nil)))
                         ((>= op s7-fv-builtin0)
                          ;; A lambda given to a built-in may be called by it, with anything.
                          (letrec ((esc (->* ((listof s7-fset acyclic)) unit)
                                     (lambda (l) (if (null? l) #u (begin (s7-fl-escape! st (car l)) (esc (cdr l)))))))
                            (begin (esc args) (s7-builtin-result (s7-fl-builtin-name st op)))))
                         ((= op s7-fv-unknown)
                          (letrec ((esc (->* ((listof s7-fset acyclic)) unit)
                                     (lambda (l) (if (null? l) #u (begin (s7-fl-escape! st (car l)) (esc (cdr l)))))))
                            (begin (esc args) (list s7-fv-unknown))))
                         (else nil)))))
            (s7-fset-union here (s7-fl-apply st (cdr ops) args))))))
  ;; Arguments `args` flowed into lambda `j`'s parameters.
  (s7-fl-params! (->* (s7-fstate int (listof s7-fset acyclic)) unit)
    (lambda (st j args)
      (let* ((l (extract (array-ref (extract st lambdas) j) lambda))
             (base (s7-fl-slot st (list (extract l id)) 0 0)))
        (letrec ((go (->* ((listof s7-fset acyclic) int) unit)
                   (lambda (as i)
                     (cond ((< i (extract l required))
                            (if (null? as) #u (begin (s7-fl-flow-slot! st (+ base i) (car as)) (go (cdr as) (+ i 1)))))
                           ((extract l rest) (s7-fl-flow-slot! st (+ base i) (list s7-fv-pair s7-fv-null)))
                           (else #u)))))
          (if (< base 0) #u (go args 0)))))))

"Every lambda of `nodes`, with the frames around it; and every frame
(lambda or scope) with its size, by number: to number the slots."
(define-type s7-fframe (productof (id int) (size int)))
(define* s7-fl-collect (subr s7-eff (s7-nodes) (productof (lambdas (listof s7-flam acyclic)) (frames (listof s7-fframe acyclic))))
  (lambda (nodes)
    (let ((lams (the (ref (listof s7-flam acyclic) @sc) (new nil)))
          (frs (the (ref (listof s7-fframe acyclic) @sc) (new nil))))
      (letrec ((walk (subr s7-eff (s7-node (listof int acyclic)) unit)
                 (lambda (n outer)
                   (tagcase (extract n form)
                     (n-set-local x (walk (extract x value) outer))
                     (n-set-global x (walk (extract x value) outer))
                     (n-define x (walk (extract x value) outer))
                     (n-if x (begin (walk (extract x test) outer) (walk (extract x then) outer) (walk (extract x else) outer)))
                     (n-lambda ls (each-lambda ls outer))
                     (n-seq ns (all ns outer))
                     (n-call x (begin (walk (extract x op) outer) (all (extract x args) outer)))
                     (n-scope x (begin (set frs (cons (product (id (extract n id)) (size (extract x size))) (get frs)))
                                  (walk (extract x body) (cons (extract n id) outer))))
                     (else y #u))))
               (all (subr s7-eff (s7-nodes (listof int acyclic)) unit)
                 (lambda (ns outer) (if (null? ns) #u (begin (walk (car ns) outer) (all (cdr ns) outer)))))
               (each-lambda (subr s7-eff ((listof s7-lambda acyclic) (listof int acyclic)) unit)
                 (lambda (ls outer)
                   (if (null? ls) #u
                       (let ((l (car ls)))
                         (begin
                           (set lams (cons (product (lambda l) (outer outer)) (get lams)))
                           (set frs (cons (product (id (extract l id)) (size (extract l size))) (get frs)))
                           (walk (extract l body) (cons (extract l id) outer))
                           (each-lambda (cdr ls) outer)))))))
        (begin (all nodes nil)
          (product (lambdas (reverse (get lams))) (frames (reverse (get frs)))))))))

"Abstract values `vs`, said: kinds by name, lambdas by theirs."
(define* s7-fl-describe (subr s7-eff (s7-fstate s7-fset) string)
  (lambda (st vs)
    (letrec ((one (subr s7-eff (int) string)
               (lambda (v)
                 (cond ((< v s7-fv-lambda0)
                        (letrec ((nth (subr spin (s7-strings int) string) (lambda (l k) (cond ((null? l) "?") ((= k 0) (car l)) (else (nth (cdr l) (- k 1)))))))
                          (nth s7-fv-kinds v)))
                       ((< v s7-fv-builtin0)
                        (let ((l (extract (array-ref (extract st lambdas) (- v s7-fv-lambda0)) lambda)))
                          (string-append "#<procedure " (if (string=? (extract l name) "") "λ" (extract l name)) ">")))
                       (else (string-append "#<procedure " (s7-fl-builtin-name st v) ">")))))
             (go (subr s7-eff (s7-fset (listof string acyclic)) (listof string acyclic))
               (lambda (vs acc) (if (null? vs) acc (go (cdr vs) (cons (one (car vs)) (if (null? acc) acc (cons " | " acc))))))))
      (s7-concat (go (reverse vs) nil)))))

"The notes: at each use of a variable, what can reach it; at each call's
operator, what it can call (if not just one built-in)."
(define* s7-fl-notes (subr s7-eff (s7-fstate s7-nodes string) (listof s7-fnote acyclic))
  ;; `source`: the text, so that only a span that is a name is noted.
  (lambda (st nodes source)
    (let ((acc (the (ref (listof s7-fnote acyclic) @sc) (new nil)))
          (name? (lambda ((a int) (e int)) (and (>= a 0) (< a e) (<= e (string-length source)) (not (char-in? (string-ref source a) "()[]'`,\""))))))
      (letrec ((note (subr s7-eff (s7-span string) unit)
                 (lambda (sp text)
                   (if (or (not (name? (extract sp start) (extract sp end))) (string=? text "")) #u
                       (set acc (cons (product (start (extract sp start)) (end (extract sp end)) (text text)) (get acc))))))
               (walk (subr s7-eff (s7-node (listof int acyclic)) unit)
                 (lambda (n frames)
                   (tagcase (extract n form)
                     (n-local l (let ((k (s7-fl-slot st frames (extract l depth) (extract l index))))
                                  (if (< k 0) #u
                                      (note (extract n span) (string-append (s7-symbol-name (extract l name)) ": "
                                                                            (s7-fl-describe st (array-ref (extract st slots) k)))))))
                     (n-set-local x (walk (extract x value) frames))
                     (n-set-global x (walk (extract x value) frames))
                     (n-define x (walk (extract x value) frames))
                     (n-if x (begin (walk (extract x test) frames) (walk (extract x then) frames) (walk (extract x else) frames)))
                     (n-lambda ls (letrec ((each (subr s7-eff ((listof s7-lambda acyclic)) unit)
                                                   (lambda (ls) (if (null? ls) #u
                                                                    (begin (walk (extract (car ls) body) (cons (extract (car ls) id) frames))
                                                                      (each (cdr ls)))))))
                                    (each ls)))
                     (n-seq ns (all ns frames))
                     (n-call x (begin (walk (extract x op) frames) (all (extract x args) frames)))
                     (n-scope x (walk (extract x body) (cons (extract n id) frames)))
                     (else y #u))))
               (all (subr s7-eff (s7-nodes (listof int acyclic)) unit)
                 (lambda (ns frames) (if (null? ns) #u (begin (walk (car ns) frames) (all (cdr ns) frames))))))
        (begin
          (all nodes nil)
          ;; Calls: what the operator can call, where it is more than a built-in's name says.
          (letrec ((calls (subr s7-eff ((listof (productof (start int) (end int) (callees s7-fset)) acyclic)) unit)
                     (lambda (l)
                       (if (null? l) #u
                           (let ((cs (extract (car l) callees)))
                             (begin
                               (if (and (pair? cs) (or (pair? (cdr cs)) (< (car cs) s7-fv-builtin0))
                                        (name? (extract (car l) start) (extract (car l) end)))
                                   (set acc (cons (product (start (extract (car l) start)) (end (extract (car l) end))
                                                           (text (string-append "calls " (s7-fl-describe st cs))))
                                                  (get acc)))
                                   #u)
                               (calls (cdr l))))))))
            (calls (get (extract st calls))))
          (get acc))))))

"The data of `text`, as far as they read: those before an error."
(define* s7-read-lenient (subr s7-eff (string string) s7-values)
  (lambda (text file)
    (letrec ((go (subr s7-eff (int s7-values) s7-values)
               (lambda (i acc)
                 (tagcase (s7-read-at text i file)
                   (datum d (go (extract d end) (cons (extract d value) acc)))
                   (else y (reverse acc))))))
      (go 0 nil))))
"Text `text` (of `file`) analysed for flow: notes at each variable's use
(what can reach it) and each call's operator (what it can call)."
(define* s7-flow (subr s7-eff (string string) (listof s7-fnote acyclic))
  (lambda (text file)
    (let* ((ns (s7-make-ns "flow" 256 (list s7-builtins)))
           (saved (get s7-current-ns))
           (first (get s7-next-id))
           (forms (s7-read-lenient text file)))
      (begin
        (set s7-current-ns ns)
        (let* ((nodes (letrec ((go (subr s7-eff (s7-values) s7-nodes)
                                 (lambda (fs)
                                   (if (null? fs) nil
                                       (let ((f (car fs)))
                                         (cond ((s7-sym-named? (s7-car f) "import") (go (cdr fs)))
                                               ((s7-sym-named? (s7-car f) "define-library")
                                                (append (go (s7-library-body (s7-library-decls (s7-value->values (s7-cddr f))))) (go (cdr fs))))
                                               (else (begin (set s7-syntax-errors nil) (cons (s7-expand-top f) (go (cdr fs)))))))))))
                         (go forms)))
               (last (get s7-next-id))
               (found (s7-fl-collect nodes))
               (lams (the (arrayof s7-flam @sc) (list->array (extract found lambdas))))
               (n (array-length lams))
               (bases (the (arrayof int @sc) (make-array (max 1 (- last first)) -1)))
               (lindex (let ((a (the (arrayof int @sc) (make-array (max 1 (- last first)) -1))))
                         (letrec ((go (subr s7-eff (int) (arrayof int @sc))
                                    (lambda (j) (if (>= j n) a
                                                    (let ((i (- (extract (extract (array-ref lams j) lambda) id) first)))
                                                      (begin (if (and (>= i 0) (< i (array-length a))) (array-set! a i j) #u) (go (+ j 1))))))))
                           (go 0))))
               (total (letrec ((go (subr s7-eff ((listof s7-fframe acyclic) int) int)
                                 (lambda (l at)
                                   (if (null? l) at
                                       (let ((i (- (extract (car l) id) first)))
                                         (begin (if (and (>= i 0) (< i (array-length bases))) (array-set! bases i at) #u)
                                           (go (cdr l) (+ at (extract (car l) size)))))))))
                        (go (extract found frames) 0)))
               (st (product (lambdas lams)
                            (rets (the (arrayof s7-fset @sc) (make-array (max 1 n) (the s7-fset nil))))
                            (escaped (the (arrayof bool @sc) (make-array (max 1 n) #f)))
                            (slots (the (arrayof s7-fset @sc) (make-array (max 1 total) (the s7-fset nil))))
                            (bases bases) (lindex lindex) (first first)
                            (globals (the (ref (listof (productof (name symbol) (values s7-fset)) acyclic) @sc) (new nil)))
                            (builtins (the (ref s7-strings @sc) (new nil)))
                            (calls (the (ref (listof (productof (start int) (end int) (callees s7-fset)) acyclic) @sc) (new nil)))
                            (changed (the (ref bool @sc) (new #t))))))
          (begin
            (set s7-current-ns saved)
            (letrec ((pass (subr s7-eff (int) unit)
                       ;; Passes over the top level and every lambda, until nothing grows.
                       (lambda (k)
                         (if (or (= k 0) (not (get (extract st changed)))) #u
                             (begin
                               (set (extract st changed) #f)
                               (set (extract st calls) nil)
                               (s7-fl-eval-all st nodes nil)
                               (letrec ((lam (subr s7-eff (int) unit)
                                          (lambda (j)
                                            (if (>= j n) #u
                                                (let* ((fl (array-ref lams j)) (l (extract fl lambda)))
                                                  (begin
                                                    (if (array-ref (extract st escaped) j)
                                                        ;; Called by code not known: its parameters may be anything.
                                                        (s7-fl-params! st j (letrec ((us (subr spin (int) (listof s7-fset acyclic))
                                                                                           (lambda (i) (if (<= i 0) nil (cons (list s7-fv-unknown) (us (- i 1)))))))
                                                                              (us (+ (extract l required) (if (extract l rest) 1 0)))))
                                                        #u)
                                                    (let ((r (s7-fl-eval st (extract l body) (cons (extract l id) (extract fl outer))))
                                                          (old (array-ref (extract st rets) j)))
                                                      (if (s7-fset-covers? old r) #u
                                                          (begin (array-set! (extract st rets) j (s7-fset-union r old)) (set (extract st changed) #t))))
                                                    (lam (+ j 1))))))))
                                 (lam 0))
                               (pass (- k 1)))))))
              (pass 40))
            (s7-fl-notes st nodes text)))))))

