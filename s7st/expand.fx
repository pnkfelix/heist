;;; expand.fx: data to core -- R7RS's syntax, expanded once, before it runs.
;;;
;;; Every variable is resolved here: a frame slot (by depth and index) or a
;;; global's cell. Every node is numbered and has a span, for an analysis
;;; to key its facts by. Derived forms (`cond`, `case`, `do`, `let*`, `and`,
;;; `or`, `define-record-type`, …) are rewritten as data, into forms with
;;; the names below that begin with a space (` if`, ` let`), which name the
;;; special forms and procedures themselves, so that no binding a program
;;; makes can capture them.
;;;
;;; `syntax-rules` renames each symbol a template brings in (`tmp` becomes
;;; `tmp 17`, its expansion's number), so that it binds nothing the macro's
;;; user wrote; free, a renamed symbol means what its name means where the
;;; macro is used. That is hygiene but for one case: a macro whose template
;;; names a variable the user's code has bound around the use sees the
;;; user's (docs/s7st.md, "What is not done").
;;;
;;; An error is not raised here: it is noted (`s7-syntax-errors`), and its
;;; form expanded to a node that raises it if run. The session looks at the
;;; notes before it runs a form.

(define-type s7-syntax-error (productof (message string) (span s7-span)))
(define s7-syntax-errors (ref (listof s7-syntax-error acyclic) @sc) (new nil))
(define s7-rename-count (ref int @sc) (new 0))
"For each expansion of a macro, by number, the namespace of the macro: where
a free symbol its template brought in means what its name means there."
(define s7-rename-nss (ref (arrayof (listof s7-ns acyclic) @sc) @sc)
  (new (the (arrayof (listof s7-ns acyclic) @sc) (make-array 1024 (the (listof s7-ns acyclic) nil)))))
"Expansion `n` noted as of a macro of namespace `ns`."
(define* s7-note-rename-ns! (subr s7-eff (int s7-ns) unit)
  (lambda (n ns)
    (let ((a (get s7-rename-nss)))
      (if (< n (array-length a)) (array-set! a n (list ns))
          (let ((b (the (arrayof (listof s7-ns acyclic) @sc) (make-array (* 2 (+ n 1)) (the (listof s7-ns acyclic) nil)))))
            (letrec ((copy (subr s7-eff (int) unit)
                       (lambda (i) (if (>= i (array-length a)) #u (begin (array-set! b i (array-ref a i)) (copy (+ i 1)))))))
              (begin (copy 0) (array-set! b n (list ns)) (set s7-rename-nss b))))))))
"The namespace renamed symbol `s` is of: its macro's, or the current one."
(define* s7-rename-ns (subr s7-eff (symbol) s7-ns)
  (lambda (s)
    (let* ((n (symbol->string s))
           (sp (letrec ((go (subr spin (int) int) (lambda (i) (cond ((< i 0) -1) ((char=? (string-ref n i) #\space) i) (else (go (- i 1)))))))
                 (go (- (string-length n) 1))))
           (k (if (< sp 0) -1 (s7-parse-digits (substring n (+ sp 1) (string-length n)) 10)))
           (a (get s7-rename-nss)))
      (if (and (>= k 0) (< k (array-length a)) (pair? (array-ref a k))) (car (array-ref a k)) (get s7-current-ns)))))

(define* s7-node-at (subr (maxeff (read @sc) (write @sc)) (s7-span s7-form) s7-node)
  (lambda (span form) (product (id (s7-fresh-id)) (span span) (form form))))
"A node that raises `message` when run; the error noted."
(define* s7-fail-node (subr (maxeff (read @sc) (write @sc) (alloc @sc)) (string s7-span) s7-node)
  (lambda (message span)
    (begin
      (set s7-syntax-errors (cons (product (message message) (span span)) (get s7-syntax-errors)))
      (s7-node-at span (sum n-fail message)))))
(define* s7-const-node (subr (maxeff (read @sc) (write @sc)) (s7-value s7-span) s7-node)
  (lambda (v span) (s7-node-at span (sum n-const v))))

;;; ------------------------------------------------------------ data

(define* s7-car (subr (read @sc) (s7-value) s7-value)
  (lambda (x) (tagcase x (pair p (get (extract p car))) (else y s7-undefined))))
(define* s7-cdr (subr (read @sc) (s7-value) s7-value)
  (lambda (x) (tagcase x (pair p (get (extract p cdr))) (else y s7-undefined))))
(define* s7-cadr (subr (read @sc) (s7-value) s7-value) (lambda (x) (s7-car (s7-cdr x))))
(define* s7-cddr (subr (read @sc) (s7-value) s7-value) (lambda (x) (s7-cdr (s7-cdr x))))
(define* s7-pair? (subr pure (s7-value) bool) (lambda (x) (tagcase x (pair p #t) (else y #f))))
(define* s7-null? (subr pure (s7-value) bool) (lambda (x) (tagcase x (null u #t) (else y #f))))
(define* s7-symbol? (subr pure (s7-value) bool) (lambda (x) (tagcase x (sym s #t) (else y #f))))
"Symbol `x`, or the symbol ` none` if `x` is no symbol."
(define* s7-sym (subr pure (s7-value) symbol)
  (lambda (x) (tagcase x (sym s s) (else y (string->symbol " none")))))
"Whether `x` is a symbol whose name, unrenamed, is `name`."
(define* s7-sym-named? (subr spin (s7-value string) bool)
  (lambda (x name) (tagcase x (sym s (string=? (s7-symbol-name s) name)) (else y #f))))
"The special form or procedure `name` itself, as a symbol no program binds."
(define* s7-kw (subr pure (string) s7-value)
  (lambda (name) (sum sym (string->symbol (string-append " " name)))))
(define* s7-l (subr (maxeff spin (alloc @sc)) (s7-values) s7-value) (lambda (l) (s7-list l)))
(define* s7-quoted (subr (maxeff spin (alloc @sc)) (s7-value) s7-value)
  (lambda (v) (s7-list (list (s7-kw "quote") v))))
"A symbol of name `name`, renamed afresh: it is bound by nothing written."
(define* s7-fresh-symbol (subr (maxeff (read @sc) (write @sc)) (string) s7-value)
  (lambda (name)
    (let ((n (get s7-rename-count)))
      (begin (set s7-rename-count (+ n 1))
        (sum sym (string->symbol (string-append name " " (int->string n))))))))
"The items of `x`, a list, or (none)."
(define* s7-items (subr (maxeff spin (read @sc)) (s7-value) (sumof (none unit) (some s7-values)))
  (lambda (x) (s7-list-items x)))
"Whether data `v` holds a renamed symbol."
(define* s7-has-renamed? (subr (maxeff spin (read @sc)) (s7-value) bool)
  (lambda (v)
    (tagcase v
      (sym s (s7-renamed? s))
      (pair p (or (s7-has-renamed? (get (extract p car))) (s7-has-renamed? (get (extract p cdr)))))
      (vec a (letrec ((go (subr (maxeff spin (read @sc)) (s7-values) bool)
                            (lambda (l) (and (pair? l) (or (s7-has-renamed? (car l)) (go (cdr l)))))))
               (go (array->list a))))
      (else y #f))))
"Data `v` with every renamed symbol unrenamed (copied only if it has one):
what a quote in a template means."
(define-rec
  (s7-strip (->* (s7-value) s7-value)
    (lambda (v)
      (if (not (s7-has-renamed? v)) v
          (tagcase v
            (sym s (sum sym (string->symbol (s7-symbol-name s))))
            (pair p (s7-cons (s7-strip (get (extract p car))) (s7-strip (get (extract p cdr)))))
            (vec a (sum vec (list->array (s7-strip-all (array->list a)))))
            (else y y)))))
  (s7-strip-all (->* (s7-values) s7-values)
    (lambda (l) (if (null? l) nil (cons (s7-strip (car l)) (s7-strip-all (cdr l)))))))

;;; ------------------------------------------------------------ scopes

(define* s7-new-scope (subr (alloc @sc) (s7-symbols) s7-scope)
  (lambda (names)
    (product (names (the (ref s7-symbols @sc) (new (reverse names))))
             (count (the (ref int @sc) (new (list-length names))))
             (macros (the (ref (listof (productof (name symbol) (macro s7-macro)) acyclic) @sc) (new nil))))))
"Name `name` added to scope `sc`: its index."
(define* s7-scope-add! (subr (maxeff (read @sc) (write @sc)) (s7-scope symbol) int)
  (lambda (sc name)
    (let ((n (get (extract sc count))))
      (begin (set (extract sc names) (cons name (get (extract sc names))))
        (set (extract sc count) (+ n 1))
        n))))
"The index of `name` in scope `sc`, or -1: the last added, if twice."
(define* s7-scope-index (subr (maxeff spin (read @sc)) (s7-scope symbol) int)
  (lambda (sc name)
    (letrec ((go (subr spin (s7-symbols int) int)
               (lambda (l i) (cond ((null? l) -1) ((eq? (car l) name) i) (else (go (cdr l) (- i 1)))))))
      (go (get (extract sc names)) (- (get (extract sc count)) 1)))))
(define* s7-scope-names (subr (read @sc) (s7-scope) s7-symbols)
  (lambda (sc) (reverse (get (extract sc names)))))
(define* s7-scope-macro (subr (maxeff spin (read @sc)) (s7-scope symbol) (sumof (none unit) (some s7-macro)))
  (lambda (sc name)
    (letrec ((go (subr spin ((listof (productof (name symbol) (macro s7-macro)) acyclic)) (sumof (none unit) (some s7-macro)))
               (lambda (l) (cond ((null? l) (sum none #u))
                                 ((eq? (extract (car l) name) name) (sum some (extract (car l) macro)))
                                 (else (go (cdr l)))))))
      (go (get (extract sc macros))))))

(define* s7-memq-symbol (subr spin (symbol s7-symbols) bool)
  (lambda (s l) (and (pair? l) (or (eq? (car l) s) (s7-memq-symbol s (cdr l))))))

"What a name means where it is: a frame slot, a macro, a special form,
or a global."
(define-type s7-binding
  (sumof (b-local (productof (depth int) (index int) (name symbol)))
         (b-macro s7-macro)
         (b-special symbol)
         (b-global s7-global)))
(define* s7-resolve-in (subr s7-eff (symbol s7-scopes s7-ns) s7-binding)
  ;; `ns`: the namespace a free name is looked up in.
  (lambda (name scopes ns)
    (letrec ((in (subr s7-eff (s7-scopes int) (sumof (none unit) (found s7-binding)))
               (lambda (ss depth)
                 (if (null? ss) (sum none #u)
                     (let ((i (s7-scope-index (car ss) name)))
                       (if (>= i 0) (sum found (sum b-local (product (depth depth) (index i) (name name))))
                           (tagcase (s7-scope-macro (car ss) name)
                             (some m (sum found (sum b-macro m)))
                             (none u (in (cdr ss) (+ depth 1))))))))))
      (tagcase (in scopes 0)
        (found b b)
        (none u
          (if (and (s7-renamed? name) (tagcase (s7-ns-find ns name) (found c #f) (none u #t)))
              ;; A symbol a macro brought in, defined nowhere as itself: its
              ;; name, as its macro's namespace means it.
              (s7-resolve-in (s7-unrename name) scopes (s7-rename-ns name))
              (let ((cell (s7-ns-cell! ns name)))
                (tagcase (get (extract cell syntax))
                  (special s (sum b-special s))
                  (macro m (sum b-macro m))
                  (none u (sum b-global cell))))))))))
(define* s7-resolve (subr s7-eff (symbol s7-scopes) s7-binding)
  (lambda (name scopes) (s7-resolve-in name scopes (get s7-current-ns))))
"The special form `x`'s head names, or ` none`: a special form's own name
(`if`, `define`), or the head's macro's -- `macro` -- or none."
(define* s7-head-kind (subr s7-eff (s7-value s7-scopes) s7-binding)
  (lambda (x scopes)
    (tagcase x
      (pair p (tagcase (get (extract p car))
                (sym s (s7-resolve s scopes))
                (else y (sum b-special (string->symbol " none")))))
      (else y (sum b-special (string->symbol " none"))))))

;;; ------------------------------------------------------------ syntax-rules

"What a pattern variable matched: one datum, or a sequence (under `...`)."
(define-type s7-match (sumof (one s7-value) (many (listof s7-match acyclic))))
(define-type s7-matches (listof (productof (name symbol) (value s7-match)) acyclic))

"A list's items and what ends it (() if it is proper)."
(define* s7-items-and-tail (subr (maxeff spin (read @sc)) (s7-value) (productof (items s7-values) (tail s7-value)))
  (lambda (x)
    (letrec ((go (subr (maxeff spin (read @sc)) (s7-value s7-values int) (productof (items s7-values) (tail s7-value)))
               (lambda (x acc n)
                 (tagcase x
                   (pair p (if (> n 100000) (product (items (reverse acc)) (tail x))
                               (go (get (extract p cdr)) (cons (get (extract p car)) acc) (+ n 1))))
                   (else y (product (items (reverse acc)) (tail y)))))))
      (go x nil 0))))

"Whether atoms `a` and `b` are equal, as a pattern's datum matches."
(define* s7-atom-equal? (subr (read @sc) (s7-value s7-value) bool)
  (lambda (a b)
    (tagcase a
      (int i (tagcase b (int j (= i j)) (else y #f)))
      (real r (tagcase b (real s (f64= r s)) (else y #f)))
      (ratio q (tagcase b (ratio p (and (= (extract q num) (extract p num)) (= (extract q den) (extract p den)))) (else y #f)))
      (char c (tagcase b (char d (char=? c d)) (else y #f)))
      (bool c (tagcase b (bool d (bool=? c d)) (else y #f)))
      (str s (tagcase b (str t (string=? (get s) (get t))) (else y #f)))
      (null u (tagcase b (null v #t) (else y #f)))
      (else y #f))))

(define* s7-append-matches (subr spin (s7-matches s7-matches) s7-matches)
  (lambda (a b) (if (null? a) b (cons (car a) (s7-append-matches (cdr a) b)))))

"The pattern variables of pattern `p` (not literals, `_` or the ellipsis)."
(define* s7-pattern-vars (subr (maxeff spin (read @sc)) (s7-value s7-macro) s7-symbols)
  (lambda (p m)
    (tagcase p
      (sym s (if (or (s7-memq-symbol s (extract m literals)) (eq? s (extract m ellipsis))
                     (string=? (s7-symbol-name s) "_"))
                 nil
                 (list s)))
      (pair q (append (s7-pattern-vars (get (extract q car)) m) (s7-pattern-vars (get (extract q cdr)) m)))
      (vec a (letrec ((go (subr (maxeff spin (read @sc)) (s7-values) s7-symbols)
                            (lambda (l) (if (null? l) nil (append (s7-pattern-vars (car l) m) (go (cdr l)))))))
               (go (array->list a))))
      (else y nil))))

"The first `n` of `l`, and the rest."
(define* s7-take (subr spin (s7-values int) s7-values)
  (lambda (l n) (if (or (<= n 0) (null? l)) nil (cons (car l) (s7-take (cdr l) (- n 1))))))
(define* s7-drop (subr spin (s7-values int) s7-values)
  (lambda (l n) (if (or (<= n 0) (null? l)) l (s7-drop (cdr l) (- n 1)))))
(define* s7-lookup-match (subr spin (symbol s7-matches) s7-match)
  (lambda (name b)
    (cond ((null? b) (sum many nil))
          ((eq? (extract (car b) name) name) (extract (car b) value))
          (else (s7-lookup-match name (cdr b))))))
(define* s7-bound-match? (subr spin (symbol s7-matches) bool)
  (lambda (name b) (and (pair? b) (or (eq? (extract (car b) name) name) (s7-bound-match? name (cdr b))))))

"Each variable of `vars` bound to the sequence of what it matched in each
of `all`."
(define* s7-gather (subr spin (s7-symbols (listof s7-matches acyclic)) s7-matches)
  (lambda (vars all)
    (if (null? vars) nil
        (cons (product (name (car vars))
                       (value (sum many (letrec ((each (subr spin ((listof s7-matches acyclic)) (listof s7-match acyclic))
                                                         (lambda (l) (if (null? l) nil
                                                                         (cons (s7-lookup-match (car vars) (car l)) (each (cdr l)))))))
                                          (each all)))))
              (s7-gather (cdr vars) all)))))
"How many ellipses begin `l`."
(define* s7-ellipses (subr spin (s7-values symbol) int)
  (lambda (l ell)
    (if (and (pair? l) (s7-symbol? (car l)) (eq? (s7-sym (car l)) ell)) (+ 1 (s7-ellipses (cdr l) ell)) 0)))
"Value `v`, a proper list, as FX-26's list."
(define* s7-value->values (subr (maxeff spin (read @sc)) (s7-value) s7-values)
  (lambda (v) (tagcase (s7-list-items v) (some l l) (none u nil))))
"Lists `l` (values that are lists) appended."
(define* s7-flatten (subr (maxeff spin (read @sc)) (s7-values) s7-values)
  (lambda (l) (if (null? l) nil (append (s7-value->values (car l)) (s7-flatten (cdr l))))))
"The pattern variables of `b` that template `t` names."
(define* s7-template-vars (subr (maxeff spin (read @sc)) (s7-value s7-matches) s7-symbols)
  (lambda (t b)
    (tagcase t
      (sym s (if (s7-bound-match? s b) (list s) nil))
      (pair p (append (s7-template-vars (get (extract p car)) b) (s7-template-vars (get (extract p cdr)) b)))
      (vec a (letrec ((go (subr (maxeff spin (read @sc)) (s7-values) s7-symbols)
                            (lambda (l) (if (null? l) nil (append (s7-template-vars (car l) b) (go (cdr l)))))))
               (go (array->list a))))
      (else y nil))))
"Those of `vars` bound to sequences."
(define* s7-seq-vars (subr spin (s7-symbols s7-matches) s7-symbols)
  (lambda (vars b)
    (cond ((null? vars) nil)
          ((tagcase (s7-lookup-match (car vars) b) (many l #t) (one v #f)) (cons (car vars) (s7-seq-vars (cdr vars) b)))
          (else (s7-seq-vars (cdr vars) b)))))
(define* s7-seq-length (subr spin (symbol s7-matches) int)
  (lambda (v b) (tagcase (s7-lookup-match v b) (many l (list-length l)) (one x 1))))
(define* s7-same-lengths? (subr spin (s7-symbols int s7-matches) bool)
  (lambda (vars n b) (or (null? vars) (and (= (s7-seq-length (car vars) b) n) (s7-same-lengths? (cdr vars) n b)))))
(define* s7-list-ref-match (subr spin ((listof s7-match acyclic) int) s7-match)
  (lambda (l i) (cond ((null? l) (sum many nil)) ((= i 0) (car l)) (else (s7-list-ref-match (cdr l) (- i 1))))))

"`b` with each of `seqs` bound to its `i`th."
(define* s7-nth-matches (subr spin (s7-symbols int s7-matches) s7-matches)
  (lambda (seqs i b)
    (if (null? seqs) b
        (cons (product (name (car seqs))
                       (value (tagcase (s7-lookup-match (car seqs) b)
                                (many l (s7-list-ref-match l i))
                                (one v (sum one v)))))
              (s7-nth-matches (cdr seqs) i b)))))
"Form `x` matched against pattern `p` of macro `m`: the variables bound,
or (no)."
(define-rec
  (s7-match-pattern (->* (s7-value s7-value s7-macro) (sumof (no unit) (yes s7-matches)))
    (lambda (p x m)
      (tagcase p
        (sym s (cond ((string=? (s7-symbol-name s) "_") (sum yes nil))
                     ((s7-memq-symbol s (extract m literals))
                      (if (and (s7-symbol? x) (string=? (s7-symbol-name (s7-sym x)) (s7-symbol-name s)))
                          (sum yes nil) (sum no #u)))
                     (else (sum yes (list (product (name s) (value (sum one x))))))))
        (pair q (let ((pp (s7-items-and-tail p)))
                  (tagcase x
                    (pair r (let ((xx (s7-items-and-tail x)))
                              (s7-match-items (extract pp items) (extract pp tail) (extract xx items) (extract xx tail) m)))
                    (null u (s7-match-items (extract pp items) (extract pp tail) nil s7-nil m))
                    (else y (sum no #u)))))
        (null u (tagcase x (null v (sum yes nil)) (else y (sum no #u))))
        (vec a (tagcase x
                 (vec b (s7-match-items (array->list a) s7-nil (array->list b) s7-nil m))
                 (else y (sum no #u))))
        (else y (if (s7-atom-equal? p x) (sum yes nil) (sum no #u))))))
  ;; Items `ps` (then tail `pt`) against items `xs` (then tail `xt`).
  (s7-match-items (->* (s7-values s7-value s7-values s7-value s7-macro) (sumof (no unit) (yes s7-matches)))
    (lambda (ps pt xs xt m)
      (let ((ell (extract m ellipsis)))
        (cond
          ((and (pair? ps) (pair? (cdr ps)) (s7-symbol? (car (cdr ps))) (eq? (s7-sym (car (cdr ps))) ell))
           ;; `p ...` then `after`: `p` takes all but what `after` needs.
           (let* ((after (cdr (cdr ps)))
                  (na (list-length after))
                  (nx (list-length xs)))
             (if (< nx na) (sum no #u)
                 (let ((reps (s7-take xs (- nx na))) (rest (s7-drop xs (- nx na))))
                   (tagcase (s7-match-each (car ps) reps m)
                     (yes b1 (tagcase (s7-match-items after pt rest xt m)
                               (yes b2 (sum yes (s7-append-matches b1 b2)))
                               (no u (sum no #u))))
                     (no u (sum no #u)))))))
          ((pair? ps)
           (if (null? xs) (sum no #u)
               (tagcase (s7-match-pattern (car ps) (car xs) m)
                 (yes b1 (tagcase (s7-match-items (cdr ps) pt (cdr xs) xt m)
                           (yes b2 (sum yes (s7-append-matches b1 b2)))
                           (no u (sum no #u))))
                 (no u (sum no #u)))))
          ;; Patterns used up: the tail takes what is left.
          (else (s7-match-pattern pt (s7-list* xs xt) m))))))
  ;; Each of `xs` against `p`: each variable of `p` bound to the sequence.
  (s7-match-each (->* (s7-value s7-values s7-macro) (sumof (no unit) (yes s7-matches)))
    (lambda (p xs m)
      (letrec ((go (->* (s7-values (listof s7-matches acyclic)) (sumof (no unit) (yes (listof s7-matches acyclic))))
                 (lambda (xs acc)
                   (if (null? xs) (sum yes (reverse acc))
                       (tagcase (s7-match-pattern p (car xs) m)
                         (yes b (go (cdr xs) (cons b acc)))
                         (no u (sum no #u)))))))
        (tagcase (go xs nil)
          (no u (sum no #u))
          (yes all (sum yes (s7-gather (s7-pattern-vars p m) all))))))))

"Template `t` filled from `b`, each symbol it brings in renamed with
`suffix`; or an error."
(define-type s7-filled (sumof (ok s7-value) (bad string)))
(define-rec
  (s7-fill (->* (s7-value s7-matches s7-macro string bool) s7-filled)
    ;; `escaped`: inside `(... ...)`, where the ellipsis is just a symbol.
    (lambda (t b m suffix escaped)
      (tagcase t
        (sym s (if (s7-bound-match? s b)
                   (tagcase (s7-lookup-match s b)
                     (one v (sum ok v))
                     (many l (sum bad (string-append "pattern variable " (s7-symbol-name s) " used without its ellipsis"))))
                   (sum ok (sum sym (string->symbol (string-append (symbol->string s) suffix))))))
        (pair p
          (let ((ell (extract m ellipsis)) (head (get (extract p car))))
            (if (and (not escaped) (s7-symbol? head) (eq? (s7-sym head) ell))
                ;; (... template): the template, its ellipses plain symbols.
                (s7-fill (s7-cadr t) b m suffix #t)
                (let ((tt (s7-items-and-tail t)))
                  (tagcase (s7-fill-items (extract tt items) b m suffix escaped)
                    (ok items (tagcase (s7-fill (extract tt tail) b m suffix escaped)
                                (ok tail (sum ok (s7-list* (s7-value->values items) tail)))
                                (bad e (sum bad e))))
                    (bad e (sum bad e)))))))
        (vec a (tagcase (s7-fill-items (array->list a) b m suffix escaped)
                 (ok items (sum ok (sum vec (list->array (s7-value->values items)))))
                 (bad e (sum bad e))))
        (else y (sum ok y)))))
  ;; Items `ts`, each followed by any number of ellipses: the list filled.
  (s7-fill-items (->* (s7-values s7-matches s7-macro string bool) s7-filled)
    (lambda (ts b m suffix escaped)
      (if (null? ts) (sum ok s7-nil)
          (let* ((ell (extract m ellipsis))
                 (depth (if escaped 0 (s7-ellipses (cdr ts) ell)))
                 (rest (s7-drop (cdr ts) depth)))
            (tagcase (s7-fill-many (car ts) b m suffix escaped depth)
              (ok here (tagcase (s7-fill-items rest b m suffix escaped)
                         (ok there (sum ok (s7-list* (s7-value->values here) there)))
                         (bad e (sum bad e))))
              (bad e (sum bad e)))))))
  ;; Template `t` under `depth` ellipses: the list of what it gives.
  (s7-fill-many (->* (s7-value s7-matches s7-macro string bool int) s7-filled)
    (lambda (t b m suffix escaped depth)
      (if (= depth 0)
          (tagcase (s7-fill t b m suffix escaped) (ok v (sum ok (s7-list (list v)))) (bad e (sum bad e)))
          (let* ((vars (s7-template-vars t b))
                 (seqs (s7-seq-vars vars b)))
            (if (null? seqs)
                (sum bad "an ellipsis follows a template with no pattern variable under one")
                (let ((n (s7-seq-length (car seqs) b)))
                  (letrec ((go (->* (int s7-values) s7-filled)
                             (lambda (i acc)
                               (if (>= i n) (sum ok (s7-list (s7-flatten (reverse acc))))
                                   (tagcase (s7-fill-many t (s7-nth-matches seqs i b) m suffix escaped (- depth 1))
                                     (ok v (go (+ i 1) (cons v acc)))
                                     (bad e (sum bad e)))))))
                    (if (s7-same-lengths? seqs n b) (go 0 nil)
                        (sum bad "pattern variables under one ellipsis matched different numbers of forms"))))))))))

"Use `x` of macro `m` rewritten by its first rule that matches."
(define* s7-transcribe (subr s7-eff (s7-macro s7-value) s7-filled)
  (lambda (m x)
    (let* ((n (get s7-rename-count))
           (suffix (string-append " " (int->string n))))
      (begin
        (set s7-rename-count (+ n 1))
        (s7-note-rename-ns! n (extract m ns))
        (letrec ((go (->* ((listof s7-rule acyclic)) s7-filled)
                   (lambda (rules)
                     (if (null? rules) (sum bad (string-append "no rule of " (s7-symbol-name (s7-sym (s7-car x))) " matches this use"))
                         ;; The pattern's first item, the keyword, is not matched.
                         (tagcase (s7-match-pattern (s7-cdr (extract (car rules) pattern)) (s7-cdr x) m)
                           (yes b (s7-fill (extract (car rules) template) b m suffix #f))
                           (no u (go (cdr rules))))))))
          (go (extract m rules)))))))

(define* s7-symbols-of (subr spin (s7-values) s7-symbols)
  (lambda (l) (cond ((null? l) nil) ((s7-symbol? (car l)) (cons (s7-sym (car l)) (s7-symbols-of (cdr l)))) (else (s7-symbols-of (cdr l))))))

"`(syntax-rules …)` read as a macro defined in `scopes`, or an error."
(define* s7-parse-rules (subr s7-eff (s7-value s7-scopes) (sumof (ok s7-macro) (bad string)))
  (lambda (spec scopes)
    (if (not (and (s7-pair? spec) (s7-sym-named? (s7-car spec) "syntax-rules")))
        (sum bad "only syntax-rules macros are supported")
        (let* ((custom (s7-symbol? (s7-cadr spec)))
               (ell (if custom (s7-sym (s7-cadr spec)) (string->symbol "...")))
               (lits (if custom (s7-car (s7-cddr spec)) (s7-cadr spec)))
               (rules (if custom (s7-cdr (s7-cddr spec)) (s7-cddr spec))))
          (tagcase (s7-items lits)
            (none u (sum bad "syntax-rules: its literals are no list"))
            (some ls
              (tagcase (s7-items rules)
                (none u (sum bad "syntax-rules: its rules are no list"))
                (some rs
                  (letrec ((rule (->* (s7-values (listof s7-rule acyclic)) (sumof (ok (listof s7-rule acyclic)) (bad string)))
                             (lambda (rs acc)
                               (if (null? rs) (sum ok (reverse acc))
                                   (tagcase (s7-items (car rs))
                                     (some r (if (and (= (list-length r) 2) (s7-pair? (car r)))
                                                 (rule (cdr rs) (cons (product (pattern (car r)) (template (car (cdr r)))) acc))
                                                 (sum bad "syntax-rules: a rule is (pattern template)")))
                                     (none u (sum bad "syntax-rules: a rule is (pattern template)")))))))
                    (tagcase (rule rs nil)
                      (ok r (sum ok (product (literals (s7-symbols-of ls)) (ellipsis ell) (rules r) (scopes scopes) (ns (get s7-current-ns)))))
                      (bad e (sum bad e))))))))))))

;;; ------------------------------------------------------------ derived forms

"The directory a relative file name is relative to (`load`,
`open-input-file`, `include`), with its `/`; \"\": the process's own. A
client sets it (the editor: the buffer's directory)."
(define s7-directory (ref string @sc) (new ""))
"File name `file`, relative to `s7-directory` if it is relative."
(define* s7-path (subr (read @sc) (string) string)
  (lambda (file)
    (if (or (string=? (get s7-directory) "") (and (> (string-length file) 0) (char=? (string-ref file 0) #\/)))
        file
        (string-append (get s7-directory) file))))
"The text of file `file`, or why not."
(define* s7-file-text (subr (maxeff (io fs-read) (read @sc) spin) (string) (sumof (text string) (failed string)))
  (lambda (file)
    (tagcase (read-file (s7-path file))
      (data d (tagcase (utf8->string d)
                (text s (sum text s))
                (else y (sum failed (string-append file ": not UTF-8")))))
      (else y (sum failed (string-append "cannot read " file))))))

"Whether feature requirement `r` (of `cond-expand`) holds."
(define* s7-feature? (subr s7-eff (s7-value) bool)
  (lambda (r)
    (cond ((s7-symbol? r)
           (let ((n (s7-symbol-name (s7-sym r))))
             (or (string=? n "r7rs") (string=? n "s7st") (string=? n "exact-closed")
                 (string=? n "full-unicode") (string=? n "else"))))
          ((s7-sym-named? (s7-car r) "and")
           (letrec ((all (subr s7-eff (s7-values) bool) (lambda (l) (or (null? l) (and (s7-feature? (car l)) (all (cdr l)))))))
             (all (s7-value->values (s7-cdr r)))))
          ((s7-sym-named? (s7-car r) "or")
           (letrec ((any (subr s7-eff (s7-values) bool) (lambda (l) (and (pair? l) (or (s7-feature? (car l)) (any (cdr l)))))))
             (any (s7-value->values (s7-cdr r)))))
          ((s7-sym-named? (s7-car r) "not") (not (s7-feature? (s7-cadr r))))
          ;; Every library is here: everything is global.
          ((s7-sym-named? (s7-car r) "library") #t)
          (else #f))))

"`do`'s bindings, `(var init)` each; and their steps (the variable, if
none)."
(define* s7-do-inits (subr (maxeff spin (read @sc) (alloc @sc)) (s7-values) s7-values)
  (lambda (bs) (if (null? bs) nil (cons (s7-l (list (s7-car (car bs)) (s7-cadr (car bs)))) (s7-do-inits (cdr bs))))))
(define* s7-do-steps (subr (maxeff spin (read @sc) (alloc @sc)) (s7-values) s7-values)
  (lambda (bs)
    (if (null? bs) nil
        (cons (if (s7-pair? (s7-cddr (car bs))) (s7-car (s7-cddr (car bs))) (s7-car (car bs)))
              (s7-do-steps (cdr bs))))))
"`define-values`' definitions: each of `items` the `i`th of list `t`, and
`tail` (if a symbol) the rest."
(define* s7-values-defines (subr (maxeff spin (read @sc) (alloc @sc)) (s7-values s7-value s7-value int) s7-values)
  (lambda (items tail t i)
    (if (null? items)
        (if (s7-symbol? tail) (list (s7-l (list (s7-kw "define") tail (s7-l (list (s7-kw "list-tail") t (sum int i)))))) nil)
        (cons (s7-l (list (s7-kw "define") (car items) (s7-l (list (s7-kw "list-ref") t (sum int i)))))
              (s7-values-defines (cdr items) tail t (+ i 1))))))
"`(define-record-type name ctor pred field …)`, as definitions."
(define* s7-derive-record (subr s7-eff (s7-value) (sumof (none unit) (datum s7-value) (bad string)))
  (lambda (args)
    (let* ((name (s7-car args))
           (ctor (s7-cadr args))
           (pred (s7-car (s7-cddr args)))
           (specs (s7-value->values (s7-cdr (s7-cddr args))))
           (fields (s7-list (letrec ((go (subr (maxeff spin (read @sc)) (s7-values) s7-values)
                                           (lambda (l) (if (null? l) nil (cons (s7-car (car l)) (go (cdr l)))))))
                              (go specs))))
           (def (lambda ((n s7-value) (e s7-value)) (s7-l (list (s7-kw "define") n e))))
           (accessors (letrec ((go (subr (maxeff spin (read @sc) (alloc @sc)) (s7-values) s7-values)
                                 (lambda (l)
                                   (if (null? l) nil
                                       (let* ((f (s7-car (car l)))
                                              (acc (s7-cadr (car l)))
                                              (mod (s7-cddr (car l)))
                                              (rest (go (cdr l)))
                                              (with-acc (the s7-values
                                                         (if (s7-symbol? acc)
                                                             (cons (def acc (s7-l (list (s7-kw "record-accessor") name (s7-quoted f)))) rest)
                                                             rest))))
                                         (the s7-values
                                              (if (s7-pair? mod)
                                                  (cons (def (s7-car mod) (s7-l (list (s7-kw "record-modifier") name (s7-quoted f)))) with-acc)
                                                  with-acc)))))))
                         (go specs)))
           (ctor-def (the s7-values (cond ((s7-pair? ctor)
                            (list (def (s7-car ctor) (s7-l (list (s7-kw "record-constructor") name (s7-quoted (s7-cdr ctor)))))))
                           ((s7-symbol? ctor)
                            (list (def ctor (s7-l (list (s7-kw "record-constructor") name (s7-quoted fields))))))
                           (else nil))))
           (pred-def (the s7-values (if (s7-symbol? pred) (list (def pred (s7-l (list (s7-kw "record-predicate") name)))) nil))))
      (if (not (s7-symbol? name))
          (sum bad "define-record-type: its name is a symbol")
          (sum datum (s7-cons (s7-kw "begin")
                              (s7-list (cons (def name (s7-l (list (s7-kw "make-record-type") (s7-quoted name) (s7-quoted fields))))
                                             (append ctor-def pred-def accessors)))))))))

"What a derived form is rewritten as: data to expand instead, or an error;
(none) if `name` is no derived form."
(define-type s7-derived (sumof (none unit) (datum s7-value) (bad string)))
(define* s7-derive (subr s7-eff (symbol s7-value) s7-derived)
  (lambda (name x)
    (let ((args (s7-cdr x))
          (begin-of (lambda ((body s7-value)) (s7-cons (s7-kw "begin") body)))
          (ok (lambda ((v s7-value)) (the s7-derived (sum datum v)))))
      (cond
        ((eq? name 'let*)
         (tagcase (s7-items (s7-car args))
           (none u (sum bad "let*: its bindings are no list"))
           (some bs (ok (if (or (null? bs) (null? (cdr bs)))
                            (s7-cons (s7-kw "let") args)
                            (s7-l (list (s7-kw "let") (s7-l (list (car bs)))
                                        (s7-list* (list (s7-kw "let*") (s7-list (cdr bs))) (s7-cdr args)))))))))
        ((eq? name 'cond)
         (tagcase (s7-items args)
           (none u (sum bad "cond: its clauses are no list"))
           (some cs
             (if (null? cs) (ok (begin-of s7-nil))
                 (let ((c (car cs)) (more (s7-cons (s7-kw "cond") (s7-list (cdr cs)))))
                   (tagcase (s7-items c)
                     (none u (sum bad "cond: a clause is no list"))
                     (some ci
                       (cond ((null? ci) (sum bad "cond: an empty clause"))
                             ((s7-sym-named? (car ci) "else") (ok (begin-of (s7-cdr c))))
                             ((and (pair? (cdr ci)) (s7-sym-named? (car (cdr ci)) "=>"))
                              (if (not (and (pair? (cdr (cdr ci))) (null? (cdr (cdr (cdr ci))))))
                                  (sum bad "cond: => takes one procedure")
                                  (let ((t (s7-fresh-symbol "t")))
                                    (ok (s7-l (list (s7-kw "let") (s7-l (list (s7-l (list t (car ci)))))
                                                    (s7-l (list (s7-kw "if") t (s7-l (list (car (cdr (cdr ci))) t)) more))))))))
                             ((null? (cdr ci)) (ok (s7-l (list (s7-kw "or") (car ci) more))))
                             (else (ok (s7-l (list (s7-kw "if") (car ci) (begin-of (s7-cdr c)) more))))))))))))
        ((eq? name 'case)
         (tagcase (s7-items (s7-cdr args))
           (none u (sum bad "case: its clauses are no list"))
           (some cs
             (let ((t (s7-fresh-symbol "key")))
               (letrec ((chain (subr s7-eff (s7-values) s7-derived)
                          (lambda (cs)
                            (if (null? cs) (ok (begin-of s7-nil))
                                (let* ((c (car cs))
                                       (body (s7-cdr c))
                                       (then (if (and (s7-pair? body) (s7-sym-named? (s7-car body) "=>"))
                                                 (s7-l (list (s7-cadr body) t))
                                                 (begin-of body))))
                                  (cond ((s7-sym-named? (s7-car c) "else") (ok then))
                                        ((not (s7-pair? c)) (sum bad "case: a clause is no list"))
                                        (else (tagcase (chain (cdr cs))
                                                (datum rest (ok (s7-l (list (s7-kw "if")
                                                                            (s7-l (list (s7-kw "memv") t (s7-quoted (s7-car c))))
                                                                            then rest))))
                                                (else y y)))))))))
                 (tagcase (chain cs)
                   (datum d (ok (s7-l (list (s7-kw "let") (s7-l (list (s7-l (list t (s7-car args))))) d))))
                   (else y y)))))))
        ((eq? name 'and)
         (cond ((s7-null? args) (ok s7-true))
               ((s7-null? (s7-cdr args)) (ok (s7-car args)))
               (else (ok (s7-l (list (s7-kw "if") (s7-car args) (s7-cons (s7-kw "and") (s7-cdr args)) s7-false))))))
        ((eq? name 'or)
         (cond ((s7-null? args) (ok s7-false))
               ((s7-null? (s7-cdr args)) (ok (s7-car args)))
               (else (let ((t (s7-fresh-symbol "t")))
                       (ok (s7-l (list (s7-kw "let") (s7-l (list (s7-l (list t (s7-car args)))))
                                       (s7-l (list (s7-kw "if") t t (s7-cons (s7-kw "or") (s7-cdr args)))))))))))
        ((eq? name 'when)
         (ok (s7-l (list (s7-kw "if") (s7-car args) (begin-of (s7-cdr args))))))
        ((eq? name 'unless)
         (ok (s7-l (list (s7-kw "if") (s7-car args) (begin-of s7-nil) (begin-of (s7-cdr args))))))
        ((eq? name 'do)
         (tagcase (s7-items (s7-car args))
           (none u (sum bad "do: its bindings are no list"))
           (some bs
             (let* ((loop (s7-fresh-symbol "loop"))
                    (inits (s7-list (s7-do-inits bs)))
                    (steps (s7-do-steps bs))
                    (exit (s7-cadr args))
                    (body (s7-cddr args)))
               (ok (s7-l (list (s7-kw "let") loop inits
                               (s7-l (list (s7-kw "if") (s7-car exit) (begin-of (s7-cdr exit))
                                           (begin-of (s7-list* (s7-value->values body)
                                                               (s7-l (list (s7-cons loop (s7-list steps)))))))))))))))
        ((eq? name 'define-record-type) (s7-derive-record args))
        ((eq? name 'define-values)
         (let* ((formals (s7-car args))
                (t (s7-fresh-symbol "values"))
                (ft (s7-items-and-tail formals)))
           (ok (s7-cons (s7-kw "begin")
                        (s7-cons (s7-l (list (s7-kw "define") t
                                             (s7-l (list (s7-kw "call-with-values")
                                                         (s7-l (list (s7-kw "lambda") s7-nil (s7-cadr args)))
                                                         (s7-kw "list")))))
                                 (s7-list (s7-values-defines (extract ft items) (extract ft tail) t 0)))))))
        ((eq? name 'cond-expand)
         (tagcase (s7-items args)
           (none u (sum bad "cond-expand: its clauses are no list"))
           (some cs (letrec ((first (subr s7-eff (s7-values) s7-derived)
                               (lambda (cs) (cond ((null? cs) (ok (begin-of s7-nil)))
                                                  ((s7-feature? (s7-car (car cs))) (ok (begin-of (s7-cdr (car cs)))))
                                                  (else (first (cdr cs)))))))
                      (first cs)))))
        ((eq? name 'import) (ok (begin-of s7-nil)))
        ((eq? name 'define-library)
         ;; Its `begin`s' forms, at top level; exports and imports dropped.
         (tagcase (s7-items (s7-cdr args))
           (none u (sum bad "define-library: its declarations are no list"))
           (some ds (letrec ((go (subr s7-eff (s7-values) s7-values)
                               (lambda (ds)
                                 (cond ((null? ds) nil)
                                       ((or (s7-sym-named? (s7-car (car ds)) "begin") (s7-sym-named? (s7-car (car ds)) "include"))
                                        (cons (car ds) (go (cdr ds))))
                                       (else (go (cdr ds)))))))
                      (ok (begin-of (s7-list (go ds))))))))
        ((eq? name 'include)
         (tagcase (s7-items args)
           (none u (sum bad "include: its files are no list"))
           (some fs (letrec ((go (subr s7-eff (s7-values s7-values) s7-derived)
                               (lambda (fs acc)
                                 (if (null? fs) (ok (begin-of (s7-list (reverse acc))))
                                     (tagcase (car fs)
                                       (str s (tagcase (s7-file-text (get s))
                                                (text t (tagcase (s7-read-all t (get s))
                                                          (data ds (go (cdr fs) (append (reverse ds) acc)))
                                                          (stop r (sum bad (string-append "include: cannot read " (get s))))))
                                                (failed m (sum bad (string-append "include: " m)))))
                                       (else y (sum bad "include: a file name is a string")))))))
                      (go fs nil)))))
        (else (sum none #u))))))

;;; ------------------------------------------------------------ the expander

"What a body holds, in order: definitions (into frame slots) and
expressions; or an error, kept to report in its place."
(define-type s7-item
  (sumof (i-def (productof (index int) (name symbol) (value s7-value) (span s7-span)))
         (i-expr (productof (form s7-value) (span s7-span)))
         (i-bad (productof (message string) (span s7-span)))))
(define-type s7-item-list (listof s7-item acyclic))
(define* s7-append-items (subr spin (s7-item-list s7-item-list) s7-item-list)
  (lambda (a b) (if (null? a) b (cons (car a) (s7-append-items (cdr a) b)))))

"A lambda's parameters: their names, the last the rest's if `rest`."
(define* s7-formals (subr (maxeff spin (read @sc) (alloc @sc)) (s7-value) (sumof (ok (productof (names s7-symbols) (rest bool))) (bad string)))
  (lambda (formals)
    (let ((ft (s7-items-and-tail formals)))
      (letrec ((all-symbols (subr spin (s7-values) bool)
                 (lambda (l) (or (null? l) (and (s7-symbol? (car l)) (all-symbols (cdr l)))))))
        (cond ((not (all-symbols (extract ft items))) (sum bad "a parameter is no symbol"))
              ((s7-null? (extract ft tail)) (sum ok (product (names (s7-symbols-of (extract ft items))) (rest #f))))
              ((s7-symbol? (extract ft tail))
               (sum ok (product (names (append (s7-symbols-of (extract ft items)) (list (s7-sym (extract ft tail))))) (rest #t))))
              (else (sum bad "a lambda's parameters are a list of symbols")))))))

"`(define …)`'s name and value: `(define x e)`, `(define x)`, `(define (f
. formals) body …)`, or curried, `(define ((f a) b) …)`."
(define* s7-define-target (subr s7-eff (s7-value) (sumof (ok (productof (name symbol) (value s7-value))) (bad string)))
  (lambda (x)
    (let ((target (s7-cadr x)) (rest (s7-cddr x)))
      (cond ((s7-symbol? target)
             (sum ok (product (name (s7-sym target))
                              (value (if (s7-pair? rest) (s7-car rest) (s7-l (list (s7-kw "begin"))))))))
            ((s7-pair? target)
             (s7-define-target (s7-l (list (s7-kw "define") (s7-car target)
                                           (s7-cons (s7-kw "lambda") (s7-cons (s7-cdr target) rest))))))
            (else (sum bad "define: what is defined is no symbol"))))))

"A `let`'s bindings, `((v e) …)`: their names and initial values."
(define* s7-let-bindings (subr (maxeff spin (read @sc) (alloc @sc)) (s7-value) (sumof (ok (productof (names s7-symbols) (inits s7-values))) (bad string)))
  (lambda (bs)
    (tagcase (s7-items bs)
      (none u (sum bad "its bindings are no list"))
      (some l (letrec ((go (subr (maxeff spin (read @sc) (alloc @sc)) (s7-values s7-symbols s7-values)
                                 (sumof (ok (productof (names s7-symbols) (inits s7-values))) (bad string)))
                         (lambda (l names inits)
                           (cond ((null? l) (sum ok (product (names (reverse names)) (inits (reverse inits)))))
                                 ((and (s7-pair? (car l)) (s7-symbol? (s7-car (car l))))
                                  (go (cdr l) (cons (s7-sym (s7-car (car l))) names)
                                      (cons (if (s7-pair? (s7-cdr (car l))) (s7-cadr (car l)) (s7-l (list (s7-kw "begin")))) inits)))
                                 (else (sum bad "a binding is (name value)"))))))
                (go l nil nil))))))

"Each of `names`, given `inits`, a definition in scope `sc`."
(define* s7-letrec-items (subr (maxeff spin (read @sc) (write @sc)) (s7-scope s7-symbols s7-values s7-span) s7-item-list)
  (lambda (sc names inits span)
    (if (or (null? names) (null? inits)) nil
        (let ((i (s7-scope-add! sc (car names))))
          (cons (sum i-def (product (index i) (name (car names)) (value (car inits)) (span span)))
                (s7-letrec-items sc (cdr names) (cdr inits) span))))))

"Each `(name (syntax-rules …))` of `bs` bound as a macro in scope `sc`,
defined in `scopes`: \"\", or an error."
(define* s7-add-macros! (subr s7-eff (s7-scope s7-values s7-scopes) string)
  (lambda (sc bs scopes)
    (if (null? bs) ""
        (let ((b (car bs)))
          (if (not (s7-symbol? (s7-car b))) "a macro's name is a symbol"
              (tagcase (s7-parse-rules (s7-cadr b) scopes)
                (ok m (begin (set (extract sc macros) (cons (product (name (s7-sym (s7-car b))) (macro m)) (get (extract sc macros))))
                        (s7-add-macros! sc (cdr bs) scopes)))
                (bad e e)))))))

"A call of procedure ` name` (one no program binds)."
(define* s7-call-kw (subr s7-eff (string s7-nodes s7-span) s7-node)
  (lambda (name args span)
    (s7-node-at span (sum n-call (product (op (s7-node-at span (sum n-global (s7-global-cell (string->symbol (string-append " " name))))))
                                          (args args))))))
"A pair of nodes' values, folded if both are constants."
(define* s7-qq-cons (subr s7-eff (s7-node s7-node s7-span) s7-node)
  (lambda (a d span)
    (tagcase (extract a form)
      (n-const va (tagcase (extract d form)
                    (n-const vd (s7-const-node (s7-cons va vd) span))
                    (else y (s7-call-kw "cons" (list a d) span))))
      (else y (s7-call-kw "cons" (list a d) span)))))

(define* s7-symbols->values (subr spin (s7-symbols) s7-values)
  (lambda (l) (if (null? l) nil (cons (sum sym (car l)) (s7-symbols->values (cdr l))))))

(define-rec
  ;; Datum `x` in `scopes`, as core; `outer` the span of the form around it.
  (s7-expand (->* (s7-value s7-scopes s7-span) s7-node)
    (lambda (x scopes outer)
      (let ((span (let ((s (s7-span-of x))) (if (< (extract s start) 0) outer s))))
        (tagcase x
          (sym s (tagcase (s7-resolve s scopes)
                   (b-local l (s7-node-at span (sum n-local l)))
                   (b-global c (s7-node-at span (sum n-global c)))
                   (b-special k (s7-fail-node (string-append "syntax used as a variable: " (s7-symbol-name s)) span))
                   (b-macro m (s7-fail-node (string-append "a macro used as a variable: " (s7-symbol-name s)) span))))
          (pair p (s7-expand-form x scopes span ""))
          (null u (s7-fail-node "() is no expression" span))
          (else y (s7-const-node y span))))))
  ;; As `s7-expand`, naming the procedure a lambda makes `name`.
  (s7-expand-named (->* (s7-value s7-scopes s7-span string) s7-node)
    (lambda (x scopes outer name)
      (let ((span (let ((s (s7-span-of x))) (if (< (extract s start) 0) outer s))))
        (tagcase x
          (pair p (s7-expand-form x scopes span name))
          (else y (s7-expand x scopes span))))))
  (s7-expand-form (->* (s7-value s7-scopes s7-span string) s7-node)
    (lambda (x scopes span name)
      (tagcase (s7-head-kind x scopes)
        (b-special k (if (eq? k (string->symbol " none"))
                         (s7-expand-call x scopes span)
                         (s7-expand-special k x scopes span name)))
        (b-macro m (tagcase (s7-transcribe m x)
                     (ok y (s7-expand-named y scopes span name))
                     (bad e (s7-fail-node e span))))
        (else y (s7-expand-call x scopes span)))))
  (s7-expand-call (->* (s7-value s7-scopes s7-span) s7-node)
    (lambda (x scopes span)
      (tagcase (s7-items x)
        (none u (s7-fail-node "a call's arguments are no list" span))
        (some l (s7-node-at span (sum n-call (product (op (s7-expand (car l) scopes span))
                                                      (args (s7-expand-all (cdr l) scopes span)))))))))
  (s7-expand-all (->* (s7-values s7-scopes s7-span) s7-nodes)
    (lambda (l scopes span)
      (if (null? l) nil (cons (s7-expand (car l) scopes span) (s7-expand-all (cdr l) scopes span)))))
  ;; Initial values, each named for the variable it is given to.
  (s7-expand-inits (->* (s7-values s7-symbols s7-scopes s7-span) s7-nodes)
    (lambda (l names scopes span)
      (if (or (null? l) (null? names)) nil
          (cons (s7-expand-named (car l) scopes span (s7-symbol-name (car names)))
                (s7-expand-inits (cdr l) (cdr names) scopes span)))))
  (s7-expand-lambda (->* (s7-value s7-values s7-scopes s7-span string) s7-lambda)
    (lambda (formals body scopes span name)
      (tagcase (s7-formals formals)
        (bad e (product (id (s7-fresh-id)) (name name) (required 0) (rest #t) (size 1)
                        (body (s7-fail-node e span)) (span span) (names (list (string->symbol " args")))))
        (ok f (let* ((sc (s7-new-scope (extract f names)))
                     (b (s7-expand-body body (the s7-scopes (cons sc scopes)) span nil))
                     (n (list-length (extract f names))))
                (product (id (s7-fresh-id)) (name name)
                         (required (if (extract f rest) (- n 1) n)) (rest (extract f rest))
                         (size (get (extract sc count))) (body b) (span span) (names (s7-scope-names sc))))))))
  (s7-expand-clauses (->* (s7-values s7-scopes s7-span string) (listof s7-lambda acyclic))
    (lambda (cs scopes span name)
      (if (null? cs) nil
          (cons (s7-expand-lambda (s7-car (car cs)) (s7-value->values (s7-cdr (car cs))) scopes span name)
                (s7-expand-clauses (cdr cs) scopes span name)))))
  ;; A body: its definitions found first (`pre`, then those of `forms`), in
  ;; the innermost scope, then each expanded.
  (s7-expand-body (->* (s7-values s7-scopes s7-span s7-item-list) s7-node)
    (lambda (forms scopes span pre)
      (let* ((items (s7-append-items pre (reverse (s7-scan forms scopes span nil))))
             (nodes (s7-expand-items items scopes span)))
        (cond ((null? nodes) (s7-const-node s7-unspecified span))
              ((null? (cdr nodes)) (car nodes))
              (else (s7-node-at span (sum n-seq nodes)))))))
  (s7-scan (->* (s7-values s7-scopes s7-span s7-item-list) s7-item-list)
    (lambda (forms scopes span acc)
      (if (null? forms) acc
          (let* ((f (car forms))
                 (fspan (let ((s (s7-span-of f))) (if (< (extract s start) 0) span s)))
                 (expr (lambda () (the s7-item-list (cons (sum i-expr (product (form f) (span fspan))) acc))))
                 (bad (lambda ((m string)) (the s7-item-list (cons (sum i-bad (product (message m) (span fspan))) acc)))))
            (s7-scan (cdr forms) scopes span
                     (tagcase (s7-head-kind f scopes)
                       (b-special k
                         (cond ((eq? k 'begin) (s7-scan (s7-value->values (s7-cdr f)) scopes fspan acc))
                               ((eq? k 'define)
                                (tagcase (s7-define-target f)
                                  (ok t (the s7-item-list
                                             (cons (sum i-def (product (index (s7-scope-add! (car scopes) (extract t name)))
                                                                       (name (extract t name)) (value (extract t value)) (span fspan)))
                                                   acc)))
                                  (bad e (bad e))))
                               ((eq? k 'define-syntax)
                                (if (not (s7-symbol? (s7-cadr f))) (bad "define-syntax: its name is a symbol")
                                    (tagcase (s7-parse-rules (s7-car (s7-cddr f)) scopes)
                                      (ok m (begin (set (extract (car scopes) macros)
                                                        (cons (product (name (s7-sym (s7-cadr f))) (macro m)) (get (extract (car scopes) macros))))
                                              acc))
                                      (bad e (bad e)))))
                               ((or (eq? k 'define-values) (eq? k 'define-record-type))
                                (tagcase (s7-derive k f)
                                  (datum d (s7-scan (list d) scopes fspan acc))
                                  (bad e (bad e))
                                  (none u (expr))))
                               (else (expr))))
                       (b-macro m (tagcase (s7-transcribe m f)
                                    (ok d (s7-scan (list d) scopes fspan acc))
                                    (bad e (bad e))))
                       (else y (expr))))))))
  (s7-expand-items (->* (s7-item-list s7-scopes s7-span) s7-nodes)
    (lambda (items scopes span)
      (if (null? items) nil
          (cons (tagcase (car items)
                  (i-def d (s7-node-at (extract d span)
                                       (sum n-set-local (product (depth 0) (index (extract d index))
                                                                 (value (s7-expand-named (extract d value) scopes (extract d span)
                                                                                         (s7-symbol-name (extract d name))))))))
                  (i-expr e (s7-expand (extract e form) scopes (extract e span)))
                  (i-bad b (s7-fail-node (extract b message) (extract b span))))
                (s7-expand-items (cdr items) scopes span)))))
  ;; Quasiquoted template `t`, `depth` quasiquotes deep.
  (s7-quasi (->* (s7-value int s7-scopes s7-span) s7-node)
    (lambda (t depth scopes span)
      (let ((wrap (lambda ((name string) (inner s7-node))
                    ;; `(name inner)`, as a list.
                    (s7-qq-cons (s7-const-node (s7-symbol name) span) (s7-qq-cons inner (s7-const-node s7-nil span) span) span))))
        (tagcase t
          (pair p
            (let ((head (get (extract p car))))
              (cond ((s7-sym-named? head "unquote")
                     (if (= depth 1) (s7-expand (s7-cadr t) scopes span)
                         (wrap "unquote" (s7-quasi (s7-cadr t) (- depth 1) scopes span))))
                    ((s7-sym-named? head "quasiquote")
                     (wrap "quasiquote" (s7-quasi (s7-cadr t) (+ depth 1) scopes span)))
                    ((and (s7-pair? head) (s7-sym-named? (s7-car head) "unquote-splicing"))
                     (let ((rest (s7-quasi (get (extract p cdr)) depth scopes span)))
                       (if (= depth 1)
                           (s7-call-kw "append" (list (s7-expand (s7-cadr head) scopes span) rest) span)
                           (s7-qq-cons (wrap "unquote-splicing" (s7-quasi (s7-cadr head) (- depth 1) scopes span)) rest span))))
                    (else (s7-qq-cons (s7-quasi head depth scopes span)
                                      (s7-quasi (get (extract p cdr)) depth scopes span) span)))))
          (vec a (let ((l (s7-quasi (s7-list (array->list a)) depth scopes span)))
                   (tagcase (extract l form)
                     (n-const v (s7-const-node t span))
                     (else y (s7-call-kw "list->vector" (list l) span)))))
          (else y (s7-const-node (s7-strip y) span))))))
  ;; Special form `k`, `x` its use.
  (s7-expand-special (->* (symbol s7-value s7-scopes s7-span string) s7-node)
    (lambda (k x scopes span name)
      (let ((args (s7-cdr x))
            (fail (lambda ((m string)) (s7-fail-node (string-append (symbol->string k) ": " m) span))))
        (cond
          ((eq? k 'quote)
           (if (and (s7-pair? args) (s7-null? (s7-cdr args))) (s7-const-node (s7-strip (s7-car args)) span) (fail "takes one datum")))
          ((eq? k 'quasiquote)
           (if (and (s7-pair? args) (s7-null? (s7-cdr args))) (s7-quasi (s7-car args) 1 scopes span) (fail "takes one template")))
          ((or (eq? k 'unquote) (eq? k 'unquote-splicing)) (fail "not in a quasiquote"))
          ((eq? k 'lambda)
           (if (s7-pair? args)
               (s7-node-at span (sum n-lambda (list (s7-expand-lambda (s7-car args) (s7-value->values (s7-cdr args)) scopes span name))))
               (fail "takes parameters and a body")))
          ((eq? k 'case-lambda)
           (tagcase (s7-items args)
             (some cs (s7-node-at span (sum n-lambda (s7-expand-clauses cs scopes span name))))
             (none u (fail "its clauses are no list"))))
          ((eq? k 'define)
           (if (pair? scopes) (fail "a definition is not allowed here")
               (tagcase (s7-define-target x)
                 (bad e (fail e))
                 (ok t (let ((cell (s7-ns-own-cell! (get s7-current-ns) (extract t name))))
                         (begin
                           (set (extract cell syntax) (sum none #u))
                           (s7-node-at span (sum n-define (product (cell cell)
                                                                  (value (s7-expand-named (extract t value) scopes span
                                                                                          (s7-symbol-name (extract t name)))))))))))))
          ((eq? k 'define-syntax)
           (cond ((pair? scopes) (fail "not allowed here"))
                 ((not (s7-symbol? (s7-car args))) (fail "its name is a symbol"))
                 (else (tagcase (s7-parse-rules (s7-cadr args) scopes)
                         (ok m (begin (set (extract (s7-ns-own-cell! (get s7-current-ns) (s7-sym (s7-car args))) syntax) (sum macro m))
                                 (s7-const-node s7-unspecified span)))
                         (bad e (fail e))))))
          ((or (eq? k 'let-syntax) (eq? k 'letrec-syntax))
           (tagcase (s7-items (s7-car args))
             (none u (fail "its bindings are no list"))
             (some bs (let* ((sc (s7-new-scope nil))
                             (inner (the s7-scopes (cons sc scopes)))
                             (err (s7-add-macros! sc bs (if (eq? k 'letrec-syntax) inner scopes))))
                        (if (not (string=? err "")) (fail err)
                            (let ((b (s7-expand-body (s7-value->values (s7-cdr args)) inner span nil)))
                              (s7-node-at span (sum n-scope (product (size (get (extract sc count))) (body b)
                                                                     (names (s7-scope-names sc)))))))))))
          ((eq? k 'syntax-rules) (fail "only a macro's definition"))
          ((eq? k 'set!)
           (if (not (and (s7-symbol? (s7-car args)) (s7-pair? (s7-cdr args)))) (fail "takes a variable and a value")
               (let ((v (s7-expand (s7-cadr args) scopes span)))
                 (tagcase (s7-resolve (s7-sym (s7-car args)) scopes)
                   (b-local l (s7-node-at span (sum n-set-local (product (depth (extract l depth)) (index (extract l index)) (value v)))))
                   (b-global c (s7-node-at span (sum n-set-global (product (cell c) (value v)))))
                   (else y (fail "what is set is no variable"))))))
          ((eq? k 'if)
           (tagcase (s7-items args)
             (some l (cond ((= (list-length l) 2)
                            (s7-node-at span (sum n-if (product (test (s7-expand (car l) scopes span))
                                                                (then (s7-expand (car (cdr l)) scopes span))
                                                                (else (s7-const-node s7-unspecified span))))))
                           ((= (list-length l) 3)
                            (s7-node-at span (sum n-if (product (test (s7-expand (car l) scopes span))
                                                                (then (s7-expand (car (cdr l)) scopes span))
                                                                (else (s7-expand (car (cdr (cdr l))) scopes span))))))
                           (else (fail "takes a test, then one or two branches"))))
             (none u (fail "its operands are no list"))))
          ((eq? k 'begin)
           (tagcase (s7-items args)
             (some l (cond ((null? l) (s7-const-node s7-unspecified span))
                           ((null? (cdr l)) (s7-expand-named (car l) scopes span name))
                           (else (s7-node-at span (sum n-seq (s7-expand-all l scopes span))))))
             (none u (fail "its forms are no list"))))
          ((eq? k 'let)
           (if (s7-symbol? (s7-car args))
               ;; A named let: the procedure bound in a scope of its own, the
               ;; initial values evaluated outside it.
               (let ((loop (s7-sym (s7-car args))))
                 (tagcase (s7-let-bindings (s7-cadr args))
                   (bad e (fail e))
                   (ok bs (let* ((sc (s7-new-scope (list loop)))
                                 (lam (s7-expand-lambda (s7-list (s7-symbols->values (extract bs names)))
                                                        (s7-value->values (s7-cddr args)) (the s7-scopes (cons sc scopes)) span
                                                        (s7-symbol-name loop)))
                                 (inits (s7-expand-inits (extract bs inits) (extract bs names) scopes span))
                                 (here (lambda ((f s7-form)) (s7-node-at span f))))
                            (here (sum n-call
                                       (product (op (here (sum n-scope
                                                               (product (size 1)
                                                                        (body (here (sum n-seq
                                                                                         (list (here (sum n-set-local
                                                                                                          (product (depth 0) (index 0)
                                                                                                                   (value (here (sum n-lambda (list lam)))))))
                                                                                               (here (sum n-local (product (depth 0) (index 0) (name loop))))))))
                                                                        (names (list loop))))))
                                                (args inits))))))))
               (tagcase (s7-let-bindings (s7-car args))
                 (bad e (fail e))
                 (ok bs (let ((lam (s7-expand-lambda (s7-list (s7-symbols->values (extract bs names)))
                                                     (s7-value->values (s7-cdr args)) scopes span ""))
                              (inits (s7-expand-inits (extract bs inits) (extract bs names) scopes span)))
                          (s7-node-at span (sum n-call (product (op (s7-node-at span (sum n-lambda (list lam)))) (args inits)))))))))
          ((or (eq? k 'letrec) (eq? k 'letrec*))
           (tagcase (s7-let-bindings (s7-car args))
             (bad e (fail e))
             (ok bs (let* ((sc (s7-new-scope nil))
                           (pre (s7-letrec-items sc (extract bs names) (extract bs inits) span))
                           (b (s7-expand-body (s7-value->values (s7-cdr args)) (the s7-scopes (cons sc scopes)) span pre)))
                      (s7-node-at span (sum n-scope (product (size (get (extract sc count))) (body b) (names (s7-scope-names sc)))))))))
          (else
           (tagcase (s7-derive k x)
             (datum d (s7-expand-named d scopes span name))
             (bad e (fail e))
             (none u (fail "is no special form s7st knows")))))))))

"Top-level form `x`, as core."
(define* s7-expand-top (subr s7-eff (s7-value) s7-node)
  (lambda (x) (s7-expand x nil (s7-span-of x))))

"The special forms, each bound by its name and by ` name`."
(define s7-special-names s7-strings
  (list "quote" "quasiquote" "unquote" "unquote-splicing" "lambda" "define" "set!" "if" "begin"
        "let" "let*" "letrec" "letrec*" "cond" "case" "and" "or" "when" "unless" "do"
        "define-syntax" "let-syntax" "letrec-syntax" "syntax-rules" "define-record-type"
        "case-lambda" "define-values" "import" "define-library" "cond-expand" "include"))
(define* s7-define-specials! (subr s7-eff (s7-strings) unit)
  (lambda (names)
    (if (null? names) #u
        (let ((k (sum special (string->symbol (car names)))))
          (begin
            (set (extract (s7-global-cell (string->symbol (car names))) syntax) k)
            (set (extract (s7-global-cell (string->symbol (string-append " " (car names)))) syntax) k)
            (s7-define-specials! (cdr names)))))))
