;;; resolve.fx: what each name in an FX-26 text refers to, as the text
;;; shows (cahoots' `(yank actor scope)`, yank's `binder-at`; the first
;;; stage of docs/fx26-analysis.md).
;;;
;;; A walk over the reader's syntax -- not Fixpt's parser's trees, whose
;;; binders have no spans -- with an environment of the local binders in
;;; scope, innermost first, each with its span. A symbol that is a use is
;;; resolved to the innermost local binder of its name, else to a
;;; definition of the file's (at the top level, or an item of a `module`),
;;; else to nothing known here (a standard name, or another file's). Types
;;; and values are looked up alike: FX-26 keeps them apart, but a name's
;;; binder is what M-. wants either way.
(module-parameters ((m-base (load-moduleof "base.fx"))
                    (m-buffer (load-moduleof "buffer.fx" m-base))))
(hide (define kit-lists (load-module "../kit/lists.fx"))
      (import kit-lists member?))


(define-type syns-a (listof syn acyclic))

;; The symbol an atom is, or "".
(define* atom-symbol (subr spin (syn) string)
  (lambda (x)
    (tagcase x
      (atom (d a b) (typecase d (symbol s (symbol->string s)) (else y "")))
      (else y ""))))

(define* syn-start (subr pure (syn) int)
  (lambda (x) (tagcase x (atom (d a b) a) (lst (i d a b) a) (dotted (i t d a b) a) (vec (i d a b) a))))
(define* syn-end (subr pure (syn) int)
  (lambda (x) (tagcase x (atom (d a b) b) (lst (i d a b) b) (dotted (i t d a b) b) (vec (i d a b) b))))

(define* items-of (subr pure (syn) syns-a)
  (lambda (x) (tagcase x (lst (i d a b) i) (else y nil))))

;; The binder an atom names, if it is a symbol.
(define* binder-of (subr spin (syn binders) binders)
  (lambda (x acc)
    (let ((n (atom-symbol x)))
      (if (string=? n "") acc (cons (product (name n) (start (syn-start x)) (end (syn-end x))) acc)))))

;; A parameter: `x`, or `(x type)`.
(define* param-binder (subr spin (syn binders) binders)
  (lambda (p acc)
    (tagcase p
      (lst (items d a b) (if (pair? items) (binder-of (car items) acc) acc))
      (else y (binder-of p acc)))))

(define* params-binders (subr spin (syns-a binders) binders)
  (lambda (ps acc) (if (null? ps) acc (params-binders (cdr ps) (param-binder (car ps) acc)))))

;; The first of `xs`'s items that is a list, its items; or nil.
(define* second (subr pure (syns-a) syns-a)
  (lambda (xs) (if (and (pair? xs) (pair? (cdr xs))) (cdr xs) nil)))

(define* lookup (subr spin (string binders) (sumof (none unit) (found binder)))
  (lambda (n env)
    (cond ((null? env) (sum none #u))
          ((string=? (extract (car env) name) n) (sum found (car env)))
          (else (lookup n (cdr env))))))

"The names a definition-like form defines, onto `acc`: `(define x …)`,
`(define* x …)`, `(define-type t …)` or `(define-type (t p …) …)`,
`(define-effect e …)`, `(define-generative t …)`, a `define-datatype`'s type
and each variant's constructor, `define-rec`'s names, and `import`'s."
(define* defined-binders (subr spin (syn binders) binders)
  (lambda (form acc)
    (let* ((items (items-of form))
           (head (if (pair? items) (atom-symbol (car items)) ""))
           (rest (if (pair? items) (cdr items) nil)))
      (cond ((member? head (list "define" "define*" "define-type" "define-effect" "define-generative") string=?)
             (if (pair? rest)
                 (tagcase (car rest)
                   (lst (is d a b) (if (pair? is) (binder-of (car is) acc) acc))
                   (else y (binder-of (car rest) acc)))
                 acc))
            ((string=? head "define-datatype")
             (if (pair? rest)
                 (letrec ((variants (subr spin (syns-a binders) binders)
                            (lambda (vs acc)
                              (if (null? vs) acc
                                  (variants (cdr vs)
                                            (let ((is (items-of (car vs))))
                                              (if (pair? is) (binder-of (car is) acc) acc)))))))
                   (variants (cdr rest)
                             (tagcase (car rest)
                               (lst (is d a b) (if (pair? is) (binder-of (car is) acc) acc))
                               (else y (binder-of (car rest) acc)))))
                 acc))
            ((string=? head "define-rec")
             (letrec ((go (subr spin (syns-a binders) binders)
                        (lambda (bs acc)
                          (if (null? bs) acc
                              (go (cdr bs) (let ((is (items-of (car bs))))
                                             (if (pair? is) (binder-of (car is) acc) acc)))))))
               (go rest acc)))
            ((string=? head "import")
             ;; `(import m name … (type t …) (effect e …))`: the names, the
             ;; marked groups' too.
             (letrec ((go (subr spin (syns-a binders) binders)
                        (lambda (xs acc)
                          (if (null? xs) acc
                              (go (cdr xs)
                                  (tagcase (car xs)
                                    (lst (is d a b) (go (if (pair? is) (cdr is) nil) acc))
                                    (else y (binder-of (car xs) acc))))))))
               (go (if (pair? rest) (cdr rest) nil) acc)))
            ((string=? head "hide")
             (letrec ((go (subr spin (syns-a binders) binders)
                        (lambda (xs acc) (if (null? xs) acc (go (cdr xs) (defined-binders (car xs) acc))))))
               (go rest acc)))
            (else acc)))))

"The binders the forms `xs` define, as items in one scope."
(define* items-binders (subr spin ((listof syn acyclic) binders) binders)
  (lambda (xs acc) (if (null? xs) acc (items-binders (cdr xs) (defined-binders (car xs) acc)))))

;; The walk: forms `xs` in environment `env` (locals, innermost first,
;; then the definitions in scope), references found onto `acc`, newest
;; first.
(define-rec
  (resolve-all (->* ((listof syn acyclic) binders references) references)
    (lambda (xs env acc) (if (null? xs) acc (resolve-all (cdr xs) env (resolve-syn (car xs) env acc)))))
  (resolve-syn (->* (syn binders references) references)
    (lambda (x env acc)
      (tagcase x
        (atom (d a b)
          (let ((n (atom-symbol x)))
            (if (string=? n "")
                acc
                (tagcase (lookup n env)
                  (found bd (cons (product (start a) (end b) (binder-start (extract bd start)) (binder-end (extract bd end)))
                                  acc))
                  (none u (cons (product (start a) (end b) (binder-start -1) (binder-end -1)) acc))))))
        (dotted (items tail d a b) (resolve-syn tail env (resolve-all items env acc)))
        (vec (items d a b) acc)
        (lst (items d a b)
          (let ((head (if (pair? items) (atom-symbol (car items)) ""))
                (rest (if (pair? items) (cdr items) nil)))
            (resolve-form head rest items env acc))))))
  ;; A list whose head is the symbol `head` ("" if it is not one).
  (resolve-form (->* (string (listof syn acyclic) (listof syn acyclic) binders references) references)
    (lambda (head rest items env acc)
      (cond
        ;; Quoted data refers to nothing.
        ((member? head (list "quote" "quasiquote") string=?) acc)
        ;; `(lambda (p …) body …)`, `(rlambda r (p …) body …)`: the
        ;; parameters' types in `env`, the body in it and the parameters.
        ((string=? head "lambda")
         (if (pair? rest)
             (let ((ps (items-of (car rest))))
               (resolve-all (cdr rest) (params-binders ps env) (resolve-param-types ps env acc)))
             acc))
        ((string=? head "vlambda")
         (if (pair? rest) (resolve-all (cdr rest) (param-binder (car rest) env) acc) acc))
        ;; `(plambda ((t kind) …) body)`: type binders.
        ((string=? head "plambda")
         (if (pair? rest) (resolve-all (cdr rest) (params-binders (items-of (car rest)) env) acc) acc))
        ;; `(let ((x e) …) body …)`: each `e` outside; the body inside.
        ((string=? head "let")
         (if (pair? rest)
             (let ((bs (items-of (car rest))))
               (resolve-all (cdr rest) (bindings-binders bs env) (resolve-binding-values bs env acc)))
             acc))
        ;; `(let* …)`: each binding sees those before it.
        ((string=? head "let*")
         (if (pair? rest)
             (letrec ((go (subr spin ((listof syn acyclic) binders references) references)
                        (lambda (bs env acc)
                          (if (null? bs)
                              (resolve-all (cdr rest) env acc)
                              (go (cdr bs) (bindings-binders (the syns-a (list (car bs))) env)
                                  (resolve-binding-values (the syns-a (list (car bs))) env acc))))))
               (go (items-of (car rest)) env acc))
             acc))
        ;; `(letrec ((x T e) …) body …)`: every name in scope everywhere.
        ((string=? head "letrec")
         (if (pair? rest)
             (let* ((bs (items-of (car rest))) (inner (bindings-binders bs env)))
               (resolve-all (cdr rest) inner (resolve-binding-values bs inner acc)))
             acc))
        ;; `(letregion r body …)` and its kin: the region named.
        ((member? head (list "letregion" "letrena" "letreap" "letfreeze") string=?)
         (if (pair? rest) (resolve-all (cdr rest) (param-binder (car rest) env) acc) acc))
        ;; `(tagcase e (tag x body) (tag (x y) body) (else y body))`.
        ((string=? head "tagcase")
         (if (pair? rest)
             (letrec ((arms (subr spin ((listof syn acyclic) references) references)
                        (lambda (as acc)
                          (if (null? as) acc
                              (let ((is (items-of (car as))))
                                (arms (cdr as)
                                      (if (and (pair? is) (pair? (cdr is)))
                                          (let ((names (tagcase (car (cdr is))
                                                         (lst (ns d a b) (params-binders ns env))
                                                         (else y (binder-of (car (cdr is)) env)))))
                                            (resolve-all (cdr (cdr is)) names acc))
                                          acc)))))))
               (arms (cdr rest) (resolve-syn (car rest) env acc)))
             acc))
        ;; `(typecase e (shape x body) … (else x body))`.
        ((string=? head "typecase")
         (if (pair? rest)
             (letrec ((arms (subr spin ((listof syn acyclic) references) references)
                        (lambda (as acc)
                          (if (null? as) acc
                              (let ((is (items-of (car as))))
                                (arms (cdr as)
                                      (if (and (pair? is) (pair? (cdr is)))
                                          (resolve-all (cdr (cdr is)) (binder-of (car (cdr is)) env) acc)
                                          acc)))))))
               (arms (cdr rest) (resolve-syn (car rest) env acc)))
             acc))
        ;; `(case key ((datum …) e …) … (else e …))`: the data are not uses.
        ((string=? head "case")
         (if (pair? rest)
             (letrec ((clauses (subr spin ((listof syn acyclic) references) references)
                        (lambda (cs acc)
                          (if (null? cs) acc
                              (let ((is (items-of (car cs))))
                                (clauses (cdr cs) (if (pair? is) (resolve-all (cdr is) env acc) acc)))))))
               (clauses (cdr rest) (resolve-syn (car rest) env acc)))
             acc))
        ;; `(product (label e) …)`: the labels are not uses.
        ((string=? head "product")
         (letrec ((fields (subr spin ((listof syn acyclic) references) references)
                    (lambda (fs acc)
                      (if (null? fs) acc
                          (let ((is (items-of (car fs))))
                            (fields (cdr fs) (if (pair? is) (resolve-all (cdr is) env acc) acc)))))))
           (fields rest acc)))
        ;; `(extract e label)`, `(sum tag e)`: the label and tag are not uses.
        ((string=? head "extract") (if (pair? rest) (resolve-syn (car rest) env acc) acc))
        ((string=? head "sum") (resolve-all (second rest) env acc))
        ;; A definition: its name is a binder, not a use; the rest is walked.
        ((member? head (list "define" "define*" "define-type" "define-effect" "define-generative") string=?)
         (resolve-all (second rest) env acc))
        ((string=? head "define-datatype") acc)
        ((string=? head "define-rec")
         (letrec ((go (subr spin ((listof syn acyclic) references) references)
                    (lambda (bs acc)
                      (if (null? bs) acc
                          (go (cdr bs) (resolve-all (second (items-of (car bs))) env acc))))))
           (go rest acc)))
        ((string=? head "import") (if (pair? rest) (resolve-syn (car rest) env acc) acc))
        ;; A module: its items' names in scope in all its items.
        ((string=? head "module") (resolve-all rest (items-binders rest env) acc))
        ((string=? head "hide") (resolve-all rest env acc))
        ;; Anything else: each item, the head included.
        (else (resolve-all items env acc)))))
  ;; `((x e) …)`'s values, each `e` (the last item: `(x T e)` has a type).
  (resolve-binding-values (->* ((listof syn acyclic) binders references) references)
    (lambda (bs env acc)
      (if (null? bs) acc
          (resolve-binding-values (cdr bs) env (resolve-all (cdr (if (pair? (items-of (car bs))) (items-of (car bs)) (the syns-a (list (car bs)))))
                                                            env acc)))))
  ;; The types of parameters `((x T) …)`, in `env`.
  (resolve-param-types (->* ((listof syn acyclic) binders references) references)
    (lambda (ps env acc)
      (if (null? ps) acc
          (resolve-param-types (cdr ps) env
                               (let ((is (items-of (car ps))))
                                 (if (pair? is) (resolve-all (cdr is) env acc) acc))))))
  (bindings-binders (->* ((listof syn acyclic) binders) binders)
    (lambda (bs env) (if (null? bs) env (bindings-binders (cdr bs) (param-binder (car bs) env))))))

"The references of a text's top-level forms `xs`: each use of a name, and
its binder (-1 if not in the text). The text's definitions are in scope
everywhere in it."
(define* resolve-text (subr spin ((listof syn acyclic)) references)
  (lambda (xs)
    (letrec ((rev (subr pure (references references) references)
               (lambda (l acc) (if (null? l) acc (rev (cdr l) (cons (car l) acc))))))
      (rev (resolve-all xs (items-binders xs nil) nil) nil))))

"The file a module expression loads: the string of the first
`(load-module \"f\")` or `(load-input \"f\")` in it, or \"\"."
(define* loaded-file (subr spin (syn) string)
  (lambda (x)
    (let ((is (items-of x)))
      (if (and (pair? is) (member? (atom-symbol (car is)) (list "load-module" "load-input") string=?)
               (pair? (cdr is)))
          (tagcase (car (cdr is))
            (atom (d a b) (typecase d (string s s) (else y "")))
            (else y ""))
          (letrec ((go (subr spin ((listof syn acyclic)) string)
                     (lambda (xs)
                       (if (null? xs) ""
                           (let ((f (loaded-file (car xs)))) (if (string=? f "") (go (cdr xs)) f))))))
            (go is))))))

"The names a text's top-level `import`s bring in from modules it defines
by loading a file, `(define m (… (load-module \"f\") …))`: each name's
place, and the file."
(define* import-links (subr spin ((listof syn acyclic)) links)
  (lambda (xs)
    (letrec ((modules (subr spin ((listof syn acyclic) (listof (productof (name string) (file string)) acyclic))
                            (listof (productof (name string) (file string)) acyclic))
               (lambda (xs acc)
                 (if (null? xs) acc
                     (let ((is (items-of (car xs))))
                       (modules (cdr xs)
                                (if (and (pair? is) (string=? (atom-symbol (car is)) "define")
                                         (pair? (cdr is)) (pair? (cdr (cdr is))))
                                    (let ((f (loaded-file (car (cdr (cdr is))))))
                                      (if (string=? f "") acc
                                          (cons (product (name (atom-symbol (car (cdr is)))) (file f)) acc)))
                                    acc))))))
             (file-of (subr spin (string (listof (productof (name string) (file string)) acyclic)) string)
               (lambda (m ms) (cond ((null? ms) "")
                                    ((string=? (extract (car ms) name) m) (extract (car ms) file))
                                    (else (file-of m (cdr ms))))))
             (names (subr spin ((listof syn acyclic) string links) links)
               (lambda (xs f acc)
                 (if (null? xs) acc
                     (names (cdr xs) f
                            (tagcase (car xs)
                              (lst (is d a b) (names (if (pair? is) (cdr is) nil) f acc))
                              (atom (d a b)
                                (let ((n (atom-symbol (car xs))))
                                  (if (string=? n "") acc (cons (product (name n) (start a) (end b) (file f)) acc))))
                              (else y acc))))))
             (imports (subr spin ((listof syn acyclic) (listof (productof (name string) (file string)) acyclic) links) links)
               (lambda (xs ms acc)
                 (if (null? xs) acc
                     (let ((is (items-of (car xs))))
                       (imports (cdr xs) ms
                                (if (and (pair? is) (string=? (atom-symbol (car is)) "import") (pair? (cdr is)))
                                    (let ((f (file-of (atom-symbol (car (cdr is))) ms)))
                                      (if (string=? f "") acc (names (cdr (cdr is)) f acc)))
                                    acc)))))))
      (imports xs (modules xs nil) nil))))
