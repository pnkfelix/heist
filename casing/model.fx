;;; model.fx: casing's models, what they mean, and their commands: a
;;; model's forms read into sigs, fields, facts, predicates and commands;
;;; a command's scope made into bounds; its formula translated, state by
;;; state over a lasso of states, into circuits (circuit.fx) over matrices
;;; (matrix.fx); and what the solver finds shown. docs/casing.md says what
;;; the language is and where it follows Alloy 6 (Pardinus) and where not.

(module-parameters ((m-sat (load-moduleof "../combo/sat.fx"))
                    (m-circuit (load-moduleof "circuit.fx" m-sat))
                    (m-matrix (load-moduleof "matrix.fx" m-sat m-circuit))))

;; Macros: each file defines its own, for now (docs/macros.md).
(define-syntax iterate
  (syntax-rules ()
    ((_ go eff ((x t i) ...) r body) (letrec ((go (subr eff (t ...) r) (lambda (x ...) body))) (go i ...)))))
(define-syntax unless (syntax-rules () ((_ c e ...) (if c #u (begin e ...)))))
(hide (define kit-strings (load-module "../kit/strings.fx"))
      (import kit-strings string-join)
      (define kit-numbers (load-module "../kit/numbers.fx"))
      (import kit-numbers lcm))

(define-type datums (listof datum acyclic))
"What the reading of a model does: it may loop, and reads the module's globals."
(define-effect ro (maxeff spin (read @globals)))

;;; ------------------------------------------------------------ data read

(define sym? (subr ro (datum string) bool)
  (lambda (d name) (and (symbol? d) (string=? (symbol->string d) name))))
"A list's head, if a symbol, else \"\"."
(define head (subr ro (datum) string)
  (lambda (d) (if (pair? d) (let ((h (car d))) (if (symbol? h) (symbol->string h) "")) "")))
(define items (subr ro (datum) datums)
  (lambda (d) (if (pair? d) (cons (car d) (items (cdr d))) nil)))
(define name-of (subr ro (datum) string)
  (lambda (d) (if (symbol? d) (symbol->string d) (error (string-append "casing: a name is expected, not " (shown d))))))
(define nth (subr ro (datum int) datum)
  (lambda (d i) (if (pair? d) (if (= i 0) (car d) (nth (cdr d) (- i 1))) (error (string-append "casing: too short: " (shown d))))))
(define len (subr ro (datum) int) (lambda (d) (if (pair? d) (+ 1 (len (cdr d))) 0)))
"A datum written, for messages."
(define shown (subr ro (datum) string)
  (lambda (d)
    (cond ((symbol? d) (symbol->string d))
          ((keyword? d) (string-append "#:" (symbol->string (keyword->symbol d))))
          ((datum-int? d) (int->string d))
          ((bool? d) (if d "#t" "#f"))
          ((null? d) "()")
          ((pair? d) (string-append "(" (string-append (string-join (shown-all (items d)) " ") ")")))
          (else "?"))))
(define shown-all (subr ro (datums) strings)
  (lambda (l) (if (null? l) nil (cons (shown (car l)) (shown-all (cdr l))))))
(define sym (subr ro (string) datum) (lambda (s) (string->symbol s)))
"Whether a name is a region's, `@r`."
(define region-name? (subr ro (string) bool)
  (lambda (n) (and (> (string-length n) 1) (char=? (string-ref n 0) #\@))))
(define region? (subr ro (datum) bool) (lambda (d) (and (symbol? d) (region-name? (name-of d)))))
(define member-string? (subr ro (string strings) bool)
  (lambda (s l) (and (pair? l) (or (string=? s (car l)) (member-string? s (cdr l))))))

;;; ------------------------------------------------------------ models

"A sig: its parent (\"\" if none), whether it is a subset (`in`) of the
parent, rather than a part of it (`extends`); abstract; its multiplicity
(\"set\", \"one\", \"lone\", \"some\"); whether it changes from state to
state, and the region it changes in (\"\" if none); whether it is
totally ordered (`#:ordered`, Alloy's `util/ordering`); its facts
(`#:fact F`: of each atom `this` of it, in every state); whether it is an
`enum`'s (its parts its values, ordered as written)."
(define-type sig-info (productof (name string) (parent string) (subset bool) (abstract bool) (mult string) (var bool) (region string)
                                 (ordered bool) (facts datums) (enum bool)))
"A field of `owner`: the columns after the owner's (expressions, sig
names most often), the multiplicity of the last, whether it changes, and
the region it changes in (\"\" if none)."
(define-type field-info (productof (name string) (owner string) (cols datums) (mult string) (var bool) (region string) (apart bool)))
"A predicate, function or event: its declarations `((x T) …)`, its body;
an event's relations and regions (`@r`) it writes (the rest are unchanged)."
(define-type def-info (productof (name string) (params datums) (body datum) (fun bool) (event bool) (writes strings)))
(define-type named (productof (name string) (body datum)))
(define-type model
  (productof (sigs (listof sig-info acyclic)) (fields (listof field-info acyclic)) (facts datums)
             (defs (listof def-info acyclic)) (asserts (listof named acyclic)) (commands datums)))

(define empty-model model (product (sigs nil) (fields nil) (facts nil) (defs nil) (asserts nil) (commands nil)))

"A field's type `T` or `(-> T U …)`: the multiplicity of its last column
when none is said (`one`, or `set` for an arrow, as in Alloy) and its
columns."
(define field-type (subr ro (datum) (productof (mult string) (cols datums)))
  (lambda (t)
    (cond ((string=? (head t) "->") (product (mult "set") (cols (cdr (items t)))))
          ((and (mult-name? (head t)) (= (len t) 2))
           (error (string-append "casing: a field's multiplicity is an option: write #:" (head t))))
          ((string=? (head t) "col") (error (string-append "casing: a col is an arrow's operand: " (shown t))))
          (else (product (mult "one") (cols (list t)))))))

"An arrow's operand's multiplicity, `(col X #:m)` (Alloy's `X m -> …`), or
\"\" if it says none. `X`'s columns are one group: a multiplicity on an
operand of several columns, `(col (-> B C) #:lone)`, counts its tuples."
(define mark-of (subr ro (datum) string)
  (lambda (d)
    (cond ((string=? (head d) "col")
           (if (< (len d) 2) (error (string-append "casing: a col of what? " (shown d)))
               (iterate go ro ((l datums (cdr (cdr (items d)))) (m string "")) string
                 (if (null? l) m
                     (let ((k (option-name (car l))))
                       (cond ((and (mult-name? k) (string=? m "")) (go (cdr l) k))
                             ((mult-name? k) (error (string-append "casing: two multiplicities in " (shown d))))
                             (else (error (string-append "casing: what is this in a col? " (shown (car l)))))))))))
          ((and (mult-name? (head d)) (= (len d) 2))
           (error (string-append "casing: an arrow's operand says its multiplicity as a col: write (col "
                                 (string-append (shown (nth d 1)) (string-append " #:" (string-append (head d) ")"))))))
          (else ""))))
"An operand without its `col`."
(define unmarked (subr ro (datum) datum) (lambda (d) (if (string=? (head d) "col") (nth d 1) d)))
"Whether `d` is an arrow with a multiplicity on some operand, or within
one: `(-> (col A #:one) (col B #:lone))`, Alloy's `A one -> lone B`."
(define marked-arrow? (subr ro (datum) bool)
  (lambda (d) (and (string=? (head d) "->")
                   (iterate any ro ((l datums (cdr (items d)))) bool
                     (and (pair? l) (or (not (string=? (mark-of (car l)) "")) (marked-arrow? (car l)) (any (cdr l))))))))
"An arrow's columns, one for each column of the relation: nested arrows
flattened, multiplicities dropped."
(define flat-cols (subr ro (datums) datums)
  (lambda (l) (if (null? l) nil
                  (let ((d (unmarked (car l))))
                    (append (if (string=? (head d) "->") (flat-cols (cdr (items d))) (list d)) (flat-cols (cdr l)))))))

"Whether `k` names a multiplicity."
(define mult-name? (subr ro (string) bool)
  (lambda (k) (or (string=? k "one") (string=? k "lone") (string=? k "some") (string=? k "set"))))
"Whether `w` names an option of a sig, a field or an event, which is
written as a keyword, `#:w`; no field may be named so."
(define option-word? (subr ro (string) bool)
  (lambda (w) (or (mult-name? w) (string=? w "abstract") (string=? w "extends") (string=? w "in")
                  (string=? w "var") (string=? w "writes") (string=? w "ordered")
                  (string=? w "fact") (string=? w "disj") (string=? w "apart") (string=? w "col"))))
"A keyword's name, `#:k`; \"\" for anything else."
(define option-name (subr ro (datum) string)
  (lambda (d) (if (keyword? d) (symbol->string (keyword->symbol d)) "")))

"Fields of `owner`, `(f g … T #:m #:var @r #:disj #:apart)`, each of
type `T`: a sig, an expression, or `(-> T U …)`, whose operands may say
their multiplicities, `(-> (col A #:one) (col B #:lone))`; `T` may mention `this`,
the owner. `#:m` is the multiplicity of the last column (`one` if not
said, or `set` for an arrow); `#:var` that they change, in region `@r` if
one follows; `#:disj` that the names are disjoint relations (Alloy's
`disj f, g: T`), as the names of a quantifier's declaration are;
`#:apart` that distinct owners' values are disjoint (Alloy's `f: disj
T`). The fields, and the sig facts `#:disj` gives."
(define-type fields-read (productof (fields (listof field-info acyclic)) (facts datums)))
(define read-field (subr ro (string datum) fields-read)
  (lambda (owner d)
    (letrec ((names (subr ro (datums strings) (productof (names strings) (rest datums)))
               ;; names, up to the type: the last item before the options
               (lambda (l acc)
                 (cond ((null? l) (error (string-append "casing: a field without a type: " (shown d))))
                       ((or (null? (cdr l)) (keyword? (car (cdr l)))) (product (names (reverse acc)) (rest l)))
                       (else (names (cdr l) (cons (let ((n (name-of (car l))))
                                                    (if (option-word? n) (error (string-append "casing: an option is a keyword: write #:" n)) n))
                                                  acc)))))))
      (let* ((nr (names (items d) nil)) (ns (extract nr names)))
        (if (null? ns) (error (string-append "casing: a field without a name: " (shown d))) #u)
        (let ((t (field-type (car (extract nr rest)))))
          (letrec ((go (subr ro (datums string bool bool string bool bool) fields-read)
                     (lambda (os mult said var region disj apart)
                       (if (null? os)
                           (product (fields (iterate each ro ((l strings ns)) (listof field-info acyclic)
                                              (if (null? l) nil
                                                  (cons (product (name (car l)) (owner owner) (cols (extract t cols)) (mult mult)
                                                                 (var var) (region region) (apart apart))
                                                        (each (cdr l))))))
                                    (facts (if (not disj) nil
                                               (if (null? (cdr ns))
                                                   (error (string-append "casing: #:disj makes several fields disjoint; for owners' values apart, write #:apart: " (car ns)))
                                                   ;; each owner's: (no (inter (join this f) (join this g)))
                                                   (iterate pairs ro ((l strings ns)) datums
                                                     (if (null? l) nil
                                                         (append (iterate go ro ((k strings (cdr l))) datums
                                                                   (if (null? k) nil
                                                                       (cons (the datum (list (sym "no") (list (sym "inter") (list (sym "join") (sym "this") (sym (car l)))
                                                                                                                    (list (sym "join") (sym "this") (sym (car k))))))
                                                                             (go (cdr k)))))
                                                                 (pairs (cdr l)))))))))
                           (let ((k (option-name (car os))))
                             (cond ((mult-name? k)
                                    (if said (error (string-append "casing: two multiplicities for field " (car ns)))
                                        (go (cdr os) k #t var region disj apart)))
                                   ((string=? k "var")
                                    (if (and (pair? (cdr os)) (region? (car (cdr os))))
                                        (go (cdr (cdr os)) mult said #t (name-of (car (cdr os))) disj apart)
                                        (go (cdr os) mult said #t "" disj apart)))
                                   ((string=? k "disj") (go (cdr os) mult said var region #t apart))
                                   ((string=? k "apart") (go (cdr os) mult said var region disj #t))
                                   (else (error (string-append "casing: what is this in field " (string-append (car ns) (string-append "? " (shown (car os)))))))))))))
            (go (cdr (extract nr rest)) (extract t mult) #f #f "" #f #f)))))))

"A predicate's, function's or event's options before its body: an
event's `#:writes x` or `#:writes (x …)`, each `x` a relation or a
region `@r`."
(define def-options (subr ro (bool datums) (productof (writes strings) (body datums)))
  (lambda (event xs)
    (letrec ((names (subr ro (datums) strings) (lambda (l) (if (null? l) nil (cons (name-of (car l)) (names (cdr l))))))
             (go (subr ro (datums strings) (productof (writes strings) (body datums)))
               (lambda (l ws)
                 (cond ((null? l) (product (writes ws) (body nil)))
                       ((and event (keyword? (car l)) (string=? (option-name (car l)) "writes") (pair? (cdr l)))
                        (let ((v (car (cdr l))))
                          (go (cdr (cdr l)) (append ws (if (pair? v) (names (items v)) (list (name-of v)))))))
                       ((and (keyword? (car l)) (string=? (option-name (car l)) "writes"))
                        (error "casing: only an event writes; a predicate or function reads"))
                       ((and event (string=? (head (car l)) "writes"))
                        (error "casing: an option is a keyword: write #:writes"))
                       ((keyword? (car l)) (error (string-append "casing: what option is this? " (shown (car l)))))
                       (else (product (writes ws) (body l)))))))
      (go xs nil))))

"A declaration, `(x y T #:m #:disj)`: its names; its type, an expression;
its multiplicity, if said (\"\" if not: `one` for a set, `set` for a
relation, as in Alloy); whether its names are bound to disjoint values."
(define-type decl (productof (names strings) (type datum) (mult string) (disj bool)))
(define read-decl (subr ro (datum) decl)
  (lambda (d)
    (letrec ((go (subr ro (datums strings) decl)
               ;; names, up to the type: the last item before the options
               (lambda (l acc)
                 (cond ((null? l) (error (string-append "casing: a declaration without a type: " (shown d))))
                       ((or (null? (cdr l)) (keyword? (car (cdr l))))
                        (if (null? acc) (error (string-append "casing: a declaration without names: " (shown d)))
                            (options (cdr l) (product (names (reverse acc)) (type (car l)) (mult "") (disj #f)))))
                       (else (go (cdr l) (cons (name-of (car l)) acc))))))
             (options (subr ro (datums decl) decl)
               (lambda (l dc)
                 (if (null? l) dc
                     (let ((k (option-name (car l))))
                       (cond ((mult-name? k)
                              (if (string=? (extract dc mult) "")
                                  (options (cdr l) (product (names (extract dc names)) (type (extract dc type)) (mult k) (disj (extract dc disj))))
                                  (error (string-append "casing: two multiplicities in " (shown d)))))
                             ((string=? k "disj")
                              (options (cdr l) (product (names (extract dc names)) (type (extract dc type)) (mult (extract dc mult)) (disj #t))))
                             (else (error (string-append "casing: what is this in a declaration? " (shown (car l)))))))))))
      (go (items d) nil))))
(define read-decls (subr ro (datums) (listof decl acyclic))
  (lambda (ds) (if (null? ds) nil (cons (read-decl (car ds)) (read-decls (cdr ds))))))
"The names declarations declare, in order."
(define decl-names (subr ro ((listof decl acyclic)) strings)
  (lambda (ds) (if (null? ds) nil (append (extract (car ds) names) (decl-names (cdr ds))))))

"A conjunction of a body's forms."
(define conj (subr ro (datums) datum)
  (lambda (fs) (if (and (pair? fs) (null? (cdr fs))) (car fs) (the datum (cons (sym "and") fs)))))

"One top-level form added to `m`."
(define add-form (subr ro (model datum) model)
  (lambda (m d)
    (let ((h (head d)) (xs (if (pair? d) (cdr (items d)) nil)))
      (cond
        ((string=? h "sig")
         (let ((name (if (string=? (name-of (car xs)) "Int") (error "casing: Int is casing's own: its atoms are integers") (name-of (car xs)))))
           (letrec ((go (subr ro (datums string bool bool string bool string bool datums (listof field-info acyclic)) model)
                      (lambda (os parent subset abstract mult var region ordered sfs fs)
                        (if (null? os)
                            (product (sigs (cons (product (name name) (parent parent) (subset subset) (abstract abstract)
                                                          (mult mult) (var var) (region region) (ordered ordered) (facts (reverse sfs)) (enum #f))
                                                 (extract m sigs)))
                                     (fields (append fs (extract m fields)))
                                     (facts (extract m facts)) (defs (extract m defs)) (asserts (extract m asserts)) (commands (extract m commands)))
                            (let* ((o (car os)) (k (option-name o)))
                              (cond
                                ((string=? k "abstract") (go (cdr os) parent subset #t mult var region ordered sfs fs))
                                ((mult-name? k) (go (cdr os) parent subset abstract k var region ordered sfs fs))
                                ((or (string=? k "extends") (string=? k "in"))
                                 (if (pair? (cdr os))
                                     (go (cdr (cdr os)) (name-of (car (cdr os))) (string=? k "in") abstract mult var region ordered sfs fs)
                                     (error (string-append "casing: whose part is this sig? " name))))
                                ((string=? k "var")                                   ; #:var, or #:var @r
                                 (if (and (pair? (cdr os)) (region? (car (cdr os))))
                                     (go (cdr (cdr os)) parent subset abstract mult #t (name-of (car (cdr os))) ordered sfs fs)
                                     (go (cdr os) parent subset abstract mult #t "" ordered sfs fs)))
                                ((string=? k "fact")                                  ; #:fact F
                                 (if (pair? (cdr os))
                                     (go (cdr (cdr os)) parent subset abstract mult var region ordered (cons (car (cdr os)) sfs) fs)
                                     (error (string-append "casing: a fact of what? " name))))
                                ((string=? k "ordered") (go (cdr os) parent subset abstract mult var region #t sfs fs))
                                ((pair? o) (let ((r (read-field name o)))
                                             (go (cdr os) parent subset abstract mult var region ordered (append (reverse (extract r facts)) sfs)
                                                 (append (reverse (extract r fields)) fs))))
                                (else (error (string-append "casing: what is this in a sig? " (shown o))))))))))
             (go (cdr xs) "" #f #f "set" #f "" #f nil nil))))
        ;; (enum E v …): Alloy's enum, an abstract sig of one part for each
        ;; value, ordered as written (util/ordering, its order fixed)
        ((string=? h "enum")
         (let ((name (name-of (car xs))) (vs (cdr xs)))
           (if (null? vs) (error (string-append "casing: an enum of no values: " name))
               (product (sigs (append (letrec ((go (subr ro (datums) (listof sig-info acyclic))
                                                     (lambda (l) (if (null? l) nil
                                                                     (cons (product (name (name-of (car l))) (parent name) (subset #f) (abstract #f) (mult "one") (var #f)
                                                                                    (region "") (ordered #f) (facts nil) (enum #f))
                                                                           (go (cdr l)))))))
                                        (reverse (go vs)))
                                      (cons (product (name name) (parent "") (subset #f) (abstract #t) (mult "set") (var #f) (region "") (ordered #t)
                                                     (facts nil) (enum #t))
                                            (extract m sigs))))
                        (fields (extract m fields)) (facts (extract m facts)) (defs (extract m defs))
                        (asserts (extract m asserts)) (commands (extract m commands))))))
        ;; (open util/relation), (open util/graph S): a library's definitions
        ((string=? h "open") (open-library m xs))
        ((string=? h "fact")
         (let ((body (if (and (pair? xs) (symbol? (car xs)) (pair? (cdr xs))) (cdr xs) xs)))
           (product (sigs (extract m sigs)) (fields (extract m fields)) (facts (cons (conj body) (extract m facts)))
                    (defs (extract m defs)) (asserts (extract m asserts)) (commands (extract m commands)))))
        ((or (string=? h "pred") (string=? h "fun") (string=? h "event"))
         (let* ((sig (car xs)) (name (name-of (car sig))) (params (cdr (items sig)))
                (event (string=? h "event"))
                (o (def-options event (cdr xs))) (body (extract o body)))
           (product (sigs (extract m sigs)) (fields (extract m fields)) (facts (extract m facts))
                    (defs (cons (product (name name) (params params) (body (if (string=? h "fun") (car body) (conj body)))
                                         (fun (string=? h "fun")) (event event) (writes (extract o writes)))
                                (extract m defs)))
                    (asserts (extract m asserts)) (commands (extract m commands)))))
        ((string=? h "assert")
         (product (sigs (extract m sigs)) (fields (extract m fields)) (facts (extract m facts)) (defs (extract m defs))
                  (asserts (cons (product (name (name-of (car xs))) (body (conj (cdr xs)))) (extract m asserts)))
                  (commands (extract m commands))))
        ((or (string=? h "run") (string=? h "check"))
         (product (sigs (extract m sigs)) (fields (extract m fields)) (facts (extract m facts)) (defs (extract m defs))
                  (asserts (extract m asserts)) (commands (cons d (extract m commands)))))
        (else (error (string-append "casing: not a form of a model: " (shown d))))))))

"A model of forms, in order."
(define read-model (subr ro (datums) model)
  (lambda (ds)
    (letrec ((go (subr ro (datums model) model) (lambda (l m) (if (null? l) m (go (cdr l) (add-form m (car l)))))))
      (let ((m (go ds empty-model)))
        (with-ordering
         (product (sigs (reverse (extract m sigs))) (fields (reverse (extract m fields))) (facts (reverse (extract m facts)))
                  (defs (extract m defs)) (asserts (extract m asserts)) (commands (reverse (extract m commands)))))))))

;;; ------------------------------------------------------------ libraries

"Alloy's `util/relation`, in casing; names in kebab-case."
(define relation-defs datum
  '((fun (dom (r (-> univ univ))) (join r univ))
    (fun (ran (r (-> univ univ))) (join univ r))
    (pred (total (r (-> univ univ)) (s univ #:set)) (all ((x s)) (some (join x r))))
    (pred (functional (r (-> univ univ)) (s univ #:set)) (all ((x s)) (lone (join x r))))
    (pred (function (r (-> univ univ)) (s univ #:set)) (all ((x s)) (one (join x r))))
    (pred (surjective (r (-> univ univ)) (s univ #:set)) (all ((x s)) (some (join r x))))
    (pred (injective (r (-> univ univ)) (s univ #:set)) (all ((x s)) (lone (join r x))))
    (pred (bijective (r (-> univ univ)) (s univ #:set)) (all ((x s)) (one (join r x))))
    (pred (bijection (r (-> univ univ)) (d c univ #:set)) (and (function r d) (bijective r c)))
    (pred (reflexive (r (-> univ univ)) (s univ #:set)) (in (<: s iden) r))
    (pred (irreflexive (r (-> univ univ))) (no (inter iden r)))
    (pred (symmetric (r (-> univ univ))) (in (~ r) r))
    (pred (antisymmetric (r (-> univ univ))) (in (inter (~ r) r) iden))
    (pred (transitive (r (-> univ univ))) (in (join r r) r))
    (pred (acyclic (r (-> univ univ)) (s univ #:set)) (all ((x s)) (not (in x (join x (^ r))))))
    (pred (complete (r (-> univ univ)) (s univ #:set)) (all ((x y s)) (implies (!= x y) (in (-> x y) (union r (~ r))))))
    (pred (preorder (r (-> univ univ)) (s univ #:set)) (and (reflexive r s) (transitive r)))
    (pred (equivalence (r (-> univ univ)) (s univ #:set)) (and (preorder r s) (symmetric r)))
    (pred (partial-order (r (-> univ univ)) (s univ #:set)) (and (preorder r s) (antisymmetric r)))
    (pred (total-order (r (-> univ univ)) (s univ #:set)) (and (partial-order r s) (complete r s)))))

"Alloy's `util/graph[node]`, in casing: `node` is the sig it is opened
on; `util/relation`'s definitions it uses are `relation/…`, as Alloy's
opens it `as rel`."
(define graph-defs datum
  '((pred (undirected (r (-> node node))) (relation/symmetric r))
    (pred (no-self-loops (r (-> node node))) (relation/irreflexive r))
    (pred (weakly-connected (r (-> node node))) (all ((n1 n2 node)) (in n1 (join n2 (* (union r (~ r)))))))
    (pred (strongly-connected (r (-> node node))) (all ((n1 n2 node)) (in n1 (join n2 (* r)))))
    (pred (rooted-at (r (-> node node)) (root node)) (in node (join root (* r))))
    (pred (ring (r (-> node node))) (all ((n node)) (and (one (join n r)) (rooted-at r n))))
    (pred (dag (r (-> node node))) (relation/acyclic r node))
    (pred (forest (r (-> node node))) (and (dag r) (all ((n node)) (lone (join r n)))))
    (pred (tree (r (-> node node))) (and (forest r) (lone ((root node)) (no (join r root)))))
    (pred (tree-rooted-at (r (-> node node)) (root node)) (and (forest r) (rooted-at r root)))
    (fun (roots (r (-> node node))) (diff node (join node (^ r))))
    (fun (leaves (r (-> node node))) (diff node (join node (^ (~ r)))))
    (fun (inner-nodes (r (-> node node))) (diff node (leaves r)))))

"`d` with each symbol named in `subst` replaced."
(define substituted (subr ro (datum (listof named acyclic)) datum)
  (lambda (d subst)
    (cond ((symbol? d)
           (iterate go ro ((l (listof named acyclic) subst)) datum
             (cond ((null? l) d) ((string=? (extract (car l) name) (symbol->string d)) (extract (car l) body)) (else (go (cdr l))))))
          ((pair? d) (the datum (cons (substituted (car d) subst) (substituted (cdr d) subst))))
          (else d))))

"A library's definitions, `lib`, renamed `prefix` + name (and with
`subst`), added after the model's own, which therefore win."
(define with-library (subr ro (model datums string (listof named acyclic)) model)
  (lambda (m lib prefix subst)
    (letrec ((renames (subr ro (datums) (listof named acyclic))       ; each definition's name, prefixed
               (lambda (l) (if (null? l) subst
                               (let ((nm (name-of (car (items (nth (car l) 1))))))
                                 (cons (product (name nm) (body (sym (string-append prefix nm)))) (renames (cdr l)))))))
             (defs (subr ro (datums (listof named acyclic) (listof def-info acyclic)) (listof def-info acyclic))
               (lambda (l sub acc)
                 (if (null? l) acc
                     (defs (cdr l) sub
                           (append acc (extract (add-form empty-model (substituted (car l) sub)) defs)))))))
      (product (sigs (extract m sigs)) (fields (extract m fields)) (facts (extract m facts))
               (defs (defs lib (if (string=? prefix "") subst (renames lib)) (extract m defs)))
               (asserts (extract m asserts)) (commands (extract m commands))))))

"(open util/relation [#:as a]), (open util/graph S [#:as a]): the
library's definitions, named `a/name` if `#:as a`."
(define open-library (subr ro (model datums) model)
  (lambda (m xs)
    (let* ((lib (name-of (car xs)))
           (rest (cdr xs))
           (as (iterate go ro ((l datums rest)) string
                 (cond ((null? l) "")
                       ((and (string=? (option-name (car l)) "as") (pair? (cdr l))) (string-append (name-of (car (cdr l))) "/"))
                       (else (go (cdr l))))))
           (args (iterate go ro ((l datums rest)) datums
                   (cond ((null? l) nil) ((keyword? (car l)) nil) (else (cons (car l) (go (cdr l)))))))
           (opened? (lambda ((nm string)) (tagcase (find-def m (string-append as nm)) (some f #t) (none u #f)))))
      (cond ((string=? lib "util/relation")
             (if (opened? "dom") (error "casing: util/relation is open already; open it again #:as another name")
                 (with-library m (items relation-defs) as nil)))
            ((string=? lib "util/graph")
             (cond ((not (= (list-length args) 1)) (error "casing: (open util/graph S): a graph of which sig?"))
                   ((opened? "dag") (error "casing: util/graph is open already; open it again #:as another name"))
                   (else
                    (let ((m2 (if (tagcase (find-def m "relation/dom") (some f #t) (none u #f)) m
                                  (with-library m (items relation-defs) "relation/" nil))))
                      (with-library m2 (items graph-defs) as (list (product (name "node") (body (car args)))))))))
            (else (error (string-append "casing: no library " (string-append lib "; casing has util/relation and util/graph (and #:ordered for util/ordering)"))))))))

;;; ------------------------------------------------------------ util/ordering

"The sigs a model orders."
(define ordered-sigs (subr ro (model) (listof sig-info acyclic))
  (lambda (m) (iterate go ro ((l (listof sig-info acyclic) (extract m sigs))) (listof sig-info acyclic)
                (cond ((null? l) nil) ((extract (car l) ordered) (cons (car l) (go (cdr l)))) (else (go (cdr l)))))))

"Alloy's `util/ordering`, for every ordered sig at once (their atoms are
apart, each being top-level): `next`, a relation, each ordered sig's
atoms in a line; and the rest of the module's functions and predicates,
over `next`. `first` and `last` take the sig. A model's own definition
of one of these names wins."
(define ordering-defs datum
  '((fun (prev) (~ next))
    (fun (first (s univ #:set)) (diff s (join s next)))
    (fun (last (s univ #:set)) (diff s (join next s)))
    (fun (nexts (e univ #:set)) (join e (^ next)))
    (fun (prevs (e univ #:set)) (join e (^ (~ next))))
    (pred (lt (a b univ)) (in a (prevs b)))
    (pred (gt (a b univ)) (in a (nexts b)))
    (pred (lte (a b univ)) (or (= a b) (lt a b)))
    (pred (gte (a b univ)) (or (= a b) (gt a b)))
    (fun (larger (a b univ)) (if (lt a b) b a))
    (fun (smaller (a b univ)) (if (lt a b) a b))
    (fun (max (es univ #:set)) (diff es (join es (^ (~ next)))))
    (fun (min (es univ #:set)) (diff es (join es (^ next))))))

"Whether casing fixes ordered sig `g`'s `next` to its atoms' order, S$0,
S$1, …: an enum's, which is its values' as written (Alloy fixes it so);
and when its atoms are interchangeable, as Kodkod's symmetry breaking
does: no `one` part of it has an atom of its own."
(define order-fixed? (subr ro (model sig-info) bool)
  (lambda (m o)
    (letrec ((under? (subr ro (string string) bool)        ; whether sig a is a part of sig b, or below one
               (lambda (a b) (tagcase (find-sig m a)
                               (none u #f)
                               (some g (and (not (extract g subset)) (not (string=? (extract g parent) ""))
                                            (or (string=? (extract g parent) b) (under? (extract g parent) b)))))))
             (any (subr ro (string (listof sig-info acyclic)) bool)
               (lambda (a os) (and (pair? os) (or (under? a (extract (car os) name)) (any a (cdr os))))))
             (go (subr ro ((listof sig-info acyclic)) bool)
               (lambda (l) (or (null? l)
                               (and (not (and (string=? (extract (car l) mult) "one") (not (extract (car l) subset))
                                              (any (extract (car l) name) (list o))))
                                    (go (cdr l)))))))
      (or (extract o enum) (go (extract m sigs))))))

"`m` with its ordering, if it orders any sig: the relation `next`, the
module's definitions, and, unless the order is fixed, the facts that
make `next` a total order of each ordered sig."
(define with-ordering (subr ro (model) model)
  (lambda (m)
    (let ((os (ordered-sigs m)))
      (if (null? os) m
          (letrec ((check (subr ro ((listof sig-info acyclic)) bool)
                     (lambda (l) (or (null? l)
                                     (cond ((not (string=? (extract (car l) parent) ""))
                                            (error (string-append "casing: an ordered sig is top-level: " (extract (car l) name))))
                                           ((extract (car l) var)
                                            (error (string-append "casing: an ordered sig does not change: " (extract (car l) name))))
                                           (else (check (cdr l)))))))
                   (field? (subr ro ((listof field-info acyclic)) bool)
                     (lambda (l) (and (pair? l) (or (string=? (extract (car l) name) "next") (field? (cdr l))))))
                   (defs (subr ro (datums (listof def-info acyclic)) (listof def-info acyclic))
                     (lambda (l acc)
                       (if (null? l) acc
                           (let ((nm (name-of (car (items (nth (car l) 1))))))
                             (defs (cdr l) (tagcase (find-def m nm)
                                             (some f acc)
                                             (none u (extract (add-form (product (sigs nil) (fields nil) (facts nil) (defs acc) (asserts nil) (commands nil))
                                                                        (car l))
                                                              defs))))))))
                   (orders (subr ro ((listof sig-info acyclic)) datums)
                     ;; each ordered sig whose order is not fixed: next within it, from its first through all
                     (lambda (l)
                       (if (null? l) nil
                           (let ((s (sym (extract (car l) name))))
                            (if (order-fixed? m (car l)) (orders (cdr l))
                             (append (list (the datum (list (sym "in") (list (sym "join") s (sym "next")) s))
                                           (the datum (list (sym "lone") (list (sym "first") s)))
                                           (the datum (list (sym "in") s (list (sym "join") (list (sym "first") s) (list (sym "*") (sym "next"))))))
                                     (orders (cdr l)))))))))
            (if (and (check os) (not (field? (extract m fields))))
                (product (sigs (extract m sigs))
                         (fields (append (extract m fields)
                                         (list (product (name "next") (owner "") (cols (list (sym "univ") (sym "univ"))) (mult "set") (var #f) (region "") (apart #f)))))
                         (facts (let ((fs (orders os)))
                                  (if (null? fs) (extract m facts)
                                      (append (extract m facts)
                                              (append (list (the datum '(all ((b univ)) (and (lone (join b next)) (lone (join next b)))))
                                                            (the datum '(no (inter (^ next) iden))))
                                                      fs)))))
                         (defs (defs (items ordering-defs) (extract m defs)))
                         (asserts (extract m asserts)) (commands (extract m commands)))
                (error "casing: a model that orders a sig has no field named next")))))))


(define find-sig (subr ro (model string) (sumof (none unit) (some sig-info)))
  (lambda (m n) (iterate go ro ((l (listof sig-info acyclic) (extract m sigs))) (sumof (none unit) (some sig-info))
                  (cond ((null? l) (sum none #u)) ((string=? (extract (car l) name) n) (sum some (car l))) (else (go (cdr l)))))))
(define find-def (subr ro (model string) (sumof (none unit) (some def-info)))
  (lambda (m n) (iterate go ro ((l (listof def-info acyclic) (extract m defs))) (sumof (none unit) (some def-info))
                  (cond ((null? l) (sum none #u)) ((string=? (extract (car l) name) n) (sum some (car l))) (else (go (cdr l)))))))
(define any-var? (subr ro (model) bool)
  (lambda (m) (or (iterate go ro ((l (listof sig-info acyclic) (extract m sigs))) bool
                    (and (pair? l) (or (extract (car l) var) (go (cdr l)))))
                  (iterate go ro ((l (listof field-info acyclic) (extract m fields))) bool
                    (and (pair? l) (or (extract (car l) var) (go (cdr l))))))))
"The names of the relations that change."
(define var-names (subr ro (model) strings)
  (lambda (m) (append (iterate go ro ((l (listof sig-info acyclic) (extract m sigs))) strings
                        (cond ((null? l) nil) ((extract (car l) var) (cons (extract (car l) name) (go (cdr l)))) (else (go (cdr l)))))
                      (iterate go ro ((l (listof field-info acyclic) (extract m fields))) strings
                        (cond ((null? l) nil) ((extract (car l) var) (cons (extract (car l) name) (go (cdr l)))) (else (go (cdr l))))))))

"The names of the relations that change in region `r`."
(define region-names (subr ro (model string) strings)
  (lambda (m r) (append (iterate go ro ((l (listof sig-info acyclic) (extract m sigs))) strings
                          (cond ((null? l) nil) ((string=? (extract (car l) region) r) (cons (extract (car l) name) (go (cdr l)))) (else (go (cdr l)))))
                        (iterate go ro ((l (listof field-info acyclic) (extract m fields))) strings
                          (cond ((null? l) nil) ((string=? (extract (car l) region) r) (cons (extract (car l) name) (go (cdr l)))) (else (go (cdr l))))))))
"The relations an event's `writes` names: a relation that changes names
itself, and a region `@r` every relation that changes in it."
(define written (subr ro (model strings) strings)
  (lambda (m ns)
    (if (null? ns) nil
        (let ((n (car ns)) (rest (written m (cdr ns))))
          (cond ((region-name? n)
                 (let ((rs (region-names m n)))
                   (if (null? rs) (error (string-append "casing: no relation changes in region " n)) (append rs rest))))
                ((member-string? n (var-names m)) (cons n rest))
                (else (error (string-append "casing: written, but it does not change: " n))))))))

;;; ------------------------------------------------------------ scopes and bounds

"A command's scope: the default, each sig's (and whether exactly), and
the steps of a trace, at least and at most."
(define-type scope-entry (productof (name string) (count int) (exact bool)))
(define-type scope (productof (default int) (sigs (listof scope-entry acyclic)) (min-steps int) (max-steps int)))

(define read-scope (subr ro (model datums) scope)
  (lambda (m specs)
    (iterate go ro ((l datums specs) (s scope (product (default 3) (sigs nil) (min-steps 1) (max-steps (if (any-var? m) 10 1))))) scope
      (if (null? l) s
          (let ((d (car l)) (rest (cdr l)))
            (cond ((datum-int? d) (go rest (product (default d) (sigs (extract s sigs)) (min-steps (extract s min-steps)) (max-steps (extract s max-steps)))))
                  ((string=? (head d) "steps")
                   (let ((a (nth d 1)) (b (if (= (len d) 3) (nth d 2) (nth d 1))))
                     (if (and (datum-int? a) (datum-int? b))
                         (go rest (product (default (extract s default)) (sigs (extract s sigs)) (min-steps (if (= (len d) 3) a 1)) (max-steps b)))
                         (error "casing: (steps N) or (steps MIN MAX)"))))
                  ((string=? (head d) "exactly")
                   (let ((c (nth d 2)))
                     (if (datum-int? c)
                         (go rest (product (default (extract s default)) (sigs (cons (product (name (name-of (nth d 1))) (count c) (exact #t)) (extract s sigs)))
                                           (min-steps (extract s min-steps)) (max-steps (extract s max-steps))))
                         (error "casing: (exactly SIG N)"))))
                  ((and (pair? d) (symbol? (car d)))
                   (let ((c (nth d 1)))
                     (if (datum-int? c)
                         (go rest (product (default (extract s default)) (sigs (cons (product (name (name-of (car d))) (count c) (exact #f)) (extract s sigs)))
                                           (min-steps (extract s min-steps)) (max-steps (extract s max-steps))))
                         (error "casing: (SIG N)"))))
                  (else (error (string-append "casing: not a scope: " (shown d))))))))))

(define scope-of (subr ro (scope string) (sumof (none unit) (some scope-entry)))
  (lambda (s n) (iterate go ro ((l (listof scope-entry acyclic) (extract s sigs))) (sumof (none unit) (some scope-entry))
                  (cond ((null? l) (sum none #u)) ((string=? (extract (car l) name) n) (sum some (car l))) (else (go (cdr l)))))))

"A sig's atoms: those it may have (upper), those it must (lower)."
(define-type sig-bound (productof (name string) (lower ints) (upper ints)))
(define-type universe (productof (names strings) (bounds (listof sig-bound acyclic)) (facts datums)))

(define bound-of (subr ro (universe string) (sumof (none unit) (some sig-bound)))
  (lambda (u n) (iterate go ro ((l (listof sig-bound acyclic) (extract u bounds))) (sumof (none unit) (some sig-bound))
                  (cond ((null? l) (sum none #u)) ((string=? (extract (car l) name) n) (sum some (car l))) (else (go (cdr l)))))))
(define ints-minus (subr ro (ints ints) ints)
  (lambda (a b) (cond ((null? a) nil) ((iterate in? ro ((l ints b)) bool (and (pair? l) (or (= (car l) (car a)) (in? (cdr l)))))
                       (ints-minus (cdr a) b))
                      (else (cons (car a) (ints-minus (cdr a) b))))))
(define range (subr ro (int int) ints) (lambda (from to) (if (>= from to) nil (cons from (range (+ from 1) to)))))

"The universe a scope gives: each top-level sig's atoms, named after it;
a `one` sig extending another gets one of its parent's, its own; other
children may have any of what is left. And the facts the bounds alone do
not say: a scope smaller than the atoms a sig may have."
(define make-universe (subr ro (model scope) universe)
  (lambda (m s)
    (letrec ((count-for (subr ro (sig-info) int)
               (lambda (g) (cond ((or (string=? (extract g mult) "one") (string=? (extract g mult) "lone")) 1)
                                 ((extract g enum) (list-length (children (extract g name) (extract m sigs))))
                                 (else (tagcase (scope-of s (extract g name)) (none u (extract s default)) (some e (extract e count)))))))
             (exact? (subr ro (sig-info) bool)
               ;; a top-level sig that is one, or ordered (Alloy's util/ordering[exactly elem]), or said exactly
               (lambda (g) (or (and (or (string=? (extract g mult) "one") (extract g ordered)) (string=? (extract g parent) ""))
                               (tagcase (scope-of s (extract g name)) (none u #f) (some e (and (extract e exact) (string=? (extract g parent) "")))))))
             (children (subr ro (string (listof sig-info acyclic)) (listof sig-info acyclic))
               (lambda (p l) (cond ((null? l) nil) ((string=? (extract (car l) parent) p) (cons (car l) (children p (cdr l)))) (else (children p (cdr l))))))
             ;; a sig's children placed in atoms `avail`, and theirs
             (place (subr ro (sig-info ints strings (listof sig-bound acyclic) datums) universe)
               (lambda (p avail names bounds facts)
                 (letrec ((ones (subr ro ((listof sig-info acyclic) ints strings (listof sig-bound acyclic) datums) universe)
                            ;; `one` parts first, an atom each, named after them
                            (lambda (cs avail names bounds facts)
                              (cond ((null? cs) (rest (children (extract p name) (extract m sigs)) avail names bounds facts))
                                    ((and (string=? (extract (car cs) mult) "one") (not (extract (car cs) subset)) (pair? avail))
                                     (let* ((a (car avail)) (g (car cs))
                                            (names (set-name names a (string-append (extract g name) "$0"))))
                                       (let ((u (place g (list a) names (cons (product (name (extract g name)) (lower (list a)) (upper (list a))) bounds) facts)))
                                         (ones (cdr cs) (cdr avail) (extract u names) (extract u bounds) (extract u facts)))))
                                    (else (ones (cdr cs) avail names bounds facts)))))
                          (rest (subr ro ((listof sig-info acyclic) ints strings (listof sig-bound acyclic) datums) universe)
                            (lambda (cs avail names bounds facts)
                              (cond ((null? cs) (product (names names) (bounds bounds) (facts facts)))
                                    ((and (string=? (extract (car cs) mult) "one") (not (extract (car cs) subset))) (rest (cdr cs) avail names bounds facts))
                                    (else
                                     (let* ((g (car cs))
                                            (up (if (extract g subset)
                                                    (tagcase (bound-of (product (names names) (bounds bounds) (facts facts)) (extract g parent)) (none u avail) (some b (extract b upper)))
                                                    avail))
                                            (facts (tagcase (scope-of s (extract g name))
                                                     (none u facts)
                                                     (some e (cons (the datum (list (sym (if (extract e exact) "=" "<=")) (list (sym "size") (sym (extract g name))) (extract e count))) facts))))
                                            (u (place g up names (cons (product (name (extract g name)) (lower nil) (upper up)) bounds) facts)))
                                       (rest (cdr cs) avail (extract u names) (extract u bounds) (extract u facts)))))))
                          (set-name (subr ro (strings int string) strings)
                            (lambda (l i x) (cond ((null? l) nil) ((= i 0) (cons x (cdr l))) (else (cons (car l) (set-name (cdr l) (- i 1) x)))))))
                   (ones (children (extract p name) (extract m sigs)) (ints-minus avail nil) names bounds facts))))
             (tops (subr ro ((listof sig-info acyclic) strings (listof sig-bound acyclic) datums) universe)
               (lambda (l names bounds facts)
                 (cond ((null? l) (product (names names) (bounds bounds) (facts facts)))
                       ((not (string=? (extract (car l) parent) "")) (tops (cdr l) names bounds facts))
                       (else
                        (let* ((g (car l)) (k (count-for g)) (base (list-length names))
                               (atoms (range base (+ base k)))
                               (names (append names (iterate nm ro ((i int 0)) strings
                                                      (if (>= i k) nil (cons (string-append (extract g name) (string-append "$" (int->string i))) (nm (+ i 1)))))))
                               (u (place g atoms names (cons (product (name (extract g name)) (lower (if (exact? g) atoms nil)) (upper atoms)) bounds) facts)))
                          (tops (cdr l) (extract u names) (extract u bounds) (extract u facts))))))))
      (tops (extract m sigs) nil nil nil))))

"`u` with Int's atoms, of bitwidth `bw`, after the sigs': -2^(bw-1) up to
2^(bw-1)-1, each named by its value; Int bound to them all. Alloy's univ
always has them; casing's only when a model mentions Int (or its scope
does), as a relation's matrix has a cell for each tuple of atoms."
(define with-int-atoms (subr ro (universe int) universe)
  (lambda (u bw)
    (let* ((base (list-length (extract u names))) (k (power 2 bw)) (lo (- 0 (quotient k 2))) (atoms (range base (+ base k))))
      (product (names (append (extract u names)
                              (iterate go ro ((l ints (range lo (+ lo k)))) strings
                                (if (null? l) nil (cons (int->string (car l)) (go (cdr l)))))))
               (bounds (cons (product (name "Int") (lower atoms) (upper atoms)) (extract u bounds)))
               (facts (extract u facts))))))

"Whether a model mentions the name `n`: in its declarations, facts,
definitions or assertions."
(define model-mentions? (subr ro (model string) bool)
  (lambda (m n)
    (letrec ((any (subr ro (datums) bool) (lambda (l) (and (pair? l) (or (mentions? (car l) n) (any (cdr l)))))))
      (or (iterate go ro ((l (listof sig-info acyclic) (extract m sigs))) bool
            (and (pair? l) (or (any (extract (car l) facts)) (go (cdr l)))))
          (iterate go ro ((l (listof field-info acyclic) (extract m fields))) bool
            (and (pair? l) (or (any (extract (car l) cols)) (go (cdr l)))))
          (any (extract m facts))
          (iterate go ro ((l (listof def-info acyclic) (extract m defs))) bool
            (and (pair? l) (or (any (extract (car l) params)) (mentions? (extract (car l) body) n) (go (cdr l)))))
          (iterate go ro ((l (listof named acyclic) (extract m asserts))) bool
            (and (pair? l) (or (mentions? (extract (car l) body) n) (go (cdr l)))))))))

;;; ------------------------------------------------------------ translation

"A relation of the problem: its matrix in each state (one, if it does
not change)."
(define-type rel (productof (name string) (arity int) (var bool) (mats (arrayof matrix @cb))))
"A problem: its circuit, atoms, states, unrolls of the loop, the loop's
inputs (one each state it may go back to), relations, model and atoms'
names. Formulas are evaluated at positions of the trace, p = j·k + s:
state s in copy j of the states. Copy 0 is the trace from its start;
copy 1 on, the loop again, so its states from the loop's; the loop goes
back from the last copy's last state. A past formula nested d deep needs
d+1 copies to say at copy d what it says at every later pass
(Pardinus's unrolling; Latvala et al., \"Simple is better\", 2005).
The bitwidth of Int's atoms, and the first of them (-1 if none). And the
polarity of the formula being translated: 1 if it stands
positively in what is asserted, -1 negatively, 0 both or not known; an
existential quantifier where it stands may be skolemized (`ground`).
Whether the formula is at the top of what is asserted: not under a
universal, a temporal operator, or `one`/`lone`, so translated once; the
sets an existential there is skolemized to are its witnesses, shown with
what is found (as Alloy shows its skolems, `$x`)."
(define-type witness (productof (name string) (val matrix)))
(define-type ctx (productof (c circuit) (n int) (k int) (u int) (loops ivec) (rels (listof rel acyclic)) (model model) (universe universe)
                           (pol int) (bw int) (ibase int) (top bool) (witnesses (arrayof (listof witness acyclic) @cb))))
(define ctx-with (subr ro (ctx int bool) ctx)
  (lambda (x p top)
    (if (and (= p (extract x pol)) (eq? top (extract x top))) x
        (product (c (extract x c)) (n (extract x n)) (k (extract x k)) (u (extract x u)) (loops (extract x loops)) (rels (extract x rels))
                 (model (extract x model)) (universe (extract x universe)) (pol p) (bw (extract x bw)) (ibase (extract x ibase))
                 (top top) (witnesses (extract x witnesses))))))
(define with-pol (subr ro (ctx int) ctx) (lambda (x p) (ctx-with x p (extract x top))))
"`x` below the top."
(define inner (subr ro (ctx) ctx) (lambda (x) (ctx-with x (extract x pol) #f)))
(define temporal-ops strings
  (list "after" "then" "always" "eventually" "until" "releases" "before" "once" "historically" "since" "triggered"))
"`x` with its polarity reversed, and neither."
(define flipped (subr ro (ctx) ctx) (lambda (x) (with-pol x (- 0 (extract x pol)))))
(define neutral (subr ro (ctx) ctx) (lambda (x) (with-pol x 0)))

"What a name is bound to: a value now, or an expression evaluated where
it is used (a predicate's argument, a `let`'s), in its own scope."
(define-type binding (productof (name string) (now bool) (val matrix) (code datum) (scope env)))
(define-type env (listof binding acyclic))

(define bind-now (subr ro (string matrix env) env)
  (lambda (n v e) (cons (product (name n) (now #t) (val v) (code (the datum #f)) (scope nil)) e)))
(define lookup (subr ro (env string) (sumof (none unit) (some binding)))
  (lambda (e n) (cond ((null? e) (sum none #u)) ((string=? (extract (car e) name) n) (sum some (car e))) (else (lookup (cdr e) n)))))
(define find-rel (subr ro (ctx string) (sumof (none unit) (some rel)))
  (lambda (x n) (iterate go ro ((l (listof rel acyclic) (extract x rels))) (sumof (none unit) (some rel))
                  (cond ((null? l) (sum none #u)) ((string=? (extract (car l) name) n) (sum some (car l))) (else (go (cdr l)))))))
(define rel-at (subr (read @cb) (rel int) matrix)
  (lambda (r i) (array-ref (extract r mats) (if (extract r var) i 0))))
"A relation at position p: as in its state."
(define rel-at-pos (subr cb-eff (ctx rel int) matrix)
  (lambda (x r p) (rel-at r (modulo p (extract x k)))))

(define cx (subr ro (ctx) circuit) (lambda (x) (extract x c)))
(define loop-at (subr (read @cb) (ctx int) int) (lambda (x l) (array-ref (extract x loops) l)))
"The positions of a trace from p on, in order, if the loop goes back to
state l: the rest of p's copy, the later copies from l, and, from the
last copy, its states from l up to p."
(define future-seq (subr cb-eff (ctx int int) ints)
  (lambda (x p l)
    (let* ((k (extract x k)) (u (extract x u)) (j (quotient p k)) (s (modulo p k)))
      (append (range p (+ (* j k) k))
              (append (iterate go cb-eff ((c int (+ j 1))) ints
                        (if (>= c u) nil (append (range (+ (* c k) l) (+ (* c k) k)) (go (+ c 1)))))
                      (if (= j (- u 1)) (range (+ (* j k) l) p) nil))))))
"The positions of a trace up to p, in order, if the loop goes back to l
(none if p is not on that trace)."
(define past-seq (subr cb-eff (ctx int int) ints)
  (lambda (x p l)
    (let* ((k (extract x k)) (j (quotient p k)) (s (modulo p k)))
      (cond ((= j 0) (range 0 (+ s 1)))
            ((< s l) nil)
            (else (append (range 0 k)
                          (append (iterate go cb-eff ((c int 1)) ints
                                    (if (>= c j) nil (append (range (+ (* c k) l) (+ (* c k) k)) (go (+ c 1)))))
                                  (range (+ (* j k) l) (+ p 1)))))))))
"g's for the loop there is."
(define per-loop (subr cb-eff (ctx (subr cb-eff (int) int)) int)
  (lambda (x g)
    (c-or (cx x) (iterate go cb-eff ((l int 0) (acc ints nil)) ints
                   (if (>= l (extract x k)) acc (go (+ l 1) (cons (c-and2 (cx x) (loop-at x l) (g l)) acc)))))))
(define each-form (subr cb-eff ((subr cb-eff (int) int) ints) ints)
  (lambda (f ps) (if (null? ps) nil (cons (f (car ps)) (each-form f (cdr ps))))))

"The position after p: the next, or, from a copy's last state, the loop's
state in the next copy (the last copy's own, from the last)."
(define after-form (subr cb-eff (ctx int (subr cb-eff (int) int)) int)
  (lambda (x p f)
    (let* ((k (extract x k)) (j (quotient p k)) (s (modulo p k)) (j2 (min (+ j 1) (- (extract x u) 1))))
      (if (< s (- k 1)) (f (+ p 1))
          (per-loop x (lambda ((l int)) (f (+ (* j2 k) l))))))))
(define after-expr (subr cb-eff (ctx int (subr cb-eff (int) matrix)) matrix)
  (lambda (x p f)
    (let* ((k (extract x k)) (j (quotient p k)) (s (modulo p k)) (j2 (min (+ j 1) (- (extract x u) 1))))
      (if (< s (- k 1)) (f (+ p 1))
          (iterate go cb-eff ((l int (- k 2)) (acc matrix (f (+ (* j2 k) (- k 1))))) matrix
            (if (< l 0) acc (go (- l 1) (m-ite (cx x) (loop-at x l) (f (+ (* j2 k) l)) acc))))))))

"f until g along positions ps: g somewhere, f at every position before."
(define until-along (subr cb-eff (circuit (subr cb-eff (int) int) (subr cb-eff (int) int) ints) int)
  (lambda (c f g ps)
    (letrec ((go (subr cb-eff (ints int ints) ints)
               (lambda (l before acc)
                 (if (null? l) acc
                     (go (cdr l) (c-and2 c before (f (car l))) (cons (c-and2 c before (g (car l))) acc))))))
      (c-or c (go ps c-true nil)))))

(define arity-error (subr ro (datum string) void)
  (lambda (d why) (error (string-append "casing: " (string-append why (string-append ": " (shown d)))))))

"Expression `d` in state `i`."
(define expr (subr cb-eff (ctx datum int env) matrix)
  (lambda (x d i e)
    (let ((c (cx x)) (n (extract x n)))
      (if (or (datum-int? d) (int-op? d))
          (int-set x (ival x d i e))                    ; an integer where a set is expected: its atom
      (if (symbol? d)
          (let ((s (symbol->string d)))
            (tagcase (lookup e s)
              (some b (if (extract b now) (extract b val) (expr x (extract b code) i (extract b scope))))
              (none u
                (tagcase (find-rel x s)
                  (some r (rel-at-pos x r i))
                  (none u
                    (cond ((string=? s "univ") (m-univ n))
                          ((string=? s "iden") (m-iden n))
                          ((string=? s "none") (m-none n 1))
                          (else (tagcase (find-def (extract x model) s)
                                  (some f (if (and (extract f fun) (null? (extract f params))) (expr x (extract f body) i nil)
                                              (arity-error d "not a relation")))
                                  (none u (arity-error d "unknown name"))))))))))
          (let* ((h (head d)) (args (if (pair? d) (cdr (items d)) nil)))
            (letrec ((all (subr cb-eff (datums) (listof matrix acyclic))
                       (lambda (l) (if (null? l) nil (cons (expr x (car l) i e) (all (cdr l))))))
                     (fold (subr cb-eff ((subr cb-eff (matrix matrix) matrix) (listof matrix acyclic)) matrix)
                       (lambda (f ms) (letrec ((go (subr cb-eff (matrix (listof matrix acyclic)) matrix)
                                                 (lambda (a l) (if (null? l) a (go (f a (car l)) (cdr l))))))
                                        (if (null? ms) (arity-error d "no operands") (go (car ms) (cdr ms))))))
                     (same (subr cb-eff ((subr cb-eff (matrix matrix) matrix)) matrix)
                       (lambda (f) (fold (lambda ((a matrix) (b matrix))
                                           (if (= (m-arity a) (m-arity b)) (f a b) (arity-error d "operands of different arities")))
                                         (all args))))
                     (binary (subr cb-eff () matrix)
                       (lambda () (let ((a (expr x (car args) i e))) (if (= (m-arity a) 2) a (arity-error d "a binary relation is expected"))))))
              (cond
                ((string=? h "join")
                 (fold (lambda ((a matrix) (b matrix))
                         (if (> (+ (m-arity a) (m-arity b)) 2) (m-join c n a b) (arity-error d "a join of two sets")))
                       (all args)))
                ((string=? h "->") (fold (lambda ((a matrix) (b matrix)) (m-product c n a b))
                                         (iterate go cb-eff ((l datums args)) (listof matrix acyclic)
                                           (if (null? l) nil (cons (expr x (unmarked (car l)) i e) (go (cdr l)))))))
                ((string=? h "union") (same (lambda ((a matrix) (b matrix)) (m-union c a b))))
                ((string=? h "inter") (same (lambda ((a matrix) (b matrix)) (m-inter c a b))))
                ((string=? h "diff") (same (lambda ((a matrix) (b matrix)) (m-diff c a b))))
                ((string=? h "++") (same (lambda ((a matrix) (b matrix)) (m-override c n a b))))
                ((string=? h "<:") (let ((s (expr x (nth d 1) i e)) (r (expr x (nth d 2) i e)))
                                     (if (= (m-arity s) 1) (m-dom-restrict c n s r) (arity-error d "a set is expected first"))))
                ((string=? h ":>") (let ((r (expr x (nth d 1) i e)) (s (expr x (nth d 2) i e)))
                                     (if (= (m-arity s) 1) (m-range-restrict c n r s) (arity-error d "a set is expected last"))))
                ((string=? h "~") (m-transpose n (binary)))
                ((string=? h "^") (m-closure c n (binary)))
                ((string=? h "*") (m-rclosure c n (binary)))
                ((string=? h "if") (let ((a (expr x (nth d 2) i e)) (b (expr x (nth d 3) i e)))
                                     (if (= (m-arity a) (m-arity b)) (m-ite c (form (neutral x) (nth d 1) i e) a b)
                                         (arity-error d "branches of different arities"))))
                ((or (string=? h "prime") (string=? h "quote"))
                 (after-expr x i (lambda ((j int)) (expr x (nth d 1) j e))))
                ((string=? h "let") (expr x (nth d 2) i (let-env x (items (nth d 1)) e)))
                ((string=? h "set") (comprehension (neutral x) (items (nth d 1)) (nth d 2) i e))
                ((string=? h "col") (arity-error d "a col is an arrow's operand"))
                ((string=? h "") (arity-error d "not an expression"))
                (else
                 (tagcase (find-def (extract x model) h)
                   (some f (if (extract f fun) (expr x (extract f body) i (call-env x f args i e))
                               (arity-error d "a predicate, not a function")))
                   (none u (arity-error d "unknown operator"))))))))))))

"`let`'s bindings, each evaluated where it is used."
(define let-env (subr cb-eff (ctx datums env) env)
  (lambda (x bs e)
    (if (null? bs) e
        (let-env x (cdr bs)
                 (cons (product (name (name-of (nth (car bs) 0))) (now #f) (val (m-none 1 1)) (code (nth (car bs) 1)) (scope e)) e)))))

"A call's scope: each parameter bound to its argument, by name."
(define call-env (subr cb-eff (ctx def-info datums int env) env)
  (lambda (x f args i e)
    (iterate bind cb-eff ((ps strings (decl-names (read-decls (extract f params)))) (as datums args) (acc env nil)) env
      (cond ((and (null? ps) (null? as)) acc)
            ((or (null? ps) (null? as)) (error (string-append "casing: wrong number of arguments to " (extract f name))))
            (else (bind (cdr ps) (cdr as) (cons (product (name (car ps)) (now #f) (val (m-none 1 1)) (code (car as)) (scope e)) acc)))))))

"Every binding of declarations `((x y T #:m #:disj) …)`, each later one's
type in the scope of those before: the bindings and when each holds.
A variable of multiplicity `one` ranges over its type's tuples. One of
`lone`, `some` or `set` (higher-order) ranges over sets of them:
- if `skolem` (the quantifier is existential where it stands), as one
  set of fresh inputs to the solver, which picks it. Each translation of
  the quantifier gets its own, so this holds under `all` (a skolem
  function, one set for each binding outside) and in each state;
- if not, as one binding for each set, which casing allows up to
  `most-sets` (Alloy refuses higher-order quantifiers it cannot
  skolemize).
The names of a `#:disj` declaration are bound to disjoint values."
(define-type grounding (productof (guard int) (scope env) (atoms ints)))
(define most-sets int 1024)
(define ground (subr cb-eff (ctx datums int env bool) (listof grounding acyclic))
  (lambda (x decls i e skolem)
    (let ((c (cx x)) (n (extract x n)))
      (letrec ((flat (subr ro ((listof decl acyclic)) (listof (productof (name string) (decl decl) (apart strings)) acyclic))
                 ;; each name, its declaration, and the names before it it is disjoint from
                 (lambda (ds)
                   (if (null? ds) nil
                       (iterate go ro ((ns strings (extract (car ds) names)) (before strings nil)) (listof (productof (name string) (decl decl) (apart strings)) acyclic)
                         (if (null? ns) (flat (cdr ds))
                             (cons (product (name (car ns)) (decl (car ds)) (apart (if (extract (car ds) disj) before nil)))
                                   (go (cdr ns) (cons (car ns) before))))))))
               (subsets (subr spin (ints) (listof ints acyclic))
                 (lambda (l) (if (null? l) (list nil)
                                 (let ((r (subsets (cdr l))))
                                   (append r (iterate go spin ((ss (listof ints acyclic) r)) (listof ints acyclic)
                                               (if (null? ss) nil (cons (cons (car l) (car ss)) (go (cdr ss))))))))))
               (go (subr cb-eff ((listof (productof (name string) (decl decl) (apart strings)) acyclic) grounding) (listof grounding acyclic))
                 (lambda (ds g)
                   (if (null? ds) (list g)
                       (let* ((en (car ds)) (dc (extract en decl)) (sc (extract g scope))
                              (tm (expr (neutral x) (extract dc type) i sc)) (k (m-arity tm))
                              (mult (cond ((not (string=? (extract dc mult) "")) (extract dc mult)) ((= k 1) "one") (else "set")))
                              ;; v bound, when `when` holds and v is apart from those it must be
                              (bind (lambda ((v matrix) (when int) (atoms ints))
                                      (let ((gd (c-and c (cons (extract g guard)
                                                               (cons (if (marked-arrow? (extract dc type)) (c-and2 c when (arrow-mults (neutral x) v (extract dc type) i sc)) when)
                                                                     (iterate apart cb-eff ((l strings (extract en apart))) ints
                                                                       (if (null? l) nil
                                                                           (cons (tagcase (lookup sc (car l))
                                                                                   (some b (m-no c (m-inter c v (extract b val))))
                                                                                   (none u c-true))
                                                                                 (apart (cdr l))))))))))
                                        (if (= gd c-false) nil
                                            (go (cdr ds) (product (guard gd) (scope (bind-now (extract en name) v sc)) (atoms atoms))))))))
                         (cond
                           ((and skolem (extract x top))       ; at the top: a witness, the solver's, shown
                            (let ((v (m-build n k (lambda ((t int)) (if (= (m-ref tm t) c-false) c-false (c-input! c))))))
                              (begin (array-set! (extract x witnesses) 0
                                                 (cons (product (name (extract en name)) (val v)) (array-ref (extract x witnesses) 0)))
                                     (bind v (c-and2 c (m-subset c v tm) (mult-holds c mult v)) (extract g atoms)))))
                           ((string=? mult "one")
                            (iterate each cb-eff ((t int 0)) (listof grounding acyclic)
                              (if (>= t (m-size tm)) nil
                                  (append (bind (m-tuple n k t) (m-ref tm t) (cons t (extract g atoms))) (each (+ t 1))))))
                           (skolem
                            (let ((v (m-build n k (lambda ((t int)) (if (= (m-ref tm t) c-false) c-false (c-input! c))))))
                              (bind v (c-and2 c (m-subset c v tm) (mult-holds c mult v)) (extract g atoms))))
                           (else
                            (let ((ts (iterate go cb-eff ((t int 0)) ints
                                        (cond ((>= t (m-size tm)) nil) ((= (m-ref tm t) c-false) (go (+ t 1))) (else (cons t (go (+ t 1))))))))
                              (if (> (power 2 (list-length ts)) most-sets)
                                  (error (string-append "casing: a higher-order quantifier that cannot be skolemized, over more than "
                                                        (string-append (int->string most-sets) (string-append " sets: " (extract en name)))))
                                  (iterate each cb-eff ((ss (listof ints acyclic) (subsets ts))) (listof grounding acyclic)
                                    (if (null? ss) nil
                                        (let ((sz (list-length (car ss))))
                                          (append (if (or (and (string=? mult "lone") (> sz 1)) (and (string=? mult "some") (= sz 0))) nil
                                                      (bind (m-build n k (lambda ((t int)) (if (in-ints? t (car ss)) c-true c-false)))
                                                            (c-and c (iterate go cb-eff ((l ints (car ss))) ints
                                                                       (if (null? l) nil (cons (m-ref tm (car l)) (go (cdr l))))))
                                                            (extract g atoms)))
                                                  (each (cdr ss)))))))))))))))
        (go (flat (read-decls decls)) (product (guard c-true) (scope e) (atoms nil)))))))

"Whether `v` has multiplicity `m`."
(define mult-holds (subr cb-eff (circuit string matrix) int)
  (lambda (c m v) (cond ((string=? m "one") (m-one c v)) ((string=? m "lone") (m-lone c v)) ((string=? m "some") (m-some c v)) (else c-true))))

"{decls | f}: of unary declarations, a relation of their atoms."
(define comprehension (subr cb-eff (ctx datums datum int env) matrix)
  (lambda (x decls f i e)
    (let* ((ds (read-decls decls)) (k (list-length (decl-names ds)))
           (gs (letrec ((check (subr ro ((listof decl acyclic)) bool)
                              (lambda (l) (or (null? l)
                                              (and (or (string=? (extract (car l) mult) "") (string=? (extract (car l) mult) "one")) (check (cdr l)))))))
                 (if (check ds) (ground x decls i e #f)
                     (error "casing: a comprehension's variables are each one atom"))))
           (n (extract x n))
           (v (the ivec (make-array (power n k) c-false))))
      (letrec ((index (subr ro (ints int) int) (lambda (as acc) (if (null? as) acc (index (cdr as) (+ (* acc n) (car as))))))
               (go (subr cb-eff ((listof grounding acyclic)) matrix)
                 (lambda (l)
                   (if (null? l) (product (arity k) (cells v))
                       (let ((t (if (= (list-length (extract (car l) atoms)) k) (index (reverse (extract (car l) atoms)) 0)
                                    (error "casing: a comprehension's variables are each one atom"))))
                         (begin (array-set! v t (c-and2 (cx x) (extract (car l) guard) (form x f i (extract (car l) scope))))
                                (go (cdr l))))))))
        (go gs)))))

"The operators whose values are integers. Arithmetic is exact: nothing
wraps and nothing overflows. `+%`, `-%`, `*%` and `neg%` wrap, to the
bitwidth of Int's atoms, and only they; `mod` is the remainder that is
never negative."
(define int-ops strings
  (list "size" "+" "-" "*" "div" "rem" "mod" "neg" "+%" "-%" "*%" "neg%" "sum" "int"))
"Whether `d` is an integer operator's: `(* r)`, of one operand, is the
reflexive closure; `(* i j)` a product."
(define int-op? (subr ro (datum) bool)
  (lambda (d) (and (member-string? (head d) int-ops) (not (and (string=? (head d) "*") (= (len d) 2))))))

"Whether `d` is an integer expression: a numeral, an integer operator's,
or a name, function or call standing for one."
(define int-expr? (subr ro (ctx datum env) bool)
  (lambda (x d e)
    (cond ((datum-int? d) #t)
          ((symbol? d)
           (tagcase (lookup e (symbol->string d))
             (some b (and (not (extract b now)) (int-expr? x (extract b code) (extract b scope))))
             (none u (tagcase (find-def (extract x model) (symbol->string d))
                       (some f (and (extract f fun) (null? (extract f params)) (int-expr? x (extract f body) nil)))
                       (none u2 #f)))))
          (else
           (let ((h (head d)))
             (cond ((int-op? d) #t)
                   ((or (string=? h "if") (string=? h "let")) (int-expr? x (nth d 2) e))
                   (else (tagcase (find-def (extract x model) h)
                           (some f (and (extract f fun) (int-expr? x (extract f body) nil)))
                           (none u #f)))))))))

"Int's atom `a`'s value."
(define atom-value (subr spin (ctx int) int)
  (lambda (x a) (- (- a (extract x ibase)) (quotient (power 2 (extract x bw)) 2))))
"Whether `a` is one of Int's atoms."
(define int-atom? (subr spin (ctx int) bool)
  (lambda (x a) (let ((b (extract x ibase))) (and (>= b 0) (>= a b) (< a (+ b (power 2 (extract x bw))))))))

"The integer a set stands for: the sum of its Int atoms' values (Alloy's
`int[e]`); other atoms add nothing."
(define rel-int (subr cb-eff (ctx matrix) bits)
  (lambda (x m)
    (if (not (= (m-arity m) 1)) (error "casing: the integer of a relation that is not a set")
        (let ((c (cx x)))
          (i-sum c (iterate go cb-eff ((a int 0)) (listof bits acyclic)
                     (cond ((>= a (m-size m)) nil)
                           ((or (not (int-atom? x a)) (= (m-ref m a) c-false)) (go (+ a 1)))
                           (else (cons (i-ite c (m-ref m a) (i-const (atom-value x a)) (i-const 0)) (go (+ a 1)))))))))))
"The set an integer stands for: its Int atom, or none if no atom has its
value (Alloy's `Int[i]`). This never wraps."
(define int-set (subr cb-eff (ctx bits) matrix)
  (lambda (x v)
    (let ((c (cx x)))
      (m-build (extract x n) 1 (lambda ((a int)) (if (int-atom? x a) (i-eq c v (i-const (atom-value x a))) c-false))))))

"Integer expression `d` in state `i`: its bits (matrix.fx), exact."
(define ival (subr cb-eff (ctx datum int env) bits)
  (lambda (x d i e)
    (let ((c (cx x)))
      (letrec ((a1 (subr cb-eff () bits) (lambda () (ival x (nth d 1) i e)))
               (a2 (subr cb-eff () bits) (lambda () (ival x (nth d 2) i e)))
               (wrap (subr spin (bits) bits) (lambda (v) (i-wrap v (extract x bw))))
               ;; a / b and its remainder; by 0, what the solver picks (as
               ;; SMT-LIB leaves it): a model that divides by 0 shows it
               (divrem (subr cb-eff (bits bits) quot-rem)
                 (lambda (a b)
                   (let ((qr (i-divrem c a b)) (zero (i-eq c b (i-const 0)))
                         (free (lambda ((w int)) (iterate go cb-eff ((k int w)) bits
                                                   (if (<= k 0) nil (cons (c-input! c) (go (- k 1))))))))
                     (product (q (i-ite c zero (free (+ 1 (i-width a))) (extract qr q)))
                              (r (i-ite c zero (free (+ 1 (i-width a))) (extract qr r))))))))
        (cond
          ((datum-int? d) (i-const d))
          ((symbol? d)
           (let ((s (symbol->string d)))
             (tagcase (lookup e s)
               (some b (if (extract b now) (rel-int x (extract b val)) (ival x (extract b code) i (extract b scope))))
               (none u (tagcase (find-def (extract x model) s)
                         (some f (if (and (extract f fun) (null? (extract f params)) (int-expr? x (extract f body) nil))
                                     (ival x (extract f body) i nil)
                                     (rel-int x (expr x d i e))))
                         (none u2 (rel-int x (expr x d i e))))))))
          (else
           (let ((h (head d)))
             (cond
               ((string=? h "size") (m-count c (expr x (nth d 1) i e)))
               ((string=? h "+") (i-add c (a1) (a2)))
               ((string=? h "-") (if (= (len d) 2) (i-neg c (a1)) (i-sub c (a1) (a2))))
               ((string=? h "neg") (i-neg c (a1)))
               ((string=? h "*") (i-mul c (a1) (a2)))
               ((string=? h "div") (extract (divrem (a1) (a2)) q))
               ((string=? h "rem") (extract (divrem (a1) (a2)) r))
               ((string=? h "mod") (let* ((b (a2)) (r (extract (divrem (a1) b) r)))
                                     (i-ite c (i-sign r) (i-add c r (i-abs c b)) r)))
               ((string=? h "+%") (wrap (i-add c (a1) (a2))))
               ((string=? h "-%") (wrap (i-sub c (a1) (a2))))
               ((string=? h "*%") (wrap (i-mul c (a1) (a2))))
               ((string=? h "neg%") (wrap (i-neg c (a1))))
               ((string=? h "int") (rel-int x (expr x (nth d 1) i e)))
               ((string=? h "sum")                    ; (sum ((x S)) i): over the bindings
                (i-sum c (iterate go cb-eff ((l (listof grounding acyclic) (ground x (items (nth d 1)) i e #f))) (listof bits acyclic)
                           (if (null? l) nil
                               (cons (i-ite c (extract (car l) guard) (ival x (nth d 2) i (extract (car l) scope)) (i-const 0))
                                     (go (cdr l)))))))
               ((string=? h "if") (i-ite c (form (neutral x) (nth d 1) i e) (a2) (ival x (nth d 3) i e)))
               ((string=? h "let") (ival x (nth d 2) i (let-env x (items (nth d 1)) e)))
               (else
                (tagcase (find-def (extract x model) h)
                  (some f (if (and (extract f fun) (int-expr? x (extract f body) nil))
                              (ival x (extract f body) i (call-env x f (cdr (items d)) i e))
                              (rel-int x (expr x d i e))))
                  (none u (rel-int x (expr x d i e)))))))))))))

"Formula `d` in state `i`."
(define form (subr cb-eff (ctx datum int env) int)
  (lambda (x0 d i e)
    (let* ((h (head d)) (x (if (member-string? h temporal-ops) (inner x0) x0))
           (c (cx x)) (args (if (pair? d) (cdr (items d)) nil))
           (k (extract x k)))
      (letrec ((f1 (subr cb-eff (int) int) (lambda (j) (form x (car args) j e)))
               (f2 (subr cb-eff (int) int) (lambda (j) (form x (car (cdr args)) j e)))
               (all-forms (subr cb-eff (datums) ints) (lambda (l) (if (null? l) nil (cons (form x (car l) i e) (all-forms (cdr l))))))
               (e1 (subr cb-eff () matrix) (lambda () (expr x (car args) i e)))
               (e2 (subr cb-eff () matrix) (lambda () (expr x (car (cdr args)) i e)))
               (same2 (subr cb-eff ((subr cb-eff (matrix matrix) int)) int)
                 (lambda (g) (let ((a (e1)) (b (e2))) (if (= (m-arity a) (m-arity b)) (g a b) (arity-error d "operands of different arities")))))
               (quantified? (subr ro () bool) (lambda () (= (list-length args) 2)))
               ;; a quantifier: its variables skolemized where it is existential
               ;; (`some` positively, `all` or `no` negatively); its body's
               ;; polarity as the quantifier's (`no`'s reversed; `one`'s and
               ;; `lone`'s both ways)
               (quant (subr cb-eff (string) int)
                 (lambda (q)
                   (let* ((pol (extract x pol))
                          (skolem (or (and (string=? q "some") (= pol 1)) (and (or (string=? q "all") (string=? q "no")) (= pol -1))))
                          (y0 (cond ((string=? q "no") (flipped x)) ((or (string=? q "one") (string=? q "lone")) (neutral x)) (else x)))
                          (gs (ground x (items (car args)) i e skolem))
                          ;; still the top if skolemized there, to one binding
                          (y (if (and skolem (extract x top) (= (list-length gs) 1)) y0 (inner y0))))
                     (letrec ((pairs (subr cb-eff ((listof grounding acyclic)) ints)
                                (lambda (l) (if (null? l) nil
                                                (cons (let ((b (form y (car (cdr args)) i (extract (car l) scope))) (g (extract (car l) guard)))
                                                        (if (string=? q "all") (c-implies c g b) (c-and2 c g b)))
                                                      (pairs (cdr l)))))))
                       (let ((ps (pairs gs)))
                         (cond ((string=? q "all") (c-and c ps))
                               ((string=? q "some") (c-or c ps))
                               ((string=? q "no") (c-not (c-or c ps)))
                               ((string=? q "lone") (c-at-most-one c ps))
                               (else (c-exactly-one c ps)))))))))
        (cond
          ((bool? d) (if d c-true c-false))
          ((sym? d "true") c-true)
          ((sym? d "false") c-false)
          ((symbol? d)
           (tagcase (find-def (extract x model) (symbol->string d))
             (some f (if (extract f fun) (arity-error d "a function, not a predicate") (call x f nil i e)))
             (none u (tagcase (lookup e (symbol->string d))
                       (some b (if (extract b now) (arity-error d "a relation, not a formula")
                                   (form x (extract b code) i (extract b scope))))
                       (none u (arity-error d "not a formula"))))))
          ((string=? h "in")
           (if (marked-arrow? (car (cdr args)))
               (let ((a (e1))) (c-and2 c (same2 (lambda ((a2 matrix) (b matrix)) (m-subset c a b))) (arrow-mults x a (car (cdr args)) i e)))
               (same2 (lambda ((a matrix) (b matrix)) (m-subset c a b)))))
          ((string=? h "=")
           (if (or (int-expr? x (car args) e) (int-expr? x (car (cdr args)) e))
               (i-eq c (ival x (car args) i e) (ival x (car (cdr args)) i e))
               (same2 (lambda ((a matrix) (b matrix)) (m-equal c a b)))))
          ((string=? h "!=") (c-not (form x (the datum (cons (sym "=") args)) i e)))
          ((string=? h "<") (i-lt c (ival x (car args) i e) (ival x (car (cdr args)) i e)))
          ((string=? h ">") (i-lt c (ival x (car (cdr args)) i e) (ival x (car args) i e)))
          ((string=? h "<=") (c-not (i-lt c (ival x (car (cdr args)) i e) (ival x (car args) i e))))
          ((string=? h ">=") (c-not (i-lt c (ival x (car args) i e) (ival x (car (cdr args)) i e))))
          ((string=? h "all") (quant "all"))
          ((string=? h "some") (if (quantified?) (quant "some") (m-some c (e1))))
          ((string=? h "no") (if (quantified?) (quant "no") (m-no c (e1))))
          ((string=? h "one") (if (quantified?) (quant "one") (m-one c (e1))))
          ((string=? h "lone") (if (quantified?) (quant "lone") (m-lone c (e1))))
          ((string=? h "not") (c-not (form (flipped x) (car args) i e)))
          ((string=? h "and") (c-and c (all-forms args)))
          ((string=? h "or") (c-or c (all-forms args)))
          ((or (string=? h "implies") (string=? h "=>")) (c-implies c (form (flipped x) (car args) i e) (f2 i)))
          ((string=? h "iff") (c-iff c (form (neutral x) (car args) i e) (form (neutral x) (car (cdr args)) i e)))
          ((string=? h "if") (c-ite c (form (neutral x) (car args) i e) (f2 i) (form x (nth d 3) i e)))
          ((string=? h "let") (form x (nth d 2) i (let-env x (items (nth d 1)) e)))
          ;; time
          ((string=? h "after") (after-form x i f1))
          ((string=? h "then") (c-and2 c (f1 i) (after-form x i f2)))
          ((string=? h "always") (per-loop x (lambda ((l int)) (c-and c (each-form f1 (future-seq x i l))))))
          ((string=? h "eventually") (per-loop x (lambda ((l int)) (c-or c (each-form f1 (future-seq x i l))))))
          ((string=? h "until") (per-loop x (lambda ((l int)) (until-along c f1 f2 (future-seq x i l)))))
          ((string=? h "releases")
           (c-not (per-loop x (lambda ((l int)) (until-along c (lambda ((j int)) (c-not (f1 j))) (lambda ((j int)) (c-not (f2 j))) (future-seq x i l))))))
          ((string=? h "before")
           (per-loop x (lambda ((l int)) (let ((ps (reverse (past-seq x i l)))) (if (and (pair? ps) (pair? (cdr ps))) (f1 (car (cdr ps))) c-false)))))
          ((string=? h "once") (per-loop x (lambda ((l int)) (c-or c (each-form f1 (past-seq x i l))))))
          ((string=? h "historically") (per-loop x (lambda ((l int)) (c-and c (each-form f1 (past-seq x i l))))))
          ((string=? h "since") (per-loop x (lambda ((l int)) (until-along c f1 f2 (reverse (past-seq x i l))))))
          ((string=? h "triggered")
           (c-not (per-loop x (lambda ((l int)) (until-along c (lambda ((j int)) (c-not (f1 j))) (lambda ((j int)) (c-not (f2 j))) (reverse (past-seq x i l)))))))
          ;; the relations named unchanged in the next state; a region @r
          ;; names every relation that changes in it
          ((string=? h "unchanged")
           (c-and c (iterate go cb-eff ((l datums args)) ints
                      (cond ((null? l) nil)
                            ((region? (car l))
                             (go (append (iterate syms ro ((ns strings (written (extract x model) (list (name-of (car l)))))) datums
                                           (if (null? ns) nil (cons (sym (car ns)) (syms (cdr ns)))))
                                         (cdr l))))
                            (else (cons (m-equal c (after-expr x i (lambda ((j int)) (expr x (car l) j e))) (expr x (car l) i e))
                                        (go (cdr l))))))))
          ((string=? h "stutter")
           (form x (the datum (cons (sym "unchanged") (iterate go ro ((l strings (var-names (extract x model)))) datums
                                                        (if (null? l) nil (cons (sym (car l)) (go (cdr l)))))))
                 i e))
          ((string=? h "") (arity-error d "not a formula"))
          (else
           (tagcase (find-def (extract x model) h)
             (some f (if (extract f fun) (arity-error d "a function, not a predicate") (call x f args i e)))
             (none u (arity-error d "unknown predicate")))))))))

"That relation `r` has the multiplicities arrow `d` says, `L m -> n R`
(several operands nest to the right, as Alloy's arrows do): each tuple
of L maps to n of R's, each of R's to m of L's; within, the operands'
own arrows' (Alloy's `A -> (B one -> one C)`: each a's B-to-C a
bijection). That r is within the arrow at all is the caller's."
(define arrow-mults (subr cb-eff (ctx matrix datum int env) int)
  (lambda (x r d i e)
    (let* ((c (cx x)) (n (extract x n)) (ops (cdr (items d)))
           (l (car ops)) (rr (if (null? (cdr (cdr ops))) (car (cdr ops)) (the datum (cons (sym "->") (cdr ops)))))
           (ml (mark-of l)) (mr (mark-of rr)) (lx (unmarked l)) (rx (unmarked rr))
           (lm (expr x lx i e)) (rm (expr x rx i e)) (a (m-arity lm)) (b (m-arity rm)) (nb (power n b)))
      (letrec ((each (subr cb-eff (matrix (subr cb-eff (int) matrix) string datum) ints)
                 ;; for each tuple t of `side`: its slice of r, of multiplicity m and within arrow `inner`'s
                 (lambda (side slice m inner)
                   (if (and (or (string=? m "") (string=? m "set")) (not (marked-arrow? inner))) nil
                       (iterate go cb-eff ((t int 0)) ints
                         (cond ((>= t (m-size side)) nil)
                               ((= (m-ref side t) c-false) (go (+ t 1)))
                               (else (let ((v (slice t)))
                                       (cons (c-implies c (m-ref side t)
                                                        (c-and2 c (mult-holds c m v)
                                                                (if (marked-arrow? inner) (arrow-mults x v inner i e) c-true)))
                                             (go (+ t 1)))))))))))
        (c-and c (append (each lm (lambda ((t int)) (m-build n b (lambda ((s int)) (m-ref r (+ (* t nb) s))))) mr rx)
                         (each rm (lambda ((s int)) (m-build n a (lambda ((p int)) (m-ref r (+ (* p nb) s))))) ml lx)))))))

"A predicate's or event's call. An event's frame: every relation that
changes and that it does not write is unchanged. A region it writes
writes every relation that changes in it."
(define call (subr cb-eff (ctx def-info datums int env) int)
  (lambda (x f args i e)
    (let ((body (form x (extract f body) i (call-env x f args i e)))
          (writes (written (extract x model) (extract f writes))))
      (if (not (extract f event)) body
          (c-and2 (cx x) body
                  (form x (the datum (cons (sym "unchanged")
                                           (iterate go ro ((l strings (var-names (extract x model)))) datums
                                             (cond ((null? l) nil)
                                                   ((member-string? (car l) writes) (go (cdr l)))
                                                   (else (cons (sym (car l)) (go (cdr l))))))))
                        i nil))))))

;;; ------------------------------------------------------------ the problem

"Whether `d` mentions the name `n`."
(define mentions? (subr ro (datum string) bool)
  (lambda (d n) (cond ((symbol? d) (string=? (symbol->string d) n))
                      ((pair? d) (or (mentions? (car d) n) (mentions? (cdr d) n)))
                      (else #f))))

"The facts the declarations give: sigs within their parents, parts
disjoint, an abstract sig its parts, multiplicities, and fields within
their columns with their last column's multiplicity."
(define declaration-facts (subr ro (model) datums)
  (lambda (m)
    (letrec ((s (subr ro (string) datum) (lambda (n) (sym n)))
             (sigs (subr ro ((listof sig-info acyclic)) datums)
               (lambda (l)
                 (if (null? l) nil
                     (let* ((g (car l)) (n (extract g name))
                            (parts (iterate go ro ((k (listof sig-info acyclic) (extract m sigs))) strings
                                     (cond ((null? k) nil)
                                           ((and (string=? (extract (car k) parent) n) (not (extract (car k) subset))) (cons (extract (car k) name) (go (cdr k))))
                                           (else (go (cdr k))))))
                            (fs (append (if (string=? (extract g parent) "") nil (list (the datum (list (sym "in") (s n) (s (extract g parent))))))
                                        (append (if (string=? (extract g mult) "set") nil (list (the datum (list (sym (extract g mult)) (s n)))))
                                                (append (if (and (extract g abstract) (pair? parts))
                                                            (list (the datum (list (sym "in") (s n) (the datum (cons (sym "union") (names->syms parts))))))
                                                            nil)
                                                        (append (disjoint parts)
                                                                ;; its facts, of each atom: (all ((this S)) F)
                                                                (iterate go ro ((k datums (extract g facts))) datums
                                                                  (if (null? k) nil
                                                                      (cons (the datum (list (sym "all") (list (list (sym "this") (s n))) (car k)))
                                                                            (go (cdr k)))))))))))
                       (append fs (sigs (cdr l)))))))
             (names->syms (subr ro (strings) datums) (lambda (l) (if (null? l) nil (cons (sym (car l)) (names->syms (cdr l))))))
             (disjoint (subr ro (strings) datums)
               (lambda (l) (if (null? l) nil
                               (append (iterate go ro ((k strings (cdr l))) datums
                                         (if (null? k) nil (cons (the datum (list (sym "no") (list (sym "inter") (sym (car l)) (sym (car k))))) (go (cdr k)))))
                                       (disjoint (cdr l))))))
             (fields (subr ro ((listof field-info acyclic)) datums)
               (lambda (l)
                 (if (null? l) nil
                     (let* ((f (car l)) (fn (sym (extract f name))) (o (sym (extract f owner)))
                            (this-f (the datum (list (sym "join") (sym "this") fn)))
                            (each (lambda ((d datum)) (the datum (list (sym "all") (list (list (sym "this") o)) d))))
                            ;; columns that mention this are each owner's: within them, owner by owner
                            ;; and so are columns that say their multiplicities
                            (own (or (iterate any ro ((l datums (extract f cols))) bool
                                       (and (pair? l) (or (mentions? (car l) "this") (any (cdr l)))))
                                     (marked-arrow? (the datum (cons (sym "->") (extract f cols))))))
                            (within (cond ((string=? (extract f owner) "")
                                           (list (the datum (list (sym "in") fn (the datum (cons (sym "->") (extract f cols)))))))
                                          (own
                                           (list (the datum (list (sym "in") fn (the datum (cons (sym "->") (cons o (iterate go ro ((l datums (flat-cols (extract f cols)))) datums
                                                                                                                      (if (null? l) nil (cons (sym "univ") (go (cdr l))))))))))
                                                 (each (the datum (list (sym "in") this-f (the datum (cons (sym "->") (extract f cols))))))))
                                          (else (list (the datum (list (sym "in") fn (the datum (cons (sym "->") (cons o (extract f cols))))))))))
                            (mult (if (string=? (extract f mult) "set") nil (list (each (the datum (list (sym (extract f mult)) this-f))))))
                            ;; #:apart: distinct owners' values apart
                            (disj (if (extract f apart)
                                      (list (the datum (list (sym "all") (list (list (sym "this") (sym "that") o (the datum #:disj)))
                                                             (list (sym "no") (list (sym "inter") this-f (list (sym "join") (sym "that") fn))))))
                                      nil)))
                       (append within (append mult (append disj (fields (cdr l))))))))))
      (append (sigs (extract m sigs)) (fields (extract m fields))))))

"A relation's matrix in one state: true on its lower bound, an input on
the rest of its upper, false elsewhere."
(define bound-matrix (subr cb-eff (circuit int int (subr ro (int) int)) matrix)
  (lambda (c n k at)            ; at: 1 lower, 0 upper only, -1 neither
    (m-build n k (lambda ((t int)) (let ((w (at t))) (cond ((= w 1) c-true) ((= w 0) (c-input! c)) (else c-false)))))))

"Which of a column's atoms it may hold: a sig's upper bound, else every atom."
(define column-atoms (subr ro (universe datum int) ints)
  (lambda (u d0 n) (let ((d (unmarked d0)))
                     (if (symbol? d) (tagcase (bound-of u (symbol->string d)) (some b (extract b upper)) (none u2 (range 0 n))) (range 0 n)))))

(define in-ints? (subr ro (int ints) bool) (lambda (x l) (and (pair? l) (or (= x (car l)) (in-ints? x (cdr l))))))

"util/ordering's `next`: each ordered sig's atoms in their order, if its
order is fixed (`order-fixed?`); else any pair of its atoms, left to the
solver (and the facts `with-ordering` adds)."
(define order-matrix (subr cb-eff (circuit int model universe) matrix)
  (lambda (c n m u)
    (letrec ((atoms (subr ro ((listof sig-info acyclic) bool) (listof ints acyclic))   ; the fixed ones', or the others'
               (lambda (l fixed) (cond ((null? l) nil)
                                       ((eq? (order-fixed? m (car l)) fixed)
                                        (cons (tagcase (bound-of u (extract (car l) name)) (some b (extract b upper)) (none u2 nil)) (atoms (cdr l) fixed)))
                                       (else (atoms (cdr l) fixed)))))
             (line? (subr ro (int int ints) bool)          ; b just after a in as
               (lambda (a b as) (and (pair? as) (pair? (cdr as))
                                     (or (and (= (car as) a) (= (car (cdr as)) b)) (line? a b (cdr as))))))
             (any (subr ro (int int (listof ints acyclic) (subr ro (int int ints) bool)) bool)
               (lambda (a b ls p) (and (pair? ls) (or (p a b (car ls)) (any a b (cdr ls) p))))))
      (let ((fixed (atoms (ordered-sigs m) #t)) (free (atoms (ordered-sigs m) #f)))
        (m-build n 2 (lambda ((t int))
                       (let ((a (quotient t n)) (b (modulo t n)))
                         (cond ((any a b fixed line?) c-true)
                               ((any a b free (lambda ((a int) (b int) (as ints)) (and (in-ints? a as) (in-ints? b as)))) (c-input! c))
                               (else c-false)))))))))

"The problem's relations, `k` states of those that change, and the loop."
(define make-ctx (subr cb-eff (model universe int int int) ctx)
  (lambda (m u k copies bw)
    (let* ((c (make-circuit)) (n (list-length (extract u names)))
           (states (lambda ((var bool) (make (subr cb-eff () matrix)))
               (let ((a (the (arrayof matrix @cb) (make-array (if var k 1) (m-none 1 1)))))
                 (iterate go cb-eff ((j int 0)) (arrayof matrix @cb)
                   (if (>= j (array-length a)) a (begin (array-set! a j (make)) (go (+ j 1))))))))
           (sig-rels (iterate go cb-eff ((l (listof sig-info acyclic) (extract m sigs))) (listof rel acyclic)
                       (if (null? l) nil
                           (let ((b (tagcase (bound-of u (extract (car l) name)) (some b b) (none u2 (the sig-bound (product (name "") (lower nil) (upper nil)))))))
                             (cons (product (name (extract (car l) name)) (arity 1) (var (extract (car l) var))
                                            (mats (states (extract (car l) var)
                                                          (lambda () (bound-matrix c n 1 (lambda ((t int)) (cond ((in-ints? t (extract b lower)) 1)
                                                                                                                 ((in-ints? t (extract b upper)) 0)
                                                                                                                 (else -1))))))))
                                   (go (cdr l)))))))
           (field-rels (letrec ((go (subr cb-eff ((listof field-info acyclic)) (listof rel acyclic))
                                  (lambda (l)
                                    (if (null? l) nil
                                        (let* ((f (car l))
                                               (rest (iterate cs ro ((ds datums (flat-cols (extract f cols)))) (listof ints acyclic)
                                                       (if (null? ds) nil (cons (column-atoms u (car ds) n) (cs (cdr ds))))))
                                               (cols (if (string=? (extract f owner) "") rest (cons (column-atoms u (sym (extract f owner)) n) rest)))
                                               (k2 (list-length cols))
                                               ;; tuple t's atoms each in its column's
                                               (ok? (lambda ((t int)) (iterate go ro ((t int t) (cs (listof ints acyclic) cols) (j int (- k2 1))) bool
                                                                        (if (null? cs) #t
                                                                            (and (in-ints? (quotient t (power n j)) (car cs))
                                                                                 (go (modulo t (power n j)) (cdr cs) (- j 1))))))))
                                          (cons (product (name (extract f name)) (arity k2) (var (extract f var))
                                                         (mats (states (extract f var)
                                                                       (if (and (string=? (extract f name) "next") (string=? (extract f owner) "") (pair? (ordered-sigs m)))
                                                                           (lambda () (order-matrix c n m u))
                                                                           (lambda () (bound-matrix c n k2 (lambda ((t int)) (if (ok? t) 0 -1))))))))
                                                (go (cdr l))))))))
                         (go (extract m fields))))
           (loops (the ivec (make-array k c-false))))
      (begin
        (iterate go cb-eff ((j int 0)) unit
          (unless (>= j k) (array-set! loops j (c-input! c)) (go (+ j 1))))
        (c-assert! c (c-exactly-one c (iterate go cb-eff ((j int 0)) ints
                                        (if (>= j k) nil (cons (array-ref loops j) (go (+ j 1)))))))
        (product (c c) (n n) (k k) (u copies) (loops loops)
                 (rels (append sig-rels
                               ;; Int, its atoms, if there are any
                               (tagcase (bound-of u "Int")
                                 (some b (list (product (name "Int") (arity 1) (var #f)
                                                        (mats (states #f (lambda () (bound-matrix c n 1 (lambda ((t int)) (if (in-ints? t (extract b upper)) 1 -1)))))))))
                                 (none u2 nil))
                               field-rels))
                 (model m) (universe u) (pol 1) (bw bw)
                 (ibase (tagcase (bound-of u "Int") (some b (car (extract b upper))) (none u2 -1)))
                 (top #t) (witnesses (the (arrayof (listof witness acyclic) @cb) (make-array 1 nil))))))))

;;; ------------------------------------------------------------ what was found

(define atom-name (subr ro (ctx int) string)
  (lambda (x a) (iterate go ro ((l strings (extract (extract x universe) names)) (i int a)) string
                  (cond ((null? l) "?") ((= i 0) (car l)) (else (go (cdr l) (- i 1)))))))
"A tuple written a->b->c."
(define tuple-shown (subr ro (ctx int int) string)
  (lambda (x k t)
    (let ((n (extract x n)))
      (letrec ((go (subr ro (int int) strings)
                 (lambda (t j) (if (< j 0) nil (cons (atom-name x (quotient t (power n j))) (go (modulo t (power n j)) (- j 1)))))))
        (string-join (go t (- k 1)) "->")))))
(define matrix-shown (subr cb-eff (ctx matrix) string)
  (lambda (x m)
    (letrec ((go (subr cb-eff (int) strings)
               (lambda (t) (if (>= t (m-size m)) nil
                               (if (c-value (cx x) (m-ref m t)) (cons (tuple-shown x (m-arity m) t) (go (+ t 1))) (go (+ t 1)))))))
      (string-append "{" (string-append (string-join (go 0) ", ") "}")))))
(define state-shown (subr cb-eff (ctx int bool) string)
  (lambda (x i changing-only)
    (letrec ((go (subr cb-eff ((listof rel acyclic)) strings)
               (lambda (l) (cond ((null? l) nil)
                                 ((string=? (extract (car l) name) "Int") (go (cdr l)))
                                 ((or (extract (car l) var) (not changing-only))
                                  (cons (string-append "  " (string-append (extract (car l) name) (string-append " = " (matrix-shown x (rel-at (car l) i))))) (go (cdr l))))
                                 (else (go (cdr l)))))))
      (string-join (go (extract x rels)) "\n"))))
"What was found: the relations; for a trace, those that do not change,
then each state's that do, and where the loop goes back to."
(define instance-shown (subr cb-eff (ctx) string)
  (lambda (x)
    (let ((k (extract x k)))
      (string-append
       (if (and (= k 1) (not (any-var? (extract x model)))) (state-shown x 0 #f)
          (let ((loop (iterate go cb-eff ((l int 0)) int
                        (if (or (>= l k) (c-value (cx x) (loop-at x l))) l (go (+ l 1)))))
                (static (iterate go cb-eff ((l (listof rel acyclic) (extract x rels))) strings
                          (cond ((null? l) nil)
                                ((or (extract (car l) var) (string=? (extract (car l) name) "Int")) (go (cdr l)))
                                (else (cons (string-append "  " (string-append (extract (car l) name) (string-append " = " (matrix-shown x (rel-at (car l) 0))))) (go (cdr l))))))))
            (string-append
             (if (null? static) "" (string-append (string-join static "\n") "\n"))
             (string-join (iterate go cb-eff ((i int 0)) strings
                            (if (>= i k) nil
                                (cons (string-append "state " (string-append (int->string i)
                                                                             (string-append (if (= i loop) " (the loop comes back here)" "")
                                                                                            (string-append ":\n" (state-shown x i #t)))))
                                      (go (+ i 1)))))
                          "\n"))))
       (witnesses-shown x)))))

"The witnesses, `$x`: of each existential at the top, the solver's
choice; for a check, the counterexample's. Two of one name are told apart
by a number, as Alloy's are."
(define witnesses-shown (subr cb-eff (ctx) string)
  (lambda (x)
    (letrec ((count (subr ro (string (listof witness acyclic)) int)
               (lambda (nm l) (cond ((null? l) 0) ((string=? (extract (car l) name) nm) (+ 1 (count nm (cdr l)))) (else (count nm (cdr l))))))
             (go (subr cb-eff ((listof witness acyclic) (listof witness acyclic)) strings)
               (lambda (l before)
                 (if (null? l) nil
                     (let* ((nm (extract (car l) name)) (j (count nm before))
                            (label (string-append "$" (if (= j 0) nm (string-append nm (string-append "_" (int->string j)))))))
                       (cons (string-append "\n  " (string-append label (string-append " = " (matrix-shown x (extract (car l) val)))))
                             (go (cdr l) (cons (car l) before))))))))
      (string-join (go (reverse (array-ref (extract x witnesses) 0)) nil) ""))))

;;; ------------------------------------------------------------ types

"Alloy's types, as its warnings. A set expression's type is a union of
tuples of sigs: each a top-level sig or a part of one (a subset sig has
its parent's), `univ`, or `Int`. Two sigs overlap when one is the other
or below it (`#:extends`), or either is `univ`. Where the types say an
operator's result is always empty, or two sides are always disjoint,
casing warns, as Alloy does (`ExprBinary`); it changes nothing found. A
type casing cannot tell, `?`, overlaps everything, so says nothing."
(define-type ttype (listof strings acyclic))
(define-type tbinding (productof (name string) (type ttype)))
(define-type tenv (listof tbinding acyclic))
(define t-unknown ttype (list (list "?")))
(define unknown? (subr ro (ttype) bool)
  (lambda (t) (and (pair? t) (or (member-string? "?" (car t)) (unknown? (cdr t))))))

"The sig a name's atoms are typed by: a subset sig's parent's."
(define prim-of (subr ro (model string) string)
  (lambda (m s) (tagcase (find-sig m s)
                  (some g (if (and (extract g subset) (not (string=? (extract g parent) ""))) (prim-of m (extract g parent)) s))
                  (none u s))))
"Whether sig a is b or below it."
(define below? (subr ro (model string string) bool)
  (lambda (m a b) (or (string=? a b)
                      (tagcase (find-sig m a)
                        (some g (and (not (extract g subset)) (not (string=? (extract g parent) "")) (below? m (extract g parent) b)))
                        (none u #f)))))
(define overlap? (subr ro (model string string) bool)
  (lambda (m a b) (or (string=? a "?") (string=? b "?") (string=? a "univ") (string=? b "univ") (below? m a b) (below? m b a))))
"Of two that overlap, the narrower."
(define meet (subr ro (model string string) string)
  (lambda (m a b) (cond ((or (string=? a "univ") (string=? a "?")) b) ((below? m a b) a) (else b))))
(define tuples-overlap? (subr ro (model strings strings) bool)
  (lambda (m a b) (or (not (= (list-length a) (list-length b)))
                      (iterate go ro ((x strings a) (y strings b)) bool
                        (or (null? x) (and (overlap? m (car x) (car y)) (go (cdr x) (cdr y))))))))
"Whether some tuple of `a` overlaps one of `b`."
(define types-overlap? (subr ro (model ttype ttype) bool)
  (lambda (m a b) (or (unknown? a) (unknown? b)
                      (iterate go ro ((l ttype a)) bool
                        (and (pair? l)
                             (or (iterate each ro ((k ttype b)) bool
                                   (and (pair? k) (or (tuples-overlap? m (car l) (car k)) (each (cdr k)))))
                                 (go (cdr l))))))))
"Every pair of `a`'s and `b`'s, made by `f` (or dropped, if it says nil)."
(define pairs-of (subr ro (ttype ttype (subr ro (strings strings) ttype)) ttype)
  (lambda (a b f) (if (null? a) nil
                      (append (iterate go ro ((k ttype b)) ttype
                                (if (null? k) nil (append (f (car a) (car k)) (go (cdr k)))))
                              (pairs-of (cdr a) b f)))))
(define slashed? (subr spin (string) bool)
  (lambda (s) (iterate go spin ((i int 0)) bool
                (and (< i (string-length s)) (or (char=? (string-ref s i) #\/) (go (+ i 1)))))))
(define last-of (subr ro (strings) string) (lambda (l) (if (null? (cdr l)) (car l) (last-of (cdr l)))))
(define but-last (subr ro (strings) strings) (lambda (l) (if (null? (cdr l)) nil (cons (car l) (but-last (cdr l))))))

"A field's type: its owner's, then its columns', each typed with `this`
its owner."
(define field-ttype (subr cb-eff (model field-info) ttype)
  (lambda (m f)
    (let ((te (if (string=? (extract f owner) "") nil
                  (list (product (name "this") (type (list (list (prim-of m (extract f owner))))))))))
      (iterate go cb-eff ((l datums (extract f cols)) (acc ttype (if (string=? (extract f owner) "") (list nil) (list (list (prim-of m (extract f owner))))))) ttype
        (if (null? l) acc
            (go (cdr l) (pairs-of acc (tc m (unmarked (car l)) te (the (arrayof strings @cb) (make-array 1 nil)) "")
                                  (lambda ((x strings) (y strings)) (list (append x y))))))))))

"The type of expression `d`; warnings, each said `where`, added to `w`."
(define tc (subr cb-eff (model datum tenv (arrayof strings @cb) string) ttype)
  (lambda (m d te w where)
    (letrec ((warn (subr cb-eff (string) unit)
               (lambda (msg) (array-set! w 0 (cons (string-append "warning: in " (string-append where (string-append ": " (string-append (shown d) (string-append ": " msg)))))
                                                    (array-ref w 0)))))
             (t (subr cb-eff (datum) ttype) (lambda (x) (tc m x te w where)))
             (ts (subr cb-eff (datums) (listof ttype acyclic)) (lambda (l) (if (null? l) nil (cons (t (car l)) (ts (cdr l))))))
             (fold (subr cb-eff ((subr cb-eff (ttype ttype) ttype) (listof ttype acyclic)) ttype)
               (lambda (f l) (if (null? l) t-unknown
                                 (iterate go cb-eff ((a ttype (car l)) (k (listof ttype acyclic) (cdr l))) ttype
                                   (if (null? k) a (go (f a (car k)) (cdr k)))))))
             (empty-warns (subr cb-eff (ttype (listof ttype acyclic) string) ttype)
               ;; r, warning if it is empty though no operand is
               (lambda (r parts msg)
                 (begin (if (and (null? r) (iterate ok ro ((l (listof ttype acyclic) parts)) bool
                                             (or (null? l) (and (pair? (car l)) (not (unknown? (car l))) (ok (cdr l))))))
                            (warn msg) #u)
                        r))))
      (cond
        ((datum-int? d) (list (list "Int")))
        ((symbol? d)
         (let ((s (symbol->string d)))
           (letrec ((look (subr ro (tenv) (sumof (none unit) (some ttype)))
                      (lambda (l) (cond ((null? l) (sum none #u)) ((string=? (extract (car l) name) s) (sum some (extract (car l) type))) (else (look (cdr l)))))))
             (tagcase (look te)
               (some ty ty)
               (none u
                 (cond ((string=? s "univ") (list (list "univ")))
                       ((string=? s "iden") (list (list "univ" "univ")))
                       ((string=? s "Int") (list (list "Int")))
                       (else
                        (tagcase (find-sig m s)
                          (some g (list (list (prim-of m s))))
                          (none u2
                            (letrec ((field (subr ro ((listof field-info acyclic)) (sumof (none unit) (some field-info)))
                                              (lambda (l) (cond ((null? l) (sum none #u)) ((string=? (extract (car l) name) s) (sum some (car l))) (else (field (cdr l)))))))
                              (tagcase (field (extract m fields))
                                (some f (field-ttype m f))
                                (none u3 t-unknown))))))))))))
        ((int-op? d) (begin (ts (cdr (items d))) (list (list "Int"))))
        (else
         (let* ((h (head d)) (args (if (pair? d) (cdr (items d)) nil)))
           (cond
             ((string=? h "join")
              (let ((parts (ts args)))
                (empty-warns (fold (lambda ((a ttype) (b ttype))
                                     (if (or (unknown? a) (unknown? b)) t-unknown
                                         (pairs-of a b (lambda ((x strings) (y strings))
                                                         (if (overlap? m (last-of x) (car y)) (list (append (but-last x) (cdr y))) nil)))))
                                   parts)
                             parts "the join always yields an empty set")))
             ((string=? h "->")
              (fold (lambda ((a ttype) (b ttype)) (if (or (unknown? a) (unknown? b)) t-unknown (pairs-of a b (lambda ((x strings) (y strings)) (list (append x y))))))
                    (ts (iterate go ro ((l datums args)) datums (if (null? l) nil (cons (unmarked (car l)) (go (cdr l))))))))
             ((or (string=? h "union") (string=? h "++")) (fold (lambda ((a ttype) (b ttype)) (append a b)) (ts args)))
             ((string=? h "inter")
              (let ((parts (ts args)))
                (empty-warns (fold (lambda ((a ttype) (b ttype))
                                     (if (or (unknown? a) (unknown? b)) t-unknown
                                         (pairs-of a b (lambda ((x strings) (y strings))
                                                         (if (tuples-overlap? m x y)
                                                             (list (iterate go ro ((p strings x) (q strings y)) strings
                                                                     (if (or (null? p) (null? q)) nil (cons (meet m (car p) (car q)) (go (cdr p) (cdr q))))))
                                                             nil)))))
                                   parts)
                             parts "the intersection is always empty: its operands are always disjoint")))
             ((string=? h "diff") (let ((parts (ts args))) (if (pair? parts) (car parts) t-unknown)))
             ((string=? h "~") (let ((a (t (car args)))) (if (unknown? a) a (pairs-of a (list nil) (lambda ((x strings) (y strings)) (list (reverse x)))))))
             ((string=? h "^") (t (car args)))
             ((string=? h "*") (append (t (car args)) (list (list "univ" "univ"))))
             ((or (string=? h "<:") (string=? h ":>"))
              (let* ((s (t (car args))) (r (t (car (cdr args)))) (dom (string=? h "<:")) (ss (if dom s r)) (rr (if dom r s)))
                (empty-warns (if (or (unknown? ss) (unknown? rr)) t-unknown
                                 (pairs-of rr ss (lambda ((x strings) (y strings))
                                                   (if (overlap? m (if dom (car x) (last-of x)) (car y)) (list x) nil))))
                             (list s r) (string-append h " is irrelevant: the result is always empty"))))
             ((string=? h "if") (begin (tf m (car args) te w where) (append (t (nth d 2)) (t (nth d 3)))))
             ((or (string=? h "prime") (string=? h "quote")) (t (car args)))
             ((string=? h "col") (t (car args)))
             ((string=? h "let") (tc m (nth d 2) (t-let m (items (nth d 1)) te w where) w where))
             ((string=? h "set")
              (let ((te2 (t-decls m (items (car args)) te w where)))
                (begin (tf m (car (cdr args)) te2 w where)
                       (iterate go cb-eff ((ns strings (decl-names (read-decls (items (car args))))) (acc ttype (list nil))) ttype
                         (if (null? ns) acc
                             (go (cdr ns) (pairs-of acc (tc m (sym (car ns)) te2 w where) (lambda ((x strings) (y strings)) (list (append x y))))))))))
             (else
              (begin (ts args)
                     (tagcase (find-def m h)
                       ;; a function's call: its body, its parameters typed by the arguments
                       (some f (if (not (extract f fun)) t-unknown
                                   (letrec ((bind (subr cb-eff (strings datums tenv) tenv)
                                              (lambda (ps as acc) (if (or (null? ps) (null? as)) acc
                                                                      (bind (cdr ps) (cdr as) (cons (product (name (car ps)) (type (t (car as)))) acc))))))
                                     (tc m (extract f body) (bind (decl-names (read-decls (extract f params))) args nil)
                                         (the (arrayof strings @cb) (make-array 1 nil)) ""))))
                       (none u t-unknown)))))))))))

"`let`'s bindings, typed."
(define t-let (subr cb-eff (model datums tenv (arrayof strings @cb) string) tenv)
  (lambda (m bs te w where)
    (if (null? bs) te
        (t-let m (cdr bs) (cons (product (name (name-of (nth (car bs) 0))) (type (tc m (nth (car bs) 1) te w where))) te) w where))))
"Declarations' names, typed by their types."
(define t-decls (subr cb-eff (model datums tenv (arrayof strings @cb) string) tenv)
  (lambda (m ds te w where)
    (iterate go cb-eff ((l (listof decl acyclic) (read-decls ds)) (te tenv te)) tenv
      (if (null? l) te
          (let ((ty (tc m (extract (car l) type) te w where)))
            (go (cdr l) (iterate each ro ((ns strings (extract (car l) names)) (te tenv te)) tenv
                          (if (null? ns) te (each (cdr ns) (cons (product (name (car ns)) (type ty)) te))))))))))

"Formula `d`'s expressions typed, and warned of."
(define tf (subr cb-eff (model datum tenv (arrayof strings @cb) string) unit)
  (lambda (m d te w where)
    (unless (not (pair? d))
      (let* ((h (head d)) (args (cdr (items d))))
        (letrec ((each (subr cb-eff (datums) unit) (lambda (l) (unless (null? l) (tf m (car l) te w where) (each (cdr l)))))
                 (exprs (subr cb-eff (datums) unit) (lambda (l) (unless (null? l) (tc m (car l) te w where) (exprs (cdr l))))))
          (cond
            ((or (string=? h "in") (string=? h "=") (string=? h "!="))
             (let ((a (tc m (car args) te w where)) (b (tc m (car (cdr args)) te w where)))
               (unless (or (null? a) (null? b) (types-overlap? m a b))
                 (array-set! w 0 (cons (string-append "warning: in " (string-append where (string-append ": " (string-append (shown d)
                                                                                                                             ": its left and right are always disjoint"))))
                                       (array-ref w 0))))))
            ((and (member-string? h (list "all" "some" "no" "one" "lone")) (= (list-length args) 2))
             (tf m (car (cdr args)) (t-decls m (items (car args)) te w where) w where))
            ((member-string? h (list "some" "no" "one" "lone" "<" "<=" ">" ">=" "unchanged")) (exprs args))
            ((string=? h "let") (tf m (nth d 2) (t-let m (items (nth d 1)) te w where) w where))
            ((member-string? h (append (list "not" "and" "or" "implies" "=>" "iff" "if") temporal-ops)) (each args))
            (else (tagcase (find-def m h) (some f (exprs args)) (none u #u)))))))))

"A model's warnings: its facts, sigs' facts, fields' types, definitions,
assertions, and commands' formulas, typed."
(define model-warnings (subr cb-eff (model) strings)
  (lambda (m)
    (let ((w (the (arrayof strings @cb) (make-array 1 nil))))
      (begin
        (iterate go cb-eff ((l datums (extract m facts)) (j int 1)) unit
          (unless (null? l) (tf m (car l) nil w (string-append "fact " (int->string j))) (go (cdr l) (+ j 1))))
        (iterate go cb-eff ((l (listof sig-info acyclic) (extract m sigs))) unit
          (unless (null? l)
            (iterate each cb-eff ((k datums (extract (car l) facts))) unit
              (unless (null? k)
                (tf m (car k) (list (product (name "this") (type (list (list (prim-of m (extract (car l) name)))))))
                    w (string-append "sig " (extract (car l) name)))
                (each (cdr k))))
            (go (cdr l))))
        (iterate go cb-eff ((l (listof field-info acyclic) (extract m fields))) unit
          (unless (null? l)
            (unless (string=? (extract (car l) owner) "")
              (iterate each cb-eff ((k datums (extract (car l) cols))) unit
                (unless (null? k)
                  (tc m (unmarked (car k)) (list (product (name "this") (type (list (list (prim-of m (extract (car l) owner)))))))
                      w (string-append "field " (extract (car l) name)))
                  (each (cdr k)))))
            (go (cdr l))))
        (letrec ((go (subr cb-eff ((listof def-info acyclic)) unit)
                   (lambda (l) (if (null? l) #u
                                   (let* ((f (car l)) (where (string-append (if (extract f fun) "fun " (if (extract f event) "event " "pred ")) (extract f name)))
                                          (te (t-decls m (extract f params) nil w where)))
                                     (begin (if (slashed? (extract f name)) #u                   ; a library's, opened #:as: not the model's
                                                (if (extract f fun) (begin (tc m (extract f body) te w where) #u) (tf m (extract f body) te w where)))
                                            (go (cdr l))))))))
          (go (extract m defs)))
        (iterate go cb-eff ((l (listof named acyclic) (extract m asserts))) unit
          (unless (null? l) (tf m (extract (car l) body) nil w (string-append "assert " (extract (car l) name))) (go (cdr l))))
        (iterate go cb-eff ((l datums (extract m commands))) unit
          (unless (null? l)
            (let ((target (nth (car l) 1))) (if (pair? target) (tf m target nil w (string-append (head (car l)) " " (shown target))) #u))
            (go (cdr l))))
        (reverse (array-ref w 0))))))

;;; ------------------------------------------------------------ commands

"A command's formula: for `run`, its predicate, its parameters found
(each a fresh relation, `one` of its type); for `check`, its assertion
false."
(define command-goal (subr ro (model datum) (productof (name string) (check bool) (goal datum) (params datums)))
  (lambda (m d)
    (let ((check (string=? (head d) "check")) (target (nth d 1)))
      (if check
          (let ((a (iterate go ro ((l (listof named acyclic) (extract m asserts))) datum
                     (cond ((null? l) (error (string-append "casing: no assertion " (shown target))))
                           ((string=? (extract (car l) name) (name-of target)) (extract (car l) body))
                           (else (go (cdr l)))))))
            (product (name (name-of target)) (check #t) (goal (the datum (list (sym "not") a))) (params nil)))
          (if (symbol? target)
              (tagcase (find-def m (symbol->string target))
                (none u (error (string-append "casing: no predicate " (shown target))))
                (some f (product (name (extract f name)) (check #f)
                                 (goal (the datum (cons target (iterate syms ro ((l strings (decl-names (read-decls (extract f params))))) datums
                                                                 (if (null? l) nil (cons (sym (car l)) (syms (cdr l))))))))
                                 (params (extract f params)))))
              (product (name "") (check #f) (goal target) (params nil)))))))

"How deep past operators nest in `d`."
(define past-depth (subr ro (datum) int)
  (lambda (d)
    (if (not (pair? d)) 0
        (let ((h (head d))
              (inner (iterate go ro ((l datum d) (m int 0)) int
                       (if (pair? l) (go (cdr l) (max m (past-depth (car l)))) m))))
          (if (or (string=? h "once") (string=? h "historically") (string=? h "before") (string=? h "since") (string=? h "triggered"))
              (+ inner 1) inner)))))
"How deep past operators nest anywhere in a model's facts, predicates,
functions, assertions, and in `goal`."
(define model-past-depth (subr ro (model datum) int)
  (lambda (m goal)
    (letrec ((ds (subr ro (datums int) int) (lambda (l k) (if (null? l) k (ds (cdr l) (max k (past-depth (car l))))))))
      (max (past-depth goal)
           (max (ds (extract m facts) 0)
                (max (iterate go ro ((l (listof def-info acyclic) (extract m defs)) (k int 0)) int
                       (if (null? l) k (go (cdr l) (max k (past-depth (extract (car l) body))))))
                     (iterate go ro ((l (listof named acyclic) (extract m asserts)) (k int 0)) int
                       (if (null? l) k (go (cdr l) (max k (past-depth (extract (car l) body))))))))))))

;;; ------------------------------------------------------------ symmetry

"Tuple `t` (of arity k, over n atoms) with atoms a and b swapped."
(define swapped (subr ro (int int int int int) int)
  (lambda (n k t a b)
    (iterate go ro ((t int t) (j int 0) (acc int 0)) int
      (if (>= j k) acc
          (let* ((d (modulo t n)) (d2 (cond ((= d a) b) ((= d b) a) (else d))))
            (go (quotient t n) (+ j 1) (+ acc (* d2 (power n j)))))))))

"A cell's kind: true 1, false -1, an input (or a gate) 0."
(define cell-kind (subr pure (int) int) (lambda (v) (cond ((= v c-true) 1) ((= v c-false) -1) (else 0))))

"Every matrix of the problem: each relation's, state by state, then each
witness's (a skolem's: Kodkod breaks symmetry on those too)."
(define problem-mats (subr cb-eff (ctx) (listof matrix acyclic))
  (lambda (x)
    (letrec ((mats (subr cb-eff ((arrayof matrix @cb) int (listof matrix acyclic)) (listof matrix acyclic))
               (lambda (ms j acc) (if (>= j (array-length ms)) acc (mats ms (+ j 1) (cons (array-ref ms j) acc)))))
             (rels (subr cb-eff ((listof rel acyclic) (listof matrix acyclic)) (listof matrix acyclic))
               (lambda (l acc) (if (null? l) acc (rels (cdr l) (mats (extract (car l) mats) 0 acc)))))
             (wits (subr cb-eff ((listof witness acyclic) (listof matrix acyclic)) (listof matrix acyclic))
               (lambda (l acc) (if (null? l) acc (wits (cdr l) (cons (extract (car l) val) acc))))))
      (reverse (wits (reverse (array-ref (extract x witnesses) 0)) (rels (extract x rels) nil))))))

"Whether swapping atoms a and b is a symmetry of the problem: it maps each
relation's cells, in every state, and each witness's, to cells of the same
kind (true, false, or an input). A formula cannot name an atom, only relations, so then it
maps each instance to an instance (Kodkod's `SymmetryDetector`, which
refines classes of atoms by the bounds). Int's atoms never are: arithmetic
reads their values."
(define swap-symmetric? (subr cb-eff (ctx (listof matrix acyclic) int int) bool)
  (lambda (x all a b)
    (let ((n (extract x n)))
      (letrec ((mat-ok (subr cb-eff (matrix int) bool)
                 (lambda (m t) (or (>= t (m-size m))
                                   (and (= (cell-kind (m-ref m t)) (cell-kind (m-ref m (swapped n (m-arity m) t a b))))
                                        (mat-ok m (+ t 1))))))
               (mats-ok (subr cb-eff ((listof matrix acyclic)) bool)
                 (lambda (l) (or (null? l) (and (mat-ok (car l) 0) (mats-ok (cdr l)))))))
        (mats-ok all)))))

"Kodkod's lex-leader (`SymmetryBreaker`): for each swap of two
neighbouring atoms that is a symmetry, the cells it moves, in order (each
relation's, state by state, tuple by tuple, then each witness's), read as
a word, true before false, are no greater than their images. Of the
instances that differ only by a permutation of such atoms some instance
satisfies this: the least one. (Either order would do; true first puts an
instance in the first atoms, as Alloy's are.) Only the first `limit`
cells of each word are compared, as Alloy's symmetry setting (20) limits
Kodkod's; 0 breaks nothing.

Only neighbours are tried. Swaps that are symmetries compose, so the atoms
that can be swapped with each other form classes; neighbours find a class
whole only when its atoms are one run (Kodkod refines its classes from
the bounds, wherever their atoms are). The universe makes them so: each
sig's atoms together, a `one` subsig's first. A class split by other atoms
would only lose symmetry broken, not instances, but `check` (the tests')
makes it an error: each run's first atom is tried with every later run's."
(define break-symmetry! (subr cb-eff (ctx int bool) unit)
  (lambda (x limit check)
    (let* ((n (extract x n)) (c (cx x))
           (top (if (< (extract x ibase) 0) n (extract x ibase)))   ; Int's atoms are last
           (all (problem-mats x)))
      (letrec ((moved (subr cb-eff ((listof matrix acyclic) int int int ints ints) (productof (xs ints) (ys ints)))
                 ;; the cells swapping a and b moves, and their images: from
                 ;; matrix l's cell t on, up to `limit` in all
                 (lambda (l t a b xs ys)
                   (cond ((or (null? l) (>= (list-length xs) limit)) (product (xs (reverse xs)) (ys (reverse ys))))
                         ((>= t (m-size (car l))) (moved (cdr l) 0 a b xs ys))
                         (else
                          (let* ((m (car l)) (v (m-ref m t)) (w (m-ref m (swapped n (m-arity m) t a b))))
                            (if (or (not (= (cell-kind v) 0)) (= v w))
                                (moved l (+ t 1) a b xs ys)
                                (moved l (+ t 1) a b (cons v xs) (cons w ys))))))))
               ;; xs ≤ ys as words, true first, given that the cells before are equal (e)
               (leq! (subr cb-eff (ints ints int) unit)
                 (lambda (xs ys e)
                   (unless (or (null? xs) (null? ys))
                     (c-assert! c (c-implies c e (c-implies c (car ys) (car xs))))
                     (leq! (cdr xs) (cdr ys) (c-and2 c e (c-iff c (car xs) (car ys)))))))
               ;; from atom a on, each neighbour swap that is a symmetry
               ;; broken; the first atom of each run, in reverse
               (each (subr cb-eff (int ints) ints)
                 (lambda (a starts)
                   (if (>= (+ a 1) top) starts
                       (if (swap-symmetric? x all a (+ a 1))
                           (begin (if (> limit 0)
                                      (let ((p (moved all 0 a (+ a 1) nil nil)))
                                        (leq! (extract p xs) (extract p ys) c-true))
                                      #u)
                                  (each (+ a 1) starts))
                           (each (+ a 1) (cons (+ a 1) starts))))))
               ;; no run's first atom (a) swaps with a later one's
               (apart! (subr cb-eff (ints ints) unit)
                 (lambda (l bs)
                   (cond ((null? l) #u)
                         ((null? bs) (unless (null? (cdr l)) (apart! (cdr l) (cdr (cdr l)))))
                         ((swap-symmetric? x all (car l) (car bs))
                          (error (string-append "casing: atoms " (string-append (int->string (car l))
                                   (string-append " and " (string-append (int->string (car bs))
                                     " are symmetric but not neighbours: their symmetry is not broken"))))))
                         (else (apart! l (cdr bs)))))))
        (let ((starts (if (or (> limit 0) check) (each 0 (if (> top 0) (list 0) nil)) nil)))
          (if check (let ((l (reverse starts))) (unless (null? l) (apart! l (cdr l)))) #u))))))

;;; ------------------------------------------------------------ more instances

(define-type truths (listof bool acyclic))
"An instance found, as values: each static relation's cells and each
witness's (`statics`), each state's cells of the relations that change
(`states`), its states and where its loop goes back to. Instances are
told apart by these, as Alloy tells them: two that differ only in a
skolem's value are two."
(define-type snapshot (productof (statics (listof truths acyclic)) (states (listof (listof truths acyclic) acyclic)) (k int) (loop int)))

"A problem's matrices that do not change (static relations', then the
witnesses'), and those of state i of the relations that do."
(define static-mats (subr cb-eff (ctx) (listof matrix acyclic))
  (lambda (x)
    (letrec ((rels (subr cb-eff ((listof rel acyclic)) (listof matrix acyclic))
               (lambda (l) (cond ((null? l) nil) ((extract (car l) var) (rels (cdr l)))
                                 (else (cons (array-ref (extract (car l) mats) 0) (rels (cdr l)))))))
             (wits (subr cb-eff ((listof witness acyclic)) (listof matrix acyclic))
               (lambda (l) (if (null? l) nil (cons (extract (car l) val) (wits (cdr l)))))))
      (append (rels (extract x rels)) (wits (reverse (array-ref (extract x witnesses) 0)))))))
(define state-mats (subr cb-eff (ctx int) (listof matrix acyclic))
  (lambda (x i)
    (iterate rels cb-eff ((l (listof rel acyclic) (extract x rels))) (listof matrix acyclic)
      (cond ((null? l) nil)
            ((extract (car l) var) (cons (array-ref (extract (car l) mats) i) (rels (cdr l))))
            (else (rels (cdr l)))))))

"The instance just found in `x`."
(define snapshot-of (subr cb-eff (ctx) snapshot)
  (lambda (x)
    (let ((c (cx x)) (k (extract x k)))
      (letrec ((vals (subr cb-eff (matrix int) truths)
                 (lambda (m t) (if (>= t (m-size m)) nil (cons (c-value c (m-ref m t)) (vals m (+ t 1))))))
               (all (subr cb-eff ((listof matrix acyclic)) (listof truths acyclic))
                 (lambda (l) (if (null? l) nil (cons (vals (car l) 0) (all (cdr l))))))
               (states (subr cb-eff (int) (listof (listof truths acyclic) acyclic))
                 (lambda (i) (if (>= i k) nil (cons (all (state-mats x i)) (states (+ i 1))))))
               (loop (subr cb-eff (int) int)
                 (lambda (l) (if (or (>= l k) (c-value c (loop-at x l))) l (loop (+ l 1))))))
        (product (statics (all (static-mats x))) (states (states 0)) (k k) (loop (loop 0)))))))

"The cells of matrices `ms` as `vss` has them, one literal each (true
for a cell that is true in vss, its negation if false)."
(define alike (subr cb-eff ((listof matrix acyclic) (listof truths acyclic) ints) ints)
  (lambda (ms vss acc)
    (letrec ((lits (subr cb-eff (matrix truths int ints) ints)
               (lambda (m vs t acc) (if (null? vs) acc
                                        (lits m (cdr vs) (+ t 1) (cons (if (car vs) (m-ref m t) (c-not (m-ref m t))) acc))))))
      (if (or (null? ms) (null? vss)) acc (alike (cdr ms) (cdr vss) (lits (car ms) (car vss) 0 acc))))))

"In `x`, the configuration is `s`'s: each static relation, and witness,
as it has them."
(define fix-statics! (subr cb-eff (ctx snapshot) unit)
  (lambda (x s) (c-assert! (cx x) (c-and (cx x) (alike (static-mats x) (extract s statics) nil)))))

"Which state of a lasso of k states, its loop back to l, is at position p
of the trace it makes."
(define lasso-state (subr pure (int int int) int)
  (lambda (p k l) (if (< p k) p (+ l (modulo (- p l) (- k l))))))

"In `x`, the instance `s` is not to be found again: not as the same
lasso, nor as another lasso that makes the same trace. Some static cell
differs; or, wherever x's loop goes back to, some state of the trace it
makes differs from s's at the same position. Two lassos, of k and k'
states with loops of p and p', make the same trace if they agree at its
first max(k, k') + lcm(p, p') positions (each is periodic from there).
For a model that does not change: some cell differs."
(define block-snapshot! (subr cb-eff (ctx snapshot) unit)
  (lambda (x s)
    (let* ((c (cx x)) (k2 (extract x k)) (k1 (extract s k)) (l1 (extract s loop)))
      (letrec ((state-of (subr spin ((listof (listof truths acyclic) acyclic) int) (listof truths acyclic))
                 (lambda (l i) (cond ((null? l) nil) ((= i 0) (car l)) (else (state-of (cdr l) (- i 1))))))
               ;; x's loop back to l2: at each position, the states alike
               (positions (subr cb-eff (int int int ints) ints)
                 (lambda (l2 p top acc)
                   (if (>= p top) acc
                       (positions l2 (+ p 1) top
                                  (alike (state-mats x (lasso-state p k2 l2)) (state-of (extract s states) (lasso-state p k1 l1)) acc)))))
               (loops (subr cb-eff (int ints) ints)
                 (lambda (l2 acc)
                   (if (>= l2 k2) acc
                       (loops (+ l2 1)
                              (cons (c-and c (cons (loop-at x l2) (positions l2 0 (+ (max k1 k2) (lcm (- k1 l1) (- k2 l2))) nil)))
                                    acc))))))
        (c-assert! c (c-not (c-and2 c (c-and c (alike (static-mats x) (extract s statics) nil))
                                      (c-or c (loops 0 nil)))))))))

"How a command is run, beyond its scope: how many instances to show
(`#:instances n`, 0 if not said: the first), whether to count them all
(`#:count`), at most how many to find (`#:limit n`, 0 if not said: no
limit), and how much symmetry to break (`#:symmetry n`: the length of
each lex-leader predicate; 0, none), and whether to check that its
symmetries are all found (`check`, the tests'). The command line says them for every
command (`casing --instances n`); a command's own say wins."
(define-type settings (productof (instances int) (count bool) (limit int) (symmetry int) (check bool)))
(define default-settings settings (product (instances 0) (count #f) (limit 0) (symmetry 20) (check #f)))
(define with-instances (subr pure (settings int) settings)
  (lambda (s n) (product (instances n) (count (extract s count)) (limit (extract s limit)) (symmetry (extract s symmetry)) (check (extract s check)))))
(define with-count (subr pure (settings) settings)
  (lambda (s) (product (instances (extract s instances)) (count #t) (limit (extract s limit)) (symmetry (extract s symmetry)) (check (extract s check)))))
(define with-limit (subr pure (settings int) settings)
  (lambda (s n) (product (instances (extract s instances)) (count (extract s count)) (limit n) (symmetry (extract s symmetry)) (check (extract s check)))))
(define with-symmetry (subr pure (settings int) settings)
  (lambda (s n) (product (instances (extract s instances)) (count (extract s count)) (limit (extract s limit)) (symmetry n) (check (extract s check)))))
"For the tests (`casing --check-symmetry`): that neighbouring atoms find all
the symmetry there is (see `break-symmetry!`)."
(define with-check (subr pure (settings) settings)
  (lambda (s) (product (instances (extract s instances)) (count (extract s count)) (limit (extract s limit)) (symmetry (extract s symmetry)) (check #t))))

"A command's items after its target: its scope, and its settings."
(define command-options (subr ro (datums settings) (productof (specs datums) (settings settings)))
  (lambda (l s)
    (letrec ((num (subr ro (datums string) int)
               (lambda (l k) (let ((bad (lambda () (error (string-append "casing: #:" (string-append k " N, N a whole number"))))))
                               (if (pair? l)
                                   (let ((d (car l))) (if (and (datum-int? d) (>= d 0)) d (bad)))
                                   (bad)))))
             (go (subr ro (datums datums settings) (productof (specs datums) (settings settings)))
               (lambda (l specs s)
                 (cond ((null? l) (product (specs (reverse specs)) (settings s)))
                       ((not (keyword? (car l))) (go (cdr l) (cons (car l) specs) s))
                       ((string=? (option-name (car l)) "instances") (go (cdr (cdr l)) specs (with-instances s (num (cdr l) "instances"))))
                       ((string=? (option-name (car l)) "limit") (go (cdr (cdr l)) specs (with-limit s (num (cdr l) "limit"))))
                       ((string=? (option-name (car l)) "symmetry") (go (cdr (cdr l)) specs (with-symmetry s (num (cdr l) "symmetry"))))
                       ((string=? (option-name (car l)) "count") (go (cdr l) specs (with-count s)))
                       (else (error (string-append "casing: what option is this? " (shown (car l)))))))))
      (go l nil s))))

"After the first instance, said as `first`: the next ones, each found by
blocking those before (Alloy's \"next\", Kodkod's `SolutionIterator`):
up to `#:instances` shown, all counted if `#:count`, and no more than
`#:limit` found. A model that changes has its traces found as Alloy's
\"next\" finds them (Pardinus's `nextP`): of the first's configuration
(its static relations and witnesses as they are), when no other trace of
k states is left, one of k+1, up to the scope's most steps (`most`); each
a trace not found before, whatever lasso it was found as. `setup k` makes
the problem of k states."
(define more-instances (subr cb-eff ((subr cb-eff (int) ctx) int ctx settings bool bool string) string)
  (lambda (setup most x0 st check temporal first)
    (let ((want (extract st instances)) (counting (extract st count)) (limit (extract st limit)))
      (if (and (= want 0) (not counting)) first
          (let* ((noun (if check "counterexample" "instance"))
                 (some-of (lambda ((i int)) (string-append (int->string i) (string-append " " (if (= i 1) noun (string-append noun "s"))))))
                 (traces (if temporal (string-append " (traces of up to " (string-append (int->string most) (if (= most 1) " state, of the first's configuration)" " states, of the first's configuration)"))) ""))
                 (said (lambda ((x ctx) (i int))
                         (let ((s (instance-shown x)) (k (extract x k)))
                           (string-append noun (string-append " " (string-append (int->string i)
                             (string-append (if temporal (string-append ", " (string-append (int->string k) (if (= k 1) " state" " states"))) "")
                                            (string-append ":" (if (string=? s "") "" (string-append "\n" s)))))))))))
            (letrec ((finish (subr cb-eff (int strings bool) string)
                       (lambda (i shown more)
                         (string-join (cons first (reverse (cons (if counting (if more (string-append "at least " (string-append (some-of i) traces))
                                                                                  (string-append (some-of i) (string-append " in all" traces)))
                                                                     (string-append (some-of i) (string-append traces (if more "; there are more" ", and no more"))))
                                                                 shown)))
                                      "\n")))
                     ;; blocked, and for a trace, the first's configuration kept
                     (block-all! (subr cb-eff (ctx (listof snapshot acyclic)) unit)
                       (lambda (x l) (unless (null? l)
                                       (if (and temporal (null? (cdr l))) (fix-statics! x (car l)) #u)
                                       (block-snapshot! x (car l)) (block-all! x (cdr l)))))
                     ;; the next instance: in x, or in a longer trace's problem
                     (advance (subr cb-eff (ctx (listof snapshot acyclic)) (sumof (none unit) (some ctx)))
                       (lambda (x found)
                         (cond ((c-solve! (cx x) nil) (sum some x))
                               ((and temporal (< (extract x k) most))
                                (let ((x2 (setup (+ (extract x k) 1))))
                                  (begin (block-all! x2 found) (advance x2 found))))
                               (else (sum none #u)))))
                     ;; i found, the last just now in x; `shown`, the 2nd on, newest first
                     (go (subr cb-eff (ctx int strings (listof snapshot acyclic)) string)
                       (lambda (x i shown found0)
                         (let* ((s (snapshot-of x)) (found (cons s found0)))
                           (begin
                             (if (and temporal (null? found0)) (fix-statics! x s) #u)
                             (block-snapshot! x s)
                             (if (or (and (not counting) (>= i want)) (and (> limit 0) (>= i limit)))
                                 (finish i shown (tagcase (advance x found) (some y #t) (none u #f)))
                                 (tagcase (advance x found)
                                   (none u (finish i shown #f))
                                   (some y (go y (+ i 1) (if (< i want) (cons (said y (+ i 1)) shown) shown) found)))))))))
              (go x0 1 nil nil)))))))

"A command run: what it found, said."
(define run-command (subr cb-eff (model datum settings) string)
  (lambda (m d s0)
    (let* ((g (command-goal m d))
           (opts (command-options (cdr (cdr (items d))) s0))
           (st (extract opts settings))
           (sc (read-scope m (extract opts specs)))
           (bw (tagcase (scope-of sc "Int")
                 (some e (if (and (>= (extract e count) 1) (<= (extract e count) 8)) (extract e count)
                             (error "casing: Int's bitwidth is from 1 to 8")))
                 (none u 4)))
           (u (if (or (model-mentions? m "Int") (mentions? d "Int")) (with-int-atoms (make-universe m sc) bw) (make-universe m sc)))
           ;; a run's parameters become relations of their own, of their
           ;; type and multiplicity (and apart, if #:disj), as Alloy skolemizes
           (m2 (iterate go ro ((ds (listof decl acyclic) (read-decls (extract g params))) (m model m)) model
                 (if (null? ds) m
                     (let* ((dc (car ds)) (t (field-type (extract dc type)))
                            (mult (cond ((not (string=? (extract dc mult) "")) (extract dc mult))
                                        ((= (list-length (extract t cols)) 1) "one") (else "set")))
                            (dollar (lambda ((nm string)) (sym (string-append "$" nm)))))
                       (iterate each ro ((ns strings (extract dc names)) (before strings nil) (m model m)) model
                         (if (null? ns) (go (cdr ds) m)
                             (let ((nm (car ns)))
                               (each (cdr ns) (cons nm before)
                                     (product (sigs (extract m sigs))
                                              (fields (append (extract m fields)
                                                              (list (product (name (string-append "$" nm)) (owner "")
                                                                             (cols (extract t cols)) (mult "set") (var #f) (region "") (apart #f)))))
                                              (facts (append (if (string=? mult "set") nil (list (the datum (list (sym mult) (dollar nm)))))
                                                             (append (if (extract dc disj)
                                                                         (iterate apart ro ((l strings before)) datums
                                                                           (if (null? l) nil
                                                                               (cons (the datum (list (sym "no") (list (sym "inter") (dollar nm) (dollar (car l)))))
                                                                                     (apart (cdr l)))))
                                                                         nil)
                                                                     (extract m facts))))
                                              (defs (extract m defs)) (asserts (extract m asserts)) (commands (extract m commands)))))))))))
           (goal (if (null? (extract g params)) (extract g goal)
                     ;; (p x y) with x y the fresh relations
                     (the datum (cons (car (items (extract g goal)))
                                      (iterate go ro ((l datums (cdr (items (extract g goal))))) datums
                                        (if (null? l) nil (cons (sym (string-append "$" (name-of (car l)))) (go (cdr l)))))))))
           (decls (declaration-facts m2))
           (temporal (any-var? m))
           (what (string-append (if (extract g check) "check " "run ") (if (string=? (extract g name) "") (shown (nth d 1)) (extract g name)))))
      (letrec ((setup (subr cb-eff (int) ctx)
                 ;; the problem of k states: what is asserted, symmetry broken
                 (lambda (k)
                   (let* ((x (make-ctx m2 u k (+ 1 (model-past-depth m2 goal)) bw)) (c (cx x)))
                     (begin
                       (letrec ((each (subr cb-eff (datums bool) unit)
                                  (lambda (l always) (unless (null? l)
                                                       (c-assert! c (form x (if always (the datum (list (sym "always") (car l))) (car l)) 0 nil))
                                                       (each (cdr l) always)))))
                         (begin (each decls temporal)
                                (each (extract u facts) temporal)
                                (each (extract m2 facts) #f)
                                (each (list goal) #f)))
                       ;; after translating, so that the witnesses are there
                       (break-symmetry! x (extract st symmetry) (extract st check))
                       x))))
               (try (subr cb-eff (int) string)
                 (lambda (k)
                   (if (> k (extract sc max-steps))
                       (string-append what (string-append (if (extract g check) ": no counterexample found" ": no instance found")
                                                          (scope-said sc temporal)))
                       (let ((x (setup k)))
                         (if (c-solve! (cx x) nil)
                             (more-instances setup (extract sc max-steps) x st (extract g check) temporal
                               (string-append what (string-append (if (extract g check) ": counterexample found" ": instance found")
                                                                  (string-append (scope-said sc temporal)
                                                                                 (string-append (if temporal (string-append ", " (string-append (int->string k) (if (= k 1) " state" " states"))) "")
                                                                                                (let ((shown (instance-shown x))) (if (string=? shown "") "" (string-append "\n" shown))))))))
                             (try (+ k 1))))))))
        (try (extract sc min-steps))))))

(define scope-said (subr ro (scope bool) string)
  (lambda (s temporal)
    (string-append " (scope " (string-append (int->string (extract s default))
                                             (string-append (string-join (iterate go ro ((l (listof scope-entry acyclic) (reverse (extract s sigs)))) strings
                                                                           (if (null? l) nil
                                                                               (cons (string-append (if (extract (car l) exact) ", exactly " ", ")
                                                                                                    (string-append (int->string (extract (car l) count)) (string-append " " (extract (car l) name))))
                                                                                     (go (cdr l)))))
                                                                         "")
                                                            (string-append (if temporal (string-append ", steps " (string-append (int->string (extract s min-steps)) (string-append ".." (int->string (extract s max-steps))))) "")
                                                                           ")"))))))

"A model's warnings (its types), then every command, in order, each one's
answer."
(define run-model (subr cb-eff (model) strings) (lambda (m) (run-model-with m default-settings)))
"As `run-model`, each command run with settings `s` but for what it says."
(define run-model-with (subr cb-eff (model settings) strings)
  (lambda (m s) (letrec ((go (subr cb-eff (datums) strings) (lambda (l) (if (null? l) nil (cons (run-command m (car l) s) (go (cdr l)))))))
                  (append (model-warnings m) (go (extract m commands))))))
