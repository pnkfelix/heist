;;; fx26.fx: FX-26 for the CFA -- its text read by Fixpt's own reader
;;; (`fx26:eager-reader.fx`) and turned into the core (core.fx), as
;;; editor/flow.fx's desugarer does; and FX-26 as a language (`cf-fx26`).
;;;
;;; Types are erased: `plambda`'s body, `proj`'s and `the`'s expression.
;;; A name the world defines nowhere is a standard procedure, a primitive:
;;; FX-26's types make nearly all of them first order -- their results hold
;;; no closure, and what they are given does not escape -- where yank had to
;;; model 330 lines of Scheme's. The few higher-order ones make what they
;;; are given escape; the few that pass their arguments on, pass them.

(define cf-reader ((proj (load-module "fx26:eager-reader.fx") @cs @ce @cm @cc)))
(import cf-reader eager-start-fx26 eager-feed-string eager-feed eager-state-syntax atom lst dotted vec (type syn syns))
(define-effect cf-reader-eff
  (maxeff (read @cs) (write @cs) (alloc @cs) (read @cm) (write @cm) (alloc @cm)
          (read @cc) (write @cc) (alloc @cc) (read @ce) (goto @ce) (comefrom @ce)))
(define-effect fx-eff (maxeff cf-eff cf-reader-eff))

"FX-26's standard procedures that call what they are given, or keep it
where code not known may; and those whose result holds their arguments'
elements."
(define fx-higher-order strings
  (list "apply" "call-with-composable-continuation" "call-with-oneshot-continuation"
        "abort-current-continuation" "with-mark" "cwcc" "%vlambda"))
(define fx-passing strings (list "reverse" "append" "datum-list"))

(define cf-fx26 cf-lang
  (product (name "fx26")
           (model (lambda ((n string))
                    (cond ((cf-member? n fx-higher-order) (m-data #t (list "unknown")))
                          ((cf-member? n fx-passing) (m-pass))
                          (else (m-data #f nil)))))))

"Text `text` read: its forms (as far as they read)."
(define* fx-read (subr (maxeff cf-reader-eff spin) (string) (listof syn acyclic))
  (lambda (text) (eager-state-syntax (eager-feed (eager-feed-string (eager-start-fx26) text) #\newline))))

;;; ------------------------------------------------------------ the syntax, read as core

"A local scope: names and their variables, innermost first."
(define-type scope (listof (productof (name string) (var int)) acyclic))
(define* scope-var (subr spin (scope string) int)
  (lambda (env n) (cond ((null? env) -1)
                        ((string=? (extract (car env) name) n) (extract (car env) var))
                        (else (scope-var (cdr env) n)))))
(define* fx-sym (subr spin (syn) string)
  (lambda (x) (tagcase x (atom (d a b) (typecase d (symbol s (symbol->string s)) (else y ""))) (else y ""))))
(define* fx-items (subr spin (syn) (listof syn acyclic))
  (lambda (x) (tagcase x (lst (i d a b) i) (else y nil))))
(define* fx-span (subr spin (int syn) cf-span)
  (lambda (file x)
    (tagcase x
      (atom (d a b) (product (file file) (start a) (end b)))
      (lst (i d a b) (product (file file) (start a) (end b)))
      (dotted (i t d a b) (product (file file) (start a) (end b)))
      (vec (i d a b) (product (file file) (start a) (end b))))))
"A parameter's name: `x`, or `(x type)`'s `x`."
(define* fx-param-name (subr spin (syn) string)
  (lambda (p) (let ((is (fx-items p))) (if (pair? is) (fx-sym (car is)) (fx-sym p)))))
(define* fx-last (subr spin ((listof syn acyclic)) syn)
  (lambda (l) (if (null? (cdr l)) (car l) (fx-last (cdr l)))))
(define* fx-append (subr spin (cores cores) cores)
  (lambda (a b) (if (null? a) b (cons (car a) (fx-append (cdr a) b)))))
"The kind of a literal."
(define* fx-literal-kind (subr spin (syn) string)
  (lambda (x)
    (tagcase x
      (atom (d a b) (typecase d (int i "int") (string s "string") (char c "char") (bool b "bool") (f64 r "f64") (else y "datum")))
      (else y "datum"))))

"Constructor `tag` of `n` fields, of variant syntax `x`: the global bound
to a lambda making `(sum tag (product (1 p1) … (n pn)))`."
(define* fx-constructor (subr fx-eff (int syn string int) core)
  (lambda (file x tag n)
    (let* ((params (letrec ((go (subr fx-eff (int) ints) (lambda (i) (if (>= i n) nil (cons (cf-new-var) (go (+ i 1)))))))
                     (go 0)))
           (fields (letrec ((go (subr fx-eff (ints int) (listof field-init acyclic))
                              (lambda (ps i) (if (null? ps) nil
                                                 (cons (product (label (int->string i)) (value (k-var (car ps) -1)))
                                                       (go (cdr ps) (+ i 1)))))))
                     (go params 1)))
           (body (k-alloc (cf-add-site (product (span (fx-span file x)) (kind "sum") (tag tag)))
                          (list (product (label "payload")
                                         (value (k-alloc (cf-add-site (product (span (fx-span file x)) (kind "product") (tag "")))
                                                         fields)))))))
      (k-bind (cf-global-var tag)
              (k-lam (cf-add-lambda (product (span (fx-span file x)) (name tag) (params params) (rest -1) (body body))))))))

(define-rec
  ;; Form `x` of file `file`, in scope `env`, as core.
  (fx-core (subr fx-eff (int syn scope) core)
    (lambda (file x env)
      (tagcase x
        (atom (d a b)
          (let ((n (fx-sym x)))
            (cond ((string=? n "") (k-const (cf-kind (fx-literal-kind x))))
                  ((>= (scope-var env n) 0) (cf-ref (scope-var env n) n (fx-span file x)))
                  ((cf-global-defined? n) (cf-ref (cf-global-var n) n (fx-span file x)))
                  ;; Defined nowhere in the world: a standard value.
                  (else (k-prim n)))))
        (lst (items d a b)
          (if (null? items) (k-none nil) (fx-form file x (fx-sym (car items)) (cdr items) env)))
        (else y (k-none nil)))))
  (fx-all (subr fx-eff (int (listof syn acyclic) scope) cores)
    (lambda (file xs env) (if (null? xs) nil (let ((c (fx-core file (car xs) env))) (cons c (fx-all file (cdr xs) env))))))
  (fx-body (subr fx-eff (int (listof syn acyclic) scope) core)
    (lambda (file xs env) (k-seq (fx-all file xs env))))
  ;; A list whose head is the symbol `head` ("" if it is not one).
  (fx-form (subr fx-eff (int syn string (listof syn acyclic) scope) core)
    (lambda (file x head rest env)
      (let ((site (lambda ((kind string) (tag string)) (cf-add-site (product (span (fx-span file x)) (kind kind) (tag tag)))))
            (one (lambda () (if (pair? rest) (fx-core file (car rest) env) (k-none nil))))
            (two? (and (pair? rest) (pair? (cdr rest)))))
        (cond
          ((or (string=? head "quote") (string=? head "quasiquote")) (k-const (cf-kind "datum")))
          ((string=? head "lambda")
           (if (pair? rest) (fx-lambda file x "" (fx-items (car rest)) (cdr rest) env) (k-none nil)))
          ((string=? head "vlambda")
           (if (pair? rest)
               (let* ((v (cf-new-var))
                      (body (fx-body file (cdr rest) (cons (product (name (fx-param-name (car rest))) (var v)) env))))
                 (k-lam (cf-add-lambda (product (span (fx-span file x)) (name (cf-anonymous)) (params nil) (rest v) (body body)))))
               (k-none nil)))
          ;; Types are erased: `plambda`'s body, `proj`'s and `the`'s expression.
          ((string=? head "plambda") (fx-body file (if (pair? rest) (cdr rest) nil) env))
          ((string=? head "proj") (one))
          ((string=? head "the") (if two? (fx-core file (car (cdr rest)) env) (k-none nil)))
          ((or (string=? head "letregion") (string=? head "letrena") (string=? head "letreap") (string=? head "letfreeze"))
           (fx-body file (if (pair? rest) (cdr rest) nil) env))
          ((string=? head "if")
           (if (pair? rest) (k-seq (list (fx-core file (car rest) env) (k-alt (fx-all file (cdr rest) env)))) (k-none nil)))
          ((or (string=? head "and") (string=? head "or")) (k-alt (fx-all file rest env)))
          ((string=? head "begin") (fx-body file rest env))
          ((string=? head "cond")
           (k-alt (letrec ((clauses (subr fx-eff ((listof syn acyclic)) cores)
                             (lambda (cs) (if (null? cs) nil
                                              (let ((is (fx-items (car cs))))
                                                (cons (if (and (pair? is) (string=? (fx-sym (car is)) "else"))
                                                          (fx-body file (cdr is) env)
                                                          (fx-body file is env))
                                                      (clauses (cdr cs))))))))
                    (clauses rest))))
          ((string=? head "case")
           (if (pair? rest)
               (k-seq (list (fx-core file (car rest) env)
                            (k-alt (letrec ((clauses (subr fx-eff ((listof syn acyclic)) cores)
                                              (lambda (cs) (if (null? cs) nil
                                                               (let ((is (fx-items (car cs))))
                                                                 (cons (fx-body file (if (pair? is) (cdr is) nil) env)
                                                                       (clauses (cdr cs))))))))
                                     (clauses (cdr rest))))))
               (k-none nil)))
          ((or (string=? head "let") (string=? head "let*") (string=? head "letrec"))
           (if (pair? rest) (fx-let file head (fx-items (car rest)) (cdr rest) env) (k-none nil)))
          ((string=? head "product")
           (k-alloc (site "product" "")
                    (letrec ((fields (subr fx-eff ((listof syn acyclic)) (listof field-init acyclic))
                               (lambda (fs) (if (null? fs) nil
                                                (let ((is (fx-items (car fs))))
                                                  (if (and (pair? is) (pair? (cdr is)))
                                                      (cons (product (label (fx-sym (car is))) (value (fx-core file (car (cdr is)) env)))
                                                            (fields (cdr fs)))
                                                      (fields (cdr fs))))))))
                      (fields rest))))
          ((string=? head "extract") (if two? (k-field (fx-core file (car rest) env) (fx-sym (car (cdr rest)))) (k-none nil)))
          ((string=? head "sum")
           (if two?
               (k-alloc (site "sum" (fx-sym (car rest))) (list (product (label "payload") (value (fx-core file (car (cdr rest)) env)))))
               (k-none nil)))
          ((string=? head "new") (k-alloc (site "ref" "") (list (product (label "contents") (value (one))))))
          ((string=? head "get") (if (pair? rest) (k-field (one) "contents") (k-none nil)))
          ((string=? head "set")
           (if two? (k-store (fx-core file (car rest) env) "contents" (fx-core file (car (cdr rest)) env)) (k-none nil)))
          ((string=? head "cons")
           (if two?
               (k-alloc (site "pair" "")
                        (list (product (label "car") (value (fx-core file (car rest) env)))
                              (product (label "cdr") (value (fx-core file (car (cdr rest)) env)))))
               (k-none nil)))
          ((string=? head "car") (if (pair? rest) (k-field (one) "car") (k-none nil)))
          ((string=? head "cdr") (if (pair? rest) (k-field (one) "cdr") (k-none nil)))
          ;; A list of its elements: one pair site, its cdr itself.
          ((string=? head "list")
           (let ((s (site "pair" "")))
             (k-alloc s (list (product (label "car") (value (k-alt (fx-all file rest env))))
                              (product (label "cdr") (value (k-alt (list (k-const (cf-kind "null")) (k-alloc s nil)))))))))
          ((string=? head "tagcase") (if (pair? rest) (fx-tagcase file (car rest) (cdr rest) env) (k-none nil)))
          ((string=? head "typecase")
           (if (pair? rest)
               (let ((subject (fx-core file (car rest) env)) (v (cf-new-var)))
                 (k-seq (list (k-bind v subject)
                              (k-alt (letrec ((arms (subr fx-eff ((listof syn acyclic)) cores)
                                                (lambda (as) (if (null? as) nil
                                                                 (let ((is (fx-items (car as))))
                                                                   (cons (if (and (pair? is) (pair? (cdr is)))
                                                                             (fx-body file (cdr (cdr is))
                                                                                      (cons (product (name (fx-sym (car (cdr is)))) (var v)) env))
                                                                             (k-none nil))
                                                                         (arms (cdr as))))))))
                                       (arms (cdr rest)))))))
               (k-none nil)))
          ;; Definitions: a global's variable given the value.
          ((or (string=? head "define") (string=? head "define*"))
           (if two?
               (let* ((name (fx-sym (car rest)))
                      (value-syn (car (if (pair? (cdr (cdr rest))) (cdr (cdr rest)) (cdr rest))))
                      (value (begin (if (null? env) (set cf-definition name) #u) (fx-named file value-syn name env))))
                 (k-bind (cf-global-var name) value))
               (k-none nil)))
          ((string=? head "define-rec")
           (k-seq (letrec ((go (subr fx-eff ((listof syn acyclic)) cores)
                             (lambda (bs) (if (null? bs) nil
                                              (let ((is (fx-items (car bs))))
                                                (if (and (pair? is) (pair? (cdr is)) (pair? (cdr (cdr is))))
                                                    (let ((b (k-bind (cf-global-var (fx-sym (car is)))
                                                                     (begin (if (null? env) (set cf-definition (fx-sym (car is))) #u)
                                                                       (fx-named file (car (cdr (cdr is))) (fx-sym (car is)) env)))))
                                                      (cons b (go (cdr bs))))
                                                    (go (cdr bs))))))))
                    (go rest))))
          ;; `(define-datatype t (tag T …) …)`: each tag a global constructor.
          ((string=? head "define-datatype")
           (k-seq (letrec ((variants (subr fx-eff ((listof syn acyclic)) cores)
                             (lambda (vs) (if (null? vs) nil
                                              (let ((is (fx-items (car vs))))
                                                (if (pair? is)
                                                    (let ((c (fx-constructor file (car vs) (fx-sym (car is)) (length (cdr is)))))
                                                      (cons c (variants (cdr vs))))
                                                    (variants (cdr vs))))))))
                    (variants (if (pair? rest) (cdr rest) nil)))))
          ((or (string=? head "define-type") (string=? head "define-effect")
               (string=? head "define-generative") (string=? head "import") (string=? head "module-parameters"))
           (k-none nil))
          ((or (string=? head "module") (string=? head "hide")) (fx-body file rest env))
          ;; `(with m x)`: x, by name.
          ((string=? head "with") (fx-body file (if (pair? rest) (cdr rest) nil) env))
          (else
           (let ((op (if (pair? (fx-items x)) (car (fx-items x)) x)))
             (let* ((f (fx-core file op env)) (args (fx-all file rest env)))
               (k-app (cf-add-call (product (span (fx-span file x)) (operator (fx-span file op)))) f args))))))))
  ;; A definition's value, a lambda named for it.
  (fx-named (subr fx-eff (int syn string scope) core)
    (lambda (file x name env)
      (let ((is (fx-items x)))
        (if (and (pair? is) (string=? (fx-sym (car is)) "lambda") (pair? (cdr is)))
            (fx-lambda file x name (fx-items (car (cdr is))) (cdr (cdr is)) env)
            (fx-core file x env)))))
  (fx-lambda (subr fx-eff (int syn string (listof syn acyclic) (listof syn acyclic) scope) core)
    (lambda (file x name params body env)
      (letrec ((bind (subr fx-eff ((listof syn acyclic) scope ints) core)
                 (lambda (ps env vs)
                   (if (null? ps)
                       (let ((b (fx-body file body env)))
                         (k-lam (cf-add-lambda (product (span (fx-span file x)) (name (if (string=? name "") (cf-anonymous) name))
                                                        (params (cf-reverse-ints vs)) (rest -1) (body b)))))
                       (let ((v (cf-new-var)))
                         (bind (cdr ps) (cons (product (name (fx-param-name (car ps))) (var v)) env) (cons v vs)))))))
        (bind params env nil))))
  ;; `let`: values outside; `let*`: each sees those before; `letrec`: all see all.
  (fx-let (subr fx-eff (int string (listof syn acyclic) (listof syn acyclic) scope) core)
    (lambda (file kind bs body env)
      (let* ((names (letrec ((go (subr spin ((listof syn acyclic)) strings)
                               (lambda (bs) (if (null? bs) nil (cons (fx-param-name (car bs)) (go (cdr bs)))))))
                      (go bs)))
             (vars (letrec ((go (subr fx-eff (strings) ints) (lambda (ns) (if (null? ns) nil (cons (cf-new-var) (go (cdr ns)))))))
                     (go names)))
             (inner (letrec ((go (subr spin (strings ints scope) scope)
                               (lambda (ns vs env) (if (null? ns) env
                                                       (go (cdr ns) (cdr vs) (cons (product (name (car ns)) (var (car vs))) env))))))
                      (go names vars env))))
        (letrec ((binds (subr fx-eff ((listof syn acyclic) strings ints scope) cores)
                   (lambda (bs ns vs scope)
                     (if (null? bs) nil
                         (let* ((is (fx-items (car bs)))
                                (value-syn (if (pair? is) (fx-last is) (car bs)))
                                (here (if (string=? kind "letrec") inner scope))
                                (value (if (and (pair? is) (pair? (cdr is))) (fx-named file value-syn (car ns) here) (k-none nil)))
                                (b (k-bind (car vs) value)))
                           (cons b (binds (cdr bs) (cdr ns) (cdr vs)
                                          (if (string=? kind "let*") (cons (product (name (car ns)) (var (car vs))) scope) scope))))))))
          (let* ((bs (binds bs names vars env)) (b (fx-body file body inner)))
            (k-seq (fx-append bs (list b))))))))
  (fx-tagcase (subr fx-eff (int syn (listof syn acyclic) scope) core)
    (lambda (file subject arms env)
      (let ((s (fx-core file subject env)))
        (k-case s
                (letrec ((go (subr fx-eff ((listof syn acyclic)) (listof arm acyclic))
                           (lambda (as)
                             (if (null? as) nil
                                 (let ((is (fx-items (car as))))
                                   (if (and (pair? is) (pair? (cdr is)))
                                       (let* ((tag (fx-sym (car is)))
                                              (names (tagcase (car (cdr is))
                                                       (lst (ns d a b) (letrec ((g (subr spin ((listof syn acyclic)) strings)
                                                                                  (lambda (l) (if (null? l) nil (cons (fx-sym (car l)) (g (cdr l)))))))
                                                                         (g ns)))
                                                       (else y (the strings (list (fx-sym (car (cdr is))))))))
                                              (vars (letrec ((g (subr fx-eff (strings) ints)
                                                                (lambda (ns) (if (null? ns) nil (cons (cf-new-var) (g (cdr ns)))))))
                                                      (g names)))
                                              (inner (letrec ((g (subr spin (strings ints scope) scope)
                                                                (lambda (ns vs env) (if (null? ns) env
                                                                                        (g (cdr ns) (cdr vs) (cons (product (name (car ns)) (var (car vs))) env))))))
                                                       (g names vars env)))
                                              (a (product (tag (if (string=? tag "else") "" tag)) (vars vars)
                                                          (fields (tagcase (car (cdr is)) (lst (ns d a b) #t) (else y #f)))
                                                          (body (fx-body file (cdr (cdr is)) inner)))))
                                         (cons a (go (cdr as))))
                                       (go (cdr as))))))))
                  (go arms)))))))

"The names forms `xs` define at their top level (in `module` and `hide`
too): each a global."
(define* fx-declare! (subr fx-eff ((listof syn acyclic)) unit)
  (lambda (xs)
    (if (null? xs) #u
        (let* ((is (fx-items (car xs))) (head (if (pair? is) (fx-sym (car is)) "")))
          (begin
            (cond ((and (or (string=? head "define") (string=? head "define*")) (pair? (cdr is)))
                   (begin (cf-global-var (fx-sym (car (cdr is)))) #u))
                  ((string=? head "define-rec")
                   (letrec ((go (subr fx-eff ((listof syn acyclic)) unit)
                              (lambda (bs) (if (null? bs) #u
                                               (let ((b (fx-items (car bs))))
                                                 (begin (if (pair? b) (begin (cf-global-var (fx-sym (car b))) #u) #u) (go (cdr bs))))))))
                     (go (cdr is))))
                  ((and (string=? head "define-datatype") (pair? (cdr is)))
                   (letrec ((go (subr fx-eff ((listof syn acyclic)) unit)
                              (lambda (vs) (if (null? vs) #u
                                               (let ((v (fx-items (car vs))))
                                                 (begin (if (pair? v) (begin (cf-global-var (fx-sym (car v))) #u) #u) (go (cdr vs))))))))
                     (go (cdr (cdr is)))))
                  ((or (string=? head "module") (string=? head "hide")) (fx-declare! (cdr is)))
                  ((and (string=? head "import") (pair? (cdr is)))
                   (letrec ((go (subr fx-eff ((listof syn acyclic)) unit)
                              (lambda (ns) (if (null? ns) #u
                                               (begin (if (string=? (fx-sym (car ns)) "") #u (begin (cf-global-var (fx-sym (car ns))) #u))
                                                 (go (cdr ns)))))))
                     (go (cdr (cdr is)))))
                  (else #u))
            (fx-declare! (cdr xs)))))))

"A world of FX-26 files (`paths` and their `texts`), read as core: its
top levels, a core each, in order."
(define* fx-world (subr (maxeff fx-eff spin) (strings strings) cores)
  (lambda (paths texts)
    (let ((forms (letrec ((go (subr (maxeff fx-eff spin) (strings) (listof (listof syn acyclic) acyclic))
                            (lambda (ts) (if (null? ts) nil (let ((f (fx-read (car ts)))) (cons f (go (cdr ts))))))))
                   (go texts))))
      (begin
        (cf-reset!)
        (letrec ((declare (subr fx-eff ((listof (listof syn acyclic) acyclic)) unit)
                   (lambda (l) (if (null? l) #u (begin (fx-declare! (car l)) (declare (cdr l)))))))
          (declare forms))
        (cf-globals-declared!)
        (letrec ((go (subr fx-eff (strings (listof (listof syn acyclic) acyclic)) cores)
                   (lambda (ps fs) (if (null? ps) nil
                                       (let ((c (fx-body (cf-file (car ps)) (car fs) nil))) (cons c (go (cdr ps) (cdr fs))))))))
          (go paths forms))))))
