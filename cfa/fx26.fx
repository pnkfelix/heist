;;; fx26.fx: FX-26 for the CFA -- its text read by Fixpt's own reader
;;; (`fx26:eager-reader.fx`) and turned into the core (core.fx), as
;;; editor/flow.fx's desugarer does; and FX-26 as a language (`cf-fx26`).
;;;
;;; Values flow as if types were erased: `plambda`'s body, `proj`'s and
;;; `the`'s expression. But types and regions flow too, where the text says
;;; them: a `plambda`'s binders, and a module file's (`(module-parameters
;;; ((r region) …))`), are variables, given what each `proj` instantiating
;;; them gives (`k-inst`) -- a region (`@ed`), a type's name, or another's
;;; binder -- and each use of one in a type is a reference to it. An
;;; instantiation the checker infers, the text does not say, so it is not
;;; seen.
;;;
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
  (list "call-with-composable-continuation" "call-with-oneshot-continuation"
        "abort-current-continuation" "with-mark" "cwcc" "%vlambda"))
(define fx-passing strings (list "reverse" "append" "datum-list"))

(define cf-fx26 cf-lang
  (product (name "fx26")
           (model (lambda ((n string))
                    (cond ((string=? n "apply") (m-apply))
                          ((member? n fx-higher-order string=?) (m-data #t (list "unknown")))
                          ((member? n fx-passing string=?) (m-pass))
                          (else (m-data #f nil)))))))

"Text `text` read: its forms (as far as they read)."
(define* fx-read (subr (maxeff cf-reader-eff spin) (string) (listof syn acyclic))
  (lambda (text) (eager-state-syntax (eager-feed (eager-feed-string (eager-start-fx26) text) #\newline))))

;;; ------------------------------------------------------------ the syntax, read as core

"Each module file's type binders' names, in order, by the file's number."
(define fx-binder-names (ref (listof (productof (file int) (names strings)) acyclic) @cf) (new nil))
(define* get-file-binders (subr (maxeff spin (read @cf)) (int) strings)
  (lambda (file) (iterate go spin ((l (listof (productof (file int) (names strings)) acyclic) (get fx-binder-names))) strings
                   (cond ((null? l) nil) ((= (extract (car l) file) file) (extract (car l) names)) (else (go (cdr l)))))))
"A module file's type binder `n`'s global, by the file's number."
(define* fx-file-binder-key (subr pure (int string) string)
  (lambda (file n) (string-append "%binder:" (int->string file) ":" n)))

"A local scope: names and their variables, innermost first."
(define-type scope (listof (productof (name string) (var int)) acyclic))
(define* scope-var (subr spin (scope string) int)
  (lambda (env n) (cond ((null? env) -1)
                        ((string=? (extract (car env) name) n) (extract (car env) var))
                        (else (scope-var (cdr env) n)))))
(define* fx-sym (subr spin (syn) string)
  (lambda (x) (tagcase x (atom (d a b xpn) (typecase d (symbol s (symbol->string s)) (else y ""))) (else y ""))))
(define* fx-items (subr spin (syn) (listof syn acyclic))
  (lambda (x) (tagcase x (lst (i d a b xpn) i) (else y nil))))
(define* fx-span (subr spin (int syn) cf-span)
  (lambda (file x)
    (tagcase x
      (atom (d a b xpn) (product (file file) (start a) (end b)))
      (lst (i d a b xpn) (product (file file) (start a) (end b)))
      (dotted (i t d a b xpn) (product (file file) (start a) (end b)))
      (vec (i d a b xpn) (product (file file) (start a) (end b))))))
"A parameter's name: `x`, or `(x type)`'s `x`."
(define* fx-param-name (subr spin (syn) string)
  (lambda (p) (let ((is (fx-items p))) (if (pair? is) (fx-sym (car is)) (fx-sym p)))))
"The kind of a literal."
(define* fx-literal-kind (subr spin (syn) string)
  (lambda (x)
    (tagcase x
      (atom (d a b xpn) (typecase d (int i "int") (string s "string") (char c "char") (bool b "bool") (f64 r "f64") (else y "datum")))
      (else y "datum"))))

"The variable a type names, `n`, is in scope `env` or a binder of file
`file` (-1: none, a type's name)."
(define* fx-type-var (subr fx-eff (int string scope) int)
  (lambda (file n env)
    (let ((v (scope-var env n)))
      (cond ((>= v 0) v)
            ((cf-global-defined? (fx-file-binder-key file n)) (cf-global-var (fx-file-binder-key file n)))
            (else -1)))))
"The references a type `x` makes to type and region variables."
(define* fx-type-refs (subr fx-eff (int syn scope) cores)
  (lambda (file x env)
    (tagcase x
      (atom (d a b xpn) (let* ((n (fx-sym x)) (v (if (string=? n "") -1 (fx-type-var file n env))))
                      (if (< v 0) nil (list (cf-ref v n (fx-span file x))))))
      (lst (items d a b xpn) (iterate go fx-eff ((l (listof syn acyclic) items)) cores
                               (if (null? l) nil (append (fx-type-refs file (car l) env) (go (cdr l))))))
      (else y nil))))
(define* fx-type-parts (subr fx-eff (int syn scope) cores)
  (lambda (file x env)
    (tagcase x
      (atom (d a b xpn) (let ((n (fx-sym x)))
                      (cond ((string=? n "") nil)
                            ((>= (fx-type-var file n env) 0) (list (cf-ref (fx-type-var file n env) n (fx-span file x))))
                            ((char=? (string-ref n 0) #\@) (list (k-const (cf-kind n))))
                            (else nil))))
      (lst (items d a b xpn) (iterate go fx-eff ((l (listof syn acyclic) items)) cores
                               (if (null? l) nil (append (fx-type-parts file (car l) env) (go (cdr l))))))
      (else y nil))))
"A type given to an instantiation, as a value: a region (`@r`), a type's
name, or a variable's; of a type made of others, the variables and regions
it is made of."
(define* fx-type-arg (subr fx-eff (int syn scope) core)
  (lambda (file x env)
    (let ((n (fx-sym x)))
      (cond ((string=? n "") (k-alt (fx-type-parts file x env)))
            ((>= (fx-type-var file n env) 0) (cf-ref (fx-type-var file n env) n (fx-span file x)))
            (else (k-const (cf-kind n)))))))
"The world file a `(load-module \"f\")` names, by number (-1: none)."
(define* fx-world-file (subr fx-eff (int string) int)
  (lambda (from f)
    (let ((dir (let ((p (cf-file-name from)))
                 (iterate go spin ((i int (- (string-length p) 1))) string
                   (cond ((< i 0) "") ((char=? (string-ref p i) #\/) (substring p 0 (+ i 1))) (else (go (- i 1))))))))
      (iterate go fx-eff ((l strings (get cf-files)) (i int 0)) int
        (cond ((null? l) -1) ((string=? (car l) (string-append dir f)) i) (else (go (cdr l) (+ i 1))))))))
"A `(module-parameters …)`'s type binders (those of a kind, not of a
module type): each its name and syntax."
(define* fx-kind-binders (subr spin ((listof syn acyclic)) (listof syn acyclic))
  (lambda (bs) (cond ((null? bs) nil)
                     ((let ((is (fx-items (car bs)))) (and (pair? is) (pair? (cdr is)) (not (string=? (fx-sym (car (cdr is))) ""))))
                      (cons (car bs) (fx-kind-binders (cdr bs))))
                     (else (fx-kind-binders (cdr bs))))))

(define* fx-append-tokens (subr spin ((listof cf-token acyclic) (listof cf-token acyclic)) (listof cf-token acyclic))
  (lambda (a b) (if (null? a) b (cons (car a) (fx-append-tokens (cdr a) b)))))
"Effect `x`, as tokens: each atom naming a type binder -- one of `names`,
whose variables are `vars`, or one in scope -- that binder's variable."
(define* fx-effect-tokens (subr fx-eff (int syn scope strings ints) (listof cf-token acyclic))
  (lambda (file x env names vars)
    (tagcase x
      (atom (d a b xpn)
        (let* ((n (fx-sym x))
               (i (if (string=? n "") -1 (cf-index n names)))
               (v (cond ((string=? n "") -1)
                        ((>= i 0) (iterate nth spin ((l ints vars) (k int i)) int
                                    (cond ((null? l) -1) ((= k 0) (car l)) (else (nth (cdr l) (- k 1))))))
                        (else (fx-type-var file n env)))))
          (if (>= v 0) (list (t-var v n)) (list (t-text (if (string=? n "") "?" n))))))
      (lst (items d a b xpn)
        (fx-append-tokens (list (t-text "("))
                          (fx-append-tokens (iterate go fx-eff ((l (listof syn acyclic) items) (first bool #t)) (listof cf-token acyclic)
                                              (if (null? l) nil
                                                  (fx-append-tokens (if first nil (list (t-text " ")))
                                                                    (fx-append-tokens (fx-effect-tokens file (car l) env names vars)
                                                                                      (go (cdr l) #f)))))
                                            (list (t-text ")")))))
      (else y (list (t-text "?"))))))
"A definition's type `t` and value's core `value`: the effect the type
declares, kept for the lambda the value makes (a `poly`'s binders, by
position, its `plambda`'s)."
(define* fx-keep-effect! (subr fx-eff (int syn core scope) unit)
  (lambda (file t value env)
    (let* ((ts (fx-items t))
           (poly (and (pair? ts) (string=? (fx-sym (car ts)) "poly") (pair? (cdr ts)) (pair? (cdr (cdr ts)))))
           (names (if poly (iterate go spin ((l (listof syn acyclic) (fx-items (car (cdr ts))))) strings
                             (if (null? l) nil (let ((is (fx-items (car l)))) (cons (fx-sym (if (pair? is) (car is) (car l))) (go (cdr l))))))
                      nil))
           (sub (fx-items (if poly (car (cdr (cdr ts))) t)))
           (l (cf-lambda-of value)))
      (when (and (>= l 0) (pair? sub) (string=? (fx-sym (car sub)) "subr") (pair? (cdr sub)))
        (set cf-effects (cons (product (lambda l)
                                       (tokens (fx-effect-tokens file (car (cdr sub)) env names (cf-poly-binders (get cf-poly-lambdas) l))))
                              (get cf-effects)))))))

"Constructor `tag` of `n` fields, of variant syntax `x`: the global bound
to a lambda making `(sum tag (product (1 p1) … (n pn)))`."
(define* fx-constructor (subr fx-eff (int syn string int) core)
  (lambda (file x tag n)
    (let* ((params (iterate go fx-eff ((i int 0)) ints
                     (if (>= i n) nil (cons (cf-new-var) (go (+ i 1))))))
           (fields (iterate go fx-eff ((ps ints params) (i int 1)) (listof field-init acyclic)
                     (if (null? ps) nil
                         (cons (product (label (int->string i)) (value (k-var (car ps) -1)))
                               (go (cdr ps) (+ i 1))))))
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
        (atom (d a b xpn)
          (let ((n (fx-sym x)))
            (cond ((string=? n "") (k-const (cf-kind (fx-literal-kind x))))
                  ((>= (scope-var env n) 0) (cf-ref (scope-var env n) n (fx-span file x)))
                  ((cf-global-defined? n) (cf-ref (cf-global-var n) n (fx-span file x)))
                  ;; Defined nowhere in the world: a standard value.
                  (else (k-prim n)))))
        (lst (items d a b xpn)
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
          ;; Types: a `plambda`'s binders are variables; a `proj` gives them.
          ((string=? head "plambda") (if (pair? rest) (fx-plambda file "" (fx-items (car rest)) (cdr rest) env) (k-none nil)))
          ((string=? head "proj")
           (if (pair? rest)
               (let* ((e (car rest))
                      (es (fx-items e))
                      (args (iterate go fx-eff ((l (listof syn acyclic) (cdr rest))) cores
                              (if (null? l) nil (let ((a (fx-type-arg file (car l) env))) (cons a (go (cdr l)))))))
                      ;; `(proj (load-module "f") …)` of a world file: its binders.
                      (target (if (and (pair? es) (string=? (fx-sym (car es)) "load-module") (pair? (cdr es)))
                                  (tagcase (car (cdr es)) (atom (d a b xpn) (typecase d (string s (fx-world-file file s)) (else y -1))) (else y -1))
                                  -1)))
                 (if (>= target 0)
                     (k-seq (letrec ((go (subr fx-eff (strings cores) cores)
                                           (lambda (ns as) (if (or (null? ns) (null? as)) nil
                                                               (cons (k-bind (cf-global-var (fx-file-binder-key target (car ns))) (car as))
                                                                     (go (cdr ns) (cdr as)))))))
                              (append (go (get-file-binders target) args) (list (fx-core file e env)))))
                     (k-inst (fx-core file e env) args)))
               (k-none nil)))
          ((string=? head "the")
           (if two? (k-seq (list (k-none (fx-type-refs file (car rest) env)) (fx-core file (car (cdr rest)) env))) (k-none nil)))
          ((or (string=? head "letregion") (string=? head "letrena") (string=? head "letreap") (string=? head "letfreeze"))
           (fx-body file (if (pair? rest) (cdr rest) nil) env))
          ((string=? head "if")
           (if (pair? rest) (k-seq (list (fx-core file (car rest) env) (k-alt (fx-all file (cdr rest) env)))) (k-none nil)))
          ((or (string=? head "and") (string=? head "or")) (k-alt (fx-all file rest env)))
          ((string=? head "begin") (fx-body file rest env))
          ((string=? head "cond")
           (k-alt (iterate clauses fx-eff ((cs (listof syn acyclic) rest)) cores
                    (if (null? cs) nil
                        (let ((is (fx-items (car cs))))
                          (cons (if (and (pair? is) (string=? (fx-sym (car is)) "else"))
                                    (fx-body file (cdr is) env)
                                    (fx-body file is env))
                                (clauses (cdr cs))))))))
          ((string=? head "case")
           (if (pair? rest)
               (k-seq (list (fx-core file (car rest) env)
                            (k-alt (iterate clauses fx-eff ((cs (listof syn acyclic) (cdr rest))) cores
                                     (if (null? cs) nil
                                         (let ((is (fx-items (car cs))))
                                           (cons (fx-body file (if (pair? is) (cdr is) nil) env)
                                                 (clauses (cdr cs)))))))))
               (k-none nil)))
          ((or (string=? head "let") (string=? head "let*") (string=? head "letrec"))
           (if (pair? rest) (fx-let file head (fx-items (car rest)) (cdr rest) env) (k-none nil)))
          ((string=? head "product")
           (k-alloc (site "product" "")
                    (iterate fields fx-eff ((fs (listof syn acyclic) rest)) (listof field-init acyclic)
                      (if (null? fs) nil
                          (let ((is (fx-items (car fs))))
                            (if (and (pair? is) (pair? (cdr is)))
                                (cons (product (label (fx-sym (car is))) (value (fx-core file (car (cdr is)) env)))
                                      (fields (cdr fs)))
                                (fields (cdr fs))))))))
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
          ;; A list of its elements: a pair site each (yank's spine).
          ((string=? head "list") (cf-list-core (fx-span file x) (fx-all file rest env) "null"))
          ((string=? head "tagcase") (if (pair? rest) (fx-tagcase file (car rest) (cdr rest) env) (k-none nil)))
          ((string=? head "typecase")
           (if (pair? rest)
               (let ((subject (fx-core file (car rest) env)) (v (cf-new-var)))
                 (k-seq (list (k-bind v subject)
                              (k-alt (iterate arms fx-eff ((as (listof syn acyclic) (cdr rest))) cores
                                       (if (null? as) nil
                                           (let ((is (fx-items (car as))))
                                             (cons (if (and (pair? is) (pair? (cdr is)))
                                                       (fx-body file (cdr (cdr is))
                                                                (cons (product (name (fx-sym (car (cdr is)))) (var v)) env))
                                                       (k-none nil))
                                                   (arms (cdr as))))))))))
               (k-none nil)))
          ;; Definitions: a global's variable given the value.
          ((or (string=? head "define") (string=? head "define*"))
           (if two?
               (let* ((name (fx-sym (car rest)))
                      (typed (pair? (cdr (cdr rest))))
                      (value-syn (car (if typed (cdr (cdr rest)) (cdr rest))))
                      (refs (if typed (fx-type-refs file (car (cdr rest)) env) nil))
                      (value (begin (when (null? env) (set cf-definition name)) (fx-named file value-syn name env)))
                      (kept (when typed (fx-keep-effect! file (car (cdr rest)) value env))))
                 (if (null? refs) (k-bind (cf-global-var name) value)
                     (k-seq (list (k-none refs) (k-bind (cf-global-var name) value)))))
               (k-none nil)))
          ((string=? head "define-rec")
           (k-seq (iterate go fx-eff ((bs (listof syn acyclic) rest)) cores
                    (if (null? bs) nil
                        (let ((is (fx-items (car bs))))
                          (if (and (pair? is) (pair? (cdr is)) (pair? (cdr (cdr is))))
                              (let ((b (k-bind (cf-global-var (fx-sym (car is)))
                                               (begin (when (null? env) (set cf-definition (fx-sym (car is))))
                                                 (fx-named file (car (cdr (cdr is))) (fx-sym (car is)) env)))))
                                (cons b (go (cdr bs))))
                              (go (cdr bs))))))))
          ;; `(define-datatype t (tag T …) …)`: each tag a global constructor.
          ((string=? head "define-datatype")
           (k-seq (iterate variants fx-eff ((vs (listof syn acyclic) (if (pair? rest) (cdr rest) nil))) cores
                    (if (null? vs) nil
                        (let ((is (fx-items (car vs))))
                          (if (pair? is)
                              (let ((c (fx-constructor file (car vs) (fx-sym (car is)) (length (cdr is)))))
                                (cons c (variants (cdr vs))))
                              (variants (cdr vs))))))))
          ;; A module file's type binders: each a reference where it binds.
          ((string=? head "module-parameters")
           (k-none (if (pair? rest)
                       (iterate go fx-eff ((bs (listof syn acyclic) (fx-kind-binders (fx-items (car rest))))) cores
                         (if (null? bs) nil
                             (let* ((b (car (fx-items (car bs)))) (n (fx-sym b)))
                               (cons (cf-ref (cf-global-var (fx-file-binder-key file n)) n (fx-span file b)) (go (cdr bs))))))
                       nil)))
          ((or (string=? head "define-type") (string=? head "define-effect")
               (string=? head "define-generative") (string=? head "import"))
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
        (cond ((and (pair? is) (string=? (fx-sym (car is)) "lambda") (pair? (cdr is)))
               (fx-lambda file x name (fx-items (car (cdr is))) (cdr (cdr is)) env))
              ((and (pair? is) (string=? (fx-sym (car is)) "plambda") (pair? (cdr is)))
               (fx-plambda file name (fx-items (car (cdr is))) (cdr (cdr is)) env))
              (else (fx-core file x env))))))
  ;; `(plambda ((I K) …) body …)`: each binder a variable, a reference where
  ;; it binds; the body's lambda (or site), named `name`, bound by them.
  (fx-plambda (subr fx-eff (int string (listof syn acyclic) (listof syn acyclic) scope) core)
    (lambda (file name binders body env)
      (let* ((names (iterate go spin ((l (listof syn acyclic) binders)) (listof syn acyclic)
                      (if (null? l) nil (let ((is (fx-items (car l)))) (cons (if (pair? is) (car is) (car l)) (go (cdr l)))))))
             (vars (iterate go fx-eff ((l (listof syn acyclic) names)) ints
                     (if (null? l) nil (cons (cf-new-var) (go (cdr l))))))
             (inner (iterate go spin ((ns (listof syn acyclic) names) (vs ints vars) (env scope env)) scope
                      (if (null? ns) env (go (cdr ns) (cdr vs) (cons (product (name (fx-sym (car ns))) (var (car vs))) env)))))
             (refs (iterate go fx-eff ((ns (listof syn acyclic) names) (vs ints vars)) cores
                     (if (null? ns) nil (cons (cf-ref (car vs) (fx-sym (car ns)) (fx-span file (car ns))) (go (cdr ns) (cdr vs))))))
             (b (if (and (pair? body) (null? (cdr body))) (fx-named file (car body) name inner) (fx-body file body inner))))
        (begin (cf-poly! b vars)
          (k-seq (list (k-none refs) b))))))
  (fx-lambda (subr fx-eff (int syn string (listof syn acyclic) (listof syn acyclic) scope) core)
    (lambda (file x name params body env)
      (iterate bind fx-eff ((ps (listof syn acyclic) params) (env scope env) (vs ints nil)) core
        (if (null? ps)
            (let* ((types (iterate go fx-eff ((l (listof syn acyclic) params)) cores
                            (if (null? l) nil
                                (let ((is (fx-items (car l))))
                                  (append (if (and (pair? is) (pair? (cdr is))) (fx-type-refs file (car (cdr is)) env) nil) (go (cdr l)))))))
                   (b (fx-body file body env)))
              (k-lam (cf-add-lambda (product (span (fx-span file x)) (name (if (string=? name "") (cf-anonymous) name))
                                             (params (reverse vs)) (rest -1)
                                             (body (if (null? types) b (k-seq (list (k-none types) b))))))))
            (let ((v (cf-new-var)))
              (bind (cdr ps) (cons (product (name (fx-param-name (car ps))) (var v)) env) (cons v vs)))))))
  ;; `let`: values outside; `let*`: each sees those before; `letrec`: all see all.
  (fx-let (subr fx-eff (int string (listof syn acyclic) (listof syn acyclic) scope) core)
    (lambda (file kind bs body env)
      (let* ((names (iterate go spin ((bs (listof syn acyclic) bs)) strings
                      (if (null? bs) nil (cons (fx-param-name (car bs)) (go (cdr bs))))))
             (vars (iterate go fx-eff ((ns strings names)) ints
                     (if (null? ns) nil (cons (cf-new-var) (go (cdr ns))))))
             (inner (iterate go spin ((ns strings names) (vs ints vars) (env scope env)) scope
                      (if (null? ns) env
                          (go (cdr ns) (cdr vs) (cons (product (name (car ns)) (var (car vs))) env))))))
        (letrec ((binds (subr fx-eff ((listof syn acyclic) strings ints scope) cores)
                   (lambda (bs ns vs scope)
                     (if (null? bs) nil
                         (let* ((is (fx-items (car bs)))
                                (value-syn (if (pair? is) (last is) (car bs)))
                                (here (if (string=? kind "letrec") inner scope))
                                (value (if (and (pair? is) (pair? (cdr is))) (fx-named file value-syn (car ns) here) (k-none nil)))
                                (b (k-bind (car vs) value)))
                           (cons b (binds (cdr bs) (cdr ns) (cdr vs)
                                          (if (string=? kind "let*") (cons (product (name (car ns)) (var (car vs))) scope) scope))))))))
          (let* ((bs (binds bs names vars env)) (b (fx-body file body inner)))
            (k-seq (append bs (list b))))))))
  (fx-tagcase (subr fx-eff (int syn (listof syn acyclic) scope) core)
    (lambda (file subject arms env)
      (let ((s (fx-core file subject env)))
        (k-case s
                (iterate go fx-eff ((as (listof syn acyclic) arms)) (listof arm acyclic)
                  (if (null? as) nil
                      (let ((is (fx-items (car as))))
                        (if (and (pair? is) (pair? (cdr is)))
                            (let* ((tag (fx-sym (car is)))
                                   (names (tagcase (car (cdr is))
                                            (lst (ns d a b xpn) (iterate g spin ((l (listof syn acyclic) ns)) strings
                                                                  (if (null? l) nil (cons (fx-sym (car l)) (g (cdr l))))))
                                            (else y (the strings (list (fx-sym (car (cdr is))))))))
                                   (vars (iterate g fx-eff ((ns strings names)) ints
                                           (if (null? ns) nil (cons (cf-new-var) (g (cdr ns))))))
                                   (inner (iterate g spin ((ns strings names) (vs ints vars) (env scope env)) scope
                                            (if (null? ns) env
                                                (g (cdr ns) (cdr vs) (cons (product (name (car ns)) (var (car vs))) env)))))
                                   (a (product (tag (if (string=? tag "else") "" tag)) (vars vars)
                                               (fields (tagcase (car (cdr is)) (lst (ns d a b xpn) #t) (else y #f)))
                                               (body (fx-body file (cdr (cdr is)) inner)))))
                              (cons a (go (cdr as))))
                            (go (cdr as)))))))))))

"The names forms `xs` define at their top level (in `module` and `hide`
too): each a global."
(define* fx-declare! (subr fx-eff (int (listof syn acyclic)) unit)
  (lambda (file xs)
    (unless (null? xs)
      (let* ((is (fx-items (car xs))) (head (if (pair? is) (fx-sym (car is)) "")))
        (begin
          (cond ((and (or (string=? head "define") (string=? head "define*")) (pair? (cdr is)))
                 (begin (cf-global-var (fx-sym (car (cdr is)))) #u))
                ((string=? head "define-rec")
                 (iterate go fx-eff ((bs (listof syn acyclic) (cdr is))) unit
                   (unless (null? bs)
                     (let ((b (fx-items (car bs))))
                       (begin (when (pair? b) (cf-global-var (fx-sym (car b))) #u) (go (cdr bs)))))))
                ((and (string=? head "define-datatype") (pair? (cdr is)))
                 (iterate go fx-eff ((vs (listof syn acyclic) (cdr (cdr is)))) unit
                   (unless (null? vs)
                     (let ((v (fx-items (car vs))))
                       (begin (when (pair? v) (cf-global-var (fx-sym (car v))) #u) (go (cdr vs)))))))
                ((or (string=? head "module") (string=? head "hide")) (fx-declare! file (cdr is)))
                ((and (string=? head "module-parameters") (pair? (cdr is)))
                 (let ((names (iterate go spin ((bs (listof syn acyclic) (fx-kind-binders (fx-items (car (cdr is)))))) strings
                                (if (null? bs) nil (cons (fx-sym (car (fx-items (car bs)))) (go (cdr bs)))))))
                   (begin
                     (set fx-binder-names (cons (product (file file) (names names)) (get fx-binder-names)))
                     (iterate go fx-eff ((ns strings names)) unit
                       (unless (null? ns) (cf-global-var (fx-file-binder-key file (car ns))) (go (cdr ns)))))))
                ((and (string=? head "import") (pair? (cdr is)))
                 (iterate go fx-eff ((ns (listof syn acyclic) (cdr (cdr is)))) unit
                   (unless (null? ns)
                     (unless (string=? (fx-sym (car ns)) "") (cf-global-var (fx-sym (car ns))) #u)
                (go (cdr ns)))))
                (else #u))
          (fx-declare! file (cdr xs)))))))

"A world of FX-26 files (`paths` and their `texts`), read as core: its
top levels, a core each, in order."
(define* fx-world (subr (maxeff fx-eff spin) (strings strings) cores)
  (lambda (paths texts)
    (let ((forms (iterate go (maxeff fx-eff spin) ((ts strings texts)) (listof (listof syn acyclic) acyclic)
                   (if (null? ts) nil (let ((f (fx-read (car ts)))) (cons f (go (cdr ts))))))))
      (begin
        (cf-reset!)
        (set cf-file-texts texts)
        (set cf-null-kind "null")
        (set fx-binder-names nil)
        (iterate declare fx-eff ((ps strings paths) (l (listof (listof syn acyclic) acyclic) forms)) unit
          (unless (null? l) (fx-declare! (cf-file (car ps)) (car l)) (declare (cdr ps) (cdr l))))
        (cf-globals-declared!)
        (iterate go fx-eff ((ps strings paths) (fs (listof (listof syn acyclic) acyclic) forms)) cores
          (if (null? ps) nil
              (let ((c (fx-body (cf-file (car ps)) (car fs) nil))) (cons c (go (cdr ps) (cdr fs))))))))))
