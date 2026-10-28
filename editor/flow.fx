;;; flow.fx: which lambdas reach which calls -- a closure-flow analysis of
;;; FX-26 programs (yank's `(yank analysis core)` and `(yank analysis
;;; cfa)`, abe5091, at 0CFA; the second stage of docs/fx26-analysis.md).
;;;
;;; The reader's syntax of every file of a program is turned into a small
;;; core language, with every binder, lambda, call and allocation site
;;; numbered, as yank's desugarer does. Then the abstract values -- lambdas,
;;; allocation sites (products, sums, refs, pairs) and *unknown* -- that
;;; can reach each variable, field and lambda's result are found by
;;; evaluating every lambda's body and the top level against a store that
;;; only grows, until it stops growing. What a call can reach is the
;;; lambdas in its operator's value.
;;;
;;; What FX-26's types buy, even unused: a name defined nowhere in the
;;; program is a standard procedure, nearly all first order -- its result
;;; holds no closure, and what it is given does not escape -- where yank
;;; had to model 330 lines of Scheme primitives. The few higher-order ones
;;; (`apply`, continuations, marks) make what they are given escape; an
;;; escaped lambda's parameters are unknown.
;;;
;;; State: global, at region @fl, so the analysis runs in a command (as the
;;; reader does). Not yet: contexts (1CFA, call sites for small procedures),
;;; a worklist instead of whole passes, a warm start after an edit.
(lambda ((m-base (load-input-moduleof "base.fx"))
         (m-buffer (load-input-moduleof "buffer.fx" m-base))
         (m-resolve (load-input-moduleof "resolve.fx" m-base m-buffer))
         (m-syntax (load-input-moduleof "syntax.fx" m-base m-buffer m-resolve))
         (m-sexp (load-input-moduleof "sexp.fx" m-base m-buffer m-resolve m-syntax)))
(module
(hide (include m-base) (include m-buffer) (include m-resolve) (include m-syntax) (include m-sexp))

;;; ------------------------------------------------------------ the core

(define-datatype core
  (k-none (listof core acyclic))                ; evaluate these; the value holds no closure
  (k-var int)                                    ; a variable, by number
  (k-lam int)                                    ; a lambda, by number
  (k-app int core (listof core acyclic))         ; a call, by number: operator, arguments
  (k-seq (listof core acyclic))                  ; in order; the last one's value
  (k-alt (listof core acyclic))                  ; each a branch; any one's value
  (k-bind int core)                              ; the variable gets the value
  (k-alloc int (listof field-init acyclic))      ; a site, by number, and its fields
  (k-field core string)                          ; a field of what the value is
  (k-store core string core)                     ; a field of what the first is, given the second
  (k-case core (listof arm acyclic))             ; tagcase: the subject, the arms
  (k-escape (listof core acyclic)))              ; given to code not known: escapes; unknown
(define-type field-init (productof (label string) (value core)))
"A `tagcase` arm: its tag (\"\" for `else`), the variables it binds --
the payload, for `(tag x body)`; its fields by position, labels `1`, `2`,
…, for `(tag (x y) body)` (`fields`) -- and its body."
(define-type arm (productof (tag string) (vars (listof int acyclic)) (fields bool) (body core)))
(define-type cores (listof core acyclic))

;;; ------------------------------------------------------------ numbering

(define-type fl-span (productof (file string) (start int) (end int)))
(define-type lambda-info (productof (span fl-span) (name string) (params (listof int acyclic)) (rest int) (body core)))
(define-type call-info (productof (span fl-span) (operator fl-span)))
(define-type site-info (productof (span fl-span) (kind string) (tag string)))

(define fl-vars (ref int @fl) (new 0))
(define fl-lambdas (ref (listof lambda-info acyclic) @fl) (new nil))   ; newest first
(define fl-calls (ref (listof call-info acyclic) @fl) (new nil))
(define fl-sites (ref (listof site-info acyclic) @fl) (new nil))
(define fl-tables (load-module "fx26:table.fx"))
(import fl-tables make-table table-ref table-set! (type table))
"The globals' variables, by name."
(define fl-globals (ref (table string int @fl) @fl)
  (new (the (table string int @fl) (make-table string-hash string=?))))
"How many lambdas, calls and sites have been numbered."
(define fl-counts (arrayof int @fl) (make-array 3 0))
"The definition being read, to name the lambdas in it: `move-by/λ`."
(define fl-definition (ref string @fl) (new ""))

(define-effect numbering (maxeff (read @fl) (write @fl) (alloc @fl) (read @globals) spin))

(define new-var (->* () int)
  (lambda () (let ((n (get fl-vars))) (begin (set fl-vars (+ n 1)) n))))

"The variable of global `name`, made on first use."
(define global-var (subr (maxeff numbering (read @globals) (alloc @fl)) (string) int)
  (lambda (name)
    (let ((v (table-ref (get fl-globals) name -1)))
      (if (>= v 0)
          v
          (let ((n (new-var)))
            (begin (table-set! (get fl-globals) name n) n))))))

(define global-defined? (subr (maxeff (read @fl) (read @globals) spin) (string) bool)
  (lambda (name) (>= (table-ref (get fl-globals) name -1) 0)))
"The next number of kind `k` (0 lambdas, 1 calls, 2 sites)."
(define next-number (->* (int) int)
  (lambda (k) (let ((n (array-ref fl-counts k))) (begin (array-set! fl-counts k (+ n 1)) n))))
(define add-lambda (->* (lambda-info) int)
  (lambda (info) (begin (set fl-lambdas (cons info (get fl-lambdas))) (next-number 0))))
(define add-call (->* (call-info) int)
  (lambda (info) (begin (set fl-calls (cons info (get fl-calls))) (next-number 1))))
(define add-site (->* (site-info) int)
  (lambda (info) (begin (set fl-sites (cons info (get fl-sites))) (next-number 2))))

;;; ------------------------------------------------------------ the syntax, read as core

"A local scope: names and their variables, innermost first."
(define-type scope (listof (productof (name string) (var int)) acyclic))

(define scope-var (->* (scope string) int)
  (lambda (env n) (cond ((null? env) -1)
                        ((string=? (extract (car env) name) n) (extract (car env) var))
                        (else (scope-var (cdr env) n)))))

(define sym-of (->* (syn) string)
  (lambda (x) (tagcase x (atom (d a b) (typecase d (symbol s (symbol->string s)) (else y ""))) (else y ""))))
(define list-items (->* (syn) (listof syn acyclic))
  (lambda (x) (tagcase x (lst (i d a b) i) (else y nil))))
(define span-of (->* (string syn) fl-span)
  (lambda (file x)
    (tagcase x
      (atom (d a b) (product (file file) (start a) (end b)))
      (lst (i d a b) (product (file file) (start a) (end b)))
      (dotted (i t d a b) (product (file file) (start a) (end b)))
      (vec (i d a b) (product (file file) (start a) (end b))))))

"A parameter's name: `x`, or `(x type)`'s `x`."
(define param-name (->* (syn) string)
  (lambda (p) (let ((is (list-items p))) (if (pair? is) (sym-of (car is)) (sym-of p)))))

"Standard procedures that call what they are given, or keep it where
code not known may: what they are given escapes."
(define higher-order strings
  (list "apply" "call-with-composable-continuation" "call-with-oneshot-continuation"
        "abort-current-continuation" "with-mark" "cwcc" "%vlambda"))
"Standard procedures whose result holds the elements of their arguments."
(define passing strings (list "reverse" "append" "list" "cons" "car" "cdr" "datum-list"))

"Constructor `tag` of `n` fields, of variant syntax `x`: the global bound
to a lambda making `(sum tag (product (1 p1) … (n pn)))`."
(define constructor-core (->* (string syn string int) core)
  (lambda (file x tag n)
    (let* ((params (letrec ((go (->* (int) (listof int acyclic)) (lambda (i) (if (>= i n) nil (cons (new-var) (go (+ i 1)))))))
                     (go 0)))
           (fields (letrec ((go (->* ((listof int acyclic) int) (listof field-init acyclic))
                              (lambda (ps i) (if (null? ps) nil
                                                 (cons (product (label (int->string i)) (value (k-var (car ps))))
                                                       (go (cdr ps) (+ i 1)))))))
                     (go params 1)))
           (body (k-alloc (add-site (product (span (span-of file x)) (kind "sum") (tag tag)))
                          (list (product (label "payload")
                                         (value (k-alloc (add-site (product (span (span-of file x)) (kind "product") (tag "")))
                                                         fields)))))))
      (k-bind (global-var tag)
              (k-lam (add-lambda (product (span (span-of file x)) (name tag) (params params) (rest -1) (body body))))))))

(define last-syn (->* ((listof syn acyclic)) syn)
  (lambda (l) (if (null? (cdr l)) (car l) (last-syn (cdr l)))))
(define reverse-ints (->* ((listof int acyclic)) (listof int acyclic))
  (lambda (l) (letrec ((go (subr spin ((listof int acyclic) (listof int acyclic)) (listof int acyclic))
                         (lambda (l acc) (if (null? l) acc (go (cdr l) (cons (car l) acc))))))
                (go l nil))))
(define append-cores (->* (cores cores) cores)
  (lambda (a b) (if (null? a) b (cons (car a) (append-cores (cdr a) b)))))

(define-rec
  ;; Form `x` of `file`, in scope `env`, as core.
  (to-core (->* (string syn scope) core)
    (lambda (file x env)
      (tagcase x
        (atom (d a b)
          (let ((n (sym-of x)))
            (cond ((string=? n "") (k-none nil))
                  ((>= (scope-var env n) 0) (k-var (scope-var env n)))
                  ((global-defined? n) (k-var (global-var n)))
                  ;; Defined nowhere in the program: a standard value, holding no closure.
                  (else (k-none nil)))))
        (lst (items d a b)
          (if (null? items)
              (k-none nil)
              (form-to-core file x (sym-of (car items)) (cdr items) env)))
        (else y (k-none nil)))))
  (all-to-core (->* (string (listof syn acyclic) scope) cores)
    (lambda (file xs env) (if (null? xs) nil (cons (to-core file (car xs) env) (all-to-core file (cdr xs) env)))))
  ;; A body: its forms in order.
  (body-to-core (->* (string (listof syn acyclic) scope) core)
    (lambda (file xs env) (k-seq (all-to-core file xs env))))
  ;; A list whose head is the symbol `head` ("" if it is not one).
  (form-to-core (->* (string syn string (listof syn acyclic) scope) core)
    (lambda (file x head rest env)
      (cond
        ((or (string=? head "quote") (string=? head "quasiquote")) (k-none nil))
        ((string=? head "lambda")
         (if (pair? rest) (lambda-to-core file x "" (list-items (car rest)) (cdr rest) env) (k-none nil)))
        ((string=? head "vlambda")
         (if (pair? rest)
             (let* ((v (new-var))
                    (body (body-to-core file (cdr rest) (cons (product (name (param-name (car rest))) (var v)) env))))
               (k-lam (add-lambda (product (span (span-of file x)) (name (string-append (get fl-definition) "/λ")) (params nil) (rest v) (body body)))))
             (k-none nil)))
        ;; Types are erased: `plambda`'s body, `proj`'s and `the`'s expression.
        ((string=? head "plambda") (body-to-core file (if (pair? rest) (cdr rest) nil) env))
        ((string=? head "proj") (if (pair? rest) (to-core file (car rest) env) (k-none nil)))
        ((string=? head "the") (if (and (pair? rest) (pair? (cdr rest))) (to-core file (car (cdr rest)) env) (k-none nil)))
        ((or (string=? head "letregion") (string=? head "letrena") (string=? head "letreap") (string=? head "letfreeze"))
         (body-to-core file (if (pair? rest) (cdr rest) nil) env))
        ((or (string=? head "if") (string=? head "and") (string=? head "or"))
         (if (string=? head "if")
             (if (pair? rest) (k-seq (list (to-core file (car rest) env) (k-alt (all-to-core file (cdr rest) env)))) (k-none nil))
             (k-alt (all-to-core file rest env))))
        ((string=? head "begin") (body-to-core file rest env))
        ((string=? head "cond")
         (k-alt (letrec ((clauses (->* ((listof syn acyclic)) cores)
                           (lambda (cs) (if (null? cs) nil
                                            (let ((is (list-items (car cs))))
                                              (cons (if (and (pair? is) (string=? (sym-of (car is)) "else"))
                                                        (body-to-core file (cdr is) env)
                                                        (body-to-core file is env))
                                                    (clauses (cdr cs))))))))
                  (clauses rest))))
        ((string=? head "case")
         (if (pair? rest)
             (k-seq (list (to-core file (car rest) env)
                          (k-alt (letrec ((clauses (->* ((listof syn acyclic)) cores)
                                            (lambda (cs) (if (null? cs) nil
                                                             (let ((is (list-items (car cs))))
                                                               (cons (body-to-core file (if (pair? is) (cdr is) nil) env)
                                                                     (clauses (cdr cs))))))))
                                   (clauses (cdr rest))))))
             (k-none nil)))
        ((or (string=? head "let") (string=? head "let*") (string=? head "letrec"))
         (if (pair? rest) (let-to-core file head (list-items (car rest)) (cdr rest) env) (k-none nil)))
        ((string=? head "product")
         (k-alloc (add-site (product (span (span-of file x)) (kind "product") (tag "")))
                  (letrec ((fields (->* ((listof syn acyclic)) (listof field-init acyclic))
                             (lambda (fs) (if (null? fs) nil
                                              (let ((is (list-items (car fs))))
                                                (if (and (pair? is) (pair? (cdr is)))
                                                    (cons (product (label (sym-of (car is))) (value (to-core file (car (cdr is)) env)))
                                                          (fields (cdr fs)))
                                                    (fields (cdr fs))))))))
                    (fields rest))))
        ((string=? head "extract")
         (if (and (pair? rest) (pair? (cdr rest)))
             (k-field (to-core file (car rest) env) (sym-of (car (cdr rest))))
             (k-none nil)))
        ((string=? head "sum")
         (if (and (pair? rest) (pair? (cdr rest)))
             (k-alloc (add-site (product (span (span-of file x)) (kind "sum") (tag (sym-of (car rest)))))
                      (list (product (label "payload") (value (to-core file (car (cdr rest)) env)))))
             (k-none nil)))
        ((string=? head "new")
         (k-alloc (add-site (product (span (span-of file x)) (kind "ref") (tag "")))
                  (list (product (label "contents") (value (if (pair? rest) (to-core file (car rest) env) (k-none nil)))))))
        ((string=? head "get") (if (pair? rest) (k-field (to-core file (car rest) env) "contents") (k-none nil)))
        ((string=? head "set")
         (if (and (pair? rest) (pair? (cdr rest)))
             (k-store (to-core file (car rest) env) "contents" (to-core file (car (cdr rest)) env))
             (k-none nil)))
        ((string=? head "cons")
         (if (and (pair? rest) (pair? (cdr rest)))
             (k-alloc (add-site (product (span (span-of file x)) (kind "pair") (tag "")))
                      (list (product (label "car") (value (to-core file (car rest) env)))
                            (product (label "cdr") (value (to-core file (car (cdr rest)) env)))))
             (k-none nil)))
        ((string=? head "car") (if (pair? rest) (k-field (to-core file (car rest) env) "car") (k-none nil)))
        ((string=? head "cdr") (if (pair? rest) (k-field (to-core file (car rest) env) "cdr") (k-none nil)))
        ((string=? head "list")
         ;; A list of its elements: one pair site, its cdr itself.
         (let ((site (add-site (product (span (span-of file x)) (kind "pair") (tag "")))))
           (k-alloc site (list (product (label "car") (value (k-alt (all-to-core file rest env))))))))
        ((string=? head "tagcase")
         (if (pair? rest) (tagcase-to-core file (car rest) (cdr rest) env) (k-none nil)))
        ((string=? head "typecase")
         (if (pair? rest)
             (let ((subject (to-core file (car rest) env)) (v (new-var)))
               (k-seq (list (k-bind v subject)
                            (k-alt (letrec ((arms (->* ((listof syn acyclic)) cores)
                                              (lambda (as) (if (null? as) nil
                                                               (let ((is (list-items (car as))))
                                                                 (cons (if (and (pair? is) (pair? (cdr is)))
                                                                           (body-to-core file (cdr (cdr is))
                                                                                         (cons (product (name (sym-of (car (cdr is)))) (var v)) env))
                                                                           (k-none nil))
                                                                       (arms (cdr as))))))))
                                     (arms (cdr rest)))))))
             (k-none nil)))
        ;; Definitions: a global's variable given the value.
        ((or (string=? head "define") (string=? head "define*"))
         (if (and (pair? rest) (pair? (cdr rest)))
             (let* ((name (sym-of (car rest)))
                    (value-syn (car (if (pair? (cdr (cdr rest))) (cdr (cdr rest)) (cdr rest))))
                    (value (begin (if (null? env) (set fl-definition name) #u)
                             (named-to-core file value-syn name env))))
               (k-bind (global-var name) value))
             (k-none nil)))
        ((string=? head "define-rec")
         (k-seq (letrec ((go (->* ((listof syn acyclic)) cores)
                           (lambda (bs) (if (null? bs) nil
                                            (let ((is (list-items (car bs))))
                                              (if (and (pair? is) (pair? (cdr is)) (pair? (cdr (cdr is))))
                                                  (cons (k-bind (global-var (sym-of (car is)))
                                                                (begin (if (null? env) (set fl-definition (sym-of (car is))) #u)
                                                                  (named-to-core file (car (cdr (cdr is))) (sym-of (car is)) env)))
                                                        (go (cdr bs)))
                                                  (go (cdr bs))))))))
                  (go rest))))
        ;; `(define-datatype t (tag T …) …)`: each tag a global constructor, a
        ;; lambda of as many parameters as types, making a sum of the tag whose
        ;; payload is a product of them, fields `1`, `2`, … (as `tagcase`'s
        ;; arms take it apart).
        ((string=? head "define-datatype")
         (k-seq (letrec ((variants (->* ((listof syn acyclic)) cores)
                           (lambda (vs)
                             (if (null? vs) nil
                                 (let ((is (list-items (car vs))))
                                   (if (pair? is)
                                       (cons (constructor-core file (car vs) (sym-of (car is)) (length (cdr is)))
                                             (variants (cdr vs)))
                                       (variants (cdr vs))))))))
                  (variants (if (pair? rest) (cdr rest) nil)))))
        ((or (string=? head "define-type") (string=? head "define-effect")
             (string=? head "define-generative") (string=? head "import") (string=? head "module-parameters"))
         (k-none nil))
        ((or (string=? head "module") (string=? head "hide")) (body-to-core file rest env))
        ;; `(with m x)`: x, by name.
        ((string=? head "with") (body-to-core file (if (pair? rest) (cdr rest) nil) env))
        ;; A call. Of a standard procedure, by what it is known to do.
        (else
         (let ((op (if (pair? (list-items x)) (car (list-items x)) x)))
           (cond ((and (not (string=? head "")) (< (scope-var env head) 0) (not (global-defined? head))
                       (member? head higher-order))
                  (k-escape (all-to-core file rest env)))
                 ((and (not (string=? head "")) (< (scope-var env head) 0) (not (global-defined? head))
                       (member? head passing))
                  (k-alt (all-to-core file rest env)))
                 ((and (not (string=? head "")) (< (scope-var env head) 0) (not (global-defined? head)))
                  (k-none (all-to-core file rest env)))
                 (else
                  (k-app (add-call (product (span (span-of file x)) (operator (span-of file op))))
                         (to-core file op env)
                         (all-to-core file rest env)))))))))
  ;; A definition's value, a lambda named for it.
  (named-to-core (->* (string syn string scope) core)
    (lambda (file x name env)
      (let ((is (list-items x)))
        (if (and (pair? is) (string=? (sym-of (car is)) "lambda") (pair? (cdr is)))
            (lambda-to-core file x name (list-items (car (cdr is))) (cdr (cdr is)) env)
            (to-core file x env)))))
  (lambda-to-core (->* (string syn string (listof syn acyclic) (listof syn acyclic) scope) core)
    (lambda (file x name params body env)
      (letrec ((bind (->* ((listof syn acyclic) scope (listof int acyclic)) core)
                 (lambda (ps env vs)
                   (if (null? ps)
                       (k-lam (add-lambda (product (span (span-of file x))
                                                   (name (if (string=? name "") (string-append (get fl-definition) "/λ") name))
                                                   (params (reverse-ints vs)) (rest -1)
                                                   (body (body-to-core file body env)))))
                       (let ((v (new-var)))
                         (bind (cdr ps) (cons (product (name (param-name (car ps))) (var v)) env) (cons v vs)))))))
        (bind params env nil))))
  ;; `let`: values outside; `let*`: each sees those before; `letrec`: all see all.
  (let-to-core (->* (string string (listof syn acyclic) (listof syn acyclic) scope) core)
    (lambda (file kind bs body env)
      (let* ((names (letrec ((go (->* ((listof syn acyclic)) strings)
                               (lambda (bs) (if (null? bs) nil (cons (param-name (car bs)) (go (cdr bs)))))))
                      (go bs)))
             (vars (letrec ((go (->* (strings) (listof int acyclic))
                              (lambda (ns) (if (null? ns) nil (cons (new-var) (go (cdr ns)))))))
                     (go names)))
             (inner (letrec ((go (->* (strings (listof int acyclic) scope) scope)
                               (lambda (ns vs env) (if (null? ns) env
                                                       (go (cdr ns) (cdr vs) (cons (product (name (car ns)) (var (car vs))) env))))))
                      (go names vars env))))
        (letrec ((binds (->* ((listof syn acyclic) strings (listof int acyclic) scope) cores)
                   ;; Each binding's value (its last item), in the scope `kind` says.
                   (lambda (bs ns vs scope)
                     (if (null? bs) nil
                         (let* ((is (list-items (car bs)))
                                (value-syn (if (pair? is) (last-syn is) (car bs)))
                                (scope-here (cond ((string=? kind "letrec") inner)
                                                  (else scope)))
                                (value (if (pair? (cdr is)) (named-to-core file value-syn (car ns) scope-here) (k-none nil))))
                           (cons (k-bind (car vs) value)
                                 (binds (cdr bs) (cdr ns) (cdr vs)
                                        (if (string=? kind "let*") (cons (product (name (car ns)) (var (car vs))) scope) scope))))))))
          (k-seq (append-cores (binds bs names vars env) (list (body-to-core file body inner))))))))
  (tagcase-to-core (->* (string syn (listof syn acyclic) scope) core)
    (lambda (file subject arms env)
      (k-case (to-core file subject env)
              (letrec ((go (->* ((listof syn acyclic)) (listof arm acyclic))
                         (lambda (as)
                           (if (null? as) nil
                               (let ((is (list-items (car as))))
                                 (if (and (pair? is) (pair? (cdr is)))
                                     (let* ((tag (sym-of (car is)))
                                            (names (tagcase (car (cdr is))
                                                     (lst (ns d a b) (letrec ((g (->* ((listof syn acyclic)) strings)
                                                                                (lambda (l) (if (null? l) nil (cons (sym-of (car l)) (g (cdr l)))))))
                                                                       (g ns)))
                                                     (else y (the strings (list (sym-of (car (cdr is))))))))
                                            (vars (letrec ((g (->* (strings) (listof int acyclic))
                                                             (lambda (ns) (if (null? ns) nil (cons (new-var) (g (cdr ns)))))))
                                                    (g names)))
                                            (inner (letrec ((g (->* (strings (listof int acyclic) scope) scope)
                                                              (lambda (ns vs env) (if (null? ns) env
                                                                                      (g (cdr ns) (cdr vs) (cons (product (name (car ns)) (var (car vs))) env))))))
                                                     (g names vars env))))
                                       (cons (product (tag (if (string=? tag "else") "" tag)) (vars vars)
                                                      (fields (tagcase (car (cdr is)) (lst (ns d a b) #t) (else y #f)))
                                                      (body (body-to-core file (cdr (cdr is)) inner)))
                                             (go (cdr as))))
                                     (go (cdr as))))))))
                (go arms))))))

"Every name the files' top levels define (their imports too: an imported
name is the module's definition of it, by name), declared a global."
(define declare-globals (->* ((listof (productof (file string) (forms (listof syn acyclic))) acyclic)) unit)
  (lambda (files)
    (if (null? files)
        #u
        (begin
          (letrec ((go (subr numbering (binders) unit)
                     (lambda (bs) (if (null? bs) #u (begin (global-var (extract (car bs) name)) (go (cdr bs)))))))
            (go (items-binders (extract (car files) forms) nil)))
          (declare-globals (cdr files))))))

;;; ------------------------------------------------------------ the analysis
;;;
;;; m-CFA (Might, Smaragdakis and Van Horn, PLDI 2010), as yank's
;;; `cfa.sld` does it: a contour is the last `m` call sites, newest first;
;;; a closure is a lambda and the contour it was made in; a call gives the
;;; callee the contour of the call site pushed onto the caller's, cut to
;;; `m`, and copies the lambda's free variables into it from the closure's.
;;; Locals are addressed by variable and contour; globals and allocation
;;; sites have one address each. At depth 0 every contour is the empty one:
;;; 0CFA. Each (lambda, contour) called, or made, is a task, evaluated
;;; again on every pass until the store stops growing.

"What the analysis does: to its own state, and reading globals' bindings
through the tables' procedures."
(define-effect flow-eff (maxeff (read @fl) (write @fl) (alloc @fl) (read @globals) spin))

"An abstract value: closure `c` as 4c, site `s` as 4s+1, unknown as -1.
A set of them: a sorted list."
(define-type vals (listof int acyclic))
(define unknown int -1)

(define vals-union (subr flow-eff (vals vals) vals)
  (lambda (a b)
    (cond ((null? a) b)
          ((null? b) a)
          ((< (car a) (car b)) (cons (car a) (vals-union (cdr a) b)))
          ((< (car b) (car a)) (cons (car b) (vals-union a (cdr b))))
          (else (cons (car a) (vals-union (cdr a) (cdr b)))))))
(define vals-has? (subr flow-eff (vals int) bool)
  (lambda (s x) (and (pair? s) (or (= (car s) x) (and (< (car s) x) (vals-has? (cdr s) x))))))
(define lambda-val? (subr flow-eff (int) bool) (lambda (x) (and (>= x 0) (= (remainder x 4) 0))))
(define site-val? (subr flow-eff (int) bool) (lambda (x) (and (>= x 0) (= (remainder x 4) 1))))

;; Keys here are pairs packed as `a * 2^20 + b`. The tables choose a
;; bucket by the hash modulo a power of two, so the hash must bring both
;; halves into the low bits: an identity hash put every contour (whose
;; low half was the empty contour, 0) into one bucket.
(define int-hash (subr pure (int) int)
  (lambda (k) (+ (* (quotient k 1048576) 7919) (* (remainder k 1048576) 1000003))))
(define int-same (subr pure (int int) bool) (lambda (a b) (= a b)))

"The analysis's depth: how many call sites a contour keeps (0: 0CFA)."
(define fl-depth (ref int @fl) (new 0))
(define set-flow-depth! (subr flow-eff (int) unit) (lambda (m) (set fl-depth m)))

;; Contours, interned: their numbers by key, and their calls by number.
(define fl-contour-ids (ref (table int int @fl) @fl) (new (the (table int int @fl) (make-table int-hash int-same))))
(define fl-contour-calls (ref (table int ints @fl) @fl) (new (the (table int ints @fl) (make-table int-hash int-same))))
(define fl-contour-count (ref int @fl) (new 0))
;; Closures, interned: a lambda and a contour.
(define fl-closure-ids (ref (table int int @fl) @fl) (new (the (table int int @fl) (make-table int-hash int-same))))
(define fl-closure-lambda (ref (table int int @fl) @fl) (new (the (table int int @fl) (make-table int-hash int-same))))
(define fl-closure-contour (ref (table int int @fl) @fl) (new (the (table int int @fl) (make-table int-hash int-same))))
(define fl-closure-count (ref int @fl) (new 0))

;; The store.
(define-type fields (listof (productof (label string) (vals vals)) acyclic))
(define fl-cells (ref (table int vals @fl) @fl) (new (the (table int vals @fl) (make-table int-hash int-same))))
(define fl-cell-array (ref (arrayof vals @fl) @fl) (new (make-array 0 nil)))
"The keys of the cells made in the table, for measuring (it cannot be
walked: `fx26:table.fx` has no iteration)."
(define fl-cell-keys (ref ints @fl) (new nil))
(define fl-results (ref (table int vals @fl) @fl) (new (the (table int vals @fl) (make-table int-hash int-same))))
(define fl-global (ref (arrayof bool @fl) @fl) (new (make-array 0 #f)))
(define fl-free (ref (arrayof ints @fl) @fl) (new (make-array 0 nil)))
(define fl-fields (ref (arrayof fields @fl) @fl) (new (make-array 0 nil)))
(define fl-callees (ref (arrayof vals @fl) @fl) (new (make-array 0 nil)))
(define fl-escaped (ref (arrayof bool @fl) @fl) (new (make-array 0 #f)))
(define fl-site-escaped (ref (arrayof bool @fl) @fl) (new (make-array 0 #f)))
(define fl-lambda-array (ref (arrayof lambda-info @fl) @fl)
  (new (make-array 0 (product (span (product (file "") (start 0) (end 0))) (name "") (params nil) (rest -1) (body (k-none nil))))))
(define fl-site-array (ref (arrayof site-info @fl) @fl)
  (new (make-array 0 (product (span (product (file "") (start 0) (end 0))) (kind "") (tag "")))))
;; The tasks: closures (a lambda and the contour its body is evaluated in).
(define fl-tasks (ref ints @fl) (new nil))
(define fl-task-seen (ref (table int bool @fl) @fl) (new (the (table int bool @fl) (make-table int-hash int-same))))
(define fl-changed (ref bool @fl) (new #f))

(define take-ints (subr flow-eff (int ints) ints)
  (lambda (n l) (if (or (<= n 0) (null? l)) nil (cons (car l) (take-ints (- n 1) (cdr l))))))
(define ints-key (subr flow-eff (ints) string)
  (lambda (l) (if (null? l) "" (string-append (int->string (car l)) "," (ints-key (cdr l))))))

"A key of two numbers as one."
(define pair-key (subr pure (int int) int) (lambda (a b) (+ (* a 1048576) b)))

"The contour of calls `l`, its number made on first use: interned by its
newest call and the contour of the rest, recursively."
(define contour-of (subr flow-eff (ints) int)
  (lambda (l)
    (if (null? l)
        0
        (let* ((rest (contour-of (cdr l))) (k (pair-key (car l) rest)) (id (table-ref (get fl-contour-ids) k -1)))
          (if (>= id 0) id
              (let ((n (get fl-contour-count)))
                (begin (set fl-contour-count (+ n 1))
                  (table-set! (get fl-contour-ids) k n)
                  (table-set! (get fl-contour-calls) n l)
                  n)))))))

"The closure of lambda `l` made in contour `c`, its number made on first
use: in the empty contour, the lambda's own number; else one past them."
(define closure-of (subr flow-eff (int int) int)
  (lambda (l c)
    (if (= c 0) l
        (let* ((k (pair-key l c)) (id (table-ref (get fl-closure-ids) k -1)))
          (if (>= id 0) id
              (let ((n (+ (get fl-closure-count) (array-length (get fl-lambda-array)))))
                (begin (set fl-closure-count (+ (get fl-closure-count) 1))
                  (table-set! (get fl-closure-ids) k n)
                  (table-set! (get fl-closure-lambda) n l)
                  (table-set! (get fl-closure-contour) n c)
                  n)))))))
(define closure-lambda (subr flow-eff (int) int)
  (lambda (cl) (if (< cl (array-length (get fl-lambda-array))) cl (table-ref (get fl-closure-lambda) cl -1))))
(define closure-contour (subr flow-eff (int) int)
  (lambda (cl) (if (< cl (array-length (get fl-lambda-array))) 0 (table-ref (get fl-closure-contour) cl 0))))

"Small procedures, and lambdas made in them (yank's `call-site-size`):
analysed apart for each call site, even at depth 0."
(define small-size (ref int @fl) (new 0))     ; off: measured to buy no callee here (docs/fx26-analysis.md)
(define set-small-size! (->* (int) unit) (lambda (n) (set small-size n)))
(define fl-small (ref (arrayof int @fl) @fl) (new (make-array 0 0)))   ; 1 small, 2 made in a small one

"The contour a call `call`, made in contour `c`, of closure `cl` gives the
callee: at depth m, the call pushed onto the caller's, cut to m; at depth
0, the call alone for a small procedure, where it was made for a lambda
made in one, and the empty one else."
(define push-contour (subr flow-eff (int int int) int)
  (lambda (call c cl)
    (let ((l (closure-lambda cl)))
      (cond ((> (get fl-depth) 0)
             (contour-of (take-ints (get fl-depth) (cons call (table-ref (get fl-contour-calls) c nil)))))
            ((= (array-ref (get fl-small) l) 1) (contour-of (list call)))
            ((= (array-ref (get fl-small) l) 2) (closure-contour cl))
            (else 0)))))

"Closure `t` to be evaluated: a task, on every pass from now on."
(define ensure-task! (subr flow-eff (int) unit)
  (lambda (t)
    (if (table-ref (get fl-task-seen) t #f)
        #u
        (begin (table-set! (get fl-task-seen) t #t) (set fl-tasks (cons t (get fl-tasks))) (set fl-changed #t)))))

"Element `i` of `cells` given `s` too."
(define join! (subr flow-eff ((arrayof vals @fl) int vals) unit)
  (lambda (cells i s)
    (if (null? s)
        #u
        (let* ((old (array-ref cells i)) (new (vals-union old s)))
          (if (= (length new) (length old)) #u (begin (array-set! cells i new) (set fl-changed #t)))))))

"Variable `v`'s address in contour `c`: a global's is its own."
(define cell-key (subr flow-eff (int int) int)
  (lambda (v c) (+ (* v 1048576) (if (array-ref (get fl-global) v) 0 c))))
(define cell (subr flow-eff (int) vals)
  (lambda (k) (if (= (remainder k 1048576) 0) (array-ref (get fl-cell-array) (quotient k 1048576)) (table-ref (get fl-cells) k nil))))

"The cell at `k` of `table` given `s` too."
(define join-table! (subr flow-eff ((table int vals @fl) int vals) unit)
  (lambda (tbl k s)
    (if (null? s)
        #u
        (let* ((old (table-ref tbl k nil)) (new (vals-union old s)))
          (if (= (length new) (length old)) #u (begin (table-set! tbl k new) (set fl-changed #t)))))))
(define join-cell! (subr flow-eff (int vals) unit)
  (lambda (k s)
    (if (= (remainder k 1048576) 0)
        (join! (get fl-cell-array) (quotient k 1048576) s)
        (begin (if (and (pair? s) (null? (table-ref (get fl-cells) k nil))) (set fl-cell-keys (cons k (get fl-cell-keys))) #u)
          (join-table! (get fl-cells) k s)))))

(define field-of (subr flow-eff (int string) vals)
  (lambda (site label)
    (letrec ((go (->* (fields) vals)
               (lambda (fs) (cond ((null? fs) nil)
                                  ((string=? (extract (car fs) label) label) (extract (car fs) vals))
                                  (else (go (cdr fs)))))))
      (go (array-ref (get fl-fields) site)))))

(define field-join! (subr flow-eff (int string vals) unit)
  (lambda (site label s)
    (if (null? s)
        #u
        (let* ((fs (array-ref (get fl-fields) site))
               (old (field-of site label))
               (new (vals-union old s)))
          (if (= (length new) (length old))
              #u
              (begin
                (array-set! (get fl-fields) site
                            (cons (product (label label) (vals new))
                                  (letrec ((drop (->* (fields) fields)
                                             (lambda (fs) (cond ((null? fs) nil)
                                                                ((string=? (extract (car fs) label) label) (drop (cdr fs)))
                                                                (else (cons (car fs) (drop (cdr fs))))))))
                                    (drop fs))))
                (set fl-changed #t)))))))

(define last-vals (subr flow-eff ((listof vals acyclic)) vals)
  (lambda (l) (if (null? (cdr l)) (car l) (last-vals (cdr l)))))
(define union-all (subr flow-eff ((listof vals acyclic)) vals)
  (lambda (l) (if (null? l) nil (vals-union (car l) (union-all (cdr l))))))
"The callees of a call, by lambda (4l): its operator's closures' lambdas,
and unknown if it may be code not known."
(define filter-callees (subr flow-eff (vals) vals)
  (lambda (ops) (cond ((null? ops) nil)
                      ((lambda-val? (car ops))
                       (vals-union (list (* 4 (closure-lambda (quotient (car ops) 4)))) (filter-callees (cdr ops))))
                      ((= (car ops) unknown) (vals-union (list unknown) (filter-callees (cdr ops))))
                      (else (filter-callees (cdr ops))))))
"The field `label` of the sites in `s` (unknown if `s` may be)."
(define fields-of (subr flow-eff (vals string) vals)
  (lambda (s label)
    (cond ((null? s) nil)
          ((site-val? (car s)) (vals-union (field-of (quotient (car s) 4) label) (fields-of (cdr s) label)))
          ((= (car s) unknown) (vals-union (list unknown) (fields-of (cdr s) label)))
          (else (fields-of (cdr s) label)))))
"The payload of the sum sites in `s` of tag `tag` (any, for \"\")."
(define payload-of (subr flow-eff (vals string) vals)
  (lambda (s tag)
    (cond ((null? s) nil)
          ((site-val? (car s))
           (let ((info (array-ref (get fl-site-array) (quotient (car s) 4))))
             (vals-union (if (and (string=? (extract info kind) "sum")
                                  (or (string=? tag "") (string=? (extract info tag) tag)))
                             (field-of (quotient (car s) 4) "payload")
                             nil)
                         (payload-of (cdr s) tag))))
          ((= (car s) unknown) (vals-union (list unknown) (payload-of (cdr s) tag)))
          (else (payload-of (cdr s) tag)))))
"An arm's variables, in contour `c`, given the payload: all of it, or
(`fields`) its product's fields by position."
(define bind-arm (subr flow-eff (ints bool vals int) unit)
  (lambda (vars fields payload c)
    (cond ((null? vars) #u)
          ((not fields) (join-cell! (cell-key (car vars) c) payload))
          (else
           (letrec ((go (->* (ints int) unit)
                      (lambda (vs i) (if (null? vs) #u
                                         (begin (join-cell! (cell-key (car vs) c) (fields-of payload (int->string i)))
                                           (go (cdr vs) (+ i 1)))))))
             (go vars 1))))))
"Arguments `as` given, in contour `c`, to parameters `ps` (and the rest,
`rest`, if not -1)."
(define pass-args (subr flow-eff (ints int (listof vals acyclic) int) unit)
  (lambda (ps rest as c)
    (cond ((null? ps) (if (>= rest 0) (join-cell! (cell-key rest c) (union-all as)) #u))
          ((null? as) #u)
          (else (begin (join-cell! (cell-key (car ps) c) (car as)) (pass-args (cdr ps) rest (cdr as) c))))))

(define-rec
  ;; What `s` holds escapes to code not known: its closures may be called
  ;; with anything (their bodies evaluated where they were made, their
  ;; parameters unknown there), and what its sites hold escapes too.
  (escape! (subr flow-eff (vals) unit)
    (lambda (s)
      (cond ((null? s) #u)
            ((lambda-val? (car s))
             (let* ((cl (quotient (car s) 4)) (l (closure-lambda cl)) (c (closure-contour cl))
                    (info (array-ref (get fl-lambda-array) l)))
               (begin
                 (if (array-ref (get fl-escaped) l) #u (begin (array-set! (get fl-escaped) l #t) (set fl-changed #t)))
                 (letrec ((params (->* (ints) unit)
                            (lambda (ps) (if (null? ps) #u
                                             (begin (join-cell! (cell-key (car ps) c) (list unknown)) (params (cdr ps)))))))
                   (params (extract info params)))
                 (if (>= (extract info rest) 0) (join-cell! (cell-key (extract info rest) c) (list unknown)) #u)
                 (ensure-task! cl)
                 (escape! (cdr s)))))
            ((site-val? (car s))
             (let ((site (quotient (car s) 4)))
               (begin
                 (if (array-ref (get fl-site-escaped) site)
                     #u
                     (begin
                       (array-set! (get fl-site-escaped) site #t)
                       (letrec ((each (->* (fields) unit)
                                  (lambda (fs) (if (null? fs) #u (begin (escape! (extract (car fs) vals)) (each (cdr fs)))))))
                         (each (array-ref (get fl-fields) site)))))
                 (escape! (cdr s)))))
            (else (escape! (cdr s))))))
  ;; The value of `x` in contour `c`, in the store as it is, joining what it
  ;; does into it.
  (eval-core (subr flow-eff (core int) vals)
    (lambda (x c)
      (tagcase x
        (k-none (xs) (begin (eval-all xs c) nil))
        (k-var (v) (cell (cell-key v c)))
        (k-lam (l) (let ((cl (closure-of l c)))
                     ;; Made: its body evaluated where it was made, whether or not
                     ;; it is called (the runtime calls some: handlers, branches).
                     (begin (ensure-task! cl) (list (* 4 cl)))))
        (k-seq (xs) (let ((vs (eval-all xs c))) (if (null? vs) nil (last-vals vs))))
        (k-alt (xs) (union-all (eval-all xs c)))
        (k-bind (v e) (begin (join-cell! (cell-key v c) (eval-core e c)) nil))
        (k-alloc (site inits)
          (begin
            (letrec ((go (->* ((listof field-init acyclic)) unit)
                       (lambda (is) (if (null? is) #u
                                        (begin (field-join! site (extract (car is) label) (eval-core (extract (car is) value) c))
                                          (go (cdr is)))))))
              (go inits))
            (list (+ 1 (* 4 site)))))
        (k-field (e label) (fields-of (eval-core e c) label))
        (k-store (e label v)
          (let ((targets (eval-core e c)) (s (eval-core v c)))
            (begin
              (letrec ((go (->* (vals) unit)
                         (lambda (ts) (cond ((null? ts) #u)
                                            ((site-val? (car ts)) (begin (field-join! (quotient (car ts) 4) label s) (go (cdr ts))))
                                            ((= (car ts) unknown) (begin (escape! s) (go (cdr ts))))
                                            (else (go (cdr ts)))))))
                (go targets))
              nil)))
        (k-escape (xs) (begin (escape! (union-all (eval-all xs c))) (list unknown)))
        (k-case (e arms)
          (let ((subject (eval-core e c)))
            (union-all
             (letrec ((go (->* ((listof arm acyclic)) (listof vals acyclic))
                        (lambda (as)
                          (if (null? as) nil
                              (let ((a (car as)))
                                (begin
                                  (bind-arm (extract a vars) (extract a fields) (payload-of subject (extract a tag)) c)
                                  (cons (eval-core (extract a body) c) (go (cdr as)))))))))
               (go arms)))))
        (k-app (call f args)
          (let ((ops (eval-core f c)) (as (eval-all args c)))
            (begin
              (join! (get fl-callees) call (filter-callees ops))
              (call-all call c ops as)))))))
  (eval-all (subr flow-eff (cores int) (listof vals acyclic))
    (lambda (xs c) (if (null? xs) nil (let ((v (eval-core (car xs) c))) (cons v (eval-all (cdr xs) c))))))
  ;; Each operator in `ops` called at `call`, in contour `c`, with `as`: the
  ;; union of their results.
  (call-all (subr flow-eff (int int vals (listof vals acyclic)) vals)
    (lambda (call c ops as)
      (cond ((null? ops) nil)
            ((lambda-val? (car ops))
             (let* ((cl (quotient (car ops) 4))
                    (l (closure-lambda cl))
                    (made (closure-contour cl))
                    (c1 (push-contour call c cl))
                    (info (array-ref (get fl-lambda-array) l))
                    (task (closure-of l c1)))
               (begin
                 ;; Its free variables, copied from where it was made.
                 (letrec ((copy (->* (ints) unit)
                            (lambda (vs) (if (null? vs) #u
                                             (begin (join-cell! (cell-key (car vs) c1) (cell (cell-key (car vs) made)))
                                               (copy (cdr vs)))))))
                   (copy (array-ref (get fl-free) l)))
                 (pass-args (extract info params) (extract info rest) as c1)
                 (ensure-task! task)
                 (vals-union (table-ref (get fl-results) task nil) (call-all call c (cdr ops) as)))))
            ((= (car ops) unknown)
             (begin (escape! (union-all as)) (vals-union (list unknown) (call-all call c (cdr ops) as))))
            (else (call-all call c (cdr ops) as))))))

(define-type program-files (listof (productof (file string) (forms (listof syn acyclic))) acyclic))

"The list `l`, newest first, as an array oldest first."
(define lambdas->array (subr flow-eff ((listof lambda-info acyclic) lambda-info) (arrayof lambda-info @fl))
  (lambda (l default)
    (let ((a (the (arrayof lambda-info @fl) (make-array (length l) default))))
      (letrec ((go (->* ((listof lambda-info acyclic) int) unit)
                 (lambda (l i) (if (null? l) #u (begin (array-set! a i (car l)) (go (cdr l) (- i 1)))))))
        (begin (go l (- (length l) 1)) a)))))
(define sites->array (subr flow-eff ((listof site-info acyclic) site-info) (arrayof site-info @fl))
  (lambda (l default)
    (let ((a (the (arrayof site-info @fl) (make-array (length l) default))))
      (letrec ((go (->* ((listof site-info acyclic) int) unit)
                 (lambda (l i) (if (null? l) #u (begin (array-set! a i (car l)) (go (cdr l) (- i 1)))))))
        (begin (go l (- (length l) 1)) a)))))

(define append-ints (subr flow-eff (ints ints) ints)
  (lambda (a b) (if (null? a) b (cons (car a) (append-ints (cdr a) b)))))
(define member-int? (subr flow-eff (int ints) bool)
  (lambda (x l) (and (pair? l) (or (= (car l) x) (member-int? x (cdr l))))))

"The variables `x` refers to and binds (its lambdas' bodies and parameters
included), onto `refs` and `binds`."
(define-type refs-binds (productof (refs ints) (binds ints)))
(define-rec
  (refs-binds-of (subr flow-eff (core refs-binds) refs-binds)
    (lambda (x acc)
      (tagcase x
        (k-none (xs) (refs-binds-all xs acc))
        (k-var (v) (product (refs (cons v (extract acc refs))) (binds (extract acc binds))))
        (k-lam (l) (let ((info (array-ref (get fl-lambda-array) l)))
                     (refs-binds-of (extract info body)
                                    (product (refs (extract acc refs))
                                             (binds (append-ints (extract info params)
                                                                 (if (>= (extract info rest) 0)
                                                                     (cons (extract info rest) (extract acc binds))
                                                                     (extract acc binds))))))))
        (k-app (call f args) (refs-binds-all args (refs-binds-of f acc)))
        (k-seq (xs) (refs-binds-all xs acc))
        (k-alt (xs) (refs-binds-all xs acc))
        (k-bind (v e) (refs-binds-of e (product (refs (extract acc refs)) (binds (cons v (extract acc binds))))))
        (k-alloc (site inits)
          (letrec ((go (->* ((listof field-init acyclic) refs-binds) refs-binds)
                     (lambda (is acc) (if (null? is) acc (go (cdr is) (refs-binds-of (extract (car is) value) acc))))))
            (go inits acc)))
        (k-field (e label) (refs-binds-of e acc))
        (k-store (e label v) (refs-binds-of v (refs-binds-of e acc)))
        (k-escape (xs) (refs-binds-all xs acc))
        (k-case (e arms)
          (letrec ((go (->* ((listof arm acyclic) refs-binds) refs-binds)
                     (lambda (as acc)
                       (if (null? as) acc
                           (go (cdr as) (refs-binds-of (extract (car as) body)
                                                       (product (refs (extract acc refs))
                                                                (binds (append-ints (extract (car as) vars) (extract acc binds))))))))))
            (go arms (refs-binds-of e acc)))))))
  (refs-binds-all (subr flow-eff (cores refs-binds) refs-binds)
    (lambda (xs acc) (if (null? xs) acc (refs-binds-all (cdr xs) (refs-binds-of (car xs) acc))))))

"Lambda `l`'s free variables: those its body refers to, not bound in it,
not global."
(define free-of (subr flow-eff (int) ints)
  (lambda (l)
    (let* ((info (array-ref (get fl-lambda-array) l))
           (rb (refs-binds-of (extract info body)
                              (product (refs nil) (binds (append-ints (extract info params)
                                                                      (if (>= (extract info rest) 0) (list (extract info rest)) nil))))))
           (bound (extract rb binds)))
      (letrec ((go (->* (ints ints) ints)
                 (lambda (rs acc)
                   (cond ((null? rs) acc)
                         ((or (array-ref (get fl-global) (car rs)) (member-int? (car rs) bound) (member-int? (car rs) acc))
                          (go (cdr rs) acc))
                         (else (go (cdr rs) (cons (car rs) acc)))))))
        (go (extract rb refs) nil)))))

"The nodes of `x`, counted no further than `limit`."
(define-rec
  (node-count (subr flow-eff (core int) int)
    (lambda (x limit)
      (if (<= limit 0) 0
          (+ 1 (tagcase x
                 (k-none (xs) (node-count-all xs (- limit 1)))
                 (k-var (v) 0)
                 (k-lam (l) 0)
                 (k-app (call f args) (node-count-all (cons f args) (- limit 1)))
                 (k-seq (xs) (node-count-all xs (- limit 1)))
                 (k-alt (xs) (node-count-all xs (- limit 1)))
                 (k-bind (v e) (node-count e (- limit 1)))
                 (k-alloc (site inits)
                   (node-count-all (letrec ((vs (subr flow-eff ((listof field-init acyclic)) cores)
                                              (lambda (is) (if (null? is) nil (cons (extract (car is) value) (vs (cdr is)))))))
                                     (vs inits))
                                   (- limit 1)))
                 (k-field (e label) (node-count e (- limit 1)))
                 (k-store (e label v) (node-count-all (list e v) (- limit 1)))
                 (k-escape (xs) (node-count-all xs (- limit 1)))
                 (k-case (e arms)
                   (node-count-all (cons e (letrec ((bs (subr flow-eff ((listof arm acyclic)) cores)
                                                      (lambda (as) (if (null? as) nil (cons (extract (car as) body) (bs (cdr as)))))))
                                             (bs arms)))
                                   (- limit 1))))))))
  (node-count-all (subr flow-eff (cores int) int)
    (lambda (xs limit)
      (if (null? xs) 0
          (let ((n (node-count (car xs) limit))) (+ n (node-count-all (cdr xs) (- limit n))))))))

(define global-var-of (subr flow-eff (string) int)
  (lambda (name) (table-ref (get fl-globals) name -1)))

"Whether lambda `l` is a small procedure: named for a definition, not
calling itself by its name, its body of `small-size` nodes or fewer."
(define small-lambda? (subr flow-eff (int) bool)
  (lambda (l)
    (let* ((info (array-ref (get fl-lambda-array) l)) (name (extract info name)) (n (string-length name)))
      (and (> n 0)
           (not (and (>= n 2) (string=? (substring name (- n 2) n) "/λ")))
           (> (get small-size) 0)
           (<= (node-count (extract info body) (+ (get small-size) 1)) (get small-size))
           (not (member-int? (global-var-of name) (extract (refs-binds-of (extract info body) (product (refs nil) (binds nil))) refs)))))))
"Lambda `l` small, and the lambdas made in its body made in a small one."
(define mark-small! (subr flow-eff (int) unit)
  (lambda (l)
    (begin
      (array-set! (get fl-small) l 1)
      (letrec ((inner (subr flow-eff (core) unit)
                 (lambda (x)
                   (tagcase x
                     (k-lam (m) (if (= (array-ref (get fl-small) m) 0)
                                    (begin (array-set! (get fl-small) m 2)
                                      (inner (extract (array-ref (get fl-lambda-array) m) body)))
                                    #u))
                     (k-none (xs) (each xs)) (k-seq (xs) (each xs)) (k-alt (xs) (each xs)) (k-escape (xs) (each xs))
                     (k-app (call f args) (begin (inner f) (each args)))
                     (k-bind (v e) (inner e))
                     (k-alloc (site inits) (letrec ((go (subr flow-eff ((listof field-init acyclic)) unit)
                                                      (lambda (is) (if (null? is) #u (begin (inner (extract (car is) value)) (go (cdr is)))))))
                                             (go inits)))
                     (k-field (e label) (inner e))
                     (k-store (e label v) (begin (inner e) (inner v)))
                     (k-case (e arms) (begin (inner e)
                                        (letrec ((go (subr flow-eff ((listof arm acyclic)) unit)
                                                   (lambda (as) (if (null? as) #u (begin (inner (extract (car as) body)) (go (cdr as)))))))
                                          (go arms))))
                     (else y #u))))
               (each (subr flow-eff (cores) unit)
                 (lambda (xs) (if (null? xs) #u (begin (inner (car xs)) (each (cdr xs)))))))
        (inner (extract (array-ref (get fl-lambda-array) l) body))))))

"The program of `files` analysed at the depth set (`set-flow-depth!`):
its top levels evaluated in the empty contour, and every task, until the
store stops growing. The number of passes."
(define analyze-flow (subr flow-eff (program-files) int)
  (lambda (files)
    (begin
      (set fl-vars 0) (set fl-lambdas nil) (set fl-calls nil) (set fl-sites nil)
      (array-set! fl-counts 0 0) (array-set! fl-counts 1 0) (array-set! fl-counts 2 0)
      (set fl-globals (the (table string int @fl) (make-table string-hash string=?)))
      (declare-globals files)
      (let* ((global-count (get fl-vars))
             (tops (letrec ((go (->* (program-files) cores)
                              (lambda (fs) (if (null? fs) nil
                                               (cons (body-to-core (extract (car fs) file) (extract (car fs) forms) nil)
                                                     (go (cdr fs)))))))
                     (go files))))
        (begin
          (set fl-lambda-array (lambdas->array (get fl-lambdas)
                                               (product (span (product (file "") (start 0) (end 0))) (name "")
                                                        (params nil) (rest -1) (body (k-none nil)))))
          (set fl-site-array (sites->array (get fl-sites) (product (span (product (file "") (start 0) (end 0))) (kind "") (tag ""))))
          ;; The globals are the variables declared first, and those the
          ;; desugaring made for names defined later (global-var).
          (set fl-global (make-array (get fl-vars) #f))
          (letrec ((mark (->* (int) unit)
                     (lambda (v) (if (>= v global-count) #u (begin (array-set! (get fl-global) v #t) (mark (+ v 1)))))))
            (mark 0))
          (set fl-free (make-array (array-length (get fl-lambda-array)) nil))
          (letrec ((frees (->* (int) unit)
                     (lambda (l) (if (>= l (array-length (get fl-lambda-array))) #u
                                     (begin (array-set! (get fl-free) l (free-of l)) (frees (+ l 1)))))))
            (frees 0))
          (set fl-small (make-array (array-length (get fl-lambda-array)) 0))
          (letrec ((mark (subr flow-eff (int) unit)
                     (lambda (l)
                       (if (>= l (array-length (get fl-lambda-array))) #u
                           (begin (if (small-lambda? l) (mark-small! l) #u) (mark (+ l 1)))))))
            (mark 0))
          (set fl-cells (the (table int vals @fl) (make-table int-hash int-same)))
          (set fl-cell-array (make-array (get fl-vars) nil))
          (set fl-cell-keys nil)
          (set fl-results (the (table int vals @fl) (make-table int-hash int-same)))
          (set fl-contour-ids (the (table int int @fl) (make-table int-hash int-same)))
          (set fl-contour-calls (the (table int ints @fl) (make-table int-hash int-same)))
          (set fl-contour-count 1)
          (set fl-closure-ids (the (table int int @fl) (make-table int-hash int-same)))
          (set fl-closure-lambda (the (table int int @fl) (make-table int-hash int-same)))
          (set fl-closure-contour (the (table int int @fl) (make-table int-hash int-same)))
          (set fl-closure-count 0)
          (set fl-tasks nil)
          (set fl-task-seen (the (table int bool @fl) (make-table int-hash int-same)))
          (set fl-fields (make-array (length (get fl-sites)) nil))
          (set fl-callees (make-array (length (get fl-calls)) nil))
          (set fl-escaped (make-array (length (get fl-lambdas)) #f))
          (set fl-site-escaped (make-array (length (get fl-sites)) #f))
          (letrec ((pass (->* (int) int)
                     (lambda (n)
                       (begin
                         (set fl-changed #f)
                         (eval-all tops 0)
                         (letrec ((tasks (->* (ints) unit)
                                    (lambda (ts)
                                      (if (null? ts) #u
                                          (let ((cl (car ts)))
                                            (begin
                                              (join-table! (get fl-results) cl
                                                           (eval-core (extract (array-ref (get fl-lambda-array) (closure-lambda cl)) body)
                                                                      (closure-contour cl)))
                                              (tasks (cdr ts))))))))
                           (tasks (get fl-tasks)))
                         (if (get fl-changed) (pass (+ n 1)) n)))))
            (pass 1)))))))

"`s` with each closure as its lambda (4l)."
(define by-lambda (subr flow-eff (vals) vals)
  (lambda (s)
    (cond ((null? s) nil)
          ((lambda-val? (car s)) (vals-union (list (* 4 (closure-lambda (quotient (car s) 4)))) (by-lambda (cdr s))))
          (else (vals-union (list (car s)) (by-lambda (cdr s)))))))

"For measuring: the values each local variable can hold, merged over its
contours, summed over the variables; and how many hold more than one."
(define flow-value-precision (subr flow-eff () (productof (total int) (several int)))
  (lambda ()
    (let ((merged (the (arrayof vals @fl) (make-array (get fl-vars) nil))))
      (begin
        (begin
          (letrec ((go (subr flow-eff (int) unit)
                     (lambda (v) (if (>= v (get fl-vars)) #u
                                     (begin (array-set! merged v (array-ref (get fl-cell-array) v)) (go (+ v 1)))))))
            (go 0))
          (letrec ((go (subr flow-eff (ints) unit)
                     (lambda (ks) (if (null? ks) #u
                                      (let ((v (quotient (car ks) 1048576)))
                                        (begin (array-set! merged v (vals-union (array-ref merged v) (table-ref (get fl-cells) (car ks) nil)))
                                          (go (cdr ks))))))))
            (go (get fl-cell-keys))))
        (letrec ((tally (subr flow-eff (int int int) (productof (total int) (several int)))
                   (lambda (v total several)
                     (if (>= v (get fl-vars)) (product (total total) (several several))
                         (if (array-ref (get fl-global) v)
                             (tally (+ v 1) total several)
                             ;; Closures counted by their lambdas: a lambda made in
                             ;; several contours is one value to whoever reads it.
                             (let ((n (length (by-lambda (array-ref merged v)))))
                               (tally (+ v 1) (+ total n) (if (> n 1) (+ several 1) several))))))))
          (tally 0 0 0))))))

"How many tasks (a lambda in a contour) the last analysis evaluated."
(define flow-task-count (subr flow-eff () int) (lambda () (length (get fl-tasks))))

;;; ------------------------------------------------------------ results

"A call's callees, as found: where the call is, where its operator is,
the lambdas it may call (their spans and names), and whether it may call
code not known."
(define-type callee (productof (span fl-span) (name string)))
(define-type call-result (productof (span fl-span) (operator fl-span) (callees (listof callee acyclic)) (unknown bool)))

(define flow-calls (->* () (listof call-result acyclic))
  (lambda ()
    (let ((calls (get fl-calls)))
      (letrec ((go (->* ((listof call-info acyclic) int (listof call-result acyclic)) (listof call-result acyclic))
                 ;; The calls, newest first, numbered down from `i`.
                 (lambda (cs i acc)
                   (if (null? cs) acc
                       (let ((vs (array-ref (get fl-callees) i)))
                         (go (cdr cs) (- i 1)
                             (cons (product (span (extract (car cs) span)) (operator (extract (car cs) operator))
                                            (callees (letrec ((ls (->* (vals) (listof callee acyclic))
                                                                (lambda (vs) (cond ((null? vs) nil)
                                                                                   ((lambda-val? (car vs))
                                                                                    (let ((info (array-ref (get fl-lambda-array) (quotient (car vs) 4))))
                                                                                      (cons (product (span (extract info span)) (name (extract info name)))
                                                                                            (ls (cdr vs)))))
                                                                                   (else (ls (cdr vs)))))))
                                                       (ls vs)))
                                            (unknown (vals-has? vs unknown)))
                                   acc)))))))
        (go calls (- (length calls) 1) nil)))))
))
