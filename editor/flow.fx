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
"A `tagcase` arm: its tag (\"\" for `else`), the variables it binds (one:
the payload; or several: the payload's fields by position, labels `1`,
`2`, …), its body."
(define-type arm (productof (tag string) (vars (listof int acyclic)) (body core)))
(define-type cores (listof core acyclic))

;;; ------------------------------------------------------------ numbering

(define-type span (productof (file string) (start int) (end int)))
(define-type lambda-info (productof (span span) (name string) (params (listof int acyclic)) (rest int) (body core)))
(define-type call-info (productof (span span) (operator span)))
(define-type site-info (productof (span span) (kind string) (tag string)))

(define fl-vars (ref int @fl) (new 0))
(define fl-lambdas (ref (listof lambda-info acyclic) @fl) (new nil))   ; newest first
(define fl-calls (ref (listof call-info acyclic) @fl) (new nil))
(define fl-sites (ref (listof site-info acyclic) @fl) (new nil))
(define fl-globals (ref (listof (productof (name string) (var int)) acyclic) @fl) (new nil))
"The definition being read, to name the lambdas in it: `move-by/λ`."
(define fl-definition (ref string @fl) (new ""))

(define-effect numbering (maxeff (read @fl) (write @fl) spin))

(define new-var (->* () int)
  (lambda () (let ((n (get fl-vars))) (begin (set fl-vars (+ n 1)) n))))

"The variable of global `name`, made on first use."
(define global-var (->* (string) int)
  (lambda (name)
    (letrec ((go (subr spin ((listof (productof (name string) (var int)) acyclic)) int)
               (lambda (gs) (cond ((null? gs) -1)
                                  ((string=? (extract (car gs) name) name) (extract (car gs) var))
                                  (else (go (cdr gs)))))))
      (let ((v (go (get fl-globals))))
        (if (>= v 0)
            v
            (let ((n (new-var)))
              (begin (set fl-globals (cons (product (name name) (var n)) (get fl-globals))) n)))))))

(define filter-globals (->* (string (listof (productof (name string) (var int)) acyclic)) (listof int acyclic))
  (lambda (name gs) (cond ((null? gs) nil)
                          ((string=? (extract (car gs) name) name) (cons (extract (car gs) var) nil))
                          (else (filter-globals name (cdr gs))))))

(define global-defined? (->* (string) bool)
  (lambda (name) (pair? (filter-globals name (get fl-globals)))))
(define add-lambda (->* (lambda-info) int)
  (lambda (info) (begin (set fl-lambdas (cons info (get fl-lambdas))) (- (length (get fl-lambdas)) 1))))
(define add-call (->* (call-info) int)
  (lambda (info) (begin (set fl-calls (cons info (get fl-calls))) (- (length (get fl-calls)) 1))))
(define add-site (->* (site-info) int)
  (lambda (info) (begin (set fl-sites (cons info (get fl-sites))) (- (length (get fl-sites)) 1))))

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
(define span-of (->* (string syn) span)
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
        ((or (string=? head "define-type") (string=? head "define-effect") (string=? head "define-datatype")
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

"An abstract value: lambda `l` as 4l, site `s` as 4s+1, unknown as -1.
A set of them: a sorted list."
(define-type vals (listof int acyclic))
(define unknown int -1)

(define vals-union (->* (vals vals) vals)
  (lambda (a b)
    (cond ((null? a) b)
          ((null? b) a)
          ((< (car a) (car b)) (cons (car a) (vals-union (cdr a) b)))
          ((< (car b) (car a)) (cons (car b) (vals-union a (cdr b))))
          (else (cons (car a) (vals-union (cdr a) (cdr b)))))))
(define vals-has? (->* (vals int) bool)
  (lambda (s x) (and (pair? s) (or (= (car s) x) (and (< (car s) x) (vals-has? (cdr s) x))))))
(define lambda-val? (->* (int) bool) (lambda (x) (and (>= x 0) (= (remainder x 4) 0))))
(define site-val? (->* (int) bool) (lambda (x) (and (>= x 0) (= (remainder x 4) 1))))

;; The store: a cell per variable, per lambda's result, per site's fields
;; (an association list from label), per call's callees; and what has
;; escaped. Made when the core is complete, sized by its numbers.
(define-type fields (listof (productof (label string) (vals vals)) acyclic))
(define fl-var-cells (ref (arrayof vals @fl) @fl) (new (make-array 0 nil)))
(define fl-results (ref (arrayof vals @fl) @fl) (new (make-array 0 nil)))
(define fl-fields (ref (arrayof fields @fl) @fl) (new (make-array 0 nil)))
(define fl-callees (ref (arrayof vals @fl) @fl) (new (make-array 0 nil)))
(define fl-escaped (ref (arrayof bool @fl) @fl) (new (make-array 0 #f)))
(define fl-site-escaped (ref (arrayof bool @fl) @fl) (new (make-array 0 #f)))
(define fl-lambda-array (ref (arrayof lambda-info @fl) @fl)
  (new (make-array 0 (product (span (product (file "") (start 0) (end 0))) (name "") (params nil) (rest -1) (body (k-none nil))))))
(define fl-site-array (ref (arrayof site-info @fl) @fl)
  (new (make-array 0 (product (span (product (file "") (start 0) (end 0))) (kind "") (tag "")))))
(define fl-changed (ref bool @fl) (new #f))

"Cell `i` of `cells` given `s` too: whether it grew."
(define join! (->* ((arrayof vals @fl) int vals) unit)
  (lambda (cells i s)
    (if (null? s)
        #u
        (let* ((old (array-ref cells i)) (new (vals-union old s)))
          (if (= (length new) (length old)) #u (begin (array-set! cells i new) (set fl-changed #t)))))))

(define field-of (->* (int string) vals)
  (lambda (site label)
    (letrec ((go (->* (fields) vals)
               (lambda (fs) (cond ((null? fs) nil)
                                  ((string=? (extract (car fs) label) label) (extract (car fs) vals))
                                  (else (go (cdr fs)))))))
      (go (array-ref (get fl-fields) site)))))

(define field-join! (->* (int string vals) unit)
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

(define last-vals (->* ((listof vals acyclic)) vals)
  (lambda (l) (if (null? (cdr l)) (car l) (last-vals (cdr l)))))
(define union-all (->* ((listof vals acyclic)) vals)
  (lambda (l) (if (null? l) nil (vals-union (car l) (union-all (cdr l))))))
"The callees of a call: its operator's lambdas, and unknown if it may be
code not known."
(define filter-callees (->* (vals) vals)
  (lambda (ops) (cond ((null? ops) nil)
                      ((or (lambda-val? (car ops)) (= (car ops) unknown)) (cons (car ops) (filter-callees (cdr ops))))
                      (else (filter-callees (cdr ops))))))
"The field `label` of the sites in `s` (unknown if `s` may be)."
(define fields-of (->* (vals string) vals)
  (lambda (s label)
    (cond ((null? s) nil)
          ((site-val? (car s)) (vals-union (field-of (quotient (car s) 4) label) (fields-of (cdr s) label)))
          ((= (car s) unknown) (vals-union (list unknown) (fields-of (cdr s) label)))
          (else (fields-of (cdr s) label)))))
"The payload of the sum sites in `s` of tag `tag` (any, for \"\")."
(define payload-of (->* (vals string) vals)
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
"An arm's variables given the payload: one, all of it; several, its
product's fields by position."
(define bind-arm (->* ((listof int acyclic) vals) unit)
  (lambda (vars payload)
    (cond ((null? vars) #u)
          ((null? (cdr vars)) (join! (get fl-var-cells) (car vars) payload))
          (else
           (letrec ((go (->* ((listof int acyclic) int) unit)
                      (lambda (vs i) (if (null? vs) #u
                                         (begin (join! (get fl-var-cells) (car vs) (fields-of payload (int->string i)))
                                                (go (cdr vs) (+ i 1)))))))
             (go vars 1))))))
"Arguments `as` given to parameters `ps` (and the rest, `rest` if not -1)."
(define pass-args (->* ((listof int acyclic) int (listof vals acyclic)) unit)
  (lambda (ps rest as)
    (cond ((null? ps) (if (>= rest 0) (join! (get fl-var-cells) rest (union-all as)) #u))
          ((null? as) #u)
          (else (begin (join! (get fl-var-cells) (car ps) (car as)) (pass-args (cdr ps) rest (cdr as)))))))

"What `s` holds escapes to code not known: its lambdas may be called with
anything, and what its sites hold escapes too."
(define-rec
  (escape! (->* (vals) unit)
    (lambda (s)
      (cond ((null? s) #u)
            ((lambda-val? (car s))
             (let ((l (quotient (car s) 4)))
               (begin
                 (if (array-ref (get fl-escaped) l)
                     #u
                     (let ((info (array-ref (get fl-lambda-array) l)))
                       (begin
                         (array-set! (get fl-escaped) l #t)
                         (set fl-changed #t)
                         (letrec ((params (->* ((listof int acyclic)) unit)
                                    (lambda (ps) (if (null? ps) #u
                                                     (begin (join! (get fl-var-cells) (car ps) (list unknown)) (params (cdr ps)))))))
                           (params (extract info params)))
                         (if (>= (extract info rest) 0) (join! (get fl-var-cells) (extract info rest) (list unknown)) #u))))
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
  ;; The value of `x` in the store as it is, joining what it does into it.
  (eval-core (->* (core) vals)
    (lambda (x)
      (tagcase x
        (k-none (xs) (begin (eval-all xs) nil))
        (k-var (v) (array-ref (get fl-var-cells) v))
        (k-lam (l) (list (* 4 l)))
        (k-seq (xs) (let ((vs (eval-all xs))) (if (null? vs) nil (last-vals vs))))
        (k-alt (xs) (union-all (eval-all xs)))
        (k-bind (v e) (begin (join! (get fl-var-cells) v (eval-core e)) nil))
        (k-alloc (site inits)
          (begin
            (letrec ((go (->* ((listof field-init acyclic)) unit)
                       (lambda (is) (if (null? is) #u
                                        (begin (field-join! site (extract (car is) label) (eval-core (extract (car is) value)))
                                               (go (cdr is)))))))
              (go inits))
            (list (+ 1 (* 4 site)))))
        (k-field (e label) (fields-of (eval-core e) label))
        (k-store (e label v)
          (let ((targets (eval-core e)) (s (eval-core v)))
            (begin
              (letrec ((go (->* (vals) unit)
                         (lambda (ts) (cond ((null? ts) #u)
                                            ((site-val? (car ts)) (begin (field-join! (quotient (car ts) 4) label s) (go (cdr ts))))
                                            ((= (car ts) unknown) (begin (escape! s) (go (cdr ts))))
                                            (else (go (cdr ts)))))))
                (go targets))
              nil)))
        (k-escape (xs) (begin (escape! (union-all (eval-all xs))) (list unknown)))
        (k-case (e arms)
          (let ((subject (eval-core e)))
            (union-all
             (letrec ((go (->* ((listof arm acyclic)) (listof vals acyclic))
                        (lambda (as)
                          (if (null? as) nil
                              (let* ((a (car as))
                                     (payload (payload-of subject (extract a tag))))
                                (begin
                                  (bind-arm (extract a vars) payload)
                                  (cons (eval-core (extract a body)) (go (cdr as)))))))))
               (go arms)))))
        (k-app (c f args)
          (let ((ops (eval-core f)) (as (eval-all args)))
            (begin
              (join! (get fl-callees) c (filter-callees ops))
              (call-all ops as)))))))
  (eval-all (->* (cores) (listof vals acyclic))
    (lambda (xs) (if (null? xs) nil (let ((v (eval-core (car xs)))) (cons v (eval-all (cdr xs)))))))
  ;; Each operator in `ops` called with `as`: the union of their results.
  (call-all (->* (vals (listof vals acyclic)) vals)
    (lambda (ops as)
      (cond ((null? ops) nil)
            ((lambda-val? (car ops))
             (let* ((l (quotient (car ops) 4)) (info (array-ref (get fl-lambda-array) l)))
               (begin
                 (pass-args (extract info params) (extract info rest) as)
                 (vals-union (array-ref (get fl-results) l) (call-all (cdr ops) as)))))
            ((= (car ops) unknown)
             (begin (escape! (union-all as)) (vals-union (list unknown) (call-all (cdr ops) as))))
            (else (call-all (cdr ops) as))))))

(define-type program-files (listof (productof (file string) (forms (listof syn acyclic))) acyclic))

"The list `l`, newest first, as an array oldest first."
(define lambdas->array (->* ((listof lambda-info acyclic) lambda-info) (arrayof lambda-info @fl))
  (lambda (l default)
    (let ((a (the (arrayof lambda-info @fl) (make-array (length l) default))))
      (letrec ((go (->* ((listof lambda-info acyclic) int) unit)
                 (lambda (l i) (if (null? l) #u (begin (array-set! a i (car l)) (go (cdr l) (- i 1)))))))
        (begin (go l (- (length l) 1)) a)))))
(define sites->array (->* ((listof site-info acyclic) site-info) (arrayof site-info @fl))
  (lambda (l default)
    (let ((a (the (arrayof site-info @fl) (make-array (length l) default))))
      (letrec ((go (->* ((listof site-info acyclic) int) unit)
                 (lambda (l i) (if (null? l) #u (begin (array-set! a i (car l)) (go (cdr l) (- i 1)))))))
        (begin (go l (- (length l) 1)) a)))))

"The program of `files` analysed: its top levels and every lambda's body
evaluated until the store stops growing. The number of passes."
(define analyze-flow (->* (program-files) int)
  (lambda (files)
    (begin
      (set fl-vars 0) (set fl-lambdas nil) (set fl-calls nil) (set fl-sites nil) (set fl-globals nil)
      (declare-globals files)
      (let ((tops (letrec ((go (->* (program-files) cores)
                             (lambda (fs) (if (null? fs) nil
                                              (cons (body-to-core (extract (car fs) file) (extract (car fs) forms) nil)
                                                    (go (cdr fs)))))))
                    (go files))))
        (begin
          (set fl-lambda-array (lambdas->array (get fl-lambdas)
                                               (product (span (product (file "") (start 0) (end 0))) (name "")
                                                        (params nil) (rest -1) (body (k-none nil)))))
          (set fl-site-array (sites->array (get fl-sites) (product (span (product (file "") (start 0) (end 0))) (kind "") (tag ""))))
          (set fl-var-cells (make-array (get fl-vars) nil))
          (set fl-results (make-array (length (get fl-lambdas)) nil))
          (set fl-fields (make-array (length (get fl-sites)) nil))
          (set fl-callees (make-array (length (get fl-calls)) nil))
          (set fl-escaped (make-array (length (get fl-lambdas)) #f))
          (set fl-site-escaped (make-array (length (get fl-sites)) #f))
          (letrec ((pass (->* (int) int)
                     (lambda (n)
                       (begin
                         (set fl-changed #f)
                         (eval-all tops)
                         (letrec ((bodies (->* (int) unit)
                                    (lambda (l)
                                      (if (>= l (array-length (get fl-lambda-array))) #u
                                          (begin (join! (get fl-results) l
                                                        (eval-core (extract (array-ref (get fl-lambda-array) l) body)))
                                                 (bodies (+ l 1)))))))
                           (bodies 0))
                         (if (get fl-changed) (pass (+ n 1)) n)))))
            (pass 1)))))))

;;; ------------------------------------------------------------ results

"A call's callees, as found: where the call is, where its operator is,
the lambdas it may call (their spans and names), and whether it may call
code not known."
(define-type callee (productof (span span) (name string)))
(define-type call-result (productof (span span) (operator span) (callees (listof callee acyclic)) (unknown bool)))

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
