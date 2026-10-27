;;; analyze.fx: what a Scheme text is, for an editor -- read, and walked,
;;; never run (the server's `analyze`; editor/scheme.fx shows it).
;;;
;;; What it finds:
;;;   - faces: comments and strings (by scanning), the heads of special
;;;     forms and macros (keyword), and the names definitions define
;;;     (function-name);
;;;   - definitions: each name a top-level form defines, and where;
;;;   - references: each use of a local variable, and its binder;
;;;   - the first read error, and where.
;;;
;;; It walks what the reader read, knowing R7RS's binding forms, as yank's
;;; `(yank analysis core)` does: a form it does not know is taken for an
;;; application, so its parts are still walked, and it never fails on odd
;;; input. It expands no macro, and changes no global: a text not yet run
;;; may be analysed (docs/s7st.md, "Openings"). Where each symbol is comes
;;; from the reader's item spans (read.fx's `s7-item-spans`).

(define-type s7-face-span (productof (start int) (end int) (face symbol)))
(define-type s7-face-spans (listof s7-face-span acyclic))
(define-type s7-def (productof (name string) (start int) (end int)))
(define-type s7-aref (productof (start int) (end int) (binder-start int) (binder-end int)))
(define-type s7-analysis
  (productof (faces s7-face-spans) (defs (listof s7-def acyclic)) (refs (listof s7-aref acyclic))
             (problem string) (problem-at int)))
"A binder in scope: its name, and where it is."
(define-type s7-binder (productof (name symbol) (span s7-span)))
(define-type s7-binders (listof s7-binder acyclic))
"A datum and where it was read."
(define-type s7-item (productof (value s7-value) (span s7-span)))
(define-type s7-itemized (listof s7-item acyclic))

"What an analysis has found so far, last first."
(define s7-an-faces (ref s7-face-spans @sc) (new nil))
(define s7-an-defs (ref (listof s7-def acyclic) @sc) (new nil))
(define s7-an-refs (ref (listof s7-aref acyclic) @sc) (new nil))

(define* s7-an-face! (subr s7-eff (s7-span symbol) unit)
  (lambda (sp f)
    (if (< (extract sp start) 0) #u
        (set s7-an-faces (cons (product (start (extract sp start)) (end (extract sp end)) (face f)) (get s7-an-faces))))))
(define* s7-an-def! (subr s7-eff (symbol s7-span) unit)
  (lambda (name sp)
    (if (< (extract sp start) 0) #u
        (begin (set s7-an-defs (cons (product (name (s7-symbol-name name)) (start (extract sp start)) (end (extract sp end))) (get s7-an-defs)))
          (s7-an-face! sp 'function-name)))))

"List `x`'s items, each with where it was read (`span`, if not known)."
(define* s7-an-items (subr s7-eff (s7-value s7-span) s7-itemized)
  (lambda (x span)
    (tagcase x
      (pair p (let ((v (get (extract p car))))
                (cons (product (value v) (span (let ((s (s7-span-of v))) (if (>= (extract s start) 0) s (s7-item-span p span)))))
                      (s7-an-items (get (extract p cdr)) span))))
      (else y nil))))
"What ends list `x`: () if it is proper, else its dotted tail."
(define* s7-an-tail (subr (maxeff spin (read @sc)) (s7-value) s7-value)
  (lambda (x) (tagcase x (pair p (s7-an-tail (get (extract p cdr)))) (else y y))))
(define* s7-an-lookup (subr spin (symbol s7-binders) (sumof (none unit) (found s7-span)))
  (lambda (s env)
    (cond ((null? env) (sum none #u))
          ((eq? (extract (car env) name) s) (sum found (extract (car env) span)))
          (else (s7-an-lookup s (cdr env))))))
"Formals `x` (read at `span`): their binders, a dotted rest's too."
(define* s7-an-formals (subr s7-eff (s7-value s7-span) s7-binders)
  (lambda (x span)
    (letrec ((go (subr s7-eff (s7-itemized) s7-binders)
               (lambda (l) (cond ((null? l) nil)
                                 ((s7-symbol? (extract (car l) value))
                                  (cons (product (name (s7-sym (extract (car l) value))) (span (extract (car l) span))) (go (cdr l))))
                                 (else (go (cdr l)))))))
      (cond ((s7-symbol? x) (list (product (name (s7-sym x)) (span span))))
            (else (let ((t (s7-an-tail x)))
                    (append (go (s7-an-items x span))
                            (if (s7-symbol? t) (list (product (name (s7-sym t)) (span span))) nil))))))))
(define* s7-an-append (subr spin (s7-binders s7-binders) s7-binders)
  (lambda (a b) (if (null? a) b (cons (car a) (s7-an-append (cdr a) b)))))
"Whether a head named `s` (not bound locally) is syntax: a special form, or
a macro the top level knows (the prelude's, a program's)."
(define* s7-an-syntax? (subr s7-eff (symbol) bool)
  (lambda (s)
    (tagcase (s7-ns-find s7-toplevel s)
      (found c (tagcase (get (extract c syntax)) (none u #f) (else y #t)))
      (none u #f))))

(define-rec
  ;; Form `x`, read at `span`, with binders `env` in scope; `top`: at top level.
  (s7-an-form (->* (s7-value s7-span s7-binders bool) unit)
    (lambda (x span env top)
      (tagcase x
        (sym s (tagcase (s7-an-lookup s env)
                 (found b (if (or (< (extract span start) 0) (< (extract b start) 0)) #u
                              (set s7-an-refs (cons (product (start (extract span start)) (end (extract span end))
                                                             (binder-start (extract b start)) (binder-end (extract b end)))
                                                    (get s7-an-refs)))))
                 (none u #u)))
        (pair p
          (let* ((items (s7-an-items x span))
                 (head (extract (car items) value))
                 (hspan (extract (car items) span))
                 (args (cdr items))
                 (name (if (and (s7-symbol? head) (tagcase (s7-an-lookup (s7-sym head) env) (none u #t) (found b #f))
                                (s7-an-syntax? (s7-sym head)))
                           (s7-symbol-name (s7-sym head)) "")))
            (if (string=? name "")
                (s7-an-all items env)
                (begin
                  (s7-an-face! hspan 'keyword)
                  (s7-an-special name args span env top)))))
        (else y #u))))
  (s7-an-all (->* (s7-itemized s7-binders) unit)
    (lambda (items env)
      (if (null? items) #u
          (begin (s7-an-form (extract (car items) value) (extract (car items) span) env #f) (s7-an-all (cdr items) env)))))
  ;; A body: the names its definitions bind found first, then each form walked.
  (s7-an-body (->* (s7-itemized s7-binders bool) unit)
    (lambda (forms env top)
      (let ((inner (if top env (s7-an-append (s7-an-defined forms) env))))
        (letrec ((go (->* (s7-itemized) unit)
                   (lambda (l) (if (null? l) #u (begin (s7-an-form (extract (car l) value) (extract (car l) span) inner top) (go (cdr l)))))))
          (go forms)))))
  ;; The binders the definitions among `forms` make (in a body).
  (s7-an-defined (->* (s7-itemized) s7-binders)
    (lambda (forms)
      (if (null? forms) nil
          (let* ((x (extract (car forms) value))
                 (items (s7-an-items x (extract (car forms) span)))
                 (head (if (pair? items) (s7-symbol-name (s7-sym (extract (car items) value))) ""))
                 (rest (s7-an-defined (cdr forms))))
            (cond ((null? items) rest)
                  ((string=? head "begin") (s7-an-append (s7-an-defined (cdr items)) rest))
                  ((and (string=? head "define") (pair? (cdr items)))
                   (let ((target (car (cdr items))))
                     (s7-an-append (s7-an-target-binder (extract target value) (extract target span)) rest)))
                  ((and (string=? head "define-values") (pair? (cdr items)))
                   (s7-an-append (s7-an-formals (extract (car (cdr items)) value) (extract (car (cdr items)) span)) rest))
                  ((string=? head "define-record-type")
                   (s7-an-append (s7-an-record-binders (cdr items)) rest))
                  (else rest))))))
  ;; The name `(define TARGET …)` defines: TARGET, or the name in `(name . formals)`.
  (s7-an-target-binder (->* (s7-value s7-span) s7-binders)
    (lambda (t span)
      (cond ((s7-symbol? t) (list (product (name (s7-sym t)) (span span))))
            ((s7-pair? t) (let ((items (s7-an-items t span)))
                            (s7-an-target-binder (extract (car items) value) (extract (car items) span))))
            (else nil))))
  ;; What `(define-record-type name ctor pred field …)` binds.
  (s7-an-record-binders (->* (s7-itemized) s7-binders)
    (lambda (items)
      (letrec ((syms (->* (s7-itemized) s7-binders)
                 (lambda (l) (cond ((null? l) nil)
                                   ((s7-symbol? (extract (car l) value))
                                    (cons (product (name (s7-sym (extract (car l) value))) (span (extract (car l) span))) (syms (cdr l))))
                                   ((s7-pair? (extract (car l) value))
                                    ;; A constructor's `(ctor field …)`, a field's `(field accessor modifier)`: all but the field names.
                                    (let ((inner (s7-an-items (extract (car l) value) (extract (car l) span))))
                                      (s7-an-append (if (pair? inner) (syms (list (car inner))) nil) (syms (cdr l)))))
                                   (else (syms (cdr l)))))))
        (if (null? items) nil
            (s7-an-append (syms (list (car items)))
                          (s7-an-append (syms (if (pair? (cdr items)) (list (car (cdr items))) nil))
                                        (letrec ((fields (->* (s7-itemized) s7-binders)
                                                   (lambda (l) (cond ((null? l) nil)
                                                                     ((s7-pair? (extract (car l) value))
                                                                      (s7-an-append (syms (cdr (s7-an-items (extract (car l) value) (extract (car l) span))))
                                                                                    (fields (cdr l))))
                                                                     ((s7-symbol? (extract (car l) value))
                                                                      (cons (product (name (s7-sym (extract (car l) value))) (span (extract (car l) span)))
                                                                            (fields (cdr l))))
                                                                     (else (fields (cdr l)))))))
                                          (fields (if (pair? (cdr items)) (cdr (cdr items)) nil)))))))))
  ;; Special form or macro `name`, its operands `args`.
  (s7-an-special (->* (string s7-itemized s7-span s7-binders bool) unit)
    (lambda (name args span env top)
      (let ((first (lambda () (if (pair? args) (car args) (product (value s7-nil) (span span)))))
            (rest (if (pair? args) (cdr args) nil)))
        (cond
          ((or (string=? name "quote") (string=? name "syntax-rules")) #u)
          ((string=? name "quasiquote") (s7-an-qq (extract (first) value) (extract (first) span) env))
          ((string=? name "lambda")
           (s7-an-body rest (s7-an-append (s7-an-formals (extract (first) value) (extract (first) span)) env) #f))
          ((string=? name "case-lambda")
           (letrec ((go (->* (s7-itemized) unit)
                      (lambda (cs) (if (null? cs) #u
                                       (let ((c (s7-an-items (extract (car cs) value) (extract (car cs) span))))
                                         (begin (if (pair? c)
                                                    (s7-an-body (cdr c) (s7-an-append (s7-an-formals (extract (car c) value) (extract (car c) span)) env) #f)
                                                    #u)
                                           (go (cdr cs))))))))
             (go args)))
          ((string=? name "define")
           (let* ((t (first)) (tv (extract t value)))
             (if (s7-pair? tv)
                 ;; (define (name . formals) body …), curried perhaps.
                 (let* ((titems (s7-an-items tv (extract t span)))
                        (formals (s7-an-formals (s7-cdr tv) (extract t span))))
                   (begin
                     (s7-an-name-def (extract (car titems) value) (extract (car titems) span) env top)
                     (s7-an-body rest (s7-an-append formals env) #f)))
                 (begin (s7-an-name-def tv (extract t span) env top) (s7-an-all rest env)))))
          ((or (string=? name "define-syntax") (string=? name "define-values"))
           (let ((t (first)))
             (begin
               (if (string=? name "define-syntax")
                   (s7-an-name-def (extract t value) (extract t span) env top)
                   (letrec ((each (->* (s7-binders) unit)
                              (lambda (bs) (if (null? bs) #u (begin (if top (s7-an-def! (extract (car bs) name) (extract (car bs) span)) #u) (each (cdr bs)))))))
                     (each (s7-an-formals (extract t value) (extract t span)))))
               (if (string=? name "define-values") (s7-an-all rest env) #u))))
          ((string=? name "define-record-type")
           (letrec ((each (->* (s7-binders) unit)
                      (lambda (bs) (if (null? bs) #u
                                       (begin (if top (s7-an-def! (extract (car bs) name) (extract (car bs) span))
                                                  (s7-an-face! (extract (car bs) span) 'function-name))
                                         (each (cdr bs)))))))
             (each (s7-an-record-binders args))))
          ((or (string=? name "let") (string=? name "let*") (string=? name "letrec") (string=? name "letrec*"))
           (if (s7-symbol? (extract (first) value))
               ;; A named let: its name bound in its body; its initial values outside.
               (let* ((loop (product (name (s7-sym (extract (first) value))) (span (extract (first) span))))
                      (bs (if (pair? rest) (s7-an-items (extract (car rest) value) (extract (car rest) span)) nil))
                      (vars (s7-an-binding-names bs)))
                 (begin (s7-an-inits bs env)
                        (s7-an-body (if (pair? rest) (cdr rest) nil) (cons loop (s7-an-append vars env)) #f)))
               (let* ((bs (s7-an-items (extract (first) value) (extract (first) span)))
                      (vars (s7-an-binding-names bs))
                      (inner (s7-an-append vars env)))
                 (begin
                   (cond ((string=? name "let") (s7-an-inits bs env))
                         ((string=? name "let*") (s7-an-inits-sequential bs env))
                         (else (s7-an-inits bs inner)))
                   (s7-an-body rest inner #f)))))
          ((or (string=? name "let-values") (string=? name "let*-values"))
           (let* ((bs (s7-an-items (extract (first) value) (extract (first) span)))
                  (vars (letrec ((go (->* (s7-itemized) s7-binders)
                                   (lambda (l) (if (null? l) nil
                                                   (let ((b (s7-an-items (extract (car l) value) (extract (car l) span))))
                                                     (s7-an-append (if (pair? b) (s7-an-formals (extract (car b) value) (extract (car b) span)) nil)
                                                                   (go (cdr l))))))))
                          (go bs))))
             (begin (s7-an-inits bs env) (s7-an-body rest (s7-an-append vars env) #f))))
          ((string=? name "do")
           (let* ((bs (s7-an-items (extract (first) value) (extract (first) span)))
                  (inner (s7-an-append (s7-an-binding-names bs) env)))
             (begin
               (s7-an-inits bs env)
               ;; Steps, the test and its results, and the body: inside.
               (letrec ((steps (->* (s7-itemized) unit)
                          (lambda (l) (if (null? l) #u
                                          (let ((b (s7-an-items (extract (car l) value) (extract (car l) span))))
                                            (begin (if (and (pair? b) (pair? (cdr b))) (s7-an-all (cdr (cdr b)) inner) #u)
                                              (steps (cdr l))))))))
                 (steps bs))
               (s7-an-all rest inner))))
          ((string=? name "receive")
           (begin (if (pair? rest) (s7-an-form (extract (car rest) value) (extract (car rest) span) env #f) #u)
             (s7-an-body (if (pair? rest) (cdr rest) nil) (s7-an-append (s7-an-formals (extract (first) value) (extract (first) span)) env) #f)))
          ((string=? name "guard")
           (let* ((spec (s7-an-items (extract (first) value) (extract (first) span)))
                  (var (the s7-binders
                            (if (and (pair? spec) (s7-symbol? (extract (car spec) value)))
                                (list (product (name (s7-sym (extract (car spec) value))) (span (extract (car spec) span))))
                                nil))))
             (begin (if (pair? spec) (s7-an-all (cdr spec) (s7-an-append var env)) #u)
                    (s7-an-body rest env #f))))
          ((or (string=? name "let-syntax") (string=? name "letrec-syntax")) (s7-an-body rest env #f))
          ((string=? name "begin") (s7-an-body args env top))
          ((string=? name "define-library")
           ;; Its `begin`s' forms are its top level.
           (letrec ((decls (->* (s7-itemized) unit)
                      (lambda (l) (if (null? l) #u
                                      (let ((d (s7-an-items (extract (car l) value) (extract (car l) span))))
                                        (begin
                                          (if (and (pair? d) (s7-sym-named? (extract (car d) value) "begin"))
                                              (begin (s7-an-face! (extract (car d) span) 'keyword) (s7-an-body (cdr d) env #t))
                                              #u)
                                          (decls (cdr l))))))))
             (decls rest)))
          (else (s7-an-all args env))))))
  ;; Name `v`, defined at `span`: a definition at top level; else a binder, marked.
  (s7-an-name-def (->* (s7-value s7-span s7-binders bool) unit)
    (lambda (v span env top)
      (cond ((s7-symbol? v) (if top (s7-an-def! (s7-sym v) span) (s7-an-face! span 'function-name)))
            ;; Curried: (define ((name a) b) …).
            ((s7-pair? v) (let ((items (s7-an-items v span)))
                            (s7-an-name-def (extract (car items) value) (extract (car items) span) env top)))
            (else #u))))
  ;; Bindings `((v init) …)`'s initial values, in `env`.
  (s7-an-inits (->* (s7-itemized s7-binders) unit)
    (lambda (bs env)
      (if (null? bs) #u
          (let ((b (s7-an-items (extract (car bs) value) (extract (car bs) span))))
            (begin (if (and (pair? b) (pair? (cdr b))) (s7-an-form (extract (car (cdr b)) value) (extract (car (cdr b)) span) env #f) #u)
              (s7-an-inits (cdr bs) env))))))
  ;; As `let*` sees them: each in the bindings before it.
  (s7-an-inits-sequential (->* (s7-itemized s7-binders) unit)
    (lambda (bs env)
      (if (null? bs) #u
          (let ((b (s7-an-items (extract (car bs) value) (extract (car bs) span))))
            (begin (if (and (pair? b) (pair? (cdr b))) (s7-an-form (extract (car (cdr b)) value) (extract (car (cdr b)) span) env #f) #u)
              (s7-an-inits-sequential (cdr bs) (s7-an-append (s7-an-binding-names (list (car bs))) env)))))))
  (s7-an-binding-names (->* (s7-itemized) s7-binders)
    (lambda (bs)
      (if (null? bs) nil
          (let ((b (s7-an-items (extract (car bs) value) (extract (car bs) span))))
            (if (and (pair? b) (s7-symbol? (extract (car b) value)))
                (cons (product (name (s7-sym (extract (car b) value))) (span (extract (car b) span))) (s7-an-binding-names (cdr bs)))
                (s7-an-binding-names (cdr bs)))))))
  ;; A quasiquoted template: what is unquoted walked.
  (s7-an-qq (->* (s7-value s7-span s7-binders) unit)
    (lambda (x span env)
      (tagcase x
        (pair p (let ((items (s7-an-items x span)))
                  (if (and (pair? items) (or (s7-sym-named? (extract (car items) value) "unquote")
                                             (s7-sym-named? (extract (car items) value) "unquote-splicing")))
                      (s7-an-all (cdr items) env)
                      (letrec ((go (->* (s7-itemized) unit)
                                 (lambda (l) (if (null? l) #u (begin (s7-an-qq (extract (car l) value) (extract (car l) span) env) (go (cdr l)))))))
                        (go items)))))
        (else y #u)))))

"Comments and strings of `s`, by scanning."
(define* s7-lexical-faces (subr spin (string) s7-face-spans)
  (lambda (s)
    (let ((n (string-length s)))
      (letrec ((line-end (subr spin (int) int)
                 (lambda (i) (if (or (>= i n) (char=? (string-ref s i) #\newline)) i (line-end (+ i 1)))))
               (string-end (subr spin (int) int)
                 (lambda (i) (cond ((>= i n) n)
                                   ((char=? (string-ref s i) #\\) (string-end (+ i 2)))
                                   ((char=? (string-ref s i) #\") (+ i 1))
                                   (else (string-end (+ i 1))))))
               (block-end (subr spin (int int) int)
                 (lambda (i depth)
                   (cond ((>= (+ i 1) n) n)
                         ((and (char=? (string-ref s i) #\|) (char=? (string-ref s (+ i 1)) #\#)) (if (= depth 1) (+ i 2) (block-end (+ i 2) (- depth 1))))
                         ((and (char=? (string-ref s i) #\#) (char=? (string-ref s (+ i 1)) #\|)) (block-end (+ i 2) (+ depth 1)))
                         (else (block-end (+ i 1) depth)))))
               (go (subr spin (int s7-face-spans) s7-face-spans)
                 (lambda (i acc)
                   (if (>= i n) (reverse acc)
                       (let ((c (string-ref s i)))
                         (cond ((char=? c #\;) (let ((j (line-end i))) (go j (cons (product (start i) (end j) (face 'comment)) acc))))
                               ((char=? c #\") (let ((j (string-end (+ i 1)))) (go j (cons (product (start i) (end j) (face 'string)) acc))))
                               ((and (char=? c #\#) (< (+ i 1) n) (char=? (string-ref s (+ i 1)) #\|))
                                (let ((j (block-end (+ i 2) 1))) (go j (cons (product (start i) (end j) (face 'comment)) acc))))
                               ;; A character literal: #\; and #\" are no comment, no string.
                               ((and (char=? c #\#) (< (+ i 1) n) (char=? (string-ref s (+ i 1)) #\\)) (go (+ i 3) acc))
                               ;; A symbol between bars: its characters are its own.
                               ((char=? c #\|) (let ((e (string-search s "|" (+ i 1)))) (go (if (< e 0) n (+ e 1)) acc)))
                               (else (go (+ i 1) acc))))))))
        (go 0 nil)))))

"Faces `l` in order of where they start (a merge sort)."
(define* s7-sort-faces (subr spin (s7-face-spans) s7-face-spans)
  (lambda (l)
    (letrec ((merge (subr spin (s7-face-spans s7-face-spans) s7-face-spans)
               (lambda (a b) (cond ((null? a) b) ((null? b) a)
                                   ((<= (extract (car a) start) (extract (car b) start)) (cons (car a) (merge (cdr a) b)))
                                   (else (cons (car b) (merge a (cdr b)))))))
             (split (subr spin (s7-face-spans s7-face-spans s7-face-spans) (productof (a s7-face-spans) (b s7-face-spans)))
               (lambda (l a b) (if (null? l) (product (a a) (b b)) (split (cdr l) b (cons (car l) a))))))
      (if (or (null? l) (null? (cdr l))) l
          (let ((halves (split l nil nil)))
            (merge (s7-sort-faces (extract halves a)) (s7-sort-faces (extract halves b))))))))

"Text `text` (of `file`) analysed."
(define* s7-analyze (subr s7-eff (string string) s7-analysis)
  (lambda (text file)
    (begin
      (set s7-an-faces nil) (set s7-an-defs nil) (set s7-an-refs nil)
      (set s7-item-spans (list (the (eqtable (ref s7-value @sc) s7-span @sc @sc) (make-eqtable (ref-identity)))))
      (letrec ((forms (subr s7-eff (int s7-itemized) (productof (forms s7-itemized) (problem string) (at int)))
                 ;; The data from `i`, and the read's error if any.
                 (lambda (i acc)
                   (tagcase (s7-read-at text i file)
                     (datum d (forms (extract d end)
                                     (cons (product (value (extract d value))
                                                    (span (product (file file) (start (extract d start)) (end (extract d end)))))
                                           acc)))
                     (none u (product (forms (reverse acc)) (problem "") (at -1)))
                     (incomplete u (product (forms (reverse acc)) (problem "a form is not closed") (at i)))
                     (bad b (product (forms (reverse acc)) (problem (extract b message)) (at (extract b at))))))))
        (let ((read (forms 0 nil)))
          (begin
            (s7-an-body (extract read forms) nil #t)
            (set s7-item-spans nil)
            (product (faces (s7-sort-faces (append (s7-lexical-faces text) (get s7-an-faces))))
                     (defs (reverse (get s7-an-defs)))
                     (refs (reverse (get s7-an-refs)))
                     (problem (extract read problem))
                     (problem-at (extract read at)))))))))
