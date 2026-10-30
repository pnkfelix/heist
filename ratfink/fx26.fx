;;; fx26.fx: FX-26 programs, for checking: their text read, and their
;;; top-level forms made the definitions eval.fx compiles, types erased (as
;;; cfa/fx26.fx reads FX-26 for the CFA).
;;;
;;; A program's files: a module file a load-module names (relative to the
;;; file it is in) is read where it is first loaded, its definitions made
;;; global, as FX-26 lets no two of a program's modules define one name.
;;; Fixpt's built-in modules (fx26:…) are FX-26's standard procedures,
;;; given here in Scheme (fx26-prelude), as is ratfink/proof.fx, the
;;; module a harness loads for any-integer, assert and the like.
;;;
;;; A proof is a procedure of no arguments whose name begins proof-: as a
;;; Kani harness is an ordinary function, it type-checks and runs under
;;; Fixpt too (where any-integer is 0 and assert fails the run).
;;;
;;; Top-level forms:
;;;   - (define name [type] e), (define* name type e), (define-rec …):
;;;     definitions of their values;
;;;   - (define-datatype head (ctor type …) …): each constructor a procedure
;;;     making (ctor . ((1 . x) (2 . y) …)), as eval.fx's tagcase takes it;
;;;   - types, effects, module parameters, imports, docstrings: nothing.
;;; Expressions are compiled as written, with FX-26's own forms (eval.fx).

(module-parameters ((m-core (load-moduleof "core.fx")) (m-print (load-moduleof "print.fx" m-core))
                    (m-syntax (load-moduleof "syntax.fx" m-core m-print))
                    (m-numbers (load-moduleof "numbers.fx" m-core))
                    (m-reader (load-moduleof "reader.fx" m-core m-numbers))
                    (m-library (load-moduleof "library.fx" m-core m-print m-syntax m-numbers m-reader))))

(hide (define kit-lists (load-module "../kit/lists.fx"))
      (import kit-lists map map2 for-each filter))
(hide (define kit-strings (load-module "../kit/strings.fx"))
      (import kit-strings string-prefix? string-suffix?))

(define fx-error (subr rf-eff (string rf-value) void) (lambda (m f) (rf-error (string-append "ratfink: " m) (list f))))
(define head-sym (subr rf-st (rf-value) symbol)
  (lambda (f) (if (and (rf-pair? f) (rf-symbol? (rf-car f))) (rf-sym-of (rf-car f)) '||)))

"The files a form's load-modules name (not inside quotes)."
(define loaded-files (subr rf-st (rf-value) strings)
  (lambda (x)
    (cond ((not (rf-pair? x)) nil)
          ((rf-eqv? (rf-car x) (q 'quote)) nil)
          ((and (rf-eqv? (rf-car x) (q 'load-module)) (rf-pair? (rf-cdr x)) (rf-string? (rf-cadr x))) (list (rf-str-of (rf-cadr x))))
          (else (append (loaded-files (rf-car x)) (loaded-files (rf-cdr x)))))))

"Files ratfink has its own of: Fixpt's built-in modules, and its proof
module."
(define built-in-file? (subr rf-st (string) bool)
  (lambda (f) (or (string-prefix? "fx26:" f) (string-suffix? "ratfink/proof.fx" f) (string=? f "proof.fx"))))

"A file's forms, read once (the survey reads them first)."
(define-type read-file (productof (path string) (forms rf-vals)))
(define files-read (ref (listof read-file acyclic) @rf) (new nil))
(define fx26-read (subr rf-eff (string) rf-vals)
  (lambda (file)
    (letrec ((find (subr rf-eff ((listof read-file acyclic)) rf-vals)
               (lambda (l)
                 (cond ((null? l)
                        (begin (set-fx26-syntax! #t)
                               (let ((forms (read-file-data file #f)))
                                 (begin (set-fx26-syntax! #f)
                                        (set files-read (cons (product (path file) (forms forms)) (get files-read)))
                                        forms))))
                       ((string=? (extract (car l) path) file) (extract (car l) forms))
                       (else (find (cdr l)))))))
      (find (get files-read)))))

(define ignored-heads symbols
  (list 'module-parameters 'define-type 'define-effect 'define-generative 'define-syscall 'define-optional-syscall
        'import 'include))

"A datatype's constructors, as definitions."
(define datatype-defines (subr rf-eff (rf-value) rf-vals)
  (lambda (form)
    (map (lambda ((v rf-value))
           (let* ((ctor (rf-car v))
                  (n (rf-length (rf-cdr v)))
                  (args (letrec ((mk (subr rf-st (int) rf-vals)
                                   (lambda (i) (if (> i n) nil (cons (rf-sym (string->symbol (string-append " field" (int->string i)))) (mk (+ i 1)))))))
                          (mk 1))))
             (rf-list (list (q 'define) (rf-cons ctor (rf-list args))
                            (rf-list (list (q 'cons) (rf-list (list (q 'quote) ctor))
                                           (rf-cons (q 'list)
                                                    (rf-list (letrec ((fields (subr rf-st (rf-vals int) rf-vals)
                                                                        (lambda (as i) (if (null? as) nil
                                                                                           (cons (rf-list (list (q 'cons) (rf-int i) (car as))) (fields (cdr as) (+ i 1)))))))
                                                               (fields args 1))))))))))
         (rf-elements (rf-cddr form)))))

"The value of a definition: its last part."
(define definition-value (subr rf-st (rf-value) rf-value)
  (lambda (form) (rf-car (rf-reverse (rf-cdr form)))))
(define strip-the (subr rf-st (rf-value) rf-value)
  (lambda (e) (if (and (rf-pair? e) (rf-eqv? (rf-car e) (q 'the)) (= (rf-length e) 3)) (strip-the (rf-caddr e)) e)))

"A definition's forms for eval.fx: a proof, or (define name e); a procedure
with a specification as a contract, and a proof of it; a harness, and a
proof of it."
(define definition (subr rf-eff (rf-value rf-value rf-value) rf-vals)
  (lambda (name type e0)
    (let* ((e (rewrite-local-specs e0)) (v (strip-the e)))
      (if (and (rf-symbol? name) (string-prefix? "proof-" (symbol->string (rf-sym-of name)))
               (rf-pair? v) (rf-eqv? (rf-car v) (q 'lambda)) (rf-null? (rf-cadr v)))
          (list (rf-cons (q 'define-proof) (rf-cons (rf-list1 name) (rf-cddr v))))
          (tagcase (spec-of type)
            (none u (list (rf-list (list (q 'define) name e))))
            (some sp0
              (let ((sp (with-formal-names sp0 v)))
              (cond ((specified? sp) (vals-append (contract-forms name sp e) (proof-forms name sp #t)))
                    ((harness? sp v) (cons (rf-list (list (q 'define) name e)) (proof-forms name sp #f)))
                    (else (list (rf-list (list (q 'define) name e))))))))))))

"A specification whose unnamed parameters take the names of its lambda's."
(define with-formal-names (subr rf-st (spec rf-value) spec)
  (lambda (sp v)
    (if (and (rf-pair? v) (rf-eqv? (rf-car v) (q 'lambda)) (rf-list? (rf-cadr v)) (= (rf-length (rf-cadr v)) (list-length (extract sp params))))
        (let* ((renames (filter (lambda ((r param)) (string-prefix? " arg" (symbol->string (rf-sym-of (extract r name)))))
                                (map2 (lambda ((p param) (f rf-value)) (product (name (extract p name)) (type (if (rf-pair? f) (rf-car f) f))))
                                      (extract sp params) (rf-elements (rf-cadr v)))))
               (rename (lambda ((x rf-value)) (subst-type renames x))))
          (product (params (map (lambda ((p param)) (product (name (rename (extract p name))) (type (extract p type)))) (extract sp params)))
                   (result (extract sp result)) (requires (map rename (extract sp requires)))
                   (result-name (extract sp result-name)) (ensures (map rename (extract sp ensures)))))
        sp)))

;;; ------------------------------------------------------------ specifications
;;;
;;; A procedure's type may say what it requires and ensures (Fixpt's
;;; docs/fx26.md, Specifications): (subr E ((x : int) …) T (requires p …)
;;; (ensures r q …)), or with ->. Such a procedure is shakedown's contract:
;;; its requires the preconditions (with (<= 0 x) for a nat parameter x),
;;; its ensures the postconditions (with (<= 0 r) for a nat result), and a
;;; result of type (bool (then P …) (else Q …)) says what its test proves.
;;; Its returns shape is its result type's, so that a call inside its own
;;; proof is a stub: the proof is modular, as Fixpt's verifier's, which
;;; knows a call by its ensures. Its proof calls it on symbolic values of
;;; its parameters' types.
;;;
;;; A harness is a procedure of unit result that asserts (Fixpt's `fixpt
;;; test` runs one on drawn inputs): its proof calls it on symbolic values.
;;;
;;; Values of a type: int, nat, bool, and lists of them of up to
;;; list-bound elements (a type's name, define-type's, read through).

(define-type param (productof (name rf-value) (type rf-value)))
(define-type spec (productof (params (listof param acyclic)) (result rf-value)
                             (requires rf-vals) (result-name rf-value) (ensures rf-vals)))
(define specified? (subr rf-st (spec) bool)
  (lambda (sp) (or (pair? (extract sp requires)) (pair? (extract sp ensures)))))

"Type abbreviations of the program (define-type name type)."
(define type-names (ref (listof param acyclic) @rf) (new nil))
(define expand-type (subr rf-st (rf-value) rf-value)
  (lambda (t)
    (if (rf-symbol? t)
        (letrec ((find (subr rf-st ((listof param acyclic)) rf-value)
                   (lambda (l) (cond ((null? l) t) ((rf-eqv? (extract (car l) name) t) (expand-type (extract (car l) type))) (else (find (cdr l)))))))
          (find (get type-names)))
        t)))

(define list-bound int 4)
"Lists a stub may return: up to this many elements."
(define result-list-bound int 8)

"A procedure type's parameters, result and clauses, if it is one."
(define spec-of (subr rf-eff (rf-value) (sumof (none unit) (some spec)))
  (lambda (type0)
    (let ((type (let ((t (expand-type type0))) (if (and (rf-pair? t) (rf-eqv? (rf-car t) (q 'poly))) (rf-caddr t) t))))
      (if (not (rf-pair? type)) (sum none #u)
          (let* ((h (rf-car type))
                 (rest (cond ((rf-eqv? h (q 'subr)) (let ((r (rf-cddr type))) (if (and (rf-pair? (rf-cadr type)) (rf-eqv? (rf-car (rf-cadr type)) (q 'conv))) (rf-cdr r) r)))
                             ((or (rf-eqv? h (q '->)) (rf-eqv? h (q '->*))) (rf-cdr type))
                             (else rf-false))))
            (if (rf-false? rest) (sum none #u)
                (let* ((ps (rf-car rest)) (result (rf-cadr rest)) (clauses (rf-elements (rf-cddr rest)))
                       (count (the (ref int @rf) (new 0)))
                       (params (map (lambda ((p rf-value))
                                      (begin
                                        (set count (+ 1 (get count)))
                                        (if (and (rf-pair? p) (= (rf-length p) 3) (rf-eqv? (rf-cadr p) (q ':)))
                                            (product (name (rf-car p)) (type (rf-caddr p)))
                                            (product (name (rf-sym (string->symbol (string-append " arg" (int->string (get count)))))) (type p)))))
                                    (rf-elements ps)))
                       (requires (fx-append-all (map (lambda ((c rf-value)) (if (rf-eqv? (rf-car c) (q 'requires)) (rf-elements (rf-cdr c)) nil)) clauses)))
                       (ens (filter (lambda ((c rf-value)) (rf-eqv? (rf-car c) (q 'ensures))) clauses))
                       (r (if (pair? ens) (rf-cadr (car ens)) (q 'result)))
                       ;; Each ensures's propositions, about the result named r.
                       (ensures (fx-append-all (map (lambda ((c rf-value)) (rename-result (rf-elements (rf-cddr c)) (rf-cadr c) r)) ens)))
                       ;; (bool (then P …) (else Q …)): what a test proves.
                       ;; Its propositions name the parameters by position: 0, 1, ….
                       (positional (lambda ((x rf-value)) (by-position x params)))
                       (latent (if (and (rf-pair? result) (rf-eqv? (rf-car result) (q 'bool)))
                                   (fx-append-all (map (lambda ((c rf-value))
                                                         (cond ((rf-eqv? (rf-car c) (q 'then)) (the rf-vals (list (F3 (q 'implies) r (rf-cons (q 'and) (positional (rf-cdr c)))))))
                                                               ((rf-eqv? (rf-car c) (q 'else)) (the rf-vals (list (F3 (q 'implies) (F2 (q 'not) r) (rf-cons (q 'and) (positional (rf-cdr c)))))))
                                                               (else (the rf-vals nil))))
                                                       (rf-elements (rf-cdr result))))
                                   nil)))
                  (sum some (product (params params) (result (if (pair? latent) (q 'bool) result))
                                     (requires (vals-append (nat-conditions params) requires))
                                     (result-name r)
                                     (ensures (vals-append (vals-append latent ensures) (if (nat-type? result) (the rf-vals (list (F3 (q '<=) (rf-int 0) r))) (the rf-vals nil)))))))))))))
(define F2 (subr rf-st (rf-value rf-value) rf-value) (lambda (a b) (rf-list2 a b)))
(define F3 (subr rf-st (rf-value rf-value rf-value) rf-value) (lambda (a b c) (rf-list3 a b c)))
"x with each integer k in it the kth parameter's name."
(define by-position (subr rf-st (rf-value (listof param acyclic)) rf-value)
  (lambda (x ps)
    (cond ((rf-exact-integer? x) (let ((k (rf-int-of x))) (if (and (>= k 0) (< k (list-length ps))) (extract (nth-param ps k) name) x)))
          ((rf-pair? x) (rf-cons (by-position (rf-car x) ps) (by-position (rf-cdr x) ps)))
          (else x))))
(define nth-param (subr rf-st ((listof param acyclic) int) param)
  (lambda (ps k) (if (= k 0) (car ps) (nth-param (cdr ps) (- k 1)))))

"A second ensures may name its result otherwise: its propositions with
that name made r."
(define rename-result (subr rf-st (rf-vals rf-value rf-value) rf-vals)
  (lambda (ps from to)
    (if (rf-eqv? from to) ps
        (map (lambda ((p rf-value)) (rf-list (list (q 'let) (rf-list1 (F2 from to)) p))) ps))))
(define nat-type? (subr rf-st (rf-value) bool) (lambda (t) (rf-eqv? (expand-type t) (q 'nat))))
(define nat-conditions (subr rf-st ((listof param acyclic)) rf-vals)
  (lambda (ps) (fx-append-all (map (lambda ((p param)) (if (nat-type? (extract p type)) (the rf-vals (list (F3 (q '<=) (rf-int 0) (extract p name)))) (the rf-vals nil))) ps))))

"How many times a value's type may unfold a named type (a datatype's, a
define-type's, mu's, dletrec's): the depth of recursive values."
(define type-fuel int 3)

"A type's definition, if the program gives one: a family's (define-type
(name (p kind) …) type) is (fx26-family (p …) type)."
(define type-definition (subr rf-st (rf-value) rf-value)
  (lambda (n)
    (letrec ((find (subr rf-st ((listof param acyclic)) rf-value)
               (lambda (l) (cond ((null? l) rf-false) ((rf-eqv? (extract (car l) name) n) (extract (car l) type)) (else (find (cdr l)))))))
      (find (get type-names)))))
(define family? (subr rf-st (rf-value) bool) (lambda (d) (and (rf-pair? d) (rf-eqv? (rf-car d) (q 'fx26-family)))))

"t with each name of s its type there."
(define subst-type (subr rf-st ((listof param acyclic) rf-value) rf-value)
  (lambda (s t)
    (cond ((rf-symbol? t)
           (letrec ((find (subr rf-st ((listof param acyclic)) rf-value)
                      (lambda (l) (cond ((null? l) t) ((rf-eqv? (extract (car l) name) t) (extract (car l) type)) (else (find (cdr l)))))))
             (find s)))
          ((rf-pair? t) (rf-cons (subst-type s (rf-car t)) (subst-type s (rf-cdr t))))
          (else t))))
(define bind-types (subr rf-st (rf-vals rf-vals) (listof param acyclic))
  (lambda (ns ts) (if (or (null? ns) (null? ts)) nil (cons (product (name (car ns)) (type (car ts))) (bind-types (cdr ns) (cdr ts))))))

"A named type unfolded once (a type's name, a family applied, mu,
dletrec); or #f."
(define unfold-type (subr rf-st (rf-value) rf-value)
  (lambda (t)
    (cond ((rf-symbol? t) (let ((d (type-definition t))) (if (family? d) rf-false d)))
          ((not (rf-pair? t)) rf-false)
          ((and (rf-eqv? (rf-car t) (q 'mu)) (= (rf-length t) 3))
           (subst-type (list (product (name (rf-cadr t)) (type t))) (rf-caddr t)))
          ((and (rf-eqv? (rf-car t) (q 'dletrec)) (= (rf-length t) 3))
           (let* ((bs (rf-elements (rf-cadr t)))
                  (s (map (lambda ((b rf-value)) (product (name (rf-car b)) (type (F3 (q 'dletrec) (rf-cadr t) (rf-car b))))) bs))
                  (body (rf-caddr t))
                  (own (filter (lambda ((b rf-value)) (rf-eqv? (rf-car b) body)) bs)))
             (subst-type s (if (pair? own) (rf-cadr (car own)) body))))
          ((rf-symbol? (rf-car t))
           (let ((d (type-definition (rf-car t))))
             (if (and (family? d) (= (rf-length (rf-cadr d)) (rf-length (rf-cdr t))))
                 (subst-type (bind-types (rf-elements (rf-cadr d)) (rf-elements (rf-cdr t))) (rf-caddr d))
                 rf-false)))
          (else rf-false))))

(define type-head? (subr rf-st (rf-value symbol) bool)
  (lambda (t h) (and (rf-pair? t) (rf-eqv? (rf-car t) (rf-sym h)))))
"The integer types of fixed width: their least and greatest values."
(define int-range (subr rf-st (rf-value) (sumof (none unit) (some (productof (lo int) (hi int)))))
  (lambda (t)
    (cond ((rf-eqv? t (q 'i32)) (sum some (product (lo (- 0 2147483648)) (hi 2147483647))))
          ((rf-eqv? t (q 'u32)) (sum some (product (lo 0) (hi 4294967295))))
          ((rf-eqv? t (q 'i64)) (sum some (product (lo (- 0 9223372036854775807)) (hi 9223372036854775807))))
          ((rf-eqv? t (q 'u64)) (sum some (product (lo 0) (hi 9223372036854775807))))
          (else (sum none #u)))))
"Types of values FX-26 has no symbolic sort for: their values are those
the program writes (its literals, domain), and a few more."
(define domain-kind (subr rf-st (rf-value) symbol)
  (lambda (t)
    (cond ((rf-eqv? t (q 'char)) 'char) ((rf-eqv? t (q 'string)) 'string) ((rf-eqv? t (q 'symbol)) 'symbol)
          ((or (rf-eqv? t (q 'f64)) (rf-eqv? t (q 'f32))) 'real)
          (else '||))))
(define unit-type? (subr rf-st (rf-value) bool)
  (lambda (t) (or (rf-eqv? t (q 'unit)) (type-head? t 'proves))))
"A product's label: as written (a datatype's are 1, 2, …)."
(define product-fields (subr rf-st (rf-value) rf-vals) (lambda (t) (rf-elements (rf-cdr t))))

"The shape of a type's values (for a stub's result), or #f: a product
an alist of its labels, a sum (label . value)."
(define type-shape (subr rf-st (rf-value int) rf-value)
  (lambda (t bound) (shape-of-type t bound type-fuel)))
(define shape-of-type (subr rf-st (rf-value int int) rf-value)
  (lambda (t bound fuel)
    (let ((part (lambda ((x rf-value)) (shape-of-type x bound fuel))))
      (cond ((or (rf-eqv? t (q 'int)) (rf-eqv? t (q 'nat)) (type-head? t 'nat)) (q 'integer))
            ((tagcase (int-range t) (some r #t) (none u #f)) (q 'integer))
            ((rf-eqv? t (q 'bool)) (q 'boolean))
            ((unit-type? t) (F2 (q 'one-of) rf-unspecified))
            ((not (eq? (domain-kind t) '||)) (rf-cons (q 'one-of) (rf-list (domain (domain-kind t)))))
            ((type-head? t 'listof)
             (let ((e (part (rf-cadr t)))) (if (rf-false? e) rf-false (F3 (q 'list-of) (rf-int bound) e))))
            ((and (type-head? t 'nlist) (rf-exact-integer? (rf-caddr t)))
             (let ((e (part (rf-cadr t))))
               (if (rf-false? e) rf-false
                   (letrec ((spine (subr rf-st (int) rf-value) (lambda (k) (if (<= k 0) (F2 (q 'one-of) rf-nil) (F3 (q 'pair) e (spine (- k 1)))))))
                     (spine (rf-int-of (rf-caddr t)))))))
            ((type-head? t 'pairof)
             (let ((a (part (rf-cadr t))) (d (part (rf-caddr t)))) (if (or (rf-false? a) (rf-false? d)) rf-false (F3 (q 'pair) a d))))
            ((type-head? t 'productof)
             (letrec ((fields (subr rf-st (rf-vals) rf-value)
                        (lambda (fs)
                          (if (null? fs) (F2 (q 'one-of) rf-nil)
                              (let ((s (part (rf-cadr (car fs)))) (rest (fields (cdr fs))))
                                (if (or (rf-false? s) (rf-false? rest)) rf-false
                                    (F3 (q 'pair) (F3 (q 'pair) (F2 (q 'one-of) (rf-car (car fs))) s) rest)))))))
               (fields (product-fields t))))
            ((type-head? t 'sumof)
             (let ((arms (filter (lambda ((x rf-value)) (not (rf-false? x)))
                                 (map (lambda ((v rf-value))
                                        (let ((s (part (rf-cadr v)))) (if (rf-false? s) rf-false (F3 (q 'pair) (F2 (q 'one-of) (rf-car v)) s))))
                                      (product-fields t)))))
               (cond ((null? arms) rf-false) ((null? (cdr arms)) (car arms)) (else (rf-cons (q 'or) (rf-list arms))))))
            (else (let ((u (if (> fuel 0) (unfold-type t) rf-false)))
                    (if (rf-false? u) rf-false (shape-of-type u bound (- fuel 1)))))))))

"An expression making a symbolic value of a type, or #f."
(define type-value (subr rf-st (rf-value) rf-value)
  (lambda (t) (value-of-type t type-fuel)))
(define value-of-type (subr rf-st (rf-value int) rf-value)
  (lambda (t fuel)
    (let ((part (lambda ((x rf-value)) (value-of-type x fuel))))
      (cond ((rf-eqv? t (q 'int)) (rf-list1 (q 'any-integer)))
            ;; (nat k): the size k.
            ((and (type-head? t 'nat) (rf-exact-integer? (rf-cadr t))) (rf-cadr t))
            ((rf-eqv? t (q 'nat)) (rf-list1 (q 'fx26-any-nat)))
            ((rf-eqv? t (q 'bool)) (rf-list1 (q 'any-boolean)))
            ((tagcase (int-range t) (some r #t) (none u #f))
             (tagcase (int-range t)
               (some r (F3 (q 'fx26-any-range) (rf-int (extract r lo)) (rf-int (extract r hi))))
               (none u rf-false)))
            ((unit-type? t) (rf-list (list (q 'if) rf-false rf-false)))
            ((not (eq? (domain-kind t) '||))
             (F2 (q 'arbitrary) (F2 (q 'quote) (rf-cons (q 'one-of) (rf-list (domain (domain-kind t)))))))
            ((type-head? t 'listof)
             (let ((e (part (rf-cadr t))))
               (if (rf-false? e) rf-false (F3 (q 'any-list) (rf-int list-bound) (rf-list (list (q 'lambda) rf-nil e))))))
            ((and (type-head? t 'nlist) (rf-exact-integer? (rf-caddr t)))
             (let ((e (part (rf-cadr t))))
               (if (rf-false? e) rf-false
                   (rf-cons (q 'list) (rf-list (letrec ((copies (subr rf-st (int) rf-vals) (lambda (k) (if (<= k 0) nil (cons e (copies (- k 1)))))))
                                                 (copies (rf-int-of (rf-caddr t)))))))))
            ((type-head? t 'pairof)
             (let ((a (part (rf-cadr t))) (d (part (rf-caddr t)))) (if (or (rf-false? a) (rf-false? d)) rf-false (F3 (q 'cons) a d))))
            ((type-head? t 'arrayof)
             (let ((e (part (F3 (q 'listof) (rf-cadr t) (rf-caddr t))))) (if (rf-false? e) rf-false (F2 (q 'list->vector) e))))
            ((type-head? t 'ref)
             (let ((e (part (rf-cadr t)))) (if (rf-false? e) rf-false (F2 (q 'vector) e))))
            ((type-head? t 'productof)
             (let ((vs (map (lambda ((f rf-value)) (part (rf-cadr f))) (product-fields t))))
               (if (memq-val? rf-false vs) rf-false
                   (rf-cons (q 'list) (rf-list (map2 (lambda ((f rf-value) (v rf-value)) (F3 (q 'cons) (F2 (q 'quote) (rf-car f)) v)) (product-fields t) vs))))))
            ;; A sum: one of its labels' values.
            ((type-head? t 'sumof)
             (let ((arms (filter (lambda ((x rf-value)) (not (rf-false? x)))
                                 (map (lambda ((v rf-value))
                                        (let ((e (part (rf-cadr v)))) (if (rf-false? e) rf-false (F3 (q 'cons) (F2 (q 'quote) (rf-car v)) e))))
                                      (product-fields t)))))
               (cond ((null? arms) rf-false) ((null? (cdr arms)) (car arms)) (else (rf-cons (q 'any-of) (rf-list arms))))))
            (else
             (let ((u (if (> fuel 0) (unfold-type t) rf-false)))
               (cond ((not (rf-false? u)) (value-of-type u (- fuel 1)))
                     ;; A type variable: the procedure cannot look at its value.
                     ((and (rf-symbol? t) (type-variable? t) (rf-false? (type-definition t))) (F2 (q 'quote) (q 'opaque)))
                     (else rf-false))))))))

"A name that is no type FX-26 has, nor the program: a type variable."
(define type-variable? (subr rf-st (rf-value) bool)
  (lambda (t)
    (not (symbols-member? (rf-sym-of t) (list 'int 'nat 'bool 'char 'string 'unit 'symbol 'datum 'i32 'u32 'i64 'u64 'f64 'f32 'void
                                              'tword 'wcell 'wglobal)))))

;;; ------------------------------------------------------------ inputs written
;;;
;;; A proof's inputs, as a report shows them in a model: FX-26's
;;; expressions of their types, (product (x 1) (y 2)), (sum some 3),
;;; (node (leaf) 0 (leaf)), (list 1 2), "yes", #\a, 'red.

(define datatype-names (ref rf-vals @rf) (new nil))
(define datatype? (subr rf-st (rf-value) bool)
  (lambda (t) (memq-val? (if (rf-pair? t) (rf-car t) t) (get datatype-names))))
(define render-input (subr rf-eff (rf-value rf-value) string)
  (lambda (v t) (render-typed v t 32)))
(define words (subr rf-st (strings) string)
  (lambda (ws) (if (null? ws) "" (if (null? (cdr ws)) (car ws) (string-append (car ws) " " (words (cdr ws)))))))
(define render-typed (subr rf-eff (rf-value rf-value int) string)
  (lambda (v t fuel)
    (let ((elements (lambda ((e rf-value) (vs rf-vals))
                      (if (null? vs) "nil" (string-append "(list " (words (map (lambda ((x rf-value)) (render-typed x e fuel)) vs)) ")")))))
      (cond ((rf-boolean? v) (if (rf-true? v) "#t" "#f"))
            ((unit-type? t) "#u")
            ((and (rf-symbol? v) (eq? (domain-kind t) 'symbol)) (string-append "'" (datum->string v)))
            ((and (type-head? t 'listof) (rf-list? v)) (elements (rf-cadr t) (rf-elements v)))
            ((and (type-head? t 'nlist) (rf-list? v)) (elements (rf-cadr t) (rf-elements v)))
            ((and (type-head? t 'arrayof) (rf-vector? v)) (string-append "(list->array " (elements (rf-cadr t) (slots-list (rf-slots-of v))) ")"))
            ((and (type-head? t 'ref) (rf-vector? v) (= (array-length (rf-slots-of v)) 1))
             (string-append "(new " (render-typed (array-ref (rf-slots-of v) 0) (rf-cadr t) fuel) ")"))
            ((and (type-head? t 'pairof) (rf-pair? v))
             (string-append "(cons " (render-typed (rf-car v) (rf-cadr t) fuel) " " (render-typed (rf-cdr v) (rf-caddr t) fuel) ")"))
            ((and (type-head? t 'productof) (rf-list? v))
             (string-append "(product " (words (map (lambda ((f rf-value)) (string-append "(" (datum->string (rf-car f)) " " (render-typed (field-value v (rf-car f)) (rf-cadr f) fuel) ")"))
                                                    (product-fields t)))
                            ")"))
            ((and (type-head? t 'sumof) (rf-pair? v))
             (let ((arm (filter (lambda ((a rf-value)) (rf-eqv? (rf-car a) (rf-car v))) (product-fields t))))
               (if (null? arm) (datum->string v)
                   (string-append "(sum " (datum->string (rf-car v)) " " (render-typed (rf-cdr v) (rf-cadr (car arm)) fuel) ")"))))
            ;; A datatype's value: its constructor applied.
            ((and (datatype? t) (rf-pair? v) (> fuel 0))
             (let* ((u (unfold-type t))
                    (arm (if (type-head? u 'sumof) (filter (lambda ((a rf-value)) (rf-eqv? (rf-car a) (rf-car v))) (product-fields u)) nil)))
               (if (null? arm) (datum->string v)
                   (string-append "(" (words (cons (datum->string (rf-car v))
                                                   (map (lambda ((f rf-value)) (render-typed (field-value (rf-cdr v) (rf-car f)) (rf-cadr f) (- fuel 1)))
                                                        (product-fields (rf-cadr (car arm))))))
                                  ")"))))
            ((> fuel 0)
             (let ((u (unfold-type t))) (if (rf-false? u) (datum->string v) (render-typed v u (- fuel 1)))))
            (else (datum->string v))))))
"An alist's value for a label, or unspecified."
(define field-value (subr rf-st (rf-value rf-value) rf-value)
  (lambda (alist label)
    (cond ((not (rf-pair? alist)) rf-unspecified)
          ((and (rf-pair? (rf-car alist)) (rf-eqv? (rf-caar alist) label)) (rf-cdar alist))
          (else (field-value (rf-cdr alist) label)))))

;;; ------------------------------------------------------------ domains
;;;
;;; Characters, strings, symbols and flonums have no sort in the solver: a
;;; value of their type is one of those the program writes (its literals,
;;; up to domain-limit of each, and in a quote its symbols) or of a few
;;; more, which the program does not write ("", "a", #\a, a symbol of its
;;; own, 0.0, 1.0, -0.5). A proof over them is exhaustive only over these.

(define domain-limit int 6)
(define-type domains (productof (char rf-vals) (string rf-vals) (symbol rf-vals) (real rf-vals)))
(define program-literals (ref domains @rf) (new (product (char nil) (string nil) (symbol nil) (real nil))))
(define literal-same? (subr rf-st (rf-value rf-value) bool)
  (lambda (a b) (if (and (rf-string? a) (rf-string? b)) (string=? (rf-str-of a) (rf-str-of b)) (rf-eqv? a b))))
(define literal-in? (subr rf-st (rf-value rf-vals) bool)
  (lambda (x l) (cond ((null? l) #f) ((literal-same? x (car l)) #t) (else (literal-in? x (cdr l))))))
(define add-literal (subr rf-st (rf-value rf-vals) rf-vals)
  (lambda (x l) (if (or (literal-in? x l) (>= (list-length l) domain-limit)) l (vals-append l (list x)))))
(define real-value? (subr rf-st (rf-value) bool) (lambda (v) (tagcase v (real r #t) (else x #f))))
(define note-literal! (subr rf-st (rf-value) unit)
  (lambda (x)
    (let ((d (get program-literals)))
      (cond ((rf-char? x) (set program-literals (product (char (add-literal x (extract d char))) (string (extract d string)) (symbol (extract d symbol)) (real (extract d real)))))
            ((rf-string? x) (set program-literals (product (char (extract d char)) (string (add-literal x (extract d string))) (symbol (extract d symbol)) (real (extract d real)))))
            ((rf-symbol? x) (set program-literals (product (char (extract d char)) (string (extract d string)) (symbol (add-literal x (extract d symbol))) (real (extract d real)))))
            ((real-value? x) (set program-literals (product (char (extract d char)) (string (extract d string)) (symbol (extract d symbol)) (real (add-literal x (extract d real))))))
            (else #u)))))
"The literals of an expression: its characters, strings and flonums, and
the symbols it quotes."
(define note-literals! (subr rf-st (rf-value bool) unit)
  (lambda (x quoted?)
    (cond ((rf-pair? x)
           (cond ((and (not quoted?) (rf-eqv? (rf-car x) (q 'quote)) (rf-pair? (rf-cdr x))) (note-literals! (rf-cadr x) #t))
                 ((and (not quoted?) (memq-val? (rf-car x) (list (q 'load-module) (q 'the)))) #u)
                 (else (begin (note-literals! (rf-car x) quoted?) (note-literals! (rf-cdr x) quoted?)))))
          ((rf-symbol? x) (if quoted? (note-literal! x) #u))
          ((rf-null? x) #u)
          (else (note-literal! x)))))
"The literals of a file's definitions."
(define note-program-literals! (subr rf-st (rf-vals) unit)
  (lambda (forms)
    (for-each (lambda ((f rf-value))
                (let ((h (head-sym f)))
                  (cond ((or (eq? h 'define) (eq? h 'define*)) (if (pair? (loaded-files f)) #u (note-literals! (definition-value f) #f)))
                        ((eq? h 'define-rec) (for-each (lambda ((b rf-value)) (note-literals! (rf-caddr b) #f)) (rf-elements (rf-cdr f))))
                        (else #u))))
              (filter rf-pair? forms))))
(define add-extra (subr rf-st (rf-value rf-vals) rf-vals)
  (lambda (x l) (if (literal-in? x l) l (vals-append l (list x)))))
(define domain (subr rf-st (symbol) rf-vals)
  (lambda (kind)
    (let ((d (get program-literals)))
      (cond ((eq? kind 'char) (add-extra (sum char #\a) (extract d char)))
            ((eq? kind 'string) (add-extra (rf-str "a") (add-extra (rf-str "") (extract d string))))
            ((eq? kind 'symbol) (add-extra (q 'ratfink-other) (extract d symbol)))
            (else (add-extra (sum real -0.5) (add-extra (sum real 1.0) (add-extra (sum real 0.0) (extract d real)))))))))

"A local procedure with a specification ((letrec ((name type lambda)) …)):
callers see a stub, which asserts what it requires and gives a value of
its result's type assumed to meet what it ensures; its body is verified
once, where the letrec is, on values of its parameters' types meeting
what it requires, its own calls the stub's (so the verification is
modular, as the stub of a top-level contract makes it). The verification
is under a fresh boolean, so that a path it ends does not end the
caller's."
(define rewrite-local-specs (subr rf-eff (rf-value) rf-value)
  (lambda (x)
    (cond ((not (rf-pair? x)) x)
          ((rf-eqv? (rf-car x) (q 'quote)) x)
          ((and (rf-eqv? (rf-car x) (q 'letrec)) (rf-pair? (rf-cdr x)) (rf-list? (rf-cadr x)))
           (let* ((bindings (rf-elements (rf-cadr x)))
                  (body (rewrite-local-specs (rf-cddr x)))
                  (checks (the (ref rf-vals @rf) (new nil)))
                  (new-bindings (map (lambda ((b rf-value)) (local-spec-binding b checks)) bindings)))
             (rf-cons (q 'letrec) (rf-cons (rf-list new-bindings) (rf-append2 (rf-list (reverse (get checks))) body)))))
          (else (rf-cons (rewrite-local-specs (rf-car x)) (rewrite-local-specs (rf-cdr x)))))))

"A letrec binding, its stub if it has a specification (whose verification
is added to checks)."
(define local-spec-binding (subr rf-eff (rf-value (ref rf-vals @rf)) rf-value)
  (lambda (b checks)
    (if (not (= (rf-length b) 3)) (rewrite-local-specs b)
        (let ((name (rf-car b)) (type (rf-cadr b)) (lam (rewrite-local-specs (rf-caddr b))))
          (tagcase (spec-of type)
            (none u (F3 name type lam))
            (some sp
              (let* ((ps (extract sp params))
                     (values (map (lambda ((p param)) (type-value (extract p type))) ps))
                     (result (type-value (extract sp result))))
                (if (or (not (specified? sp)) (memq-val? rf-false values) (rf-false? result))
                    (F3 name type lam)
                    (begin
                      (set checks (cons (local-verification name sp lam values) (get checks)))
                      (F3 name type (local-stub name sp result)))))))))))

(define spec-label (subr rf-eff (rf-value string rf-value) rf-value)
  (lambda (name what e) (rf-str (string-append what " of " (symbol->string (rf-sym-of name)) ": " (datum->string e)))))

"(if (any-boolean) (let* ((x v) …) (assume req) … (let ((r (lam x …))) (assert ens label) …)) #u)"
(define local-verification (subr rf-eff (rf-value spec rf-value rf-vals) rf-value)
  (lambda (name sp lam values)
    (let* ((names (map (lambda ((p param)) (extract p name)) (extract sp params)))
           (r (extract sp result-name))
           (assumes (map (lambda ((e rf-value)) (F2 (q 'assume) e)) (extract sp requires)))
           (asserts (map (lambda ((e rf-value)) (F3 (q 'assert) e (spec-label name "postcondition" e))) (extract sp ensures)))
           (call (rf-cons lam (rf-list names)))
           (check (rf-list (list (q 'let) (rf-list1 (F2 r call)) (rf-cons (q 'begin) (rf-list (vals-append asserts (list rf-unspecified))))))))
      (rf-list (list (q 'if) (rf-list1 (q 'any-boolean))
                     (rf-list (list (q 'let*) (rf-list (map2 (lambda ((n rf-value) (v rf-value)) (F2 n v)) names values))
                                    (rf-cons (q 'begin) (rf-list (vals-append assumes (list check))))))
                     rf-unspecified)))))

"(lambda (x …) (assert req label) … (let ((r v)) (assume ens) … r))"
(define local-stub (subr rf-eff (rf-value spec rf-value) rf-value)
  (lambda (name sp result)
    (let* ((names (map (lambda ((p param)) (extract p name)) (extract sp params)))
           (r (extract sp result-name))
           (asserts (map (lambda ((e rf-value)) (F3 (q 'assert) e (spec-label name "precondition" e))) (extract sp requires)))
           (assumes (map (lambda ((e rf-value)) (F2 (q 'assume) e)) (extract sp ensures)))
           (give (rf-list (list (q 'let) (rf-list1 (F2 r result)) (rf-cons (q 'begin) (rf-list (vals-append assumes (list r))))))))
      (rf-list (list (q 'lambda) (rf-list names) (rf-cons (q 'begin) (rf-list (vals-append asserts (list give)))))))))

"A harness: of unit result, its body asserting."
(define harness? (subr rf-st (spec rf-value) bool)
  (lambda (sp v)
    (and (rf-eqv? (expand-type (extract sp result)) (q 'unit))
         (rf-pair? v) (rf-eqv? (rf-car v) (q 'lambda)) (mentions? (q 'assert) v))))
(define mentions? (subr rf-st (rf-value rf-value) bool)
  (lambda (s x) (cond ((rf-eqv? s x) #t) ((rf-pair? x) (or (mentions? s (rf-car x)) (mentions? s (rf-cdr x)))) (else #f))))

(define contract-forms (subr rf-eff (rf-value spec rf-value) rf-vals)
  (lambda (name sp e)
    (let* ((names (map (lambda ((p param)) (extract p name)) (extract sp params)))
           (shape (type-shape (extract sp result) result-list-bound)))
      (list (rf-list (vals-append (list (q 'define/contract) (rf-cons name (rf-list names)))
                                  (vals-append (if (pair? (extract sp requires)) (list (rf-cons (q 'requires) (rf-list (extract sp requires)))) nil)
                                               (vals-append (if (pair? (extract sp ensures))
                                                                (list (rf-cons (q 'ensures) (rf-cons (rf-list1 (extract sp result-name)) (rf-list (extract sp ensures)))))
                                                                nil)
                                                            (vals-append (if (rf-false? shape) nil (list (F2 (q 'returns-typed) shape)))
                                                                         (list (rf-cons e (rf-list names))))))))))))

"A proof calling name on symbolic values of its parameters' types (of its
contract, if for-contract?); none if a type has none."
(define proof-forms (subr rf-eff (rf-value spec bool) rf-vals)
  (lambda (name sp for-contract?)
    (let ((values (map (lambda ((p param)) (type-value (extract p type))) (extract sp params))))
      (if (memq-val? rf-false values) nil
          ;; (define-proof (name …) (begin (fx26-inputs-begin) (let* ((x v) …) (fx26-inputs-end (x T) …) (name x …))))
          (list (rf-list (list (q 'define-proof)
                               (rf-cons name (if for-contract? (rf-list1 (F2 (q 'for-contract) name)) rf-nil))
                               (F3 (q 'begin)
                                   (rf-list1 (q 'fx26-inputs-begin))
                                   (rf-list (list (q 'let*)
                                                  (rf-list (map2 (lambda ((p param) (v rf-value)) (F2 (extract p name) v)) (extract sp params) values))
                                                  (rf-cons (q 'fx26-inputs-end) (rf-list (map (lambda ((p param)) (F2 (extract p name) (extract p type))) (extract sp params))))
                                                  (rf-cons name (rf-list (map (lambda ((p param)) (extract p name)) (extract sp params))))))))))))))

"Collect the program's type definitions (of forms read): (define-type
name type), a family's (define-type (name (p kind) …) type), and a
datatype's, (define-datatype head (ctor type …) …), a sumof of productofs
labelled 1, 2, …."
(define note-types! (subr rf-st (rf-vals) unit)
  (lambda (forms)
    (for-each (lambda ((f rf-value))
                (let ((h (head-sym f)))
                  (cond ((and (eq? h 'define-type) (= (rf-length f) 3)) (note-type! (rf-cadr f) (rf-caddr f)))
                        ((and (eq? h 'define-datatype) (rf-pair? (rf-cdr f)))
                         (begin
                         (set datatype-names (cons (if (rf-pair? (rf-cadr f)) (rf-car (rf-cadr f)) (rf-cadr f)) (get datatype-names)))
                         (note-type! (rf-cadr f)
                                     (rf-cons (q 'sumof)
                                              (rf-list (map (lambda ((v rf-value))
                                                              (F2 (rf-car v)
                                                                  (rf-cons (q 'productof)
                                                                           (letrec ((fields (subr rf-st (rf-value int) rf-value)
                                                                                              (lambda (ts i) (if (rf-pair? ts) (rf-cons (F2 (rf-int i) (rf-car ts)) (fields (rf-cdr ts) (+ i 1))) rf-nil))))
                                                                             (fields (rf-cdr v) 1)))))
                                                            (rf-elements (rf-cddr f))))))))
                        (else #u))))
              (filter rf-pair? forms))))
(define note-type! (subr rf-st (rf-value rf-value) unit)
  (lambda (head t)
    (cond ((rf-symbol? head) (set type-names (cons (product (name head) (type t)) (get type-names))))
          ((and (rf-pair? head) (rf-symbol? (rf-car head)))
           (set type-names (cons (product (name (rf-car head))
                                          (type (F3 (q 'fx26-family) (rf-list (map (lambda ((p rf-value)) (if (rf-pair? p) (rf-car p) p)) (rf-elements (rf-cdr head)))) t)))
                                 (get type-names))))
          (else #u))))

"Survey a program before translating it: its files' types and literals
(so a definition's proof knows those of files loaded after it)."
(define survey-file (subr rf-eff (string (ref strings @rf)) unit)
  (lambda (file seen)
    (begin
      (set seen (cons file (get seen)))
      (let ((forms (fx26-read file)) (dir (directory-of file)))
        (begin
          (note-types! forms)
          (note-program-literals! forms)
          (for-each (lambda ((form rf-value))
                      (for-each (lambda ((f string))
                                  (let ((path (if (string-prefix? "/" f) f (string-append dir "/" f))))
                                    (if (or (built-in-file? f) (symbols-member? (string->symbol path) (map string->symbol (get seen)))) #u
                                        (survey-file path seen))))
                                (loaded-files form)))
                    forms))))))

"A program's forms, from file, and the module files it loads; loaded holds
the files read so far."
(define translate-file (subr rf-eff (string (ref strings @rf)) rf-vals)
  (lambda (file loaded)
    (begin
      (set loaded (cons file (get loaded)))
      (let ((dir (directory-of file)))
        (letrec ((load-files (subr rf-eff (rf-value) rf-vals)
                   (lambda (form)
                     (fx-append-all
                      (map (lambda ((f string))
                             (let ((path (if (string-prefix? "/" f) f (string-append dir "/" f))))
                               (if (or (built-in-file? f) (symbols-member? (string->symbol path) (map string->symbol (get loaded)))) nil
                                   (translate-file path loaded))))
                           (loaded-files form)))))
                 (each (subr rf-eff (rf-value) rf-vals)
                   (lambda (form)
                     (let ((h (head-sym form)))
                       (cond ((rf-string? form) nil)
                             ((symbols-member? h ignored-heads) nil)
                             ((eq? h 'define-datatype) (datatype-defines form))
                             ((eq? h 'define-rec)
                              (fx-append-all (map (lambda ((b rf-value)) (definition (rf-car b) (rf-cadr b) (rf-caddr b))) (rf-elements (rf-cdr form)))))
                             ((or (eq? h 'define) (eq? h 'define*))
                              (let ((files (load-files form)))
                                (if (pair? (loaded-files form))
                                    (vals-append files (list (rf-list (list (q 'define) (rf-cadr form) rf-true))))
                                    (definition (rf-cadr form) (if (= (rf-length form) 4) (rf-caddr form) rf-false) (definition-value form)))))
                             (else (let ((files (load-files form)))
                                     (if (pair? (loaded-files form)) files (list form)))))))))
          (fx-append-all (map each (fx26-read file))))))))

"An FX-26 program's forms for check-forms: FX-26's standard procedures,
then the program's."
(define fx26-program (subr rf-eff (string) rf-vals)
  (lambda (file)
    (begin (survey-file file (the (ref strings @rf) (new nil)))
           (vals-append (fx26-prelude) (translate-file file (the (ref strings @rf) (new nil)))))))

;;; ------------------------------------------------------------ FX-26's standard procedures

"Those that are not Scheme's own, in Scheme (read with no places, as
shakedown's prelude is)."
(define fx26-prelude-text string "
(define nil '())
(define (new v) (vector v))
(define (get r) (vector-ref r 0))
(define (set r v) (vector-set! r 0 v))
(define (list-length l) (length l))
(define (int->string n) (number->string n))
(define (char->string c) (string c))
(define (make-array n v) (make-vector n v))
(define (array-ref a i) (vector-ref a i))
(define (array-set! a i v) (vector-set! a i v))
(define (array-length a) (vector-length a))
(define (list->array l) (list->vector l))
(define (array->list a) (vector->list a))
(define (write-out s) (display s) (cons 'done (if #f #f)))
(define (write-err s) (display s) (cons 'done (if #f #f)))
(define (arithmetic-shift n k) (if (< k 0) (floor-quotient n (expt 2 (- k))) (* n (expt 2 k))))
(define (bool=? a b) (eq? a b))
(define (implies a b) (or (not a) b))
(define (fx26-any-nat) (let ((n (any-integer))) (assume (<= 0 n)) n))
(define (fx26-any-range lo hi) (let ((n (any-integer))) (assume (<= lo n)) (assume (<= n hi)) n))
(define (int->f64 n) (inexact n))
(define (f64->int x) (exact x))
(define (f64+ a b) (+ a b))
(define (f64- a b) (- a b))
(define (f64* a b) (* a b))
(define (f64/ a b) (/ a b))
(define (f64< a b) (< a b))
(define (f64<= a b) (<= a b))
(define (f64> a b) (> a b))
(define (f64>= a b) (>= a b))
(define (f64= a b) (= a b))
(define (f64-neg a) (- a))
(define (f64-abs a) (abs a))
(define (f64-floor a) (floor a))
(define (f64-ceiling a) (ceiling a))
(define (f64-round a) (round a))
(define (f64-truncate a) (truncate a))
(define (f64-sqrt a) (sqrt a))
(define (make-table hash same) (make-hashtable hash same))
(define (table-ref t k d) (hashtable-ref t k d))
(define (table-set! t k v) (hashtable-set! t k v))
(define (table-has? t k) (hashtable-contains? t k))
(define (table-count t) (hashtable-count t))
(define (string-hash s) 0)
(define (symbol-hash s) 0)
(define (pair-identity) #f)
(define (ref-identity) #f)
(define (array-identity) #f)
(define (make-eqtable identity) (make-eq-hashtable))
(define (eqtable-ref t k d) (hashtable-ref t k d))
(define (eqtable-has? t k) (hashtable-contains? t k))
(define (eqtable-set! t k v) (hashtable-set! t k v))
(define (eqtable-delete! t k) (hashtable-delete! t k))
(define (eqtable-count t) (hashtable-count t))
")
(define fx26-prelude-cache (ref (sumof (none unit) (some rf-vals)) @rf) (new (sum none #u)))
(define fx26-prelude (subr rf-eff () rf-vals)
  (lambda ()
    (tagcase (get fx26-prelude-cache)
      (some fs fs)
      (none u (let ((fs (read-text* fx26-prelude-text "fx26-prelude" #f #f))) (begin (set fx26-prelude-cache (sum some fs)) fs))))))
(define fx-append-all (subr rf-st ((listof rf-vals acyclic)) rf-vals)
  (lambda (ls) (if (null? ls) nil (vals-append (car ls) (fx-append-all (cdr ls))))))
