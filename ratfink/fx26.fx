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

(define fx-error (subr rf-eff (string rf-value) void) (lambda (m f) (rf-error (string-append "ratfink: " m) (list f))))
(define head-sym (subr rf-st (rf-value) symbol)
  (lambda (f) (if (and (rf-pair? f) (rf-symbol? (rf-car f))) (rf-sym-of (rf-car f)) '||)))
(define string-starts? (subr rf-st (string string) bool)
  (lambda (prefix s) (and (>= (string-length s) (string-length prefix)) (string=? (substring s 0 (string-length prefix)) prefix))))
(define string-ends? (subr rf-st (string string) bool)
  (lambda (suffix s) (and (>= (string-length s) (string-length suffix))
                          (string=? (substring s (- (string-length s) (string-length suffix)) (string-length s)) suffix))))

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
  (lambda (f) (or (string-starts? "fx26:" f) (string-ends? "ratfink/proof.fx" f) (string=? f "proof.fx"))))

(define fx26-read (subr rf-eff (string) rf-vals)
  (lambda (file)
    (begin (set-fx26-syntax! #t)
           (let ((forms (read-file-data file #f))) (begin (set-fx26-syntax! #f) forms)))))

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
      (if (and (rf-symbol? name) (string-starts? "proof-" (symbol->string (rf-sym-of name)))
               (rf-pair? v) (rf-eqv? (rf-car v) (q 'lambda)) (rf-null? (rf-cadr v)))
          (list (rf-cons (q 'define-proof) (rf-cons (rf-list1 name) (rf-cddr v))))
          (tagcase (spec-of type)
            (none u (list (rf-list (list (q 'define) name e))))
            (some sp
              (cond ((specified? sp) (vals-append (contract-forms name sp e) (proof-forms name sp #t)))
                    ((harness? sp v) (cons (rf-list (list (q 'define) name e)) (proof-forms name sp #f)))
                    (else (list (rf-list (list (q 'define) name e)))))))))))

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
                                            (product (name (rf-sym (string->symbol (string-append "arg" (int->string (get count)))))) (type p)))))
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

"The shape of a type's values, or #f."
(define type-shape (subr rf-st (rf-value int) rf-value)
  (lambda (t0 bound)
    (let ((t (expand-type t0)))
      (cond ((or (rf-eqv? t (q 'int)) (rf-eqv? t (q 'nat)) (and (rf-pair? t) (rf-eqv? (rf-car t) (q 'nat)))) (q 'integer))
            ((rf-eqv? t (q 'bool)) (q 'boolean))
            ((and (rf-pair? t) (rf-eqv? (rf-car t) (q 'listof)))
             (let ((e (type-shape (rf-cadr t) bound))) (if (rf-false? e) rf-false (F3 (q 'list-of) (rf-int bound) e))))
            (else rf-false)))))
"An expression making a symbolic value of a type, or #f."
(define type-value (subr rf-st (rf-value) rf-value)
  (lambda (t0)
    (let ((t (expand-type t0)))
      (cond ((rf-eqv? t (q 'int)) (rf-list1 (q 'any-integer)))
            ;; (nat k): the size k.
            ((and (rf-pair? t) (rf-eqv? (rf-car t) (q 'nat)) (rf-exact-integer? (rf-cadr t))) (rf-cadr t))
            ;; A type variable: the procedure cannot look at its value.
            ((and (rf-symbol? t) (type-variable? t)) (F2 (q 'quote) (q 'opaque)))
            ((rf-eqv? t (q 'nat)) (rf-list1 (q 'fx26-any-nat)))
            ((rf-eqv? t (q 'bool)) (rf-list1 (q 'any-boolean)))
            ((and (rf-pair? t) (rf-eqv? (rf-car t) (q 'listof)))
             (let ((e (type-value (rf-cadr t))))
               (if (rf-false? e) rf-false (F3 (q 'any-list) (rf-int list-bound) (rf-list (list (q 'lambda) rf-nil e))))))
            (else rf-false)))))

"A name that is no type FX-26 has, nor the program: a type variable."
(define type-variable? (subr rf-st (rf-value) bool)
  (lambda (t)
    (not (symbols-member? (rf-sym-of t) (list 'int 'nat 'bool 'char 'string 'unit 'symbol 'datum 'i32 'u32 'i64 'u64 'f64 'f32 'void)))))

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
             (rf-cons (q 'letrec) (rf-cons (rf-list new-bindings) (rf-append2 (rf-list (vals-reverse (get checks))) body)))))
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
          (list (rf-list (list (q 'define-proof)
                               (rf-cons name (if for-contract? (rf-list1 (F2 (q 'for-contract) name)) rf-nil))
                               (F3 (q 'let*)
                                   (rf-list (map2 (lambda ((p param) (v rf-value)) (F2 (extract p name) v)) (extract sp params) values))
                                   (rf-cons name (rf-list (map (lambda ((p param)) (extract p name)) (extract sp params))))))))))))

"Collect the program's type abbreviations (of forms read)."
(define note-types! (subr rf-st (rf-vals) unit)
  (lambda (forms)
    (for-each (lambda ((f rf-value))
                (if (and (rf-eqv? (rf-car f) (q 'define-type)) (rf-symbol? (rf-cadr f)) (= (rf-length f) 3))
                    (set type-names (cons (product (name (rf-cadr f)) (type (rf-caddr f))) (get type-names)))
                    #u))
              (filter rf-pair? forms))))

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
                             (let ((path (if (string-starts? "/" f) f (string-append dir "/" f))))
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
          (let ((forms (fx26-read file))) (begin (note-types! forms) (fx-append-all (map each forms)))))))))

"An FX-26 program's forms for check-forms: FX-26's standard procedures,
then the program's."
(define fx26-program (subr rf-eff (string) rf-vals)
  (lambda (file)
    (vals-append (fx26-prelude) (translate-file file (the (ref strings @rf) (new nil))))))

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
