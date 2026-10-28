;;; core.fx: the language the CFA analyses, whatever language a program
;;; was written in -- FX-26 (fx26.fx) or Scheme (scheme.fx) -- and what a
;;; language tells the analysis about itself (`cf-lang`).
;;;
;;; As yank's `(yank analysis core)` and editor/flow.fx's core: every
;;; variable, lambda, call, allocation site and reference is numbered, in
;;; the world being read (`cf-reset!`). A name a world defines nowhere is
;;; one of its language's primitives, `k-prim`: what calling it does is the
;;; language's to say (`cf-model`), so the analysis itself knows neither
;;; language.
;;;
;;; Types and regions (FX-26's): a `plambda`'s binders are variables, and
;;; the lambda or site its body makes is said to be bound by them
;;; (`cf-poly!`); an instantiation (`k-inst`) gives them what it is given.
;;; Values themselves flow as if no type were there.
;;;
;;; State: global, at region @cf. One world is read and analysed at a time.

"What the CFA does to its own state."
(define-effect cf-eff (maxeff spin (read @globals) (read @cf) (write @cf) (alloc @cf)))

(define cf-tables (load-module "fx26:table.fx"))
(import cf-tables make-table table-ref table-set! (type table))

(define-type ints (listof int acyclic))
(define-type strings (listof string acyclic))
(define* cf-reverse-ints (subr spin (ints) ints)
  (lambda (l) (letrec ((go (subr spin (ints ints) ints) (lambda (l acc) (if (null? l) acc (go (cdr l) (cons (car l) acc))))))
                (go l nil))))
(define* cf-member? (subr spin (string strings) bool)
  (lambda (x l) (and (pair? l) (or (string=? (car l) x) (cf-member? x (cdr l))))))
"The place of `x` in `l` (-1: not there)."
(define* cf-index (subr spin (string strings) int)
  (lambda (x l) (letrec ((go (subr spin (strings int) int)
                           (lambda (l i) (cond ((null? l) -1) ((string=? (car l) x) i) (else (go (cdr l) (+ i 1)))))))
                  (go l 0))))

;;; ------------------------------------------------------------ the core

(define-datatype core
  (k-none (listof core acyclic))                ; evaluate these; the value is of no interest
  (k-const int)                                  ; a datum of a kind, by number (`cf-kind`)
  (k-var int int)                                ; a variable, by number; the reference, by number (-1: none)
  (k-prim string)                                ; a primitive of the language, by name
  (k-lam int)                                    ; a lambda, by number
  (k-app int core (listof core acyclic))         ; a call, by number: operator, arguments
  (k-seq (listof core acyclic))                  ; in order; the last one's value
  (k-alt (listof core acyclic))                  ; each a branch; any one's value
  (k-bind int core)                              ; the variable gets the value
  (k-alloc int (listof field-init acyclic))      ; a site, by number, and its fields
  (k-field core string)                          ; a field of what the value is
  (k-store core string core)                     ; a field of what the first is, given the second
  (k-case core (listof arm acyclic))             ; tagcase: the subject, the arms
  (k-escape (listof core acyclic))               ; given to code not known: escapes; unknown
  (k-inst core (listof core acyclic)))           ; instantiated: the value; its binders given these (`cf-poly`)
(define-type field-init (productof (label string) (value core)))
"A case's arm: its tag (\"\" for any), the variables it binds -- the
payload; or (`fields`) its product's fields by position, labels `1`, `2`,
… -- and its body."
(define-type arm (productof (tag string) (vars (listof int acyclic)) (fields bool) (body core)))
(define-type cores (listof core acyclic))

;;; ------------------------------------------------------------ languages

"What calling a primitive does, as its language says:
  m-data: its result is data of these kinds (by name; \"unknown\": anything),
          and, if `escapes`, what it is given escapes (it may call it, or
          keep it where code not known can);
  m-pass: its result is what it is given (FX-26's `list`, `reverse`);
  m-map:  it calls its first argument with the elements (the `car`s) of
          the lists it is given after, and what that returns escapes; its
          result is data of these kinds;
  m-apply: it calls its first argument with those after it but the last,
          then the elements of the last (a list); its result is that call's."
(define-datatype cf-model
  (m-data bool strings)
  (m-pass)
  (m-map strings)
  (m-apply))

"A language: its name, and what each of its primitives does."
(define-type cf-lang (productof (name string) (model (subr (maxeff spin (read @globals)) (string) cf-model))))

;;; ------------------------------------------------------------ numbering

"Where a node is: a file of the world, by number, and characters."
(define-type cf-span (productof (file int) (start int) (end int)))
(define-type lambda-info (productof (span cf-span) (name string) (params ints) (rest int) (body core)))
(define-type call-info (productof (span cf-span) (operator cf-span)))
(define-type site-info (productof (span cf-span) (kind string) (tag string)))
(define-type ref-info (productof (span cf-span) (name string)))

(define cf-no-span cf-span (product (file -1) (start 0) (end 0)))

(define cf-vars (ref int @cf) (new 0))
(define cf-lambdas (ref (listof lambda-info acyclic) @cf) (new nil))   ; newest first
(define cf-calls (ref (listof call-info acyclic) @cf) (new nil))
(define cf-sites (ref (listof site-info acyclic) @cf) (new nil))
(define cf-refs (ref (listof ref-info acyclic) @cf) (new nil))
"How many lambdas, calls, sites and references have been numbered."
(define cf-counts (arrayof int @cf) (make-array 4 0))
"The globals' variables, by name; and how many variables are globals'."
(define cf-globals (ref (table string int @cf) @cf) (new (the (table string int @cf) (make-table string-hash string=?))))
(define cf-global-count (ref int @cf) (new 0))
"The type binders of lambdas and sites made by a `plambda`'s body: each
lambda's (site's) number, and the binders' variables."
(define-type cf-poly (productof (number int) (binders (listof int acyclic))))
(define cf-poly-lambdas (ref (listof cf-poly acyclic) @cf) (new nil))
(define cf-poly-sites (ref (listof cf-poly acyclic) @cf) (new nil))
"A lambda's declared effect, as its definition says it: text, and the
variables of the type binders it names, to be said by what reaches them."
(define-datatype cf-token (t-text string) (t-var int string))
(define-type cf-effect (productof (lambda int) (tokens (listof cf-token acyclic))))
(define cf-effects (ref (listof cf-effect acyclic) @cf) (new nil))
"The world's files, by number."
(define cf-files (ref strings @cf) (new nil))
"The kinds of data the world's constants and primitives make, by name --
the language's (`number`, `string`, …), and, in FX-26, a region or a type
an instantiation gives (`@ed`) -- each numbered as first met."
(define cf-kinds (ref strings @cf) (new nil))
(define cf-kind-count (ref int @cf) (new 0))
"The definition being read, to name the lambdas in it: `go/λ`."
(define cf-definition (ref string @cf) (new ""))

(define-type cf-rest (productof (lambda int) (site int)))
(define cf-rest-sites (ref (listof cf-rest acyclic) @cf) (new nil))
(define cf-null-kind (ref string @cf) (new "null"))
"Everything numbered forgotten: a world to be read."
(define* cf-reset! (subr cf-eff () unit)
  (lambda ()
    (begin
      (set cf-vars 0) (set cf-lambdas nil) (set cf-calls nil) (set cf-sites nil) (set cf-refs nil)
      (array-set! cf-counts 0 0) (array-set! cf-counts 1 0) (array-set! cf-counts 2 0) (array-set! cf-counts 3 0)
      (set cf-globals (the (table string int @cf) (make-table string-hash string=?)))
      (set cf-global-count 0) (set cf-files nil) (set cf-definition "")
      (set cf-kinds nil) (set cf-kind-count 0) (set cf-poly-lambdas nil) (set cf-poly-sites nil) (set cf-effects nil)
      (set cf-rest-sites nil))))

"Kind `name`'s number, made on first use."
(define* cf-kind (subr cf-eff (string) int)
  (lambda (name)
    (let ((i (cf-index name (get cf-kinds))))
      (if (>= i 0) (- (- (get cf-kind-count) 1) i)
          (let ((n (get cf-kind-count)))
            (begin (set cf-kinds (cons name (get cf-kinds))) (set cf-kind-count (+ n 1)) n))))))
(define* cf-kind-name (subr cf-eff (int) string)
  (lambda (k) (letrec ((go (subr cf-eff (strings int) string)
                         (lambda (l i) (cond ((null? l) "?") ((= i 0) (car l)) (else (go (cdr l) (- i 1)))))))
                (go (get cf-kinds) (- (- (get cf-kind-count) 1) k)))))

(define* cf-new-var (subr cf-eff () int)
  (lambda () (let ((n (get cf-vars))) (begin (set cf-vars (+ n 1)) n))))

"The variable of global `name`, made on first use."
(define* cf-global-var (subr cf-eff (string) int)
  (lambda (name)
    (let ((v (table-ref (get cf-globals) name -1)))
      (if (>= v 0) v
          (let ((n (cf-new-var))) (begin (table-set! (get cf-globals) name n) n))))))
(define* cf-global-defined? (subr cf-eff (string) bool)
  (lambda (name) (>= (table-ref (get cf-globals) name -1) 0)))
"The globals are the variables declared so far: the rest are locals."
(define* cf-globals-declared! (subr cf-eff () unit) (lambda () (set cf-global-count (get cf-vars))))

(define* cf-next-number (subr cf-eff (int) int)
  (lambda (k) (let ((n (array-ref cf-counts k))) (begin (array-set! cf-counts k (+ n 1)) n))))
(define* cf-add-call (subr cf-eff (call-info) int)
  (lambda (info) (begin (set cf-calls (cons info (get cf-calls))) (cf-next-number 1))))
(define* cf-add-site (subr cf-eff (site-info) int)
  (lambda (info) (begin (set cf-sites (cons info (get cf-sites))) (cf-next-number 2))))
"A lambda with a rest parameter has a site, the list the rest are given
in (`cf-rest-sites`): its `car` what they are, its `cdr` itself, or the end
of a list (the kind the language names `cf-null-kind`)."
(define* cf-rest-site (subr spin ((listof cf-rest acyclic) int) int)
  (lambda (l n) (cond ((null? l) -1) ((= (extract (car l) lambda) n) (extract (car l) site)) (else (cf-rest-site (cdr l) n)))))
(define* cf-add-lambda (subr cf-eff (lambda-info) int)
  (lambda (info)
    (let ((n (begin (set cf-lambdas (cons info (get cf-lambdas))) (cf-next-number 0))))
      (begin
        (if (>= (extract info rest) 0)
            (set cf-rest-sites (cons (product (lambda n) (site (cf-add-site (product (span (extract info span)) (kind "pair") (tag "")))))
                                     (get cf-rest-sites)))
            #u)
        n))))
(define* cf-add-ref (subr cf-eff (ref-info) int)
  (lambda (info) (begin (set cf-refs (cons info (get cf-refs))) (cf-next-number 3))))
"A use of variable `v`, named `name`, at `span`."
(define* cf-ref (subr cf-eff (int string cf-span) core)
  (lambda (v name span) (k-var v (cf-add-ref (product (span span) (name name))))))

"Core `x`, a `plambda`'s body, bound by `binders`: the lambda or site it
makes, if it makes one, so said."
(define* cf-poly! (subr cf-eff (core ints) unit)
  (lambda (x binders)
    (tagcase x
      (k-lam (l) (set cf-poly-lambdas (cons (product (number l) (binders binders)) (get cf-poly-lambdas))))
      (k-alloc (s inits) (set cf-poly-sites (cons (product (number s) (binders binders)) (get cf-poly-sites))))
      (k-seq (xs) (if (pair? xs) (cf-poly! (car (reverse xs)) binders) #u))
      (else y #u))))
"The lambda core `x` makes, if it makes one (-1: none)."
(define* cf-lambda-of (subr spin (core) int)
  (lambda (x) (tagcase x
                (k-lam (l) l)
                (k-seq (xs) (if (pair? xs) (cf-lambda-of (car (reverse xs))) -1))
                (else y -1))))
(define* cf-poly-binders (subr spin ((listof cf-poly acyclic) int) ints)
  (lambda (l n) (cond ((null? l) nil) ((= (extract (car l) number) n) (extract (car l) binders)) (else (cf-poly-binders (cdr l) n)))))

"File `path`'s number in the world, made on first use."
(define* cf-file (subr cf-eff (string) int)
  (lambda (path)
    (letrec ((go (subr cf-eff (strings int) int)
               (lambda (l i) (cond ((null? l) (begin (set cf-files (append (get cf-files) (list path))) i))
                                   ((string=? (car l) path) i)
                                   (else (go (cdr l) (+ i 1)))))))
      (go (get cf-files) 0))))
(define* cf-file-name (subr cf-eff (int) string)
  (lambda (i) (letrec ((go (subr cf-eff (strings int) string)
                         (lambda (l i) (cond ((null? l) "") ((= i 0) (car l)) (else (go (cdr l) (- i 1)))))))
                (go (get cf-files) i))))

"A lambda's name where it has none of its own: of the definition it is in."
(define* cf-anonymous (subr cf-eff () string)
  (lambda () (string-append (get cf-definition) "/λ")))

