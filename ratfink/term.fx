;;; term.fx: symbolic terms, the formulas sent to the solver: shakedown's
;;; `(shakedown term)`.
;;;
;;; A term is an Int- or Bool-sorted expression over symbolic constants.
;;; Its leaves are terms or concrete values: exact integers for Int, #t and
;;; #f for Bool. Terms are hash-consed (built once for each operator and
;;; arguments), so terms of one id are one and the solver sees a DAG. The
;;; constructors (t-and, t-+, …) fold constants and apply simple identities,
;;; so a term with no constants in it is never built: (t-+ 1 2) is 3.
;;;
;;; Ids are given in the order shakedown gives them -- where shakedown's
;;; code builds terms in a `let`'s inits, in the order Twobit evaluates
;;; them, right to left -- since the solver is sent terms by their ids.

(module-parameters ((m-core (load-moduleof "core.fx"))))

;;; ------------------------------------------------------------ operators and sorts

(define iabs (subr rf-st (int) int) (lambda (i) (if (< i 0) (- 0 i) i)))

(define op-const int 0)
(define op-not int 1)
(define op-and int 2)
(define op-or int 3)
(define op-ite int 4)
(define op-eq int 5)
(define op-lt int 6)
(define op-le int 7)
(define op-add int 8)
(define op-sub int 9)
(define op-mul int 10)
(define op-div int 11)
(define op-mod int 12)
(define op-abs int 13)
"An operator's name in SMT-LIB (and shakedown's)."
(define op-name (subr rf-st (int) string)
  (lambda (op)
    (cond ((= op op-const) "const") ((= op op-not) "not") ((= op op-and) "and") ((= op op-or) "or")
          ((= op op-ite) "ite") ((= op op-eq) "=") ((= op op-lt) "<") ((= op op-le) "<=")
          ((= op op-add) "+") ((= op op-sub) "-") ((= op op-mul) "*") ((= op op-div) "div")
          ((= op op-mod) "mod") (else "abs"))))
(define sort-int int 0)
(define sort-bool int 1)
(define sort-name (subr rf-st (int) string) (lambda (s) (if (= s sort-int) "Int" "Bool")))

(define term-id (subr rf-st (rf-term) int) (lambda (t) (extract t id)))
(define term-op (subr rf-st (rf-term) int) (lambda (t) (extract t op)))
(define term-args (subr rf-st (rf-term) rf-vals) (lambda (t) (extract t args)))
(define term-sort (subr rf-st (rf-term) int) (lambda (t) (extract t sort)))
(define term-arg (subr rf-st (rf-term int) rf-value) (lambda (t i) (vals-ref (extract t args) i)))

"The term a value is (a dummy for any other value)."
(define no-term rf-term (product (id -1) (op -1) (args nil) (sort -1)))
(define term-of (subr rf-st (rf-value) rf-term) (lambda (v) (tagcase v (term t t) (else x no-term))))

(define int-term? (subr rf-st (rf-value) bool)
  (lambda (v) (tagcase v (term t (= (extract t sort) sort-int)) (else x #f))))
(define bool-term? (subr rf-st (rf-value) bool)
  (lambda (v) (tagcase v (term t (= (extract t sort) sort-bool)) (else x #f))))
(define int-like? (subr rf-st (rf-value) bool)
  (lambda (v) (tagcase v (int i #t) (term t (= (extract t sort) sort-int)) (else x #f))))
(define bool-like? (subr rf-st (rf-value) bool)
  (lambda (v) (tagcase v (bool b #t) (term t (= (extract t sort) sort-bool)) (else x #f))))
(define constant? (subr rf-st (rf-value) bool)
  (lambda (v) (tagcase v (term t (= (extract t op) op-const)) (else x #f))))
"Whether v is a term of operator op."
(define op? (subr rf-st (int rf-value) bool)
  (lambda (op v) (tagcase v (term t (= (extract t op) op)) (else x #f))))
"The arguments of a term value (none for anything else)."
(define targs (subr rf-st (rf-value) rf-vals) (lambda (v) (tagcase v (term t (extract t args)) (else x nil))))
(define targ1 (subr rf-st (rf-value) rf-value) (lambda (v) (vals-ref (targs v) 0)))
(define targ2 (subr rf-st (rf-value) rf-value) (lambda (v) (vals-ref (targs v) 1)))
(define targ3 (subr rf-st (rf-value) rf-value) (lambda (v) (vals-ref (targs v) 2)))
(define tid (subr rf-st (rf-value) int) (lambda (v) (tagcase v (term t (extract t id)) (else x -1))))

;;; ------------------------------------------------------------ the table of terms

(define next-term-id (ref int @rf) (new 0))
(define fresh-term-id! (subr rf-st () int)
  (lambda () (begin (set next-term-id (+ (get next-term-id) 1)) (get next-term-id))))

"A key: an operator and its arguments."
(define-type term-key (productof (op int) (args rf-vals)))
(define arg-hash (subr rf-st (rf-value) int)
  (lambda (a) (tagcase a (term t (* 31 (extract t id))) (int i (+ 7 (* 31 (modulo i 1000003)))) (bool b (if b 1 2)) (else x 3))))
(define key-hash (subr rf-st (term-key) int)
  (lambda (k)
    (letrec ((go (subr rf-st (rf-vals int) int)
               (lambda (l h) (if (null? l) h (go (cdr l) (modulo (+ (* h 1000003) (arg-hash (car l))) 4294967291))))))
      (go (extract k args) (+ 17 (extract k op))))))
"Whether two arguments are the same: terms by id, concrete values by value."
(define same-arg? (subr rf-st (rf-value rf-value) bool)
  (lambda (a b)
    (tagcase a
      (term s (tagcase b (term t (= (extract s id) (extract t id))) (else x #f)))
      (int i (tagcase b (int j (= i j)) (else x #f)))
      (bool c (tagcase b (bool d (eq? c d)) (else x #f)))
      (else x #f))))
(define same-args? (subr rf-st (rf-vals rf-vals) bool)
  (lambda (a b) (cond ((null? a) (null? b)) ((null? b) #f) ((same-arg? (car a) (car b)) (same-args? (cdr a) (cdr b))) (else #f))))
(define key-same? (subr rf-st (term-key term-key) bool)
  (lambda (a b) (and (= (extract a op) (extract b op)) (same-args? (extract a args) (extract b args)))))

(define-type term-table (htable term-key rf-term))
(define new-term-table (subr rf-st () term-table) (lambda () ((proj ht-make term-key rf-term) key-hash key-same?)))
(define the-terms (ref term-table @rf) (new (new-term-table)))

"The term of op and args, made if it is not there."
(define mk (subr rf-st (int int rf-vals) rf-value)
  (lambda (op sort args)
    (let* ((key (product (op op) (args args)))
           (t ((proj ht-ref term-key rf-term) (get the-terms) key no-term)))
      (if (>= (extract t id) 0)
          (sum term t)
          (let ((t (product (id (fresh-term-id!)) (op op) (args args) (sort sort))))
            (begin ((proj ht-set! term-key rf-term) (get the-terms) key t) (sum term t)))))))

"Tables keyed by terms' ids."
(define-type (by-id (v type)) (table int v @rf))
(define id-hash (subr pure (int) int) (lambda (i) i))
(define id-same? (subr pure (int int) bool) (lambda (a b) (= a b)))

"Index constants' ranges, by id."
(define ranges (ref (by-id int) @rf) (new (the (by-id int) (make-table id-hash id-same?))))

"A fresh symbolic constant of the sort."
(define make-constant (subr rf-st (int) rf-value)
  (lambda (sort) (sum term (product (id (fresh-term-id!)) (op op-const) (args nil) (sort sort)))))
"An Int constant whose value is known to be in [0, n): an index that picks
one of n things. The solver may encode it as n booleans (smt.fx)."
(define make-index-constant (subr rf-st (int) rf-value)
  (lambda (n)
    (let ((k (make-constant sort-int)))
      (begin (table-set! (get ranges) (tid k) n) k))))
"n for an index constant, else -1."
(define constant-range (subr rf-st (rf-value) int)
  (lambda (k) (table-ref (get ranges) (tid k) -1)))

"Forget every term (a new program's check)."
(define reset-terms! (subr rf-st () unit)
  (lambda ()
    (begin (set the-terms (new-term-table))
           (set next-term-id 0)
           (set ranges (the (by-id int) (make-table id-hash id-same?)))
           (set pushed-table (new-pushed-table))
           (set choice-table (the (by-id bool) (make-table id-hash id-same?)))
           (set cases-table (the (by-id maybe-cases) (make-table id-hash id-same?)))
           (set distributed (new-pushed-table)))))

;;; ------------------------------------------------------------ ordering arguments

"Arguments of commutative operators are put in order, concrete ones first,
so that equal terms are built the same way."
(define arg<? (subr rf-st (rf-value rf-value) bool)
  (lambda (a b)
    (tagcase a
      (term s (tagcase b (term t (< (extract s id) (extract t id))) (else x #f)))
      (else x (rf-term? b)))))
"Sorted, stably (shakedown inserts each in turn, or past 32, list-sort's
merge sort: stable either way)."
(define sort-args (subr rf-st (rf-vals) rf-vals)
  (lambda (args)
    (let ((n (list-length args)))
      (if (< n 2) args
          (let ((half (quotient n 2)))
            (merge-args (sort-args (vals-head args half)) (sort-args (vals-tail args half))))))))
(define merge-args (subr rf-st (rf-vals rf-vals) rf-vals)
  (lambda (a b)
    (cond ((null? a) b) ((null? b) a)
          ((arg<? (car b) (car a)) (cons (car b) (merge-args a (cdr b))))
          (else (cons (car a) (merge-args (cdr a) b))))))

;;; ------------------------------------------------------------ Booleans

(define t-not (subr rf-st (rf-value) rf-value)
  (lambda (a)
    (tagcase a
      (bool b (rf-bool (not b)))
      (else x (if (op? op-not a) (targ1 a) (mk op-not sort-bool (list a)))))))

"An and or or with this many arguments or more is kept whole, not flattened
(a path's condition grows by one at each step)."
(define many-args int 32)
(define shorter? (subr rf-st (rf-vals int) bool)
  (lambda (l n) (or (null? l) (and (> n 0) (shorter? (cdr l) (- n 1))))))

(define-type seen-set (by-id bool))
(define new-seen (subr rf-st () seen-set) (lambda () (the seen-set (make-table id-hash id-same?))))
"Whether a value (a term: the others never reach here twice) is in seen."
(define seen? (subr rf-st (seen-set rf-value) bool) (lambda (s v) (table-ref s (tid v) #f)))
(define see! (subr rf-st (seen-set rf-value) unit) (lambda (s v) (table-set! s (tid v) #t)))

"Flatten nested uses of op, drop the identity, and stop at the absorbing
element: `none` if the absorbing element was found."
(define-type maybe-vals (sumof (none unit) (some rf-vals)))
(define collect (subr rf-st (int bool rf-vals) maybe-vals)
  (lambda (op identity xs)
    (letrec ((loop (subr rf-st (rf-vals rf-vals int (sumof (none unit) (some seen-set))) maybe-vals)
               (lambda (xs acc n seen)
                 (if (null? xs) (sum some acc)
                     (let ((x (car xs)))
                       (cond ((and (rf-boolean? x) (eq? (rf-true? x) identity)) (loop (cdr xs) acc n seen))
                             ((rf-boolean? x) (sum none #u))
                             ((and (op? op x) (shorter? (targs x) many-args))
                              (loop (vals-append (targs x) (cdr xs)) acc n seen))
                             ((tagcase seen (some s (seen? s x)) (none u (memq-val? x acc)))
                              (loop (cdr xs) acc n seen))
                             ((and (tagcase seen (none u #t) (some s #f)) (= n many-args))
                              (let ((s (new-seen)))
                                (begin (for-each (lambda ((y rf-value)) (see! s y)) acc)
                                       (loop xs acc n (sum some s)))))
                             (else
                              (begin (tagcase seen (some s (see! s x)) (none u #u))
                                     (loop (cdr xs) (cons x acc) (+ n 1) seen)))))))))
      (loop xs nil 0 (sum none #u)))))

(define complementary? (subr rf-st (rf-vals) bool)
  (lambda (xs)
    (if (< (list-length xs) many-args)
        (letrec ((loop (subr rf-st (rf-vals) bool)
                   (lambda (ys) (and (pair? ys) (or (and (op? op-not (car ys)) (memq-val? (targ1 (car ys)) xs)) (loop (cdr ys)))))))
          (loop xs))
        (let ((s (new-seen)))
          (begin
            (for-each (lambda ((x rf-value)) (if (rf-term? x) (see! s x) #u)) xs)
            (letrec ((loop (subr rf-st (rf-vals) bool)
                       (lambda (ys) (and (pair? ys) (or (and (op? op-not (car ys)) (seen? s (targ1 (car ys)))) (loop (cdr ys)))))))
              (loop xs)))))))

(define junction (subr rf-st (int bool rf-vals) rf-value)
  (lambda (op identity xs)
    (tagcase (collect op identity xs)
      (none u (rf-bool (not identity)))
      (some args
        (cond ((null? args) (rf-bool identity))
              ((null? (cdr args)) (car args))
              ((complementary? args) (rf-bool (not identity)))
              (else (mk op sort-bool (sort-args args))))))))

(define t-and* (subr rf-st (rf-vals) rf-value) (lambda (xs) (junction op-and #t xs)))
(define t-or* (subr rf-st (rf-vals) rf-value) (lambda (xs) (junction op-or #f xs)))
(define t-and (subr rf-st (rf-value rf-value) rf-value) (lambda (a b) (t-and* (list a b))))
(define t-or (subr rf-st (rf-value rf-value) rf-value) (lambda (a b) (t-or* (list a b))))
(define t-and3 (subr rf-st (rf-value rf-value rf-value) rf-value) (lambda (a b c) (t-and* (list a b c))))
(define t-implies (subr rf-st (rf-value rf-value) rf-value) (lambda (a b) (t-or (t-not a) b)))

"if c then a else b; a and b both Int-like or both Bool-like."
(define t-ite (subr rf-st (rf-value rf-value rf-value) rf-value)
  (lambda (c a b)
    (cond ((rf-true? c) a)
          ((rf-false? c) b)
          ((op? op-not c) (t-ite (targ1 c) b a))
          (else
           ;; An ite on the same condition in an arm takes its own arm.
           (let ((a (if (and (op? op-ite a) (rf-eqv? c (targ1 a))) (targ2 a) a))
                 (b (if (and (op? op-ite b) (rf-eqv? c (targ1 b))) (targ3 b) b)))
             (cond ((rf-eqv? a b) a)
                   ((bool-like? a)
                    (cond ((rf-true? a) (t-or c b))
                          ((rf-false? a) (t-and (t-not c) b))
                          ((rf-true? b) (t-or (t-not c) a))
                          ((rf-false? b) (t-and c a))
                          ((rf-eqv? a c) (t-or c b))
                          ((rf-eqv? b c) (t-and c a))
                          (else (mk op-ite sort-bool (list c a b)))))
                   (else (mk op-ite sort-int (list c a b)))))))))

"a = b, for two Int-like or two Bool-like values."
(define t-= (subr rf-st (rf-value rf-value) rf-value)
  (lambda (a b)
    (cond ((rf-eqv? a b) rf-true)
          ((and (rf-exact-integer? a) (rf-exact-integer? b)) rf-false)
          ((and (rf-boolean? a) (rf-boolean? b)) rf-false)
          ((rf-boolean? a) (if (rf-true? a) b (t-not b)))
          ((rf-boolean? b) (if (rf-true? b) a (t-not a)))
          ;; Push a comparison with a constant into the arms of an ite,
          ;; which then often folds: (= (ite c 1 2) 1) is c.
          ((and (op? op-ite a) (not (rf-term? b))) (push-= a b))
          ((and (op? op-ite b) (not (rf-term? a))) (push-= b a))
          (else (mk op-eq sort-bool (sort-args (list a b)))))))

"(= a b) for an ite a and a concrete b, by arm, remembered: the arms of an
ite are often shared (a DAG)."
(define-type pushed-key (productof (id int) (v rf-value)))
(define pushed-hash (subr rf-st (pushed-key) int)
  (lambda (k) (modulo (+ (* 1000003 (extract k id)) (arg-hash (extract k v))) 4294967291)))
(define pushed-same? (subr rf-st (pushed-key pushed-key) bool)
  (lambda (a b) (and (= (extract a id) (extract b id)) (same-arg? (extract a v) (extract b v)))))
(define new-pushed-table (subr rf-st () (htable pushed-key rf-value))
  (lambda () ((proj ht-make pushed-key rf-value) pushed-hash pushed-same?)))
(define pushed-table (ref (htable pushed-key rf-value) @rf) (new (new-pushed-table)))
(define push-= (subr rf-st (rf-value rf-value) rf-value)
  (lambda (a b)
    (let* ((key (product (id (tid a)) (v b)))
           (known ((proj ht-ref pushed-key rf-value) (get pushed-table) key rf-unbound)))
      (if (rf-unbound? known)
          (let ((r (t-ite (targ1 a) (t-= (targ2 a) b) (t-= (targ3 a) b))))
            (begin ((proj ht-set! pushed-key rf-value) (get pushed-table) key r) r))
          known))))

;;; ------------------------------------------------------------ integers

(define t-< (subr rf-st (rf-value rf-value) rf-value)
  (lambda (a b)
    (cond ((and (rf-exact-integer? a) (rf-exact-integer? b)) (rf-bool (< (rf-int-of a) (rf-int-of b))))
          ((rf-eqv? a b) rf-false)
          (else (tagcase (combine-cases (lambda ((x int) (y int)) (if (< x y) 1 0)) #t a b)
                  (some v v)
                  (none u (mk op-lt sort-bool (list a b))))))))
(define t-<= (subr rf-st (rf-value rf-value) rf-value)
  (lambda (a b)
    (cond ((and (rf-exact-integer? a) (rf-exact-integer? b)) (rf-bool (<= (rf-int-of a) (rf-int-of b))))
          ((rf-eqv? a b) rf-true)
          (else (tagcase (combine-cases (lambda ((x int) (y int)) (if (<= x y) 1 0)) #t a b)
                  (some v v)
                  (none u (mk op-le sort-bool (list a b))))))))

"The concrete addend of a sum (+ k t), or 0; and the rest."
(define sum-constant (subr rf-st (rf-value) int)
  (lambda (t) (if (and (op? op-add t) (rf-exact-integer? (targ1 t))) (rf-int-of (targ1 t)) 0)))
(define sum-rest (subr rf-st (rf-value) rf-value)
  (lambda (t) (if (and (op? op-add t) (rf-exact-integer? (targ1 t))) (targ2 t) t)))

(define t-+ (subr rf-st (rf-value rf-value) rf-value)
  (lambda (a b)
    (cond ((and (rf-exact-integer? a) (rf-exact-integer? b)) (rf-int (+ (rf-int-of a) (rf-int-of b))))
          ((rf-eqv? a (rf-int 0)) b)
          ((rf-eqv? b (rf-int 0)) a)
          ;; Keep one concrete addend: (+ (+ 1 x) 2) is (+ 3 x).
          ((and (rf-exact-integer? b) (not (= (sum-constant a) 0)))
           (t-+ (sum-rest a) (rf-int (+ (rf-int-of b) (sum-constant a)))))
          ((and (rf-exact-integer? a) (not (= (sum-constant b) 0)))
           (t-+ (sum-rest b) (rf-int (+ (rf-int-of a) (sum-constant b)))))
          (else
           ;; A choice plus an integer is a choice; a sum of two choices
           ;; stays a sum.
           (tagcase (if (or (rf-exact-integer? a) (rf-exact-integer? b))
                        (combine-cases (lambda ((x int) (y int)) (+ x y)) #f a b)
                        (sum none #u))
             (some v v)
             (none u (mk op-add sort-int (sort-args (list a b)))))))))

"The cases of an ite of integers, if it is one with few enough values."
(define ite-cases (subr rf-st (rf-value) maybe-cases)
  (lambda (a) (if (op? op-ite a) (integer-cases a) (sum none #u))))

(define t-neg (subr rf-st (rf-value) rf-value)
  (lambda (a)
    (cond ((rf-exact-integer? a) (rf-int (- 0 (rf-int-of a))))
          ((and (op? op-sub a) (null? (cdr (targs a)))) (targ1 a))
          (else (tagcase (ite-cases a)
                  (some cases (from-cases cases (lambda ((v int)) (rf-int (- 0 v)))))
                  (none u (mk op-sub sort-int (list a))))))))

(define t-- (subr rf-st (rf-value rf-value) rf-value)
  (lambda (a b)
    (cond ((and (rf-exact-integer? a) (rf-exact-integer? b)) (rf-int (- (rf-int-of a) (rf-int-of b))))
          ((rf-exact-integer? b) (t-+ a (rf-int (- 0 (rf-int-of b)))))
          ((rf-eqv? a b) (rf-int 0))
          ((rf-eqv? a (rf-int 0)) (t-neg b))
          (else
           (tagcase (if (rf-exact-integer? a) (combine-cases (lambda ((x int) (y int)) (- x y)) #f a b) (sum none #u))
             (some v v)
             (none u (mk op-sub sort-int (list a b))))))))

(define t-* (subr rf-st (rf-value rf-value) rf-value)
  (lambda (a b)
    (cond ((and (rf-exact-integer? a) (rf-exact-integer? b)) (rf-int (* (rf-int-of a) (rf-int-of b))))
          ((or (rf-eqv? a (rf-int 0)) (rf-eqv? b (rf-int 0))) (rf-int 0))
          ((rf-eqv? a (rf-int 1)) b)
          ((rf-eqv? b (rf-int 1)) a)
          ((rf-eqv? a (rf-int -1)) (t-neg b))
          ((rf-eqv? b (rf-int -1)) (t-neg a))
          (else
           (tagcase (combine-cases (lambda ((x int) (y int)) (* x y)) #f a b)
             (some v v)
             (none u
               ;; A product with a choice among a few integers is a choice
               ;; of products, so stays linear.
               (tagcase (ite-cases a)
                 (some cases (from-cases cases (lambda ((v int)) (t-* (rf-int v) b))))
                 (none u
                   (tagcase (ite-cases b)
                     (some cases (from-cases cases (lambda ((v int)) (t-* a (rf-int v)))))
                     (none u
                       ;; And with a choice of too many values, or of sums
                       ;; of choices, the same arithmetic over its parts.
                       (cond ((and (rf-term? a) (choice? a)) (distribute a b))
                             ((and (rf-term? b) (choice? b)) (distribute b a))
                             (else (mk op-mul sort-int (sort-args (list a b)))))))))))))))

"Whether t is built of integers by ite, + and -: a choice of values,
however many."
(define choice-table (ref (by-id bool) @rf) (new (the (by-id bool) (make-table id-hash id-same?))))
(define choice? (subr rf-st (rf-value) bool)
  (lambda (t)
    (cond ((rf-exact-integer? t) #t)
          ((not (or (op? op-ite t) (op? op-add t) (op? op-sub t))) #f)
          ((table-has? (get choice-table) (tid t)) (table-ref (get choice-table) (tid t) #f))
          (else
           (let ((c (letrec ((all (subr rf-st (rf-vals) bool)
                                (lambda (args) (or (null? args) (and (choice? (car args)) (all (cdr args)))))))
                      (all (if (op? op-ite t) (cdr (targs t)) (targs t))))))
             (begin (table-set! (get choice-table) (tid t) c) c))))))

"(* c b) for a choice c, as its ites and sums of products, each of a choice
among few integers and b. Memoized: c is a DAG."
(define distributed (ref (htable pushed-key rf-value) @rf) (new (new-pushed-table)))
(define distribute (subr rf-st (rf-value rf-value) rf-value)
  (lambda (c b)
    (if (or (rf-exact-integer? c) (tagcase (integer-cases c) (some cs #t) (none u #f)))
        (t-* c b)
        (let* ((key (product (id (tid c)) (v b)))
               (known ((proj ht-ref pushed-key rf-value) (get distributed) key rf-unbound)))
          (if (not (rf-unbound? known)) known
              (let* ((args (targs c))
                     (p (cond ((op? op-ite c) (t-ite (car args) (distribute (targ2 c) b) (distribute (targ3 c) b)))
                              ((op? op-add c) (t-+ (distribute (car args) b) (distribute (targ2 c) b)))
                              ((null? (cdr args)) (t-neg (distribute (car args) b)))
                              (else (t-- (distribute (car args) b) (distribute (targ2 c) b))))))
                (begin ((proj ht-set! pushed-key rf-value) (get distributed) key p) p)))))))

;;; ------------------------------------------------------------ choices among a few integers
;;;
;;; A term built of ites whose leaves are integers takes one of a few
;;; values; its cases are a list of (value . condition), counting values,
;;; not leaves.

(define max-cases int 32)
(define-type a-case (productof (value int) (cond rf-value)))
(define-type cases (listof a-case acyclic))
(define-type maybe-cases (sumof (none unit) (some cases)))
(define cases-table (ref (by-id maybe-cases) @rf) (new (the (by-id maybe-cases) (make-table id-hash id-same?))))

"t's cases, or none if it is not such a term (or has too many)."
(define integer-cases (subr rf-st (rf-value) maybe-cases)
  (lambda (t)
    (cond ((rf-exact-integer? t) (sum some (list (product (value (rf-int-of t)) (cond rf-true)))))
          ((not (op? op-ite t)) (sum none #u))
          ((table-has? (get cases-table) (tid t)) (table-ref (get cases-table) (tid t) (sum none #u)))
          (else (compute-cases! t)))))

(define compute-cases! (subr rf-st (rf-value) maybe-cases)
  (lambda (t)
    (let* ((c (targ1 t))
           (yes (integer-cases (targ2 t)))
           (no (tagcase yes (some y (integer-cases (targ3 t))) (none u (sum none #u))))
           (cs (tagcase yes
                 (none u (sum none #u))
                 (some ys
                   (tagcase no
                     (none u (sum none #u))
                     (some ns
                       ;; add-cases's arguments, left to right.
                       (let* ((a (map (lambda ((k a-case)) (product (value (extract k value)) (cond (t-and c (extract k cond))))) ys))
                              (b (map (lambda ((k a-case)) (product (value (extract k value)) (cond (t-and (t-not c) (extract k cond))))) ns)))
                         (add-cases a b))))))))
      (begin (table-set! (get cases-table) (tid t) cs) cs))))

"The union of two lists of cases, or none if it has too many values."
(define add-cases (subr rf-st (cases cases) maybe-cases)
  (lambda (xs ys)
    (letrec ((loop (subr rf-st (cases cases) maybe-cases)
               (lambda (ys acc)
                 (cond ((> (list-length acc) max-cases) (sum none #u))
                       ((null? ys) (sum some acc))
                       (else
                        (let ((y (car ys)))
                          (tagcase (find-case (extract y value) acc)
                            (some k (loop (cdr ys)
                                          (map (lambda ((j a-case))
                                                 (if (eq? j k)
                                                     (product (value (extract k value)) (cond (t-or (extract k cond) (extract y cond))))
                                                     j))
                                               acc)))
                            (none u (loop (cdr ys) (cons y acc))))))))))
      (loop ys xs))))
(define find-case (subr rf-st (int cases) (sumof (none unit) (some a-case)))
  (lambda (v l) (cond ((null? l) (sum none #u)) ((= v (extract (car l) value)) (sum some (car l))) (else (find-case v (cdr l))))))

"A term that is (f value) under each case's condition."
(define from-cases (subr rf-st (cases (subr rf-st (int) rf-value)) rf-value)
  (lambda (cs f)
    (if (null? (cdr cs))
        (f (extract (car cs) value))
        (let* ((x (f (extract (car cs) value)))
               (y (from-cases (cdr cs) f)))
          (t-ite (extract (car cs) cond) x y)))))

"(op a b) as a choice, if a and b are integers or choices and not both
integers, and the result has few enough values. `bool?`: op gives 1 or 0
for true or false."
(define combine-cases (subr rf-st ((subr rf-st (int int) int) bool rf-value rf-value) (sumof (none unit) (some rf-value)))
  (lambda (op bool? a b)
    (if (not (or (rf-term? a) (rf-term? b))) (sum none #u)
        ;; shakedown's (let ((as …) (bs …)) …): bs first.
        (let* ((bs (integer-cases b))
               (as (integer-cases a)))
          (tagcase as
            (none u (sum none #u))
            (some xs
              (tagcase bs
                (none u (sum none #u))
                (some ys
                  (let ((pairs (the cases
                                 (apply-append
                                  (map (lambda ((x a-case))
                                         (map (lambda ((y a-case))
                                                (product (value (op (extract x value) (extract y value)))
                                                         (cond (t-and (extract x cond) (extract y cond)))))
                                              ys))
                                       xs)))))
                    (letrec ((loop (subr rf-st (cases maybe-cases) (sumof (none unit) (some rf-value)))
                               (lambda (pairs acc)
                                 (tagcase acc
                                   (none u (sum none #u))
                                   (some cs
                                     (if (null? pairs)
                                         (let ((cs (filter-cases cs)))
                                           (if (pair? cs)
                                               (sum some (from-cases cs (lambda ((v int)) (if bool? (rf-bool (= v 1)) (rf-int v)))))
                                               (sum none #u)))
                                         (loop (cdr pairs) (add-cases cs (list (car pairs))))))))))
                      (loop pairs (sum some (the cases nil)))))))))))))
(define apply-append (subr rf-st ((listof cases acyclic)) cases)
  (lambda (ls) (if (null? ls) nil (append (car ls) (apply-append (cdr ls))))))
(define filter-cases (subr rf-st (cases) cases)
  (lambda (cs) (cond ((null? cs) nil)
                     ((rf-false? (extract (car cs) cond)) (filter-cases (cdr cs)))
                     (else (cons (car cs) (filter-cases (cdr cs)))))))

"SMT-LIB's div and mod: a = b*q + r with 0 <= r < |b|. Of choices of
integers, the choice of each case's."
(define int-mod (subr rf-st (int int) int) (lambda (a b) (modulo a (iabs b))))
(define int-div (subr rf-st (int int) int) (lambda (a b) (quotient (- a (modulo a (iabs b))) b)))
"Whether a choice of integers has 0 among its cases."
(define contains-zero? (subr rf-st (rf-value) bool)
  (lambda (b) (tagcase (integer-cases b) (some cs (tagcase (find-case 0 cs) (some k #t) (none u #f))) (none u #f))))

(define t-div (subr rf-st (rf-value rf-value) rf-value)
  (lambda (a b)
    (cond ((and (rf-exact-integer? a) (rf-exact-integer? b)) (rf-int (int-div (rf-int-of a) (rf-int-of b))))
          (else (tagcase (if (and (not (rf-eqv? b (rf-int 0))) (not (contains-zero? b))) (combine-cases int-div #f a b) (sum none #u))
                  (some v v)
                  (none u (mk op-div sort-int (list a b))))))))
(define t-mod (subr rf-st (rf-value rf-value) rf-value)
  (lambda (a b)
    (cond ((and (rf-exact-integer? a) (rf-exact-integer? b)) (rf-int (int-mod (rf-int-of a) (rf-int-of b))))
          (else (tagcase (if (and (not (rf-eqv? b (rf-int 0))) (not (contains-zero? b))) (combine-cases int-mod #f a b) (sum none #u))
                  (some v v)
                  (none u (mk op-mod sort-int (list a b))))))))
(define t-abs (subr rf-st (rf-value) rf-value)
  (lambda (a)
    (cond ((rf-exact-integer? a) (rf-int (iabs (rf-int-of a))))
          ((op? op-abs a) a)
          (else (tagcase (combine-cases (lambda ((x int) (y int)) (iabs x)) #f a (rf-int 0))
                  (some v v)
                  (none u (mk op-abs sort-int (list a))))))))

;;; ------------------------------------------------------------ inspecting terms

"The constants in some terms, in order of creation."
(define term-constants (subr rf-st (rf-vals) rf-vals)
  (lambda (xs)
    (let ((seen (new-seen)) (found (the (ref rf-vals @rf) (new nil))))
      (letrec ((walk (subr rf-st (rf-value) unit)
                 (lambda (t)
                   (if (and (rf-term? t) (not (seen? seen t)))
                       (begin (see! seen t)
                              (if (constant? t)
                                  (set found (cons t (get found)))
                                  (for-each walk (targs t))))
                       #u))))
        (begin (for-each walk xs)
               (sort-by-id (get found)))))))
(define sort-by-id (subr rf-st (rf-vals) rf-vals)
  (lambda (ts)
    (let ((n (list-length ts)))
      (if (< n 2) ts
          (let ((half (quotient n 2)))
            (merge-by-id (sort-by-id (vals-head ts half)) (sort-by-id (vals-tail ts half))))))))
(define merge-by-id (subr rf-st (rf-vals rf-vals) rf-vals)
  (lambda (a b)
    (cond ((null? a) b) ((null? b) a)
          ((< (tid (car b)) (tid (car a))) (cons (car b) (merge-by-id a (cdr b))))
          (else (cons (car a) (merge-by-id (cdr a) b))))))

"The value of term t (or a concrete value) where each constant k has the
value (value-of k); memo, a table of the values of terms found so far."
(define-type term-memo (by-id rf-value))
(define new-term-memo (subr rf-st () term-memo) (lambda () (the term-memo (make-table id-hash id-same?))))
(define term-value (subr rf-st (rf-value (subr rf-st (rf-value) rf-value) term-memo) rf-value)
  (lambda (t value-of memo)
    (letrec ((walk (subr rf-st (rf-value) rf-value)
               (lambda (t)
                 (cond ((not (rf-term? t)) t)
                       ((constant? t) (value-of t))
                       ((table-has? memo (tid t)) (table-ref memo (tid t) rf-false))
                       (else
                        (let ((v (apply-op (term-op (term-of t)) (map walk (targs t)))))
                          (begin (table-set! memo (tid t) v) v)))))))
      (walk t))))
(define all-true? (subr rf-st (rf-vals) bool) (lambda (l) (or (null? l) (and (not (rf-false? (car l))) (all-true? (cdr l))))))
(define any-true? (subr rf-st (rf-vals) bool) (lambda (l) (and (pair? l) (or (not (rf-false? (car l))) (any-true? (cdr l))))))
(define ints-fold (subr rf-st ((subr rf-st (int int) int) int rf-vals) int)
  (lambda (f acc l) (if (null? l) acc (ints-fold f (f acc (rf-int-of (car l))) (cdr l)))))
(define apply-op (subr rf-st (int rf-vals) rf-value)
  (lambda (op args)
    (let ((a (vals-ref args 0)) (b (vals-ref args 1)))
      (cond ((= op op-not) (rf-bool (rf-false? a)))
            ((= op op-and) (rf-bool (all-true? args)))
            ((= op op-or) (rf-bool (any-true? args)))
            ((= op op-ite) (if (rf-false? a) (vals-ref args 2) b))
            ((= op op-eq) (rf-bool (rf-eqv? a b)))
            ((= op op-lt) (rf-bool (< (rf-int-of a) (rf-int-of b))))
            ((= op op-le) (rf-bool (<= (rf-int-of a) (rf-int-of b))))
            ((= op op-add) (rf-int (ints-fold (lambda ((x int) (y int)) (+ x y)) 0 args)))
            ((= op op-sub) (if (null? (cdr args)) (rf-int (- 0 (rf-int-of a)))
                               (rf-int (ints-fold (lambda ((x int) (y int)) (- x y)) (rf-int-of a) (cdr args)))))
            ((= op op-mul) (rf-int (ints-fold (lambda ((x int) (y int)) (* x y)) 1 args)))
            ;; SMT-LIB leaves a divisor of 0 to the model: any value will do.
            ((= op op-div) (if (= (rf-int-of b) 0) (rf-int 0) (t-div a b)))
            ((= op op-mod) (if (= (rf-int-of b) 0) (rf-int 0) (t-mod a b)))
            (else (rf-int (iabs (rf-int-of a))))))))

"A term as a datum, for people: constants as (name-of k), ite as if."
(define term->datum (subr rf-st (rf-value (subr rf-st (rf-value) rf-value)) rf-value)
  (lambda (t name-of)
    (cond ((not (rf-term? t)) t)
          ((constant? t) (name-of t))
          (else
           (let ((op (term-op (term-of t))))
             (rf-cons (rf-sym (if (= op op-ite) 'if (string->symbol (op-name op))))
                      (rf-list (map (lambda ((a rf-value)) (term->datum a name-of)) (targs t)))))))))
