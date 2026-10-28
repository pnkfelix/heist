;;; term.fx: terms, hash-consed, and built by constructors that simplify
;;; (lockpick's `(lockpick term)`).
;;;
;;; A term is an int, its id, from 0: equal terms are one id, and later
;;; layers index their tables by it. What the term is, the store keeps: its
;;; operator (SMT-LIB's name where there is one), parameters (ints: a
;;; variable's serial number, a constant's value, extract's indices; a
;;; rational is two, numerator and denominator), a name (a variable's),
;;; arguments (terms) and sort. The store is the module's own state, and
;;; never shrinks: terms live as long as the process.
;;;
;;; Sorts are ints: Bool -1, Int -2, Real -3, and (_ BitVec n) n.

(module-parameters ((m-sat (load-moduleof "sat.fx")) (m-rat (load-moduleof "rat.fx"))))

(define bool-sort int -1)
(define int-sort int -2)
(define real-sort int -3)
(define* bv-sort (subr pure (int) int) (lambda (n) n))
(define* bv-sort? (subr pure (int) bool) (lambda (s) (> s 0)))
(define* bv-sort-width (subr pure (int) int) (lambda (s) s))
(define* sort-bool? (subr pure (int) bool) (lambda (s) (= s -1)))
(define* arith-sort? (subr pure (int) bool) (lambda (s) (or (= s -2) (= s -3))))
(define* sort->string (subr pure (int) string)
  (lambda (s) (cond ((= s -1) "Bool") ((= s -2) "Int") ((= s -3) "Real")
                    (else (string-append "(_ BitVec " (string-append (int->string s) ")"))))))

;;; ------------------------------------------------------------ the store

(define-type term-info (productof (op string) (params ints) (name string) (args ints) (sort int) (hash int)))
(define no-info term-info (product (op "") (params nil) (name "") (args nil) (sort 0) (hash 0)))

(hide
  (define infos (ref (arrayof term-info @cb) @cb) (new (the (arrayof term-info @cb) (make-array 1024 no-info))))
  (define count (ref int @cb) (new 0))
  ;; Open hashing: each bucket's first term, and each term's next in its bucket (-1: none).
  (define buckets (ref ivec @cb) (new (the ivec (make-array 1024 -1))))
  (define chain (ref ivec @cb) (new (the ivec (make-array 1024 -1))))
  (define var-serial (ref int @cb) (new 0)))

(define* info (subr (read @cb) (int) term-info) (lambda (t) (array-ref (get infos) t)))
(define* term-op (subr (read @cb) (int) string) (lambda (t) (extract (info t) op)))
(define* term-params (subr (read @cb) (int) ints) (lambda (t) (extract (info t) params)))
(define* term-args (subr (read @cb) (int) ints) (lambda (t) (extract (info t) args)))
(define* term-sort (subr (read @cb) (int) int) (lambda (t) (extract (info t) sort)))
(define* term-name (subr (read @cb) (int) string) (lambda (t) (extract (info t) name)))
(define* term-arg0 (subr (read @cb) (int) int) (lambda (t) (car (term-args t))))
(define* term-arg1 (subr (read @cb) (int) int) (lambda (t) (car (cdr (term-args t)))))
(define* term-arg2 (subr (read @cb) (int) int) (lambda (t) (car (cdr (cdr (term-args t))))))
(define* term-param0 (subr (read @cb) (int) int) (lambda (t) (car (term-params t))))
(define* term-param1 (subr (read @cb) (int) int) (lambda (t) (car (cdr (term-params t)))))
(define* term-bool? (subr (read @cb) (int) bool) (lambda (t) (= (term-sort t) -1)))
(define* term-op? (subr (read @cb) (int string) bool) (lambda (t op) (string=? (term-op t) op)))
"The number of terms made so far: every term is below it."
(define* term-count (subr (read @cb) () int) (lambda () (get count)))

(define* ints=? (subr spin (ints ints) bool)
  (lambda (a b) (if (null? a) (null? b) (and (pair? b) (= (car a) (car b)) (ints=? (cdr a) (cdr b))))))
(define* mix (subr pure (int int) int) (lambda (h x) (bitwise-and (+ (* h 31) x) 281474976710655)))
(define* mix-ints (subr spin (int ints) int) (lambda (h l) (if (null? l) h (mix-ints (mix h (bitwise-and (car l) 1099511627775)) (cdr l)))))

(define* rehash! (subr cb-eff (int) unit)
  (lambda (n)
    (let ((b (the ivec (make-array n -1))) (c (get chain)) (m (get count)) (is (get infos)))
      (letrec ((go (subr cb-eff (int) unit)
                 (lambda (t) (if (>= t m) #u
                                 (let ((i (modulo (extract (array-ref is t) hash) n)))
                                   (begin (array-set! c t (array-ref b i)) (array-set! b i t) (go (+ t 1))))))))
        (begin (go 0) (set buckets b))))))

"The term of this operator, parameters, name, arguments and sort, made if
there is none yet. The sort is of the key: the constant 2 of sort Int and
that of sort Real are two terms."
(define* make-app* (subr cb-eff (string ints string ints int) int)
  (lambda (op params name args sort)
    (let* ((h (mix-ints (mix-ints (mix (string-hash op) (+ sort 8)) params) args))
           (b (get buckets)) (i (modulo h (array-length b))))
      (letrec ((find (subr cb-eff (int) int)
                 (lambda (t)
                   (cond ((< t 0) -1)
                         ((let ((x (info t)))
                            (and (= (extract x hash) h) (= (extract x sort) sort) (string=? (extract x op) op)
                                 (ints=? (extract x params) params) (ints=? (extract x args) args)))
                          t)
                         (else (find (array-ref (get chain) t)))))))
        (let ((found (find (array-ref b i))))
          (if (>= found 0) found
              (let ((t (get count)))
                (begin
                  (if (>= t (array-length (get infos)))
                      (let ((n (* 2 (array-length (get infos)))) (old (get infos)))
                        (let ((w (the (arrayof term-info @cb) (make-array n no-info))))
                          (letrec ((copy (subr cb-eff (int) unit) (lambda (k) (if (>= k t) #u (begin (array-set! w k (array-ref old k)) (copy (+ k 1)))))))
                            (begin (copy 0) (set infos w) (set chain (ivec-grow (get chain) n -1))))))
                      #u)
                  (array-set! (get infos) t (product (op op) (params params) (name name) (args args) (sort sort) (hash h)))
                  (array-set! (get chain) t (array-ref (get buckets) i))
                  (array-set! (get buckets) i t)
                  (set count (+ t 1))
                  (if (> (+ t 1) (array-length (get buckets))) (rehash! (* 2 (array-length (get buckets)))) #u)
                  t))))))))
(define* make-app (subr cb-eff (string ints ints int) int)
  (lambda (op params args sort) (make-app* op params "" args sort)))

"A variable (a declared constant). Each declaration makes a new one, even
of a name declared before (after a pop, say): the serial number tells
them apart."
(define* make-var (subr cb-eff (string int) int)
  (lambda (name sort) (begin (set var-serial (+ (get var-serial) 1)) (make-app* "var" (list (get var-serial)) name nil sort))))
(define* var-term? (subr (read @cb) (int) bool) (lambda (t) (term-op? t "var")))
(define* var-name (subr (read @cb) (int) string) (lambda (t) (term-name t)))

;;; ------------------------------------------------------------ lists of terms

"`l` sorted (a merge sort, stable), duplicates kept."
(define* sort-ints (subr spin (ints) ints)
  (lambda (l)
    (letrec ((split (subr spin (ints ints ints) (productof (a ints) (b ints)))
               (lambda (l a b) (if (null? l) (product (a a) (b b)) (split (cdr l) b (cons (car l) a)))))
             (merge (subr spin (ints ints) ints)
               (lambda (a b) (cond ((null? a) b) ((null? b) a)
                                   ((<= (car a) (car b)) (cons (car a) (merge (cdr a) b)))
                                   (else (cons (car b) (merge a (cdr b))))))))
      (if (or (null? l) (null? (cdr l))) l
          (let ((p (split l nil nil))) (merge (sort-ints (extract p a)) (sort-ints (extract p b))))))))
"Terms sorted by id, without duplicates."
(define* list-sort-terms (subr spin (ints) ints)
  (lambda (l)
    (letrec ((dedup (subr spin (ints) ints)
               (lambda (l) (cond ((or (null? l) (null? (cdr l))) l)
                                 ((= (car l) (car (cdr l))) (dedup (cdr l)))
                                 (else (cons (car l) (dedup (cdr l))))))))
      (dedup (sort-ints l)))))
(define* memv? (subr spin (int ints) bool) (lambda (x l) (and (pair? l) (or (= x (car l)) (memv? x (cdr l))))))
(define* filter-ints (subr cb-eff ((subr cb-eff (int) bool) ints) ints)
  (lambda (p l) (cond ((null? l) nil) ((p (car l)) (cons (car l) (filter-ints p (cdr l)))) (else (filter-ints p (cdr l))))))
(define* map-ints (subr cb-eff ((subr cb-eff (int) int) ints) ints)
  (lambda (f l) (if (null? l) nil (let ((x (f (car l)))) (cons x (map-ints f (cdr l)))))))
(define* append-ints (subr spin (ints ints) ints)
  (lambda (a b) (if (null? a) b (cons (car a) (append-ints (cdr a) b)))))

;;; ------------------------------------------------------------ Boolean terms

"True and false, the first terms made (ids 0 and 1, as lockpick's)."
(define true-id int (make-app "true" nil nil -1))
(define false-id int (make-app "false" nil nil -1))
(define* true-term (subr pure () int) (lambda () 0))
(define* false-term (subr pure () int) (lambda () 1))
(define* bool-term (subr cb-eff (bool) int) (lambda (b) (if b (true-term) (false-term))))
(define* true-term? (subr cb-eff (int) bool) (lambda (t) (= t (true-term))))
(define* false-term? (subr cb-eff (int) bool) (lambda (t) (= t (false-term))))
(define* not-term? (subr (read @cb) (int) bool) (lambda (t) (term-op? t "not")))

(define* mk-not (subr cb-eff (int) int)
  (lambda (t)
    (cond ((true-term? t) (false-term))
          ((false-term? t) (true-term))
          ((not-term? t) (term-arg0 t))
          (else (make-app "not" nil (list t) -1)))))

"The arguments of an n-ary and (op \"and\", unit true, zero false) or or
(the reverse), flattened, without units and duplicates; or (zero?) they
hold zero, or a term and its negation."
(define-type junction (productof (zero bool) (args ints)))
(define* junction-args (subr cb-eff (string int int ints) junction)
  (lambda (op unit zero ts)
    (let ((flat (letrec ((go (subr cb-eff (ints ints) ints)
                           (lambda (ts acc)
                             (cond ((null? ts) acc)
                                   ((term-op? (car ts) op) (go (cdr ts) (go (term-args (car ts)) acc)))
                                   (else (go (cdr ts) (cons (car ts) acc)))))))
                  (go ts nil))))
      (if (memv? zero flat) (product (zero #t) (args nil))
          (let ((args (list-sort-terms (filter-ints (lambda ((t int)) (not (= t unit))) flat))))
            ;; t and (not t): look for each not's argument among the others.
            (if (letrec ((go (subr cb-eff (ints) bool)
                           (lambda (as) (and (pair? as) (or (and (not-term? (car as)) (memv? (term-arg0 (car as)) args)) (go (cdr as)))))))
                  (go args))
                (product (zero #t) (args nil))
                (product (zero #f) (args args))))))))
(define* mk-junction (subr cb-eff (string int int ints) int)
  (lambda (op unit zero ts)
    (let ((j (junction-args op unit zero ts)))
      (cond ((extract j zero) zero)
            ((null? (extract j args)) unit)
            ((null? (cdr (extract j args))) (car (extract j args)))
            (else (make-app op nil (extract j args) -1))))))
(define* mk-and (subr cb-eff (ints) int) (lambda (ts) (mk-junction "and" (true-term) (false-term) ts)))
(define* mk-or (subr cb-eff (ints) int) (lambda (ts) (mk-junction "or" (false-term) (true-term) ts)))
(define* mk-and2 (subr cb-eff (int int) int) (lambda (a b) (mk-and (list a b))))
(define* mk-or2 (subr cb-eff (int int) int) (lambda (a b) (mk-or (list a b))))
(define* mk-implies (subr cb-eff (int int) int) (lambda (a b) (mk-or2 (mk-not a) b)))

"Boolean equality (iff), as (= a b). Negations are pulled out, so that
(= (not a) b) and (not (= a b)) are one term."
(define* mk-iff (subr cb-eff (int int) int)
  (lambda (a b)
    (cond ((= a b) (true-term))
          ((true-term? a) b)
          ((true-term? b) a)
          ((false-term? a) (mk-not b))
          ((false-term? b) (mk-not a))
          ((not-term? a) (mk-not (mk-iff (term-arg0 a) b)))
          ((not-term? b) (mk-not (mk-iff a (term-arg0 b))))
          ((> a b) (mk-iff b a))
          (else (make-app "=" nil (list a b) -1)))))
(define* mk-xor (subr cb-eff (int int) int) (lambda (a b) (mk-not (mk-iff a b))))

"A constant of a theory: a bitvector or a number."
(define* constant-term? (subr (read @cb) (int) bool) (lambda (t) (or (term-op? t "bv") (term-op? t "num"))))

"Equality of two terms of one sort (other sorts than Bool come with their
theories)."
(define* mk-eq (subr cb-eff (int int) int)
  (lambda (a b)
    (cond ((sort-bool? (term-sort a)) (mk-iff a b))
          ((= a b) (true-term))
          ;; Distinct constants (hash-consing makes equal ones one term).
          ((and (constant-term? a) (constant-term? b)) (false-term))
          ((> a b) (mk-eq b a))
          (else (make-app "=" nil (list a b) -1)))))

(define* mk-distinct (subr cb-eff (ints) int)
  (lambda (ts)
    (letrec ((go (subr cb-eff (ints ints) int)
               (lambda (ts acc)
                 (if (null? ts) (mk-and acc)
                     (go (cdr ts) (append-ints (map-ints (lambda ((u int)) (mk-not (mk-eq (car ts) u))) (cdr ts)) acc))))))
      (go ts nil))))

"Cardinality: (card lo hi) of Boolean terms holds when at least lo and at
most hi of them are true (hi `no-bound` for none). The terms are a multiset:
one given twice counts twice. True ones go into the bounds, false ones
go, and a term with its negation counts one; what reduces to and, or, a
constant, or the negation of an and is that."
"No upper bound, for `mk-card`."
(define no-bound int -4611686018427387904)
(define* mk-card (subr cb-eff (int int ints) int)
  (lambda (lo hi ts)
    (letrec ((go (subr cb-eff (ints int int ints) int)
               (lambda (ts lo hi acc)
                 (cond ((null? ts)
                        (letrec ((rm (subr cb-eff (ints ints int) int)
                                   ;; acc without pairs of a term and its negation, and their number.
                                   (lambda (ts acc pairs)
                                     (if (null? ts)
                                         (card-of (- lo pairs) (if (= hi no-bound) no-bound (- hi pairs)) (sort-ints acc))
                                         (let ((u (mk-not (car ts))))
                                           (if (memv? u (cdr ts)) (rm (remv-once u (cdr ts)) acc (+ pairs 1))
                                               (rm (cdr ts) (cons (car ts) acc) pairs)))))))
                          (rm acc nil 0)))
                       ((true-term? (car ts)) (go (cdr ts) (- lo 1) (if (= hi no-bound) no-bound (- hi 1)) acc))
                       ((false-term? (car ts)) (go (cdr ts) lo hi acc))
                       (else (go (cdr ts) lo hi (cons (car ts) acc)))))))
      (go ts lo hi nil))))
(define* card-of (subr cb-eff (int int ints) int)
  (lambda (lo hi ts)
    (let* ((n (list-length ts)) (lo (max lo 0)) (hi (if (and (not (= hi no-bound)) (< hi n)) hi no-bound)) (none (= hi no-bound)))
      (cond ((or (> lo n) (and (not none) (< hi lo))) (false-term))
            ((and (= lo 0) none) (true-term))
            ((and none (= lo n)) (mk-and ts))
            ((and none (= lo 1)) (mk-or ts))
            ((= hi 0) (mk-and (map-ints mk-not ts)))
            ((and (= lo 0) (= hi (- n 1))) (mk-not (mk-and ts)))
            (else (make-app "card" (list lo hi) ts -1))))))
(define* mk-at-least (subr cb-eff (int ints) int) (lambda (k ts) (mk-card k no-bound ts)))
(define* mk-at-most (subr cb-eff (int ints) int) (lambda (k ts) (mk-card 0 k ts)))
(define* mk-exactly (subr cb-eff (int ints) int) (lambda (k ts) (mk-card k k ts)))

(define* mk-ite (subr cb-eff (int int int) int)
  (lambda (c a b)
    (cond ((true-term? c) a)
          ((false-term? c) b)
          ((= a b) a)
          ((not-term? c) (mk-ite (term-arg0 c) b a))
          ((sort-bool? (term-sort a))
           (cond ((true-term? a) (mk-or2 c b))
                 ((false-term? a) (mk-and2 (mk-not c) b))
                 ((true-term? b) (mk-or2 (mk-not c) a))
                 ((false-term? b) (mk-and2 c a))
                 ((= c a) (mk-or2 c b))
                 ((= c b) (mk-and2 c a))
                 (else (make-app "ite" nil (list c a b) -1))))
          (else (make-app "ite" nil (list c a b) (term-sort a))))))
