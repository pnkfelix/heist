;;; matrix.fx: relations over a universe of atoms, as matrices of circuits
;;; (Kodkod's `BooleanMatrix`, dense).
;;;
;;; The universe is atoms 0 … n-1. A tuple of arity k is an int, its atoms
;;; as digits base n, the first most significant: (a b) is a·n + b. A
;;; matrix of arity k has n^k cells, each the circuit (an id of
;;; circuit.fx) that says whether that tuple is in the relation. A matrix
;;; is not changed once made.

(module-parameters ((m-sat (load-moduleof "../combo/sat.fx"))
                    (m-circuit (load-moduleof "circuit.fx" m-sat))))

(define-type matrix (productof (arity int) (cells ivec)))

(define* power (subr spin (int int) int) (lambda (n k) (if (<= k 0) 1 (* n (power n (- k 1))))))
(define* m-size (subr (read @cb) (matrix) int) (lambda (m) (array-length (extract m cells))))
(define* m-arity (subr pure (matrix) int) (lambda (m) (extract m arity)))
(define* m-ref (subr (read @cb) (matrix int) int) (lambda (m i) (array-ref (extract m cells) i)))

"A matrix of arity `k` over `n` atoms, every cell `x`."
(define* m-fill (subr cb-eff (int int int) matrix)
  (lambda (n k x) (product (arity k) (cells (the ivec (make-array (power n k) x))))))

"A matrix whose cell i is `(f i)`."
(define* m-build (subr cb-eff (int int (subr cb-eff (int) int)) matrix)
  (lambda (n k f)
    (let ((v (the ivec (make-array (power n k) c-false))))
      (letrec ((go (subr cb-eff (int) matrix)
                 (lambda (i) (if (>= i (array-length v)) (product (arity k) (cells v))
                                 (begin (array-set! v i (f i)) (go (+ i 1)))))))
        (go 0)))))

"Cell by cell."
(define* m-map2 (subr cb-eff (matrix matrix (subr cb-eff (int int) int)) matrix)
  (lambda (a b f)
    (let* ((s (m-size a)) (v (the ivec (make-array s c-false))))
      (letrec ((go (subr cb-eff (int) matrix)
                 (lambda (i) (if (>= i s) (product (arity (m-arity a)) (cells v))
                                 (begin (array-set! v i (f (m-ref a i) (m-ref b i))) (go (+ i 1)))))))
        (go 0)))))

(define* m-union (subr cb-eff (circuit matrix matrix) matrix)
  (lambda (c a b) (m-map2 a b (lambda ((x int) (y int)) (c-or2 c x y)))))
(define* m-inter (subr cb-eff (circuit matrix matrix) matrix)
  (lambda (c a b) (m-map2 a b (lambda ((x int) (y int)) (c-and2 c x y)))))
(define* m-diff (subr cb-eff (circuit matrix matrix) matrix)
  (lambda (c a b) (m-map2 a b (lambda ((x int) (y int)) (c-and2 c x (c-not y))))))
"Cell by cell, `i` choosing `a`'s or `b`'s."
(define* m-ite (subr cb-eff (circuit int matrix matrix) matrix)
  (lambda (c i a b) (m-map2 a b (lambda ((x int) (y int)) (c-ite c i x y)))))

"The cross product: a tuple of `a`'s then one of `b`'s."
(define* m-product (subr cb-eff (circuit int matrix matrix) matrix)
  (lambda (c n a b)
    (let ((sb (m-size b)))
      (m-build n (+ (m-arity a) (m-arity b))
               (lambda ((i int)) (c-and2 c (m-ref a (quotient i sb)) (m-ref b (modulo i sb))))))))

"The relational join a.b: `a`'s last atom matched with `b`'s first, both
dropped. Arity (+ ka kb -2), at least 1."
(define* m-join (subr cb-eff (circuit int matrix matrix) matrix)
  (lambda (c n a b)
    (let* ((ka (m-arity a)) (kb (m-arity b))
           (rest (power n (- kb 1))))       ; tuples of b's after its first atom
      (m-build n (- (+ ka kb) 2)
               (lambda ((i int))
                 (let ((pre (quotient i rest)) (post (modulo i rest)))
                   (letrec ((terms (subr cb-eff (int ints) ints)
                              (lambda (x acc)
                                (if (>= x n) acc
                                    (let ((p (m-ref a (+ (* pre n) x))))
                                      (terms (+ x 1)
                                             (if (= p c-false) acc
                                                 (let ((q (m-ref b (+ (* x rest) post))))
                                                   (if (= q c-false) acc (cons (c-and2 c p q) acc))))))))))
                     (c-or c (terms 0 nil)))))))))

"A binary relation's transpose."
(define* m-transpose (subr cb-eff (int matrix) matrix)
  (lambda (n a) (m-build n 2 (lambda ((i int)) (m-ref a (+ (* (modulo i n) n) (quotient i n)))))))

"The identity on every atom, and every atom."
(define* m-iden (subr cb-eff (int) matrix)
  (lambda (n) (m-build n 2 (lambda ((i int)) (if (= (quotient i n) (modulo i n)) c-true c-false)))))
(define* m-univ (subr cb-eff (int) matrix) (lambda (n) (m-fill n 1 c-true)))
(define* m-none (subr cb-eff (int int) matrix) (lambda (n k) (m-fill n k c-false)))
"The one tuple `t` (of arity k)."
(define* m-tuple (subr cb-eff (int int int) matrix)
  (lambda (n k t) (m-build n k (lambda ((i int)) (if (= i t) c-true c-false)))))

"Transitive closure, by squaring: r + r.r covers paths of up to 2 steps,
and so on, until paths of n steps."
(define* m-closure (subr cb-eff (circuit int matrix) matrix)
  (lambda (c n a)
    (letrec ((go (subr cb-eff (matrix int) matrix)
               (lambda (r len) (if (>= len n) r (go (m-union c r (m-join c n r r)) (* len 2))))))
      (go a 1))))
(define* m-rclosure (subr cb-eff (circuit int matrix) matrix)
  (lambda (c n a) (m-union c (m-closure c n a) (m-iden n))))

"A tuple's first and last atom."
(define* tuple-first (subr spin (int int int) int) (lambda (n k t) (quotient t (power n (- k 1)))))
(define* tuple-last (subr pure (int int) int) (lambda (n t) (modulo t n)))

"s <: r (s unary): r's tuples whose first atom is in s. r :> s: whose
last is."
(define* m-dom-restrict (subr cb-eff (circuit int matrix matrix) matrix)
  (lambda (c n s r)
    (let ((k (m-arity r)))
      (m-build n k (lambda ((i int)) (c-and2 c (m-ref s (tuple-first n k i)) (m-ref r i)))))))
(define* m-range-restrict (subr cb-eff (circuit int matrix matrix) matrix)
  (lambda (c n r s)
    (m-build n (m-arity r) (lambda ((i int)) (c-and2 c (m-ref s (tuple-last n i)) (m-ref r i))))))

"r ++ s: s, and r's tuples whose first atom no tuple of s's has."
(define* m-override (subr cb-eff (circuit int matrix matrix) matrix)
  (lambda (c n r s)
    (let* ((k (m-arity s)) (rest (power n (- k 1)))
           (dom (m-build n 1 (lambda ((x int))
                               (c-or c (letrec ((go (subr cb-eff (int ints) ints)
                                                  (lambda (j acc) (if (>= j rest) acc (go (+ j 1) (cons (m-ref s (+ (* x rest) j)) acc))))))
                                         (go 0 nil)))))))
      (m-build n k (lambda ((i int)) (c-or2 c (m-ref s i) (c-and2 c (m-ref r i) (c-not (m-ref dom (quotient i rest))))))))))

;;; ------------------------------------------------------------ formulas

"Every cell's circuit."
(define* m-cells (subr cb-eff (matrix) ints)
  (lambda (m) (letrec ((go (subr cb-eff (int ints) ints)
                         (lambda (i acc) (if (< i 0) acc (go (- i 1) (let ((x (m-ref m i))) (if (= x c-false) acc (cons x acc))))))))
                (go (- (m-size m) 1) nil))))

(define* m-subset (subr cb-eff (circuit matrix matrix) int)
  (lambda (c a b)
    (c-and c (letrec ((go (subr cb-eff (int ints) ints)
                        (lambda (i acc) (if (>= i (m-size a)) acc
                                            (go (+ i 1) (let ((x (m-ref a i))) (if (= x c-false) acc (cons (c-implies c x (m-ref b i)) acc))))))))
               (go 0 nil)))))
(define* m-equal (subr cb-eff (circuit matrix matrix) int)
  (lambda (c a b) (c-and2 c (m-subset c a b) (m-subset c b a))))
(define* m-some (subr cb-eff (circuit matrix) int) (lambda (c a) (c-or c (m-cells a))))
(define* m-no (subr cb-eff (circuit matrix) int) (lambda (c a) (c-not (m-some c a))))
(define* m-lone (subr cb-eff (circuit matrix) int) (lambda (c a) (c-at-most-one c (m-cells a))))
(define* m-one (subr cb-eff (circuit matrix) int) (lambda (c a) (c-exactly-one c (m-cells a))))

;;; ------------------------------------------------------------ counts

"A count, unary: element j (from 0) says the count is at least j+1."
(define-type count ints)

"How many of `a`'s tuples there are."
(define* m-count (subr cb-eff (circuit matrix) count)
  (lambda (c a)
    ;; adding bit x to [s1 s2 …]: s'j = sj or (s(j-1) and x), s0 true
    (letrec ((add (subr cb-eff (count int int) count)
               (lambda (s x prev)
                 (if (null? s) (if (= (c-and2 c prev x) c-false) nil (list (c-and2 c prev x)))
                     (cons (c-or2 c (car s) (c-and2 c prev x)) (add (cdr s) x (car s))))))
             (go (subr cb-eff (ints count) count)
               (lambda (bits s) (if (null? bits) s (go (cdr bits) (add s (car bits) c-true))))))
      (go (m-cells a) nil))))

(define* count-const (subr spin (int) count)
  (lambda (k) (if (<= k 0) nil (cons c-true (count-const (- k 1))))))

"Element j of a count, false past its end."
(define* count-at (subr spin (count int) int)
  (lambda (s j) (cond ((null? s) c-false) ((= j 0) (car s)) (else (count-at (cdr s) (- j 1))))))

(define* count-length (subr spin (count) int) (lambda (s) (list-length s)))

"a + b: at least j+1 when a is at least p and b at least j+1-p."
(define* count-add (subr cb-eff (circuit count count) count)
  (lambda (c a b)
    (let ((la (count-length a)) (lb (count-length b)))
      (letrec ((at (subr cb-eff (int) int)
                 (lambda (j)               ; sum >= j+1
                   (c-or c (letrec ((go (subr cb-eff (int ints) ints)
                                      (lambda (p acc)  ; a >= p, b >= j+1-p
                                        (if (> p (+ j 1)) acc
                                            (go (+ p 1)
                                                (cons (c-and2 c (if (= p 0) c-true (count-at a (- p 1)))
                                                              (if (= (- (+ j 1) p) 0) c-true (count-at b (- j p))))
                                                      acc))))))
                             (go 0 nil)))))
               (all (subr cb-eff (int) count)
                 (lambda (j) (if (>= j (+ la lb)) nil (cons (at j) (all (+ j 1)))))))
        (all 0)))))

"a - b, at least 0: at least j+1 when, for some p, a is at least p+j+1
and b at most p."
(define* count-sub (subr cb-eff (circuit count count) count)
  (lambda (c a b)
    (let ((la (count-length a)) (lb (count-length b)))
      (letrec ((at (subr cb-eff (int) int)
                 (lambda (j)
                   (c-or c (letrec ((go (subr cb-eff (int ints) ints)
                                      (lambda (p acc)  ; b = exactly p: b>=p and not b>=p+1
                                        (if (> p lb) acc
                                            (go (+ p 1)
                                                (cons (c-and c (list (if (= p 0) c-true (count-at b (- p 1)))
                                                                     (c-not (count-at b p))
                                                                     (count-at a (+ p j))))
                                                      acc))))))
                             (go 0 nil)))))
               (all (subr cb-eff (int) count)
                 (lambda (j) (if (>= j la) nil (cons (at j) (all (+ j 1)))))))
        (all 0)))))

"a >= b: wherever b is at least j, so is a."
(define* count-ge (subr cb-eff (circuit count count) int)
  (lambda (c a b)
    (c-and c (letrec ((go (subr cb-eff (int count ints) ints)
                        (lambda (j bs acc) (if (null? bs) acc (go (+ j 1) (cdr bs) (cons (c-implies c (car bs) (count-at a j)) acc))))))
               (go 0 b nil)))))
(define* count-eq (subr cb-eff (circuit count count) int)
  (lambda (c a b) (c-and2 c (count-ge c a b) (count-ge c b a))))
