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

;; Macros: each file defines its own, for now (docs/macros.md).
(define-syntax loop
  (syntax-rules ()
    ((_ go eff ((x t i) ...) r body) (letrec ((go (subr eff (t ...) r) (lambda (x ...) body))) (go i ...)))))

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
      (loop go cb-eff ((i int 0)) matrix
        (if (>= i (array-length v)) (product (arity k) (cells v))
            (begin (array-set! v i (f i)) (go (+ i 1))))))))

"Cell by cell."
(define* m-map2 (subr cb-eff (matrix matrix (subr cb-eff (int int) int)) matrix)
  (lambda (a b f)
    (let* ((s (m-size a)) (v (the ivec (make-array s c-false))))
      (loop go cb-eff ((i int 0)) matrix
        (if (>= i s) (product (arity (m-arity a)) (cells v))
            (begin (array-set! v i (f (m-ref a i) (m-ref b i))) (go (+ i 1))))))))

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
    (loop go cb-eff ((r matrix a) (len int 1)) matrix
      (if (>= len n) r (go (m-union c r (m-join c n r r)) (* len 2))))))
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
                               (c-or c (loop go cb-eff ((j int 0) (acc ints nil)) ints
                                         (if (>= j rest) acc (go (+ j 1) (cons (m-ref s (+ (* x rest) j)) acc)))))))))
      (m-build n k (lambda ((i int)) (c-or2 c (m-ref s i) (c-and2 c (m-ref r i) (c-not (m-ref dom (quotient i rest))))))))))

;;; ------------------------------------------------------------ formulas

"Every cell's circuit."
(define* m-cells (subr cb-eff (matrix) ints)
  (lambda (m) (loop go cb-eff ((i int (- (m-size m) 1)) (acc ints nil)) ints
                (if (< i 0) acc (go (- i 1) (let ((x (m-ref m i))) (if (= x c-false) acc (cons x acc))))))))

(define* m-subset (subr cb-eff (circuit matrix matrix) int)
  (lambda (c a b)
    (c-and c (loop go cb-eff ((i int 0) (acc ints nil)) ints
               (if (>= i (m-size a)) acc
                   (go (+ i 1) (let ((x (m-ref a i))) (if (= x c-false) acc (cons (c-implies c x (m-ref b i)) acc)))))))))
(define* m-equal (subr cb-eff (circuit matrix matrix) int)
  (lambda (c a b) (c-and2 c (m-subset c a b) (m-subset c b a))))
(define* m-some (subr cb-eff (circuit matrix) int) (lambda (c a) (c-or c (m-cells a))))
(define* m-no (subr cb-eff (circuit matrix) int) (lambda (c a) (c-not (m-some c a))))
(define* m-lone (subr cb-eff (circuit matrix) int) (lambda (c a) (c-at-most-one c (m-cells a))))
(define* m-one (subr cb-eff (circuit matrix) int) (lambda (c a) (c-exactly-one c (m-cells a))))

;;; ------------------------------------------------------------ integers

"An integer, exact: its bits, least significant first, two's complement,
the last the sign. Each operation's result is as wide as its value
needs, so nothing wraps and nothing overflows; `i-wrap` is the one
operation that wraps, and only when asked."
(define-type bits ints)

(define* repeat (subr spin (int int) ints) (lambda (x k) (if (<= k 0) nil (cons x (repeat x (- k 1))))))
(define* i-width (subr spin (bits) int) (lambda (a) (list-length a)))
(define* i-sign (subr spin (bits) int) (lambda (a) (if (null? (cdr a)) (car a) (i-sign (cdr a)))))
"The bits of the constant `k`, as few as hold it."
(define* i-const (subr spin (int) bits)
  (lambda (k) (if (or (= k 0) (= k -1)) (list (if (= k 0) c-false c-true))
                  (cons (if (= (modulo k 2) 0) c-false c-true) (i-const (quotient (- k (modulo k 2)) 2))))))
"`a` sign-extended to `w` bits, at least its width."
(define* i-ext (subr spin (bits int) bits)
  (lambda (a w) (append a (repeat (i-sign a) (- w (i-width a))))))
"`a` without sign bits that repeat the one below (the same circuit)."
(define* i-trim (subr spin (bits) bits)
  (lambda (a) (let ((r (reverse a)))
                (if (and (pair? (cdr r)) (= (car r) (car (cdr r)))) (i-trim (reverse (cdr r))) a))))
(define* take-bits (subr spin (bits int) bits)
  (lambda (a w) (if (or (<= w 0) (null? a)) nil (cons (car a) (take-bits (cdr a) (- w 1))))))
(define* not-bits (subr spin (bits) bits) (lambda (a) (if (null? a) nil (cons (c-not (car a)) (not-bits (cdr a))))))

"a + b + cin, of the same width w: the sum mod 2^w (a ripple of full adders)."
(define* add-bits (subr cb-eff (circuit bits bits int) bits)
  (lambda (c a b cin)
    (if (null? a) nil
        (let ((x (car a)) (y (car b)))
          (cons (c-iff c (c-iff c x y) cin)                      ; x xor y xor cin
                (add-bits c (cdr a) (cdr b) (c-or2 c (c-and2 c x y) (c-and2 c cin (c-or2 c x y)))))))))

(define* i-add (subr cb-eff (circuit bits bits) bits)
  (lambda (c a b) (let ((w (+ 1 (max (i-width a) (i-width b)))))
                    (i-trim (add-bits c (i-ext a w) (i-ext b w) c-false)))))
(define* i-sub (subr cb-eff (circuit bits bits) bits)
  (lambda (c a b) (let ((w (+ 1 (max (i-width a) (i-width b)))))
                    (i-trim (add-bits c (i-ext a w) (not-bits (i-ext b w)) c-true)))))
(define* i-neg (subr cb-eff (circuit bits) bits) (lambda (c a) (i-sub c (i-const 0) a)))
"a·b: both sign-extended to the width of the product, which holds it."
(define* i-mul (subr cb-eff (circuit bits bits) bits)
  (lambda (c a b)
    (let* ((w (+ (i-width a) (i-width b))) (x (i-ext a w)))
      (letrec ((and-all (subr cb-eff (bits int) bits)
                 (lambda (l y) (if (null? l) nil (cons (c-and2 c (car l) y) (and-all (cdr l) y)))))
               (go (subr cb-eff (bits int bits) bits)        ; acc + Σ y_i·(x << i), mod 2^w
                 (lambda (ys i acc)
                   (if (null? ys) acc
                       (go (cdr ys) (+ i 1)
                           (add-bits c acc (take-bits (append (repeat c-false i) (and-all x (car ys))) w) c-false))))))
        (i-trim (go (i-ext b w) 0 (repeat c-false w)))))))
"a < b: the sign of a - b, exact."
(define* i-lt (subr cb-eff (circuit bits bits) int)
  (lambda (c a b) (let ((w (+ 1 (max (i-width a) (i-width b)))))
                    (i-sign (add-bits c (i-ext a w) (not-bits (i-ext b w)) c-true)))))
(define* i-eq (subr cb-eff (circuit bits bits) int)
  (lambda (c a b)
    (let ((w (max (i-width a) (i-width b))))
      (c-and c (loop go cb-eff ((x bits (i-ext a w)) (y bits (i-ext b w))) ints
                 (if (null? x) nil (cons (c-iff c (car x) (car y)) (go (cdr x) (cdr y)))))))))
"`i` ? a : b, bit by bit."
(define* i-ite (subr cb-eff (circuit int bits bits) bits)
  (lambda (c i a b)
    (let ((w (max (i-width a) (i-width b))))
      (i-trim (loop go cb-eff ((x bits (i-ext a w)) (y bits (i-ext b w))) bits
                (if (null? x) nil (cons (c-ite c i (car x) (car y)) (go (cdr x) (cdr y)))))))))
"The sum of integers, added in pairs."
(define* i-sum (subr cb-eff (circuit (listof bits acyclic)) bits)
  (lambda (c l)
    (cond ((null? l) (i-const 0))
          ((null? (cdr l)) (car l))
          (else (i-sum c (loop pairs cb-eff ((l (listof bits acyclic) l)) (listof bits acyclic)
                           (cond ((null? l) nil) ((null? (cdr l)) l)
                                 (else (cons (i-add c (car l) (car (cdr l))) (pairs (cdr (cdr l))))))))))))
"`a` wrapped to `w` bits: its value mod 2^w, as a `w`-bit two's complement."
(define* i-wrap (subr spin (bits int) bits)
  (lambda (a w) (i-trim (take-bits (i-ext a w) w))))
"|a|: nonnegative."
(define* i-abs (subr cb-eff (circuit bits) bits) (lambda (c a) (i-ite c (i-sign a) (i-neg c a) a)))
"a / b, truncated toward zero, and its remainder, of a's sign (as Alloy's
and Java's): by restoring division of the magnitudes. For b = 0 the
result is not said (the caller says it)."
(define-type quot-rem (productof (q bits) (r bits)))
(define* i-divrem (subr cb-eff (circuit bits bits) quot-rem)
  (lambda (c a b)
    (let* ((ua (i-abs c a)) (ub (i-abs c b))
           (w (+ 2 (max (i-width ua) (i-width ub))))
           (d (not-bits (i-ext ub w))))
      (letrec ((go (subr cb-eff (bits bits bits) quot-rem)    ; n's bits, most significant first
                 (lambda (ns r q)
                   (if (null? ns) (product (q (i-trim (append q (list c-false)))) (r (i-trim r)))
                       (let* ((r2 (cons (car ns) (take-bits r (- w 1))))       ; r·2 + n_i
                              (t (add-bits c r2 d c-true))                     ; r2 - |b|
                              (ge (c-not (i-sign t))))
                         (go (cdr ns)
                             (loop pick cb-eff ((x bits t) (y bits r2)) bits
                               (if (null? x) nil (cons (c-ite c ge (car x) (car y)) (pick (cdr x) (cdr y)))))
                             (cons ge q)))))))
        (let ((qr (go (reverse ua) (repeat c-false w) nil)))
          (product (q (i-ite c (c-not (c-iff c (i-sign a) (i-sign b))) (i-neg c (extract qr q)) (extract qr q)))
                   (r (i-ite c (i-sign a) (i-neg c (extract qr r)) (extract qr r)))))))))

"How many of `a`'s tuples there are."
(define* m-count (subr cb-eff (circuit matrix) bits)
  (lambda (c a) (i-sum c (loop go cb-eff ((l ints (m-cells a))) (listof bits acyclic)
                           (if (null? l) nil (cons (list (car l) c-false) (go (cdr l))))))))
