;;; circuit.fx: boolean circuits, hash-consed, and given to combo's SAT
;;; solver by Tseitin's encoding (Kodkod's `kodkod.engine.bool`, in
;;; little: one gate, AND, of any number of inputs).
;;;
;;; A circuit value is an int, its id: `c-true` 1, `c-false` -1, and from
;;; 2 an input or a gate; the negation of x is -x. A gate's inputs are
;;; sorted by id, duplicates gone, and equal gates are one id, so that
;;; translating the same subformula twice costs nothing the second time.
;;; OR is an AND of negations, negated.
;;;
;;; Only what is asserted is encoded, and only once: each node gets a SAT
;;; variable the first time an assertion reaches it.

(module-parameters ((m-sat (load-moduleof "../combo/sat.fx"))))
(hide (define kit-lists (load-module "../kit/lists.fx"))
      (import kit-lists list-sort)
      (define kit-numbers (load-module "../kit/numbers.fx"))
      (import kit-numbers abs))

(define c-true int 1)
(define c-false int -1)

"A circuit's store: each node's kind (0 an input, 1 an AND) and inputs,
the AND gates by hash (open hashing: each bucket's first node, each
node's next), each node's SAT variable once encoded (0 until then), and
the solver they go to."
(define-type circuit
  (productof (kinds (ref ivec @cb)) (args (ref (arrayof ints @cb) @cb)) (hashes (ref ivec @cb))
             (buckets (ref ivec @cb)) (chain (ref ivec @cb)) (count (ref int @cb))
             (vars (ref ivec @cb)) (solver sat-solver) (true-var int)))

(define* make-circuit (subr cb-eff () circuit)
  (lambda ()
    (let* ((s (make-solver)) (t (sat-new-var! s)))
      (begin
        (sat-add-clause! s (list (make-lit t #f)))
        (product (kinds (new (the ivec (make-array 1024 0))))
                 (args (new (the (arrayof ints @cb) (make-array 1024 (the ints nil)))))
                 (hashes (new (the ivec (make-array 1024 0))))
                 (buckets (new (the ivec (make-array 1024 0))))
                 (chain (new (the ivec (make-array 1024 0))))
                 (count (new 2))
                 (vars (new (the ivec (make-array 1024 0))))
                 (solver s) (true-var t))))))

(define* c-count (subr (read @cb) (circuit) int) (lambda (c) (get (extract c count))))
(define* c-solver (subr pure (circuit) sat-solver) (lambda (c) (extract c solver)))

(hide
  (define* widen-ivec (subr cb-eff (ivec int) ivec)
    (lambda (v n)
      (let ((w (the ivec (make-array n 0))))
        (letrec ((go (subr cb-eff (int) ivec)
                   (lambda (i) (if (>= i (array-length v)) w (begin (array-set! w i (array-ref v i)) (go (+ i 1)))))))
          (go 0)))))
  (define* widen-args (subr cb-eff ((arrayof ints @cb) int) (arrayof ints @cb))
    (lambda (v n)
      (let ((w (the (arrayof ints @cb) (make-array n (the ints nil)))))
        (letrec ((go (subr cb-eff (int) (arrayof ints @cb))
                   (lambda (i) (if (>= i (array-length v)) w (begin (array-set! w i (array-ref v i)) (go (+ i 1)))))))
          (go 0)))))
  (define* mix (subr pure (int int) int) (lambda (h x) (bitwise-and (+ (* h 31) x) 281474976710655)))
  (define* hash-ints (subr spin (int ints) int)
    (lambda (h l) (if (null? l) h (hash-ints (mix h (+ (car l) 1099511627776)) (cdr l)))))
  (define* same-ints? (subr spin (ints ints) bool)
    (lambda (a b) (cond ((null? a) (null? b)) ((null? b) #f) ((= (car a) (car b)) (same-ints? (cdr a) (cdr b))) (else #f))))

  "Room for node `n`: every array by node at least n+1 long, the table
  rehashed when it is half full."
  (define* room! (subr cb-eff (circuit int) unit)
    (lambda (c n)
      (let ((cap (array-length (get (extract c kinds)))))
        (if (< n cap) #u
            (let ((m (* 2 cap)))
              (begin
                (set (extract c kinds) (widen-ivec (get (extract c kinds)) m))
                (set (extract c args) (widen-args (get (extract c args)) m))
                (set (extract c hashes) (widen-ivec (get (extract c hashes)) m))
                (set (extract c chain) (widen-ivec (get (extract c chain)) m))
                (set (extract c vars) (widen-ivec (get (extract c vars)) m))
                (let ((b (the ivec (make-array m 0))) (ch (get (extract c chain))) (hs (get (extract c hashes)))
                      (ks (get (extract c kinds))) (top (get (extract c count))))
                  (letrec ((go (subr cb-eff (int) unit)
                             (lambda (i) (if (>= i top) #u
                                             (if (= (array-ref ks i) 1)
                                                 (let ((k (modulo (array-ref hs i) m)))
                                                   (begin (array-set! ch i (array-ref b k)) (array-set! b k i) (go (+ i 1))))
                                                 (go (+ i 1)))))))
                    (begin (go 2) (set (extract c buckets) b))))))))))

  "A new node of kind `k`, inputs `as`, hash `h`."
  (define* new-node! (subr cb-eff (circuit int ints int) int)
    (lambda (c k as h)
      (let ((n (get (extract c count))))
        (begin
          (room! c n)
          (set (extract c count) (+ n 1))
          (array-set! (get (extract c kinds)) n k)
          (array-set! (get (extract c args)) n as)
          (array-set! (get (extract c hashes)) n h)
          (array-set! (get (extract c vars)) n 0)
          (if (= k 1)
              (let* ((b (get (extract c buckets))) (i (modulo h (array-length b))))
                (begin (array-set! (get (extract c chain)) n (array-ref b i)) (array-set! b i n) n))
              n))))))

"A new input: a variable of the problem."
(define* c-input! (subr cb-eff (circuit) int) (lambda (c) (new-node! c 0 nil 0)))

(define* c-not (subr pure (int) int) (lambda (x) (- 0 x)))

"The AND of `xs`, simplified: true dropped, false or x with -x false,
duplicates one, none true, one itself."
(define* c-and (subr cb-eff (circuit ints) int)
  (lambda (c xs)
    (letrec ((by-node (subr pure (int int) bool)
               (lambda (a b) (let ((x (abs a)) (y (abs b))) (or (< x y) (and (= x y) (< a b))))))
             ;; sorted, so x and -x are next to each other (-x first)
             (clean (subr spin (ints ints) (sumof (none unit) (some ints)))
               (lambda (l acc)
                 (cond ((null? l) (sum some (reverse acc)))
                       ((= (car l) c-true) (clean (cdr l) acc))
                       ((= (car l) c-false) (sum none #u))
                       ((and (pair? acc) (= (car acc) (car l))) (clean (cdr l) acc))
                       ((and (pair? acc) (= (car acc) (- 0 (car l)))) (sum none #u))
                       (else (clean (cdr l) (cons (car l) acc)))))))
      (tagcase (clean (list-sort by-node xs) nil)
        (none u c-false)
        (some as
          (cond ((null? as) c-true)
                ((null? (cdr as)) (car as))
                (else
                 (let* ((h (hash-ints 7 as)) (b (get (extract c buckets))))
                   (letrec ((look (subr cb-eff (int) int)
                              (lambda (n)
                                (cond ((= n 0) (new-node! c 1 as h))
                                      ((and (= (array-ref (get (extract c hashes)) n) h)
                                            (same-ints? (array-ref (get (extract c args)) n) as))
                                       n)
                                      (else (look (array-ref (get (extract c chain)) n)))))))
                     (look (array-ref b (modulo h (array-length b)))))))))))))

(define* c-or (subr cb-eff (circuit ints) int)
  (lambda (c xs) (c-not (c-and c (letrec ((neg (subr spin (ints) ints) (lambda (l) (if (null? l) nil (cons (- 0 (car l)) (neg (cdr l)))))))
                                   (neg xs))))))
(define* c-and2 (subr cb-eff (circuit int int) int) (lambda (c a b) (c-and c (list a b))))
(define* c-or2 (subr cb-eff (circuit int int) int) (lambda (c a b) (c-or c (list a b))))
(define* c-implies (subr cb-eff (circuit int int) int) (lambda (c a b) (c-or c (list (c-not a) b))))
(define* c-iff (subr cb-eff (circuit int int) int)
  (lambda (c a b) (c-and2 c (c-implies c a b) (c-implies c b a))))
(define* c-ite (subr cb-eff (circuit int int int) int)
  (lambda (c i t e) (cond ((= i c-true) t) ((= i c-false) e) ((= t e) t)
                          (else (c-or2 c (c-and2 c i t) (c-and2 c (c-not i) e))))))

"At most one of `xs`, pairwise (fine for the few a bound gives)."
(define* c-at-most-one (subr cb-eff (circuit ints) int)
  (lambda (c xs)
    (letrec ((pairs (subr cb-eff (ints ints) ints)
               (lambda (l acc)
                 (if (null? l) acc
                     (pairs (cdr l)
                            (letrec ((against (subr cb-eff (ints ints) ints)
                                       (lambda (m acc) (if (null? m) acc (against (cdr m) (cons (c-or2 c (c-not (car l)) (c-not (car m))) acc))))))
                              (against (cdr l) acc)))))))
      (c-and c (pairs xs nil)))))
(define* c-exactly-one (subr cb-eff (circuit ints) int)
  (lambda (c xs) (c-and2 c (c-or c xs) (c-at-most-one c xs))))

;;; ------------------------------------------------------------ to SAT

"The SAT literal of `x`, its nodes encoded if they were not."
(define* c-lit! (subr cb-eff (circuit int) int)
  (lambda (c x)
    (let ((n (abs x)))
      (if (= n 1) (make-lit (extract c true-var) (< x 0))
          (let ((v (array-ref (get (extract c vars)) n)))
            (if (> v 0) (make-lit v (< x 0))
                (let ((v (sat-new-var! (extract c solver))))
                  (begin
                    (array-set! (get (extract c vars)) n v)
                    (if (= (array-ref (get (extract c kinds)) n) 1)
                        ;; g = AND(as): g -> a for each a, and (AND as) -> g
                        (let* ((as (array-ref (get (extract c args)) n))
                               (g (make-lit v #f)) (ng (make-lit v #t)))
                          (letrec ((each (subr cb-eff (ints ints) unit)
                                     (lambda (l negs)
                                       (if (null? l) (begin (sat-add-clause! (extract c solver) (cons g negs)) #u)
                                           (let ((a (c-lit! c (car l))))
                                             (begin (sat-add-clause! (extract c solver) (list ng a))
                                                    (each (cdr l) (cons (bitwise-xor a 1) negs))))))))
                            (each as nil)))
                        #u)
                    (make-lit v (< x 0))))))))))

"`x` must hold."
(define* c-assert! (subr cb-eff (circuit int) unit)
  (lambda (c x) (begin (sat-add-clause! (extract c solver) (list (c-lit! c x))) #u)))

"Solve: whether what was asserted can hold (under assumptions, circuit
values taken as true for this solve only)."
(define* c-solve! (subr cb-eff (circuit ints) bool)
  (lambda (c assumed)
    (letrec ((lits (subr cb-eff (ints) ints) (lambda (l) (if (null? l) nil (cons (c-lit! c (car l)) (lits (cdr l)))))))
      (= (sat-solve (extract c solver) (lits assumed)) sat-sat))))

"`x`'s value in the last solution. A node never encoded is false if an
input, else as its inputs say."
(define* c-value (subr cb-eff (circuit int) bool)
  (lambda (c x)
    (let ((n (abs x)))
      (let ((b (if (= n 1) #t
                   (let ((v (array-ref (get (extract c vars)) n)))
                     (cond ((> v 0) (sat-value (extract c solver) v))
                           ((= (array-ref (get (extract c kinds)) n) 0) #f)
                           (else (letrec ((all (subr cb-eff (ints) bool)
                                            (lambda (l) (or (null? l) (and (c-value c (car l)) (all (cdr l)))))))
                                   (all (array-ref (get (extract c args)) n)))))))))
        (if (< x 0) (not b) b)))))

"The SAT variables made so far, and the gates."
(define* c-sat-vars (subr (maxeff (read @cb) spin) (circuit) int)
  (lambda (c) (letrec ((go (subr (maxeff (read @cb) spin) (int int) int)
                         (lambda (i k) (if (>= i (get (extract c count))) k (go (+ i 1) (if (> (array-ref (get (extract c vars)) i) 0) (+ k 1) k))))))
                (go 2 1))))
