;;; blast.fx: terms to clauses of the SAT solver (lockpick's
;;; `(lockpick blast)`).
;;;
;;; A Boolean term is given a literal, by the Tseitin encoding: a new
;;; variable x for (and a b ...), with clauses saying x <-> (and a b ...),
;;; and likewise for the other connectives. A bitvector term is given an
;;; array of literals, its bits from the least significant (bit-blasting),
;;; made by circuits after cbmc's (src/solvers/flattening/bv_utils.cpp):
;;; ripple-carry adders, shift-and-add multipliers, barrel shifters, and
;;; division by a quotient and a remainder constrained by a = b*q + r,
;;; r < b. An arithmetic atom is a literal of the simplex theory.
;;;
;;; Gates fold constants (the literals of true and false) and are hashed,
;;; so that a gate on the same inputs is made once. The clauses that define
;;; literals are added once, unguarded: they only name things, so they hold
;;; at every level of the assertion stack. Assertions are added under a
;;; guard (an activation literal) if one is given.
;;;
;;; Terms reach here checked (smtlib.fx's parser refuses what the blaster
;;; cannot do: nonlinear products, division by a variable), so blasting
;;; does not fail.

(module-parameters ((m-sat (load-moduleof "sat.fx")) (m-rat (load-moduleof "rat.fx"))
                    (m-term (load-moduleof "term.fx" m-sat m-rat))
                    (m-bv (load-moduleof "bv.fx" m-sat m-rat m-term))
                    (m-arith (load-moduleof "arith.fx" m-sat m-rat m-term))
                    (m-eval (load-moduleof "eval.fx" m-sat m-rat m-term))
                    (m-simplex (load-moduleof "simplex.fx" m-sat m-rat))))

(define-type divided (productof (q ivec) (r ivec)))

(define-type blaster
  (productof
   (solver sat-solver)
   (lits (ref ivec @cb))                         ; by term: its literal, or 0
   (bits (ref ivecs @cb)) (has-bits (ref bools @cb))   ; by term: its bits
   (true-lit int)
   (gates (table int int @cb))                   ; and and xor gates: key -> literal
   (ites (table string int @cb))                 ; ite gates: \"c x y\" -> literal
   (divs (table string divided @cb))             ; \"a b\" -> quotient and remainder bits
   (simplex simplex) (has-simplex (ref bool @cb)) ; the arithmetic theory, once needed
   (tvars (ref ivec @cb))                        ; by term: its simplex variable, or -1
   (defined (table string bool @cb))             ; \"a k\" of div/mod defined
   (int-terms (ref ints @cb))))                  ; integer terms with simplex variables

(define* int-hash (subr pure (int) int) (lambda (k) (bitwise-and k 1152921504606846975)))

(define* make-blaster (subr cb-eff (sat-solver) blaster)
  (lambda (s)
    (let ((t (make-lit (sat-new-var! s) #f)))
      (begin
        (sat-add-clause! s (list t))
        (product (solver s)
                 (lits (new (the ivec (make-array 1024 0))))
                 (bits (new (the ivecs (make-array 1024 (the ivec (make-array 0 0))))))
                 (has-bits (new (the bools (make-array 1024 #f))))
                 (true-lit t)
                 (gates (the (table int int @cb) (make-table int-hash (lambda ((a int) (b int)) (= a b)))))
                 (ites (the (table string int @cb) (make-table string-hash string=?)))
                 (divs (the (table string divided @cb) (make-table string-hash string=?)))
                 (simplex (make-simplex s)) (has-simplex (new #f))
                 (tvars (new (the ivec (make-array 1024 -1))))
                 (defined (the (table string bool @cb) (make-table string-hash string=?)))
                 (int-terms (new (the ints nil))))))))

(define* blaster-solver (subr pure (blaster) sat-solver) (lambda (b) (extract b solver)))
(define* blaster-true-lit (subr pure (blaster) int) (lambda (b) (extract b true-lit)))
(define* blaster-int-terms (subr (read @cb) (blaster) ints) (lambda (b) (get (extract b int-terms))))
(define* blaster-has-simplex? (subr (read @cb) (blaster) bool) (lambda (b) (get (extract b has-simplex))))
(define* blaster-simplex (subr pure (blaster) simplex) (lambda (b) (extract b simplex)))

"The literal of term t, 0 if it has none yet."
(define* blaster-lit (subr cb-eff (blaster int) int)
  (lambda (b t) (let ((v (get (extract b lits)))) (if (< t (array-length v)) (array-ref v t) 0))))
(define* set-lit! (subr cb-eff (blaster int int) int)
  (lambda (b t l)
    (begin (set (extract b lits) (grow-ivec (get (extract b lits)) t 0))
           (array-set! (get (extract b lits)) t l)
           l)))
(define* bits-of (subr cb-eff (blaster int) ivec)
  (lambda (b t) (array-ref (get (extract b bits)) t)))
(define* has-bits? (subr cb-eff (blaster int) bool)
  (lambda (b t) (let ((v (get (extract b has-bits)))) (and (< t (array-length v)) (array-ref v t)))))
(define* set-bits! (subr cb-eff (blaster int ivec) ivec)
  (lambda (b t bits)
    (begin (set (extract b bits) (grow-ivecs (get (extract b bits)) t))
           (set (extract b has-bits) (grow-bools (get (extract b has-bits)) t #f))
           (array-set! (get (extract b bits)) t bits)
           (array-set! (get (extract b has-bits)) t #t)
           bits)))
"The simplex variable of term t, or -1."
(define* tvar-of (subr cb-eff (blaster int) int)
  (lambda (b t) (let ((v (get (extract b tvars)))) (if (< t (array-length v)) (array-ref v t) -1))))
(define* set-tvar! (subr cb-eff (blaster int int) unit)
  (lambda (b t x) (begin (set (extract b tvars) (grow-ivec (get (extract b tvars)) t -1)) (array-set! (get (extract b tvars)) t x))))

(define* new-lit! (subr cb-eff (blaster) int) (lambda (b) (make-lit (sat-new-var! (extract b solver)) #f)))
(define* clause! (subr cb-eff (blaster ints) unit) (lambda (b lits) (begin (sat-add-clause! (extract b solver) lits) #u)))

;;; ------------------------------------------------------------ gates

(define* tt (subr pure (blaster) int) (lambda (b) (extract b true-lit)))
(define* ff (subr pure (blaster) int) (lambda (b) (lit-neg (extract b true-lit))))
(define* neg (subr pure (int) int) (lambda (x) (lit-neg x)))
(define* const? (subr pure (blaster int) bool) (lambda (b x) (or (= x (tt b)) (= x (ff b)))))

(define* and2 (subr cb-eff (blaster int int) int)
  (lambda (b x y)
    (cond ((or (= x (ff b)) (= y (ff b))) (ff b))
          ((= x (tt b)) y)
          ((= y (tt b)) x)
          ((= x y) x)
          ((= x (neg y)) (ff b))
          ((> x y) (and2 b y x))
          (else
           (let ((key (+ (* (+ (* x 536870912) y) 4) 0)))
             (if (table-has? (extract b gates) key) (table-ref (extract b gates) key 0)
                 (let ((z (new-lit! b)))
                   (begin (clause! b (list (neg z) x))
                          (clause! b (list (neg z) y))
                          (clause! b (list z (neg x) (neg y)))
                          (table-set! (extract b gates) key z)
                          z))))))))
(define* or2 (subr cb-eff (blaster int int) int) (lambda (b x y) (neg (and2 b (neg x) (neg y)))))
(define* xor2 (subr cb-eff (blaster int int) int)
  (lambda (b x y)
    (cond ((= x (ff b)) y)
          ((= y (ff b)) x)
          ((= x (tt b)) (neg y))
          ((= y (tt b)) (neg x))
          ((= x y) (ff b))
          ((= x (neg y)) (tt b))
          ;; Inputs made positive: xor(not x, y) = not xor(x, y).
          ((lit-negative? x) (neg (xor2 b (neg x) y)))
          ((lit-negative? y) (neg (xor2 b x (neg y))))
          ((> x y) (xor2 b y x))
          (else
           (let ((key (+ (* (+ (* x 536870912) y) 4) 1)))
             (if (table-has? (extract b gates) key) (table-ref (extract b gates) key 0)
                 (let ((z (new-lit! b)))
                   (begin (clause! b (list (neg z) x y))
                          (clause! b (list (neg z) (neg x) (neg y)))
                          (clause! b (list z (neg x) y))
                          (clause! b (list z x (neg y)))
                          (table-set! (extract b gates) key z)
                          z))))))))
(define* xnor2 (subr cb-eff (blaster int int) int) (lambda (b x y) (neg (xor2 b x y))))

"if c then x else y"
(define* ite-gate (subr cb-eff (blaster int int int) int)
  (lambda (b c x y)
    (cond ((= c (tt b)) x)
          ((= c (ff b)) y)
          ((= x y) x)
          ((lit-negative? c) (ite-gate b (neg c) y x))
          ((= x (tt b)) (or2 b c y))
          ((= x (ff b)) (and2 b (neg c) y))
          ((= y (tt b)) (or2 b (neg c) x))
          ((= y (ff b)) (and2 b c x))
          ((= x (neg y)) (xnor2 b c x))
          ((= c x) (or2 b c y))
          ((= c y) (and2 b c x))
          (else
           (let ((key (string-append (int->string c) (string-append " " (string-append (int->string x) (string-append " " (int->string y)))))))
             (if (table-has? (extract b ites) key) (table-ref (extract b ites) key 0)
                 (let ((z (new-lit! b)))
                   (begin (clause! b (list (neg z) (neg c) x))
                          (clause! b (list (neg z) c y))
                          (clause! b (list z (neg c) (neg x)))
                          (clause! b (list z c (neg y)))
                          (clause! b (list (neg z) x y))
                          (clause! b (list z (neg x) (neg y)))
                          (table-set! (extract b ites) key z)
                          z))))))))

(define* map-neg (subr spin (ints) ints) (lambda (l) (if (null? l) nil (cons (lit-neg (car l)) (map-neg (cdr l))))))

"The conjunction of a list of literals, as one gate."
(define* and-list (subr cb-eff (blaster ints) int)
  (lambda (b ls)
    (let ((ls (letrec ((go (subr cb-eff (ints ints) ints)
                         (lambda (ls acc)
                           (cond ((null? ls) acc)
                                 ((= (car ls) (tt b)) (go (cdr ls) acc))
                                 ((memv? (car ls) acc) (go (cdr ls) acc))
                                 (else (go (cdr ls) (cons (car ls) acc)))))))
                (go ls nil))))
      (cond ((memv? (ff b) ls) (ff b))
            ((null? ls) (tt b))
            ((null? (cdr ls)) (car ls))
            ((null? (cdr (cdr ls))) (and2 b (car ls) (car (cdr ls))))
            ((letrec ((go (subr cb-eff (ints) bool) (lambda (l) (and (pair? l) (or (memv? (neg (car l)) ls) (go (cdr l)))))))
               (go ls))
             (ff b))
            (else
             (let ((z (new-lit! b)))
               (begin
                 (letrec ((go (subr cb-eff (ints) unit) (lambda (l) (if (null? l) #u (begin (clause! b (list (neg z) (car l))) (go (cdr l)))))))
                   (go ls))
                 (clause! b (cons z (map-neg ls)))
                 z)))))))
(define* or-list (subr cb-eff (blaster ints) int) (lambda (b ls) (neg (and-list b (map-neg ls)))))

"A full adder: the sum and the carry of x + y + c."
(define-type sum-carry (productof (s int) (c int)))
(define* full-adder (subr cb-eff (blaster int int int) sum-carry)
  (lambda (b x y c)
    (if (or (const? b x) (const? b y) (const? b c))
        (let ((xy (xor2 b x y)))
          (let ((s (xor2 b xy c))) (product (s s) (c (or2 b (and2 b x y) (and2 b c xy))))))
        ;; (lockpick's `let` of s and co: Twobit evaluates a `let`'s
        ;; inits right to left, so co is made first, as here.)
        (let* ((co (new-lit! b)) (s (new-lit! b)))
          (begin
            ;; co = majority(x, y, c)
            (clause! b (list (neg x) (neg y) co))
            (clause! b (list (neg x) (neg c) co))
            (clause! b (list (neg y) (neg c) co))
            (clause! b (list x y (neg co)))
            (clause! b (list x c (neg co)))
            (clause! b (list y c (neg co)))
            ;; s = x xor y xor c
            (clause! b (list x y c (neg s)))
            (clause! b (list x (neg y) (neg c) (neg s)))
            (clause! b (list (neg x) y (neg c) (neg s)))
            (clause! b (list (neg x) (neg y) c (neg s)))
            (clause! b (list (neg x) (neg y) (neg c) s))
            (clause! b (list (neg x) y c s))
            (clause! b (list x (neg y) c s))
            (clause! b (list x y (neg c) s))
            (product (s s) (c co)))))))

;;; ------------------------------------------------------------ circuits
;;; On arrays of bits, least significant first.

(define* bits-map1 (subr cb-eff ((subr cb-eff (int) int) ivec) ivec)
  (lambda (f v)
    (let ((out (the ivec (make-array (array-length v) 0))))
      (letrec ((go (subr cb-eff (int) ivec) (lambda (i) (if (= i (array-length v)) out (begin (array-set! out i (f (array-ref v i))) (go (+ i 1)))))))
        (go 0)))))
(define* bits-map2 (subr cb-eff ((subr cb-eff (int int) int) ivec ivec) ivec)
  (lambda (f v w)
    (let ((out (the ivec (make-array (array-length v) 0))))
      (letrec ((go (subr cb-eff (int) ivec) (lambda (i) (if (= i (array-length v)) out (begin (array-set! out i (f (array-ref v i) (array-ref w i))) (go (+ i 1)))))))
        (go 0)))))
(define* bits-neg (subr cb-eff (ivec) ivec) (lambda (v) (bits-map1 (lambda ((x int)) (lit-neg x)) v)))

(define* const-bits (subr cb-eff (blaster int int) ivec)
  (lambda (b value width)
    (let ((out (the ivec (make-array width 0))))
      (letrec ((go (subr cb-eff (int int) ivec)
                 (lambda (i v) (if (= i width) out (begin (array-set! out i (if (= 1 (bitwise-and v 1)) (tt b) (ff b))) (go (+ i 1) (arithmetic-shift v -1)))))))
        (go 0 value)))))

"The sum of xs + ys + cin, and the carry out."
(define-type sum-bits (productof (s ivec) (c int)))
(define* adder (subr cb-eff (blaster ivec ivec int) sum-bits)
  (lambda (b xs ys cin)
    (let* ((n (array-length xs)) (out (the ivec (make-array n 0))))
      (letrec ((go (subr cb-eff (int int) sum-bits)
                 (lambda (i c)
                   (if (= i n) (product (s out) (c c))
                       (let ((sc (full-adder b (array-ref xs i) (array-ref ys i) c)))
                         (begin (array-set! out i (extract sc s)) (go (+ i 1) (extract sc c))))))))
        (go 0 cin)))))
(define* add-bits (subr cb-eff (blaster ivec ivec) ivec) (lambda (b xs ys) (extract (adder b xs ys (ff b)) s)))
(define* sub-bits (subr cb-eff (blaster ivec ivec) ivec) (lambda (b xs ys) (extract (adder b xs (bits-neg ys) (tt b)) s)))
(define* neg-bits (subr cb-eff (blaster ivec) ivec)
  (lambda (b xs) (extract (adder b (bits-neg xs) (const-bits b 0 (array-length xs)) (tt b)) s)))
"xs < ys, unsigned: there is no carry out of xs + not ys + 1."
(define* ult-bits (subr cb-eff (blaster ivec ivec) int)
  (lambda (b xs ys) (neg (extract (adder b xs (bits-neg ys) (tt b)) c))))
"Signed: flip the sign bits and compare unsigned."
(define* slt-bits (subr cb-eff (blaster ivec ivec) int)
  (lambda (b xs ys)
    (let* ((n (array-length xs))
           (flip (lambda ((v ivec)) (let ((w (ivec-take v n))) (begin (array-set! w (- n 1) (neg (array-ref w (- n 1)))) w)))))
      (ult-bits b (flip xs) (flip ys)))))
(define* eq-bits (subr cb-eff (blaster ivec ivec) int)
  (lambda (b xs ys) (and-list b (ivec->list (bits-map2 (lambda ((x int) (y int)) (xnor2 b x y)) xs ys) 0 (array-length xs)))))

"The product, truncated to width bits (the inputs are zero-extended or
truncated to width first)."
(define* mul-bits (subr cb-eff (blaster ivec ivec int) ivec)
  (lambda (b xs ys width)
    (let* ((pad (lambda ((v ivec))
                  (let ((w (the ivec (make-array width (ff b)))))
                    (letrec ((go (subr cb-eff (int) ivec) (lambda (i) (if (= i (min width (array-length v))) w (begin (array-set! w i (array-ref v i)) (go (+ i 1)))))))
                      (go 0)))))
           (xs (pad xs)) (ys (pad ys))
           ;; Shift the operand with more constant bits into ys, whose bits
           ;; select the partial products.
           (nconst (lambda ((v ivec)) (letrec ((go (subr cb-eff (int int) int) (lambda (i n) (if (= i width) n (go (+ i 1) (if (const? b (array-ref v i)) (+ n 1) n))))))
                                        (go 0 0))))
           (swap? (> (nconst xs) (nconst ys)))
           (xs* (the ivec (if swap? ys xs))) (ys* (the ivec (if swap? xs ys)))
           (acc (the ivec (make-array width (ff b)))))
      (letrec ((row (subr cb-eff (int) ivec)
                 (lambda (i)
                   (if (= i width) acc
                       (let ((y (array-ref ys* i)))
                         (begin
                           (if (= y (ff b)) #u
                               (letrec ((go (subr cb-eff (int int) unit)
                                          (lambda (j c)
                                            (if (>= j width) #u
                                                (let ((sc (full-adder b (array-ref acc j) (and2 b (array-ref xs* (- j i)) y) c)))
                                                  (begin (array-set! acc j (extract sc s)) (go (+ j 1) (extract sc c))))))))
                                 (go i (ff b))))
                           (row (+ i 1))))))))
        (row 0)))))

"Quotient and remainder of unsigned division, as fresh bits q and r with
constraints: if ys is not 0, xs = ys*q + r (computed at twice the width, so
nothing overflows) and r < ys; if ys is 0, q is all ones and r is xs. The
constraints are unguarded: they define q and r."
(define* divide (subr cb-eff (blaster ivec ivec) divided)
  (lambda (b xs ys)
    (let* ((n (array-length xs))
           (q (the ivec (make-array n 0))) (r (the ivec (make-array n 0)))
           (zero (eq-bits b ys (const-bits b 0 n))))
      (begin
        (letrec ((go (subr cb-eff (int) unit) (lambda (i) (if (= i n) #u (begin (array-set! q i (new-lit! b)) (array-set! r i (new-lit! b)) (go (+ i 1)))))))
          (go 0))
        (let* ((ext (lambda ((v ivec)) (ivec-grow v (* 2 n) (ff b))))
               (prod (mul-bits b ys q (* 2 n)))
               (total (adder b prod (ext r) (ff b)))
               (ax (ext xs)))
          (begin
            ;; not zero -> sum = xs (no carry out either), r < ys
            (letrec ((go (subr cb-eff (int) unit)
                       (lambda (i) (if (= i (* 2 n)) #u
                                       (let ((s (array-ref (extract total s) i)) (a (array-ref ax i)))
                                         (begin (clause! b (list zero (neg s) a)) (clause! b (list zero s (neg a))) (go (+ i 1))))))))
              (go 0))
            (clause! b (list zero (neg (extract total c))))
            (clause! b (list zero (ult-bits b r ys)))
            ;; zero -> q = ones, r = xs
            (letrec ((go (subr cb-eff (int) unit)
                       (lambda (i) (if (= i n) #u
                                       (begin (clause! b (list (neg zero) (array-ref q i)))
                                              (clause! b (list (neg zero) (neg (array-ref r i)) (array-ref xs i)))
                                              (clause! b (list (neg zero) (array-ref r i) (neg (array-ref xs i))))
                                              (go (+ i 1)))))))
              (go 0))
            (product (q q) (r r))))))))

"Barrel shifter: (shift-once v k) shifts by the constant k, and `f` is the
bit shifted in."
(define* shift-bits (subr cb-eff (blaster ivec ivec (subr cb-eff (ivec int) ivec) int) ivec)
  (lambda (b xs ss shift-once f)
    (let* ((n (array-length xs))
           (stages (letrec ((go (subr cb-eff (int) int) (lambda (k) (if (< (expt2 k) n) (go (+ k 1)) k)))) (go 0))))
      (letrec ((go (subr cb-eff (int ivec) ivec)
                 (lambda (k v)
                   (if (and (< k stages) (< k (array-length ss)))
                       (let ((s (array-ref ss k)) (shifted (shift-once v (expt2 k))))
                         (go (+ k 1) (bits-map2 (lambda ((x int) (y int)) (ite-gate b s x y)) shifted v)))
                       ;; A shift amount with a bit at or above stages set shifts
                       ;; everything out.
                       (let ((over (or-list b (letrec ((hi (subr cb-eff (int ints) ints)
                                                          (lambda (i acc) (if (< i (array-length ss)) (hi (+ i 1) (cons (array-ref ss i) acc)) acc))))
                                                 (hi stages nil)))))
                         (bits-map1 (lambda ((x int)) (ite-gate b over f x)) v))))))
        (go 0 xs)))))
(define* shl-once (subr cb-eff (blaster) (subr cb-eff (ivec int) ivec))
  (lambda (b)
    (lambda ((v ivec) (k int))
      (let* ((n (array-length v)) (w (the ivec (make-array n (ff b)))))
        (letrec ((go (subr cb-eff (int) ivec) (lambda (i) (if (>= i n) w (begin (array-set! w i (array-ref v (- i k))) (go (+ i 1)))))))
          (go k))))))
(define* shr-once (subr cb-eff (int) (subr cb-eff (ivec int) ivec))
  (lambda (fill)
    (lambda ((v ivec) (k int))
      (let* ((n (array-length v)) (w (the ivec (make-array n fill))))
        (letrec ((go (subr cb-eff (int) ivec) (lambda (i) (if (>= (+ i k) n) w (begin (array-set! w i (array-ref v (+ i k))) (go (+ i 1)))))))
          (go 0))))))

;;; ------------------------------------------------------------ terms to literals and bits

"The literal of a Boolean term, defining it if need be."
(define blast-bool! (subr cb-eff (blaster int) int)
  (lambda (b t) (let ((l (blaster-lit b t))) (if (> l 0) l (set-lit! b t (define-bool! b t))))))

(define blast-list! (subr cb-eff (blaster ints) ints)
  (lambda (b ts) (if (null? ts) nil (let ((l (blast-bool! b (car ts)))) (cons l (blast-list! b (cdr ts)))))))

(define define-bool! (subr cb-eff (blaster int) int)
  (lambda (b t)
    (let ((args (term-args t)) (op (term-op t)))
      (cond
       ((string=? op "true") (tt b))
       ((string=? op "false") (ff b))
       ((string=? op "var") (new-lit! b))
       ((string=? op "not") (neg (blast-bool! b (car args))))
       ;; The order lockpick's `let`s come to under Twobit (inits right to
       ;; left): x is made before the arguments are blasted.
       ((string=? op "and")
        (let* ((x (new-lit! b)) (ls (blast-list! b args)))
          (begin (letrec ((go (subr cb-eff (ints) unit) (lambda (l) (if (null? l) #u (begin (clause! b (list (neg x) (car l))) (go (cdr l)))))))
                   (go ls))
                 (clause! b (cons x (map-neg ls)))
                 x)))
       ((string=? op "or")
        (let* ((x (new-lit! b)) (ls (blast-list! b args)))
          (begin (letrec ((go (subr cb-eff (ints) unit) (lambda (l) (if (null? l) #u (begin (clause! b (list x (neg (car l)))) (go (cdr l)))))))
                   (go ls))
                 (clause! b (cons (neg x) ls))
                 x)))
       ((string=? op "=")
        (cond ((term-bool? (car args))
               (let* ((x (new-lit! b)) (q (blast-bool! b (car (cdr args)))) (p (blast-bool! b (car args))))
                 (begin (clause! b (list (neg x) (neg p) q))
                        (clause! b (list (neg x) p (neg q)))
                        (clause! b (list x p q))
                        (clause! b (list x (neg p) (neg q)))
                        x)))
              ((arith-sort? (term-sort (car args))) (blast-bool! b (mk-arith-eq (car args) (car (cdr args)))))
              (else (eq-bits b (blast-bits! b (car args)) (blast-bits! b (car (cdr args)))))))
       ((or (string=? op "<=") (string=? op ">=")) (atom-lit! b t))
       ((string=? op "card") (card-lit b (term-param0 t) (term-param1 t) (blast-list! b args)))
       ((string=? op "ite")
        (let* ((q (blast-bool! b (car (cdr (cdr args))))) (p (blast-bool! b (car (cdr args)))) (c (blast-bool! b (car args))))
          (ite-gate b c p q)))
       ((string=? op "bvult") (ult-bits b (blast-bits! b (car args)) (blast-bits! b (car (cdr args)))))
       ((string=? op "bvslt") (slt-bits b (blast-bits! b (car args)) (blast-bits! b (car (cdr args)))))
       (else (begin (error (string-append "combo: unsupported term " op)) 0))))))

;;; Cardinality, by a totalizer (Bailleux and Boufkhad, "Efficient CNF
;;; Encoding of Boolean Cardinality Constraints", 2003): a tree over the
;;; literals whose nodes count, in unary, the true ones below them, with
;;; clauses both ways, so that the literal made is equivalent to the
;;; constraint (it may be negated, or under an or). Counts are kept only up
;;; to what the bounds need: hi+1, or lo.

(define* card-lit (subr cb-eff (blaster int int ints) int)
  (lambda (b lo hi ls)
    (let ((outs (totalize b (list->ivec ls) 0 (list-length ls) (if (= hi no-bound) lo (+ hi 1)))))
      (and2 b (if (> lo 0) (array-ref outs (- lo 1)) (tt b)) (if (= hi no-bound) (tt b) (neg (array-ref outs hi)))))))

"Literals r1 ... rm (m at most c) for the literals of v from `from` to
`to`, ri true if and only if at least i of them are (when i < c; rc: at
least c)."
(define* totalize (subr cb-eff (blaster ivec int int int) ivec)
  (lambda (b v from to c)
    (if (= (- to from) 1)
        (let ((r (the ivec (make-array 1 0)))) (begin (array-set! r 0 (array-ref v from)) r))
        (let* ((mid (quotient (+ from to) 2))
               (x (totalize b v from mid c))
               (y (totalize b v mid to c))
               (p (array-length x)) (q (array-length y))
               (m (min (+ p q) c))
               (r (the ivec (make-array m 0))))
          (begin
            (letrec ((go (subr cb-eff (int) unit) (lambda (k) (if (= k m) #u (begin (array-set! r k (new-lit! b)) (go (+ k 1)))))))
              (go 0))
            ;; At least i on the left and j on the right: at least i+j. x0 and
            ;; y0 are true, and x(p+1) and y(q+1) false.
            (let ((xi (lambda ((i int)) (cond ((= i 0) (tt b)) ((> i p) (ff b)) (else (array-ref x (- i 1))))))
                  (yj (lambda ((j int)) (cond ((= j 0) (tt b)) ((> j q) (ff b)) (else (array-ref y (- j 1)))))))
              (letrec ((outer (subr cb-eff (int) unit)
                         (lambda (i)
                           (if (> i p) #u
                               (letrec ((inner (subr cb-eff (int) unit)
                                          (lambda (j)
                                            (if (> j q) #u
                                                (begin
                                                  (if (> (+ i j) 0) (clause! b (list (neg (xi i)) (neg (yj j)) (array-ref r (- (min (+ i j) m) 1)))) #u)
                                                  ;; At most i on the left and j on the right: at most i+j.
                                                  (if (< (+ i j) m) (clause! b (list (xi (+ i 1)) (yj (+ j 1)) (neg (array-ref r (+ i j))))) #u)
                                                  (inner (+ j 1)))))))
                                 (begin (inner 0) (outer (+ i 1))))))))
                (outer 0)))
            r)))))

"The bits of a bitvector term, blasting it if need be."
(define blast-bits! (subr cb-eff (blaster int) ivec)
  (lambda (b t) (if (has-bits? b t) (bits-of b t) (set-bits! b t (define-bits! b t)))))

(define define-bits! (subr cb-eff (blaster int) ivec)
  (lambda (b t)
    (let* ((args (term-args t)) (w (term-width t)) (op (term-op t))
           (arg (lambda ((i int)) (blast-bits! b (list-ref-int args i)))))
      (cond
       ((string=? op "var") (let ((v (the ivec (make-array w 0))))
                              (letrec ((go (subr cb-eff (int) ivec) (lambda (i) (if (= i w) v (begin (array-set! v i (new-lit! b)) (go (+ i 1)))))))
                                (go 0))))
       ((string=? op "bv") (const-bits b (bv-value t) w))
       ((string=? op "bvnot") (bits-neg (arg 0)))
       ((string=? op "bvand") (bits-map2 (lambda ((x int) (y int)) (and2 b x y)) (arg 0) (arg 1)))
       ((string=? op "bvor") (bits-map2 (lambda ((x int) (y int)) (or2 b x y)) (arg 0) (arg 1)))
       ((string=? op "bvxor") (bits-map2 (lambda ((x int) (y int)) (xor2 b x y)) (arg 0) (arg 1)))
       ((string=? op "bvneg") (neg-bits b (arg 0)))
       ((string=? op "bvadd") (add-bits b (arg 0) (arg 1)))
       ((string=? op "bvsub") (sub-bits b (arg 0) (arg 1)))
       ((string=? op "bvmul") (mul-bits b (arg 0) (arg 1) w))
       ((string=? op "bvudiv") (extract (division b (car args) (car (cdr args))) q))
       ((string=? op "bvurem") (extract (division b (car args) (car (cdr args))) r))
       ((string=? op "bvshl") (shift-bits b (arg 0) (arg 1) (shl-once b) (ff b)))
       ((string=? op "bvlshr") (shift-bits b (arg 0) (arg 1) (shr-once (ff b)) (ff b)))
       ((string=? op "bvashr")
        (let* ((x (arg 0)) (sign (array-ref x (- (array-length x) 1))))
          (shift-bits b x (arg 1) (shr-once sign) sign)))
       ((string=? op "concat")
        (let* ((lo (arg 1)) (hi (arg 0)) (v (the ivec (make-array w 0))) (nl (array-length lo)))
          (letrec ((go (subr cb-eff (int) ivec)
                     (lambda (i) (if (= i w) v (begin (array-set! v i (if (< i nl) (array-ref lo i) (array-ref hi (- i nl)))) (go (+ i 1)))))))
            (go 0))))
       ((string=? op "extract")
        (let* ((lo (term-param1 t)) (x (arg 0)) (v (the ivec (make-array w 0))))
          (letrec ((go (subr cb-eff (int) ivec) (lambda (i) (if (= i w) v (begin (array-set! v i (array-ref x (+ lo i))) (go (+ i 1)))))))
            (go 0))))
       ((string=? op "sign_extend")
        (let* ((x (arg 0)) (n (array-length x))) (ivec-grow x w (array-ref x (- n 1)))))
       ((string=? op "ite")
        (let ((c (blast-bool! b (car args))))
          (bits-map2 (lambda ((x int) (y int)) (ite-gate b c x y)) (arg 1) (arg 2))))
       (else (begin (error (string-append "combo: unsupported term " op)) (the ivec (make-array 0 0))))))))

"One divider for bvudiv and bvurem of the same arguments."
(define division (subr cb-eff (blaster int int) divided)
  (lambda (b x y)
    (let ((key (string-append (int->string x) (string-append " " (int->string y)))))
      (if (table-has? (extract b divs) key)
          (table-ref (extract b divs) key (product (q (the ivec (make-array 0 0))) (r (the ivec (make-array 0 0)))))
          (let ((qr (divide b (blast-bits! b x) (blast-bits! b y))))
            (begin (table-set! (extract b divs) key qr) qr))))))

;;; ------------------------------------------------------------ arithmetic
;;; Atoms are literals of the simplex theory.

(define* simplex-of (subr cb-eff (blaster) simplex)
  (lambda (b)
    (begin
      (if (get (extract b has-simplex)) #u
          (begin (set (extract b has-simplex) #t)
                 (sat-set-theory! (extract b solver) (simplex-theory (extract b simplex)))))
      (extract b simplex))))

"The literal of the atom t, (<= form k) or (>= form k)."
(define atom-lit! (subr cb-eff (blaster int) int)
  (lambda (b t)
    (let* ((x (form-var! b (atom-form t))) (l (new-lit! b)))
      (begin (simplex-add-atom! (simplex-of b) (lit-var l) x (term-op? t "<=") (atom-bound t))
             l))))

"The simplex variable of a linear form: the variable itself, or a slack
variable for a sum."
(define form-var! (subr cb-eff (blaster int) int)
  (lambda (b form)
    (if (or (term-op? form "+") (term-op? form "scale"))
        (let ((x (tvar-of b form)))
          (if (>= x 0) x
              (let* ((f (linear-form form))
                     (sf (letrec ((go (subr cb-eff (monos) sform)
                                    (lambda (ms) (if (null? ms) nil
                                                     (let ((v (term-var! b (extract (car ms) x))))
                                                       (cons (product (x v) (c (extract (car ms) c))) (go (cdr ms))))))))
                           (go (extract f ms))))
                     (x (simplex-slack! (simplex-of b) (sform-sort sf) (all-int? (extract f ms)))))
                (begin (set-tvar! b form x) x))))
        (term-var! b form))))

"The simplex variable of a term that linear forms take as a variable, made
(with the clauses that define it) if need be."
(define term-var! (subr cb-eff (blaster int) int)
  (lambda (b t)
    (let ((x (tvar-of b t)))
      (if (>= x 0) x
          (let ((x (simplex-new-var! (simplex-of b) (int-term? t))))
            (begin
              (set-tvar! b t x)
              (if (int-term? t) (set (extract b int-terms) (cons t (get (extract b int-terms)))) #u)
              (define-arith-term! b t)
              x))))))

(define define! (subr cb-eff (blaster int) unit) (lambda (b t) (blast-assert! b t 0)))

(define define-arith-term! (subr cb-eff (blaster int) unit)
  (lambda (b t)
    (let ((args (term-args t)) (op (term-op t)))
      (cond
       ((string=? op "var") #u)
       ;; An ite of ites, t = (ite c1 x (ite c2 y z)), as t = each leaf under
       ;; its path (c1 -> t = x, not c1 and c2 -> t = y, ...), with no
       ;; variables for the inner ites.
       ((string=? op "ite")
        (letrec ((go (subr cb-eff ((listof ints acyclic)) unit)
                   (lambda (paths)
                     (if (null? paths) #u
                         (let* ((path (car paths))
                                (guards (map-ints (lambda ((c int)) (if (term-op? c "not") (term-arg0 c) (mk-not c))) (cdr path))))
                           (begin
                             (define! b (mk-or (append-ints guards (list (mk-le t (car path))))))
                             (define! b (mk-or (append-ints guards (list (mk-ge t (car path))))))
                             (go (cdr paths))))))))
          (go (ite-leaves b t))))
       ((or (string=? op "div") (string=? op "mod"))
        (let* ((a (car args)) (k (car (cdr args)))
               (key (string-append (int->string a) (string-append " " (rat->string (num-value k))))))
          (if (table-has? (extract b defined) key) #u
              (begin
                (table-set! (extract b defined) key #t)
                (let* ((r (mk-imod a k)) (q (mk-idiv a k)))
                  (begin
                    (define! b (mk-arith-eq a (mk-add (list (mk-mul (list k q)) r))))
                    (define! b (mk-ge r (num rat-0 int-sort)))
                    (define! b (mk-le r (num (rat- (rat-abs (num-value k)) rat-1) int-sort)))))))))
       ((string=? op "to_int")
        (let ((x (car args)) (i (mk-to-real t)))
          (begin (define! b (mk-le i x))
                 (define! b (mk-lt x (mk-add (list i (num rat-1 real-sort))))))))
       (else (error (string-append "combo: nonlinear arithmetic is not supported: " op)))))))

"The leaves of the tree of ites t, each with its path: a list (leaf
condition ...), the conditions (or their negations) all true where t is
the leaf. An inner ite is a leaf if the tree would have more than 16, or if
it has a variable (it is in another term, perhaps a condition here, as in
(abs (abs x)): so each condition is given its literal first)."
(define ite-leaves (subr cb-eff (blaster int) (listof ints acyclic))
  (lambda (b t)
    (let ((leaves (the (ref int @cb) (new 1))))
      (letrec ((walk (subr cb-eff (int ints bool) (listof ints acyclic))
                 (lambda (t path top?)
                   (if (and (term-op? t "ite") (or top? (and (< (get leaves) 16) (< (tvar-of b t) 0))))
                       (let ((c (term-arg0 t)))
                         (begin
                           (if top? #u (set leaves (+ (get leaves) 1)))
                           (blast-bool! b c)
                           (let ((x (walk (term-arg1 t) (cons c path) #f)))
                             (append x (walk (term-arg2 t) (cons (mk-not c) path) #f)))))
                       (list (cons t path))))))
        (walk t nil #t)))))

"The value of variable v in the solver's model. A variable never blasted
is unconstrained, and takes its sort's default value."
(define* blaster-var-value (subr cb-eff (blaster int) rat)
  (lambda (b v)
    (let ((s (extract b solver)))
      (cond
       ((term-bool? v) (let ((l (blaster-lit b v))) (if (> l 0) (rat-bool (sat-lit-value s l)) (default-value (term-sort v)))))
       ((arith-sort? (term-sort v)) (let ((x (tvar-of b v))) (if (>= x 0) (simplex-value (extract b simplex) x) rat-0)))
       ((has-bits? b v)
        (let ((bits (bits-of b v)))
          (letrec ((go (subr cb-eff (int int) int)
                     (lambda (i acc) (if (< i 0) acc (go (- i 1) (+ (* 2 acc) (if (sat-lit-value s (array-ref bits i)) 1 0)))))))
            (int->rat (go (- (array-length bits) 1) 0)))))
       (else (default-value (term-sort v)))))))

"Assert t, under guard (a literal, or 0): the clauses added say guard ->
t. Conjunctions are split, and disjunctions become one clause, so they
need no literal of their own."
(define blast-assert! (subr cb-eff (blaster int int) unit)
  (lambda (b t guard)
    (let ((g (the ints (if (> guard 0) (list (neg guard)) nil))))
      (letrec ((go (subr cb-eff (int) unit)
                 (lambda (t)
                   (let ((op (term-op t)))
                     (cond
                      ((string=? op "and") (letrec ((each (subr cb-eff (ints) unit) (lambda (l) (if (null? l) #u (begin (go (car l)) (each (cdr l)))))))
                                             (each (term-args t))))
                      ((string=? op "or") (clause! b (append-ints g (blast-list! b (term-args t)))))
                      ;; At most one of a few: a clause for each pair (and one
                      ;; of them all, for exactly one), which propagate at once.
                      ((string=? op "card")
                       (let ((lo (term-param0 t)) (hi (term-param1 t)) (args (term-args t)))
                         (if (and (= hi 1) (<= (list-length args) 6))
                             (let ((ls (blast-list! b args)))
                               (begin
                                 (if (= lo 1) (clause! b (append-ints g ls)) #u)
                                 (letrec ((pairs (subr cb-eff (ints) unit)
                                            (lambda (ls)
                                              (if (null? ls) #u
                                                  (begin
                                                    (letrec ((each (subr cb-eff (ints) unit)
                                                               (lambda (l) (if (null? l) #u (begin (clause! b (append-ints g (list (neg (car ls)) (neg (car l))))) (each (cdr l)))))))
                                                      (each (cdr ls)))
                                                    (pairs (cdr ls)))))))
                                   (pairs ls))))
                             (clause! b (append-ints g (list (blast-bool! b t)))))))
                      ((string=? op "not")
                       (let ((a (term-arg0 t)))
                         (if (term-op? a "or")
                             (letrec ((each (subr cb-eff (ints) unit) (lambda (l) (if (null? l) #u (begin (go (mk-not (car l))) (each (cdr l)))))))
                               (each (term-args a)))
                             (clause! b (append-ints g (list (blast-bool! b t)))))))
                      (else (clause! b (append-ints g (list (blast-bool! b t))))))))))
        (go t)))))
