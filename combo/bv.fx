;;; bv.fx: bitvector terms, built by constructors that simplify
;;; (lockpick's `(lockpick bv)`).
;;;
;;; The operators kept in terms are fewer than SMT-LIB's: the others are
;;; written with them.
;;;   bv (a constant: params value width)  bvnot bvand bvor bvxor bvneg
;;;   bvadd bvsub bvmul bvudiv bvurem bvshl bvlshr bvashr
;;;   concat extract (params hi lo) sign_extend (params k)
;;;   bvult bvslt (Boolean), = and ite (term.fx's)
;;; bvsdiv, bvsrem and bvsmod become unsigned division of absolute values,
;;; so that one divider serves all; comparisons become bvult and bvslt,
;;; swapped or negated; shifts and rotations by constants become extract
;;; and concat; zero_extend and repeat become concat.

(module-parameters ((m-sat (load-moduleof "sat.fx")) (m-rat (load-moduleof "rat.fx"))
                    (m-term (load-moduleof "term.fx" m-sat m-rat))))

(define* term-width (subr cb-eff (int) int) (lambda (t) (term-sort t)))

(define* bv-const (subr cb-eff (int int) int)
  (lambda (value width) (make-app "bv" (list (modulo value (expt2 width)) width) nil width)))
(define* bv-const? (subr cb-eff (int) bool) (lambda (t) (term-op? t "bv")))
(define* bv-value (subr cb-eff (int) int) (lambda (t) (term-param0 t)))
(define* bv-zero? (subr cb-eff (int) bool) (lambda (t) (and (bv-const? t) (= 0 (bv-value t)))))
(define* bv-ones? (subr cb-eff (int) bool)
  (lambda (t) (and (bv-const? t) (= (bv-value t) (- (expt2 (term-width t)) 1)))))
(define* bv-one? (subr cb-eff (int) bool) (lambda (t) (and (bv-const? t) (= 1 (bv-value t)))))

"The integer a w-bit pattern stands for in two's complement."
(define* to-signed (subr cb-eff (int int) int)
  (lambda (v w) (if (>= v (expt2 (- w 1))) (- v (expt2 w)) v)))

(define* app1 (subr cb-eff (string int) int) (lambda (op a) (make-app op nil (list a) (term-sort a))))
(define* same-sort-app (subr cb-eff (string int int) int) (lambda (op a b) (make-app op nil (list a b) (term-sort a))))
"Commutative operators: arguments in order of id."
(define* commute (subr cb-eff (string int int) int)
  (lambda (op a b) (if (> a b) (same-sort-app op b a) (same-sort-app op a b))))
(define* both-const? (subr cb-eff (int int) bool) (lambda (a b) (and (bv-const? a) (bv-const? b))))
"The negation of t if that is t's argument, else -1, so as not to make
terms just to compare them."
(define* bvnot-arg (subr cb-eff (int) int) (lambda (t) (if (term-op? t "bvnot") (term-arg0 t) -1)))

;;; ------------------------------------------------------------ bitwise

(define* mk-bvnot (subr cb-eff (int) int)
  (lambda (a)
    (cond ((bv-const? a) (bv-const (- (- (expt2 (term-width a)) 1) (bv-value a)) (term-width a)))
          ((term-op? a "bvnot") (term-arg0 a))
          (else (app1 "bvnot" a)))))

(define* mk-bvand (subr cb-eff (int int) int)
  (lambda (a b)
    (cond ((both-const? a b) (bv-const (bitwise-and (bv-value a) (bv-value b)) (term-width a)))
          ((or (bv-zero? a) (bv-ones? b)) a)
          ((or (bv-zero? b) (bv-ones? a)) b)
          ((= a b) a)
          ((or (= a (bvnot-arg b)) (= b (bvnot-arg a))) (bv-const 0 (term-width a)))
          (else (commute "bvand" a b)))))
(define* mk-bvor (subr cb-eff (int int) int)
  (lambda (a b)
    (cond ((both-const? a b) (bv-const (bitwise-ior (bv-value a) (bv-value b)) (term-width a)))
          ((or (bv-zero? a) (bv-ones? b)) b)
          ((or (bv-zero? b) (bv-ones? a)) a)
          ((= a b) a)
          ((or (= a (bvnot-arg b)) (= b (bvnot-arg a))) (bv-const -1 (term-width a)))
          (else (commute "bvor" a b)))))
(define* mk-bvxor (subr cb-eff (int int) int)
  (lambda (a b)
    (cond ((both-const? a b) (bv-const (bitwise-xor (bv-value a) (bv-value b)) (term-width a)))
          ((bv-zero? a) b)
          ((bv-zero? b) a)
          ((bv-ones? a) (mk-bvnot b))
          ((bv-ones? b) (mk-bvnot a))
          ((= a b) (bv-const 0 (term-width a)))
          (else (commute "bvxor" a b)))))
(define* mk-bvnand (subr cb-eff (int int) int) (lambda (a b) (mk-bvnot (mk-bvand a b))))
(define* mk-bvnor (subr cb-eff (int int) int) (lambda (a b) (mk-bvnot (mk-bvor a b))))
(define* mk-bvxnor (subr cb-eff (int int) int) (lambda (a b) (mk-bvnot (mk-bvxor a b))))

;;; ------------------------------------------------------------ arithmetic

(define* mk-bvneg (subr cb-eff (int) int)
  (lambda (a)
    (cond ((bv-const? a) (bv-const (- 0 (bv-value a)) (term-width a)))
          ((term-op? a "bvneg") (term-arg0 a))
          (else (app1 "bvneg" a)))))
(define* mk-bvadd (subr cb-eff (int int) int)
  (lambda (a b)
    (cond ((both-const? a b) (bv-const (+ (bv-value a) (bv-value b)) (term-width a)))
          ((bv-zero? a) b)
          ((bv-zero? b) a)
          (else (commute "bvadd" a b)))))
(define* mk-bvsub (subr cb-eff (int int) int)
  (lambda (a b)
    (cond ((both-const? a b) (bv-const (- (bv-value a) (bv-value b)) (term-width a)))
          ((bv-zero? b) a)
          ((bv-zero? a) (mk-bvneg b))
          ((= a b) (bv-const 0 (term-width a)))
          (else (same-sort-app "bvsub" a b)))))
(define* mk-bvmul (subr cb-eff (int int) int)
  (lambda (a b)
    (cond ((both-const? a b) (bv-const (* (bv-value a) (bv-value b)) (term-width a)))
          ((bv-zero? a) a)
          ((bv-zero? b) b)
          ((bv-one? a) b)
          ((bv-one? b) a)
          ((bv-ones? a) (mk-bvneg b))
          ((bv-ones? b) (mk-bvneg a))
          (else (commute "bvmul" a b)))))

"Division by zero is as SMT-LIB says: bvudiv gives all ones, bvurem the
dividend."
(define* mk-bvudiv (subr cb-eff (int int) int)
  (lambda (a b)
    (cond ((both-const? a b)
           (if (= 0 (bv-value b)) (bv-const -1 (term-width a)) (bv-const (quotient (bv-value a) (bv-value b)) (term-width a))))
          ((bv-one? b) a)
          (else (same-sort-app "bvudiv" a b)))))
(define* mk-bvurem (subr cb-eff (int int) int)
  (lambda (a b)
    (cond ((both-const? a b) (if (= 0 (bv-value b)) a (bv-const (remainder (bv-value a) (bv-value b)) (term-width a))))
          ((bv-one? b) (bv-const 0 (term-width a)))
          ((bv-zero? b) a)
          ((= a b) (bv-const 0 (term-width a)))
          (else (same-sort-app "bvurem" a b)))))

"The sign bit of t, as a Boolean term."
(define* msb (subr cb-eff (int) int)
  (lambda (t) (let ((w (term-width t))) (mk-eq (mk-extract (- w 1) (- w 1) t) (bv-const 1 1)))))
(define* abs-term (subr cb-eff (int) int) (lambda (t) (mk-ite (msb t) (mk-bvneg t) t)))

"SMT-LIB's signed division, remainder and modulus, by cases on the signs;
the cases come to unsigned operations on absolute values."
(define* mk-bvsdiv (subr cb-eff (int int) int)
  (lambda (s t)
    (if (both-const? s t) (const-signed-div s t)
        (let ((q (mk-bvudiv (abs-term s) (abs-term t))))
          (mk-ite (mk-xor (msb s) (msb t)) (mk-bvneg q) q)))))
(define* mk-bvsrem (subr cb-eff (int int) int)
  (lambda (s t) (let ((r (mk-bvurem (abs-term s) (abs-term t)))) (mk-ite (msb s) (mk-bvneg r) r))))
(define* mk-bvsmod (subr cb-eff (int int) int)
  (lambda (s t)
    (let* ((u (mk-bvurem (abs-term s) (abs-term t))) (ms (msb s)) (mt (msb t)))
      (mk-ite (mk-eq u (bv-const 0 (term-width s))) u
              (mk-ite (mk-and2 (mk-not ms) (mk-not mt)) u
                      (mk-ite (mk-and2 ms (mk-not mt)) (mk-bvadd (mk-bvneg u) t)
                              (mk-ite (mk-and2 (mk-not ms) mt) (mk-bvadd u t) (mk-bvneg u))))))))
(define* const-signed-div (subr cb-eff (int int) int)
  (lambda (s t)
    (let* ((w (term-width s)) (a (to-signed (bv-value s) w)) (b (to-signed (bv-value t) w)))
      (if (= b 0) (bv-const (if (< a 0) 1 -1) w)
          ;; Truncating division.
          (bv-const (* (if (bool=? (< a 0) (< b 0)) 1 -1) (quotient (if (< a 0) (- 0 a) a) (if (< b 0) (- 0 b) b))) w)))))

;;; ------------------------------------------------------------ shifts
;;; By a constant, they are extract and concat.

(define* mk-bvshl (subr cb-eff (int int) int)
  (lambda (a b)
    (let ((w (term-width a)))
      (cond ((bv-const? b)
             (let ((k (bv-value b)))
               (cond ((= k 0) a) ((>= k w) (bv-const 0 w))
                     (else (mk-concat (mk-extract (- (- w 1) k) 0 a) (bv-const 0 k))))))
            ((bv-zero? a) a)
            (else (same-sort-app "bvshl" a b))))))
(define* mk-bvlshr (subr cb-eff (int int) int)
  (lambda (a b)
    (let ((w (term-width a)))
      (cond ((bv-const? b)
             (let ((k (bv-value b)))
               (cond ((= k 0) a) ((>= k w) (bv-const 0 w))
                     (else (mk-concat (bv-const 0 k) (mk-extract (- w 1) k a))))))
            ((bv-zero? a) a)
            (else (same-sort-app "bvlshr" a b))))))
(define* mk-bvashr (subr cb-eff (int int) int)
  (lambda (a b)
    (let ((w (term-width a)))
      (cond ((bv-const? b)
             (let ((k (min (bv-value b) (- w 1))))
               (if (= k 0) a (mk-sign-extend k (mk-extract (- w 1) k a)))))
            ((or (bv-zero? a) (bv-ones? a)) a)
            (else (same-sort-app "bvashr" a b))))))

;;; ------------------------------------------------------------ concatenation and extraction

(define mk-concat (subr cb-eff (int int) int)
  (lambda (a b)
    (let ((wa (term-width a)) (wb (term-width b)))
      (cond ((both-const? a b) (bv-const (+ (* (bv-value a) (expt2 wb)) (bv-value b)) (+ wa wb)))
            ;; Adjacent extracts of one term join.
            ((and (term-op? a "extract") (term-op? b "extract") (= (term-arg0 a) (term-arg0 b))
                  (= (term-param1 a) (+ 1 (term-param0 b))))
             (mk-extract (term-param0 a) (term-param1 b) (term-arg0 a)))
            (else (make-app "concat" nil (list a b) (+ wa wb)))))))

"Bits hi down to lo of t."
(define mk-extract (subr cb-eff (int int int) int)
  (lambda (hi lo t)
    (let ((w (term-width t)) (op (term-op t)))
      (cond ((and (= lo 0) (= hi (- w 1))) t)
            ((bv-const? t) (bv-const (quotient (bv-value t) (expt2 lo)) (+ 1 (- hi lo))))
            ((string=? op "extract")
             (let ((lo2 (term-param1 t))) (mk-extract (+ hi lo2) (+ lo lo2) (term-arg0 t))))
            ((string=? op "concat")
             (let* ((a (term-arg0 t)) (b (term-arg1 t)) (wb (term-width b)))
               (cond ((< hi wb) (mk-extract hi lo b))
                     ((>= lo wb) (mk-extract (- hi wb) (- lo wb) a))
                     (else (mk-concat (mk-extract (- hi wb) 0 a) (mk-extract (- wb 1) lo b))))))
            ((and (string=? op "sign_extend") (< hi (term-width (term-arg0 t)))) (mk-extract hi lo (term-arg0 t)))
            ((string=? op "bvnot") (mk-bvnot (mk-extract hi lo (term-arg0 t))))
            ((string=? op "bvand") (mk-bvand (mk-extract hi lo (term-arg0 t)) (mk-extract hi lo (term-arg1 t))))
            ((string=? op "bvor") (mk-bvor (mk-extract hi lo (term-arg0 t)) (mk-extract hi lo (term-arg1 t))))
            ((string=? op "bvxor") (mk-bvxor (mk-extract hi lo (term-arg0 t)) (mk-extract hi lo (term-arg1 t))))
            ((string=? op "ite") (mk-ite (term-arg0 t) (mk-extract hi lo (term-arg1 t)) (mk-extract hi lo (term-arg2 t))))
            (else (make-app "extract" (list hi lo) (list t) (+ 1 (- hi lo))))))))

(define* mk-zero-extend (subr cb-eff (int int) int) (lambda (k t) (if (= k 0) t (mk-concat (bv-const 0 k) t))))
(define mk-sign-extend (subr cb-eff (int int) int)
  (lambda (k t)
    (cond ((= k 0) t)
          ((bv-const? t) (bv-const (to-signed (bv-value t) (term-width t)) (+ k (term-width t))))
          ((term-op? t "sign_extend") (mk-sign-extend (+ k (term-param0 t)) (term-arg0 t)))
          (else (make-app "sign_extend" (list k) (list t) (+ k (term-width t)))))))
(define* mk-repeat (subr cb-eff (int int) int)
  (lambda (k t) (letrec ((go (subr cb-eff (int int) int) (lambda (i acc) (if (>= i k) acc (go (+ i 1) (mk-concat acc t))))))
                  (go 1 t))))
(define* mk-rotate-left (subr cb-eff (int int) int)
  (lambda (k t)
    (let* ((w (term-width t)) (k (modulo k w)))
      (if (= k 0) t (mk-concat (mk-extract (- (- w 1) k) 0 t) (mk-extract (- w 1) (- w k) t))))))
(define* mk-rotate-right (subr cb-eff (int int) int)
  (lambda (k t) (mk-rotate-left (- (term-width t) (modulo k (term-width t))) t)))

;;; ------------------------------------------------------------ comparisons

(define* mk-bvult (subr cb-eff (int int) int)
  (lambda (a b)
    (cond ((both-const? a b) (bool-term (< (bv-value a) (bv-value b))))
          ((= a b) (false-term))
          ((bv-zero? b) (false-term))
          ((bv-ones? a) (false-term))
          ((bv-zero? a) (mk-not (mk-eq b a)))
          (else (make-app "bvult" nil (list a b) bool-sort)))))
(define* mk-bvslt (subr cb-eff (int int) int)
  (lambda (a b)
    (cond ((both-const? a b) (let ((w (term-width a))) (bool-term (< (to-signed (bv-value a) w) (to-signed (bv-value b) w)))))
          ((= a b) (false-term))
          (else (make-app "bvslt" nil (list a b) bool-sort)))))
(define* mk-bvule (subr cb-eff (int int) int) (lambda (a b) (mk-not (mk-bvult b a))))
(define* mk-bvugt (subr cb-eff (int int) int) (lambda (a b) (mk-bvult b a)))
(define* mk-bvuge (subr cb-eff (int int) int) (lambda (a b) (mk-not (mk-bvult a b))))
(define* mk-bvsle (subr cb-eff (int int) int) (lambda (a b) (mk-not (mk-bvslt b a))))
(define* mk-bvsgt (subr cb-eff (int int) int) (lambda (a b) (mk-bvslt b a)))
(define* mk-bvsge (subr cb-eff (int int) int) (lambda (a b) (mk-not (mk-bvslt a b))))
(define* mk-bvcomp (subr cb-eff (int int) int)
  (lambda (a b) (mk-ite (mk-eq a b) (bv-const 1 1) (bv-const 0 1))))
