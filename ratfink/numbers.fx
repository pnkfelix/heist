;;; numbers.fx: concrete numbers, as Larceny computes them -- exact
;;; integers, exact ratios, flonums -- for what shakedown leaves to
;;; Larceny's own arithmetic (on concrete numbers) and its reader. Complex
;;; numbers are not here: what would make one is an error.
;;;
;;; Measured on shakedown's Larceny (2026-10-29): (/ 6 4) is 3/2, (max 1
;;; 2.0) 2.0, (sqrt 4) 2, (sqrt 1/4) 1/2, (exp 0) 1.0, (expt 2 -1) 1/2,
;;; (expt 4 1/2) 2.0, (round 2.5) 2.0, (round 7/2) 4.

(module-parameters ((m-core (load-moduleof "core.fx"))))

(define iabs-n (subr rf-st (int) int) (lambda (i) (if (< i 0) (- 0 i) i)))
(define gcd (subr rf-st (int int) int)
  (lambda (a b) (let ((a (iabs-n a)) (b (iabs-n b))) (if (= b 0) a (gcd b (remainder a b))))))
"n/d in lowest terms, an integer if d divides n (d is not 0)."
(define make-ratio (subr rf-st (int int) rf-value)
  (lambda (n d)
    (let* ((g (gcd n d)) (s (if (< d 0) -1 1)) (n (quotient (* s n) g)) (d (quotient (* s d) g)))
      (if (= d 1) (rf-int n) (sum ratio (product (num n) (den d)))))))
(define num-of (subr rf-st (rf-value) int) (lambda (v) (tagcase v (int i i) (ratio q (extract q num)) (else x 0))))
(define den-of (subr rf-st (rf-value) int) (lambda (v) (tagcase v (ratio q (extract q den)) (else x 1))))
(define exact? (subr rf-st (rf-value) bool) (lambda (v) (tagcase v (int i #t) (ratio q #t) (else x #f))))
(define real? (subr rf-st (rf-value) bool) (lambda (v) (tagcase v (real r #t) (else x #f))))
"A number as a flonum."
(define ->flonum (subr rf-st (rf-value) f64)
  (lambda (v) (tagcase v (int i (int->f64 i)) (ratio q (ratio->f64 (extract q num) (extract q den))) (real r r) (else x 0.0))))
"n/d as the nearest flonum (n, d bignums perhaps)."
(define ratio->f64 (subr rf-st (int int) f64)
  (lambda (n d)
    ;; Scale so that the quotient has 64 bits or more, divide exactly in
    ;; integers, and let int->f64 round; then scale back by powers of 2.
    (let* ((neg (< n 0)) (n (iabs-n n))
           (shift (- (+ 64 (bit-length d)) (bit-length n)))
           (q (if (> shift 0) (quotient (arithmetic-shift n shift) d) (quotient n (arithmetic-shift d (- 0 shift)))))
           (f (f64* (int->f64 q) (f64-expt 2.0 (int->f64 (- 0 shift))))))
      (if neg (f64-neg f) f))))
(define bit-length (subr rf-st (int) int)
  (lambda (n) (if (<= n 0) 0 (+ 1 (bit-length (arithmetic-shift n -1))))))

"A flonum's exact value (it is finite)."
(define f64->exact (subr rf-st (f64) rf-value)
  (lambda (x)
    (let* ((bits (f64->bits x))
           (b (u64->int bits))
           (neg (>= b 9223372036854775808))
           (e (bitwise-and (arithmetic-shift b -52) 2047))
           (m (bitwise-and b 4503599627370495))
           (mant (if (= e 0) m (+ m 4503599627370496)))
           (exp (if (= e 0) -1074 (- e 1075)))
           (mag (if (>= exp 0) (rf-int (arithmetic-shift mant exp)) (make-ratio mant (arithmetic-shift 1 (- 0 exp))))))
      (if neg (num-neg mag) mag))))

;;; ------------------------------------------------------------ arithmetic

(define num-neg (subr rf-st (rf-value) rf-value)
  (lambda (a) (tagcase a (int i (rf-int (- 0 i))) (ratio q (make-ratio (- 0 (extract q num)) (extract q den))) (real r (sum real (f64-neg r))) (else x a))))
(define num-add (subr rf-st (rf-value rf-value) rf-value)
  (lambda (a b)
    (cond ((or (real? a) (real? b)) (sum real (f64+ (->flonum a) (->flonum b))))
          ((and (rf-exact-integer? a) (rf-exact-integer? b)) (rf-int (+ (rf-int-of a) (rf-int-of b))))
          (else (make-ratio (+ (* (num-of a) (den-of b)) (* (num-of b) (den-of a))) (* (den-of a) (den-of b)))))))
(define num-sub (subr rf-st (rf-value rf-value) rf-value)
  (lambda (a b)
    (cond ((or (real? a) (real? b)) (sum real (f64- (->flonum a) (->flonum b))))
          ((and (rf-exact-integer? a) (rf-exact-integer? b)) (rf-int (- (rf-int-of a) (rf-int-of b))))
          (else (make-ratio (- (* (num-of a) (den-of b)) (* (num-of b) (den-of a))) (* (den-of a) (den-of b)))))))
(define num-mul (subr rf-st (rf-value rf-value) rf-value)
  (lambda (a b)
    (cond ((or (real? a) (real? b)) (sum real (f64* (->flonum a) (->flonum b))))
          ((and (rf-exact-integer? a) (rf-exact-integer? b)) (rf-int (* (rf-int-of a) (rf-int-of b))))
          (else (make-ratio (* (num-of a) (num-of b)) (* (den-of a) (den-of b)))))))
"a / b; b is not an exact 0 (the caller checks)."
(define num-div (subr rf-st (rf-value rf-value) rf-value)
  (lambda (a b)
    (cond ((or (real? a) (real? b)) (sum real (f64/ (->flonum a) (->flonum b))))
          (else (make-ratio (* (num-of a) (den-of b)) (* (den-of a) (num-of b)))))))
"-1, 0 or 1 as a < b, a = b, a > b; for NaN, 2."
(define num-compare (subr rf-st (rf-value rf-value) int)
  (lambda (a b)
    (cond ((or (real? a) (real? b))
           (let ((x (->flonum a)) (y (->flonum b)))
             (cond ((f64< x y) -1) ((f64> x y) 1) ((f64= x y) 0) (else 2))))
          (else (let ((l (* (num-of a) (den-of b))) (r (* (num-of b) (den-of a))))
                  (cond ((< l r) -1) ((> l r) 1) (else 0)))))))
(define num-zero? (subr rf-st (rf-value) bool) (lambda (a) (= 0 (num-compare a (rf-int 0)))))
(define num-sign (subr rf-st (rf-value) int) (lambda (a) (num-compare a (rf-int 0))))
"An exact value made inexact if inexact? (the contagion of max and min)."
(define inexact-if (subr rf-st (bool rf-value) rf-value)
  (lambda (inexact? v) (if (and inexact? (exact? v)) (sum real (->flonum v)) v)))
(define num-max (subr rf-st (rf-value rf-value) rf-value)
  (lambda (a b) (inexact-if (or (real? a) (real? b)) (if (< (num-compare a b) 0) b a))))
(define num-min (subr rf-st (rf-value rf-value) rf-value)
  (lambda (a b) (inexact-if (or (real? a) (real? b)) (if (> (num-compare a b) 0) b a))))
(define num-abs (subr rf-st (rf-value) rf-value) (lambda (a) (if (< (num-sign a) 0) (num-neg a) a)))
(define num-integer? (subr rf-st (rf-value) bool)
  (lambda (v) (tagcase v (int i #t) (real r (and (f64-finite? r) (f64= r (f64-floor r)))) (else x #f))))
(define num-exact (subr rf-st (rf-value) rf-value)
  (lambda (v) (tagcase v (real r (f64->exact r)) (else x v))))
(define num-inexact (subr rf-st (rf-value) rf-value) (lambda (v) (sum real (->flonum v))))

"Rounding: kind 0 floor, 1 ceiling, 2 round (to even), 3 truncate."
(define num-round (subr rf-st (int rf-value) rf-value)
  (lambda (kind v)
    (tagcase v
      (real r (sum real (cond ((= kind 0) (f64-floor r)) ((= kind 1) (f64-ceiling r)) ((= kind 2) (f64-round r)) (else (f64-truncate r)))))
      (ratio q
        (let* ((n (extract q num)) (d (extract q den))
               (fl (floor-div n d)))
          (rf-int
           (cond ((= kind 0) fl)
                 ((= kind 1) (+ fl 1))
                 ((= kind 3) (if (< n 0) (+ fl 1) fl))
                 (else (let ((twice (- (* 2 n) (* 2 (* d fl)))))
                         (cond ((< twice d) fl) ((> twice d) (+ fl 1)) ((= 0 (modulo fl 2)) fl) (else (+ fl 1)))))))))
      (else x v))))
(define floor-div (subr rf-st (int int) int)
  (lambda (n d) (let ((q (quotient n d))) (if (and (not (= (* q d) n)) (not (eq? (< n 0) (< d 0)))) (- q 1) q))))

"Integer division of concrete integers (exact or inexact integral)."
(define int-op (subr rf-st ((subr rf-st (int int) int) rf-value rf-value) rf-value)
  (lambda (op a b)
    (let ((r (op (rf-int-of (num-exact a)) (rf-int-of (num-exact b)))))
      (if (or (real? a) (real? b)) (sum real (int->f64 r)) (rf-int r)))))

"base^n for an exact integer n."
(define num-expt-int (subr rf-st (rf-value int) rf-value)
  (lambda (base n)
    (letrec ((pow (subr rf-st (rf-value int) rf-value)
               (lambda (b k) (cond ((= k 0) (if (real? b) (sum real 1.0) (rf-int 1)))
                                   ((= 0 (modulo k 2)) (let ((h (pow b (quotient k 2)))) (num-mul h h)))
                                   (else (num-mul b (pow b (- k 1))))))))
      (if (< n 0) (num-div (rf-int 1) (pow base (- 0 n))) (pow base n)))))
(define num-expt (subr rf-st (rf-value rf-value) rf-value)
  (lambda (base n)
    (tagcase n
      (int k (if (and (num-zero? base) (< k 0)) (sum real (f64/ 1.0 0.0)) (num-expt-int base k)))
      (else x (sum real (f64-expt (->flonum base) (->flonum n)))))))

"The exact integer square root of n >= 0."
(define isqrt (subr rf-st (int) int)
  (lambda (n)
    (if (< n 2) n
        (letrec ((go (subr rf-st (int) int)
                   (lambda (x) (let ((y (quotient (+ x (quotient n x)) 2))) (if (>= y x) x (go y))))))
          (go n)))))
"sqrt of a non-negative number: exact where the root is."
(define num-sqrt (subr rf-st (rf-value) rf-value)
  (lambda (v)
    (tagcase v
      (int i (let ((r (isqrt i))) (if (= (* r r) i) (rf-int r) (sum real (f64-sqrt (int->f64 i))))))
      (ratio q (let ((a (isqrt (extract q num))) (b (isqrt (extract q den))))
                 (if (and (= (* a a) (extract q num)) (= (* b b) (extract q den))) (make-ratio a b) (sum real (f64-sqrt (->flonum v))))))
      (else x (sum real (f64-sqrt (->flonum v)))))))
