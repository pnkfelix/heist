;;; rat.fx: exact rationals, over FX-26's `int` (a bignum where it must
;;; be), as Scheme's exact numbers serve lockpick: a numerator and a
;;; positive denominator without a common factor.

(define-type rat (productof (n int) (d int)))

(hide (define kit-numbers (load-module "../kit/numbers.fx"))
      (import kit-numbers gcd lcm))

"n/d, made canonical (d not 0)."
(define* make-rat (subr spin (int int) rat)
  (lambda (n d)
    (let* ((g (gcd n d)) (g (if (< d 0) (- 0 g) g)))
      (if (= g 1) (product (n n) (d d)) (product (n (quotient n g)) (d (quotient d g)))))))
(define* int->rat (subr pure (int) rat) (lambda (n) (product (n n) (d 1))))
(define rat-0 rat (product (n 0) (d 1)))
(define rat-1 rat (product (n 1) (d 1)))
(define* rat-num (subr pure (rat) int) (lambda (q) (extract q n)))
(define* rat-den (subr pure (rat) int) (lambda (q) (extract q d)))

(define* rat+ (subr spin (rat rat) rat)
  (lambda (a b)
    (if (and (= (extract a d) 1) (= (extract b d) 1)) (int->rat (+ (extract a n) (extract b n)))
        (make-rat (+ (* (extract a n) (extract b d)) (* (extract b n) (extract a d))) (* (extract a d) (extract b d))))))
(define* rat-neg (subr pure (rat) rat) (lambda (a) (product (n (- 0 (extract a n))) (d (extract a d)))))
(define* rat- (subr spin (rat rat) rat) (lambda (a b) (rat+ a (rat-neg b))))
(define* rat* (subr spin (rat rat) rat)
  (lambda (a b)
    (if (and (= (extract a d) 1) (= (extract b d) 1)) (int->rat (* (extract a n) (extract b n)))
        (make-rat (* (extract a n) (extract b n)) (* (extract a d) (extract b d))))))
"a/b (b not 0)."
(define* rat/ (subr spin (rat rat) rat)
  (lambda (a b) (make-rat (* (extract a n) (extract b d)) (* (extract a d) (extract b n)))))
(define* rat-abs (subr pure (rat) rat) (lambda (a) (if (< (extract a n) 0) (rat-neg a) a)))
(define* rat-sign (subr pure (rat) int) (lambda (a) (cond ((< (extract a n) 0) -1) ((> (extract a n) 0) 1) (else 0))))
(define* rat-zero? (subr pure (rat) bool) (lambda (a) (= (extract a n) 0)))
(define* rat-int? (subr pure (rat) bool) (lambda (a) (= (extract a d) 1)))
(define* rat= (subr pure (rat rat) bool) (lambda (a b) (and (= (extract a n) (extract b n)) (= (extract a d) (extract b d)))))
(define* rat< (subr pure (rat rat) bool)
  (lambda (a b) (< (* (extract a n) (extract b d)) (* (extract b n) (extract a d)))))
(define* rat<= (subr pure (rat rat) bool) (lambda (a b) (not (rat< b a))))
(define* rat-max (subr pure (rat rat) rat) (lambda (a b) (if (rat< a b) b a)))
(define* rat-min (subr pure (rat rat) rat) (lambda (a b) (if (rat< b a) b a)))
"The greatest integer not above n/d (d > 0)."
(define* floor-div (subr pure (int int) int)
  (lambda (n d) (if (>= n 0) (quotient n d) (- 0 (quotient (- (+ (- 0 n) d) 1) d)))))
(define* rat-floor (subr pure (rat) int) (lambda (a) (floor-div (extract a n) (extract a d))))
(define* rat-ceiling (subr pure (rat) int) (lambda (a) (- 0 (floor-div (- 0 (extract a n)) (extract a d)))))
(define* rat-int (subr pure (int) rat) (lambda (n) (int->rat n)))
"SMT-LIB's integer division: a = b (div a b) + (mod a b), 0 <= mod < |b|."
(define* euclid-div (subr pure (int int) int)
  (lambda (a b) (if (> b 0) (floor-div a b) (- 0 (floor-div a (- 0 b))))))
(define* expt2 (subr spin (int) int) (lambda (k) (arithmetic-shift 1 k)))
(define* rat->string (subr pure (rat) string)
  (lambda (a) (if (= (extract a d) 1) (int->string (extract a n))
                  (string-append (int->string (extract a n)) (string-append "/" (int->string (extract a d)))))))
