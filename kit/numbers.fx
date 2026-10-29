;;; numbers.fx: kit's exact-integer procedures -- R7RS's, and SRFI 151's
;;; integer-length, over FX-26's `int` (a bignum where it must be). Fixpt's
;;; own: `quotient`, `remainder`, `modulo` (= floor-remainder), `max`,
;;; `min`, `arithmetic-shift`, the bitwise operations, `int->string`.
;;;
;;; A module file of no state: (define numbers (load-module "kit/numbers.fx")).

"|n|."
(define abs (subr pure (int) int) (lambda (n) (if (< n 0) (- 0 n) n)))

;; A loop that halves a number, or takes a remainder by it, is not one the
;; checkers see end; each here is given fuel too, which it never runs out
;; of: `bit-bound`, more than the bits of |n| (a decimal digit is less than
;; four bits), so that it is `pure`.
(define bit-bound (subr pure (int) int)
  (lambda (n) (+ 4 (* 4 (string-length (int->string n))))))

"The greatest common divisor of `a` and `b`, not negative; (gcd 0 0) is 0."
(define gcd (subr pure (int int) int)
  (lambda (a b)
    (letrec ((go (subr pure (int int int) int)
               ;; Euclid's, by remainders, not halving: but the remainder at
               ;; least halves every two steps (b mod (a mod b) < b/2), so
               ;; there are fewer than twice b's bits (Lamé: at most five
               ;; times its decimal digits), and the fuel never runs out.
               (lambda (a b fuel) (if (or (<= b 0) (<= fuel 0)) a (go b (remainder a b) (- fuel 1))))))
      (go (abs a) (abs b) (* 2 (bit-bound b))))))

"The least common multiple of `a` and `b`, not negative; 0 if either is."
(define lcm (subr pure (int int) int)
  (lambda (a b) (if (or (= a 0) (= b 0)) 0 (abs (* (quotient a (gcd a b)) b)))))

"R7RS's floor/: the quotient rounded toward negative infinity (b not 0)."
(define floor-quotient (subr pure (int int) int)
  (lambda (a b)
    (let ((q (quotient a b)))
      (if (and (not (= (remainder a b) 0)) (not (bool=? (< a 0) (< b 0)))) (- q 1) q))))
"Its remainder, of `b`'s sign: Fixpt's `modulo`."
(define floor-remainder (subr pure (int int) int) (lambda (a b) (modulo a b)))
"R7RS's truncate/: Fixpt's `quotient` and `remainder`."
(define truncate-quotient (subr pure (int int) int) (lambda (a b) (quotient a b)))
(define truncate-remainder (subr pure (int int) int) (lambda (a b) (remainder a b)))

"`b` to the power `k` (k >= 0; an error else), by squaring."
(define expt (subr pure (int int) int)
  (lambda (b k)
    (letrec ((go (subr pure (int int int int) int)
               ;; acc · base^k is the answer.
               (lambda (base k acc fuel)
                 (cond ((or (<= k 0) (<= fuel 0)) acc)
                       ((= (remainder k 2) 1) (go (* base base) (quotient k 2) (* acc base) (- fuel 1)))
                       (else (go (* base base) (quotient k 2) acc (- fuel 1)))))))
      (if (< k 0) (error "expt: negative exponent") (go b k 1 (bit-bound k))))))

"SRFI 151's integer-length: the bits `n` needs, its sign aside (that of
-n-1 for a negative n): 0 for 0 and -1, 3 for 7 and -8."
(define integer-length (subr pure (int) int)
  (lambda (n)
    (letrec ((go (subr pure (int int int) int)
               (lambda (m k fuel) (if (or (<= m 0) (<= fuel 0)) k (go (arithmetic-shift m -1) (+ k 1) (- fuel 1))))))
      (let ((m (if (< n 0) (- -1 n) n))) (go m 0 (bit-bound m))))))

"R7RS's exact-integer-sqrt, of n >= 0 (an error else): the greatest `s`
whose square is at most `n`, and `n` - s², the rest."
(define exact-integer-sqrt (subr pure (int) (productof (s int) (rest int)))
  (lambda (n)
    (if (< n 0) (error "exact-integer-sqrt: negative")
        (let ((s (if (< n 2) n
                     ;; Newton's, from a power of two above the root: falls
                     ;; to the root and stops.
                     (letrec ((go (subr pure (int int) int)
                                (lambda (x fuel)
                                  (let ((y (arithmetic-shift (+ x (quotient n x)) -1)))
                                    (if (or (>= y x) (<= fuel 0)) x (go y (- fuel 1)))))))
                       (go (arithmetic-shift 1 (+ 1 (arithmetic-shift (integer-length n) -1))) (integer-length n))))))
          (product (s s) (rest (- n (* s s))))))))

"The digits of a radix, as `number->string` writes them."
(define digit-chars string "0123456789abcdefghijklmnopqrstuvwxyz")

"`n` in `radix` (2 to 36; an error else), its letters lower case, as R7RS's
number->string writes an exact integer."
(define number->string (subr pure (int int) string)
  (lambda (n radix)
    (cond ((or (< radix 2) (> radix 36)) (error "number->string: radix not 2 to 36"))
          ((= radix 10) (int->string n))
          (else
           (letrec ((go (subr pure (int (listof char acyclic) int) (listof char acyclic))
                      (lambda (m acc fuel)
                        (let ((acc (the (listof char acyclic) (cons (string-ref digit-chars (remainder m radix)) acc))))
                          (if (or (< m radix) (<= fuel 0)) acc (go (quotient m radix) acc (- fuel 1)))))))
             (let ((m (abs n)))
               (string-append (if (< n 0) "-" "") (list->string (go m nil (bit-bound m))))))))))

"The value of digit `c` in `radix` (0-9, then a-z or A-Z), or #f."
(define radix-digit (subr pure (char int) (union false nat))
  (lambda (c radix)
    (let* ((k (char->integer c))
           (d (cond ((and (>= k 48) (<= k 57)) (- k 48))
                    ((and (>= k 97) (<= k 122)) (- k 87))
                    ((and (>= k 65) (<= k 90)) (- k 55))
                    (else 99))))
      (if (< d radix) (confirm-nat d (n n) #f) #f))))

"The integer `s` writes in `radix` (2 to 36): an optional sign, then one
digit or more; #f if it is not one. (R7RS's string->number, for exact
integers, with no prefix.)"
(define string->integer (subr pure (string int) (union false int))
  (lambda (s radix)
    (let* ((n (string-length s))
           (sign (if (and (> n 0) (or (char=? (string-ref s 0) #\-) (char=? (string-ref s 0) #\+))) 1 0)))
      (letrec ((go (subr pure (int int) (union false int))
                 (lambda (i acc)
                   (if (>= i n) (if (and (= sign 1) (char=? (string-ref s 0) #\-)) (- 0 acc) acc)
                       (let ((d (radix-digit (string-ref s i) radix)))
                         (if (bool? d) #f (go (+ i 1) (+ (* acc radix) d))))))))
        (if (or (< radix 2) (> radix 36) (<= n sign)) #f (go sign 0))))))

"2^k as a float, k an integer whose power is a normal float or 0 or
infinity."
(define two-to (subr pure (int) f64) (lambda (k) (f64-expt 2.0 (int->f64 k))))

"n/d (d not 0) as the nearest float, ties to even (R7RS's inexact of an
exact ratio): exact, as both fit in 53 bits, by one division; else the
quotient to 55 bits or 56, rounded to 53 by the bits below and the
remainder, then scaled. Correctly rounded where the result is a normal
float; a result in the subnormal range is rounded twice."
(define ratio->f64 (subr pure (int int) f64)
  (lambda (n0 d0)
    (let* ((neg (not (bool=? (< n0 0) (< d0 0)))) (n (abs n0)) (d (abs d0)))
      (cond ((= d 0) (error "ratio->f64: zero denominator"))
            ((= n 0) (if neg (f64-neg 0.0) 0.0))
            ((and (< (integer-length n) 54) (< (integer-length d) 54))
             (let ((x (f64/ (int->f64 n) (int->f64 d)))) (if neg (f64-neg x) x)))
            (else
             (let* ((s (- 55 (- (integer-length n) (integer-length d))))
                    (num (if (>= s 0) (arithmetic-shift n s) n))
                    (den (if (>= s 0) d (arithmetic-shift d (- 0 s))))
                    (q (quotient num den))
                    (r (remainder num den))
                    (extra (- (integer-length q) 53))
                    (m (arithmetic-shift q (- 0 extra)))
                    (low (- q (arithmetic-shift m extra)))
                    (half (arithmetic-shift 1 (- extra 1)))
                    (up (or (> low half) (and (= low half) (or (> r 0) (= (remainder m 2) 1)))))
                    (x (f64* (int->f64 (if up (+ m 1) m)) (two-to (- extra s)))))
               (if neg (f64-neg x) x)))))))
