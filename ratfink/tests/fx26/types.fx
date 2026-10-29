;;; Specifications and harnesses over FX-26's types, each one's proof
;;; calling it on symbolic values of its parameters' types: bin/ratfink
;;; ratfink/tests/fx26/types.fx. One whose name ends -wrong claims what
;;; is false: its proof fails.
;;;
;;; A specification's propositions are of ints and bools (Fixpt's
;;; docs/fx26.md, Specifications); a value of another type is in one as
;;; the argument of a logic function (a pure global of an int's or bool's
;;; result). A harness asserts what it will.

;; Products.
(define-type point (productof (x int) (y int)))
(define px (subr pure ((p : point)) int) (lambda (p) (extract p x)))
(define py (subr pure ((p : point)) int) (lambda (p) (extract p y)))
(define swap (subr pure ((p : point)) point (ensures r (and (= (px r) (py p)) (= (py r) (px p)))))
  (lambda (p) (product (x (extract p y)) (y (extract p x)))))
(define swap-wrong (subr pure ((p : point)) point (ensures r (= (px r) (px p))))
  (lambda (p) (product (x (extract p y)) (y (extract p x)))))

;; Sums.
(define-type maybe-int (sumof (none unit) (some int)))
(define none? (subr pure ((o : maybe-int)) bool) (lambda (o) (tagcase o (none u #t) (else x #f))))
(define get-or (subr pure ((o : maybe-int) (d : int)) int (ensures r (implies (none? o) (= r d))))
  (lambda (o d) (tagcase o (some v v) (none u d))))
(define get-or-wrong (subr pure ((o : maybe-int) (d : int)) int (ensures r (= r d)))
  (lambda (o d) (tagcase o (some v v) (none u d))))

;; A recursive datatype: the proof's trees are of bounded depth.
(define-datatype tree (leaf) (node tree int tree))
(define size (subr (maxeff spin (read (globals size))) ((t : tree)) int (ensures r (>= r 0)))
  (lambda (t) (tagcase t (leaf () 0) (node (l v r) (+ 1 (+ (size l) (size r)))))))
(define size-wrong (subr (maxeff spin (read (globals size-wrong))) ((t : tree)) int (ensures r (> r 0)))
  (lambda (t) (tagcase t (leaf () 0) (node (l v r) (+ 1 (+ (size-wrong l) (size-wrong r)))))))

;; Lists of a datatype, through a family.
(define-type (forest (r region)) (listof tree r))
(define leaves (subr (maxeff spin (read (globals leaves))) ((f : (forest acyclic))) int (ensures r (>= r 0)))
  (lambda (f) (if (null? f) 0 (+ (tagcase (car f) (leaf () 1) (else t 0)) (leaves (cdr f))))))

;; mu.
(define-type ints (mu l (sumof (end unit) (more (productof (head int) (tail l))))))
(define total (subr (maxeff spin (read (globals total))) ((l : ints)) int)
  (lambda (l) (tagcase l (end u 0) (more p (+ (extract p head) (total (extract p tail)))))))
(define total-of-nats (subr (maxeff spin (read (globals total))) ((l : ints)) unit)
  (lambda (l)
    (letrec ((nats? (subr pure (ints) bool)
               (lambda (l) (tagcase l (end u #t) (more p (and (>= (extract p head) 0) (nats? (extract p tail))))))))
      (begin (assume (nats? l)) (assert (>= (total l) 0))))))
(define total-wrong (subr (maxeff spin (read (globals total))) ((l : ints)) unit)
  (lambda (l) (assert (>= (total l) 0))))

;; Strings, characters and symbols: a value is one the program writes, or
;; a few more.
(define len (subr pure ((s : string)) int) (lambda (s) (string-length s)))
(define yes? (subr pure ((s : string)) bool (ensures r (implies r (= (len s) 3))))
  (lambda (s) (string=? s "yes")))
(define yes-wrong (subr pure ((s : string)) bool (ensures r (not r)))
  (lambda (s) (string=? s "yes")))
(define digit-value (subr pure ((c : char)) int (ensures r (and (<= -1 r) (<= r 9))))
  (lambda (c) (if (and (char<=? #\0 c) (char<=? c #\9)) (- (char->integer c) (char->integer #\0)) -1)))
(define colour-code (subr pure ((s : symbol)) int (ensures r (<= r 2)))
  (lambda (s) (cond ((eq? s 'red) 0) ((eq? s 'green) 1) (else 2))))
(define colour-code-wrong (subr pure ((s : symbol)) int (ensures r (<= r 1)))
  (lambda (s) (cond ((eq? s 'red) 0) ((eq? s 'green) 1) (else 2))))

;; Integers of fixed width.
(define widen (subr pure ((x : i32)) int (ensures r (and (<= -2147483648 r) (< r 2147483648))))
  (lambda (x) x))
(define widen-wrong (subr pure ((x : u32)) int (ensures r (< r 65536)))
  (lambda (x) x))

;; Floats, pairs, arrays and refs, by harnesses.
(define magnitude (subr pure (f64) unit) (lambda (x) (assert (f64>= (f64-abs x) 0.0))))
(define magnitude-wrong (subr pure (f64) unit) (lambda (x) (assert (f64> (f64-abs x) 0.0))))
(define pair-sum (subr pure ((pairof int int acyclic)) unit)
  (lambda (p) (assert (= (+ (car p) (cdr p)) (+ (cdr p) (car p))))))
(define first-or (subr (read @heap) ((arrayof int @heap) int) unit)
  (lambda (a d)
    (let ((v (if (> (array-length a) 0) (array-ref a 0) d)))
      (assert (or (= v d) (= v (array-ref a 0)))))))
(define deref-wrong (subr (maxeff (read @heap) (write @heap)) ((ref int @heap)) unit)
  (lambda (b) (begin (set b (+ (get b) 1)) (assert (> (get b) 0)))))

(size (node (leaf) 1 (leaf)))
