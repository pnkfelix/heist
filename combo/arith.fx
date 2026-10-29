;;; arith.fx: integer and real terms, built by constructors that simplify,
;;; and kept linear and canonical (lockpick's `(lockpick arith)`).
;;;
;;; A linear term is a sum of monomials and a constant:
;;;   num (params: q, a rational, as numerator and denominator), of sort Int or Real
;;;   scale (params: c; argument x): c * x, for c not 0 or 1
;;;   + (m1 ... mk [num]): monomials in order of their variables' ids, then
;;;     the constant if it is not 0
;;; The "variables" of a linear term are the terms that are not sums,
;;; scalings or constants: declared variables, and also ite, div, mod,
;;; to_int and nonlinear products, which the arithmetic theory treats as
;;; variables with definitions. to_real is transparent: a linear term may
;;; mix integer and real variables.
;;;
;;; Atoms are (<= form k) and (>= form k), with form a linear term without
;;; a constant, whose first monomial has a positive coefficient; if all its
;;; variables are integers, its coefficients are integers without a common
;;; factor and k is rounded. Other comparisons are written with them:
;;; (< a b) is (not (>= a b)), (= a b) is (and (<= a b) (>= a b)).

(module-parameters ((m-sat (load-moduleof "sat.fx")) (m-rat (load-moduleof "rat.fx"))
                    (m-term (load-moduleof "term.fx" m-sat m-rat))))

(hide (define kit-lists (load-module "../kit/lists.fx"))
      (import kit-lists map filter)
      (define kit-numbers (load-module "../kit/numbers.fx"))
      (import kit-numbers gcd lcm))

(define* int-term? (subr cb-eff (int) bool) (lambda (t) (= (term-sort t) int-sort)))

(define* num (subr cb-eff (rat int) int)
  (lambda (q sort) (make-app "num" (list (rat-num q) (rat-den q)) nil sort)))
(define* num-int (subr cb-eff (int int) int) (lambda (n sort) (num (int->rat n) sort)))
(define* num? (subr cb-eff (int) bool) (lambda (t) (term-op? t "num")))
(define* num-value (subr cb-eff (int) rat)
  (lambda (t) (product (n (term-param0 t)) (d (term-param1 t)))))
(define* scale-coeff (subr cb-eff (int) rat)
  (lambda (t) (product (n (term-param0 t)) (d (term-param1 t)))))

;;; ------------------------------------------------------------ linear forms
;;; Monomials sorted by their variables' ids, no zero coefficients, and a
;;; constant.

(define-type mono (productof (x int) (c rat)))
(define-type monos (listof mono acyclic))
(define-type form (productof (ms monos) (k rat)))

(define* reverse-monos (subr spin (monos) monos)
  (lambda (l) (letrec ((go (subr spin (monos monos) monos) (lambda (l acc) (if (null? l) acc (go (cdr l) (cons (car l) acc))))))
                (go l nil))))

(define* linear-form (subr cb-eff (int) form)
  (lambda (t)
    (let ((op (term-op t)))
      (cond ((string=? op "num") (product (ms nil) (k (num-value t))))
            ((string=? op "scale") (product (ms (list (product (x (term-arg0 t)) (c (scale-coeff t))))) (k rat-0)))
            ((string=? op "+")
             (letrec ((go (subr cb-eff (ints monos rat) form)
                        (lambda (as ms k)
                          (if (null? as) (product (ms (reverse-monos ms)) (k k))
                              (let ((a (car as)))
                                (cond ((num? a) (go (cdr as) ms (rat+ k (num-value a))))
                                      ((term-op? a "scale") (go (cdr as) (cons (product (x (term-arg0 a)) (c (scale-coeff a))) ms) k))
                                      (else (go (cdr as) (cons (product (x a) (c rat-1)) ms) k))))))))
               (go (term-args t) nil rat-0)))
            ((string=? op "to_real") (linear-form (term-arg0 t)))
            (else (product (ms (list (product (x t) (c rat-1)))) (k rat-0)))))))

"The sum of two forms' monomials."
(define* form+ (subr cb-eff (monos monos) monos)
  (lambda (ms ns)
    (cond ((null? ms) ns)
          ((null? ns) ms)
          ((= (extract (car ms) x) (extract (car ns) x))
           (let ((c (rat+ (extract (car ms) c) (extract (car ns) c))))
             (if (rat-zero? c) (form+ (cdr ms) (cdr ns))
                 (cons (product (x (extract (car ms) x)) (c c)) (form+ (cdr ms) (cdr ns))))))
          ((< (extract (car ms) x) (extract (car ns) x)) (cons (car ms) (form+ (cdr ms) ns)))
          (else (cons (car ns) (form+ ms (cdr ns)))))))
(define* form-scale (subr cb-eff (rat monos) monos)
  (lambda (c ms)
    (if (rat-zero? c) nil
        (letrec ((go (subr cb-eff (monos) monos)
                   (lambda (ms) (if (null? ms) nil (cons (product (x (extract (car ms) x)) (c (rat* c (extract (car ms) c)))) (go (cdr ms)))))))
          (go ms)))))

(define* monomial (subr cb-eff (int rat int) int)
  (lambda (x c sort) (if (rat= c rat-1) x (make-app "scale" (list (rat-num c) (rat-den c)) (list x) sort))))

"The term of a form and constant."
(define* linear-term (subr cb-eff (monos rat int) int)
  (lambda (ms k sort)
    (cond ((null? ms) (num k sort))
          ((and (null? (cdr ms)) (rat-zero? k)) (monomial (extract (car ms) x) (extract (car ms) c) sort))
          (else
           (letrec ((go (subr cb-eff (monos) ints)
                      (lambda (ms) (if (null? ms) (if (rat-zero? k) nil (list (num k sort)))
                                       (let ((m (monomial (extract (car ms) x) (extract (car ms) c) sort))) (cons m (go (cdr ms))))))))
             (make-app "+" nil (go ms) sort))))))

(define* sum-sort (subr cb-eff (ints) int)
  (lambda (ts) (if (letrec ((go (subr cb-eff (ints) bool) (lambda (l) (and (pair? l) (or (= (term-sort (car l)) real-sort) (go (cdr l)))))))
                     (go ts))
                   real-sort int-sort)))

;;; ------------------------------------------------------------ arithmetic

(define* mk-add (subr cb-eff (ints) int)
  (lambda (ts)
    (letrec ((go (subr cb-eff (ints monos rat) int)
               (lambda (as ms k)
                 (if (null? as) (linear-term ms k (sum-sort ts))
                     (let ((f (linear-form (car as)))) (go (cdr as) (form+ ms (extract f ms)) (rat+ k (extract f k))))))))
      (go ts nil rat-0))))
(define* mk-neg (subr cb-eff (int) int) (lambda (t) (mk-mul (list (num-int -1 (term-sort t)) t))))
(define* mk-sub (subr cb-eff (int ints) int)
  (lambda (t ts) (if (null? ts) (mk-neg t) (mk-add (cons t (the ints (map mk-neg ts)))))))

"Products: linear if all factors but one are constants; otherwise a
nonlinear product, which the theory does not handle."
(define mk-mul (subr cb-eff (ints) int)
  (lambda (ts)
    (let* ((sort (sum-sort ts))
           (consts (the ints (filter (lambda ((t int)) (term-op? t "num")) ts)))
           (others (the ints (filter (lambda ((t int)) (not (term-op? t "num"))) ts)))
           (c (letrec ((go (subr cb-eff (ints rat) rat) (lambda (l c) (if (null? l) c (go (cdr l) (rat* c (num-value (car l))))))))
                (go consts rat-1))))
      (cond ((null? others) (num c sort))
            ((rat-zero? c) (num rat-0 sort))
            ((null? (cdr others))
             (let ((f (linear-form (car others)))) (linear-term (form-scale c (extract f ms)) (rat* c (extract f k)) sort)))
            (else
             (let ((p (make-app "*" nil (list-sort-terms others) sort)))
               (if (rat= c rat-1) p (linear-term (list (product (x p) (c c))) rat-0 sort))))))))

"Real division: by a constant only (else a nonlinear term)."
(define* mk-div-real (subr cb-eff (int int) int)
  (lambda (a b)
    (if (and (num? b) (not (rat-zero? (num-value b))))
        (mk-mul (list (num (rat/ rat-1 (num-value b)) real-sort) a))
        (make-app "/" nil (list a b) real-sort))))

"SMT-LIB's integer div and mod: a = b * (div a b) + (mod a b),
0 <= (mod a b) < |b|."
(define* mk-idiv (subr cb-eff (int int) int)
  (lambda (a b)
    (cond ((and (num? a) (num? b) (not (rat-zero? (num-value b))))
           (num-int (euclid-div (rat-num (num-value a)) (rat-num (num-value b))) int-sort))
          ((and (num? b) (rat= (num-value b) rat-1)) a)
          (else (make-app "div" nil (list a b) int-sort)))))
(define* mk-imod (subr cb-eff (int int) int)
  (lambda (a b)
    (cond ((and (num? a) (num? b) (not (rat-zero? (num-value b))))
           (let ((x (rat-num (num-value a))) (y (rat-num (num-value b))))
             (num-int (- x (* y (euclid-div x y))) int-sort)))
          ((and (num? b) (rat= (rat-abs (num-value b)) rat-1)) (num rat-0 int-sort))
          (else (make-app "mod" nil (list a b) int-sort)))))

(define* mk-abs (subr cb-eff (int) int)
  (lambda (t)
    (if (num? t) (num (rat-abs (num-value t)) (term-sort t))
        (mk-ite (mk-ge t (num rat-0 (term-sort t))) t (mk-neg t)))))
(define* mk-to-real (subr cb-eff (int) int)
  (lambda (t)
    (cond ((= (term-sort t) real-sort) t)
          ((num? t) (num (num-value t) real-sort))
          (else (make-app "to_real" nil (list t) real-sort)))))
(define* mk-to-int (subr cb-eff (int) int)
  (lambda (t)
    (cond ((= (term-sort t) int-sort) t)
          ((num? t) (num-int (rat-floor (num-value t)) int-sort))
          ((term-op? t "to_real") (term-arg0 t))
          (else (make-app "to_int" nil (list t) int-sort)))))
(define* mk-is-int (subr cb-eff (int) int)
  (lambda (t) (if (= (term-sort t) int-sort) (true-term) (mk-arith-eq t (mk-to-real (mk-to-int t))))))

;;; ------------------------------------------------------------ atoms

(define* atom? (subr cb-eff (int) bool) (lambda (t) (or (term-op? t "<=") (term-op? t ">="))))
(define* atom-form (subr cb-eff (int) int) (lambda (t) (term-arg0 t)))
(define* atom-bound (subr cb-eff (int) rat) (lambda (t) (num-value (term-arg1 t))))

(define* all-int? (subr cb-eff (monos) bool)
  (lambda (ms) (or (null? ms) (and (int-term? (extract (car ms) x)) (all-int? (cdr ms))))))

"The atom ms op k (op \"<=\" or \">=\"), normalized."
(define* make-atom (subr cb-eff (string monos rat) int)
  (lambda (op ms k)
    (if (null? ms)
        (bool-term (if (string=? op "<=") (rat<= rat-0 k) (rat<= k rat-0)))
        (let* ((int? (all-int? ms))
               ;; Scale: integers without a common factor, or a leading 1.
               (scale (if int?
                          (let ((l (letrec ((go (subr cb-eff (monos int) int) (lambda (ms l) (if (null? ms) l (go (cdr ms) (lcm l (rat-den (extract (car ms) c))))))))
                                     (go ms 1))))
                            (let ((g (letrec ((go (subr cb-eff (monos int) int)
                                                (lambda (ms g) (if (null? ms) g (go (cdr ms) (gcd g (rat-num (rat* (int->rat l) (extract (car ms) c)))))))))
                                       (go ms 0))))
                              (make-rat l g)))
                          (rat/ rat-1 (rat-abs (extract (car ms) c)))))
               (scale (if (< (rat-sign (extract (car ms) c)) 0) (rat-neg scale) scale))
               (op (if (< (rat-sign scale) 0) (if (string=? op "<=") ">=" "<=") op))
               (ms (form-scale scale ms))
               (k (rat* scale k))
               (k (if int? (int->rat (if (string=? op "<=") (rat-floor k) (rat-ceiling k))) k))
               (sort (if int? int-sort real-sort)))
          (make-app op nil (list (linear-term ms rat-0 sort) (num k sort)) bool-sort)))))

"a op b, as (a - b) op 0."
(define* compare (subr cb-eff (string int int) int)
  (lambda (op a b)
    (let ((fa (linear-form a)) (fb (linear-form b)))
      (make-atom op (form+ (extract fa ms) (form-scale (rat-neg rat-1) (extract fb ms))) (rat- (extract fb k) (extract fa k))))))
(define mk-le (subr cb-eff (int int) int) (lambda (a b) (compare "<=" a b)))
(define mk-ge (subr cb-eff (int int) int) (lambda (a b) (compare ">=" a b)))
(define* mk-lt (subr cb-eff (int int) int) (lambda (a b) (mk-not (mk-ge a b))))
(define* mk-gt (subr cb-eff (int int) int) (lambda (a b) (mk-not (mk-le a b))))
(define mk-arith-eq (subr cb-eff (int int) int) (lambda (a b) (mk-and2 (mk-le a b) (mk-ge a b))))
(define* mk-arith-distinct (subr cb-eff (ints) int)
  (lambda (ts)
    (letrec ((go (subr cb-eff (ints ints) int)
               (lambda (ts acc)
                 (if (null? ts) (mk-and acc)
                     (go (cdr ts) (the ints (append (the ints (map (lambda ((u int)) (mk-not (mk-arith-eq (car ts) u))) (cdr ts))) acc)))))))
      (go ts nil))))
