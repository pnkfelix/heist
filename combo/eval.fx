;;; eval.fx: the value of a term, given the values of its variables
;;; (lockpick's `(lockpick eval)`). Used for get-value, and to check
;;; models against the assertions.
;;;
;;; Values are rationals: Bool 1 or 0, integers for Int and for bitvectors
;;; (unsigned, below 2^width), rationals for Real.

(module-parameters ((m-sat (load-moduleof "sat.fx")) (m-rat (load-moduleof "rat.fx"))
                    (m-term (load-moduleof "term.fx" m-sat m-rat))))

"The value a variable that nothing constrains takes, as z3 gives: false,
or 0."
(define* default-value (subr pure (int) rat) (lambda (sort) rat-0))
(define* rat-bool (subr pure (bool) rat) (lambda (b) (if b rat-1 rat-0)))
(define* rat-true? (subr pure (rat) bool) (lambda (q) (not (rat-zero? q))))

"The value of `t`, where `(var-value v)` is the value of variable v."
(define* eval-term (subr cb-eff (int (subr cb-eff (int) rat)) rat)
  (lambda (t var-value)
    (let ((memo (the (arrayof rat @cb) (make-array (term-count) rat-0)))
          (done (the (arrayof bool @cb) (make-array (term-count) #f))))
      (letrec ((ev (subr cb-eff (int) rat)
                 (lambda (t)
                   (if (array-ref done t) (array-ref memo t)
                       (let ((v (eval-op t (term-op t) ev var-value)))
                         (begin (array-set! memo t v) (array-set! done t #t) v))))))
        (ev t)))))

(define* eval-op (subr cb-eff (int string (subr cb-eff (int) rat) (subr cb-eff (int) rat)) rat)
  (lambda (t op ev var-value)
    (let* ((args (term-args t))
           (arg (lambda ((i int)) (ev (list-ref-int args i))))
           (int-arg (lambda ((i int)) (rat-num (ev (list-ref-int args i))))))
      (cond
       ((string=? op "var") (var-value t))
       ((string=? op "true") rat-1)
       ((string=? op "false") rat-0)
       ((string=? op "not") (rat-bool (not (rat-true? (arg 0)))))
       ((string=? op "and") (rat-bool (letrec ((go (subr cb-eff (ints) bool) (lambda (l) (or (null? l) (and (rat-true? (ev (car l))) (go (cdr l)))))))
                                        (go args))))
       ((string=? op "or") (rat-bool (letrec ((go (subr cb-eff (ints) bool) (lambda (l) (and (pair? l) (or (rat-true? (ev (car l))) (go (cdr l)))))))
                                       (go args))))
       ((string=? op "card")
        (let ((n (letrec ((go (subr cb-eff (ints int) int) (lambda (l n) (if (null? l) n (go (cdr l) (if (rat-true? (ev (car l))) (+ n 1) n))))))
                   (go args 0)))
              (lo (term-param0 t)) (hi (term-param1 t)))
          (rat-bool (and (>= n lo) (or (= hi no-bound) (<= n hi))))))
       ((string=? op "=") (rat-bool (rat= (arg 0) (arg 1))))
       ((string=? op "ite") (if (rat-true? (arg 0)) (arg 1) (arg 2)))
       ((string=? op "num") (product (n (term-param0 t)) (d (term-param1 t))))
       ((string=? op "scale") (rat* (product (n (term-param0 t)) (d (term-param1 t))) (arg 0)))
       ((string=? op "+") (letrec ((go (subr cb-eff (ints rat) rat) (lambda (l s) (if (null? l) s (go (cdr l) (rat+ s (ev (car l))))))))
                            (go args rat-0)))
       ((string=? op "*") (letrec ((go (subr cb-eff (ints rat) rat) (lambda (l s) (if (null? l) s (go (cdr l) (rat* s (ev (car l))))))))
                            (go args rat-1)))
       ((string=? op "/") (if (rat-zero? (arg 1)) rat-0 (rat/ (arg 0) (arg 1))))
       ((string=? op "div") (let ((b (int-arg 1))) (if (= b 0) rat-0 (int->rat (euclid-div (int-arg 0) b)))))
       ((string=? op "mod") (let ((a (int-arg 0)) (b (int-arg 1))) (if (= b 0) (int->rat a) (int->rat (- a (* b (euclid-div a b)))))))
       ((string=? op "to_real") (arg 0))
       ((string=? op "to_int") (int->rat (rat-floor (arg 0))))
       ((string=? op "<=") (rat-bool (rat<= (arg 0) (arg 1))))
       ((string=? op ">=") (rat-bool (rat<= (arg 1) (arg 0))))
       ((bv-sort? (term-sort t)) (int->rat (eval-bv t op (bv-sort-width (term-sort t)) int-arg)))
       ((string=? op "bvult") (rat-bool (< (int-arg 0) (int-arg 1))))
       ((string=? op "bvslt")
        (let ((w (bv-sort-width (term-sort (term-arg0 t)))))
          (rat-bool (< (signed (int-arg 0) w) (signed (int-arg 1) w)))))
       (else (begin (error (string-append "eval-term: unknown operator " op)) rat-0))))))

(define* list-ref-int (subr cb-eff (ints int) int) (lambda (l i) (if (= i 0) (car l) (list-ref-int (cdr l) (- i 1)))))
(define* signed (subr cb-eff (int int) int) (lambda (v w) (if (>= v (expt2 (- w 1))) (- v (expt2 w)) v)))

"Bitvector operators, on naturals below 2^w, as SMT-LIB defines them (not
as the blaster computes them)."
(define* eval-bv (subr cb-eff (int string int (subr cb-eff (int) int)) int)
  (lambda (t op w arg)
    (let* ((m (expt2 w)) (wrap (lambda ((x int)) (modulo x m))))
      (cond
       ((string=? op "bv") (term-param0 t))
       ((string=? op "bvnot") (- (- m 1) (arg 0)))
       ((string=? op "bvand") (bitwise-and (arg 0) (arg 1)))
       ((string=? op "bvor") (bitwise-ior (arg 0) (arg 1)))
       ((string=? op "bvxor") (bitwise-xor (arg 0) (arg 1)))
       ((string=? op "bvneg") (wrap (- 0 (arg 0))))
       ((string=? op "bvadd") (wrap (+ (arg 0) (arg 1))))
       ((string=? op "bvsub") (wrap (- (arg 0) (arg 1))))
       ((string=? op "bvmul") (wrap (* (arg 0) (arg 1))))
       ((string=? op "bvudiv") (if (= 0 (arg 1)) (- m 1) (quotient (arg 0) (arg 1))))
       ((string=? op "bvurem") (if (= 0 (arg 1)) (arg 0) (remainder (arg 0) (arg 1))))
       ((string=? op "bvshl") (if (>= (arg 1) w) 0 (wrap (arithmetic-shift (arg 0) (arg 1)))))
       ((string=? op "bvlshr") (if (>= (arg 1) w) 0 (arithmetic-shift (arg 0) (- 0 (arg 1)))))
       ((string=? op "bvashr") (wrap (arithmetic-shift (signed (arg 0) w) (- 0 (min (arg 1) w)))))
       ((string=? op "concat")
        (let ((lo-width (bv-sort-width (term-sort (term-arg1 t))))) (+ (arithmetic-shift (arg 0) lo-width) (arg 1))))
       ((string=? op "extract") (modulo (arithmetic-shift (arg 0) (- 0 (term-param1 t))) m))
       ((string=? op "sign_extend") (wrap (signed (arg 0) (bv-sort-width (term-sort (term-arg0 t))))))
       (else (begin (error (string-append "eval-term: unknown operator " op)) 0))))))
