;;; simplex.fx: linear arithmetic over the rationals and the integers, as a
;;; theory for the SAT solver (lockpick's `(lockpick simplex)`): the
;;; general simplex of Dutertre and de Moura, "A Fast Linear-Arithmetic
;;; Solver for DPLL(T)" (CAV 2006), with branch and bound for integers.
;;;
;;; Variables are numbered from 0. Some are the terms' variables, some are
;;; slack variables, one for each linear form that atoms bound
;;; (s = 2x - y). The tableau keeps each basic variable as a total of
;;; nonbasic ones; the assignment always satisfies it. A bound on a
;;; variable comes from an atom literal (its reason), and is undone when
;;; the SAT solver backtracks past that literal.
;;;
;;; Values and bounds are delta-rationals c + k*delta, for strict bounds on
;;; reals (x < 3 is x <= 3 - delta); delta is given a value only when a
;;; model is read. Each is kept as two rationals in parallel arrays.
;;;
;;; Not here: lockpick's theory propagation (LOCKPICK_PROPAGATE), which is
;;; off there by default.

(module-parameters ((m-sat (load-moduleof "sat.fx")) (m-rat (load-moduleof "rat.fx"))))

(hide (define kit-numbers (load-module "../kit/numbers.fx"))
      (import kit-numbers gcd lcm))

(define tables (load-module "fx26:table.fx"))
(import tables make-table table-ref table-set! table-has? (type table))

(define-type rats (arrayof rat @cb))
"A linear form over simplex variables: (variable, coefficient), sorted by
variable."
(define-type smono (productof (x int) (c rat)))
(define-type sform (listof smono acyclic))
"An atom: x <= k (le) or x >= k."
(define-type atom (productof (x int) (le bool) (k rat)))
"A bound change to undo: at trail position `stamp`, the bound (upper or
lower) of x was c + k delta, of reason literal `reason` (0: none)."
(define-type undo-rec (productof (stamp int) (x int) (upper bool) (c rat) (k rat) (reason int)))

(define-type simplex
  (productof
   (solver sat-solver) (n (ref int @cb))
   ;; By variable: value, lower bound (c, k, reason literal, 0 if none),
   ;; upper bound, integer?, row if basic (-1 if not).
   (vc (ref rats @cb)) (vk (ref rats @cb))
   (loc (ref rats @cb)) (lok (ref rats @cb)) (lor (ref ivec @cb))
   (hic (ref rats @cb)) (hik (ref rats @cb)) (hir (ref ivec @cb))
   (int (ref bools @cb)) (row-of (ref ivec @cb))
   ;; The tableau, sparse, after z3's and Yices's: by row, its basic
   ;; variable, and its entries 0 .. rlen - 1, each a nonbasic variable
   ;; (rvars), its coefficient (rcoefs) and its place in that variable's
   ;; column (rcpos). Rows are fraction-free: row r is d x_b = total of a x
   ;; for its entries, d = rden > 0 and the a integers, with no common
   ;; factor. By variable, its column: the rows it is in (crows), at which
   ;; entry (crpos), 0 .. clen - 1.
   (nrows (ref int @cb)) (basic (ref ivec @cb))
   (rvars (ref ivecs @cb)) (rcoefs (ref ivecs @cb)) (rcpos (ref ivecs @cb))
   (rlen (ref ivec @cb)) (rden (ref ivec @cb))
   (crows (ref ivecs @cb)) (crpos (ref ivecs @cb)) (clen (ref ivec @cb))
   ;; By variable, -1 except in row-add-scaled!.
   (where (ref ivec @cb))
   ;; The basic variables that may be out of bounds (0 .. ncand - 1), and by
   ;; variable whether it is one of them.
   (cand (ref ivec @cb)) (ncand (ref int @cb)) (in-cand (ref bools @cb))
   ;; By SAT variable, its atom, if it is one.
   (has-atom (ref bools @cb)) (atoms (ref (arrayof atom @cb) @cb))
   (undo (ref (listof undo-rec acyclic) @cb))
   ;; How much of the SAT trail has been read.
   (qhead (ref int @cb))
   ;; "x:f" -> the SAT variable of the atom x <= f, made by branch and bound.
   (branches (table string int @cb))
   (delta (ref rat @cb))
   ;; By variable: whether a slack, and its form (over variables made
   ;; before it), and its form over variables not slacks (made when first
   ;; needed).
   (slack (ref bools @cb)) (defs (ref (arrayof sform @cb) @cb))
   (expanded (ref (arrayof sform @cb) @cb)) (has-expanded (ref bools @cb))
   ;; How many times integers were found not integers, for spacing cuts.
   (finals (ref int @cb))
   (cuts (ref bool @cb))))

(define* grow-rats (subr cb-eff (rats int rat) rats)
  (lambda (v i fill)
    (if (< i (array-length v)) v
        (let ((w (the rats (make-array (* 2 (+ i 1)) fill))))
          (letrec ((go (subr cb-eff (int) rats) (lambda (k) (if (>= k (array-length v)) w (begin (array-set! w k (array-ref v k)) (go (+ k 1)))))))
            (go 0))))))
(define* grow-forms (subr cb-eff ((arrayof sform @cb) int) (arrayof sform @cb))
  (lambda (v i)
    (if (< i (array-length v)) v
        (let ((w (the (arrayof sform @cb) (make-array (* 2 (+ i 1)) (the sform nil)))))
          (letrec ((go (subr cb-eff (int) (arrayof sform @cb)) (lambda (k) (if (>= k (array-length v)) w (begin (array-set! w k (array-ref v k)) (go (+ k 1)))))))
            (go 0))))))
"`v` with x at i, made longer if need be."
(define* put (subr cb-eff (ivec int int) ivec)
  (lambda (v i x) (let ((v (grow-ivec v i 0))) (begin (array-set! v i x) v))))

(define no-atom atom (product (x 0) (le #t) (k rat-0)))

(define* make-simplex (subr cb-eff (sat-solver) simplex)
  (lambda (s)
    (let ((rats16 (lambda () (the (ref rats @cb) (new (the rats (make-array 16 rat-0))))))
          (ivec16 (lambda ((x int)) (the (ref ivec @cb) (new (the ivec (make-array 16 x))))))
          (ivecs16 (lambda () (the (ref ivecs @cb) (new (the ivecs (make-array 16 (the ivec (make-array 0 0)))))))))
      (product (solver s) (n (new 0))
               (vc (rats16)) (vk (rats16)) (loc (rats16)) (lok (rats16)) (lor (ivec16 0))
               (hic (rats16)) (hik (rats16)) (hir (ivec16 0))
               (int (new (the bools (make-array 16 #f)))) (row-of (ivec16 -1))
               (nrows (new 0)) (basic (ivec16 0))
               (rvars (ivecs16)) (rcoefs (ivecs16)) (rcpos (ivecs16)) (rlen (ivec16 0)) (rden (ivec16 1))
               (crows (ivecs16)) (crpos (ivecs16)) (clen (ivec16 0))
               (where (ivec16 -1))
               (cand (ivec16 0)) (ncand (new 0)) (in-cand (new (the bools (make-array 16 #f))))
               (has-atom (new (the bools (make-array 16 #f)))) (atoms (new (the (arrayof atom @cb) (make-array 16 no-atom))))
               (undo (new (the (listof undo-rec acyclic) nil)))
               (qhead (new 0))
               (branches (the (table string int @cb) (make-table string-hash string=?)))
               (delta (new rat-1))
               (slack (new (the bools (make-array 16 #f)))) (defs (new (the (arrayof sform @cb) (make-array 16 (the sform nil)))))
               (expanded (new (the (arrayof sform @cb) (make-array 16 (the sform nil))))) (has-expanded (new (the bools (make-array 16 #f))))
               (finals (new 0))
               (cuts (new #t))))))

;; The arrays read most, by name.
(define* vc (subr cb-eff (simplex) rats) (lambda (sx) (get (extract sx vc))))
(define* vk (subr cb-eff (simplex) rats) (lambda (sx) (get (extract sx vk))))
(define* loc (subr cb-eff (simplex) rats) (lambda (sx) (get (extract sx loc))))
(define* lok (subr cb-eff (simplex) rats) (lambda (sx) (get (extract sx lok))))
(define* lor (subr cb-eff (simplex) ivec) (lambda (sx) (get (extract sx lor))))
(define* hic (subr cb-eff (simplex) rats) (lambda (sx) (get (extract sx hic))))
(define* hik (subr cb-eff (simplex) rats) (lambda (sx) (get (extract sx hik))))
(define* hir (subr cb-eff (simplex) ivec) (lambda (sx) (get (extract sx hir))))
(define* row-of (subr cb-eff (simplex) ivec) (lambda (sx) (get (extract sx row-of))))
(define* int-var? (subr cb-eff (simplex int) bool) (lambda (sx x) (array-ref (get (extract sx int)) x)))
(define* basic (subr cb-eff (simplex) ivec) (lambda (sx) (get (extract sx basic))))
(define* rvars (subr cb-eff (simplex int) ivec) (lambda (sx r) (array-ref (get (extract sx rvars)) r)))
(define* rcoefs (subr cb-eff (simplex int) ivec) (lambda (sx r) (array-ref (get (extract sx rcoefs)) r)))
(define* rlen (subr cb-eff (simplex int) int) (lambda (sx r) (array-ref (get (extract sx rlen)) r)))
(define* rden (subr cb-eff (simplex int) int) (lambda (sx r) (array-ref (get (extract sx rden)) r)))
(define* clen (subr cb-eff (simplex int) int) (lambda (sx x) (array-ref (get (extract sx clen)) x)))
(define* simplex-nvars (subr cb-eff (simplex) int) (lambda (sx) (get (extract sx n))))
(define* simplex-set-cuts! (subr (write @cb) (simplex bool) unit) (lambda (sx b) (set (extract sx cuts) b)))
(define* slack? (subr cb-eff (simplex int) bool) (lambda (sx x) (array-ref (get (extract sx slack)) x)))

"A new nonbasic variable, valued 0, without bounds."
(define* simplex-new-var! (subr cb-eff (simplex bool) int)
  (lambda (sx int?)
    (let* ((x (simplex-nvars sx))
          (gr! (lambda ((r (ref rats @cb))) (set r (grow-rats (get r) x rat-0))))
          (gi! (lambda ((r (ref ivec @cb)) (fill int)) (set r (grow-ivec (get r) x fill))))
          (gb! (lambda ((r (ref bools @cb))) (set r (grow-bools (get r) x #f))))
          (gv! (lambda ((r (ref ivecs @cb))) (set r (grow-ivecs (get r) x)))))
      (begin
        (gr! (extract sx vc)) (gr! (extract sx vk)) (gr! (extract sx loc)) (gr! (extract sx lok)) (gi! (extract sx lor) 0)
        (gr! (extract sx hic)) (gr! (extract sx hik)) (gi! (extract sx hir) 0)
        (gb! (extract sx int)) (gi! (extract sx row-of) -1)
        (gv! (extract sx crows)) (gv! (extract sx crpos)) (gi! (extract sx clen) 0)
        (gi! (extract sx where) -1) (gb! (extract sx in-cand)) (gb! (extract sx slack))
        (set (extract sx defs) (grow-forms (get (extract sx defs)) x))
        (set (extract sx expanded) (grow-forms (get (extract sx expanded)) x)) (gb! (extract sx has-expanded))
        (array-set! (get (extract sx int)) x int?)
        (array-set! (get (extract sx crows)) x (the ivec (make-array 4 0)))
        (array-set! (get (extract sx crpos)) x (the ivec (make-array 4 0)))
        (set (extract sx n) (+ x 1))
        x))))

"Add x with coefficient a to row r (which has no x). Its place in the row."
(define* entry-add! (subr cb-eff (simplex int int int) int)
  (lambda (sx r x a)
    (let ((i (rlen sx r)) (p (clen sx x)))
      (begin
        (array-set! (get (extract sx rvars)) r (put (rvars sx r) i x))
        (array-set! (get (extract sx rcoefs)) r (put (rcoefs sx r) i a))
        (array-set! (get (extract sx rcpos)) r (put (array-ref (get (extract sx rcpos)) r) i p))
        (array-set! (get (extract sx rlen)) r (+ i 1))
        (array-set! (get (extract sx crows)) x (put (array-ref (get (extract sx crows)) x) p r))
        (array-set! (get (extract sx crpos)) x (put (array-ref (get (extract sx crpos)) x) p i))
        (array-set! (get (extract sx clen)) x (+ p 1))
        i))))

"Remove entry i of row r. The row's last entry takes its place, and in the
column the column's last entry."
(define* entry-remove! (subr cb-eff (simplex int int) unit)
  (lambda (sx r i)
    (let* ((vars (rvars sx r)) (coefs (rcoefs sx r)) (cpos (array-ref (get (extract sx rcpos)) r))
           (x (array-ref vars i)) (p (array-ref cpos i)) (last (- (rlen sx r) 1)))
      (begin
        (if (= i last) #u
            (let ((y (array-ref vars last)) (py (array-ref cpos last)))
              (begin (array-set! vars i y) (array-set! coefs i (array-ref coefs last)) (array-set! cpos i py)
                     (array-set! (array-ref (get (extract sx crpos)) y) py i))))
        (array-set! coefs last 0)
        (array-set! (get (extract sx rlen)) r last)
        (let* ((rows (array-ref (get (extract sx crows)) x)) (rpos (array-ref (get (extract sx crpos)) x)) (lastc (- (clen sx x) 1)))
          (begin
            (if (= p lastc) #u
                (let ((r2 (array-ref rows lastc)) (i2 (array-ref rpos lastc)))
                  (begin (array-set! rows p r2) (array-set! rpos p i2)
                         (array-set! (array-ref (get (extract sx rcpos)) r2) i2 p))))
            (array-set! (get (extract sx clen)) x lastc)))))))

"Row r2 plus c times row r (r2 has none of r's variables basic)."
(define* row-add-scaled! (subr cb-eff (simplex int int int) unit)
  (lambda (sx r2 c r)
    (let ((where (get (extract sx where))))
      (letrec ((mark (subr cb-eff (int) unit)
                 (lambda (i) (if (= i (rlen sx r2)) #u (begin (array-set! where (array-ref (rvars sx r2) i) i) (mark (+ i 1))))))
               (unmark (subr cb-eff (int) unit)
                 (lambda (i) (if (= i (rlen sx r2)) #u (begin (array-set! where (array-ref (rvars sx r2) i) -1) (unmark (+ i 1))))))
               (add (subr cb-eff (int) unit)
                 (lambda (i)
                   (if (= i (rlen sx r)) #u
                       (let* ((k (array-ref (rvars sx r) i)) (e (* c (array-ref (rcoefs sx r) i))) (w (array-ref where k)))
                         (begin
                           (if (< w 0)
                               (array-set! where k (entry-add! sx r2 k e))
                               (let* ((coefs2 (rcoefs sx r2)) (e2 (+ (array-ref coefs2 w) e)))
                                 (if (= e2 0)
                                     (let ((last (- (rlen sx r2) 1)))
                                       (begin (array-set! where (array-ref (rvars sx r2) last) w)
                                              (array-set! where k -1)
                                              (entry-remove! sx r2 w)))
                                     (array-set! coefs2 w e2))))
                           (add (+ i 1))))))))
        (begin (mark 0) (add 0) (unmark 0))))))

"Basic x may now be out of bounds."
(define* touch! (subr cb-eff (simplex int) unit)
  (lambda (sx x)
    (if (array-ref (get (extract sx in-cand)) x) #u
        (begin (array-set! (get (extract sx in-cand)) x #t)
               (set (extract sx cand) (put (get (extract sx cand)) (get (extract sx ncand)) x))
               (set (extract sx ncand) (+ 1 (get (extract sx ncand))))))))

(define* sform-sort (subr cb-eff (sform) sform)
  (lambda (l)
    (letrec ((insert (subr cb-eff (smono sform) sform)
               (lambda (m l) (cond ((null? l) (list m)) ((< (extract m x) (extract (car l) x)) (cons m l)) (else (cons (car l) (insert m (cdr l)))))))
             (go (subr cb-eff (sform sform) sform) (lambda (l acc) (if (null? l) acc (go (cdr l) (insert (car l) acc))))))
      (go l nil))))
"`f` plus c x, coefficients of 0 dropped (f sorted)."
(define* sform-add (subr cb-eff (sform int rat) sform)
  (lambda (f x c)
    (cond ((null? f) (if (rat-zero? c) nil (list (product (x x) (c c)))))
          ((= (extract (car f) x) x)
           (let ((e (rat+ (extract (car f) c) c))) (if (rat-zero? e) (cdr f) (cons (product (x x) (c e)) (cdr f)))))
          ((< x (extract (car f) x)) (if (rat-zero? c) f (cons (product (x x) (c c)) f)))
          (else (cons (car f) (sform-add (cdr f) x c))))))

"A slack variable s, with the row s = total of c * x for (x, c) in `form`,
written over the nonbasic variables."
(define* simplex-slack! (subr cb-eff (simplex sform bool) int)
  (lambda (sx form int?)
    (let* ((s (simplex-new-var! sx int?)) (r (get (extract sx nrows)))
           ;; The total, over nonbasic variables, sorted by variable.
           (total (letrec ((go (subr cb-eff (sform sform) sform)
                           (lambda (form total)
                             (if (null? form) total
                                 (let* ((x (extract (car form) x)) (c (extract (car form) c)) (rx (array-ref (row-of sx) x)))
                                   (if (>= rx 0)
                                       (let ((c (rat/ c (int->rat (rden sx rx)))))
                                         (letrec ((row (subr cb-eff (int sform) sform)
                                                    (lambda (i total) (if (= i (rlen sx rx)) total
                                                                        (row (+ i 1) (sform-add total (array-ref (rvars sx rx) i) (rat* c (int->rat (array-ref (rcoefs sx rx) i)))))))))
                                           (go (cdr form) (row 0 total))))
                                       (go (cdr form) (sform-add total x c))))))))
                  (go form nil))))
      (begin
        (set (extract sx basic) (grow-ivec (basic sx) r 0))
        (set (extract sx rvars) (grow-ivecs (get (extract sx rvars)) r))
        (set (extract sx rcoefs) (grow-ivecs (get (extract sx rcoefs)) r))
        (set (extract sx rcpos) (grow-ivecs (get (extract sx rcpos)) r))
        (set (extract sx rlen) (grow-ivec (get (extract sx rlen)) r 0))
        (set (extract sx rden) (grow-ivec (get (extract sx rden)) r 1))
        (array-set! (basic sx) r s)
        (array-set! (get (extract sx rvars)) r (the ivec (make-array 4 0)))
        (array-set! (get (extract sx rcoefs)) r (the ivec (make-array 4 0)))
        (array-set! (get (extract sx rcpos)) r (the ivec (make-array 4 0)))
        (array-set! (get (extract sx rlen)) r 0)
        (set (extract sx nrows) (+ r 1))
        (array-set! (row-of sx) s r)
        (array-set! (get (extract sx slack)) s #t)
        (array-set! (get (extract sx defs)) s form)
        ;; In the order of the variables, so that a build is repeatable; d s =
        ;; total (d a) y, d the least common multiple of the denominators.
        (let ((d (letrec ((go (subr cb-eff (sform int) int) (lambda (l d) (if (null? l) d (go (cdr l) (lcm d (rat-den (extract (car l) c))))))))
                   (go total 1))))
          (begin
            (array-set! (get (extract sx rden)) r d)
            (letrec ((go (subr cb-eff (sform) unit)
                       (lambda (l) (if (null? l) #u
                                       (begin (entry-add! sx r (extract (car l) x) (rat-num (rat* (int->rat d) (extract (car l) c)))) (go (cdr l)))))))
              (go total))))
        (letrec ((go (subr cb-eff (sform rat rat) unit)
                   (lambda (l c k)
                     (if (null? l) (begin (array-set! (vc sx) s c) (array-set! (vk sx) s k))
                         (let ((y (extract (car l) x)) (a (extract (car l) c)))
                           (go (cdr l) (rat+ c (rat* a (array-ref (vc sx) y))) (rat+ k (rat* a (array-ref (vk sx) y)))))))))
          (go total rat-0 rat-0))
        (touch! sx s)
        s))))

"The SAT variable v stands for the atom x <= k (le) or x >= k."
(define* simplex-add-atom! (subr cb-eff (simplex int int bool rat) unit)
  (lambda (sx v x le k)
    (begin
      (set (extract sx has-atom) (grow-bools (get (extract sx has-atom)) v #f))
      (let ((as (get (extract sx atoms))))
        (if (< v (array-length as)) #u
            (let ((w (the (arrayof atom @cb) (make-array (* 2 (+ v 1)) no-atom))))
              (letrec ((go (subr cb-eff (int) unit) (lambda (i) (if (>= i (array-length as)) #u (begin (array-set! w i (array-ref as i)) (go (+ i 1)))))))
                (begin (go 0) (set (extract sx atoms) w))))))
      (array-set! (get (extract sx has-atom)) v #t)
      (array-set! (get (extract sx atoms)) v (product (x x) (le le) (k k))))))

;;; ------------------------------------------------------------ delta-rationals

(define* d< (subr cb-eff (rat rat rat rat) bool)
  (lambda (c1 k1 c2 k2) (or (rat< c1 c2) (and (rat= c1 c2) (rat< k1 k2)))))
(define* below-lower? (subr cb-eff (simplex int) bool)
  (lambda (sx x) (and (> (array-ref (lor sx) x) 0) (d< (array-ref (vc sx) x) (array-ref (vk sx) x) (array-ref (loc sx) x) (array-ref (lok sx) x)))))
(define* above-upper? (subr cb-eff (simplex int) bool)
  (lambda (sx x) (and (> (array-ref (hir sx) x) 0) (d< (array-ref (hic sx) x) (array-ref (hik sx) x) (array-ref (vc sx) x) (array-ref (vk sx) x)))))

"Set nonbasic x to c + k delta, and the basic variables with it."
(define* update! (subr cb-eff (simplex int rat rat) unit)
  (lambda (sx x c k)
    (let ((dc (rat- c (array-ref (vc sx) x))) (dk (rat- k (array-ref (vk sx) x)))
          (rows (array-ref (get (extract sx crows)) x)) (rpos (array-ref (get (extract sx crpos)) x))
          (vcs (vc sx)) (vks (vk sx)))
      (letrec ((go (subr cb-eff (int) unit)
                 (lambda (p)
                   (if (= p (clen sx x)) #u
                       (let* ((r (array-ref rows p)) (b (array-ref (basic sx) r))
                              (a (make-rat (array-ref (rcoefs sx r) (array-ref rpos p)) (rden sx r))))
                         (begin
                           (if (rat-zero? dc) #u (array-set! vcs b (rat+ (array-ref vcs b) (rat* a dc))))
                           (if (rat-zero? dk) #u (array-set! vks b (rat+ (array-ref vks b) (rat* a dk))))
                           (touch! sx b)
                           (go (+ p 1))))))))
        (begin (go 0) (array-set! vcs x c) (array-set! vks x k))))))

"Assert a bound on x, upper or lower: c + k delta, because of the literal
reason, at trail position stamp. A conflict, a list of true literals that
cannot all hold; or none."
(define* assert-bound! (subr cb-eff (simplex int bool rat rat int int) ints)
  (lambda (sx x upper? c k reason stamp)
    (if upper?
        (cond ((and (> (array-ref (hir sx) x) 0) (not (d< c k (array-ref (hic sx) x) (array-ref (hik sx) x)))) nil)
              ((and (> (array-ref (lor sx) x) 0) (d< c k (array-ref (loc sx) x) (array-ref (lok sx) x)))
               (list reason (array-ref (lor sx) x)))
              (else
               (begin
                 (set (extract sx undo) (cons (product (stamp stamp) (x x) (upper #t) (c (array-ref (hic sx) x)) (k (array-ref (hik sx) x)) (reason (array-ref (hir sx) x)))
                                              (get (extract sx undo))))
                 (array-set! (hic sx) x c) (array-set! (hik sx) x k) (array-set! (hir sx) x reason)
                 (cond ((>= (array-ref (row-of sx) x) 0) (touch! sx x))
                       ((above-upper? sx x) (update! sx x c k))
                       (else #u))
                 nil)))
        (cond ((and (> (array-ref (lor sx) x) 0) (not (d< (array-ref (loc sx) x) (array-ref (lok sx) x) c k))) nil)
              ((and (> (array-ref (hir sx) x) 0) (d< (array-ref (hic sx) x) (array-ref (hik sx) x) c k))
               (list reason (array-ref (hir sx) x)))
              (else
               (begin
                 (set (extract sx undo) (cons (product (stamp stamp) (x x) (upper #f) (c (array-ref (loc sx) x)) (k (array-ref (lok sx) x)) (reason (array-ref (lor sx) x)))
                                              (get (extract sx undo))))
                 (array-set! (loc sx) x c) (array-set! (lok sx) x k) (array-set! (lor sx) x reason)
                 (cond ((>= (array-ref (row-of sx) x) 0) (touch! sx x))
                       ((below-lower? sx x) (update! sx x c k))
                       (else #u))
                 nil))))))

(define* backtrack! (subr cb-eff (simplex int) unit)
  (lambda (sx n)
    (letrec ((go (subr cb-eff ((listof undo-rec acyclic)) unit)
               (lambda (u)
                 (if (and (pair? u) (>= (extract (car u) stamp) n))
                     (let* ((e (car u)) (x (extract e x)))
                       (begin
                         (if (extract e upper)
                             (begin (array-set! (hic sx) x (extract e c)) (array-set! (hik sx) x (extract e k)) (array-set! (hir sx) x (extract e reason)))
                             (begin (array-set! (loc sx) x (extract e c)) (array-set! (lok sx) x (extract e k)) (array-set! (lor sx) x (extract e reason))))
                         (go (cdr u))))
                     (set (extract sx undo) u)))))
      (begin (go (get (extract sx undo)))
             (if (< n (get (extract sx qhead))) (set (extract sx qhead) n) #u)))))

;;; ------------------------------------------------------------ pivoting

"Row r, both sides times m."
(define* row-scale! (subr cb-eff (simplex int int) unit)
  (lambda (sx r m)
    (let ((coefs (rcoefs sx r)))
      (letrec ((go (subr cb-eff (int) unit) (lambda (i) (if (= i (rlen sx r)) #u (begin (array-set! coefs i (* m (array-ref coefs i))) (go (+ i 1)))))))
        (begin (go 0) (array-set! (get (extract sx rden)) r (* m (rden sx r))))))))

"Row r divided by the common factor of its coefficients."
(define* row-normalize! (subr cb-eff (simplex int) unit)
  (lambda (sx r)
    (let ((d (rden sx r)))
      (if (= d 1) #u
          (let* ((coefs (rcoefs sx r)) (n (rlen sx r))
                 (g (letrec ((go (subr cb-eff (int int) int) (lambda (i g) (if (or (= i n) (= g 1)) g (go (+ i 1) (gcd g (array-ref coefs i)))))))
                      (go 0 d))))
            (if (= g 1) #u
                (letrec ((go (subr cb-eff (int) unit) (lambda (i) (if (= i n) #u (begin (array-set! coefs i (quotient (array-ref coefs i) g)) (go (+ i 1)))))))
                  (begin (go 0) (array-set! (get (extract sx rden)) r (quotient d g))))))))))

"Make x_j, entry ij of row r, basic in row r, whose basic variable becomes
nonbasic."
(define* pivot! (subr cb-eff (simplex int int int) unit)
  (lambda (sx r j ij)
    (let* ((b (array-ref (basic sx) r)) (a (array-ref (rcoefs sx r) ij)) (sign (if (< a 0) -1 1)) (d (rden sx r)))
      (begin
        ;; From d b = a x_j + total a_k x_k: |a| x_j = sign (d b - total a_k x_k).
        (entry-remove! sx r ij)
        (let ((coefs (rcoefs sx r)))
          (letrec ((go (subr cb-eff (int) unit) (lambda (i) (if (= i (rlen sx r)) #u (begin (array-set! coefs i (* (- 0 sign) (array-ref coefs i))) (go (+ i 1)))))))
            (go 0)))
        (entry-add! sx r b (* sign d))
        (array-set! (get (extract sx rden)) r (if (< a 0) (- 0 a) a))
        (array-set! (basic sx) r j)
        (array-set! (row-of sx) j r)
        (array-set! (row-of sx) b -1)
        (touch! sx j)
        ;; Substitute in the other rows that have x_j, which leaves its column
        ;; empty. For d2 b2 = c x_j + rest, and D x_j = form (row r):
        ;; (D/g) d2 b2 = (c/g) form + (D/g) rest, g = gcd(c, D).
        (let ((dj (if (< a 0) (- 0 a) a)))
          (letrec ((go (subr cb-eff () unit)
                     (lambda ()
                       (let ((n (clen sx j)))
                         (if (= n 0) #u
                             (let* ((r2 (array-ref (array-ref (get (extract sx crows)) j) (- n 1)))
                                    (i2 (array-ref (array-ref (get (extract sx crpos)) j) (- n 1)))
                                    (c (array-ref (rcoefs sx r2) i2))
                                    (g (gcd c dj)))
                               (begin (entry-remove! sx r2 i2)
                                      (if (= g dj) #u (row-scale! sx r2 (quotient dj g)))
                                      (row-add-scaled! sx r2 (quotient c g) r)
                                      (row-normalize! sx r2)
                                      (go))))))))
            (go)))))))

"Set basic x_i (row r) to c + k delta by changing nonbasic x_j, entry ij
of the row, then pivot them."
(define* pivot-and-update! (subr cb-eff (simplex int int int rat rat) unit)
  (lambda (sx r j ij c k)
    (let* ((i (array-ref (basic sx) r))
           (a (make-rat (array-ref (rcoefs sx r) ij) (rden sx r)))
           (tc (rat/ (rat- c (array-ref (vc sx) i)) a))
           (tk (rat/ (rat- k (array-ref (vk sx) i)) a)))
      (begin (update! sx j (rat+ (array-ref (vc sx) j) tc) (rat+ (array-ref (vk sx) j) tk))
             (pivot! sx r j ij)))))

(define* can-increase? (subr cb-eff (simplex int) bool)
  (lambda (sx x) (or (= 0 (array-ref (hir sx) x)) (d< (array-ref (vc sx) x) (array-ref (vk sx) x) (array-ref (hic sx) x) (array-ref (hik sx) x)))))
(define* can-decrease? (subr cb-eff (simplex int) bool)
  (lambda (sx x) (or (= 0 (array-ref (lor sx) x)) (d< (array-ref (loc sx) x) (array-ref (lok sx) x) (array-ref (vc sx) x) (array-ref (vk sx) x)))))

"The row of the least basic variable out of its bounds, or -1. The
candidates found within bounds are dropped."
(define* violated-row (subr cb-eff (simplex) int)
  (lambda (sx)
    (let ((cand (get (extract sx cand))) (n (get (extract sx ncand))) (in (get (extract sx in-cand))) (row-of (row-of sx)))
      (letrec ((go (subr cb-eff (int int int) int)
                 (lambda (i j best)
                   (if (= i n)
                       (begin (set (extract sx ncand) j) (if (< best 0) -1 (array-ref row-of best)))
                       (let ((x (array-ref cand i)))
                         (if (and (>= (array-ref row-of x) 0) (or (below-lower? sx x) (above-upper? sx x)))
                             (begin (array-set! cand j x) (go (+ i 1) (+ j 1) (if (or (< best 0) (< x best)) x best)))
                             (begin (array-set! in x #f) (go (+ i 1) j best))))))))
        (go 0 0 -1)))))

"Make the assignment satisfy the bounds, or find them infeasible: none,
or a conflict (a list of true literals). The basic variable to fix is the
least one out of bounds; the nonbasic one to pivot with, of those that can
move it, the one in the fewest rows (the least fill-in), as in Yices and
z3. After 1000 pivots it is the least one: Bland's rule, which
terminates."
(define* check! (subr cb-eff (simplex) ints)
  (lambda (sx)
    (letrec ((go (subr cb-eff (int) ints)
               (lambda (pivots)
                 (let ((r (violated-row sx)))
                   (if (< r 0) nil
                       (let* ((i (array-ref (basic sx) r)) (vars (rvars sx r)) (coefs (rcoefs sx r)) (n (rlen sx r))
                              (low? (below-lower? sx i)) (bland? (> pivots 1000)) (clen (get (extract sx clen)))
                              ;; The entry of the nonbasic variable to pivot with.
                              (ij (letrec ((find (subr cb-eff (int int) int)
                                             (lambda (e best)
                                               (if (= e n) best
                                                   (let ((x (array-ref vars e)))
                                                     (if (and (or (< best 0)
                                                                  (let ((y (array-ref vars best)))
                                                                    (if bland? (< x y)
                                                                        (let ((cx (array-ref clen x)) (cy (array-ref clen y)))
                                                                          (or (< cx cy) (and (= cx cy) (< x y)))))))
                                                              (if (bool=? low? (> (array-ref coefs e) 0)) (can-increase? sx x) (can-decrease? sx x)))
                                                         (find (+ e 1) e)
                                                         (find (+ e 1) best)))))))
                                    (find 0 -1))))
                         (if (>= ij 0)
                             (begin
                               (if low?
                                   (pivot-and-update! sx r (array-ref vars ij) ij (array-ref (loc sx) i) (array-ref (lok sx) i))
                                   (pivot-and-update! sx r (array-ref vars ij) ij (array-ref (hic sx) i) (array-ref (hik sx) i)))
                               (go (+ pivots 1)))
                             ;; The row and the bounds of its variables conflict.
                             (cons (if low? (array-ref (lor sx) i) (array-ref (hir sx) i))
                                   (letrec ((collect (subr cb-eff (int ints) ints)
                                              (lambda (e acc)
                                                (if (= e n) acc
                                                    (collect (+ e 1) (cons (if (bool=? low? (> (array-ref coefs e) 0))
                                                                               (array-ref (hir sx) (array-ref vars e))
                                                                               (array-ref (lor sx) (array-ref vars e)))
                                                                           acc))))))
                                     (collect 0 nil))))))))))
      (go 0))))

;;; ------------------------------------------------------------ as a theory

"The bound literal l (of an atom) asserts."
(define* assert-atom! (subr cb-eff (simplex int atom int) ints)
  (lambda (sx l a stamp)
    (let ((x (extract a x)) (le (extract a le)) (k (extract a k)) (int? (int-var? sx (extract a x))))
      (if (lit-negative? l)
          ;; not (x <= k): x > k;  not (x >= k): x < k.
          (if le
              (if int? (assert-bound! sx x #f (rat+ k rat-1) rat-0 l stamp) (assert-bound! sx x #f k rat-1 l stamp))
              (if int? (assert-bound! sx x #t (rat- k rat-1) rat-0 l stamp) (assert-bound! sx x #t k (rat-neg rat-1) l stamp)))
          (assert-bound! sx x le k rat-0 l stamp)))))

(define* conflict-clause (subr cb-eff (ints) theory-answer)
  (lambda (lits) (letrec ((go (subr cb-eff (ints) ints) (lambda (l) (if (null? l) nil (cons (lit-neg (car l)) (go (cdr l)))))))
                   (t-conflict (go lits)))))

(define* theory-check (subr cb-eff (simplex bool) theory-answer)
  (lambda (sx final?)
    (let* ((s (extract sx solver)) (n (sat-trail-size s)))
      (letrec ((go (subr cb-eff (int) theory-answer)
                 (lambda (i)
                   (if (< i n)
                       (let* ((l (sat-trail-lit s i)) (v (lit-var l))
                              (has (and (< v (array-length (get (extract sx has-atom)))) (array-ref (get (extract sx has-atom)) v)))
                              (confl (if has (assert-atom! sx l (array-ref (get (extract sx atoms)) v) i) nil)))
                         (if (pair? confl)
                             (begin (set (extract sx qhead) (+ i 1)) (conflict-clause confl))
                             (go (+ i 1))))
                       (begin
                         (set (extract sx qhead) n)
                         (let ((confl (check! sx)))
                           (cond ((pair? confl) (conflict-clause confl))
                                 (final? (final-check! sx))
                                 (else (t-ok)))))))))
        (go (get (extract sx qhead)))))))

"At a full assignment: make the integer variables integers. First
integer equalities; then patching: an integer nonbasic variable with a
value not an integer is moved to the integer below (still within its
bounds, which are integers), and the tableau checked again; then the cube
test, cuts, and branching."
(define* final-check! (subr cb-eff (simplex) theory-answer)
  (lambda (sx)
    (let ((d (diophantine-conflict sx)))
      (if (pair? d) (conflict-clause d) (final-check-2! sx)))))

(define* final-check-2! (subr cb-eff (simplex) theory-answer)
  (lambda (sx)
    (cond ((patch! sx)
           (let ((confl (check! sx))) (if (pair? confl) (conflict-clause confl) (final-check-2! sx))))
          ((< (fractional sx #f) 0) (begin (fix-delta! sx) (t-ok)))
          (else
           (begin
             (set (extract sx finals) (+ 1 (get (extract sx finals))))
             ;; Cuts alone can follow each other for ever: one time in three.
             (cond ((and (= 1 (modulo (get (extract sx finals)) 4)) (cube! sx)) (begin (fix-delta! sx) (t-ok)))
                   ((and (get (extract sx cuts)) (= 0 (modulo (get (extract sx finals)) 3)))
                    (let ((c (cut! sx))) (if (pair? c) (t-lemma c) (branch! sx))))
                   (else (branch! sx))))))))

;;; ------------------------------------------------------------ the unit cube test
;;; Bromberger and Weidenbach, "Fast Cube Tests for LIA Constraint
;;; Solving" (IJCAR 2016): if the bounds, each made tighter by half the
;;; 1-norm of its form's coefficients (s = a.x <= u becomes s <= u - |a|/2,
;;; and x <= u becomes x <= u - 1/2), have a rational solution, rounding it
;;; gives an integer solution of the bounds. A variable fixed by its bounds
;;; keeps its value, and is left out of the norms. Only when every variable
;;; is an integer. Whether it found a solution, which is then the
;;; assignment.

(define* touch-basics! (subr cb-eff (simplex) unit)
  (lambda (sx) (letrec ((go (subr cb-eff (int) unit) (lambda (r) (if (= r (get (extract sx nrows))) #u (begin (touch! sx (array-ref (basic sx) r)) (go (+ r 1)))))))
                 (go 0))))

(define* copy-rats (subr cb-eff (rats) rats)
  (lambda (v) (let ((w (the rats (make-array (array-length v) rat-0))))
                (letrec ((go (subr cb-eff (int) rats) (lambda (i) (if (= i (array-length v)) w (begin (array-set! w i (array-ref v i)) (go (+ i 1)))))))
                  (go 0)))))

"Half the total of the absolute values of the coefficients of x's form over
the variables that are not slacks, those not fixed."
(define* half-norm (subr cb-eff (simplex int bools) rat)
  (lambda (sx x fixed)
    (if (slack? sx x)
        (letrec ((go (subr cb-eff (sform rat) rat)
                   (lambda (f total) (if (null? f) (rat/ total (int->rat 2))
                                       (go (cdr f) (if (array-ref fixed (extract (car f) x)) total (rat+ total (rat-abs (extract (car f) c)))))))))
          (go (expand sx x) rat-0))
        (make-rat 1 2))))

"q rounded to the nearest integer, ties to even (Scheme's `round`)."
(define* rat-round (subr cb-eff (rat) int)
  (lambda (q)
    (let* ((f (rat-floor q)) (twice (- (* 2 (rat-num q)) (* (* 2 f) (rat-den q)))))   ; 2 (q - f) d
      (cond ((< twice (rat-den q)) f)
            ((> twice (rat-den q)) (+ f 1))
            ((= 0 (remainder f 2)) f)
            (else (+ f 1))))))

(define* cube! (subr cb-eff (simplex) bool)
  (lambda (sx)
    (let ((n (simplex-nvars sx)))
      (and (letrec ((go (subr cb-eff (int) bool) (lambda (x) (or (= x n) (and (int-var? sx x) (go (+ x 1))))))) (go 0))
           (let* ((fixed (let ((v (the bools (make-array n #f))))
                           (letrec ((go (subr cb-eff (int) bools)
                                      (lambda (x) (if (= x n) v
                                                      (begin (array-set! v x (and (> (array-ref (lor sx) x) 0) (> (array-ref (hir sx) x) 0)
                                                                                  (rat= (array-ref (loc sx) x) (array-ref (hic sx) x))))
                                                             (go (+ x 1)))))))
                             (go 0))))
                  (lows (copy-rats (loc sx))) (highs (copy-rats (hic sx)))
                  ;; (A fixed slack whose form has variables not fixed leaves no room.)
                  (room? (letrec ((go (subr cb-eff (int) bool)
                                    (lambda (x)
                                      (cond ((= x n) #t)
                                            ((array-ref fixed x)
                                             (and (or (not (slack? sx x)) (rat-zero? (half-norm sx x fixed))) (go (+ x 1))))
                                            (else
                                             (let ((w (half-norm sx x fixed)))
                                               (begin
                                                 (if (> (array-ref (lor sx) x) 0) (array-set! (loc sx) x (rat+ (array-ref (loc sx) x) w)) #u)
                                                 (if (> (array-ref (hir sx) x) 0) (array-set! (hic sx) x (rat- (array-ref (hic sx) x) w)) #u)
                                                 (and (not (and (> (array-ref (lor sx) x) 0) (> (array-ref (hir sx) x) 0)
                                                                (rat< (array-ref (hic sx) x) (array-ref (loc sx) x))))
                                                      (go (+ x 1))))))))))
                           (go 0)))
                  (solved? (and room?
                                (begin
                                  ;; Nonbasic variables are kept within bounds.
                                  (letrec ((go (subr cb-eff (int) unit)
                                             (lambda (x) (if (= x n) #u
                                                             (begin (if (>= (array-ref (row-of sx) x) 0) #u
                                                                        (cond ((below-lower? sx x) (update! sx x (array-ref (loc sx) x) rat-0))
                                                                              ((above-upper? sx x) (update! sx x (array-ref (hic sx) x) rat-0))
                                                                              (else #u)))
                                                                    (go (+ x 1)))))))
                                    (go 0))
                                  (touch-basics! sx)
                                  (null? (check! sx))))))
             (begin
               (set (extract sx loc) lows)
               (set (extract sx hic) highs)
               (touch-basics! sx)
               (and solved? (round-assignment! sx fixed))))))))

"Round the values of the variables that are not slacks, and make the
slacks' values agree (each slack's form has only variables made before
it). This satisfies every row. Whether the bounds hold (they should)."
(define* round-assignment! (subr cb-eff (simplex bools) bool)
  (lambda (sx fixed)
    (let ((n (simplex-nvars sx)) (vcs (vc sx)))
      (begin
        (letrec ((go (subr cb-eff (int) unit)
                   (lambda (x)
                     (if (= x n) #u
                         (begin
                           (array-set! vcs x
                                       (cond ((slack? sx x)
                                              (letrec ((total (subr cb-eff (sform rat) rat)
                                                              (lambda (f s) (if (null? f) s (total (cdr f) (rat+ s (rat* (extract (car f) c) (array-ref vcs (extract (car f) x)))))))))
                                                (total (array-ref (get (extract sx defs)) x) rat-0)))
                                             ((array-ref fixed x) (array-ref vcs x))
                                             (else (int->rat (rat-round (array-ref vcs x))))))
                           (array-set! (vk sx) x rat-0)
                           (go (+ x 1)))))))
          (go 0))
        (touch-basics! sx)
        (letrec ((go (subr cb-eff (int) bool)
                   (lambda (x) (or (= x n) (and (not (below-lower? sx x)) (not (above-upper? sx x)) (rat-int? (array-ref vcs x)) (go (+ x 1)))))))
          (go 0))))))

;;; ------------------------------------------------------------ cuts
;;; A Gomory mixed-integer cut, if a row of an integer basic variable with a
;;; value not an integer has all its nonbasic variables at bounds: then the
;;; row and those bounds imply that a total of the nonbasic variables'
;;; distances from their bounds is at least 1, which the current values are
;;; not. The lemma (cut not-bound ...), the cut a new atom; or none.

(define* frac (subr cb-eff (rat) rat) (lambda (q) (rat- q (int->rat (rat-floor q)))))
(define-type gterm (productof (j int) (lower bool) (a rat)))

(define* cut! (subr cb-eff (simplex) ints)
  (lambda (sx)
    (letrec ((go (subr cb-eff (int) ints)
               (lambda (r)
                 (if (>= r (get (extract sx nrows))) nil
                     (let* ((i (array-ref (basic sx) r)) (b (array-ref (vc sx) i))
                            (c (if (and (int-var? sx i) (rat-zero? (array-ref (vk sx) i)) (not (rat-int? b))) (gomory sx r b) nil)))
                       (if (pair? c) c (go (+ r 1))))))))
      (go 0))))

(define* gomory (subr cb-eff (simplex int rat) ints)
  (lambda (sx r b)
    (let ((vars (rvars sx r)) (coefs (rcoefs sx r)) (n (rlen sx r)) (f0 (frac b)))
      ;; Each nonbasic variable with whether at its lower bound, and its
      ;; coefficient; or none if one is not at a bound.
      (letrec ((collect (subr cb-eff (int (listof gterm acyclic)) (productof (ok bool) (ts (listof gterm acyclic))))
                 (lambda (e acc)
                   (if (= e n) (product (ok #t) (ts acc))
                       (let* ((j (array-ref vars e)) (a (make-rat (array-ref coefs e) (rden sx r)))
                              (c (array-ref (vc sx) j)) (k (array-ref (vk sx) j)))
                         (cond ((and (> (array-ref (lor sx) j) 0) (rat= c (array-ref (loc sx) j)) (rat= k (array-ref (lok sx) j)))
                                (collect (+ e 1) (cons (product (j j) (lower #t) (a a)) acc)))
                               ((and (> (array-ref (hir sx) j) 0) (rat= c (array-ref (hic sx) j)) (rat= k (array-ref (hik sx) j)))
                                (collect (+ e 1) (cons (product (j j) (lower #f) (a a)) acc)))
                               (else (product (ok #f) (ts nil)))))))))
        (let ((terms (collect 0 nil)))
          (if (not (extract terms ok)) nil
              ;; x_i = b + total a'_j t_j, t_j >= 0 the distance of x_j from its
              ;; bound; the cut is total g_j t_j >= 1.
              (letrec ((go (subr cb-eff ((listof gterm acyclic) sform rat ints) ints)
                         (lambda (ts form rhs reasons)
                           (if (null? ts) (if (pair? form) (make-cut! sx form rhs reasons) nil)
                               (let* ((j (extract (car ts) j)) (lower? (extract (car ts) lower)) (a (extract (car ts) a))
                                      (abar (rat-neg (if lower? a (rat-neg a))))
                                      (g (if (int-var? sx j)
                                             (let ((fj (frac abar)))
                                               (if (rat<= fj f0) (rat/ fj f0) (rat/ (rat- rat-1 fj) (rat- rat-1 f0))))
                                             (if (rat< rat-0 abar) (rat/ abar f0) (rat/ (rat-neg abar) (rat- rat-1 f0))))))
                                 (cond ((rat-zero? g) (go (cdr ts) form rhs reasons))
                                       (lower? (go (cdr ts) (cons (product (x j) (c g)) form) (rat+ rhs (rat* g (array-ref (loc sx) j)))
                                                   (cons (array-ref (lor sx) j) reasons)))
                                       (else (go (cdr ts) (cons (product (x j) (c (rat-neg g))) form) (rat- rhs (rat* g (array-ref (hic sx) j)))
                                                 (cons (array-ref (hir sx) j) reasons)))))))))
                (go (extract terms ts) nil rat-1 nil))))))))

"The cut total form >= rhs as a new atom, and the lemma: the reasons imply it."
(define* make-cut! (subr cb-eff (simplex sform rat ints) ints)
  (lambda (sx form rhs reasons)
    (let* ((int? (letrec ((go (subr cb-eff (sform) bool) (lambda (f) (or (null? f) (and (int-var? sx (extract (car f) x)) (go (cdr f)))))))
                   (go form)))
           ;; Over integers: integer coefficients, and the bound rounded up.
           (scale (if int? (letrec ((go (subr cb-eff (sform int) int) (lambda (f l) (if (null? f) l (go (cdr f) (lcm l (rat-den (extract (car f) c))))))))
                             (go form 1))
                      1))
           (form (letrec ((go (subr cb-eff (sform) sform) (lambda (f) (if (null? f) nil (cons (product (x (extract (car f) x)) (c (rat* (int->rat scale) (extract (car f) c)))) (go (cdr f)))))))
                   (go form)))
           (rhs (if int? (int->rat (rat-ceiling (rat* (int->rat scale) rhs))) rhs))
           (x (simplex-slack! sx (sform-sort form) int?))
           (v (sat-new-var! (extract sx solver)))
           (l (make-lit v #f)))
      (begin (simplex-add-atom! sx v x #f rhs)
             (cons l (letrec ((go (subr cb-eff (ints) ints) (lambda (l) (if (null? l) nil (cons (lit-neg (car l)) (go (cdr l)))))))
                       (go reasons)))))))

;;; ------------------------------------------------------------ integer equalities
;;; Those the bounds now assert (a slack or a variable with equal bounds)
;;; may have no integer solution even though branching takes long to find
;;; out (x = y, 2y = 2z + 1). They are solved over the integers, after
;;; Griggio, "A Practical Approach to Satisfiability Modulo Linear Integer
;;; Arithmetic" (JSAT 2012): divide by the gcd of the coefficients (a
;;; constant it does not divide means no solution); eliminate a variable of
;;; coefficient 1 or -1; else make the coefficients smaller with a new
;;; variable. Each equation keeps the bound literals it comes from, which
;;; explain a conflict. Those literals, or none.

"An equation: total of the form = c, from these bound literals."
(define-type equation (productof (form sform) (c rat) (src ints)))
(define-type equations (listof equation acyclic))

(define* poly+ (subr cb-eff (sform sform) sform)
  (lambda (p q)
    (cond ((null? p) q)
          ((null? q) p)
          ((= (extract (car p) x) (extract (car q) x))
           (let ((c (rat+ (extract (car p) c) (extract (car q) c))))
             (if (rat-zero? c) (poly+ (cdr p) (cdr q)) (cons (product (x (extract (car p) x)) (c c)) (poly+ (cdr p) (cdr q))))))
          ((< (extract (car p) x) (extract (car q) x)) (cons (car p) (poly+ (cdr p) q)))
          (else (cons (car q) (poly+ p (cdr q)))))))
(define* poly-scale (subr cb-eff (rat sform) sform)
  (lambda (c p) (if (rat-zero? c) nil
                    (letrec ((go (subr cb-eff (sform) sform) (lambda (p) (if (null? p) nil (cons (product (x (extract (car p) x)) (c (rat* c (extract (car p) c)))) (go (cdr p)))))))
                      (go p)))))
(define* poly-without (subr cb-eff (int sform) sform)
  (lambda (x p) (cond ((null? p) nil) ((= (extract (car p) x) x) (poly-without x (cdr p))) (else (cons (car p) (poly-without x (cdr p)))))))

"The form of x over variables that are not slacks."
(define expand (subr cb-eff (simplex int) sform)
  (lambda (sx x)
    (cond ((not (slack? sx x)) (list (product (x x) (c rat-1))))
          ((array-ref (get (extract sx has-expanded)) x) (array-ref (get (extract sx expanded)) x))
          (else
           (let ((p (letrec ((go (subr cb-eff (sform sform) sform)
                               (lambda (f acc) (if (null? f) acc (go (cdr f) (poly+ acc (poly-scale (extract (car f) c) (expand sx (extract (car f) x)))))))))
                      (go (array-ref (get (extract sx defs)) x) nil))))
             (begin (array-set! (get (extract sx expanded)) x p) (array-set! (get (extract sx has-expanded)) x #t) p))))))

(define* current-equalities (subr cb-eff (simplex) equations)
  (lambda (sx)
    (letrec ((go (subr cb-eff (int equations) equations)
               (lambda (x acc)
                 (if (= x (simplex-nvars sx)) acc
                     (go (+ x 1)
                         (if (and (int-var? sx x) (> (array-ref (lor sx) x) 0) (> (array-ref (hir sx) x) 0)
                                  (rat= (array-ref (loc sx) x) (array-ref (hic sx) x))
                                  (rat-zero? (array-ref (lok sx) x)) (rat-zero? (array-ref (hik sx) x)))
                             (let ((form (expand sx x)))
                               (if (letrec ((all (subr cb-eff (sform) bool) (lambda (f) (or (null? f) (and (rat-int? (extract (car f) c)) (all (cdr f)))))))
                                     (all form))
                                   (cons (product (form form) (c (array-ref (loc sx) x)) (src (list (array-ref (lor sx) x) (array-ref (hir sx) x)))) acc)
                                   acc))
                             acc))))))
      (go 0 nil))))

(define* member-int? (subr cb-eff (int ints) bool) (lambda (x l) (and (pair? l) (or (= x (car l)) (member-int? x (cdr l))))))
(define* union-ints (subr cb-eff (ints ints) ints)
  (lambda (a b) (cond ((null? a) b) ((member-int? (car a) b) (union-ints (cdr a) b)) (else (cons (car a) (union-ints (cdr a) b))))))

"In e, replace x by the polynomial p plus constant k (x = p + k), with the
sources of that substitution added if x occurs."
(define* substitute (subr cb-eff (equation int sform rat ints) equation)
  (lambda (e x p k sources)
    (letrec ((find (subr cb-eff (sform) rat) (lambda (f) (cond ((null? f) rat-0) ((= (extract (car f) x) x) (extract (car f) c)) (else (find (cdr f)))))))
      (let ((a (find (extract e form))))
        (if (rat-zero? a) e
            (product (form (poly+ (poly-without x (extract e form)) (poly-scale a p)))
                     (c (rat- (extract e c) (rat* a k)))
                     (src (union-ints sources (extract e src)))))))))
(define* substitute-all (subr cb-eff (equations int sform rat ints) equations)
  (lambda (es x p k src) (if (null? es) nil (cons (substitute (car es) x p k src) (substitute-all (cdr es) x p k src)))))

(define* solve-equalities (subr cb-eff (equations int) ints)
  (lambda (eqs fresh)
    (letrec ((go (subr cb-eff (equations int int) ints)
               (lambda (eqs fresh steps)
                 (cond
                  ((null? eqs) nil)
                  ((> steps 10000) nil)              ; (it ends; this is a guard)
                  (else
                   (let* ((e (car eqs)) (form (extract e form)) (c (extract e c)))
                     (if (null? form)
                         (if (rat-zero? c) (go (cdr eqs) fresh (+ steps 1)) (extract e src))
                         (let ((g (letrec ((gg (subr cb-eff (sform int) int) (lambda (f g) (if (null? f) g (gg (cdr f) (gcd g (rat-num (extract (car f) c))))))))
                                    (gg form 0))))
                           (if (not (rat-int? (rat/ c (int->rat g)))) (extract e src)
                               (let* ((form (poly-scale (make-rat 1 g) form))
                                      (c (rat/ c (int->rat g)))
                                      (m (letrec ((least (subr cb-eff (sform smono) smono)
                                                    (lambda (f b) (if (null? f) b (least (cdr f) (if (rat< (rat-abs (extract (car f) c)) (rat-abs (extract b c))) (car f) b))))))
                                           (least form (car form))))
                                      (x (extract m x)) (a (extract m c)) (src (extract e src)))
                                 (if (rat= (rat-abs a) rat-1)
                                     ;; x = (c - rest) / a
                                     (let ((p (poly-scale (rat-neg a) (poly-without x form))) (k (rat* a c)))
                                       (go (substitute-all (cdr eqs) x p k src) fresh (+ steps 1)))
                                     ;; a x + total a_j x_j = c, a > 0 (else negate):
                                     ;; x = s - total floor(a_j/a) x_j + floor(c/a)
                                     ;; leaves a s + total (a_j mod a) x_j = c mod a.
                                     (let* ((sign (if (rat< a rat-0) (rat-neg rat-1) rat-1))
                                            (a (rat* sign a))
                                            (rest (poly-scale sign (poly-without x form)))
                                            (c (rat* sign c))
                                            (p (poly+ (list (product (x fresh) (c rat-1)))
                                                      (letrec ((fl (subr cb-eff (sform) sform)
                                                                 (lambda (f) (if (null? f) nil
                                                                                 (let ((q (int->rat (- 0 (rat-floor (rat/ (extract (car f) c) a))))))
                                                                                   (if (rat-zero? q) (fl (cdr f)) (cons (product (x (extract (car f) x)) (c q)) (fl (cdr f)))))))))
                                                        (fl rest))))
                                            (k (int->rat (rat-floor (rat/ c a))))
                                            (e (product (form (the sform (cons (product (x x) (c a)) rest))) (c c) (src src))))
                                       (go (substitute-all (cons e (cdr eqs)) x p k src) (+ fresh 1) (+ steps 1))))))))))))))
      (go eqs fresh 0))))

(define* diophantine-conflict (subr cb-eff (simplex) ints)
  (lambda (sx)
    (let ((eqs (current-equalities sx)))
      ;; One alone was normalized when made.
      (if (and (pair? eqs) (pair? (cdr eqs))) (solve-equalities eqs (simplex-nvars sx)) nil))))

;;; ------------------------------------------------------------ branch and bound

"Whether some nonbasic variable was moved."
(define* patch! (subr cb-eff (simplex) bool)
  (lambda (sx)
    (letrec ((go (subr cb-eff (int bool) bool)
               (lambda (x moved?)
                 (if (= x (simplex-nvars sx)) moved?
                     (let ((c (array-ref (vc sx) x)))
                       (if (and (int-var? sx x) (< (array-ref (row-of sx) x) 0) (not (rat-int? c)))
                           (begin (update! sx x (int->rat (rat-floor c)) rat-0) (go (+ x 1) #t))
                           (go (+ x 1) moved?)))))))
      (go 0 #f))))

"The least integer variable (a slack, if `slacks?`) whose value is not an
integer, or -1."
(define* fractional (subr cb-eff (simplex bool) int)
  (lambda (sx slacks?)
    (letrec ((go (subr cb-eff (int) int)
               (lambda (x)
                 (cond ((= x (simplex-nvars sx)) -1)
                       ((and (int-var? sx x)
                             (not (and (rat-int? (array-ref (vc sx) x)) (rat-zero? (array-ref (vk sx) x))))
                             (or (not slacks?) (slack? sx x)))
                        x)
                       (else (go (+ x 1)))))))
      (go 0))))

"Branch and bound: for an integer variable with a value not an integer, a
new atom x <= floor(value) for the SAT solver to decide (its negation is x
>= floor(value) + 1). Slack variables are tried first: a total like x + y =
3/2 is refuted at once by branching on the total, while branching on x and y
walks along the line for ever."
(define* branch! (subr cb-eff (simplex) theory-answer)
  (lambda (sx)
    (let ((x (let ((x (fractional sx #t))) (if (>= x 0) x (fractional sx #f)))))
      (if (< x 0) (t-ok)
          (let* ((c (array-ref (vc sx) x))
                 (f (if (and (rat-int? c) (rat< (array-ref (vk sx) x) rat-0)) (- (rat-num c) 1) (rat-floor c)))
                 (key (string-append (int->string x) (string-append ":" (int->string f)))))
            (begin
              (if (table-has? (extract sx branches) key) #u
                  (let ((v (sat-new-var! (extract sx solver))))
                    (begin
                      (table-set! (extract sx branches) key v)
                      ;; Not simplex-add-atom!'s list of a variable's atoms
                      ;; (lockpick's, for propagation): propagating branch atoms
                      ;; made branch and bound wander.
                      (simplex-add-atom! sx v x #t (int->rat f))
                      ;; Try first the side toward 0.
                      (sat-set-phase! (extract sx solver) v (rat< c rat-0)))))
              (t-continue)))))))

"A value for delta small enough that every bound holds of the values with
it."
(define* fix-delta! (subr cb-eff (simplex) unit)
  (lambda (sx)
    (letrec ((limit (subr cb-eff (rat rat rat rat rat) rat)
               ;; d, made small enough that c1 + k1 d <= c2 + k2 d.
               (lambda (d c1 k1 c2 k2) (if (and (rat< c1 c2) (rat< k2 k1)) (rat-min d (rat/ (rat- c2 c1) (rat- k1 k2))) d)))
             (go (subr cb-eff (int rat) unit)
               (lambda (x d)
                 (if (= x (simplex-nvars sx)) (set (extract sx delta) d)
                     (let* ((c (array-ref (vc sx) x)) (k (array-ref (vk sx) x))
                            (d (if (> (array-ref (lor sx) x) 0) (limit d (array-ref (loc sx) x) (array-ref (lok sx) x) c k) d))
                            (d (if (> (array-ref (hir sx) x) 0) (limit d c k (array-ref (hic sx) x) (array-ref (hik sx) x)) d)))
                       (go (+ x 1) d))))))
      (go 0 rat-1))))

"The value of x in the model (after a check that found one)."
(define* simplex-value (subr cb-eff (simplex int) rat)
  (lambda (sx x) (rat+ (array-ref (vc sx) x) (rat* (get (extract sx delta)) (array-ref (vk sx) x)))))

(define* simplex-theory (subr cb-eff (simplex) theory)
  (lambda (sx)
    (product (check (lambda ((final? bool)) (theory-check sx final?)))
             (backtrack (lambda ((n int)) (backtrack! sx n))))))
