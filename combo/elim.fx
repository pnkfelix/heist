;;; elim.fx: bounded variable elimination (Een and Biere, "Effective
;;; Preprocessing in SAT through Variable and Clause Elimination", 2005),
;;; with their subsumption and self-subsuming resolution, before search, of
;;; a CNF solved once (lockpick's `(lockpick elim)`).
;;;
;;; A variable x is eliminated by replacing the clauses with x and those
;;; with not-x by their resolvents on x (dropping the tautologies), when
;;; that does not make more clauses. The result is satisfiable just when the
;;; CNF is, and a model of it is extended to one of the CNF by giving the
;;; eliminated variables values, the last eliminated first
;;; (`extend-model!`). Units found on the way are propagated.
;;;
;;; Literals are sat.fx's. With a proof kept, the changes are its DRAT
;;; lines: a resolvent is implied by unit propagation from the two clauses
;;; it comes from, and is added before they are deleted.

(module-parameters ((m-sat (load-moduleof "sat.fx"))))
(hide (define kit-strings (load-module "../kit/strings.fx"))
      (import kit-strings string-concatenate))

;; The limits: a resolvent of more literals stops the elimination of a
;; variable (as in MiniSat), as do more than max-pairs pairs of clauses to
;; resolve. A clause is checked against those with its rarest variable only
;; when they are at most max-subsume-occs. The budget: the literals that
;; may be looked at in resolving, in all, after which nothing more is
;; eliminated.
(define max-resolvent int 20)
(define max-pairs int 2000)
(define max-subsume-occs int 1000)
(define initial-budget int 30000000)

(define-type clause-list (listof ivec acyclic))
"An elimination: the variable's positive literal, and its clauses."
(define-type elim-entry (productof (x int) (clauses clause-list)))
(define-type elim-stack (listof elim-entry acyclic))

"The state. clauses: those made so far (an empty array for one deleted),
and their signatures; occs: for each literal, the clauses with it (some
deleted since), and noccs the number of live ones. vals: for each literal,
whether it is a unit; units those literals, and queue those not yet
propagated. stamp and mark (by literal) for resolving; touched (by
variable) for what to look at again; limit for count-resolvents and
subsume-check. squeue: the clauses added since they were last checked for
clauses they subsume. stack: the latest elimination first."
(define-type elim-state
  (productof
   (clauses (ref ivecs @cb)) (sigs (ref ivec @cb)) (nclauses (ref int @cb))
   (occs (arrayof ints @cb)) (noccs ivec) (vals (arrayof bool @cb))
   (units (ref ints @cb)) (queue (ref ints @cb))
   (mark ivec) (stamp (ref int @cb)) (touched (arrayof bool @cb))
   (squeue (ref ints @cb)) (stack (ref elim-stack @cb))
   (budget (ref int @cb)) (limit (ref int @cb))
   (proof bool) (proof-lines (ref strings @cb))
   (ok (ref bool @cb))))

(define* ec (subr (read @cb) (elim-state int) ivec) (lambda (st i) (array-ref (get (extract st clauses)) i)))
(define* live? (subr (read @cb) (ivec) bool) (lambda (c) (> (array-length c) 0)))
(define* st-ok? (subr (read @cb) (elim-state) bool) (lambda (st) (get (extract st ok))))
(define* noccs (subr (read @cb) (elim-state int) int) (lambda (st l) (array-ref (extract st noccs) l)))

(define* proof-line! (subr cb-eff (elim-state string ivec) unit)
  (lambda (st prefix lits)
    (if (not (extract st proof)) #u
        (letrec ((go (subr cb-eff (int strings) strings)
                   (lambda (k acc) (if (= k (array-length lits)) acc (go (+ k 1) (cons " " (cons (int->string (lit->int (array-ref lits k))) acc)))))))
          (set (extract st proof-lines) (cons (string-concatenate (reverse (cons "0\n" (go 0 (list prefix))))) (get (extract st proof-lines))))))))

"A clause's variables, as bits (v mod 32): if c subsumes d (but for a
literal negated), c's bits are among d's."
(define* signature (subr cb-eff (ivec) int)
  (lambda (c) (letrec ((go (subr cb-eff (int int) int)
                         (lambda (k sig) (if (= k (array-length c)) sig (go (+ k 1) (bitwise-ior sig (arithmetic-shift 1 (bitwise-and (lit-var (array-ref c k)) 31))))))))
                (go 0 0))))

"Add a clause (distinct literals, not a tautology, with no literal of a
unit): a unit becomes one, and the empty clause makes the CNF
unsatisfiable."
(define el-add! (subr cb-eff (elim-state ivec) unit)
  (lambda (st c)
    (cond ((= 0 (array-length c)) (set (extract st ok) #f))
          ((= 1 (array-length c)) (el-unit! st (array-ref c 0)))
          (else
           (let ((n (get (extract st nclauses))))
             (begin
               (if (< n (array-length (get (extract st clauses)))) #u
                   (begin (set (extract st clauses) (grow-ivecs (get (extract st clauses)) n))
                          (set (extract st sigs) (grow-ivec (get (extract st sigs)) n 0))))
               (array-set! (get (extract st clauses)) n c)
               (array-set! (get (extract st sigs)) n (signature c))
               (set (extract st nclauses) (+ n 1))
               (set (extract st squeue) (cons n (get (extract st squeue))))
               (letrec ((go (subr cb-eff (int) unit)
                          (lambda (k)
                            (if (= k (array-length c)) #u
                                (let ((l (array-ref c k)))
                                  (begin (array-set! (extract st occs) l (cons n (array-ref (extract st occs) l)))
                                         (array-set! (extract st noccs) l (+ 1 (noccs st l)))
                                         (array-set! (extract st touched) (lit-var l) #t)
                                         (go (+ k 1))))))))
                 (go 0))))))))

(define* no-clause (subr (alloc @cb) () ivec) (lambda () (the ivec (make-array 0 0))))

(define* el-delete! (subr cb-eff (elim-state int) unit)
  (lambda (st i)
    (let ((c (ec st i)))
      (begin
        (proof-line! st "d " c)
        (array-set! (get (extract st clauses)) i (no-clause))
        (letrec ((go (subr cb-eff (int) unit)
                   (lambda (k) (if (= k (array-length c)) #u
                                   (let ((l (array-ref c k)))
                                     (begin (array-set! (extract st noccs) l (- (noccs st l) 1))
                                            (array-set! (extract st touched) (lit-var l) #t)
                                            (go (+ k 1))))))))
          (go 0))))))

(define el-unit! (subr cb-eff (elim-state int) unit)
  (lambda (st l)
    (let ((vals (extract st vals)))
      (cond ((array-ref vals l) #u)
            ((array-ref vals (lit-neg l)) (set (extract st ok) #f))
            (else (begin (array-set! vals l #t)
                         (set (extract st units) (cons l (get (extract st units))))
                         (set (extract st queue) (cons l (get (extract st queue))))))))))

"c without x."
(define* without (subr cb-eff (ivec int) ivec)
  (lambda (c x)
    (let ((d (the ivec (make-array (- (array-length c) 1) 0))))
      (letrec ((go (subr cb-eff (int int) ivec)
                 (lambda (i j) (cond ((= i (array-length c)) d)
                                     ((= (array-ref c i) x) (go (+ i 1) j))
                                     (else (begin (array-set! d j (array-ref c i)) (go (+ i 1) (+ j 1))))))))
        (go 0 0)))))

"Propagate the units: delete the clauses they satisfy, and remove their
negations from the others."
(define* el-propagate! (subr cb-eff (elim-state) unit)
  (lambda (st)
    (if (not (and (st-ok? st) (pair? (get (extract st queue))))) #u
        (let ((l (car (get (extract st queue)))) (occs (extract st occs)))
          (begin
            (set (extract st queue) (cdr (get (extract st queue))))
            (letrec ((del (subr cb-eff (ints) unit)
                       (lambda (is) (if (null? is) #u (begin (if (live? (ec st (car is))) (el-delete! st (car is)) #u) (del (cdr is)))))))
              (del (array-ref occs l)))
            (array-set! occs l nil)
            (let ((nl (lit-neg l)))
              (begin
                (letrec ((shorten (subr cb-eff (ints) unit)
                           (lambda (is)
                             (if (null? is) #u
                                 (let ((c (ec st (car is))))
                                   (begin
                                     (if (and (live? c) (st-ok? st))
                                         (let ((d (without c nl)))
                                           (begin (proof-line! st "" d) (el-delete! st (car is)) (el-add! st d)))
                                         #u)
                                     (shorten (cdr is))))))))
                  (shorten (array-ref occs nl)))
                (array-set! occs nl nil)))
            (el-propagate! st))))))

"The live clauses with literal l, which also become l's occurrences."
(define* live-occs! (subr cb-eff (elim-state int) ints)
  (lambda (st l)
    (let ((is (letrec ((go (subr cb-eff (ints ints) ints)
                         (lambda (is acc) (cond ((null? is) acc) ((live? (ec st (car is))) (go (cdr is) (cons (car is) acc))) (else (go (cdr is) acc))))))
                (go (array-ref (extract st occs) l) nil))))
      (begin (array-set! (extract st occs) l is) is))))

;;; ------------------------------------------------------------ resolving
;;; On x: the clauses with x are marked one at a time (mark-clause!), and
;;; resolved with each of those with not-x. The resolvents are counted
;;; first, and built only when x is to be eliminated.

(define* mark-clause! (subr cb-eff (elim-state ivec) unit)
  (lambda (st p)
    (let ((stamp (+ 1 (get (extract st stamp)))))
      (begin (set (extract st stamp) stamp)
             (letrec ((go (subr cb-eff (int) unit) (lambda (k) (if (= k (array-length p)) #u (begin (array-set! (extract st mark) (array-ref p k) stamp) (go (+ k 1)))))))
               (go 0))))))
(define* marked? (subr (read @cb) (elim-state int) bool)
  (lambda (st l) (= (array-ref (extract st mark) l) (get (extract st stamp)))))

"The size of the resolvent of the marked clause p with n (with nx), or -1
if it is a tautology."
(define* resolvent-size (subr cb-eff (elim-state ivec ivec int) int)
  (lambda (st p n nx)
    (letrec ((go (subr cb-eff (int int) int)
               (lambda (k size)
                 (if (= k (array-length n)) size
                     (let ((l (array-ref n k)))
                       (cond ((= l nx) (go (+ k 1) size))
                             ((marked? st (lit-neg l)) -1)
                             ((marked? st l) (go (+ k 1) size))
                             (else (go (+ k 1) (+ size 1)))))))))
      (go 0 (- (array-length p) 1)))))

"The resolvent of the marked clause p (with x) with n, of size literals."
(define* resolvent (subr cb-eff (elim-state ivec ivec int int) ivec)
  (lambda (st p n x size)
    (let ((r (the ivec (make-array size 0))))
      (letrec ((fill-p (subr cb-eff (int int) int)
                 (lambda (i j) (cond ((= i (array-length p)) j)
                                     ((= (array-ref p i) x) (fill-p (+ i 1) j))
                                     (else (begin (array-set! r j (array-ref p i)) (fill-p (+ i 1) (+ j 1)))))))
               (fill-n (subr cb-eff (int int) ivec)
                 (lambda (k j) (if (= k (array-length n)) r
                                   (let ((l (array-ref n k)))
                                     (if (or (marked? st l) (= l (lit-neg x))) (fill-n (+ k 1) j)
                                         (begin (array-set! r j l) (fill-n (+ k 1) (+ j 1)))))))))
        (fill-n 0 (fill-p 0 0))))))

"The number of resolvents on x (not tautologies) of the clauses pos with
those neg, or -1 if there are more than limit or one has more than
max-resolvent literals."
(define* count-resolvents (subr cb-eff (elim-state int ints ints int) int)
  (lambda (st x pos neg limit)
    (begin
      (set (extract st limit) limit)
      (letrec ((pair-up (subr cb-eff (ivec ints int) int)
                 (lambda (p ns count)
                   (if (null? ns) count
                       (let ((n (ec st (car ns))))
                         (begin
                           (set (extract st budget) (- (get (extract st budget)) (array-length n)))
                           (let ((size (resolvent-size st p n (lit-neg x))))
                             (cond ((< size 0) (pair-up p (cdr ns) count))
                                   ((or (> size max-resolvent) (>= count (get (extract st limit)))) -1)
                                   (else (pair-up p (cdr ns) (+ count 1))))))))))
               (outer (subr cb-eff (ints int) int)
                 (lambda (ps count)
                   (cond ((< count 0) -1)
                         ((null? ps) count)
                         (else (let ((p (ec st (car ps)))) (begin (mark-clause! st p) (outer (cdr ps) (pair-up p neg count)))))))))
        (outer pos 0)))))

"The resolvents (not tautologies) of the clauses pos with those neg on x."
(define* build-resolvents (subr cb-eff (elim-state int ints ints) clause-list)
  (lambda (st x pos neg)
    (letrec ((pair-up (subr cb-eff (ivec ints clause-list) clause-list)
               (lambda (p ns acc)
                 (if (null? ns) acc
                     (let* ((n (ec st (car ns))) (size (resolvent-size st p n (lit-neg x))))
                       (pair-up p (cdr ns) (if (< size 0) acc (cons (resolvent st p n x size) acc)))))))
             (outer (subr cb-eff (ints clause-list) clause-list)
               (lambda (ps acc)
                 (if (null? ps) acc
                     (let ((p (ec st (car ps)))) (begin (mark-clause! st p) (outer (cdr ps) (pair-up p neg acc))))))))
      (outer pos nil))))

"Eliminate variable v if that adds no clauses. Whether it did."
(define try-eliminate! (subr cb-eff (elim-state int) bool)
  (lambda (st v)
    (let* ((x (make-lit v #f)) (pos (live-occs! st x)) (neg (live-occs! st (lit-neg x)))
           (np (list-length pos)) (nn (list-length neg)))
      (and (<= (* np nn) max-pairs)
           (>= (count-resolvents st x pos neg (+ np nn)) 0)
           (let ((rs (build-resolvents st x pos neg)))
             (begin
               (letrec ((each (subr cb-eff (clause-list (subr cb-eff (ivec) unit)) unit) (lambda (l f) (if (null? l) #u (begin (f (car l)) (each (cdr l) f)))))
                        (each-i (subr cb-eff (ints) unit) (lambda (l) (if (null? l) #u (begin (el-delete! st (car l)) (each-i (cdr l)))))))
                 (begin
                   (each rs (lambda ((r ivec)) (proof-line! st "" r)))
                   (set (extract st stack)
                        (cons (product (x x) (clauses (letrec ((go (subr cb-eff (ints) clause-list) (lambda (is) (if (null? is) nil (cons (ec st (car is)) (go (cdr is)))))))
                                                        (go (el-append pos neg)))))
                              (get (extract st stack))))
                   (each-i pos)
                   (each-i neg)
                   (each rs (lambda ((r ivec)) (el-add! st r)))))
               (el-propagate! st)
               (subsume-all! st)
               #t))))))

(define* el-append (subr spin (ints ints) ints) (lambda (a b) (if (null? a) b (cons (car a) (el-append (cdr a) b)))))

;;; ------------------------------------------------------------ subsumption
;;; Each clause of the queue deletes the clauses it subsumes, and
;;; strengthens those it subsumes but for one literal, negated there
;;; (self-subsuming resolution: C or l and D or C or not-l give D or C,
;;; which replaces the second). The clauses to look at are those with the
;;; clause's rarest variable, either way.

(define subsume-all! (subr cb-eff (elim-state) unit)
  (lambda (st)
    (if (not (and (st-ok? st) (pair? (get (extract st squeue))) (> (get (extract st budget)) 0))) #u
        (let ((i (car (get (extract st squeue)))))
          (begin (set (extract st squeue) (cdr (get (extract st squeue))))
                 (if (live? (ec st i)) (begin (subsume-with! st i) (el-propagate! st)) #u)
                 (subsume-all! st))))))

"The literal of c whose variable has the fewest occurrences."
(define* rarest (subr cb-eff (elim-state ivec) int)
  (lambda (st c)
    (letrec ((go (subr cb-eff (int int) int)
               (lambda (k best)
                 (if (= k (array-length c)) best
                     (let ((l (array-ref c k)))
                       (go (+ k 1) (if (< (+ (noccs st l) (noccs st (lit-neg l))) (+ (noccs st best) (noccs st (lit-neg best)))) l best)))))))
      (go 1 (array-ref c 0)))))

(define subsume-with! (subr cb-eff (elim-state int) unit)
  (lambda (st i)
    (let* ((c (ec st i)) (x (rarest st c)))
      (if (> (+ (noccs st x) (noccs st (lit-neg x))) max-subsume-occs) #u
          (begin (mark-clause! st c)
                 (set (extract st limit) (array-length c))
                 (subsume-each! st i (live-occs! st x))
                 (subsume-each! st i (live-occs! st (lit-neg x))))))))

;; What subsume-check finds.
(define not-subsumed int -1)
(define subsumed int 0)

"Whether the marked clause, of (limit) literals, subsumes d: `subsumed`,
or the literal of d whose negation is in it if it subsumes d but for that,
or `not-subsumed`. Of d's first k literals, matched are in it, and flipped
is negated there (0: none)."
(define* subsume-check (subr cb-eff (elim-state ivec int int int) int)
  (lambda (st d k matched flipped)
    (if (= k (array-length d))
        (cond ((and (= matched (get (extract st limit))) (= flipped 0)) subsumed)
              ((and (> flipped 0) (= (+ matched 1) (get (extract st limit)))) flipped)
              (else not-subsumed))
        (let ((l (array-ref d k)))
          (cond ((marked? st l) (subsume-check st d (+ k 1) (+ matched 1) flipped))
                ((marked? st (lit-neg l)) (if (> flipped 0) not-subsumed (subsume-check st d (+ k 1) matched l)))
                (else (subsume-check st d (+ k 1) matched flipped)))))))

"Check the marked clause i against the clauses js."
(define subsume-each! (subr cb-eff (elim-state int ints) unit)
  (lambda (st i js)
    (if (or (null? js) (not (live? (ec st i)))) #u
        (let* ((j (car js)) (d (ec st j)))
          (begin
            (if (and (live? d) (not (= i j)) (>= (array-length d) (get (extract st limit)))
                     (= 0 (bitwise-and (array-ref (get (extract st sigs)) i) (bitwise-not (array-ref (get (extract st sigs)) j)))))
                (begin
                  (set (extract st budget) (- (get (extract st budget)) (array-length d)))
                  (let ((r (subsume-check st d 0 0 0)))
                    (cond ((= r subsumed) (el-delete! st j))
                          ((> r 0) (let ((e (without d r))) (begin (proof-line! st "" e) (el-delete! st j) (el-add! st e))))
                          (else #u))))
                #u)
            (subsume-each! st i (cdr js)))))))

;;; ------------------------------------------------------------ rounds

(define* eliminated? (subr (read @cb) (elim-state int) bool)
  (lambda (st v) (and (= 0 (noccs st (make-lit v #f))) (= 0 (noccs st (make-lit v #t))))))
(define* eligible? (subr cb-eff (elim-state int) bool)
  (lambda (st v)
    (let ((x (make-lit v #f)) (vals (extract st vals)))
      (not (or (array-ref vals x) (array-ref vals (lit-neg x)) (eliminated? st v))))))

"The touched variables, by the product of their numbers of occurrences,
which are then no longer touched."
(define* candidates (subr cb-eff (elim-state int) ints)
  (lambda (st nvars)
    (let* ((touched (extract st touched))
           (vs (letrec ((go (subr cb-eff (int ints) ints)
                          (lambda (v acc) (cond ((= v 0) acc)
                                                ((array-ref touched v) (begin (array-set! touched v #f) (go (- v 1) (cons v acc))))
                                                (else (go (- v 1) acc))))))
                 (go nvars nil)))
           (vec (list->ivec vs))
           (cost (lambda ((v int)) (* (noccs st (+ v v)) (noccs st (+ (+ v v) 1))))))
      (begin (ivec-sort! vec (array-length vec) (lambda ((a int) (b int)) (< (cost a) (cost b))))
             (ivec->list vec 0 (array-length vec))))))

"Eliminate what can be, in rounds: each looks at the variables touched
since the last, the fewest occurrences first."
(define* eliminate-all! (subr cb-eff (elim-state int) unit)
  (lambda (st nvars)
    (let ((vs (candidates st nvars)))
      (if (null? vs) #u
          (let ((any? (letrec ((go (subr cb-eff (ints bool) bool)
                                 (lambda (vs any?)
                                   (if (or (null? vs) (not (st-ok? st)) (<= (get (extract st budget)) 0)) any?
                                       (go (cdr vs) (or (and (eligible? st (car vs)) (try-eliminate! st (car vs))) any?))))))
                        (go vs #f))))
            (if (and any? (st-ok? st) (> (get (extract st budget)) 0)) (eliminate-all! st nvars) #u))))))

"The literals as a sorted array without duplicates, or an empty one for a
tautology (a clause read is never empty: lockpick's #f)."
(define-type normalized (productof (taut bool) (c ivec)))
(define* normalize (subr cb-eff (ints) normalized)
  (lambda (lits)
    (let ((v (list->ivec lits)))
      (begin
        (insertion-sort! v)
        (letrec ((go (subr cb-eff (int ints) normalized)
                   (lambda (i acc)
                     (cond ((= i (array-length v)) (product (taut #f) (c (list->ivec (reverse acc)))))
                           ((and (pair? acc) (= (car acc) (array-ref v i))) (go (+ i 1) acc))
                           ((and (pair? acc) (= (car acc) (lit-neg (array-ref v i)))) (product (taut #t) (c (no-clause))))
                           (else (go (+ i 1) (cons (array-ref v i) acc)))))))
          (go 0 nil))))))

"What elimination gives: whether the clauses may be satisfiable; if so,
clauses (lists of literals) to solve, and the stack for `extend-model!`;
and the proof's lines, newest first."
(define-type eliminated (productof (ok bool) (clauses (listof ints acyclic)) (stack elim-stack) (proof strings)))

"Eliminate what can be of `clauses` (lists of literals over variables 1 to
nvars), keeping a proof if `proof`."
(define* eliminate (subr cb-eff (int (listof ints acyclic) bool) eliminated)
  (lambda (nvars clauses proof)
    (let* ((nl (* 2 (+ nvars 1)))
           (st (the elim-state (product (clauses (new (the ivecs (make-array 1024 (no-clause))))) (sigs (new (the ivec (make-array 1024 0)))) (nclauses (new 0))
                        (occs (the (arrayof ints @cb) (make-array nl (the ints nil)))) (noccs (the ivec (make-array nl 0)))
                        (vals (the (arrayof bool @cb) (make-array nl #f)))
                        (units (new (the ints nil))) (queue (new (the ints nil)))
                        (mark (the ivec (make-array nl 0))) (stamp (new 0)) (touched (the (arrayof bool @cb) (make-array (+ nvars 1) #f)))
                        (squeue (new (the ints nil))) (stack (new (the elim-stack nil)))
                        (budget (new initial-budget)) (limit (new 0))
                        (proof proof) (proof-lines (new (the strings nil)))
                        (ok (new #t))))))
      (begin
        (letrec ((add (subr cb-eff ((listof ints acyclic)) unit)
                   (lambda (cs)
                     (if (null? cs) #u
                         (let ((n (normalize (car cs))))
                           (begin
                             (if (and (not (extract n taut)) (st-ok? st) (not (exists-unit? st (extract n c))))
                                 (el-add! st (remove-false st (extract n c)))
                                 #u)
                             (add (cdr cs))))))))
          (add clauses))
        (el-propagate! st)
        (subsume-all! st)
        (if (st-ok? st) (eliminate-all! st nvars) #u)
        (if (st-ok? st)
            (product (ok #t)
                     (clauses (append (letrec ((go (subr cb-eff (ints) (listof ints acyclic)) (lambda (l) (if (null? l) nil (cons (list (car l)) (go (cdr l)))))))
                                        (go (get (extract st units))))
                                      (letrec ((go (subr cb-eff (int (listof ints acyclic)) (listof ints acyclic))
                                                 (lambda (i acc) (if (< i 0) acc
                                                                     (let ((c (ec st i)))
                                                                       (go (- i 1) (if (live? c) (cons (ivec->list c 0 (array-length c)) acc) acc)))))))
                                        (go (- (get (extract st nclauses)) 1) nil))))
                     (stack (get (extract st stack)))
                     (proof (get (extract st proof-lines))))
            (product (ok #f) (clauses nil) (stack nil) (proof (get (extract st proof-lines)))))))))

"Whether a literal of c is a unit already."
(define* exists-unit? (subr cb-eff (elim-state ivec) bool)
  (lambda (st c) (letrec ((go (subr cb-eff (int) bool) (lambda (k) (and (< k (array-length c)) (or (array-ref (extract st vals) (array-ref c k)) (go (+ k 1)))))))
                   (go 0))))
"c without the negations of units (written to the proof if any)."
(define* remove-false (subr cb-eff (elim-state ivec) ivec)
  (lambda (st c)
    (letrec ((go (subr cb-eff (ivec int) ivec)
               (lambda (c k)
                 (cond ((= k (array-length c)) c)
                       ((array-ref (extract st vals) (lit-neg (array-ref c k)))
                        (let ((d (without c (array-ref c k)))) (begin (proof-line! st "" d) (go d k))))
                       (else (go c (+ k 1)))))))
      (go c 0))))

"model: by variable, satisfying the clauses `eliminate` gave; it is changed
into one of the clauses it was given. Of the clauses of an eliminated x,
either those with x or those with not-x are all true without it; x is set
to make the others true."
(define* extend-model! (subr cb-eff (elim-stack (arrayof bool @cb)) unit)
  (lambda (stack model)
    (let ((true? (lambda ((l int)) (if (lit-negative? l) (not (array-ref model (lit-var l))) (array-ref model (lit-var l))))))
      (letrec ((each (subr cb-eff (elim-stack) unit)
                 (lambda (es)
                   (if (null? es) #u
                       (let* ((x (extract (car es) x)) (v (lit-var x)))
                         (begin
                           (array-set! model v
                                       (letrec ((go (subr cb-eff (clause-list) bool)
                                                  (lambda (cs)
                                                    (and (pair? cs)
                                                         (let ((c (car cs)))
                                                           (or (and (ivec-member? x c)
                                                                    (not (letrec ((any (subr cb-eff (int) bool)
                                                                                         (lambda (k) (and (< k (array-length c))
                                                                                                          (or (and (not (= (array-ref c k) x)) (true? (array-ref c k)))
                                                                                                              (any (+ k 1)))))))
                                                                           (any 0))))
                                                               (go (cdr cs))))))))
                                         (go (extract (car es) clauses))))
                           (each (cdr es))))))))
        (each stack)))))

(define* ivec-member? (subr cb-eff (int ivec) bool)
  (lambda (x c) (letrec ((go (subr cb-eff (int) bool) (lambda (k) (and (< k (array-length c)) (or (= x (array-ref c k)) (go (+ k 1)))))))
                  (go 0))))
"The variables eliminated."
(define* eliminated-vars (subr spin (elim-stack) ints)
  (lambda (stack) (if (null? stack) nil (cons (lit-var (extract (car stack) x)) (eliminated-vars (cdr stack))))))
