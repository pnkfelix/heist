;;; sat.fx: a CDCL SAT solver, after MiniSat (Een and Sorensson, "An
;;; Extensible SAT-solver", 2003) and Glucose: lockpick's `(lockpick sat)`
;;; (../lockpick, src/lockpick/sat-core.scm at 2bae0a4), in FX-26.
;;;
;;; Variables are 1, 2, ...; the literal of variable v is 2v, its negation
;;; 2v+1 (negation flips the low bit). The solver is incremental: clauses
;;; may be added between solves, which may be given assumptions (literals
;;; taken as decisions for one solve). lockpick's DESIGN.md says why the
;;; solver is as it is; what differs here:
;;;   - A clause is an array `[header lit1 lit2 …]`, and is referred to by
;;;     its number in the solver's clause table (`cdb`), so that watches,
;;;     reasons and the clause lists are arrays of ints. A deleted clause's
;;;     number is used again once nothing refers to it.
;;;   - A proof (DRAT) is kept as lines, newest first, for the caller to
;;;     write out (`sat-proof-lines`).
;;;   - Statuses are ints: `sat-sat` 10, `sat-unsat` 20, `sat-unknown` 0,
;;;     as DIMACS solvers exit.
;;;
;;; State: what a solver is, in region @cb. No state of the module's own.

"What the solver, and the rest of combo, does: its own state at @cb, and
reading the clock for deadlines."
(define-effect cb-eff (maxeff spin (read @globals) (read @cb) (write @cb) (alloc @cb) (io clock)))

(define-type ints (listof int acyclic))
(define-type strings (listof string acyclic))
(define-type ivec (arrayof int @cb))

;;; ------------------------------------------------------------ literals

(define* make-lit (subr pure (int bool) int) (lambda (v negative?) (if negative? (+ (+ v v) 1) (+ v v))))
(define* lit-var (subr pure (int) int) (lambda (l) (arithmetic-shift l -1)))
(define* lit-neg (subr pure (int) int) (lambda (l) (bitwise-xor l 1)))
(define* lit-negative? (subr pure (int) bool) (lambda (l) (= 1 (bitwise-and l 1))))
"DIMACS integers (-3 is \"not x3\") to literals, and back."
(define* int->lit (subr pure (int) int) (lambda (n) (if (< n 0) (+ (* -2 n) 1) (* 2 n))))
(define* lit->int (subr pure (int) int) (lambda (l) (if (lit-negative? l) (- 0 (lit-var l)) (lit-var l))))

"A solve's answer."
(define sat-sat int 10)
(define sat-unsat int 20)
(define sat-unknown int 0)

;;; ------------------------------------------------------------ small things

"An array of `n` ints, `v`'s first and then `fill`."
(define* ivec-grow (subr cb-eff (ivec int int) ivec)
  (lambda (v n fill)
    (let ((w (the ivec (make-array n fill))) (m (array-length v)))
      (letrec ((go (subr cb-eff (int) ivec)
                 (lambda (i) (if (>= i m) w (begin (array-set! w i (array-ref v i)) (go (+ i 1)))))))
        (go 0)))))
(define* ivec-copy (subr cb-eff (ivec int) ivec)
  (lambda (v n) (ivec-grow (ivec-take v n) n 0)))
"The first `n` of `v`, as an array of its own."
(define* ivec-take (subr cb-eff (ivec int) ivec)
  (lambda (v n)
    (let ((w (the ivec (make-array n 0))))
      (letrec ((go (subr cb-eff (int) ivec)
                 (lambda (i) (if (>= i n) w (begin (array-set! w i (array-ref v i)) (go (+ i 1)))))))
        (go 0)))))
(define* ivec-fill! (subr cb-eff (ivec int int int) unit)
  (lambda (v from to x)
    (if (>= from to) #u (begin (array-set! v from x) (ivec-fill! v (+ from 1) to x)))))
(define* list->ivec (subr cb-eff (ints) ivec)
  (lambda (l)
    (let ((v (the ivec (make-array (list-length l) 0))))
      (letrec ((go (subr cb-eff (ints int) ivec)
                 (lambda (l i) (if (null? l) v (begin (array-set! v i (car l)) (go (cdr l) (+ i 1)))))))
        (go l 0)))))
"`v`'s elements from `from` to `to`, as a list."
(define* ivec->list (subr cb-eff (ivec int int) ints)
  (lambda (v from to)
    (letrec ((go (subr cb-eff (int ints) ints)
               (lambda (i acc) (if (< i from) acc (go (- i 1) (cons (array-ref v i) acc))))))
      (go (- to 1) nil))))
(define* reverse-ints (subr spin (ints) ints)
  (lambda (l) (letrec ((go (subr spin (ints ints) ints) (lambda (l acc) (if (null? l) acc (go (cdr l) (cons (car l) acc))))))
                (go l nil))))
(define* remv-once (subr spin (int ints) ints)
  (lambda (x l) (cond ((null? l) nil) ((= x (car l)) (cdr l)) (else (cons (car l) (remv-once x (cdr l)))))))
(define* ints-max (subr spin (int ints) int)
  (lambda (m l) (if (null? l) m (ints-max (max m (car l)) (cdr l)))))

(define-type bools (arrayof bool @cb))
(define-type ivecs (arrayof ivec @cb))
(define* grow-bools (subr cb-eff (bools int bool) bools)
  (lambda (v i fill)
    (if (< i (array-length v)) v
        (let ((w (the bools (make-array (* 2 (+ i 1)) fill))))
          (letrec ((go (subr cb-eff (int) bools) (lambda (k) (if (>= k (array-length v)) w (begin (array-set! w k (array-ref v k)) (go (+ k 1)))))))
            (go 0))))))
(define* grow-ivecs (subr cb-eff (ivecs int) ivecs)
  (lambda (v i)
    (if (< i (array-length v)) v
        (let ((w (the ivecs (make-array (* 2 (+ i 1)) (the ivec (make-array 0 0))))))
          (letrec ((go (subr cb-eff (int) ivecs) (lambda (k) (if (>= k (array-length v)) w (begin (array-set! w k (array-ref v k)) (go (+ k 1)))))))
            (go 0))))))
"`v` with room at i (as lockpick's `grow`)."
(define* grow-ivec (subr cb-eff (ivec int int) ivec)
  (lambda (v i fill) (if (< i (array-length v)) v (ivec-grow v (* 2 (+ i 1)) fill))))

"Sort `v`'s first `n` elements, stably (a merge sort, as R6RS's
`vector-sort!`), by `less?`."
(define* ivec-sort! (subr cb-eff (ivec int (subr cb-eff (int int) bool)) unit)
  (lambda (v n less?)
    (let ((tmp (the ivec (make-array n 0))))
      (letrec ((merge (subr cb-eff (int int int) unit)
                 ;; v[lo, mid) and v[mid, hi), each sorted, into tmp, then back.
                 (lambda (lo mid hi)
                   (letrec ((go (subr cb-eff (int int int) unit)
                              (lambda (i j k)
                                (cond ((>= k hi) #u)
                                      ((and (< i mid) (or (>= j hi) (not (less? (array-ref v j) (array-ref v i)))))
                                       (begin (array-set! tmp k (array-ref v i)) (go (+ i 1) j (+ k 1))))
                                      (else (begin (array-set! tmp k (array-ref v j)) (go i (+ j 1) (+ k 1)))))))
                            (back (subr cb-eff (int) unit)
                              (lambda (k) (if (>= k hi) #u (begin (array-set! v k (array-ref tmp k)) (back (+ k 1)))))))
                     (begin (go lo mid lo) (back lo)))))
               (sort (subr cb-eff (int int) unit)
                 (lambda (lo hi)
                   (if (< (- hi lo) 2) #u
                       (let ((mid (quotient (+ lo hi) 2)))
                         (begin (sort lo mid) (sort mid hi) (merge lo mid hi)))))))
        (sort 0 n)))))

;;; ------------------------------------------------------------ theories

"A theory's answer to a check (DPLL(T)): the assignment is consistent
with it; `t-conflict`, a clause it proves, false now; `t-continue`, it
made new variables to decide (branch and bound); `t-lemma`, a clause it
proves whose first literal is unassigned and the rest false (a cut);
`t-propagate`, clauses like that, whose first literals are to be
assigned; `t-unsat`, it proves the clauses unsatisfiable."
(define-datatype theory-answer
  (t-ok)
  (t-conflict ints)
  (t-continue)
  (t-lemma ints)
  (t-propagate (listof ints acyclic))
  (t-unsat))
"A theory: `check`, called when propagation is done (with #t when every
variable is assigned); `backtrack`, when the trail is cut to that many
literals. Each closes over the solver it is given to."
(define-type theory (productof (check (subr cb-eff (bool) theory-answer)) (backtrack (subr cb-eff (int) unit))))
(define no-theory theory
  (product (check (lambda ((final bool)) (t-ok))) (backtrack (lambda ((n int)) #u))))

;;; ------------------------------------------------------------ the solver

"The solver. Arrays by variable have cap+1 slots, those by literal
2(cap+1). A clause is `[header lit1 lit2 …]`, its header, from the low
bit: learnt?, deleted?, used since the last reduction?, then its LBD;
lit1 and lit2 are watched, and a clause that is a reason has the literal
it implied first. Watches: for each literal, pairs (blocker, clause) and
their number (times 2); a binary clause's blocker is minus its other
literal. Reasons are clause numbers, -1 for none."
(define-type sat-solver
  (productof
   (ok (ref bool @cb)) (nvars (ref int @cb)) (cap (ref int @cb))
   (vals (ref ivec @cb)) (levels (ref ivec @cb)) (reasons (ref ivec @cb))
   (activity (ref ivec @cb)) (polarity (ref ivec @cb)) (seen (ref ivec @cb))
   (heap-index (ref ivec @cb)) (heap (ref ivec @cb)) (heap-size (ref int @cb))
   (watches (ref (arrayof ivec @cb) @cb)) (wcount (ref ivec @cb))
   (trail (ref ivec @cb)) (trail-size (ref int @cb)) (trail-lim (ref ivec @cb))
   (nlevels (ref int @cb)) (qhead (ref int @cb))
   (cdb (ref (arrayof ivec @cb) @cb)) (cdb-top (ref int @cb)) (cdb-free (ref ints @cb)) (cdb-dead (ref ints @cb))
   (clauses (ref ivec @cb)) (nclauses (ref int @cb)) (learnts (ref ivec @cb)) (nlearnts (ref int @cb))
   (var-inc (ref int @cb)) (level-stamp (ref ivec @cb)) (stamp (ref int @cb))
   (conflicts (ref int @cb)) (decisions (ref int @cb)) (propagations (ref int @cb)) (restarts (ref int @cb))
   (next-reduce (ref int @cb)) (reduce-inc (ref int @cb)) (simp-trail-size (ref int @cb))
   (model (ref (arrayof bool @cb) @cb)) (final-conflict (ref ints @cb))
   (proof (ref bool @cb)) (proof-lines (ref strings @cb))
   (conflict-budget (ref int @cb)) (deadline (ref int @cb))
   (theory (ref theory @cb)) (has-theory (ref bool @cb))
   (tpos (ref ivec @cb)) (lmin (ref ivec @cb)) (lcount (ref ivec @cb))
   (aout (ref ints @cb)) (toclear (ref ints @cb))
   (glue-fast (ref int @cb)) (glue-sum (ref int @cb)) (glue-count (ref int @cb)) (trail-slow (ref int @cb))))

(define T int 1)
(define F int -1)
(define U int 0)

(define* new-ivec (subr (alloc @cb) (int int) (ref ivec @cb)) (lambda (n x) (new (the ivec (make-array n x)))))
(define* new-int (subr (alloc @cb) (int) (ref int @cb)) (lambda (n) (new n)))
(define* empty-watches (subr cb-eff (int) (arrayof ivec @cb))
  (lambda (n)
    (let ((w (the (arrayof ivec @cb) (make-array n (the ivec (make-array 0 0))))))
      (letrec ((go (subr cb-eff (int) (arrayof ivec @cb))
                 (lambda (i) (if (>= i n) w (begin (array-set! w i (the ivec (make-array 4 0))) (go (+ i 1)))))))
        (go 0)))))

(define* make-solver (subr cb-eff () sat-solver)
  (lambda ()
    (let* ((cap 16) (nv (+ cap 1)) (nl (* 2 nv)))
      (product (ok (new #t)) (nvars (new-int 0)) (cap (new-int cap))
               (vals (new-ivec nl U)) (levels (new-ivec nv 0)) (reasons (new-ivec nv -1))
               (activity (new-ivec nv 0)) (polarity (new-ivec nv 1)) (seen (new-ivec nv 0))
               (heap-index (new-ivec nv -1)) (heap (new-ivec nv 0)) (heap-size (new-int 0))
               (watches (new (empty-watches nl))) (wcount (new-ivec nl 0))
               (trail (new-ivec nv 0)) (trail-size (new-int 0)) (trail-lim (new-ivec nv 0))
               (nlevels (new-int 0)) (qhead (new-int 0))
               (cdb (new (the (arrayof ivec @cb) (make-array 64 (the ivec (make-array 0 0))))))
               (cdb-top (new-int 0)) (cdb-free (new (the ints nil))) (cdb-dead (new (the ints nil)))
               (clauses (new-ivec 64 0)) (nclauses (new-int 0)) (learnts (new-ivec 64 0)) (nlearnts (new-int 0))
               (var-inc (new-int 128)) (level-stamp (new-ivec nv 0)) (stamp (new-int 0))
               (conflicts (new-int 0)) (decisions (new-int 0)) (propagations (new-int 0)) (restarts (new-int 0))
               (next-reduce (new-int 2000)) (reduce-inc (new-int 300)) (simp-trail-size (new-int 0))
               (model (new (the (arrayof bool @cb) (make-array 0 #f)))) (final-conflict (new (the ints nil)))
               (proof (new #f)) (proof-lines (new (the strings nil)))
               (conflict-budget (new-int -1)) (deadline (new-int -1))
               (theory (new no-theory)) (has-theory (new #f))
               (tpos (new-ivec nv 0)) (lmin (new-ivec nv 0)) (lcount (new-ivec nv 0))
               (aout (new (the ints nil))) (toclear (new (the ints nil)))
               (glue-fast (new-int 0)) (glue-sum (new-int 0)) (glue-count (new-int 0)) (trail-slow (new-int 0))))))

;; The arrays read most, by name.
(define* s-vals (subr (read @cb) (sat-solver) ivec) (lambda (s) (get (extract s vals))))
(define* s-levels (subr (read @cb) (sat-solver) ivec) (lambda (s) (get (extract s levels))))
(define* s-reasons (subr (read @cb) (sat-solver) ivec) (lambda (s) (get (extract s reasons))))
(define* s-trail (subr (read @cb) (sat-solver) ivec) (lambda (s) (get (extract s trail))))
(define* s-seen (subr (read @cb) (sat-solver) ivec) (lambda (s) (get (extract s seen))))
(define* s-watches (subr (read @cb) (sat-solver) (arrayof ivec @cb)) (lambda (s) (get (extract s watches))))
(define* s-wcount (subr (read @cb) (sat-solver) ivec) (lambda (s) (get (extract s wcount))))
(define* s-nlevels (subr (read @cb) (sat-solver) int) (lambda (s) (get (extract s nlevels))))
(define* s-trail-size (subr (read @cb) (sat-solver) int) (lambda (s) (get (extract s trail-size))))
"Clause number `c`."
(define* cl (subr (read @cb) (sat-solver int) ivec) (lambda (s c) (array-ref (get (extract s cdb)) c)))
(define* level-of (subr (read @cb) (sat-solver int) int) (lambda (s l) (array-ref (s-levels s) (lit-var l))))
(define* incr! (subr (maxeff (read @cb) (write @cb)) ((ref int @cb) int) unit) (lambda (r n) (set r (+ (get r) n))))

(define* sat-ok? (subr (read @cb) (sat-solver) bool) (lambda (s) (get (extract s ok))))
(define* sat-nvars (subr (read @cb) (sat-solver) int) (lambda (s) (get (extract s nvars))))

(define* ensure-capacity! (subr cb-eff (sat-solver int) unit)
  (lambda (s nvars)
    (if (<= nvars (get (extract s cap))) #u
        (let* ((cap (letrec ((go (subr spin (int) int) (lambda (c) (if (< c nvars) (go (* 2 c)) c))))
                      (go (* 2 (get (extract s cap))))))
               (nv (+ cap 1)) (nl (* 2 nv))
               (grow! (lambda ((r (ref ivec @cb)) (n int) (fill int)) (set r (ivec-grow (get r) n fill))))
               (old-nl (array-length (s-vals s))))
          (begin
            (grow! (extract s vals) nl U) (grow! (extract s levels) nv 0) (grow! (extract s reasons) nv -1)
            (grow! (extract s activity) nv 0) (grow! (extract s polarity) nv 1) (grow! (extract s seen) nv 0)
            (grow! (extract s tpos) nv 0) (grow! (extract s lmin) nv 0) (grow! (extract s lcount) nv 0)
            (grow! (extract s heap-index) nv -1) (grow! (extract s heap) nv 0)
            (let ((w (the (arrayof ivec @cb) (make-array nl (the ivec (make-array 0 0))))) (old (s-watches s)))
              (letrec ((go (subr cb-eff (int) unit)
                         (lambda (i) (if (>= i nl) #u
                                         (begin (array-set! w i (if (< i old-nl) (array-ref old i) (the ivec (make-array 4 0))))
                                                (go (+ i 1)))))))
                (begin (go 0) (set (extract s watches) w))))
            (grow! (extract s wcount) nl 0)
            (grow! (extract s trail) nv 0) (grow! (extract s trail-lim) nv 0) (grow! (extract s level-stamp) nv 0)
            (set (extract s cap) cap))))))

;;; ------------------------------------------------------------ the order heap
;;; Variables by activity, greatest first.

(define* heap-up! (subr cb-eff (sat-solver int) unit)
  (lambda (s i)
    (let* ((heap (get (extract s heap))) (index (get (extract s heap-index))) (act (get (extract s activity)))
           (v (array-ref heap i)))
      (letrec ((go (subr cb-eff (int) unit)
                 (lambda (i)
                   (let ((parent (arithmetic-shift (- i 1) -1)))
                     (if (and (> i 0) (> (array-ref act v) (array-ref act (array-ref heap parent))))
                         (let ((pv (array-ref heap parent)))
                           (begin (array-set! heap i pv) (array-set! index pv i) (go parent)))
                         (begin (array-set! heap i v) (array-set! index v i)))))))
        (go i)))))

(define* heap-down! (subr cb-eff (sat-solver int) unit)
  (lambda (s i)
    (let* ((heap (get (extract s heap))) (index (get (extract s heap-index))) (act (get (extract s activity)))
           (n (get (extract s heap-size))) (v (array-ref heap i)))
      (letrec ((go (subr cb-eff (int) unit)
                 (lambda (i)
                   (let ((left (+ (* 2 i) 1)))
                     (if (< left n)
                         (let* ((right (+ left 1))
                                (child (if (and (< right n) (> (array-ref act (array-ref heap right)) (array-ref act (array-ref heap left))))
                                           right left))
                                (cv (array-ref heap child)))
                           (if (> (array-ref act cv) (array-ref act v))
                               (begin (array-set! heap i cv) (array-set! index cv i) (go child))
                               (begin (array-set! heap i v) (array-set! index v i))))
                         (begin (array-set! heap i v) (array-set! index v i)))))))
        (go i)))))

(define* heap-insert! (subr cb-eff (sat-solver int) unit)
  (lambda (s v)
    (if (>= (array-ref (get (extract s heap-index)) v) 0) #u
        (let ((n (get (extract s heap-size))))
          (begin (array-set! (get (extract s heap)) n v)
                 (array-set! (get (extract s heap-index)) v n)
                 (set (extract s heap-size) (+ n 1))
                 (heap-up! s n))))))

"Remove and return the greatest variable (the heap is not empty)."
(define* heap-pop! (subr cb-eff (sat-solver) int)
  (lambda (s)
    (let* ((heap (get (extract s heap))) (v (array-ref heap 0)) (n (- (get (extract s heap-size)) 1)))
      (begin (array-set! (get (extract s heap-index)) v -1)
             (set (extract s heap-size) n)
             (if (> n 0) (begin (array-set! heap 0 (array-ref heap n)) (heap-down! s 0)) #u)
             v))))

(define* heap-remove! (subr cb-eff (sat-solver int) unit)
  (lambda (s v)
    (let ((i (array-ref (get (extract s heap-index)) v)))
      (if (< i 0) #u
          (let* ((heap (get (extract s heap))) (n (- (get (extract s heap-size)) 1)) (last (array-ref heap n)))
            (begin (array-set! (get (extract s heap-index)) v -1)
                   (set (extract s heap-size) n)
                   (if (< i n)
                       (begin (array-set! heap i last)
                              (array-set! (get (extract s heap-index)) last i)
                              (heap-down! s i)
                              (heap-up! s (array-ref (get (extract s heap-index)) last)))
                       #u)))))))

"A new variable, which is returned."
(define* sat-new-var! (subr cb-eff (sat-solver) int)
  (lambda (s)
    (let ((v (+ (sat-nvars s) 1)))
      (begin (ensure-capacity! s v) (set (extract s nvars) v) (heap-insert! s v) v))))
(define* ensure-vars! (subr cb-eff (sat-solver int) unit)
  (lambda (s n) (if (< (sat-nvars s) n) (begin (sat-new-var! s) (ensure-vars! s n)) #u)))

;;; ------------------------------------------------------------ activity (VSIDS)
;;; Activities are ints: the increment grows by 1/19 a conflict (a decay of
;;; 0.95), and all are scaled down when one passes 2^52.

(define activity-limit int 4503599627370496)

(define* rescale-activity! (subr cb-eff (sat-solver) unit)
  (lambda (s)
    (let ((act (get (extract s activity))) (n (sat-nvars s)))
      (letrec ((go (subr cb-eff (int) unit)
                 (lambda (v) (if (> v n) #u (begin (array-set! act v (arithmetic-shift (array-ref act v) -32)) (go (+ v 1)))))))
        (begin (go 1) (set (extract s var-inc) (max 128 (arithmetic-shift (get (extract s var-inc)) -32))))))))

(define* bump-var! (subr cb-eff (sat-solver int) unit)
  (lambda (s v)
    (let* ((act (get (extract s activity))) (a (+ (array-ref act v) (get (extract s var-inc)))))
      (begin (array-set! act v a)
             (if (> a activity-limit) (rescale-activity! s) #u)
             (let ((i (array-ref (get (extract s heap-index)) v)))
               (if (>= i 0) (heap-up! s i) #u))))))

(define* decay-var-activity! (subr cb-eff (sat-solver) unit)
  (lambda (s) (let ((inc (get (extract s var-inc)))) (set (extract s var-inc) (+ inc (quotient inc 19))))))

;;; ------------------------------------------------------------ watches

(define* watch-push! (subr cb-eff (sat-solver int int int) unit)
  (lambda (s l blocker c)
    (let* ((watches (s-watches s)) (wcount (s-wcount s)) (n (array-ref wcount l))
           (ws (let ((ws (array-ref watches l)))
                 (if (< (+ n 1) (array-length ws)) ws
                     (let ((w (ivec-grow ws (* 2 (array-length ws)) 0))) (begin (array-set! watches l w) w))))))
      (begin (array-set! ws n blocker) (array-set! ws (+ n 1) c) (array-set! wcount l (+ n 2))))))

(define* attach-clause! (subr cb-eff (sat-solver int) unit)
  (lambda (s c)
    (let* ((k (cl s c)) (l1 (array-ref k 1)) (l2 (array-ref k 2)))
      (if (= 3 (array-length k))
          (begin (watch-push! s l1 (- 0 l2) c) (watch-push! s l2 (- 0 l1) c))
          (begin (watch-push! s l1 l2 c) (watch-push! s l2 l1 c))))))

(define* clause-learnt? (subr (read @cb) (sat-solver int) bool) (lambda (s c) (= 1 (bitwise-and (array-ref (cl s c) 0) 1))))
(define* clause-deleted? (subr (read @cb) (sat-solver int) bool) (lambda (s c) (not (= 0 (bitwise-and (array-ref (cl s c) 0) 2)))))
(define* clause-used? (subr (read @cb) (sat-solver int) bool) (lambda (s c) (not (= 0 (bitwise-and (array-ref (cl s c) 0) 4)))))
(define* clause-lbd (subr (read @cb) (sat-solver int) int) (lambda (s c) (arithmetic-shift (array-ref (cl s c) 0) -3)))
(define* clause-set-used! (subr (maxeff (read @cb) (write @cb)) (sat-solver int bool) unit)
  (lambda (s c used?)
    (let ((k (cl s c))) (array-set! k 0 (if used? (bitwise-ior (array-ref k 0) 4) (bitwise-and (array-ref k 0) (bitwise-not 4)))))))
(define* clause-set-lbd! (subr (maxeff (read @cb) (write @cb)) (sat-solver int int) unit)
  (lambda (s c lbd) (let ((k (cl s c))) (array-set! k 0 (+ (* lbd 8) (bitwise-and (array-ref k 0) 7))))))
(define* clause-lits (subr cb-eff (sat-solver int) ints)
  (lambda (s c) (let ((k (cl s c))) (ivec->list k 1 (array-length k)))))

"Remove the deleted clauses from every watch list; their numbers are then
free to be used again."
(define* sweep-watches! (subr cb-eff (sat-solver) unit)
  (lambda (s)
    (let ((watches (s-watches s)) (wcount (s-wcount s)) (top (* 2 (+ (sat-nvars s) 1))))
      (letrec ((each (subr cb-eff (int) unit)
                 (lambda (l)
                   (if (>= l top) #u
                       (let ((ws (array-ref watches l)) (n (array-ref wcount l)))
                         (letrec ((go (subr cb-eff (int int) unit)
                                    (lambda (i j)
                                      (if (< i n)
                                          (let ((c (array-ref ws (+ i 1))))
                                            (if (clause-deleted? s c) (go (+ i 2) j)
                                                (begin (array-set! ws j (array-ref ws i)) (array-set! ws (+ j 1) c)
                                                       (go (+ i 2) (+ j 2)))))
                                          (array-set! wcount l j)))))
                           (begin (go 0 0) (each (+ l 1)))))))))
        (begin
          (each 2)
          ;; Nothing refers to the deleted clauses now.
          (let ((cdb (get (extract s cdb))) (empty (the ivec (make-array 0 0))))
            (letrec ((free (subr cb-eff (ints) unit)
                       (lambda (l) (if (null? l) #u
                                       (begin (array-set! cdb (car l) empty)
                                              (set (extract s cdb-free) (cons (car l) (get (extract s cdb-free))))
                                              (free (cdr l)))))))
              (begin (free (get (extract s cdb-dead))) (set (extract s cdb-dead) nil)))))))))

;;; ------------------------------------------------------------ clauses

"A new clause of these literals, learnt or not, of this LBD: its number."
(define* make-clause (subr cb-eff (sat-solver ints bool int) int)
  (lambda (s lits learnt? lbd)
    (let ((k (the ivec (make-array (+ (list-length lits) 1) 0))))
      (begin
        (array-set! k 0 (+ (* lbd 8) (if learnt? 1 0)))
        (letrec ((go (subr cb-eff (ints int) unit)
                   (lambda (l i) (if (null? l) #u (begin (array-set! k i (car l)) (go (cdr l) (+ i 1)))))))
          (go lits 1))
        (store-clause! s k)))))
(define* store-clause! (subr cb-eff (sat-solver ivec) int)
  (lambda (s k)
    (let ((free (get (extract s cdb-free))))
      (if (pair? free)
          (begin (set (extract s cdb-free) (cdr free)) (array-set! (get (extract s cdb)) (car free) k) (car free))
          (let* ((n (get (extract s cdb-top))) (cdb (get (extract s cdb)))
                 (cdb (if (< n (array-length cdb)) cdb
                          (let ((w (the (arrayof ivec @cb) (make-array (* 2 (array-length cdb)) (the ivec (make-array 0 0))))))
                            (letrec ((go (subr cb-eff (int) unit)
                                       (lambda (i) (if (>= i n) #u (begin (array-set! w i (array-ref cdb i)) (go (+ i 1)))))))
                              (begin (go 0) (set (extract s cdb) w) w))))))
            (begin (array-set! cdb n k) (set (extract s cdb-top) (+ n 1)) n))))))

;;; ------------------------------------------------------------ the trail

(define* assign! (subr cb-eff (sat-solver int int) unit)
  (lambda (s l reason)
    (let ((vals (s-vals s)) (v (lit-var l)) (n (s-trail-size s)))
      (begin (array-set! vals l T)
             (array-set! vals (lit-neg l) F)
             (array-set! (s-levels s) v (s-nlevels s))
             (array-set! (s-reasons s) v reason)
             (array-set! (get (extract s tpos)) v n)
             (array-set! (s-trail s) n l)
             (set (extract s trail-size) (+ n 1))))))

(define* new-level! (subr cb-eff (sat-solver) unit)
  (lambda (s)
    (let ((k (s-nlevels s)))
      (begin (array-set! (get (extract s trail-lim)) k (s-trail-size s)) (set (extract s nlevels) (+ k 1))))))

"Undo the assignments above `level`, saving their phases."
(define* cancel-until! (subr cb-eff (sat-solver int) unit)
  (lambda (s level)
    (if (<= (s-nlevels s) level) #u
        (let ((lim (array-ref (get (extract s trail-lim)) level))
              (trail (s-trail s)) (vals (s-vals s)) (reasons (s-reasons s)) (pol (get (extract s polarity))))
          (letrec ((go (subr cb-eff (int) unit)
                     (lambda (i)
                       (if (< i lim) #u
                           (let* ((l (array-ref trail i)) (v (lit-var l)))
                             (begin (array-set! vals l U) (array-set! vals (lit-neg l) U)
                                    (array-set! reasons v -1)
                                    (array-set! pol v (bitwise-and l 1))
                                    (heap-insert! s v)
                                    (go (- i 1))))))))
            (begin (go (- (s-trail-size s) 1))
                   (set (extract s trail-size) lim)
                   (set (extract s qhead) lim)
                   (set (extract s nlevels) level)
                   (if (get (extract s has-theory)) ((extract (get (extract s theory)) backtrack) lim) #u)))))))

;;; ------------------------------------------------------------ propagation
;;; Two watched literals, with blockers. Returns a conflicting clause, or -1.

"The position of a literal of clause `k`, from 3, that is not false, or 0."
(define* unfalse-pos (subr cb-eff (ivec ivec) int)
  (lambda (vals k)
    (let ((end (array-length k)))
      (letrec ((go (subr cb-eff (int) int)
                 (lambda (p) (cond ((= p end) 0) ((= (array-ref vals (array-ref k p)) F) (go (+ p 1))) (else p)))))
        (go 3)))))

"`l` is implied by clause `c`, at trail position `tsize`."
(define* imply! (subr cb-eff (sat-solver int int int) unit)
  (lambda (s l c tsize)
    (let ((v (lit-var l)) (vals (s-vals s)))
      (begin (array-set! vals l T)
             (array-set! vals (lit-neg l) F)
             (array-set! (s-levels s) v (s-nlevels s))
             (array-set! (s-reasons s) v c)
             (array-set! (get (extract s tpos)) v tsize)
             (array-set! (s-trail s) tsize l)))))

"At a conflict found in the watches of `fl` at i (its watch kept at j):
keep the rest of them."
(define* propagate-conflict! (subr cb-eff (sat-solver int int int) unit)
  (lambda (s fl i j)
    (let* ((ws (array-ref (s-watches s) fl)) (n (array-ref (s-wcount s) fl)))
      (letrec ((go (subr cb-eff (int int) unit)
                 (lambda (i j)
                   (if (< i n)
                       (begin (array-set! ws j (array-ref ws i)) (array-set! ws (+ j 1) (array-ref ws (+ i 1))) (go (+ i 2) (+ j 2)))
                       (array-set! (s-wcount s) fl j)))))
        (go i j)))))

(define* propagate-done! (subr cb-eff (sat-solver int int int int) int)
  (lambda (s qhead tsize nprops confl)
    (begin (set (extract s qhead) qhead)
           (set (extract s trail-size) tsize)
           (incr! (extract s propagations) nprops)
           confl)))

(define* propagate! (subr cb-eff (sat-solver) int)
  (lambda (s)
    (let ((q0 (get (extract s qhead))) (trail (s-trail s)) (vals (s-vals s))
          (watches (s-watches s)) (wcount (s-wcount s)) (cdb (get (extract s cdb))))
      (letrec ((go (subr cb-eff (int int int int) int)
                 (lambda (qhead tsize i j)
                   (if (>= qhead tsize)
                       (propagate-done! s qhead tsize (- qhead q0) -1)
                       (let* ((fl (lit-neg (array-ref trail qhead)))
                              (ws (array-ref watches fl))
                              (n (array-ref wcount fl)))
                         (if (= i n)
                             (begin (array-set! wcount fl j) (go (+ qhead 1) tsize 0 0))
                             (let ((blocker (array-ref ws i)) (c (array-ref ws (+ i 1))))
                               (cond
                                ((< blocker 0)
                                 ;; A binary clause of fl and other: fl goes to slot 2
                                 ;; when it is a reason or the conflict.
                                 (let* ((other (- 0 blocker)) (val (array-ref vals other)))
                                   (begin
                                     (array-set! ws j blocker) (array-set! ws (+ j 1) c)
                                     (if (= val T) (go qhead tsize (+ i 2) (+ j 2))
                                         (let ((k (array-ref cdb c)))
                                           (begin
                                             (if (= (array-ref k 1) fl) (begin (array-set! k 1 other) (array-set! k 2 fl)) #u)
                                             (if (= val F)
                                                 (begin (propagate-conflict! s fl (+ i 2) (+ j 2))
                                                        (propagate-done! s tsize tsize (+ 1 (- qhead q0)) c))
                                                 (begin (imply! s other c tsize) (go qhead (+ tsize 1) (+ i 2) (+ j 2))))))))))
                                ((= (array-ref vals blocker) T)
                                 (begin (array-set! ws j blocker) (array-set! ws (+ j 1) c) (go qhead tsize (+ i 2) (+ j 2))))
                                (else
                                 (let ((k (array-ref cdb c)))
                                   (begin
                                     ;; Make fl the second literal.
                                     (if (= (array-ref k 1) fl) (begin (array-set! k 1 (array-ref k 2)) (array-set! k 2 fl)) #u)
                                     (let ((first (array-ref k 1)))
                                       (if (and (not (= first blocker)) (= (array-ref vals first) T))
                                           (begin (array-set! ws j first) (array-set! ws (+ j 1) c) (go qhead tsize (+ i 2) (+ j 2)))
                                           ;; Look for a new literal to watch.
                                           (let ((p (unfalse-pos vals k)))
                                             (if (> p 0)
                                                 (let ((l (array-ref k p)))
                                                   (begin (array-set! k 2 l) (array-set! k p fl)
                                                          (watch-push! s l first c)
                                                          (go qhead tsize (+ i 2) j)))
                                                 ;; The clause is unit or conflicting.
                                                 (begin
                                                   (array-set! ws j first) (array-set! ws (+ j 1) c)
                                                   (if (= (array-ref vals first) F)
                                                       (begin (propagate-conflict! s fl (+ i 2) (+ j 2))
                                                              (propagate-done! s tsize tsize (+ 1 (- qhead q0)) c))
                                                       (begin (imply! s first c tsize) (go qhead (+ tsize 1) (+ i 2) (+ j 2))))))))))))))))))))
        (go q0 (s-trail-size s) 0 0)))))

;;; ------------------------------------------------------------ conflict analysis
;;; First UIP, with recursive minimization.

"The number of distinct levels among `lits`."
(define* compute-lbd (subr cb-eff (sat-solver ints) int)
  (lambda (s lits)
    (let ((stamp (+ (get (extract s stamp)) 1)) (ls (get (extract s level-stamp))) (levels (s-levels s)))
      (begin
        (set (extract s stamp) stamp)
        (letrec ((go (subr cb-eff (ints int) int)
                   (lambda (l n)
                     (if (null? l) n
                         (let ((lv (array-ref levels (lit-var (car l)))))
                           (if (= (array-ref ls lv) stamp) (go (cdr l) n)
                               (begin (array-set! ls lv stamp) (go (cdr l) (+ n 1)))))))))
          (go lits 0))))))

"A learnt clause took part in a conflict."
(define* touch-clause! (subr cb-eff (sat-solver int) unit)
  (lambda (s c)
    (begin (clause-set-used! s c #t)
           (if (> (clause-lbd s c) 2)
               (let ((lbd (compute-lbd s (clause-lits s c))))
                 (if (< lbd (clause-lbd s c)) (clause-set-lbd! s c lbd) #u))
               #u))))

"The learnt clause of a conflict, as a list whose first literal is the
asserting one and whose second (if any) has the greatest level of the
rest."
(define* analyze (subr cb-eff (sat-solver int) ints)
  (lambda (s confl)
    (begin (set (extract s aout) nil)
           (if (clause-learnt? s confl) (touch-clause! s confl) #u)
           (analyze-scan s confl 1 0 (- (s-trail-size s) 1)))))

"Mark the literals of clause `c` from position `k`: those of the conflict
level are counted in `pathc`, the others go to the learnt clause. `index`:
where to go on looking down the trail."
(define analyze-scan (subr cb-eff (sat-solver int int int int) ints)
  (lambda (s c k pathc index)
    (let ((cls (cl s c)))
      (if (< k (array-length cls))
          (let* ((q (array-ref cls k)) (v (lit-var q)) (seen (s-seen s)) (levels (s-levels s)))
            (if (and (= 0 (array-ref seen v)) (> (array-ref levels v) 0))
                (begin
                  (array-set! seen v 1)
                  (bump-var! s v)
                  (if (>= (array-ref levels v) (s-nlevels s))
                      (analyze-scan s c (+ k 1) (+ pathc 1) index)
                      (begin (set (extract s aout) (cons q (get (extract s aout))))
                             (analyze-scan s c (+ k 1) pathc index))))
                (analyze-scan s c (+ k 1) pathc index)))
          (analyze-next s pathc index)))))

"The next marked literal down the trail: the first UIP if it is the last
of its level, else resolve with its reason."
(define analyze-next (subr cb-eff (sat-solver int int) ints)
  (lambda (s pathc index)
    (let* ((p (array-ref (s-trail s) index)) (v (lit-var p)))
      (if (= 0 (array-ref (s-seen s) v))
          (analyze-next s pathc (- index 1))
          (begin
            (array-set! (s-seen s) v 0)
            (if (= pathc 1)
                (minimize s (lit-neg p) (get (extract s aout)))
                (let ((c (array-ref (s-reasons s) v)))
                  (begin (if (clause-learnt? s c) (touch-clause! s c) #u)
                         (analyze-scan s c 2 (- pathc 1) (- index 1))))))))))

"Mark `p` (if it is not marked) and remember to clear it."
(define* mark-seen! (subr cb-eff (sat-solver int int) unit)
  (lambda (s p mark)
    (let ((seen (s-seen s)))
      (if (= 0 (array-ref seen (lit-var p)))
          (begin (array-set! seen (lit-var p) mark) (set (extract s toclear) (cons p (get (extract s toclear)))))
          #u))))

(define-type frame (productof (lit int) (pos int)))
(define-type frames (listof frame acyclic))
"Whether `p` is implied by literals of the clause (MiniSat's
litRedundant), by a depth-first search through the reasons. Seen marks:
1 in the clause, 2 shown not implied, 3 shown implied; 2 and 3 are kept
for the rest of the clause. As in CaDiCaL, it gives up at once on a
literal of a level with no literal of the clause, or earlier on the trail
than all of those."
(define* redundant? (subr cb-eff (sat-solver int) bool)
  (lambda (s p)
    (let ((reasons (s-reasons s)) (seen (s-seen s)) (levels (s-levels s))
          (lcount (get (extract s lcount))) (lmin (get (extract s lmin))) (tpos (get (extract s tpos))))
      (letrec ((go (subr cb-eff (int int frames) bool)
                 (lambda (p k stack)
                   (let ((c (cl s (array-ref reasons (lit-var p)))))
                     (if (< k (array-length c))
                         (let* ((l (array-ref c k)) (v (lit-var l)) (mark (array-ref seen v)))
                           (cond ((or (= mark 1) (= mark 3) (= 0 (array-ref levels v))) (go p (+ k 1) stack))
                                 ((or (= mark 2) (< (array-ref reasons v) 0)
                                      (let ((level (array-ref levels v)))
                                        (or (= 0 (array-ref lcount level)) (< (array-ref tpos v) (array-ref lmin level)))))
                                  ;; Nothing on the path to l is implied.
                                  (begin (mark-seen! s p 2)
                                         (letrec ((unwind (subr cb-eff (frames) unit)
                                                    (lambda (st) (if (null? st) #u (begin (mark-seen! s (extract (car st) lit) 2) (unwind (cdr st)))))))
                                           (unwind stack))
                                         #f))
                                 (else (go l 2 (cons (product (lit p) (pos (+ k 1))) stack)))))
                         (begin (mark-seen! s p 3)
                                (if (null? stack) #t
                                    (go (extract (car stack) lit) (extract (car stack) pos) (cdr stack)))))))))
        (go p 2 nil)))))

"Remove from the learnt clause (uip . rest) the literals implied by the
others, and order it for watching. The literals of rest are marked seen;
they are unmarked here."
(define* minimize (subr cb-eff (sat-solver int ints) ints)
  (lambda (s uip rest)
    (let ((levels (s-levels s)) (tpos (get (extract s tpos))) (lmin (get (extract s lmin)))
          (lcount (get (extract s lcount))) (seen (s-seen s)) (reasons (s-reasons s)))
      (begin
        (set (extract s toclear) rest)
        ;; The levels of the clause's literals, for redundant?.
        (letrec ((count (subr cb-eff (ints) unit)
                   (lambda (l)
                     (if (null? l) #u
                         (let* ((v (lit-var (car l))) (level (array-ref levels v)) (n (array-ref lcount level)))
                           (begin (array-set! lcount level (+ n 1))
                                  (if (or (= n 0) (< (array-ref tpos v) (array-ref lmin level))) (array-set! lmin level (array-ref tpos v)) #u)
                                  (count (cdr l))))))))
          (count rest))
        (let ((kept (letrec ((go (subr cb-eff (ints ints) ints)
                               (lambda (l acc)
                                 (cond ((null? l) acc)
                                       ((and (>= (array-ref reasons (lit-var (car l))) 0)
                                             ;; The only literal of its level is needed.
                                             (> (array-ref lcount (array-ref levels (lit-var (car l)))) 1)
                                             (redundant? s (car l)))
                                        (go (cdr l) acc))
                                       (else (go (cdr l) (cons (car l) acc)))))))
                      (go rest nil))))
          (begin
            (letrec ((clear (subr cb-eff (ints) unit)
                       (lambda (l) (if (null? l) #u (begin (array-set! seen (lit-var (car l)) 0) (clear (cdr l)))))))
              (clear (get (extract s toclear))))
            (set (extract s toclear) nil)
            (letrec ((uncount (subr cb-eff (ints) unit)
                       (lambda (l) (if (null? l) #u (begin (array-set! lcount (array-ref levels (lit-var (car l))) 0) (uncount (cdr l)))))))
              (uncount rest))
            ;; The literal of the greatest level second.
            (if (null? kept) (list uip)
                (let ((best (letrec ((go (subr cb-eff (ints int) int)
                                       (lambda (l best)
                                         (cond ((null? l) best)
                                               ((> (array-ref levels (lit-var (car l))) (array-ref levels (lit-var best))) (go (cdr l) (car l)))
                                               (else (go (cdr l) best))))))
                              (go (cdr kept) (car kept)))))
                  (cons uip (cons best (remv-once best kept)))))))))))

"The assumptions that, with the clauses, make `p` false: `p` is an
assumption found false (MiniSat's analyzeFinal)."
(define* analyze-final (subr cb-eff (sat-solver int) ints)
  (lambda (s p)
    (let ((seen (s-seen s)) (levels (s-levels s)) (reasons (s-reasons s)) (trail (s-trail s)))
      (if (= 0 (s-nlevels s)) (list p)
          (begin
            (array-set! seen (lit-var p) 1)
            (let ((lim0 (array-ref (get (extract s trail-lim)) 0)))
              (letrec ((go (subr cb-eff (int ints) ints)
                         (lambda (i out)
                           (if (< i lim0)
                               (begin (array-set! seen (lit-var p) 0) out)
                               (let* ((l (array-ref trail i)) (v (lit-var l)))
                                 (if (= 0 (array-ref seen v)) (go (- i 1) out)
                                     (let ((c (array-ref reasons v)))
                                       (begin
                                         (array-set! seen v 0)
                                         (if (>= c 0)
                                             (let ((k (cl s c)))
                                               (letrec ((mark (subr cb-eff (int) unit)
                                                          (lambda (j) (if (>= j (array-length k)) #u
                                                                          (let ((u (lit-var (array-ref k j))))
                                                                            (begin (if (> (array-ref levels u) 0) (array-set! seen u 1) #u)
                                                                                   (mark (+ j 1))))))))
                                                 (begin (mark 2) (go (- i 1) out))))
                                             (go (- i 1) (cons l out)))))))))))
                (go (- (s-trail-size s) 1) (list p)))))))))

;;; ------------------------------------------------------------ proofs (DRAT, as lines)

(define* proof-write! (subr cb-eff (sat-solver string ints) unit)
  (lambda (s prefix lits)
    (if (not (get (extract s proof))) #u
        (letrec ((go (subr cb-eff (ints (listof string acyclic)) (listof string acyclic))
                   (lambda (l acc) (if (null? l) acc (go (cdr l) (cons " " (cons (int->string (lit->int (car l))) acc)))))))
          (set (extract s proof-lines)
               (cons (string-concat (reverse-strings (cons "0\n" (go lits (list prefix))))) (get (extract s proof-lines))))))))
(define* reverse-strings (subr spin (strings) strings)
  (lambda (l) (letrec ((go (subr spin (strings strings) strings) (lambda (l acc) (if (null? l) acc (go (cdr l) (cons (car l) acc))))))
                (go l nil))))
"The strings of `l`, joined."
(define* string-concat (subr spin (strings) string)
  (lambda (l) (list->string (letrec ((chars (subr spin (strings) (listof char acyclic))
                                        (lambda (l) (if (null? l) nil (append (string->list (car l)) (chars (cdr l)))))))
                               (chars l)))))

;;; ------------------------------------------------------------ the clause database

(define* push-clause! (subr cb-eff (sat-solver int) unit)
  (lambda (s c)
    (let ((push! (lambda ((v (ref ivec @cb)) (n (ref int @cb)))
                   (begin (if (= (get n) (array-length (get v))) (set v (ivec-grow (get v) (* 2 (get n)) 0)) #u)
                          (array-set! (get v) (get n) c)
                          (set n (+ (get n) 1))))))
      (if (clause-learnt? s c) (push! (extract s learnts) (extract s nlearnts)) (push! (extract s clauses) (extract s nclauses))))))

(define* delete-clause! (subr cb-eff (sat-solver int) unit)
  (lambda (s c)
    (let ((k (cl s c)))
      (begin (array-set! k 0 (bitwise-ior (array-ref k 0) 2))
             (set (extract s cdb-dead) (cons c (get (extract s cdb-dead))))
             (if (get (extract s proof)) (proof-write! s "d " (clause-lits s c)) #u)))))

"Whether `c` is the reason for an assignment."
(define* locked? (subr cb-eff (sat-solver int) bool)
  (lambda (s c)
    (let ((l (array-ref (cl s c) 1)))
      (and (= (array-ref (s-reasons s) (lit-var l)) c) (= (array-ref (s-vals s) l) T)))))

"Move the literals of the sorted `v` that are kept to its front, and
return their number, or -1 if the clause is true (at level 0, or a
tautology)."
(define* clause-compact! (subr cb-eff (sat-solver ivec) int)
  (lambda (s v)
    (let ((vals (s-vals s)) (n (array-length v)))
      (letrec ((go (subr cb-eff (int int) int)
                 (lambda (k m)
                   (if (= k n) m
                       (let ((l (array-ref v k)))
                         (cond ((and (> m 0) (= l (array-ref v (- m 1)))) (go (+ k 1) m))
                               ((and (> k 0) (= l (lit-neg (array-ref v (- k 1))))) -1)
                               ((= (array-ref vals l) T) -1)
                               ((= (array-ref vals l) F) (go (+ k 1) m))
                               (else (begin (array-set! v m l) (go (+ k 1) (+ m 1))))))))))
        (go 0 0)))))

(define* insertion-sort! (subr cb-eff (ivec) unit)
  (lambda (v)
    (letrec ((outer (subr cb-eff (int) unit)
               (lambda (i)
                 (if (>= i (array-length v)) #u
                     (let ((x (array-ref v i)))
                       (letrec ((inner (subr cb-eff (int) unit)
                                  (lambda (j)
                                    (if (and (>= j 0) (> (array-ref v j) x))
                                        (begin (array-set! v (+ j 1) (array-ref v j)) (inner (- j 1)))
                                        (array-set! v (+ j 1) x)))))
                         (begin (inner (- i 1)) (outer (+ i 1)))))))))
      (outer 1))))

"Add a clause (its variables made if need be). Whether the clauses may
still be satisfiable. The literals are sorted, so that duplicates and
complementary literals are next to each other, then go into the clause
without the duplicates and those false at level 0."
(define* sat-add-clause! (subr cb-eff (sat-solver ints) bool)
  (lambda (s lits)
    (begin
      (cancel-until! s 0)
      (let ((v (list->ivec lits)))
        (begin
          (ensure-vars! s (letrec ((go (subr cb-eff (int int) int)
                                     (lambda (k m) (if (= k (array-length v)) m (go (+ k 1) (max m (lit-var (array-ref v k))))))))
                            (go 0 0)))
          (if (not (sat-ok? s)) #u
              (begin
                (if (< (array-length v) 16) (insertion-sort! v) (ivec-sort! v (array-length v) (lambda ((a int) (b int)) (< a b))))
                (let ((m (clause-compact! s v)))
                  (if (< m 0) #u
                      (begin
                        (if (= m (array-length v)) #u (proof-write! s "" (ivec->list v 0 m)))
                        (cond ((= m 0) (set (extract s ok) #f))
                              ((= m 1) (begin (assign! s (array-ref v 0) -1)
                                              (if (>= (propagate! s) 0) (begin (proof-write! s "" nil) (set (extract s ok) #f)) #u)))
                              (else (let ((k (the ivec (make-array (+ m 1) 0))))
                                      (begin (letrec ((go (subr cb-eff (int) unit)
                                                        (lambda (i) (if (= i m) #u (begin (array-set! k (+ i 1) (array-ref v i)) (go (+ i 1)))))))
                                               (go 0))
                                             (let ((c (store-clause! s k)))
                                               (begin (push-clause! s c) (attach-clause! s c))))))))))))))
      (sat-ok? s))))

"Drop the deleted clauses from a list of clauses (`v`, `n` of them)."
(define* compact-list! (subr cb-eff (sat-solver (ref ivec @cb) (ref int @cb)) unit)
  (lambda (s vr nr)
    (let ((v (get vr)) (n (get nr)))
      (letrec ((go (subr cb-eff (int int) unit)
                 (lambda (i j)
                   (if (< i n)
                       (let ((c (array-ref v i)))
                         (if (clause-deleted? s c) (go (+ i 1) j) (begin (array-set! v j c) (go (+ i 1) (+ j 1)))))
                       (set nr j)))))
        (go 0 0)))))

"Delete about half of the learnt clauses: those of the greatest LBD,
keeping those of LBD 2 or less, those that are reasons, and (once) those
used since the last reduction."
(define* reduce-db! (subr cb-eff (sat-solver) unit)
  (lambda (s)
    (let* ((n (get (extract s nlearnts))) (v (ivec-take (get (extract s learnts)) n)))
      (begin
        (ivec-sort! v n (lambda ((a int) (b int)) (> (clause-lbd s a) (clause-lbd s b))))
        (letrec ((go (subr cb-eff (int) unit)
                   (lambda (i)
                     (if (= i n) #u
                         (let ((c (array-ref v i)))
                           (begin
                             (cond ((or (>= i (quotient n 2)) (<= (clause-lbd s c) 2) (locked? s c)) #u)
                                   ((clause-used? s c) (clause-set-used! s c #f))
                                   (else (delete-clause! s c)))
                             (go (+ i 1))))))))
          (go 0))
        (compact-list! s (extract s learnts) (extract s nlearnts))
        (sweep-watches! s)))))

(define* satisfied? (subr cb-eff (sat-solver int) bool)
  (lambda (s c)
    (let ((vals (s-vals s)) (k (cl s c)))
      (letrec ((go (subr cb-eff (int) bool)
                 (lambda (p) (and (< p (array-length k)) (or (= (array-ref vals (array-ref k p)) T) (go (+ p 1)))))))
        (go 1)))))

"At level 0, with new units since last time: delete the clauses they
satisfy. The units go into the proof first, so that deleting their
reasons loses nothing."
(define* simplify! (subr cb-eff (sat-solver) unit)
  (lambda (s)
    (if (<= (s-trail-size s) (get (extract s simp-trail-size))) #u
        (begin
          (letrec ((units (subr cb-eff (int) unit)
                     (lambda (i)
                       (if (= i (s-trail-size s)) #u
                           (let ((l (array-ref (s-trail s) i)))
                             (begin (array-set! (s-reasons s) (lit-var l) -1) (proof-write! s "" (list l)) (units (+ i 1))))))))
            (units (get (extract s simp-trail-size))))
          (let ((del! (lambda ((v ivec) (n int))
                        (letrec ((go (subr cb-eff (int) unit)
                                   (lambda (i) (if (= i n) #u
                                                   (begin (if (satisfied? s (array-ref v i)) (delete-clause! s (array-ref v i)) #u)
                                                          (go (+ i 1)))))))
                          (go 0)))))
            (begin (del! (get (extract s clauses)) (get (extract s nclauses)))
                   (del! (get (extract s learnts)) (get (extract s nlearnts)))))
          (compact-list! s (extract s clauses) (extract s nclauses))
          (compact-list! s (extract s learnts) (extract s nlearnts))
          (sweep-watches! s)
          (set (extract s simp-trail-size) (s-trail-size s))))))

;;; ------------------------------------------------------------ search

"The next decision literal, or 0 if every variable is assigned."
(define* pick-branch (subr cb-eff (sat-solver) int)
  (lambda (s)
    (let ((vals (s-vals s)) (pol (get (extract s polarity))))
      (letrec ((go (subr cb-eff () int)
                 (lambda ()
                   (if (= 0 (get (extract s heap-size))) 0
                       (let ((v (heap-pop! s)))
                         (if (= (array-ref vals (+ v v)) U) (+ (+ v v) (array-ref pol v)) (go)))))))
        (go)))))

"Restarts, as in Glucose (Audemard and Simon, 2012): when the recent learnt
clauses are worse (greater LBD) than those of the whole search, by a
factor 1.25, after at least 50 conflicts since the last. Put off when the
trail is 1.4 times longer than usual at conflicts. The averages are of
ints times 2^16: the recent LBDs over about 32 conflicts, the trail over
about 4096."
(define* note-conflict! (subr cb-eff (sat-solver int) unit)
  (lambda (s lbd)
    (let ((fast (get (extract s glue-fast))) (tr (get (extract s trail-slow))))
      (begin (set (extract s glue-fast) (+ fast (arithmetic-shift (- (* lbd 65536) fast) -5)))
             (incr! (extract s glue-sum) lbd)
             (incr! (extract s glue-count) 1)
             (set (extract s trail-slow) (+ tr (arithmetic-shift (- (* (s-trail-size s) 65536) tr) -12)))))))
(define* restart? (subr cb-eff (sat-solver int) bool)
  (lambda (s nconfl)
    (and (>= nconfl 50)
         (> (* (* 4 (get (extract s glue-fast))) (get (extract s glue-count))) (* 327680 (get (extract s glue-sum)))))))
(define* block-restart? (subr cb-eff (sat-solver) bool)
  (lambda (s)
    (and (> (get (extract s glue-count)) 10000)
         (> (* 655360 (s-trail-size s)) (* 14 (get (extract s trail-slow)))))))

"Learn from a conflict: backjump and assert the learnt clause."
(define* learn! (subr cb-eff (sat-solver int) unit)
  (lambda (s confl)
    (let* ((lits (analyze s confl))
           (bt (if (null? (cdr lits)) 0 (level-of s (car (cdr lits)))))
           (lbd (compute-lbd s lits)))
      (begin
        (note-conflict! s lbd)
        (proof-write! s "" lits)
        (cancel-until! s bt)
        (if (null? (cdr lits))
            (assign! s (car lits) -1)
            (let ((c (make-clause s lits #t lbd)))
              (begin (push-clause! s c) (attach-clause! s c) (assign! s (car lits) c))))
        (decay-var-activity! s)))))

"The literal of `lits` of the greatest level (the first such)."
(define* best-level (subr cb-eff (sat-solver int ints) int)
  (lambda (s b l) (cond ((null? l) b) ((> (level-of s (car l)) (level-of s b)) (best-level s (car l) (cdr l))) (else (best-level s b (cdr l))))))

;; What a theory's check comes to, for the search.
(define check-ok int -1)
(define check-unsat int -2)
(define check-continue int -3)

"Clauses whose first literal the others, all false, imply: each added (as
learnt, of LBD at least 3, so that reduce-db! may drop it) and its first
literal assigned, if it is still unassigned."
(define* theory-propagate! (subr cb-eff (sat-solver (listof ints acyclic)) int)
  (lambda (s clauses)
    (if (null? clauses) check-continue
        (let ((lits (car clauses)))
          (begin
            (if (= (array-ref (s-vals s) (car lits)) U)
                (let* ((best (best-level s (car (cdr lits)) (cdr lits)))
                       (lits (the ints (cons (car lits) (cons best (remv-once best (cdr lits))))))
                       (c (make-clause s lits #t (max 3 (compute-lbd s lits)))))
                  (begin (push-clause! s c) (attach-clause! s c) (assign! s (car lits) c)))
                #u)
            (theory-propagate! s (cdr clauses)))))))

"A clause whose first literal is unassigned and the others false: added,
and its first literal implied by it."
(define* theory-lemma! (subr cb-eff (sat-solver ints) int)
  (lambda (s lits)
    (begin
      (if (null? (cdr lits))
          (begin (cancel-until! s 0) (assign! s (car lits) -1))
          (let* ((best (best-level s (car (cdr lits)) (cdr lits)))
                 (lits (the ints (cons (car lits) (cons best (remv-once best (cdr lits))))))
                 (c (make-clause s lits #t (compute-lbd s lits))))
            (begin (push-clause! s c) (attach-clause! s c) (assign! s (car lits) c))))
      check-continue)))

(define* theory-unsat! (subr cb-eff (sat-solver) int)
  (lambda (s) (begin (set (extract s ok) #f) check-unsat)))

"`lits`: a clause the theory proves, false now. A conflict to analyze (a
clause with two literals of the current level), or what to do instead."
(define* theory-conflict! (subr cb-eff (sat-solver ints) int)
  (lambda (s lits)
    (begin
      (incr! (extract s conflicts) 1)
      (let ((top (letrec ((go (subr cb-eff (int ints) int) (lambda (m l) (if (null? l) m (go (max m (level-of s (car l))) (cdr l))))))
                   (go 0 lits))))
        (if (= top 0) (theory-unsat! s)
            (let* ((at-top (letrec ((go (subr cb-eff (ints) ints)
                                      (lambda (l) (cond ((null? l) nil) ((= (level-of s (car l)) top) (cons (car l) (go (cdr l)))) (else (go (cdr l)))))))
                             (go lits)))
                   (rest (letrec ((go (subr cb-eff (ints) ints)
                                    (lambda (l) (cond ((null? l) nil) ((< (level-of s (car l)) top) (cons (car l) (go (cdr l)))) (else (go (cdr l)))))))
                           (go lits))))
              (begin
                (cancel-until! s top)
                (if (null? (cdr at-top))
                    ;; Unit below top: backjump and assert it.
                    (let ((second (letrec ((go (subr cb-eff (int ints) int) (lambda (m l) (if (null? l) m (go (max m (level-of s (car l))) (cdr l))))))
                                    (go 0 rest))))
                      (begin
                        (cancel-until! s second)
                        (if (null? rest)
                            (assign! s (car at-top) -1)
                            (let* ((best (best-level s (car rest) rest))
                                   (lits (the ints (cons (car at-top) (cons best (remv-once best rest)))))
                                   (c (make-clause s lits #t (compute-lbd s lits))))
                              (begin (push-clause! s c) (attach-clause! s c) (assign! s (car at-top) c))))
                        check-continue))
                    (let* ((lits (the ints (append at-top rest)))
                           (c (make-clause s lits #t (compute-lbd s lits))))
                      (begin (push-clause! s c) (attach-clause! s c) c))))))))))

"Ask the theory: `check-ok`, `check-unsat`, `check-continue` (it added
variables, or its clause, unit after a backjump, was asserted), or a
conflicting clause to analyze."
(define* theory-check! (subr cb-eff (sat-solver bool) int)
  (lambda (s final?)
    (tagcase ((extract (get (extract s theory)) check) final?)
      (t-ok () check-ok)
      (t-unsat () (theory-unsat! s))
      (t-continue () check-continue)
      (t-conflict (lits) (if (null? lits) (theory-unsat! s) (theory-conflict! s lits)))
      (t-lemma (lits) (theory-lemma! s lits))
      (t-propagate (cs) (theory-propagate! s cs)))))

(define* now-ns (subr (io clock) () int) (lambda () (i64->int (clock))))

"Whether the conflict budget or the time is up. Unless `always?`, the
clock is read only every 256 conflicts."
(define* out-of-budget? (subr cb-eff (sat-solver bool) bool)
  (lambda (s always?)
    (or (let ((b (get (extract s conflict-budget)))) (and (>= b 0) (>= (get (extract s conflicts)) b)))
        (let ((d (get (extract s deadline))))
          (and (>= d 0) (or always? (= 0 (bitwise-and (get (extract s conflicts)) 255)))
               (>= (now-ns) d))))))

;; What a search ends in.
(define search-sat int 1)
(define search-unsat int 2)
(define search-restart int 0)

"Search until a model, unsatisfiability, or a restart."
(define* search (subr cb-eff (sat-solver ivec) int)
  (lambda (s assumptions)
    (letrec ((go (subr cb-eff (int) int)
               (lambda (nconfl)
                 (let ((confl (let ((c (propagate! s)))
                                (if (or (>= c 0) (not (get (extract s has-theory)))) c (theory-check! s #f)))))
                   (cond
                    ((= confl check-unsat) search-unsat)
                    ((= confl check-continue)
                     (if (out-of-budget? s #t) (begin (cancel-until! s 0) search-restart) (go nconfl)))
                    ((>= confl 0)
                     (begin
                       (incr! (extract s conflicts) 1)
                       (if (= 0 (s-nlevels s))
                           (begin (proof-write! s "" nil) (set (extract s ok) #f) search-unsat)
                           (let ((nconfl (if (block-restart? s) -1 nconfl)))
                             (begin (learn! s confl) (go (+ nconfl 1)))))))
                    ((or (restart? s nconfl) (out-of-budget? s #f)) (begin (cancel-until! s 0) search-restart))
                    (else
                     (begin
                       (if (= 0 (s-nlevels s)) (simplify! s) #u)
                       (if (>= (get (extract s conflicts)) (get (extract s next-reduce)))
                           (begin (incr! (extract s reduce-inc) 300)
                                  (set (extract s next-reduce) (+ (get (extract s conflicts)) (+ 2000 (get (extract s reduce-inc)))))
                                  (reduce-db! s))
                           #u)
                       (decide nconfl)))))))
             (decide (subr cb-eff (int) int)
               (lambda (nconfl)
                 (let ((k (s-nlevels s)))
                   (if (< k (array-length assumptions))
                       (let* ((p (array-ref assumptions k)) (val (array-ref (s-vals s) p)))
                         (cond ((= val T) (begin (new-level! s) (decide nconfl)))
                               ((= val F) (begin (set (extract s final-conflict) (analyze-final s p)) search-unsat))
                               (else (begin (new-level! s) (assign! s p -1) (go nconfl)))))
                       (let ((next (pick-branch s)))
                         (if (= next 0)
                             (let ((r (if (get (extract s has-theory)) (theory-check! s #t) check-ok)))
                               (cond ((= r check-ok) search-sat)
                                     ((= r check-unsat) search-unsat)
                                     ((= r check-continue)
                                      (if (out-of-budget? s #t) (begin (cancel-until! s 0) search-restart) (go nconfl)))
                                     (else (begin (learn! s r) (go (+ nconfl 1))))))
                             (begin (incr! (extract s decisions) 1)
                                    (new-level! s)
                                    (assign! s next -1)
                                    (go nconfl)))))))))
      (go 0))))

"Solve under assumptions (literals): `sat-sat` (see `sat-model`),
`sat-unsat` (see `sat-final-conflict`: the assumptions that make it so,
none if the clauses alone are unsatisfiable), or `sat-unknown`, when the
budget runs out."
(define* sat-solve (subr cb-eff (sat-solver ints) int)
  (lambda (s assumptions)
    (begin
      (set (extract s model) (the (arrayof bool @cb) (make-array 0 #f)))
      (set (extract s final-conflict) nil)
      (ensure-vars! s (letrec ((go (subr spin (int ints) int) (lambda (m l) (if (null? l) m (go (max m (lit-var (car l))) (cdr l))))))
                        (go 0 assumptions)))
      (if (not (sat-ok? s)) sat-unsat
          (let ((as (list->ivec assumptions)))
            (letrec ((go (subr cb-eff () int)
                       (lambda ()
                         (let ((status (search s as)))
                           (begin
                             (incr! (extract s restarts) 1)
                             (cond ((= status search-sat)
                                    (let* ((n (sat-nvars s)) (m (the (arrayof bool @cb) (make-array (+ n 1) #f))) (vals (s-vals s)))
                                      (begin
                                        (letrec ((fill (subr cb-eff (int) unit)
                                                   (lambda (v) (if (> v n) #u (begin (array-set! m v (= (array-ref vals (+ v v)) T)) (fill (+ v 1)))))))
                                          (fill 1))
                                        (set (extract s model) m)
                                        (cancel-until! s 0)
                                        sat-sat)))
                                   ((= status search-unsat) (begin (cancel-until! s 0) sat-unsat))
                                   ((out-of-budget? s #t) sat-unknown)
                                   (else (go))))))))
              (go)))))))

"The value of variable `v`, or literal `l`, in the last model."
(define* sat-value (subr (read @cb) (sat-solver int) bool)
  (lambda (s v) (let ((m (get (extract s model)))) (and (< v (array-length m)) (array-ref m v)))))
(define* sat-lit-value (subr (read @cb) (sat-solver int) bool)
  (lambda (s l) (let ((b (sat-value s (lit-var l)))) (if (lit-negative? l) (not b) b))))
(define* sat-final-conflict (subr (read @cb) (sat-solver) ints) (lambda (s) (get (extract s final-conflict))))
"The last model, by variable (`elim.fx` extends it)."
(define* sat-model (subr (read @cb) (sat-solver) (arrayof bool @cb)) (lambda (s) (get (extract s model))))

"A conflict budget (-1: none), and a deadline, in nanoseconds of the
clock (`now-ns`; -1: none)."
(define* sat-set-conflict-budget! (subr (write @cb) (sat-solver int) unit) (lambda (s b) (set (extract s conflict-budget) b)))
(define* sat-set-deadline! (subr (write @cb) (sat-solver int) unit) (lambda (s d) (set (extract s deadline) d)))
(define* sat-conflicts (subr (read @cb) (sat-solver) int) (lambda (s) (get (extract s conflicts))))
"Keep a DRAT proof; its lines so far, newest first."
(define* sat-keep-proof! (subr (write @cb) (sat-solver) unit) (lambda (s) (set (extract s proof) #t)))
(define* sat-proof-lines (subr (read @cb) (sat-solver) strings) (lambda (s) (get (extract s proof-lines))))
(define* sat-clear-proof-lines! (subr (write @cb) (sat-solver) unit) (lambda (s) (set (extract s proof-lines) nil)))

(define* sat-set-theory! (subr (write @cb) (sat-solver theory) unit)
  (lambda (s th) (begin (set (extract s theory) th) (set (extract s has-theory) #t))))

;; For theories: the trail, and what is assigned.
(define* sat-trail-size (subr (read @cb) (sat-solver) int) (lambda (s) (s-trail-size s)))
(define* sat-trail-lit (subr (read @cb) (sat-solver int) int) (lambda (s i) (array-ref (s-trail s) i)))
(define* sat-lit-level (subr (read @cb) (sat-solver int) int) (lambda (s l) (level-of s l)))
(define* sat-lit-true? (subr (read @cb) (sat-solver int) bool) (lambda (s l) (= (array-ref (s-vals s) l) T)))
(define* sat-lit-assigned? (subr (read @cb) (sat-solver int) bool) (lambda (s l) (not (= (array-ref (s-vals s) l) U))))
(define* sat-decision-level (subr (read @cb) (sat-solver) int) (lambda (s) (s-nlevels s)))
"The value variable `v` is decided to first (until phase saving changes it)."
(define* sat-set-phase! (subr (maxeff (read @cb) (write @cb)) (sat-solver int bool) unit)
  (lambda (s v negative?) (array-set! (get (extract s polarity)) v (if negative? 1 0))))
"`v`, unassigned and in no clause, is never to be decided (it was
eliminated); its value in models is false."
(define* sat-remove-var! (subr cb-eff (sat-solver int) unit) (lambda (s v) (heap-remove! s v)))

(define-type stat (productof (name string) (value int)))
(define* sat-stats (subr (read @cb) (sat-solver) (listof stat acyclic))
  (lambda (s)
    (list (product (name "vars") (value (sat-nvars s)))
          (product (name "clauses") (value (get (extract s nclauses))))
          (product (name "learnts") (value (get (extract s nlearnts))))
          (product (name "conflicts") (value (get (extract s conflicts))))
          (product (name "decisions") (value (get (extract s decisions))))
          (product (name "propagations") (value (get (extract s propagations))))
          (product (name "restarts") (value (get (extract s restarts)))))))
