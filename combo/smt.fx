;;; smt.fx: an SMT solver context, combo's interface for programs that link
;;; it in (lockpick's `(lockpick smt)`):
;;;   (define c (make-smt))
;;;   (smt-assert! c term)                 ; terms from term.fx, bv.fx, arith.fx
;;;   (smt-push! c) ... (smt-pop! c)
;;;   (smt-check c assumption-terms)       ; sat-sat, sat-unsat or sat-unknown
;;;   (smt-value c term)                   ; after sat: its value
;;;
;;; The assertion stack is kept with activation literals: each level above 0
;;; has a SAT variable a, and an assertion t made at that level is added as
;;; the clauses of a -> t. A check assumes the activation literals of the
;;; levels in force. Popping a level adds the unit clause (not a), which
;;; satisfies its clauses for good (they are deleted at the next
;;; simplification), and also every clause learnt from them. The other
;;; learnt clauses stay. Literals given to terms stay too: the clauses that
;;; define them are unguarded, and hold at every level.

(module-parameters ((m-sat (load-moduleof "sat.fx")) (m-rat (load-moduleof "rat.fx"))
                    (m-term (load-moduleof "term.fx" m-sat m-rat))
                    (m-bv (load-moduleof "bv.fx" m-sat m-rat m-term))
                    (m-arith (load-moduleof "arith.fx" m-sat m-rat m-term))
                    (m-eval (load-moduleof "eval.fx" m-sat m-rat m-term))
                    (m-simplex (load-moduleof "simplex.fx" m-sat m-rat))
                    (m-blast (load-moduleof "blast.fx" m-sat m-rat m-term m-bv m-arith m-eval m-simplex))))

"A level above 0: its activation literal, and its assertions, newest first."
(define-type smt-frame (productof (act int) (assertions (ref ints @cb))))
(define-type smt
  (productof
   (solver sat-solver) (blaster blaster)
   (frames (ref (listof smt-frame acyclic) @cb))     ; innermost first
   (base (ref ints @cb))                         ; level 0's assertions, newest first
   (has-model (ref bool @cb))
   (failed (ref ints @cb))
   (reason (ref string @cb))
   (timeout (ref int @cb))                       ; milliseconds, or -1
   (check-models (ref bool @cb))
   ;; What went wrong inside the last check (\"\": nothing): a model that
   ;; does not satisfy an assertion is combo's bug.
   (problem (ref string @cb))))

(define* make-smt (subr cb-eff () smt)
  (lambda ()
    (let ((s (make-solver)))
      (product (solver s) (blaster (make-blaster s))
               (frames (new (the (listof smt-frame acyclic) nil))) (base (new (the ints nil)))
               (has-model (new #f)) (failed (new (the ints nil))) (reason (new "unknown"))
               (timeout (new -1)) (check-models (new #t)) (problem (new ""))))))

(define* smt-solver (subr pure (smt) sat-solver) (lambda (c) (extract c solver)))
(define* smt-level (subr (read @cb) (smt) int) (lambda (c) (list-length (get (extract c frames)))))
(define* smt-timeout (subr (read @cb) (smt) int) (lambda (c) (get (extract c timeout))))
(define* smt-set-timeout! (subr (write @cb) (smt int) unit) (lambda (c ms) (set (extract c timeout) ms)))
(define* smt-set-check-models! (subr (write @cb) (smt bool) unit) (lambda (c b) (set (extract c check-models) b)))
(define* smt-model-available? (subr (read @cb) (smt) bool) (lambda (c) (get (extract c has-model))))
(define* smt-reason-unknown (subr (read @cb) (smt) string) (lambda (c) (get (extract c reason))))
(define* smt-failed-assumptions (subr (read @cb) (smt) ints) (lambda (c) (get (extract c failed))))
(define* smt-problem (subr (read @cb) (smt) string) (lambda (c) (get (extract c problem))))
(define* smt-stats (subr (read @cb) (smt) (listof stat acyclic)) (lambda (c) (sat-stats (extract c solver))))

"The assertions in force, oldest first."
(define* smt-assertions (subr cb-eff (smt) ints)
  (lambda (c)
    (letrec ((go (subr cb-eff ((listof smt-frame acyclic) ints) ints)
               (lambda (fs acc) (if (null? fs) (append-ints (reverse-ints (get (extract c base))) acc)
                                    (go (cdr fs) (append-ints (reverse-ints (get (extract (car fs) assertions))) acc))))))
      (go (get (extract c frames)) nil))))

"Assert a Boolean term."
(define* smt-assert! (subr cb-eff (smt int) unit)
  (lambda (c t)
    (let ((frames (get (extract c frames))))
      (begin
        (set (extract c has-model) #f)
        (if (null? frames)
            (begin (set (extract c base) (cons t (get (extract c base)))) (blast-assert! (extract c blaster) t 0))
            (let ((f (car frames)))
              (begin (set (extract f assertions) (cons t (get (extract f assertions))))
                     (blast-assert! (extract c blaster) t (extract f act)))))))))

(define* smt-push! (subr cb-eff (smt) unit)
  (lambda (c)
    (let ((a (make-lit (sat-new-var! (extract c solver)) #f)))
      (set (extract c frames) (cons (product (act a) (assertions (the (ref ints @cb) (new (the ints nil))))) (get (extract c frames)))))))

"Pop a level (there is one)."
(define* smt-pop! (subr cb-eff (smt) unit)
  (lambda (c)
    (let ((a (extract (car (get (extract c frames))) act)))
      (begin (set (extract c frames) (cdr (get (extract c frames))))
             (set (extract c has-model) #f)
             (sat-add-clause! (extract c solver) (list (lit-neg a)))
             #u))))

"The literals of -bound <= x <= bound for each integer variable (none if
`bound` is -1)."
(define* box-lits (subr cb-eff (blaster int) ints)
  (lambda (b bound)
    (if (< bound 0) nil
        (letrec ((go (subr cb-eff (ints ints) ints)
                   (lambda (ts acc)
                     (if (null? ts) acc
                         (let* ((hi (blast-bool! b (mk-le (car ts) (num-int bound int-sort))))
                                (lo (blast-bool! b (mk-ge (car ts) (num-int (- 0 bound) int-sort)))))
                           (go (cdr ts) (cons hi (cons lo acc))))))))
          (go (blaster-int-terms b) nil)))))

"Check the assertions in force, with the Boolean terms `assumptions`
assumed too: sat-sat, sat-unsat or sat-unknown.

With integer variables, branch and bound may wander off without end where
they are unbounded. So the check is first made with every integer variable
assumed to be in [-B, B], for B = 2^8 and 2^16, and only then without
bounds: an answer sat, or unsat with no bound among the failed
assumptions, is the answer. No cuts in the first box: there branch and
bound soon ends, and cuts (valid, but with growing coefficients) led a
fuzzed formula away from its small solutions."
(define* smt-check (subr cb-eff (smt ints) int)
  (lambda (c assumptions)
    (let* ((s (extract c solver)) (b (extract c blaster))
           (alits (blast-list! b assumptions))
           (acts (reverse-ints (letrec ((go (subr cb-eff ((listof smt-frame acyclic)) ints)
                                          (lambda (fs) (if (null? fs) nil (cons (extract (car fs) act) (go (cdr fs)))))))
                                 (go (get (extract c frames)))))))
      (begin
        (set (extract c has-model) #f)
        (set (extract c failed) nil)
        (set (extract c problem) "")
        (sat-set-deadline! s (if (< (get (extract c timeout)) 0) -1 (+ (now-ns) (* (get (extract c timeout)) 1000000))))
        (letrec ((go (subr cb-eff (ints) int)
                   (lambda (bounds)
                     (begin
                       (if (blaster-has-simplex? b) (simplex-set-cuts! (blaster-simplex b) (not (= (car bounds) 256))) #u)
                       (let* ((blits (box-lits b (car bounds)))
                              (answer (sat-solve s (append-ints acts (append-ints alits blits)))))
                         (if (and (= answer sat-unsat) (>= (car bounds) 0)
                                  (let ((failed (sat-final-conflict s)))
                                    (letrec ((any (subr cb-eff (ints) bool) (lambda (ls) (and (pair? ls) (or (memv? (car ls) failed) (any (cdr ls)))))))
                                      (any blits))))
                             (go (cdr bounds))
                             (finish-check! c answer assumptions alits)))))))
          (go (if (null? (blaster-int-terms b)) (list -1) (list 256 65536 -1))))))))

(define* finish-check! (subr cb-eff (smt int ints ints) int)
  (lambda (c answer assumptions alits)
    (let ((s (extract c solver)) (b (extract c blaster)))
      (begin
        (cond ((= answer sat-sat)
               (begin (set (extract c has-model) #t)
                      (if (get (extract c check-models)) (check-model c (append-ints assumptions (smt-assertions c))) #u)))
              ((= answer sat-unsat)
               (let ((failed (sat-final-conflict s)))
                 (set (extract c failed)
                      (letrec ((go (subr cb-eff (ints ints) ints)
                                 (lambda (ts ls) (cond ((null? ts) nil)
                                                       ((memv? (car ls) failed) (cons (car ts) (go (cdr ts) (cdr ls))))
                                                       (else (go (cdr ts) (cdr ls)))))))
                        (go assumptions alits)))))
              (else (set (extract c reason) (if (< (get (extract c timeout)) 0) "unknown" "timeout"))))
        answer))))

"Every term must be true in the model: if not, combo has a bug, said by
`smt-problem`."
(define* check-model (subr cb-eff (smt ints) unit)
  (lambda (c terms)
    (if (null? terms) #u
        (if (rat-true? (smt-value c (car terms)))
            (check-model c (cdr terms))
            (set (extract c problem) "combo: internal error: the model does not satisfy an assertion")))))

"The value of a term in the model of the last check (which was sat):
Bool 1 or 0, integers for Int and bitvectors, rationals for Real."
(define* smt-value (subr cb-eff (smt int) rat)
  (lambda (c t) (eval-term t (lambda ((v int)) (blaster-var-value (extract c blaster) v)))))
