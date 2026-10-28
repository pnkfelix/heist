;;; dimacs.fx: CNF in DIMACS format, and a solver's answer in the format of
;;; the SAT Competition (lockpick's `(lockpick dimacs)`). Also the
;;; incremental format iCNF ("p inccnf"), where a line "a LITS 0" asks for
;;; a solve under the assumptions LITS, of the clauses so far.
;;;
;;; Reading is of bytes already read (the caller does the I/O), into the
;;; clauses and assumptions in order; answers are text.

(module-parameters ((m-sat (load-moduleof "sat.fx"))))

"What a CNF says, in order: a clause, or (iCNF) a solve under assumptions."
(define-datatype dimacs-item (d-clause ints) (d-assume ints))
(define-type dimacs-items (listof dimacs-item acyclic))
"A CNF read: the number of variables of its header (0 if none), and its
items; or why it could not be read."
(define-datatype dimacs-read
  (dimacs-ok int dimacs-items)
  (dimacs-bad string))

(define-type bytes (bytevectorof @cb))

"Read a CNF. Comment lines start with c, and % ends the formula (as in
some old benchmark files)."
(define* read-dimacs (subr cb-eff (bytes) dimacs-read)
  (lambda (b)
    (let ((len (bytevector-length b)))
      (letrec ((at (subr (read @cb) (int) int) (lambda (i) (if (< i len) (u8->int (bytevector-u8-ref b i)) -1)))
               (space? (subr pure (int) bool) (lambda (c) (or (= c 32) (and (>= c 9) (<= c 13)))))
               (digit? (subr pure (int) bool) (lambda (c) (and (>= c 48) (<= c 57))))
               (skip-space (subr cb-eff (int) int) (lambda (i) (if (space? (at i)) (skip-space (+ i 1)) i)))
               (skip-line (subr cb-eff (int) int)
                 (lambda (i) (cond ((>= i len) i) ((= (at i) 10) (+ i 1)) (else (skip-line (+ i 1))))))
               (word-end (subr cb-eff (int) int) (lambda (i) (if (and (< i len) (not (space? (at i)))) (word-end (+ i 1)) i)))
               (word (subr cb-eff (int int) string)
                 (lambda (i j) (list->string (letrec ((go (subr cb-eff (int) (listof char acyclic))
                                                         (lambda (k) (if (>= k j) nil (cons (integer->char (at k)) (go (+ k 1)))))))
                                                (go i)))))
               ;; An integer at i: its value and the position after it, or -1.
               (int-end (subr cb-eff (int) int)
                 (lambda (i) (let ((j (if (= (at i) 45) (+ i 1) i)))
                               (letrec ((go (subr cb-eff (int) int) (lambda (k) (if (digit? (at k)) (go (+ k 1)) k))))
                                 (let ((k (go j))) (if (= k j) -1 k))))))
               (int-at (subr cb-eff (int int) int)
                 (lambda (i end)
                   (let ((neg (= (at i) 45)))
                     (letrec ((go (subr cb-eff (int int) int)
                                (lambda (k n) (if (>= k end) n (go (+ k 1) (+ (* n 10) (- (at k) 48)))))))
                       (let ((n (go (if neg (+ i 1) i) 0))) (if neg (- 0 n) n))))))
               (bad-int (subr cb-eff (int) dimacs-read)
                 (lambda (i) (dimacs-bad (string-append "read-dimacs: expected an integer at " (word i (word-end i))))))
               (go (subr cb-eff (int int ints dimacs-items) dimacs-read)
                 (lambda (i nvars clause items)
                   (let* ((i (skip-space i)) (c (at i)))
                     (cond ((or (< c 0) (= c 37))         ; the end, or %
                            (dimacs-ok nvars (reverse-items (if (null? clause) items (cons (d-clause (reverse-ints clause)) items)))))
                           ((= c 99) (go (skip-line i) nvars clause items))   ; c
                           ((= c 112)                                         ; p
                            (let* ((i (skip-space (+ i 1))) (e (word-end i)) (format (word i e)))
                              (cond ((string=? format "cnf")
                                     (let* ((i (skip-space e)) (e1 (int-end i)))
                                       (if (< e1 0) (bad-int i)
                                           (let* ((n (int-at i e1)) (i (skip-space e1)) (e2 (int-end i)))
                                             (if (< e2 0) (bad-int i) (go e2 n clause items))))))
                                    ((string=? format "inccnf") (go e nvars clause items))
                                    (else (dimacs-bad (string-append "read-dimacs: not a CNF header " format))))))
                           ((= c 97)                                          ; a
                            (letrec ((lits (subr cb-eff (int ints) dimacs-read)
                                       (lambda (i acc)
                                         (let* ((i (skip-space i)) (e (int-end i)))
                                           (if (< e 0) (bad-int i)
                                               (let ((n (int-at i e)))
                                                 (if (= n 0) (go e nvars clause (cons (d-assume (reverse-ints acc)) items))
                                                     (lits e (cons (int->lit n) acc)))))))))
                              (lits (+ i 1) nil)))
                           (else
                            (let ((e (int-end i)))
                              (if (< e 0) (bad-int i)
                                  (let ((n (int-at i e)))
                                    (if (= n 0) (go e nvars nil (cons (d-clause (reverse-ints clause)) items))
                                        (go e nvars (cons (int->lit n) clause) items)))))))))))
        (go 0 0 nil nil)))))

(define* reverse-items (subr spin (dimacs-items) dimacs-items)
  (lambda (l) (letrec ((go (subr spin (dimacs-items dimacs-items) dimacs-items) (lambda (l acc) (if (null? l) acc (go (cdr l) (cons (car l) acc))))))
                (go l nil))))

"The answer as the SAT Competition asks: \"s SATISFIABLE\" and the model on
\"v\" lines, or \"s UNSATISFIABLE\", or \"s UNKNOWN\"."
(define* dimacs-result (subr cb-eff (sat-solver int) string)
  (lambda (s answer)
    (cond ((= answer sat-sat)
           (let ((n (sat-nvars s)))
             (letrec ((go (subr cb-eff (int int strings) strings)
                        (lambda (v col acc)
                          (let ((acc (the strings (if (= col 0) (cons "v" acc) acc))))
                            (if (> v n) (cons " 0\n" acc)
                                (let ((acc (the strings (cons (int->string (if (sat-value s v) v (- 0 v))) (cons " " acc)))))
                                  (if (> col 15) (go (+ v 1) 0 (cons "\n" acc)) (go (+ v 1) (+ col 1) acc))))))))
               (string-concat (cons "s SATISFIABLE\n" (reverse-strings (go 1 0 nil)))))))
          ((= answer sat-unsat) "s UNSATISFIABLE\n")
          (else "s UNKNOWN\n"))))

"After an iCNF solve found unsatisfiable: the failed assumptions, on an
\"f\" line."
(define* dimacs-failed (subr cb-eff (sat-solver) string)
  (lambda (s)
    (letrec ((go (subr cb-eff (ints strings) strings)
               (lambda (l acc) (if (null? l) acc (go (cdr l) (cons (int->string (lit->int (car l))) (cons " " acc)))))))
      (string-concat (cons "f" (reverse-strings (cons " 0\n" (go (sat-final-conflict s) nil))))))))
