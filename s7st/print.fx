;;; print.fx: `write` and `display` -- a value's external representation.
;;;
;;; A cyclic list or vector is not written with datum labels (R7RS's
;;; `write` would): printing stops after `s7-print-limit` items with
;;; `...`, so that it ends.

"Strings `l`, joined: pairwise, so the work is n log n."
(define* s7-concat (subr spin ((listof string acyclic)) string)
  (lambda (l)
    (letrec ((pairs (subr spin ((listof string acyclic)) (listof string acyclic))
               (lambda (l)
                 (cond ((null? l) nil)
                       ((null? (cdr l)) l)
                       (else (cons (string-append (car l) (car (cdr l))) (pairs (cdr (cdr l)))))))))
      (cond ((null? l) "")
            ((null? (cdr l)) (car l))
            (else (s7-concat (pairs l)))))))

"`s` on `l`, an immutable list."
(define* s7-push (subr pure (string (listof string acyclic)) (listof string acyclic))
  (lambda (s l) (cons s l)))

(define s7-print-limit int 100000)

"Whether symbol name `s` must be written between bars: it is empty, would
read as a number, or has a character a symbol read cannot."
(define* s7-bar-symbol? (subr (maxeff spin (alloc @sc) (read @sc)) (string) bool)
  (lambda (s)
    (let ((n (string-length s)))
      (letrec ((odd (subr spin (int) bool)
                 (lambda (i) (and (< i n)
                                  (or (s7-delimiter? (string-ref s i)) (char-in? (string-ref s i) "'`,#")
                                      (char=? (string-ref s i) #\[) (char=? (string-ref s i) #\])
                                      (odd (+ i 1)))))))
        (or (= n 0)
            (string=? s ".")
            (char=? (string-ref s 0) #\#)
            (odd 0)
            (typecase (s7-parse-number s 10) (bool b #f) (else y #t)))))))

(define* s7-hex (subr spin (int) string)
  (lambda (i)
    (letrec ((go (subr spin (int (listof char acyclic)) (listof char acyclic))
               (lambda (i acc)
                 (let* ((d (remainder i 16))
                        (c (string-ref "0123456789abcdef" d)))
                   (if (< i 16) (cons c acc) (go (quotient i 16) (cons c acc)))))))
      (list->string (go i nil)))))

"Ints `l`, each after a space but the first, then `end`."
(define* s7-join-ints (subr spin ((listof int acyclic) string) (listof string acyclic))
  (lambda (l end)
    (cond ((null? l) (list end))
          ((null? (cdr l)) (list (int->string (car l)) end))
          (else (cons (int->string (car l)) (cons " " (s7-join-ints (cdr l) end)))))))

"How character `c` is written."
(define* s7-char-name (subr spin (char) string)
  (lambda (c)
    (let ((i (char->integer c)))
      (cond ((char=? c #\space) "space")
            ((char=? c #\newline) "newline")
            ((char=? c #\tab) "tab")
            ((= i 13) "return")
            ((= i 0) "null")
            ((= i 7) "alarm")
            ((= i 8) "backspace")
            ((= i 127) "delete")
            ((= i 27) "escape")
            ((< i 32) (string-append "x" (s7-hex i)))
            (else (char->string c))))))

"String `s` as `write` writes it: quoted, escaped."
(define* s7-quote-string (subr spin (string string) string)
  (lambda (s quote)
    (let ((n (string-length s)))
      (letrec ((go (subr spin (int (listof string acyclic)) (listof string acyclic))
                 (lambda (i acc)
                   (if (>= i n) acc
                       (let* ((c (string-ref s i)) (k (char->integer c)))
                         (go (+ i 1)
                             (cons (cond ((char=? c #\\) "\\\\")
                                         ((string=? (char->string c) quote) (string-append "\\" quote))
                                         ((char=? c #\newline) "\\n")
                                         ((char=? c #\tab) "\\t")
                                         ((= k 13) "\\r")
                                         ((< k 32) (string-append "\\x" (s7-hex k) ";"))
                                         (else (char->string c)))
                                   acc)))))))
        (s7-concat (reverse (the (listof string acyclic) (cons quote (go 0 (list quote))))))))))

"Which pairs (by car cell) and vectors of `v` a datum label must mark, as
`write` marks them: those a cycle comes back to; or, if `shared`, those met
more than once. Each mapped to -1 (not yet numbered). A list's tail is
walked in a loop, not by recursion."
(define-type s7-marks (productof (pairs (eqtable (ref s7-value @sc) int @sc @sc)) (vecs (eqtable (arrayof s7-value @sc) int @sc @sc))))
(define* s7-label-marks (subr (maxeff spin (read @sc) (write @sc) (alloc @sc)) (s7-value bool) s7-marks)
  (lambda (v shared)
    (let ((need (product (pairs (the (eqtable (ref s7-value @sc) int @sc @sc) (make-eqtable (ref-identity))))
                         (vecs (the (eqtable (arrayof s7-value @sc) int @sc @sc) (make-eqtable (array-identity))))))
          ;; 1: being walked (on the stack); 2: walked.
          (pstate (the (eqtable (ref s7-value @sc) int @sc @sc) (make-eqtable (ref-identity))))
          (vstate (the (eqtable (arrayof s7-value @sc) int @sc @sc) (make-eqtable (array-identity)))))
      (letrec ((seen-pair (subr (maxeff spin (read @sc) (write @sc) (alloc @sc)) ((ref s7-value @sc)) bool)
                 ;; Whether pair (cell) `c` has been met: if so, marked if it must be.
                 (lambda (c)
                   (let ((st (eqtable-ref pstate c 0)))
                     (cond ((= st 0) #f)
                           ((or (= st 1) shared) (begin (eqtable-set! (extract need pairs) c -1) #t))
                           (else #t)))))
               (visit (subr (maxeff spin (read @sc) (write @sc) (alloc @sc)) (s7-value) unit)
                 (lambda (x)
                   (tagcase x
                     (pair p (if (seen-pair (extract p car)) #u (chain x nil)))
                     (vec a (let ((st (eqtable-ref vstate a 0)))
                              (cond ((= st 0) (begin (eqtable-set! vstate a 1)
                                                (letrec ((each (subr (maxeff spin (read @sc) (write @sc) (alloc @sc)) (s7-values) unit)
                                                           (lambda (l) (if (null? l) #u (begin (visit (car l)) (each (cdr l)))))))
                                                  (each (array->list a)))
                                                (eqtable-set! vstate a 2)))
                                    ((or (= st 1) shared) (eqtable-set! (extract need vecs) a -1))
                                    (else #u))))
                     (else y #u))))
               ;; A list's pairs from `x` (not met yet), each on the stack while its tail is walked.
               (chain (subr (maxeff spin (read @sc) (write @sc) (alloc @sc)) (s7-value (listof (ref s7-value @sc) acyclic)) unit)
                 (lambda (x walked)
                   (tagcase x
                     (pair p (if (seen-pair (extract p car)) (done walked)
                                 (begin (eqtable-set! pstate (extract p car) 1)
                                   (visit (get (extract p car)))
                                   (chain (get (extract p cdr)) (cons (extract p car) walked)))))
                     (else y (begin (visit y) (done walked))))))
               (done (subr (maxeff spin (read @sc) (write @sc) (alloc @sc)) ((listof (ref s7-value @sc) acyclic)) unit)
                 (lambda (l) (if (null? l) #u (begin (eqtable-set! pstate (car l) 2) (done (cdr l)))))))
        (begin (visit v) need)))))

"Value `v` shown, its datum labels as `labels` says: 0, none (`write-simple`:
it ends, on a cycle, at `s7-print-limit` items); 1, where a cycle comes
back (`write`, `display`); 2, wherever a pair or vector is met twice
(`write-shared`)."
(define* s7-show-with (subr (maxeff spin (read @sc) (write @sc) (alloc @sc)) (s7-value bool int) string)
  (lambda (v write? labels)
   (let* ((marks (if (= labels 0)
                     (product (pairs (the (eqtable (ref s7-value @sc) int @sc @sc) (make-eqtable (ref-identity))))
                              (vecs (the (eqtable (arrayof s7-value @sc) int @sc @sc) (make-eqtable (array-identity)))))
                     (s7-label-marks v (= labels 2))))
          (next (the (ref int @sc) (new 0)))
          ;; The label `x` has, if it must have one: "#n=" the first time, "#n#" after; else "".
          (label (lambda ((x s7-value))
                   (let ((number (lambda ((n int) (fresh (subr (maxeff spin (read @sc) (write @sc) (alloc @sc)) (int) unit)))
                                   (if (>= n 0) (string-append "#" (int->string n) "#")
                                       (let ((k (get next)))
                                         (begin (set next (+ k 1)) (fresh k) (string-append "#" (int->string k) "=")))))))
                     (tagcase x
                       (pair p (let ((n (eqtable-ref (extract marks pairs) (extract p car) -2)))
                                 (if (= n -2) "" (number n (lambda ((k int)) (eqtable-set! (extract marks pairs) (extract p car) k))))))
                       (vec a (let ((n (eqtable-ref (extract marks vecs) a -2)))
                                (if (= n -2) "" (number n (lambda ((k int)) (eqtable-set! (extract marks vecs) a k))))))
                       (else y ""))))))
    (letrec ((go (subr (maxeff spin (read @sc) (write @sc) (alloc @sc)) (s7-value (listof string acyclic) int)
                       (productof (out (listof string acyclic)) (left int)))
               ;; `v` shown onto `acc` (last first), `left` items more allowed.
               (lambda (v acc left)
                 (let ((one (lambda ((s string)) (product (out (s7-push s acc)) (left (- left 1))))))
                   (if (<= left 0) (product (out (s7-push "..." acc)) (left 0))
                       (tagcase v
                         (null u (one "()"))
                         (unspec u (one "#<unspecified>"))
                         (undef u (one "#<undefined>"))
                         (eof u (one "#<eof>"))
                         (bool b (one (if b "#t" "#f")))
                         (int i (one (int->string i)))
                         (ratio q (one (string-append (int->string (extract q num)) "/" (int->string (extract q den)))))
                         (real r (one (f64->string r)))
                         (char c (one (if write? (string-append "#\\" (s7-char-name c)) (char->string c))))
                         (str s (one (if write? (s7-quote-string (get s) "\"") (get s))))
                         (sym s (let ((name (s7-symbol-name s)))
                                  (one (if (and write? (s7-bar-symbol? name)) (s7-quote-string name "|") name))))
                         (pair p (let ((l (label v)))
                                   (cond ((string=? l "") (pair-items v (s7-push "(" acc) (- left 1) #t))
                                         ((char=? (string-ref l (- (string-length l) 1)) #\#) (one l))
                                         (else (pair-items v (s7-push "(" (s7-push l acc)) (- left 1) #t)))))
                         (vec a (let ((l (label v)))
                                  (cond ((string=? l "") (items (array->list a) (s7-push "#(" acc) left #t))
                                        ((char=? (string-ref l (- (string-length l) 1)) #\#) (one l))
                                        (else (items (array->list a) (s7-push "#(" (s7-push l acc)) left #t)))))
                         (bytes a (one (s7-concat (cons "#u8(" (s7-join-ints (array->list a) ")")))))
                         (proc c (one (let ((n (get (extract c name))))
                                        (if (string=? n "") "#<procedure>" (string-append "#<procedure " n ">")))))
                         (prim p (one (string-append "#<procedure " (extract p name) ">")))
                         (cont c (one "#<continuation>"))
                         (multi l (if (null? l) (product (out acc) (left left))
                                      (items l acc left #f)))
                         (record r (record-of r acc left))
                         (rtd r (one (string-append "#<record-type " (extract r name) ">")))
                         (port p (one (if (extract p input) "#<input-port>" "#<output-port>")))
                         (table t (one (string-append "#<hash-table " (int->string (get (extract t count))) ">")))
                         (env u (one "#<environment>"))
                         (errobj e (let ((irritants (tagcase (s7-list-items (extract e irritants)) (some l l) (none u nil))))
                                     (if write?
                                         (items-then irritants (cons (string-append "#<error " (s7-quote-string (extract e message) "\""))
                                                                     acc)
                                                     left ">")
                                         (items-then irritants (cons (extract e message) acc) left "")))))))))
             ;; A list's items from pair `v`, the first not to have a space before it.
             (pair-items (subr (maxeff spin (read @sc) (write @sc) (alloc @sc)) (s7-value (listof string acyclic) int bool)
                               (productof (out (listof string acyclic)) (left int)))
               (lambda (v acc left first)
                 (tagcase v
                   (null u (product (out (s7-push ")" acc)) (left left)))
                   (pair p (if (and (not first) (not (= (eqtable-ref (extract marks pairs) (extract p car) -2) -2)))
                               ;; A tail a label marks: written after a dot.
                               (let ((r (go v (s7-push " . " acc) left)))
                                 (product (out (s7-push ")" (extract r out))) (left (extract r left))))
                               (let ((r (go (get (extract p car)) (if first acc (s7-push " " acc)) left)))
                                 (pair-items (get (extract p cdr)) (extract r out) (extract r left) #f))))
                   (else y (let ((r (go y (cons " . " acc) left)))
                             (product (out (s7-push ")" (extract r out))) (left (extract r left))))))))
             ;; Items `l`, then `)` if `close`.
             (items (subr (maxeff spin (read @sc) (write @sc) (alloc @sc)) (s7-values (listof string acyclic) int bool)
                          (productof (out (listof string acyclic)) (left int)))
               (lambda (l acc left close)
                 (letrec ((each (subr (maxeff spin (read @sc) (write @sc) (alloc @sc)) (s7-values (listof string acyclic) int bool)
                                      (productof (out (listof string acyclic)) (left int)))
                            (lambda (l acc left first)
                              (if (null? l) (product (out (if close (s7-push ")" acc) acc)) (left left))
                                  (let ((r (go (car l) (if first acc (cons " " acc)) left)))
                                    (each (cdr l) (extract r out) (extract r left) #f))))))
                   (each l acc left #t))))
             ;; Irritants after a message, each after a space, then `end`.
             (items-then (subr (maxeff spin (read @sc) (write @sc) (alloc @sc)) (s7-values (listof string acyclic) int string)
                               (productof (out (listof string acyclic)) (left int)))
               (lambda (l acc left end)
                 (if (null? l) (product (out (s7-push end acc)) (left left))
                     (let ((r (go (car l) (cons " " acc) left)))
                       (items-then (cdr l) (extract r out) (extract r left) end)))))
             (record-of (subr (maxeff spin (read @sc) (write @sc) (alloc @sc)) (s7-record (listof string acyclic) int)
                              (productof (out (listof string acyclic)) (left int)))
               (lambda (r acc left)
                 (letrec ((fields (subr (maxeff spin (read @sc) (write @sc) (alloc @sc)) (s7-symbols int (listof string acyclic) int)
                                        (productof (out (listof string acyclic)) (left int)))
                            (lambda (names i acc left)
                              (if (null? names) (product (out (s7-push ">" acc)) (left left))
                                  (let ((g (go (array-ref (extract r fields) i)
                                               (cons (string-append " " (s7-symbol-name (car names)) "=") acc) left)))
                                    (fields (cdr names) (+ i 1) (extract g out) (extract g left)))))))
                   (fields (extract (extract r rtd) fields) 0
                           (cons (string-append "#<" (extract (extract r rtd) name)) acc) left)))))
      (s7-concat (reverse (extract (go v nil s7-print-limit) out)))))))

"Value `v` as `write` (if `write?`) or `display` shows it, a cycle marked
with datum labels."
(define* s7-show (subr (maxeff spin (read @sc) (write @sc) (alloc @sc)) (s7-value bool) string)
  (lambda (v write?) (s7-show-with v write? 1)))
