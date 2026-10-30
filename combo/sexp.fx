;;; sexp.fx: reading and writing the S-expressions of SMT-LIB2 (lockpick's
;;; `(lockpick sexp)`).
;;;
;;; Data read: symbols (simple, or |quoted|), keywords (:foo, a symbol whose
;;; name starts with \":\"), numerals, decimals (1.5, exact), bitvector
;;; literals (#b0101, #x1F), strings (\"\" is a quote) and lists.
;;;
;;; The reader is fed text (`sexp-feed!`), and gives the next datum once the
;;; text has all of it (`sexp-read`), so that it never waits for input
;;; beyond the command it is reading: a client talking to the solver through
;;; a pipe waits for each answer. It does no I/O itself.

(module-parameters ((m-sat (load-moduleof "sat.fx")) (m-rat (load-moduleof "rat.fx"))))
(hide (define kit-strings (load-module "../kit/strings.fx"))
      (import kit-strings reverse-list->string))

(define-datatype sexp
  (sx-sym string)
  (sx-num int)
  (sx-dec rat)
  (sx-bv int int)                ; value, width
  (sx-str string)
  (sx-list (listof sexp acyclic)))
(define-type sexps (listof sexp acyclic))

"What a read gives: a datum; none until more text is fed; the end (the
text is all fed, and was all read); or a syntax error, at a line and
column (from 1 and 0, as z3 counts)."
(define-datatype sexp-result
  (r-datum sexp)
  (r-more)
  (r-eof)
  (r-error string int int))

"A reader: the text fed and not yet read (from pos), where pos is, and
whether all of the text has been fed."
(define-type sexp-reader
  (productof (buf (ref string @cb)) (pos (ref int @cb)) (line (ref int @cb)) (column (ref int @cb))
             (closed (ref bool @cb))))

(define* make-sexp-reader (subr cb-eff () sexp-reader)
  (lambda () (product (buf (new "")) (pos (new 0)) (line (new 1)) (column (new 0)) (closed (new #f)))))
"More text for the reader."
(define* sexp-feed! (subr cb-eff (sexp-reader string) unit)
  (lambda (r text)
    (let ((buf (get (extract r buf))) (pos (get (extract r pos))))
      (begin (set (extract r buf) (string-append (substring buf pos (string-length buf)) text))
             (set (extract r pos) 0)))))
"No more text will come."
(define* sexp-close! (subr (write @cb) (sexp-reader) unit) (lambda (r) (set (extract r closed) #t)))
(define* sexp-reader-line (subr (read @cb) (sexp-reader) int) (lambda (r) (get (extract r line))))
(define* sexp-reader-column (subr (read @cb) (sexp-reader) int) (lambda (r) (get (extract r column))))

;;; ------------------------------------------------------------ characters

(define* char-code (subr pure (char) int) (lambda (c) (char->integer c)))
(define* digit? (subr pure (char) bool) (lambda (c) (and (char>=? c #\0) (char<=? c #\9))))
(define* letter? (subr pure (char) bool)
  (lambda (c) (or (and (char>=? c #\a) (char<=? c #\z)) (and (char>=? c #\A) (char<=? c #\Z)) (> (char-code c) 127))))
(define* white? (subr pure (char) bool)
  (lambda (c) (or (char=? c #\space) (char=? c #\newline) (char=? c #\tab) (= (char-code c) 13) (= (char-code c) 12) (= (char-code c) 11))))
(define* symbol-char? (subr spin (char) bool)
  (lambda (c) (or (letter? c) (digit? c)
                  (letrec ((go (subr spin ((listof char acyclic)) bool) (lambda (l) (and (pair? l) (or (char=? c (car l)) (go (cdr l)))))))
                    (go (string->list "~!@$%^&*_-+=<>.?/"))))))
(define* hex-value (subr pure (char) int)
  (lambda (c) (cond ((digit? c) (- (char-code c) 48))
                    ((and (char>=? c #\a) (char<=? c #\f)) (+ 10 (- (char-code c) 97)))
                    ((and (char>=? c #\A) (char<=? c #\F)) (+ 10 (- (char-code c) 65)))
                    (else -1))))

;;; ------------------------------------------------------------ reading
;;; A datum is read from the reader's position; one that runs past the end
;;; of the text fed is read again once more is, from where it started.

;; Why a read stopped short: the text ran out (more may come), or an error.
(define-datatype scan
  (s-ok sexp int int int)          ; the datum; the position, line and column after it
  (s-short)
  (s-bad string int int))

(define* sexp-read (subr cb-eff (sexp-reader) sexp-result)
  (lambda (r)
    (let* ((buf (get (extract r buf))) (n (string-length buf)) (closed (get (extract r closed))))
      (letrec ((at (subr cb-eff (int) char) (lambda (i) (string-ref buf i)))
               ;; Skip white space and comments: the position, line and column after.
               (skip (subr cb-eff (int int int) (productof (i int) (line int) (col int)))
                 (lambda (i line col)
                   (cond ((>= i n) (product (i i) (line line) (col col)))
                         ((char=? (at i) #\newline) (skip (+ i 1) (+ line 1) 0))
                         ((white? (at i)) (skip (+ i 1) line (+ col 1)))
                         ((char=? (at i) #\;)
                          (letrec ((go (subr cb-eff (int int) (productof (i int) (line int) (col int)))
                                     (lambda (i col) (if (and (< i n) (not (char=? (at i) #\newline))) (go (+ i 1) (+ col 1)) (skip i line col)))))
                            (go i col)))
                         (else (product (i i) (line line) (col col))))))
               (span (subr cb-eff (int (subr spin (char) bool)) int)
                 (lambda (i ok?) (if (and (< i n) (ok? (at i))) (span (+ i 1) ok?) i)))
               (datum (subr cb-eff (int int int) scan)
                 (lambda (i line col)
                   (let* ((p (skip i line col)) (i (extract p i)) (line (extract p line)) (col (extract p col)))
                     (cond ((>= i n) (s-short))
                           ((char=? (at i) #\() (items (+ i 1) line (+ col 1) nil))
                           ((char=? (at i) #\)) (s-bad "unexpected ')'" line col))
                           (else (atom i line col))))))
               (items (subr cb-eff (int int int sexps) scan)
                 (lambda (i line col acc)
                   (let* ((p (skip i line col)) (i (extract p i)) (line (extract p line)) (col (extract p col)))
                     (cond ((>= i n) (s-short))
                           ((char=? (at i) #\)) (s-ok (sx-list (reverse acc)) (+ i 1) line (+ col 1)))
                           (else (tagcase (datum i line col)
                                   (s-ok (x i2 l2 c2) (items i2 l2 c2 (cons x acc)))
                                   (s-short () (s-short))
                                   (s-bad (m l c) (s-bad m l c))))))))
               ;; Text with no newline in it, from i to j: the column after it.
               (atom (subr cb-eff (int int int) scan)
                 (lambda (i line col)
                   (let ((c (at i)))
                     (cond
                      ((digit? c)
                       (let ((j (span i digit?)))
                         (cond ((and (>= j n) (not closed)) (s-short))
                               ((and (< j n) (char=? (at j) #\.))
                                (let ((k (span (+ j 1) digit?)))
                                  (if (and (>= k n) (not closed)) (s-short)
                                      (s-ok (sx-dec (rat+ (int->rat (decimal (substring buf i j)))
                                                          (if (= k (+ j 1)) rat-0 (make-rat (decimal (substring buf (+ j 1) k)) (expt10 (- k (+ j 1)))))))
                                            k line (+ col (- k i))))))
                               (else (s-ok (sx-num (decimal (substring buf i j))) j line (+ col (- j i)))))))
                      ((char=? c #\#)
                       (cond ((>= (+ i 1) n) (if closed (s-bad "invalid literal" line (+ col 1)) (s-short)))
                             ((char=? (at (+ i 1)) #\b)
                              (let ((j (span (+ i 2) (lambda ((c char)) (or (char=? c #\0) (char=? c #\1))))))
                                (cond ((and (>= j n) (not closed)) (s-short))
                                      ((= j (+ i 2)) (s-bad "invalid binary literal" line (+ col 2)))
                                      (else (s-ok (sx-bv (radix (substring buf (+ i 2) j) 2) (- j (+ i 2))) j line (+ col (- j i)))))))
                             ((char=? (at (+ i 1)) #\x)
                              (let ((j (span (+ i 2) (lambda ((c char)) (>= (hex-value c) 0)))))
                                (cond ((and (>= j n) (not closed)) (s-short))
                                      ((= j (+ i 2)) (s-bad "invalid hexadecimal literal" line (+ col 2)))
                                      (else (s-ok (sx-bv (radix (substring buf (+ i 2) j) 16) (* 4 (- j (+ i 2)))) j line (+ col (- j i)))))))
                             (else (s-bad "invalid literal" line (+ col 2)))))
                      ((char=? c #\")
                       (letrec ((go (subr cb-eff (int int int (listof char acyclic)) scan)
                                  (lambda (k line col acc)
                                    (cond ((>= k n) (if closed (s-bad "unexpected end of file in a string" line col) (s-short)))
                                          ((char=? (at k) #\")
                                           (cond ((>= (+ k 1) n) (if closed (s-ok (sx-str (reverse-list->string acc)) (+ k 1) line (+ col 1)) (s-short)))
                                                 ((char=? (at (+ k 1)) #\") (go (+ k 2) line (+ col 2) (cons #\" acc)))
                                                 (else (s-ok (sx-str (reverse-list->string acc)) (+ k 1) line (+ col 1)))))
                                          ((char=? (at k) #\newline) (go (+ k 1) (+ line 1) 0 (cons #\newline acc)))
                                          (else (go (+ k 1) line (+ col 1) (cons (at k) acc)))))))
                         (go (+ i 1) line (+ col 1) nil)))
                      ((char=? c #\|)
                       (letrec ((go (subr cb-eff (int int int) scan)
                                  (lambda (k line col)
                                    (cond ((>= k n) (if closed (s-bad "unexpected end of file in a quoted symbol" line col) (s-short)))
                                          ((char=? (at k) #\|) (s-ok (sx-sym (substring buf (+ i 1) k)) (+ k 1) line (+ col 1)))
                                          ((char=? (at k) #\newline) (go (+ k 1) (+ line 1) 0))
                                          (else (go (+ k 1) line (+ col 1)))))))
                         (go (+ i 1) line (+ col 1))))
                      ((char=? c #\:)
                       (let ((j (span (+ i 1) symbol-char?)))
                         (if (and (>= j n) (not closed)) (s-short) (s-ok (sx-sym (substring buf i j)) j line (+ col (- j i))))))
                      ((symbol-char? c)
                       (let ((j (span i symbol-char?)))
                         (if (and (>= j n) (not closed)) (s-short) (s-ok (sx-sym (substring buf i j)) j line (+ col (- j i))))))
                      (else (s-bad (string-append "unexpected character " (list->string (list c))) line (+ col 1))))))))
        (let ((p (skip (get (extract r pos)) (get (extract r line)) (get (extract r column)))))
          (if (>= (extract p i) n)
              (begin (set (extract r pos) (extract p i)) (set (extract r line) (extract p line)) (set (extract r column) (extract p col))
                     (if closed (r-eof) (r-more)))
              (tagcase (datum (get (extract r pos)) (get (extract r line)) (get (extract r column)))
                (s-ok (x i line col) (begin (set (extract r pos) i) (set (extract r line) line) (set (extract r column) col) (r-datum x)))
                (s-short () (if closed
                                ;; Where the text ends.
                                (letrec ((go (subr cb-eff (int int int) sexp-result)
                                           (lambda (i line col)
                                             (cond ((>= i n) (begin (set (extract r pos) n) (r-error "unexpected end of file" line col)))
                                                   ((char=? (at i) #\newline) (go (+ i 1) (+ line 1) 0))
                                                   (else (go (+ i 1) line (+ col 1)))))))
                                  (go (get (extract r pos)) (get (extract r line)) (get (extract r column))))
                                (r-more)))
                (s-bad (m line col) (begin (set (extract r pos) n) (set (extract r line) line) (set (extract r column) col) (r-error m line col))))))))))

"The number the digits of `s` write in base `b`."
(define* radix (subr spin (string int) int)
  (lambda (s b) (letrec ((go (subr spin (int int) int) (lambda (i acc) (if (>= i (string-length s)) acc (go (+ i 1) (+ (* acc b) (hex-value (string-ref s i))))))))
                  (go 0 0))))
(define* decimal (subr spin (string) int) (lambda (s) (radix s 10)))
(define* expt10 (subr spin (int) int) (lambda (k) (if (= k 0) 1 (* 10 (expt10 (- k 1))))))

;;; ------------------------------------------------------------ writing

"A symbol as SMT-LIB writes it: quoted with bars unless simple."
(define* symbol->smt-string (subr spin (string) string)
  (lambda (s)
    (if (and (> (string-length s) 0) (not (digit? (string-ref s 0)))
             (letrec ((go (subr spin (int) bool) (lambda (i) (or (= i (string-length s)) (and (symbol-char? (string-ref s i)) (go (+ i 1)))))))
               (go 0)))
        s
        (string-append "|" (string-append s "|")))))

"Digits of `v` in base `b` (2 or 16), lower case, at least `n` of them."
(define* digits (subr spin (int int int) string)
  (lambda (v b n)
    (letrec ((go (subr spin (int int (listof char acyclic)) (listof char acyclic))
               (lambda (v k acc)
                 (if (and (= v 0) (>= k n)) acc
                     (go (quotient v b) (+ k 1) (cons (string-ref "0123456789abcdef" (remainder v b)) acc))))))
      (list->string (go v 0 nil)))))

"#x if the width is a multiple of 4, else #b, as z3 does."
(define* bv->string (subr spin (int int) string)
  (lambda (value width)
    (if (and (> width 0) (= 0 (remainder width 4)))
        (string-append "#x" (digits value 16 (quotient width 4)))
        (string-append "#b" (digits value 2 width)))))

"A decimal as it was read: digits, a point, digits."
(define* decimal->string (subr spin (rat) string)
  (lambda (q)
    (letrec ((go (subr spin (int int) string)
               (lambda (scale k)
                 (let ((x (rat* q (int->rat scale))))
                   (cond ((rat-int? x)
                          (let* ((ds (int->string (rat-num x)))
                                 (ds (if (< (string-length ds) (+ k 1)) (string-append (make-string (- (+ k 1) (string-length ds)) #\0) ds) ds))
                                 (point (- (string-length ds) k)))
                            (string-append (substring ds 0 point) (string-append "." (if (= k 0) "0" (substring ds point (string-length ds)))))))
                         ((> k 40) (rat->string q))
                         (else (go (* scale 10) (+ k 1))))))))
      (go 1 0))))

(define* sexp->string (subr spin (sexp) string)
  (lambda (x)
    (tagcase x
      (sx-sym (s) (if (and (> (string-length s) 1) (char=? (string-ref s 0) #\:)) s (symbol->smt-string s)))
      (sx-num (n) (if (< n 0) (string-append "(- " (string-append (int->string (- 0 n)) ")")) (int->string n)))
      (sx-dec (q) (decimal->string q))
      (sx-bv (v w) (bv->string v w))
      (sx-str (s) (string-append "\"" (string-append (list->string (letrec ((go (subr spin ((listof char acyclic)) (listof char acyclic))
                                                                            (lambda (l) (cond ((null? l) nil)
                                                                                              ((char=? (car l) #\") (cons #\" (cons #\" (go (cdr l)))))
                                                                                              (else (cons (car l) (go (cdr l))))))))
                                                                   (go (string->list s))))
                                                 "\"")))
      (sx-list (l) (if (null? l) "()"
                       (string-append "(" (string-append (sexp->string (car l))
                                                        (string-append (letrec ((go (subr spin (sexps) string)
                                                                                  (lambda (l) (if (null? l) "" (string-append " " (string-append (sexp->string (car l)) (go (cdr l))))))))
                                                                         (go (cdr l)))
                                                                       ")"))))))))
