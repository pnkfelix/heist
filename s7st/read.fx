;;; read.fx: R7RS's external representations, read from a string.
;;;
;;; Each list read has its span kept in its first pair, and each item's in
;;; the pair that holds it (value.fx's `s7-src`),
;;; so that the expander can say where a form is, and an analysis where
;;; each node came from. What is read is mutable, as Scheme's data is.

"Where the item pair `p` holds was read, or `default`."
(define* s7-item-span (subr pure (s7-pair s7-span) s7-span)
  (lambda (p default) (tagcase (extract p src) (read r (extract r item)) (none u default))))
"The span of datum `v`, if it is a list read."
(define* s7-span-of (subr pure (s7-value) s7-span)
  (lambda (v)
    (tagcase v
      (pair p (tagcase (extract p src) (read r (extract r list)) (none u s7-no-span)))
      (else y s7-no-span))))

"What reading from a place gives: a datum, and where it ended; nothing but
space and comments; a datum not ended when the text is; or an error, and
where."
(define-type s7-read
  (sumof (datum (productof (value s7-value) (start int) (end int)))
         (none unit)
         (incomplete unit)
         (bad (productof (message string) (at int)))))

(define* s7-delimiter? (subr pure (char) bool)
  (lambda (c) (or (char-whitespace? c) (char-in? c "()\";|"))))

"The value of digits `s` in `radix`, or -1 if one is no digit of it (or
there are none). Any length: an int is a bignum."
(define* s7-parse-digits (subr spin (string int) int)
  (lambda (s radix)
    (let ((n (string-length s)))
      (letrec ((digit (subr spin (char) int)
                 (lambda (c)
                   (let ((d (cond ((char-numeric? c) (- (char->integer c) 48))
                                  ((and (char>=? c #\a) (char<=? c #\z)) (+ 10 (- (char->integer c) 97)))
                                  ((and (char>=? c #\A) (char<=? c #\Z)) (+ 10 (- (char->integer c) 65)))
                                  (else 99))))
                     (if (< d radix) d -1))))
               (go (subr spin (int int) int)
                 (lambda (i acc)
                   (if (>= i n) acc
                       (let ((d (digit (string-ref s i))))
                         (if (< d 0) -1 (go (+ i 1) (+ (* acc radix) d))))))))
        (if (= n 0) -1 (go 0 0))))))

"Whether `s` is an unsigned decimal: digits with at most one point, at
least one digit, then perhaps an exponent."
(define* s7-decimal? (subr spin (string) bool)
  (lambda (s)
    (let ((n (string-length s)))
      (letrec ((mantissa (subr spin (int bool bool) bool)
                 ;; From `i`, a point seen, a digit seen.
                 (lambda (i point digit)
                   (cond ((>= i n) digit)
                         ((char-numeric? (string-ref s i)) (mantissa (+ i 1) point #t))
                         ((and (char=? (string-ref s i) #\.) (not point)) (mantissa (+ i 1) #t digit))
                         ((and digit (char-in? (string-ref s i) "eE")) (exponent (+ i 1) #t))
                         (else #f))))
               (exponent (subr spin (int bool) bool)
                 (lambda (i first)
                   (cond ((>= i n) (not first))
                         ((and first (char-in? (string-ref s i) "+-") (< (+ i 1) n)) (exponent (+ i 1) #f))
                         ((char-numeric? (string-ref s i)) (exponent (+ i 1) #f))
                         (else #f)))))
        (mantissa 0 #f #f)))))


"Character `name`'s character (`#\\name`), or #f."
(define* s7-char-named (subr spin (string) (union false char))
  (lambda (name)
    (let ((n (string-length name)))
      (cond ((= n 1) (string-ref name 0))
            ((string=? name "space") #\space)
            ((string=? name "newline") #\newline)
            ((string=? name "linefeed") #\newline)
            ((string=? name "tab") #\tab)
            ((string=? name "return") (integer->char 13))
            ((or (string=? name "null") (string=? name "nul")) (integer->char 0))
            ((string=? name "alarm") (integer->char 7))
            ((string=? name "backspace") (integer->char 8))
            ((or (string=? name "delete") (string=? name "rubout")) (integer->char 127))
            ((or (string=? name "escape") (string=? name "altmode")) (integer->char 27))
            ((and (> n 1) (char=? (string-ref name 0) #\x))
             (let ((code (s7-parse-digits (substring name 1 n) 16)))
               (if (and (>= code 0) (< code 1114112) (not (and (>= code 55296) (< code 57344))))
                   (integer->char code)
                   #f)))
            (else #f)))))

"Decimal `s` (unsigned: digits, a point, an exponent) exactly: `1.1` is
11/10."
(define* s7-exact-decimal (subr spin (string) s7-value)
  (lambda (s)
    (let* ((e (let ((a (string-search s "e" 0)) (b (string-search s "E" 0))) (if (>= a 0) a b)))
           (mant (if (>= e 0) (substring s 0 e) s))
           (expo (if (>= e 0)
                     (let* ((x (substring s (+ e 1) (string-length s)))
                            (neg (and (> (string-length x) 0) (char=? (string-ref x 0) #\-)))
                            (digits (if (and (> (string-length x) 0) (char-in? (string-ref x 0) "+-")) (substring x 1 (string-length x)) x))
                            (v (s7-parse-digits digits 10)))
                       (if neg (- 0 v) v))
                     0))
           (pt (string-search mant "." 0))
           (before (if (>= pt 0) (substring mant 0 pt) mant))
           (after (if (>= pt 0) (substring mant (+ pt 1) (string-length mant)) ""))
           (m (s7-parse-digits (string-append (if (string=? before "") "0" before) after) 10))
           (scale (- expo (string-length after)))
           (ten (lambda ((k int)) (letrec ((go (subr spin (int int) int) (lambda (k acc) (if (<= k 0) acc (go (- k 1) (* acc 10)))))) (go k 1)))))
      (if (>= scale 0) (sum int (* m (ten scale))) (s7-make-ratio m (ten (- 0 scale)))))))

"Number `s`, in `radix`, or #f: an integer, a ratio, a decimal, or an
infinity or NaN; each signed, and perhaps prefixed (`#x`, `#e`, …)."
(define* s7-parse-number (subr (maxeff spin (alloc @sc) (read @sc)) (string int) (union false s7-value))
  (lambda (s radix)
    (let ((n (string-length s)))
      (cond ((= n 0) #f)
            ((and (>= n 2) (char=? (string-ref s 0) #\#))
             (let ((c (char-downcase (string-ref s 1))) (rest (substring s 2 n)))
               (cond ((char=? c #\x) (s7-parse-number rest 16))
                     ((char=? c #\b) (s7-parse-number rest 2))
                     ((char=? c #\o) (s7-parse-number rest 8))
                     ((char=? c #\d) (s7-parse-number rest 10))
                     ((char=? c #\e)
                      (let* ((neg (and (> (string-length rest) 0) (char=? (string-ref rest 0) #\-)))
                             (body (if (and (> (string-length rest) 0) (char-in? (string-ref rest 0) "+-")) (substring rest 1 (string-length rest)) rest)))
                        (if (and (= radix 10) (s7-decimal? body) (< (s7-parse-digits body 10) 0))
                            (let ((v (s7-exact-decimal body)))
                              (if neg (tagcase v (int i (sum int (- 0 i))) (ratio q (s7-make-ratio (- 0 (extract q num)) (extract q den))) (else y v)) v))
                            (let ((v (s7-parse-number rest radix)))
                              (typecase v
                                (bool b #f)
                                (else y (tagcase y
                                          (real r (if (f64-finite? r) (s7-f64->exact r) #f))
                                          (else z y))))))))
                     ((char=? c #\i)
                      (let ((v (s7-parse-number rest radix)))
                        (typecase v
                          (bool b #f)
                          (else y (tagcase y
                                    (int i (sum real (int->f64 i)))
                                    (ratio q (sum real (ratio->f64 (extract q num) (extract q den))))
                                    (else z y))))))
                     (else #f))))
            ((string=? s "+inf.0") (sum real (f64/ 1.0 0.0)))
            ((string=? s "-inf.0") (sum real (f64/ -1.0 0.0)))
            ((or (string=? s "+nan.0") (string=? s "-nan.0")) (sum real (f64/ 0.0 0.0)))
            (else
             (let* ((neg (char=? (string-ref s 0) #\-))
                    (signed (or neg (char=? (string-ref s 0) #\+)))
                    (body (if signed (substring s 1 n) s))
                    (slash (string-search body "/" 0)))
               (cond ((string=? body "") #f)
                     ((>= slash 0)
                      (let ((a (s7-parse-digits (substring body 0 slash) radix))
                            (b (s7-parse-digits (substring body (+ slash 1) (string-length body)) radix)))
                        (cond ((or (< a 0) (<= b 0)) #f)
                              (else (s7-make-ratio (if neg (- 0 a) a) b)))))
                     (else
                      (let ((i (s7-parse-digits body radix)))
                        (cond ((>= i 0) (sum int (if neg (- 0 i) i)))
                              ((not (= radix 10)) #f)
                              ;; A decimal: digits, a point, an exponent, and nothing else.
                              ((not (s7-decimal? body)) #f)
                              (else
                               (let ((got (the (listof f64 @sc) (string->f64 (if neg (string-append "-" body) body)))))
                                 (if (null? got) #f (sum real (car got)))))))))))))))

"Whether symbols and character names read are case folded (`#!fold-case`,
until `#!no-fold-case`; and what `include-ci` reads). A read of a whole
text (`s7-read-all`) begins without."
(define s7-fold-case (ref bool @sc) (new #f))

"A datum label being read (`#n=`): its number, what stands for it until
its datum is read, and then that datum."
(define-type s7-label (productof (n int) (placeholder s7-value) (value (ref s7-value @sc))))
"Placeholder `old` replaced by `new` throughout `v`'s pairs and vectors,
each visited once (it may have cycles already)."
(define* s7-patch-label! (subr (maxeff spin (read @sc) (write @sc) (alloc @sc)) (s7-value s7-value s7-value) unit)
  (lambda (v old new)
    (let ((pairs (the (eqtable (ref s7-value @sc) bool @sc @sc) (make-eqtable (ref-identity))))
          (vecs (the (eqtable (arrayof s7-value @sc) bool @sc @sc) (make-eqtable (array-identity)))))
      (letrec ((fix (subr (maxeff spin (read @sc) (write @sc) (alloc @sc)) (s7-value) s7-value)
                 ;; `x`, or `new` if it is the placeholder; what it holds patched.
                 (lambda (x)
                   (if (s7-same-pair? x old) new
                       (begin
                         (tagcase x
                           (pair p (if (eqtable-has? pairs (extract p car)) #u
                                       (begin (eqtable-set! pairs (extract p car) #t)
                                         (set (extract p car) (fix (get (extract p car))))
                                         (set (extract p cdr) (fix (get (extract p cdr)))))))
                           (vec a (if (eqtable-has? vecs a) #u
                                      (begin (eqtable-set! vecs a #t)
                                        (letrec ((each (subr (maxeff spin (read @sc) (write @sc) (alloc @sc)) (int) unit)
                                                   (lambda (i) (if (>= i (array-length a)) #u
                                                                   (begin (array-set! a i (fix (array-ref a i))) (each (+ i 1)))))))
                                          (each 0)))))
                           (else y #u))
                         x)))))
        (begin (fix v) #u)))))

"Read one datum of `text` from `i`, in `file` (for spans)."
(define* s7-read-at (subr s7-read-eff (string int string) s7-read)
  (lambda (text i file)
    (let ((n (string-length text))
          (labels (the (ref (listof s7-label acyclic) @sc) (new nil))))
      (letrec ((bad (subr s7-read-eff (string int) s7-read)
                 (lambda (m at) (sum bad (product (message m) (at at)))))
               ;; Past space and comments from `i`: where a datum may start, or a read's error.
               (skip (subr s7-read-eff (int) (sumof (at int) (err s7-read)))
                 (lambda (i)
                   (cond ((>= i n) (sum at i))
                         ((char-whitespace? (string-ref text i)) (skip (+ i 1)))
                         ((char=? (string-ref text i) #\;)
                          ;; To the line's end: a newline, or a return.
                          (letrec ((eol (subr s7-read-eff (int) int)
                                     (lambda (j) (cond ((>= j n) n) ((char-in? (string-ref text j) "\n\r") j) (else (eol (+ j 1)))))))
                            (let ((e (eol i))) (if (>= e n) (sum at n) (skip (+ e 1))))))
                         ((and (char=? (string-ref text i) #\#) (< (+ i 1) n) (char=? (string-ref text (+ i 1)) #\|))
                          (block (+ i 2) 1))
                         ((and (char=? (string-ref text i) #\#) (< (+ i 1) n) (char=? (string-ref text (+ i 1)) #\;))
                          ;; A datum commented out.
                          (tagcase (datum (+ i 2))
                            (datum d (skip (extract d end)))
                            (none u (sum err (bad "#; with no datum after it" i)))
                            (else y (sum err y))))
                         ((and (char=? (string-ref text i) #\#) (< (+ i 1) n) (char=? (string-ref text (+ i 1)) #\!))
                          ;; A directive: #!fold-case, #!no-fold-case; others skipped.
                          (let* ((e (token-end (+ i 2))) (d (substring text (+ i 2) e)))
                            (begin
                              (cond ((string=? d "fold-case") (set s7-fold-case #t))
                                    ((string=? d "no-fold-case") (set s7-fold-case #f))
                                    (else #u))
                              (skip e))))
                         (else (sum at i)))))
               ;; A block comment's text from `i`, `depth` deep.
               (block (subr s7-read-eff (int int) (sumof (at int) (err s7-read)))
                 (lambda (i depth)
                   (cond ((>= (+ i 1) n) (sum err (sum incomplete #u)))
                         ((and (char=? (string-ref text i) #\|) (char=? (string-ref text (+ i 1)) #\#))
                          (if (= depth 1) (skip (+ i 2)) (block (+ i 2) (- depth 1))))
                         ((and (char=? (string-ref text i) #\#) (char=? (string-ref text (+ i 1)) #\|))
                          (block (+ i 2) (+ depth 1)))
                         (else (block (+ i 1) depth)))))
               (token-end (subr s7-read-eff (int) int)
                 (lambda (i) (if (or (>= i n) (s7-delimiter? (string-ref text i))) i (token-end (+ i 1)))))
               (done (subr s7-read-eff (s7-value int int) s7-read)
                 (lambda (v a e) (sum datum (product (value v) (start a) (end e)))))
               ;; The datum from `i`.
               (datum (subr s7-read-eff (int) s7-read)
                 (lambda (i)
                   (tagcase (skip i)
                     (err r r)
                     (at a
                       (if (>= a n) (sum none #u)
                           (let ((c (string-ref text a)))
                             (cond ((or (char=? c #\() (char=? c #\[)) (items (+ a 1) a (if (char=? c #\() #\) #\]) nil nil))
                                   ((or (char=? c #\)) (char=? c #\])) (bad "unexpected close parenthesis" a))
                                   ((char=? c #\') (abbrev a "quote"))
                                   ((char=? c #\`) (abbrev a "quasiquote"))
                                   ((char=? c #\,)
                                    (if (and (< (+ a 1) n) (char=? (string-ref text (+ a 1)) #\@))
                                        (abbrev (+ a 1) "unquote-splicing")
                                        (abbrev a "unquote")))
                                   ((char=? c #\") (str (+ a 1) a nil))
                                   ((char=? c #\|) (bar (+ a 1) a nil))
                                   ((char=? c #\#) (hash a))
                                   (else (atom a)))))))))
               ;; `'x` and its kin, the mark ending at `a`.
               (abbrev (subr s7-read-eff (int string) s7-read)
                 (lambda (a name)
                   (tagcase (datum (+ a 1))
                     (datum d (done (build (list (s7-symbol name) (extract d value))
                                           (list (product (file file) (start a) (end (extract d start)))
                                                 (product (file file) (start (extract d start)) (end (extract d end))))
                                           s7-nil a (extract d end))
                                    a (extract d end)))
                     (none u (sum incomplete #u))
                     (else y y))))
               ;; Items `vs` (read at `spans`), then `tail`, as pairs the reader
               ;; made: the first beginning a list read from `a` to `e`.
               (build (subr s7-read-eff (s7-values (listof s7-span acyclic) s7-value int int) s7-value)
                 (lambda (vs spans tail a e)
                   (letrec ((go (subr s7-read-eff (s7-values (listof s7-span acyclic) bool) s7-value)
                              (lambda (vs spans first)
                                (if (null? vs) tail
                                    (s7-cons-read (car vs) (go (cdr vs) (if (pair? spans) (cdr spans) nil) #f)
                                                  (if first (product (file file) (start a) (end e)) s7-no-span)
                                                  (if (pair? spans) (car spans) s7-no-span))))))
                     (go vs spans #t))))
               ;; A list's items from `i`, its open at `open`, closed by `close`; read so far, last first.
               (items (subr s7-read-eff (int int char s7-values (listof s7-span acyclic)) s7-read)
                 ;; `spans`: where each of `acc` was read, last first.
                 (lambda (i open close acc spans)
                   (tagcase (skip i)
                     (err r r)
                     (at a
                       (cond ((>= a n) (sum incomplete #u))
                             ((or (char=? (string-ref text a) #\)) (char=? (string-ref text a) #\]))
                              (if (char=? (string-ref text a) close)
                                  (done (build (reverse acc) (reverse spans) s7-nil open (+ a 1)) open (+ a 1))
                                  (bad "mismatched close parenthesis" a)))
                             ((and (char=? (string-ref text a) #\.) (pair? acc)
                                   (or (>= (+ a 1) n) (s7-delimiter? (string-ref text (+ a 1)))))
                              (tagcase (datum (+ a 1))
                                (datum d
                                  (tagcase (skip (extract d end))
                                    (err r r)
                                    (at e (cond ((>= e n) (sum incomplete #u))
                                                ((char=? (string-ref text e) close)
                                                 (done (build (reverse acc) (reverse spans) (extract d value) open (+ e 1)) open (+ e 1)))
                                                (else (bad "more than one datum after a dot" e))))))
                                (none u (sum incomplete #u))
                                (else y y)))
                             (else
                              (tagcase (datum a)
                                (datum d (items (extract d end) open close (cons (extract d value) acc)
                                                (cons (product (file file) (start (extract d start)) (end (extract d end))) spans)))
                                (none u (sum incomplete #u))
                                (else y y))))))))
               ;; A string's characters from `i`, last first.
               (str (subr s7-read-eff (int int (listof char acyclic)) s7-read)
                 (lambda (i start acc)
                   (cond ((>= i n) (sum incomplete #u))
                         ((char=? (string-ref text i) #\") (done (s7-string (list->string (reverse acc))) start (+ i 1)))
                         ((char=? (string-ref text i) #\\)
                          (tagcase (escape (+ i 1) #\")
                            (ch c (str (extract c next) start (if (extract c skip) acc (cons (extract c char) acc))))
                            (err r r)))
                         (else (str (+ i 1) start (cons (string-ref text i) acc))))))
               ;; `|sym bol|`'s characters from `i`.
               (bar (subr s7-read-eff (int int (listof char acyclic)) s7-read)
                 (lambda (i start acc)
                   (cond ((>= i n) (sum incomplete #u))
                         ((char=? (string-ref text i) #\|) (done (s7-symbol (list->string (reverse acc))) start (+ i 1)))
                         ((char=? (string-ref text i) #\\)
                          (tagcase (escape (+ i 1) #\|)
                            (ch c (bar (extract c next) start (if (extract c skip) acc (cons (extract c char) acc))))
                            (err r r)))
                         (else (bar (+ i 1) start (cons (string-ref text i) acc))))))
               ;; The escape after a backslash at `i - 1`, in a string closed by `close`.
               (escape (subr s7-read-eff (int char)
                             (sumof (ch (productof (char char) (next int) (skip bool))) (err s7-read)))
                 (lambda (i close)
                   (if (>= i n) (sum err (sum incomplete #u))
                       (let ((c (string-ref text i))
                             (one (lambda ((c char)) (sum ch (product (char c) (next (+ i 1)) (skip #f))))))
                         (cond ((char=? c #\n) (one #\newline))
                               ((char=? c #\t) (one #\tab))
                               ((char=? c #\r) (one (integer->char 13)))
                               ((char=? c #\a) (one (integer->char 7)))
                               ((char=? c #\b) (one (integer->char 8)))
                               ((char=? c #\0) (one (integer->char 0)))
                               ((or (char=? c #\\) (char=? c close) (char=? c #\") (char=? c #\|)) (one c))
                               ((char=? c #\x)
                                (let ((semi (string-search text ";" i)))
                                  (if (< semi 0) (sum err (sum incomplete #u))
                                      (typecase (s7-char-named (substring text i semi))
                                        (char ch (sum ch (product (char ch) (next (+ semi 1)) (skip #f))))
                                        (else y (sum err (bad "bad \\x escape" i)))))))
                               ((or (char=? c #\newline) (char=? c #\space) (char=? c #\tab))
                                ;; A line ended by a backslash: it, and the next's leading space, gone.
                                (let ((e (string-search text "\n" i)))
                                  (if (< e 0) (sum err (bad "backslash at the end of the text" i))
                                      (letrec ((lead (subr spin (int) int)
                                                 (lambda (j) (if (and (< j n) (char-in? (string-ref text j) " \t")) (lead (+ j 1)) j))))
                                        (sum ch (product (char #\space) (next (lead (+ e 1))) (skip #t)))))))
                               (else (sum err (bad (string-append "unknown escape \\" (char->string c)) i))))))))
               ;; What `#` at `a` starts.
               (hash (subr s7-read-eff (int) s7-read)
                 (lambda (a)
                   (if (>= (+ a 1) n) (sum incomplete #u)
                       (let ((c (string-ref text (+ a 1))))
                         (cond ((char-numeric? c) (label a))
                               ((char=? c #\()
                                (tagcase (items (+ a 2) a #\) nil nil)
                                  (datum d (tagcase (s7-list-items (extract d value))
                                             (some l (done (sum vec (list->array l)) a (extract d end)))
                                             (none u (bad "a vector may not be dotted" a))))
                                  (else y y)))
                               ((char=? c #\\)
                                ;; A character: the one after, and any letters after it.
                                (if (>= (+ a 2) n) (sum incomplete #u)
                                    (let* ((e (token-end (+ a 3)))
                                           (raw (substring text (+ a 2) e))
                                           (name (if (and (get s7-fold-case) (> (string-length raw) 1)) (string-downcase raw) raw)))
                                      (typecase (s7-char-named name)
                                        (char ch (done (sum char ch) a e))
                                        (else y (bad (string-append "unknown character #\\" name) a))))))
                               ((and (char=? c #\u) (< (+ a 3) n) (string=? (substring text (+ a 1) (+ a 4)) "u8("))
                                (tagcase (items (+ a 4) a #\) nil nil)
                                  (datum d (tagcase (s7-list-items (extract d value))
                                             (some l (if (every (lambda ((v s7-value)) (tagcase v (int i (and (>= i 0) (< i 256))) (else y #f))) l)
                                                         (done (sum bytes (list->array (map (lambda ((v s7-value)) (tagcase v (int i i) (else y 0))) l))) a (extract d end))
                                                         (bad "a bytevector's items are 0 to 255" a)))
                                             (none u (bad "a bytevector may not be dotted" a))))
                                  (else y y)))
                               (else
                                (let* ((e (token-end (+ a 1))) (word (substring text a e)))
                                  (cond ((or (string=? (string-downcase word) "#t") (string=? (string-downcase word) "#true")) (done s7-true a e))
                                        ((or (string=? (string-downcase word) "#f") (string=? (string-downcase word) "#false")) (done s7-false a e))
                                        (else
                                         (typecase (s7-parse-number word 10)
                                           (bool b (bad (string-append "unknown syntax " word) a))
                                           (else v (done v a e))))))))))))
               ;; `#n=datum` or `#n#`, at `a`.
               (label (subr s7-read-eff (int) s7-read)
                 (lambda (a)
                   (letrec ((digits (subr s7-read-eff (int) int) (lambda (j) (if (and (< j n) (char-numeric? (string-ref text j))) (digits (+ j 1)) j))))
                     (let* ((e (digits (+ a 1)))
                            (k (s7-parse-digits (substring text (+ a 1) e) 10)))
                       (cond ((>= e n) (sum incomplete #u))
                             ((char=? (string-ref text e) #\=)
                              (let* ((ph (s7-cons (s7-symbol " label") s7-nil))
                                     (cell (the (ref s7-value @sc) (new ph))))
                                (begin
                                  (set labels (cons (product (n k) (placeholder ph) (value cell)) (get labels)))
                                  (tagcase (datum (+ e 1))
                                    (datum d (begin (set cell (extract d value))
                                               (s7-patch-label! (extract d value) ph (extract d value))
                                               (done (extract d value) a (extract d end))))
                                    (none u (sum incomplete #u))
                                    (else y y)))))
                             ((char=? (string-ref text e) #\#)
                              (letrec ((find (subr s7-read-eff ((listof s7-label acyclic)) s7-read)
                                         (lambda (l) (cond ((null? l) (bad (string-append "no datum labelled #" (int->string k) "=") a))
                                                           ((= (extract (car l) n) k) (done (get (extract (car l) value)) a (+ e 1)))
                                                           (else (find (cdr l)))))))
                                (find (get labels))))
                             (else (bad "a datum label is #n= or #n#" a)))))))
               (atom (subr s7-read-eff (int) s7-read)
                 (lambda (a)
                   (let* ((e (token-end a)) (word (substring text a e)))
                     (typecase (s7-parse-number word 10)
                       (bool b (done (s7-symbol (if (get s7-fold-case) (string-downcase word) word)) a e))
                       (else v (done v a e)))))))
        (datum i)))))

"As `s7-read-all`, case folded from the start if `fold`."
(define* s7-read-all-folding (subr (maxeff spin (read @sc) (write @sc) (alloc @sc)) (string string bool)
                                   (sumof (data s7-values) (stop s7-read)))
  (lambda (text file fold)
    (letrec ((go (subr (maxeff spin (read @globals) (read @sc) (write @sc) (alloc @sc)) (int s7-values) (sumof (data s7-values) (stop s7-read)))
               (lambda (i acc)
                 (tagcase (s7-read-at text i file)
                   (datum d (go (extract d end) (cons (extract d value) acc)))
                   (none u (sum data (reverse acc)))
                   (else y (sum stop y))))))
      (begin (set s7-fold-case fold) (go 0 nil)))))
"Every datum of `text`, in order: all of them, or the first error (or
`incomplete`)."
(define* s7-read-all (subr (maxeff spin (read @sc) (write @sc) (alloc @sc)) (string string)
                           (sumof (data s7-values) (stop s7-read)))
  (lambda (text file) (s7-read-all-folding text file #f)))

