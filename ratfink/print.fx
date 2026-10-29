;;; print.fx: values as Larceny's `write` and `display` show them -- which
;;; shakedown's labels and reports are made of, and what a checked
;;; program's output is.
;;;
;;; Measured on shakedown's Larceny (2026-10-29):
;;;   - a flonum is its shortest digits that read back, positional when its
;;;     decimal exponent k (x = d.ddd × 10^k) is from -5 to 8 (0.00001,
;;;     123456789.123), else d.ddde<k> (1.0e9, 1.0e-6); a whole one ends .0;
;;;   - (quote x), (quasiquote x), (unquote x), (unquote-splicing x) as 'x,
;;;     `x, ,x and ,@x;
;;;   - a symbol between bars unless it is an identifier (R6RS's, with @ an
;;;     initial): ||, |a b|, |1|, |-x|, |a#|; ->x, @x and ... are not;
;;;   - characters by name (null alarm backspace tab newline return escape
;;;     space delete), #\x1f for other controls and spaces, else as is;
;;;   - strings with \a \b \t \n \r \" \\, and \x1f; for other controls.

(module-parameters ((m-core (load-moduleof "core.fx"))))
(hide (define kit-strings (load-module "../kit/strings.fx"))
      (import kit-strings string-concatenate string-index make-chars))
(hide (define kit-chars (load-module "../kit/chars.fx"))
      (import kit-chars char-name hex-string))

(define hex-digit (subr rf-st (int) string)
  (lambda (d) (char->string (string-ref "0123456789abcdef" d))))

"n copies of c."
(define repeat-char (subr rf-st (int char) string)
  (lambda (n c) (list->string (make-chars n c))))

;;; ------------------------------------------------------------ numbers

"n in base radix (2 to 16)."
(define int->string-radix (subr rf-st (int int) string)
  (lambda (n radix)
    (if (= radix 10) (int->string n)
        (letrec ((go (subr rf-st (int) string)
                   (lambda (n) (if (< n radix) (hex-digit n) (string-append (go (quotient n radix)) (hex-digit (remainder n radix)))))))
          (if (< n 0) (string-append "-" (go (- 0 n))) (go n))))))

"A flonum as Larceny writes it."
(define flonum->string (subr rf-st (f64) string)
  (lambda (x)
    (let ((s (f64->string x)))
      (if (or (f64-nan? x) (f64-infinite? x)) s
          (let* ((neg (char=? (string-ref s 0) #\-))
                 (body (if neg (substring s 1 (string-length s)) s))
                 (dot (string-index body #\.))
                 (int-part (if (bool? dot) body (substring body 0 dot)))
                 (frac-part (if (bool? dot) "" (substring body (+ dot 1) (string-length body))))
                 (all (string-append int-part frac-part))
                 ;; The significant digits, and the exponent of the first.
                 (lead (count-leading #\0 all))
                 (digits0 (substring all lead (string-length all)))
                 (digits (strip-trailing-zeros digits0))
                 (k (- (- (string-length int-part) lead) 1))
                 (sign (if neg "-" "")))
            (cond ((string=? digits "") (string-append sign "0.0"))
                  ((and (>= k -5) (<= k 8))
                   (string-append sign
                                  (if (< k 0)
                                      (string-append "0." (repeat-char (- (- 0 k) 1) #\0) digits)
                                      (let* ((n (string-length digits))
                                             (whole (if (> n (+ k 1)) (substring digits 0 (+ k 1))
                                                        (string-append digits (repeat-char (- (+ k 1) n) #\0))))
                                             (frac (if (> n (+ k 1)) (substring digits (+ k 1) n) "0")))
                                        (string-append whole "." frac)))))
                  (else
                   (string-append sign (substring digits 0 1) "."
                                  (if (> (string-length digits) 1) (substring digits 1 (string-length digits)) "0")
                                  "e" (int->string k)))))))))
(define count-leading (subr rf-st (char string) int)
  (lambda (c s)
    (letrec ((go (subr rf-st (int) int) (lambda (i) (if (and (< i (string-length s)) (char=? (string-ref s i) c)) (go (+ i 1)) i))))
      (go 0))))
(define strip-trailing-zeros (subr rf-st (string) string)
  (lambda (s)
    (letrec ((go (subr rf-st (int) int) (lambda (i) (if (and (> i 0) (char=? (string-ref s (- i 1)) #\0)) (go (- i 1)) i))))
      (substring s 0 (go (string-length s))))))

"A number value as number->string makes it, in base radix."
(define number->string-radix (subr rf-st (rf-value int) string)
  (lambda (v radix)
    (tagcase v
      (int i (int->string-radix i radix))
      (ratio q (string-append (int->string-radix (extract q num) radix) "/" (int->string-radix (extract q den) radix)))
      (real r (flonum->string r))
      (else x ""))))
(define number->string (subr rf-st (rf-value) string) (lambda (v) (number->string-radix v 10)))

;;; ------------------------------------------------------------ characters, strings, symbols

"What follows #\\ as Larceny writes `c`: its R7RS name, x and hex for
another control or space character, else itself."
(define char-text (subr rf-st (char) string)
  (lambda (c)
    (let ((name (char-name c)) (n (char->integer c)))
      (cond ((not (bool? name)) name)
            ((or (< n 32) (and (>= n 128) (<= n 160)) (and (> n 160) (char-whitespace? c))) (string-append "x" (hex-string n)))
            (else (char->string c))))))
(define write-char-string (subr rf-st (char) string) (lambda (c) (string-append "#\\" (char-text c))))

(define string-escape (subr rf-st (char) string)
  (lambda (c)
    (let ((n (char->integer c)))
      (cond ((= n 7) "\\a") ((= n 8) "\\b") ((= n 9) "\\t") ((= n 10) "\\n") ((= n 13) "\\r")
            ((char=? c #\") "\\\"") ((char=? c #\\) "\\\\")
            ((or (< n 32) (and (>= n 127) (<= n 160)) (and (> n 160) (char-whitespace? c))) (string-append "\\x" (hex-string n) ";"))
            (else (char->string c))))))
(define write-string-literal (subr rf-st (string) string)
  (lambda (s)
    (letrec ((go (subr rf-st (int strings) strings)
               (lambda (i acc) (if (< i 0) acc (go (- i 1) (cons (string-escape (string-ref s i)) acc))))))
      (string-append "\"" (string-concatenate (go (- (string-length s) 1) nil)) "\""))))

(define initial? (subr rf-st (char) bool)
  (lambda (c)
    (or (char-alphabetic? c)
        (and (> (char->integer c) 127) (not (char-whitespace? c)))
        (string-has? "!$%&*/:<=>?^_~@" c))))
(define subsequent? (subr rf-st (char) bool)
  (lambda (c) (or (initial? c) (char-numeric? c) (string-has? "+-.@" c))))
(define string-has? (subr rf-st (string char) bool) (lambda (s c) (not (bool? (string-index s c)))))
(define all-subsequent? (subr rf-st (string int) bool)
  (lambda (s i) (or (>= i (string-length s)) (and (subsequent? (string-ref s i)) (all-subsequent? s (+ i 1))))))
"Whether a symbol's name is written as it is."
(define plain-symbol? (subr rf-st (string) bool)
  (lambda (s)
    (let ((n (string-length s)))
      (cond ((= n 0) #f)
            ((or (string=? s "+") (string=? s "-") (string=? s "...")) #t)
            ((and (>= n 2) (char=? (string-ref s 0) #\-) (char=? (string-ref s 1) #\>)) (all-subsequent? s 2))
            ((initial? (string-ref s 0)) (all-subsequent? s 1))
            (else #f)))))
(define write-symbol-string (subr rf-st (symbol) string)
  (lambda (sym)
    (let ((s (symbol->string sym)))
      (if (plain-symbol? s) s
          (letrec ((go (subr rf-st (int strings) strings)
                     (lambda (i acc)
                       (if (< i 0) acc
                           (let ((c (string-ref s i)))
                             (go (- i 1) (cons (cond ((char=? c #\|) "\\|") ((char=? c #\\) "\\\\") (else (char->string c))) acc)))))))
            (string-append "|" (string-concatenate (go (- (string-length s) 1) nil)) "|"))))))

;;; ------------------------------------------------------------ data

"The prefix a two-element list (quote x) and the like is written with, or
\"\"."
(define abbreviation (subr rf-st (rf-value) string)
  (lambda (v)
    (tagcase v
      (pair p
        (if (and (rf-pair? (array-ref p 1)) (rf-null? (rf-cdr (array-ref p 1))))
            (tagcase (array-ref p 0)
              (sym s (cond ((eq? s 'quote) "'") ((eq? s 'quasiquote) "`") ((eq? s 'unquote) ",")
                           ((eq? s 'unquote-splicing) ",@") (else "")))
              (else x ""))
            ""))
      (else x ""))))

"v's text, as write (display? false) or display writes it; `other` gives
the text of what is not data (a term, a procedure, shakedown's unspecified
value, …). abbreviate?: (quote x) as 'x, as Larceny's write; shakedown's
show writes pairs itself, without."
(define datum-text (subr rf-eff (rf-value bool bool (subr rf-eff (rf-value) string)) string)
  (lambda (v display? abbreviate? other)
    (letrec ((walk (subr rf-eff (rf-value strings) strings)
               ;; v's text, before acc.
               (lambda (v acc)
                 (tagcase v
                   (null u (cons "()" acc))
                   (bool b (cons (if b "#t" "#f") acc))
                   (int i (cons (int->string i) acc))
                   (ratio q (cons (number->string v) acc))
                   (real r (cons (flonum->string r) acc))
                   (char c (cons (if display? (char->string c) (write-char-string c)) acc))
                   (str s (cons (if display? s (write-string-literal s)) acc))
                   (sym s (cons (if display? (symbol->string s) (write-symbol-string s)) acc))
                   (eof u (cons "#<EOF>" acc))
                   (pair p
                     (let ((prefix (if abbreviate? (abbreviation v) "")))
                       (if (not (string=? prefix ""))
                           (cons prefix (walk (rf-cadr v) acc))
                           (cons "(" (walk (array-ref p 0) (tail (array-ref p 1) acc))))))
                   (vec a (cons "#(" (elements a 0 acc)))
                   (else x (cons (other v) acc)))))
             ;; The rest of a list after its first element, and ")".
             (tail (subr rf-eff (rf-value strings) strings)
               (lambda (v acc)
                 (tagcase v
                   (null u (cons ")" acc))
                   (pair p (cons " " (walk (array-ref p 0) (tail (array-ref p 1) acc))))
                   (else x (cons " . " (walk v (cons ")" acc)))))))
             (elements (subr rf-eff (rf-slots int strings) strings)
               (lambda (a i acc)
                 (cond ((>= i (array-length a)) (cons ")" acc))
                       ((= i 0) (walk (array-ref a 0) (elements a 1 acc)))
                       (else (cons " " (walk (array-ref a i) (elements a (+ i 1) acc))))))))
      (string-concatenate (walk v nil)))))

"How Larceny writes what is not data in shakedown: shakedown's own records
(a term, a union, a closure, a primitive, …), by their record types' names."
(define larceny-record-text (subr rf-st (rf-value) string)
  (lambda (v)
    (tagcase v
      (term t "#<record term>") (choice c "#<record symbol-choice>") (union u "#<record union>")
      (multiple m "#<record multiple>") (closure c "#<record closure>") (prim p "#<record primitive>")
      (rtd r "#<record record-type>") (inst i "#<record instance>") (port p "#<record port>")
      (table t "#<record table>") (unspec u "#<record unspecified-type>") (unbound u "#<record unbound-type>")
      (unassigned u "#<record unassigned-type>") (deleted u "#<record deleted-type>") (frame f "#<frame>")
      (else x "#<value>"))))
