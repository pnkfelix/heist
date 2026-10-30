;;; strings.fx: kit's string procedures -- SRFI 13's and SRFI 130's that
;;; Heist's programs each wrote, and a string's written form (R7RS's
;;; `write`). Fixpt's own: `string-append`, `substring`, `string-search`,
;;; `string-copy`, `string->list`, `list->string`, `string-downcase`, the
;;; comparisons.
;;;
;;; A list of strings given is `(listof string (acyclic p))`, at any place;
;;; one made is at a region `r` the caller chooses (`lists.fx` says why). An
;;; index not found is #f.
;;;
;;; A module file of no state: (define strings (load-module "kit/strings.fx")).

"Whether `s` begins with `prefix`."
(define string-prefix? (subr pure (string string) bool)
  (lambda (prefix s)
    (and (<= (string-length prefix) (string-length s))
         (string=? (substring s 0 (string-length prefix)) prefix))))

"Whether `s` ends with `suffix`."
(define string-suffix? (subr pure (string string) bool)
  (lambda (suffix s)
    (let ((n (string-length s)) (k (string-length suffix)))
      (and (<= k n) (string=? (substring s (- n k) n) suffix)))))

"The index of the first `c` in `s` at or after `start`, or #f."
(define string-index-from (subr pure (string char int) (union false nat))
  (lambda (s c start)
    (let ((n (string-length s)))
      (letrec ((go (subr pure (int) (union false nat))
                 (lambda (i) (cond ((>= i n) #f)
                                   ((char=? (string-ref s i) c) (confirm-nat i (k k) #f))
                                   (else (go (+ i 1)))))))
        (go (if (< start 0) 0 start))))))

"The index of the first `c` in `s`, or #f."
(define string-index (subr pure (string char) (union false nat))
  (lambda (s c) (string-index-from s c 0)))

"The strings of `ss`, one after another."
(define string-concatenate
  (poly ((p place)) (subr (read (acyclic p)) ((listof string (acyclic p))) string))
  (plambda ((p place))
    (lambda (ss) (apply string-append ss))))

"The characters of `l`, last first, as a string (SRFI 13's
reverse-list->string): for a string built a character at a time on a list."
(define reverse-list->string
  (poly ((p place)) (subr (read (acyclic p)) ((listof char (acyclic p))) string))
  (plambda ((p place))
    (lambda (l) (list->string (the (listof char acyclic) (reverse l))))))

"The strings of `ss` with `sep` between each two (SRFI 130's string-join,
its default grammar)."
(define string-join
  (poly ((p place)) (subr (read (acyclic p)) ((listof string (acyclic p)) string) string))
  (plambda ((p place))
    (lambda (ss sep)
      (letrec ((go (subr (read (acyclic p)) ((listof string (acyclic p))) (listof string acyclic))
                 (lambda (ss) (if (null? ss) nil
                                  (the (listof string acyclic) (cons sep (the (listof string acyclic) (cons (car ss) (go (cdr ss))))))))))
        (if (null? ss) "" (apply string-append (the (listof string acyclic) (cons (car ss) (go (cdr ss))))))))))

"The fields of `s` between the `c`s, empty ones too: \"a,,b\" is \"a\", \"\"
and \"b\"; \"\" is one empty field."
(define string-split
  (poly ((r region)) (subr (alloc r) (string char) (listof string r)))
  (plambda ((r region))
    (lambda (s c)
      (let ((n (string-length s)))
        (letrec ((go (subr (alloc r) (int int) (listof string r))
                   ;; The fields from `start`, which `i` is scanning.
                   (lambda (start i)
                     (cond ((>= i n) (cons (substring s start n) nil))
                           ((char=? (string-ref s i) c) (cons (substring s start i) (go (+ i 1) (+ i 1))))
                           (else (go start (+ i 1)))))))
          (go 0 0))))))

"The words of `s`: its runs of what is not whitespace (SRFI 13's
string-tokenize, of whitespace)."
(define string-tokenize
  (poly ((r region)) (subr (alloc r) (string) (listof string r)))
  (plambda ((r region))
    (lambda (s)
      (let ((n (string-length s)))
        (letrec ((go (subr (alloc r) (int int) (listof string r))
                   ;; A word begins at `start` if start < i.
                   (lambda (start i)
                     (cond ((>= i n) (if (< start i) (cons (substring s start n) nil) nil))
                           ((char-whitespace? (string-ref s i))
                            (if (< start i) (cons (substring s start i) (go (+ i 1) (+ i 1))) (go (+ i 1) (+ i 1))))
                           (else (go start (+ i 1)))))))
          (go 0 0))))))

"`s` made `n` long (SRFI 13's string-pad-right): `c`s added at its right,
or its first `n` characters kept."
(define string-pad-right (subr pure (string int char) string)
  (lambda (s n c)
    (let ((k (string-length s)))
      (if (>= k n) (substring s 0 (if (< n 0) 0 n))
          (string-append s (list->string (the (listof char acyclic) (make-chars (- n k) c))))))))

"`s` made `n` long (SRFI 13's string-pad): `c`s added at its left, or its
last `n` characters kept."
(define string-pad (subr pure (string int char) string)
  (lambda (s n c)
    (let ((k (string-length s)))
      (if (>= k n) (substring s (- k (if (< n 0) 0 n)) k)
          (string-append (list->string (the (listof char acyclic) (make-chars (- n k) c))) s)))))

"`k` `c`s."
(define make-chars (subr pure (int char) (listof char acyclic))
  (lambda (k c) (if (<= k 0) nil (the (listof char acyclic) (cons c (make-chars (- k 1) c))))))

"How `write` writes character `c` inside a string literal."
(define string-escape (subr pure (char) string)
  (lambda (c)
    (let ((k (char->integer c)))
      (cond ((char=? c #\\) "\\\\") ((char=? c #\") "\\\"")
            ((= k 7) "\\a") ((= k 8) "\\b") ((= k 9) "\\t") ((= k 10) "\\n") ((= k 13) "\\r")
            ((or (< k 32) (= k 127)) (string-append "\\x" (hex-digits k) ";"))
            (else (char->string c))))))
(define hex-digits (subr pure (int) string)
  (lambda (k) (string-append (if (>= k 16) (char->string (string-ref "0123456789abcdef" (quotient k 16))) "")
                             (char->string (string-ref "0123456789abcdef" (remainder k 16))))))

"`s` as R7RS's `write` writes it: in double quotes, with \\\\, \\\", \\a, \\b,
\\t, \\n, \\r, and \\x..; for another control character."
(define written-string (subr pure (string) string)
  (lambda (s)
    (letrec ((go (subr pure (int (listof string acyclic)) (listof string acyclic))
               ;; From the end, so the pieces come out in order.
               (lambda (i acc) (if (< i 0) acc (go (- i 1) (the (listof string acyclic) (cons (string-escape (string-ref s i)) acc)))))))
      (string-append "\"" (apply string-append (go (- (string-length s) 1) nil)) "\""))))
