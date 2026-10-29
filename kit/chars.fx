;;; chars.fx: kit's character procedures -- R7RS's digit-value, its
;;; lexical syntax's delimiters and character names, and a character's
;;; written form. Fixpt's own: `char-numeric?`, `char-alphabetic?`,
;;; `char-whitespace?`, `char-upcase`, `char-downcase`, the comparisons.
;;;
;;; R7RS's forms, not a host's: a Scheme that writes characters its own way
;;; (Larceny's or s7's names and escapes) keeps its own.
;;;
;;; A module file of no state: (define chars (load-module "kit/chars.fx")).

"Where each block of Unicode's decimal digits (Nd) begins: ten code
points, 0 to 9 (Unicode 16; s7st's table)."
(define digit-zeros (listof int acyclic)
  (list 48 1632 1776 1984 2406 2534 2662 2790 2918 3046
        3174 3302 3430 3558 3664 3792 3872 4160 4240 6112
        6160 6470 6608 6784 6800 6992 7088 7232 7248 42528
        43216 43264 43472 43504 43600 44016 65296 66720 68912 68928
        69734 69872 69942 70096 70384 70736 70864 71248 71360 71376
        71472 71904 72016 72688 72784 73040 73120 73552 90416 92768
        92864 93008 93552 118000 120782 120792 120802 120812 120822 123200
        123632 124144 124401 125264 130032))

"R7RS's digit-value: the value of the decimal digit `c` (Unicode's, any
script), or #f."
(define digit-value (subr pure (char) (union false nat))
  (lambda (c)
    (let ((k (char->integer c)))
      (letrec ((go (subr pure ((listof int acyclic)) (union false nat))
                 (lambda (l)
                   (cond ((null? l) #f)
                         ((and (>= k (car l)) (< k (+ (car l) 10))) (confirm-nat (- k (car l)) (n n) #f))
                         (else (go (cdr l)))))))
        (go digit-zeros)))))

"Whether `c` ends an identifier or a number in R7RS's lexical syntax:
whitespace, a parenthesis, a double quote, a semicolon or a vertical
line."
(define char-delimiter? (subr pure (char) bool)
  (lambda (c)
    (or (char-whitespace? c) (char=? c #\() (char=? c #\)) (char=? c #\") (char=? c #\;) (char=? c #\|))))

"R7RS's character names, and their characters' code points."
(define char-names (listof (productof (name string) (code int)) acyclic)
  (list (product (name "alarm") (code 7)) (product (name "backspace") (code 8))
        (product (name "delete") (code 127)) (product (name "escape") (code 27))
        (product (name "newline") (code 10)) (product (name "null") (code 0))
        (product (name "return") (code 13)) (product (name "space") (code 32))
        (product (name "tab") (code 9))))

"`c`'s R7RS name (#\\space's \"space\"), or #f."
(define char-name (subr pure (char) (union false string))
  (lambda (c)
    (let ((k (char->integer c)))
      (letrec ((go (subr pure ((listof (productof (name string) (code int)) acyclic)) (union false string))
                 (lambda (l) (cond ((null? l) #f) ((= (extract (car l) code) k) (extract (car l) name)) (else (go (cdr l)))))))
        (go char-names)))))

"The value of hex digit `c`, or -1."
(define hex-value (subr pure (char) int)
  (lambda (c)
    (let ((k (char->integer c)))
      (cond ((and (>= k 48) (<= k 57)) (- k 48))
            ((and (>= k 97) (<= k 102)) (- k 87))
            ((and (>= k 65) (<= k 70)) (- k 55))
            (else -1)))))

"The character `text` names after R7RS's #\\ -- one character, a name
(\"space\"), or x and hex digits (\"x41\") -- or #f."
(define name->char (subr pure (string) (union false char))
  (lambda (text)
    (let ((n (string-length text)))
      (letrec ((named (subr pure ((listof (productof (name string) (code int)) acyclic)) (union false char))
                 (lambda (l) (cond ((null? l) #f)
                                   ((string=? (extract (car l) name) text) (integer->char (extract (car l) code)))
                                   (else (named (cdr l))))))
               (hex (subr pure (int int) (union false char))
                 (lambda (i acc)
                   (cond ((>= i n) (if (<= acc 1114111) (integer->char acc) #f))
                         ((< (hex-value (string-ref text i)) 0) #f)
                         (else (hex (+ i 1) (+ (* acc 16) (hex-value (string-ref text i)))))))))
        (cond ((= n 1) (string-ref text 0))
              ((= n 0) #f)
              ;; No name begins with x.
              ((char=? (string-ref text 0) #\x) (hex 1 0))
              (else (named char-names)))))))

"The hex digits of `n` (n >= 0), lower case."
(define hex-string (subr pure (int) string)
  (lambda (n)
    (letrec ((go (subr pure (int (listof char acyclic) int) (listof char acyclic))
               (lambda (m acc fuel)
                 (let ((acc (the (listof char acyclic) (cons (string-ref "0123456789abcdef" (remainder m 16)) acc))))
                   (if (or (< m 16) (<= fuel 0)) acc (go (quotient m 16) acc (- fuel 1)))))))
      (list->string (go n nil 8)))))

"`c` as R7RS's `write` writes it: #\\ and its name if it has one, else #\\x
and hex for another control character, else #\\ and itself."
(define written-char (subr pure (char) string)
  (lambda (c)
    (let ((name (char-name c)) (k (char->integer c)))
      (cond ((not (bool? name)) (string-append "#\\" name))
            ((or (< k 32) (= k 127)) (string-append "#\\x" (hex-string k)))
            (else (string-append "#\\" (char->string c)))))))
