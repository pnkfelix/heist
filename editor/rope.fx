;;; rope.fx: text as a persistent rope (cahoots' `(yank actor rope)`,
;;; c337e2a). A balanced tree of strings: changing it makes a new rope
;;; that shares most of the old, and the old stays as it was. So a
;;; buffer's text at each revision is a value: a snapshot costs nothing,
;;; and a turn that fails has changed nothing.
;;;
;;; Positions run from 0 to the length, between characters. Each node
;;; knows its length and its newlines, so a line's start, or the line of
;;; a position, is one walk down the tree. Lines are numbered from 0.
;;; An AVL tree by height; leaves hold up to `leaf-size` characters.

"The tree. A rope is immutable data, so it is transmissible: an
analysis in another process can be sent one."
(define-datatype rope
  (leaf string int)                     ; text, its newlines
  (branch rope rope int int int))       ; left, right, length, newlines, height

(hide
  (define leaf-size int 512)

  (define count-newlines (subr spin (string int int) int)
    (lambda (s start end)
      (letrec ((go (subr spin (int int) int)
                 (lambda (i n)
                   (if (>= i end) n (go (+ i 1) (if (char=? (string-ref s i) #\newline) (+ n 1) n))))))
        (go start 0))))

  (define make-leaf (subr spin (string) rope)
    (lambda (s) (leaf s (count-newlines s 0 (string-length s)))))

  (define node (subr pure (rope rope) rope)
    (lambda (l r)
      (branch l r (+ (rope-length l) (rope-length r))
              (+ (rope-newlines l) (rope-newlines r))
              (+ 1 (max (rope-height l) (rope-height r))))))

  (define is-empty? (subr pure (rope) bool) (lambda (r) (= 0 (rope-length r))))

  ;; a then b, as a node, rotated if their heights are two apart.
  (define balance (subr pure (rope rope) rope)
    (lambda (a b)
      (let ((ha (rope-height a)) (hb (rope-height b)))
        (cond ((> ha (+ hb 1))
               (tagcase a
                 (branch (al ar n nl h)
                   (if (>= (rope-height al) (rope-height ar))
                       (node al (node ar b))
                       (tagcase ar
                         (branch (arl arr n2 nl2 h2) (node (node al arl) (node arr b)))
                         (else y (node a b)))))
                 (else y (node a b))))
              ((> hb (+ ha 1))
               (tagcase b
                 (branch (bl br n nl h)
                   (if (>= (rope-height br) (rope-height bl))
                       (node (node a bl) br)
                       (tagcase bl
                         (branch (bll blr n2 nl2 h2) (node (node a bll) (node blr br)))
                         (else y (node a b)))))
                 (else y (node a b))))
              (else (node a b)))))))

(define empty-rope rope (leaf "" 0))

(define rope-length (subr pure (rope) int)
  (lambda (r) (tagcase r (leaf (s nl) (string-length s)) (branch (l rt n nl h) n))))

(define rope-newlines (subr pure (rope) int)
  (lambda (r) (tagcase r (leaf (s nl) nl) (branch (l rt n nl h) nl))))

(define rope-height (subr pure (rope) int)
  (lambda (r) (tagcase r (leaf (s nl) 0) (branch (l rt n nl h) h))))

"A rope of string `s`, balanced."
(define string->rope (subr spin (string) rope)
  (lambda (s)
    (letrec ((build (subr spin (int int) rope)
               (lambda (start end)
                 (if (<= (- end start) leaf-size)
                     (make-leaf (substring s start end))
                     (let ((mid (quotient (+ start end) 2)))
                       (node (build start mid) (build mid end)))))))
      (build 0 (string-length s)))))

"`l` then `r`, their heights at most one apart on the way up: AVL's join."
(define rope-append (subr spin (rope rope) rope)
  (lambda (l r)
    (letrec ((join (subr spin (rope rope) rope)
               (lambda (l r)
                 (cond ((is-empty? l) r)
                       ((is-empty? r) l)
                       (else
                        (tagcase l
                          (leaf (ls lnl)
                            (tagcase r
                              (leaf (rs rnl)
                                (if (<= (+ (string-length ls) (string-length rs)) leaf-size)
                                    (leaf (string-append ls rs) (+ lnl rnl))
                                    (node l r)))
                              (branch (rl rr n nl h)
                                (if (> h 1) (balance (join l rl) rr) (node l r)))))
                          (branch (ll lr ln lnl lh)
                            (cond ((> lh (+ (rope-height r) 1)) (balance ll (join lr r)))
                                  ((> (rope-height r) (+ lh 1))
                                   (tagcase r
                                     (branch (rl rr n nl h) (balance (join l rl) rr))
                                     (else y (node l r))))
                                  (else (node l r))))))))))
      (join l r))))

"The text before `pos` and after it."
(define rope-split (subr spin (rope int) (productof (before rope) (after rope)))
  (lambda (r pos)
    (letrec ((split (subr spin (rope int) (productof (before rope) (after rope)))
               (lambda (r pos)
                 (cond ((<= pos 0) (product (before empty-rope) (after r)))
                       ((>= pos (rope-length r)) (product (before r) (after empty-rope)))
                       (else
                        (tagcase r
                          (leaf (s nl)
                            (product (before (make-leaf (substring s 0 pos)))
                                     (after (make-leaf (substring s pos (string-length s))))))
                          (branch (l rt n nl h)
                            (let ((ln (rope-length l)))
                              (cond ((< pos ln)
                                     (let ((p (split l pos)))
                                       (product (before (extract p before))
                                                (after (rope-append (extract p after) rt)))))
                                    ((= pos ln) (product (before l) (after rt)))
                                    (else
                                     (let ((p (split rt (- pos ln))))
                                       (product (before (rope-append l (extract p before)))
                                                (after (extract p after))))))))))))))
      (split r pos))))

(define rope-insert (subr spin (rope int string) rope)
  (lambda (r pos s)
    (let ((p (rope-split r pos)))
      (rope-append (rope-append (extract p before) (string->rope s)) (extract p after)))))

(define rope-delete (subr spin (rope int int) rope)
  (lambda (r start end)
    (let* ((p (rope-split r start))
           (q (rope-split (extract p after) (- end start))))
      (rope-append (extract p before) (extract q after)))))

"The character at `i`, which must be within the text."
(define rope-ref (subr pure (rope int) char)
  (lambda (r i)
    (letrec ((go (subr pure (rope int) char)
               (lambda (r i)
                 (tagcase r
                   (leaf (s nl) (string-ref s i))
                   (branch (l rt n nl h)
                     (let ((ln (rope-length l)))
                       (if (< i ln) (go l i) (go rt (- i ln)))))))))
      (go r i))))

"The text from `start` to `end`, as a string: its leaves' pieces, joined once."
(define rope-substring (subr spin (rope int int) string)
  (lambda (r start end)
    (letrec ((walk (subr spin (rope int int (listof string acyclic)) (listof string acyclic))
               ;; The pieces, last first, onto `acc`.
               (lambda (r start end acc)
                 (if (>= start end)
                     acc
                     (tagcase r
                       (leaf (s nl) (cons (substring s start end) acc))
                       (branch (l rt n nl h)
                         (let ((ln (rope-length l)))
                           (walk rt (max 0 (- start ln)) (- end ln)
                                 (walk l start (min end ln) acc)))))))))
      (apply string-append (reverse (walk r (max start 0) (min end (rope-length r)) nil))))))

(define rope->string (subr spin (rope) string)
  (lambda (r) (rope-substring r 0 (rope-length r))))

(define rope-line-count (subr pure (rope) int) (lambda (r) (+ 1 (rope-newlines r))))

"Where line `n` starts: after the nth newline, or the end if there are
not so many."
(define rope-line-start (subr spin (rope int) int)
  (lambda (r n)
    (letrec ((go (subr spin (rope int) int)
               (lambda (r n)
                 (cond ((<= n 0) 0)
                       ((> n (rope-newlines r)) (rope-length r))
                       (else
                        (tagcase r
                          (leaf (s nl)
                            (letrec ((scan (subr spin (int int) int)
                                       (lambda (i n)
                                         (if (char=? (string-ref s i) #\newline)
                                             (if (= n 1) (+ i 1) (scan (+ i 1) (- n 1)))
                                             (scan (+ i 1) n)))))
                              (scan 0 n)))
                          (branch (l rt ln lnl h)
                            (if (<= n (rope-newlines l))
                                (go l n)
                                (+ (rope-length l) (go rt (- n (rope-newlines l))))))))))))
      (go r n))))

"Where line `n` ends: before its newline, or at the end."
(define rope-line-end (subr spin (rope int) int)
  (lambda (r n)
    (if (>= n (rope-newlines r))
        (rope-length r)
        (- (rope-line-start r (+ n 1)) 1))))

"The line `pos` is on: the newlines before it."
(define rope-line-of (subr spin (rope int) int)
  (lambda (r pos)
    (letrec ((go (subr spin (rope int) int)
               (lambda (r pos)
                 (if (<= pos 0)
                     0
                     (tagcase r
                       (leaf (s nl) (count-newlines s 0 (min pos (string-length s))))
                       (branch (l rt n nl h)
                         (let ((ln (rope-length l)))
                           (if (<= pos ln)
                               (go l pos)
                               (+ (rope-newlines l) (go rt (- pos ln)))))))))))
      (go r pos))))
