;;; regexp.fx: regular expressions in Emacs's syntax (Yank's `(yank
;;; regexp)`, ported): searching a string, for isearch's M-r and C-M-s.
;;;
;;;   .  any character but a newline      [abc] [^a-z] [[:alpha:]]  sets
;;;   *  +  ?  repeat (*? +? ?? as few times as will do)
;;;   \{n\} \{n,m\} \{n,\} \{,m\}  repeat n to m times
;;;   ^  $  the start, the end of a line   \` \'  of the text
;;;   \( \)  a group, numbered from 1   \(?: \)  one with no number
;;;   \|  or    \1 .. \9  the text group n matched
;;;   \w \W  a word character, any other   \sC \SC  syntax class C
;;;          (- or space: whitespace; w: word; _: symbol; .: punctuation)
;;;   \b \B  a word boundary, not one   \< \>  a word's start, end
;;;   \_< \_>  a symbol's start, end
;;;
;;; ^ is special only at the start of the expression, or after \( or \|;
;;; $ only at the end, or before \) or \|; * + ? only after something they
;;; can repeat. Otherwise they stand for themselves.
;;;
;;; The matcher backtracks, as Emacs's does, in continuation-passing
;;; style; what the groups matched is passed along, not kept in a table,
;;; so that backing out of a match undoes nothing. A module of no state:
;;; (define rx (load-module "regexp.fx")).

"An expression's tree. A repetition's `high` is -1 for no limit; a test is
one of bol eol bot eot word-boundary not-word-boundary word-start
word-end symbol-start symbol-end; a class (\\w, \\sC) one of word
whitespace symbol punctuation."
(define-type rx
  (sumof (seq (listof rx acyclic)) (alt (listof rx acyclic)) (chr char) (any unit)
         (set (productof (negated bool) (items (listof rx-item acyclic))))
         (rep (productof (low int) (high int) (greedy bool) (node rx)))
         (group (productof (n int) (node rx)))
         (backref int)
         (test string)
         (class (productof (name string) (negated bool)))))
"An item of a set: a character, a range, or a class ([:alpha:] and kin)."
(define-type rx-item (sumof (one char) (range (productof (low char) (high char))) (named string)))

"A compiled expression: its tree, how many numbered groups it has, the
character each match starts with if that is known, and whether matching
ignores case."
(define-type regexp (productof (node rx) (groups int) (first (sumof (none unit) (some char))) (fold bool)))
"What the groups matched, the latest first."
(define-type captures (listof (productof (n int) (start int) (end int)) acyclic))
"A match: where it starts and ends, and its groups'."
(define-type rx-match (productof (start int) (end int) (groups captures)))
(define-type maybe-match (sumof (none unit) (some rx-match)))

;;; ------------------------------------------------------------ parsing

(define-type parsed (sumof (ok (productof (node rx) (i int) (g int))) (bad string)))

(define class-names (listof string acyclic)
  (list "alpha" "alnum" "digit" "xdigit" "upper" "lower" "space" "blank" "punct" "word" "ascii" "cntrl" "graph" "print"))

(define* name-in? (subr spin (string (listof string acyclic)) bool)
  (lambda (x l) (and (pair? l) (or (string=? x (car l)) (name-in? x (cdr l))))))

(define* rx-reverse (subr spin ((listof rx acyclic) (listof rx acyclic)) (listof rx acyclic))
  (lambda (l acc) (if (null? l) acc (rx-reverse (cdr l) (cons (car l) acc)))))

"`source` parsed: its tree and how many numbered groups, or why it is no
regexp."
(define* rx-parse (subr spin (string) (sumof (ok (productof (node rx) (groups int))) (bad string)))
  (lambda (source)
    (let ((n (string-length source)))
      (letrec ((at? (subr spin (int string) bool)
                 (lambda (i s) (and (<= (+ i (string-length s)) n) (string=? s (substring source i (+ i (string-length s)))))))
               (ch (subr spin (int) char) (lambda (i) (string-ref source i)))
               (is? (subr spin (int char) bool) (lambda (i c) (and (< i n) (char=? (string-ref source i) c))))
               (ok (subr spin (rx int int) parsed) (lambda (node i g) (sum ok (product (node node) (i i) (g g)))))
               ;; Alternatives, up to \) or the end.
               (alternatives (subr spin (int int) parsed)
                 (lambda (i g)
                   (letrec ((more (subr spin ((listof rx acyclic) int int) parsed)
                              (lambda (alts i g)
                                (if (at? i "\\|")
                                    (tagcase (sequence (+ i 2) g)
                                      (ok r (more (cons (extract r node) alts) (extract r i) (extract r g)))
                                      (bad m (sum bad m)))
                                    (if (null? (cdr alts)) (ok (car alts) i g) (ok (sum alt (rx-reverse alts nil)) i g))))))
                     (tagcase (sequence i g)
                       (ok r (more (list (extract r node)) (extract r i) (extract r g)))
                       (bad m (sum bad m))))))
               ;; A sequence, up to \|, \), or the end.
               (sequence (subr spin (int int) parsed)
                 (lambda (i g)
                   (letrec ((go (subr spin ((listof rx acyclic) int int bool) parsed)
                              (lambda (items i g start)
                                (cond ((or (= i n) (at? i "\\|") (at? i "\\)")) (ok (sum seq (rx-reverse items nil)) i g))
                                      ((and start (is? i #\^)) (go (cons (sum test "bol") items) (+ i 1) g #f))
                                      ((and (is? i #\$) (or (= (+ i 1) n) (at? (+ i 1) "\\|") (at? (+ i 1) "\\)")))
                                       (go (cons (sum test "eol") items) (+ i 1) g #f))
                                      ((and (or (is? i #\*) (is? i #\+) (is? i #\?)) (pair? items) (repeatable? (car items)))
                                       (let* ((c (ch i))
                                              (lazy (is? (+ i 1) #\?))
                                              (node (car items))
                                              (r (cond ((char=? c #\*) (product (low 0) (high -1) (greedy (not lazy)) (node node)))
                                                       ((char=? c #\+) (product (low 1) (high -1) (greedy (not lazy)) (node node)))
                                                       (else (product (low 0) (high 1) (greedy (not lazy)) (node node))))))
                                         (go (cons (sum rep r) (cdr items)) (+ i (if lazy 2 1)) g #f)))
                                      ((and (at? i "\\{") (pair? items) (repeatable? (car items)))
                                       (tagcase (interval (+ i 2) (car items))
                                         (ok r (go (cons (extract r node) (cdr items)) (extract r i) g #f))
                                         (bad m (sum bad m))))
                                      (else (tagcase (atom i g)
                                              (ok r (go (cons (extract r node) items) (extract r i) (extract r g) #f))
                                              (bad m (sum bad m))))))))
                     (go nil i g #t))))
               (repeatable? (subr spin (rx) bool) (lambda (x) (tagcase x (test t #f) (else y #t))))
               ;; Digits at i: their value and where they end; -1 if none.
               (number-at (subr spin (int) (productof (value int) (i int)))
                 (lambda (i)
                   (letrec ((go (subr spin (int int) (productof (value int) (i int)))
                              (lambda (j v) (if (and (< j n) (char-numeric? (ch j)))
                                                (go (+ j 1) (+ (* v 10) (- (char->integer (ch j)) 48)))
                                                (product (value (if (= j i) -1 v)) (i j))))))
                     (go i 0))))
               ;; After \{: n\}, n,m\}, n,\}, ,m\}, applied to `node`.
               (interval (subr spin (int rx) parsed)
                 (lambda (i node)
                   (let* ((lo (number-at i))
                          (low (max 0 (extract lo value)))
                          (hi (if (is? (extract lo i) #\,) (number-at (+ (extract lo i) 1)) (product (value low) (i (extract lo i)))))
                          (high (extract hi value)))
                     (cond ((not (at? (extract hi i) "\\}")) (sum bad "Invalid regexp: unmatched \\{"))
                           ((and (>= high 0) (< high low)) (sum bad "Invalid regexp: bad interval \\{"))
                           (else (ok (sum rep (product (low low) (high high) (greedy #t) (node node))) (+ (extract hi i) 2) 0))))))
               (atom (subr spin (int int) parsed)
                 (lambda (i g)
                   (let ((c (ch i)))
                     (cond ((char=? c #\.) (ok (sum any #u) (+ i 1) g))
                           ((char=? c #\[) (bracket (+ i 1) g))
                           ((char=? c #\\) (escape (+ i 1) g))
                           (else (ok (sum chr c) (+ i 1) g))))))
               (escape (subr spin (int int) parsed)
                 (lambda (i g)
                   (if (>= i n) (sum bad "Invalid regexp: trailing backslash")
                       (let ((c (ch i)) (j (+ i 1)))
                         (cond ((char=? c #\() (group j g))
                               ((char=? c #\)) (sum bad "Invalid regexp: unmatched \\)"))
                               ((char=? c #\w) (ok (sum class (product (name "word") (negated #f))) j g))
                               ((char=? c #\W) (ok (sum class (product (name "word") (negated #t))) j g))
                               ((or (char=? c #\s) (char=? c #\S))
                                (if (>= j n) (sum bad "Invalid regexp: \\s must be followed by a syntax class")
                                    (let ((d (ch j)))
                                      (let ((name (cond ((or (char=? d #\-) (char=? d #\space)) "whitespace")
                                                        ((char=? d #\w) "word") ((char=? d #\_) "symbol") ((char=? d #\.) "punctuation")
                                                        (else ""))))
                                        (if (string=? name "")
                                            (sum bad (string-append "Invalid regexp: unknown syntax class " (char->string d)))
                                            (ok (sum class (product (name name) (negated (char=? c #\S)))) (+ j 1) g))))))
                               ((char=? c #\b) (ok (sum test "word-boundary") j g))
                               ((char=? c #\B) (ok (sum test "not-word-boundary") j g))
                               ((char=? c #\<) (ok (sum test "word-start") j g))
                               ((char=? c #\>) (ok (sum test "word-end") j g))
                               ((char=? c #\`) (ok (sum test "bot") j g))
                               ((char=? c #\') (ok (sum test "eot") j g))
                               ((char=? c #\_)
                                (cond ((is? j #\<) (ok (sum test "symbol-start") (+ j 1) g))
                                      ((is? j #\>) (ok (sum test "symbol-end") (+ j 1) g))
                                      (else (sum bad "Invalid regexp: \\_ must be followed by < or >"))))
                               ((and (char-numeric? c) (not (char=? c #\0)))
                                (let ((k (- (char->integer c) 48)))
                                  (if (> k g)
                                      (sum bad (string-append "Invalid regexp: \\" (char->string c) " refers to no group"))
                                      (ok (sum backref k) j g))))
                               (else (ok (sum chr c) j g)))))))
               (group (subr spin (int int) parsed)
                 (lambda (i g)
                   (let* ((numbered (not (at? i "?:")))
                          (g2 (if numbered (+ g 1) g)))
                     (tagcase (alternatives (if numbered i (+ i 2)) g2)
                       (ok r (if (at? (extract r i) "\\)")
                                 (ok (if numbered (sum group (product (n g2) (node (extract r node)))) (extract r node))
                                     (+ (extract r i) 2) (extract r g))
                                 (sum bad "Invalid regexp: unmatched \\(")))
                       (bad m (sum bad m))))))
               ;; After [: the set, through its ].
               (bracket (subr spin (int int) parsed)
                 (lambda (i0 g)
                   (let ((negated (is? i0 #\^)))
                     (letrec ((go (subr spin ((listof rx-item acyclic) int bool) parsed)
                                (lambda (items i first)
                                  (cond ((>= i n) (sum bad "Invalid regexp: unmatched ["))
                                        ((and (char=? (ch i) #\]) (not first))
                                         (ok (sum set (product (negated negated) (items items))) (+ i 1) g))
                                        ((at? i "[:")
                                         (letrec ((close (subr spin (int) int)
                                                    (lambda (j) (cond ((> (+ j 2) n) -1) ((at? j ":]") j) (else (close (+ j 1)))))))
                                           (let ((e (close (+ i 2))))
                                             (if (< e 0) (sum bad "Invalid regexp: bad character class")
                                                 (let ((name (substring source (+ i 2) e)))
                                                   (if (name-in? name class-names)
                                                       (go (cons (sum named name) items) (+ e 2) #f)
                                                       (sum bad (string-append "Invalid regexp: unknown character class " name))))))))
                                        ((and (is? (+ i 1) #\-) (< (+ i 2) n) (not (char=? (ch (+ i 2)) #\])))
                                         (let ((low (ch i)) (high (ch (+ i 2))))
                                           (if (< (char->integer high) (char->integer low))
                                               (sum bad (string-append "Invalid regexp: bad range " (char->string low) "-" (char->string high)))
                                               (go (cons (sum range (product (low low) (high high))) items) (+ i 3) #f))))
                                        (else (go (cons (sum one (ch i)) items) (+ i 1) #f))))))
                       (go nil (if negated (+ i0 1) i0) #t))))))
        (tagcase (alternatives 0 0)
          (ok r (if (< (extract r i) n)
                    (sum bad "Invalid regexp: unmatched \\)")
                    (sum ok (product (node (extract r node)) (groups (extract r g))))))
          (bad m (sum bad m)))))))

"The character each match of `x` starts with, if it is known: tests match
no characters, so what follows them counts."
(define* first-char (subr spin (rx) (sumof (none unit) (some char)))
  (lambda (x)
    (tagcase x
      (chr c (sum some c))
      (seq items (letrec ((go (subr spin ((listof rx acyclic)) (sumof (none unit) (some char)))
                                (lambda (l) (cond ((null? l) (sum none #u))
                                                  (else (tagcase (car l) (test t (go (cdr l))) (else y (first-char (car l)))))))))
                   (go items)))
      (group g (first-char (extract g node)))
      (rep r (if (> (extract r low) 0) (first-char (extract r node)) (sum none #u)))
      (else y (sum none #u)))))

"`source` compiled, matching ignoring case if `fold`; or why it is no
regexp."
(define* make-regexp (subr spin (string bool) (sumof (ok regexp) (bad string)))
  (lambda (source fold)
    (tagcase (rx-parse source)
      (ok r (sum ok (product (node (extract r node)) (groups (extract r groups)) (first (first-char (extract r node))) (fold fold))))
      (bad m (sum bad m)))))

;;; ------------------------------------------------------------ characters

(define* word-char? (subr pure (char) bool) (lambda (c) (or (char-alphabetic? c) (char-numeric? c))))
"Symbol constituents, as Lisp and Scheme have them (for \\_< \\_>)."
(define* symbol-char? (subr pure (char) bool)
  (lambda (c) (or (word-char? c) (char-in? c "_-+*/<>=!?$%&~^:."))))
(define* upper? (subr pure (char) bool) (lambda (c) (not (char=? c (char-downcase c)))))
(define* lower? (subr pure (char) bool) (lambda (c) (not (char=? c (char-upcase c)))))

(define* class-char? (subr pure (string char) bool)
  (lambda (name c)
    (let ((k (char->integer c)))
      (case name
        (("alpha") (char-alphabetic? c))
        (("alnum" "word") (word-char? c))
        (("digit") (char-numeric? c))
        (("xdigit") (or (char-numeric? c) (char-in? (char-downcase c) "abcdef")))
        (("upper") (upper? c))
        (("lower") (lower? c))
        (("space") (char-whitespace? c))
        (("blank") (or (char=? c #\space) (= k 9)))
        (("punct") (and (< k 128) (not (word-char? c)) (not (char-whitespace? c)) (> k 32) (not (= k 127))))
        (("ascii") (< k 128))
        (("cntrl") (or (< k 32) (= k 127)))
        (("graph") (and (> k 32) (not (= k 127)) (not (char-whitespace? c))))
        (("print") (and (>= k 32) (not (= k 127))))
        (else #f)))))

(define* syntax-class-char? (subr pure (string char) bool)
  (lambda (name c)
    (case name
      (("whitespace") (char-whitespace? c))
      (("word") (word-char? c))
      (("symbol") (and (symbol-char? c) (not (word-char? c))))
      (("punctuation") (and (not (word-char? c)) (not (char-whitespace? c)) (not (symbol-char? c))))
      (else #f))))

;;; ------------------------------------------------------------ matching

"Matching `re` in `text` (`size` long), as the matcher's procedures see
it."
(define-type rx-env (productof (text string) (size int) (fold bool)))
(define-type rx-k (subr spin (int captures) maybe-match))

(define* same-char? (subr pure (rx-env char char) bool)
  (lambda (env a b) (if (extract env fold) (char=? (char-downcase a) (char-downcase b)) (char=? a b))))

"Whether there is a character at `pos`, and `ok?` is true of it."
(define* char-test (subr spin (rx-env int (subr spin (char) bool)) bool)
  (lambda (env pos ok?) (and (>= pos 0) (< pos (extract env size)) (ok? (string-ref (extract env text) pos)))))

(define* in-set? (subr spin (rx-env (listof rx-item acyclic) char) bool)
  (lambda (env items c)
    (and (pair? items)
         (or (tagcase (car items)
               (one d (same-char? env d c))
               (range r (let ((lo (char->integer (extract r low))) (hi (char->integer (extract r high))))
                          (letrec ((in (subr pure (char) bool) (lambda (x) (and (<= lo (char->integer x)) (<= (char->integer x) hi)))))
                            (or (in c) (and (extract env fold) (or (in (char-upcase c)) (in (char-downcase c))))))))
               (named name (class-char? name c)))
             (in-set? env (cdr items) c)))))

(define* test-holds? (subr spin (rx-env string int) bool)
  (lambda (env t pos)
    (let* ((before-word (char-test env (- pos 1) word-char?))
           (after-word (char-test env pos word-char?))
           (before-sym (char-test env (- pos 1) symbol-char?))
           (after-sym (char-test env pos symbol-char?)))
      (case t
        (("bol") (or (= pos 0) (char-test env (- pos 1) (lambda ((c char)) (char=? c #\newline)))))
        (("eol") (or (= pos (extract env size)) (char-test env pos (lambda ((c char)) (char=? c #\newline)))))
        (("bot") (= pos 0))
        (("eot") (= pos (extract env size)))
        (("word-boundary") (not (bool=? before-word after-word)))
        (("not-word-boundary") (bool=? before-word after-word))
        (("word-start") (and after-word (not before-word)))
        (("word-end") (and before-word (not after-word)))
        (("symbol-start") (and after-sym (not before-sym)))
        (("symbol-end") (and before-sym (not after-sym)))
        (else #f)))))

"Group `n`'s latest capture, if it matched."
(define* capture-of (subr spin (captures int) (sumof (none unit) (some (productof (start int) (end int)))))
  (lambda (cs n)
    (cond ((null? cs) (sum none #u))
          ((= (extract (car cs) n) n) (sum some (product (start (extract (car cs) start)) (end (extract (car cs) end)))))
          (else (capture-of (cdr cs) n)))))

"Match `x` at `pos`, then `k` from where it ends: k's answer, or none if
no way of matching makes k succeed."
(define* rx-match-node (subr spin (rx-env rx int captures rx-k) maybe-match)
  (lambda (env x pos cs k)
    (tagcase x
      (seq items (letrec ((go (subr spin ((listof rx acyclic) int captures) maybe-match)
                                (lambda (l p c) (if (null? l) (k p c)
                                                    (rx-match-node env (car l) p c (lambda ((p2 int) (c2 captures)) (go (cdr l) p2 c2)))))))
                   (go items pos cs)))
      (alt items (letrec ((go (subr spin ((listof rx acyclic)) maybe-match)
                                (lambda (l) (if (null? l) (sum none #u)
                                                (tagcase (rx-match-node env (car l) pos cs k)
                                                  (some m (sum some m))
                                                  (none u (go (cdr l))))))))
                   (go items)))
      (chr c (if (char-test env pos (lambda ((d char)) (same-char? env c d))) (k (+ pos 1) cs) (sum none #u)))
      (any u (if (char-test env pos (lambda ((d char)) (not (char=? d #\newline)))) (k (+ pos 1) cs) (sum none #u)))
      (set s (if (char-test env pos (lambda ((d char)) (not (bool=? (extract s negated) (in-set? env (extract s items) d)))))
                 (k (+ pos 1) cs) (sum none #u)))
      (class c (if (char-test env pos (lambda ((d char)) (not (bool=? (extract c negated) (syntax-class-char? (extract c name) d)))))
                   (k (+ pos 1) cs) (sum none #u)))
      (rep r
        ;; A repetition that matched nothing is not repeated again, once
        ;; the low count is reached.
        (let ((low (extract r low)) (high (extract r high)))
          (letrec ((loop (subr spin (int int captures) maybe-match)
                     (lambda (p count c)
                       (let ((more (lambda ()
                                     (if (or (< high 0) (< count high))
                                         (rx-match-node env (extract r node) p c
                                                        (lambda ((p2 int) (c2 captures))
                                                          (if (or (> p2 p) (< count low)) (loop p2 (+ count 1) c2) (sum none #u))))
                                         (sum none #u))))
                             (enough (lambda () (if (>= count low) (k p c) (sum none #u)))))
                         (if (extract r greedy)
                             (tagcase (more) (some m (sum some m)) (none u (enough)))
                             (tagcase (enough) (some m (sum some m)) (none u (more))))))))
            (loop pos 0 cs))))
      (group g (rx-match-node env (extract g node) pos cs
                              (lambda ((p int) (c captures))
                                (k p (cons (product (n (extract g n)) (start pos) (end p)) c)))))
      (backref n (tagcase (capture-of cs n)
                   (some g (letrec ((go (subr spin (int int) maybe-match)
                                          (lambda (i p)
                                            (cond ((= i (extract g end)) (k p cs))
                                                  ((char-test env p (lambda ((d char)) (same-char? env (string-ref (extract env text) i) d)))
                                                   (go (+ i 1) (+ p 1)))
                                                  (else (sum none #u))))))
                             (go (extract g start) pos)))
                   (none u (sum none #u))))
      (test t (if (test-holds? env t pos) (k pos cs) (sum none #u))))))

"A match of `re` starting at `pos` in `text`."
(define* regexp-match-at (subr spin (regexp string int) maybe-match)
  (lambda (re text pos)
    (let ((env (product (text text) (size (string-length text)) (fold (extract re fold)))))
      (rx-match-node env (extract re node) pos nil
                     (lambda ((end int) (cs captures)) (sum some (product (start pos) (end end) (groups cs))))))))

"The first match of `re` in `text` starting at or after `from` (if not
`forward`, the last starting at or before it)."
(define* regexp-search (subr spin (regexp string int bool) maybe-match)
  (lambda (re text from forward)
    (let* ((size (string-length text))
           (may-start? (lambda ((pos int))
                         (tagcase (extract re first)
                           (none u #t)
                           (some c (and (< pos size)
                                        (if (extract re fold)
                                            (char=? (char-downcase (string-ref text pos)) (char-downcase c))
                                            (char=? (string-ref text pos) c))))))))
      (letrec ((go (subr spin (int) maybe-match)
                 (lambda (pos)
                   (if (or (< pos 0) (> pos size)) (sum none #u)
                       (tagcase (if (may-start? pos) (regexp-match-at re text pos) (sum none #u))
                         (some m (sum some m))
                         (none u (go (if forward (+ pos 1) (- pos 1)))))))))
        (go (if forward (max from 0) (min from size)))))))

"Group `n` of match `m` (0: all of it), if it matched."
(define* match-group (subr spin (rx-match int) (sumof (none unit) (some (productof (start int) (end int)))))
  (lambda (m n) (if (= n 0) (sum some (product (start (extract m start)) (end (extract m end)))) (capture-of (extract m groups) n))))

"Whether a search for `s` as a regexp ignores case: unless it has an
upper-case letter not after a backslash (\\W is not one)."
(define* regexp-fold-case? (subr spin (string) bool)
  (lambda (s)
    (letrec ((go (subr spin (int) bool)
               (lambda (i) (cond ((>= i (string-length s)) #t)
                                 ((char=? (string-ref s i) #\\) (go (+ i 2)))
                                 ((upper? (string-ref s i)) #f)
                                 (else (go (+ i 1)))))))
      (go 0))))
