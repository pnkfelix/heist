;;; sexp.fx: lists and the things in them, as the text has them now
;;; (yank's `(yank sexp)`, and cahoots' `(yank actor paredit)` and
;;; `(yank actor structure)`, c337e2a, in a first form).
;;;
;;; A scanner over the text, from the start of the top-level form point is
;;; in (a `(` at the start of a line): it knows strings, comments and
;;; character literals (`#\(`), so a paren in one is not a paren. It works
;;; on the text as it is, in the command's turn, not on the syntax actor's
;;; annotation, which may be of a revision before. From it: moving by
;;; sexps (C-M-f, C-M-b, C-M-u, C-M-d), killing one (C-M-k), the match of
;;; the paren at point, and paredit's keys and structural edits.


"Where the top-level form `pos` is in starts: the last `(` at the start of a
line at or before `pos`; 0 if none."
(define top-start (->* (rope int) int)
  (lambda (t pos)
    (letrec ((go (->* (int) int)
               (lambda (line)
                 (if (< line 0) 0
                     (let ((s (rope-line-start t line)))
                       (if (and (< s (rope-length t)) (<= s pos) (char=? (rope-ref t s) #\())
                           s
                           (go (- line 1))))))))
      (go (rope-line-of t pos)))))

"What a scan from a form's start finds at a position: the lists open there
(their opening positions, innermost first), and whether it is in a string
(from where) or a comment."
(define-type scan-state (productof (opens ints) (string-at int) (comment bool)))

"The text `s` (of the buffer from `base`) scanned from its start to `to`."
(define scan-to (->* (string int int) scan-state)
  (lambda (s base to)
    (let ((n (min (string-length s) (- to base))))
      (letrec ((go (->* (int ints int bool) scan-state)
                 (lambda (i opens str comment)
                   (if (>= i n)
                       (product (opens opens) (string-at str) (comment comment))
                       (let ((c (string-ref s i)))
                         (cond (comment (go (+ i 1) opens -1 (not (char=? c #\newline))))
                               ((>= str 0)
                                (cond ((char=? c #\\) (go (+ i 2) opens str #f))
                                      ((char=? c #\") (go (+ i 1) opens -1 #f))
                                      (else (go (+ i 1) opens str #f))))
                               ((char=? c #\;) (go (+ i 1) opens -1 #t))
                               ((char=? c #\") (go (+ i 1) opens (+ base i) #f))
                               ((and (char=? c #\#) (< (+ i 1) n) (char=? (string-ref s (+ i 1)) #\\))
                                (go (+ i 3) opens -1 #f))
                               ((or (char=? c #\() (char=? c #\[)) (go (+ i 1) (cons (+ base i) opens) -1 #f))
                               ((or (char=? c #\)) (char=? c #\]))
                                (go (+ i 1) (if (pair? opens) (cdr opens) opens) -1 #f))
                               (else (go (+ i 1) opens -1 #f))))))))
        (go 0 nil -1 #f)))))

"The scan state at `pos` in `t`."
(define scan-at (->* (rope int) scan-state)
  (lambda (t pos)
    (let ((from (top-start t pos)))
      (scan-to (rope-substring t from pos) from pos))))

(define delimiter? (->* (char) bool)
  (lambda (c) (or (char-whitespace? c) (char-in? c "()[]\";"))))

"Past spaces and comments from `pos`, forward."
(define skip-space (->* (rope int) int)
  (lambda (t pos)
    (let ((n (rope-length t)))
      (letrec ((go (->* (int) int)
                 (lambda (i)
                   (cond ((>= i n) n)
                         ((char-whitespace? (rope-ref t i)) (go (+ i 1)))
                         ((char=? (rope-ref t i) #\;)
                          (letrec ((eol (->* (int) int)
                                     (lambda (j) (if (or (>= j n) (char=? (rope-ref t j) #\newline)) j (eol (+ j 1))))))
                            (go (eol i))))
                         (else i)))))
        (go pos)))))

"Where the sexp starting at `pos` (no space before it) ends; -1 if none
does: a close paren there, or the end of the text, or an unclosed list."
(define sexp-end (->* (rope int) int)
  (lambda (t pos)
    (let ((n (rope-length t)))
      (if (>= pos n) -1
          (let ((c (rope-ref t pos)))
            (cond ((or (char=? c #\)) (char=? c #\])) -1)
                  ((char=? c #\")
                   (letrec ((go (->* (int) int)
                              (lambda (i) (cond ((>= i n) -1)
                                                ((char=? (rope-ref t i) #\\) (go (+ i 2)))
                                                ((char=? (rope-ref t i) #\") (+ i 1))
                                                (else (go (+ i 1)))))))
                     (go (+ pos 1))))
                  ((or (char=? c #\() (char=? c #\[))
                   ;; Each item in turn, to the close.
                   (letrec ((go (->* (int) int)
                              (lambda (i)
                                (let ((j (skip-space t i)))
                                  (cond ((>= j n) -1)
                                        ((char-in? (rope-ref t j) ")]") (+ j 1))
                                        (else (let ((e (sexp-end t j))) (if (< e 0) -1 (go e)))))))))
                     (go (+ pos 1))))
                  ((char-in? c "'`,")
                   (let ((j (skip-space t (+ pos 1)))) (sexp-end t (if (and (< j n) (char=? (rope-ref t j) #\@)) (+ j 1) j))))
                  ((and (char=? c #\#) (< (+ pos 1) n) (char=? (rope-ref t (+ pos 1)) #\\))
                   (letrec ((go (->* (int) int)
                              (lambda (i) (if (or (>= i n) (delimiter? (rope-ref t i))) i (go (+ i 1))))))
                     (go (+ pos 3))))
                  ((and (char=? c #\#) (< (+ pos 1) n) (char=? (rope-ref t (+ pos 1)) #\())
                   (sexp-end t (+ pos 1)))
                  (else
                   (letrec ((go (->* (int) int)
                              (lambda (i) (if (or (>= i n) (delimiter? (rope-ref t i))) i (go (+ i 1))))))
                     (go pos)))))))))

"The sexps of the list opening at `open` (or, -1, of the top level from
`from`): each one's start and end, in order, up to `limit`."
(define-type sexp-span (productof (start int) (end int)))
(define-type sexp-spans (listof sexp-span acyclic))
(define children (->* (rope int int) sexp-spans)
  (lambda (t from limit)
    (let ((n (rope-length t)))
      (letrec ((go (->* (int) sexp-spans)
                 (lambda (i)
                   (let ((j (skip-space t i)))
                     (if (or (>= j n) (>= j limit) (char-in? (rope-ref t j) ")]"))
                         nil
                         (let ((e (sexp-end t j)))
                           (if (< e 0) nil (cons (product (start j) (end e)) (go e)))))))))
        (go from)))))

"Where the items around `pos` start being read: just inside the innermost
list open there, or the top-level form's start."
(define items-from (->* (rope int) int)
  (lambda (t pos)
    (let ((st (scan-at t pos)))
      (if (pair? (extract st opens)) (+ 1 (car (extract st opens))) (top-start t pos)))))

;;; ------------------------------------------------------------ motion

(define-type motion (subr (maxeff spin (read @globals)) (rope int) int))
"A command moving point by `m`, which gives -1 where it cannot."
(define* sexp-motion (subr pure (motion string) command)
  (lambda (m why)
    (lambda ((b buffer))
      (let ((to (m (extract b text) (extract b point))))
        (if (< to 0) (say b why) (done (with-point b to)))))))

"C-M-f: past the next sexp."
(define forward-sexp (->* (rope int) int)
  (lambda (t p) (sexp-end t (skip-space t p))))

"C-M-b: to the start of the sexp before point."
(define backward-sexp (->* (rope int) int)
  (lambda (t p)
    (letrec ((last (->* (sexp-spans int) int)
               (lambda (cs best) (cond ((null? cs) best)
                                       ((< (extract (car cs) start) p) (last (cdr cs) (extract (car cs) start)))
                                       (else best)))))
      (last (children t (items-from t p) p) -1))))

"C-M-u: to the open paren of the list point is in."
(define up-list (->* (rope int) int)
  (lambda (t p) (let ((st (scan-at t p))) (if (pair? (extract st opens)) (car (extract st opens)) -1))))

"C-M-d: into the next list, after its open paren."
(define down-list (->* (rope int) int)
  (lambda (t p)
    (let ((n (rope-length t)))
      (letrec ((go (->* (int) int)
                 (lambda (i)
                   (let ((j (skip-space t i)))
                     (cond ((>= j n) -1)
                           ((char-in? (rope-ref t j) "([") (+ j 1))
                           ((char-in? (rope-ref t j) ")]") -1)
                           (else (let ((e (sexp-end t j))) (if (< e 0) -1 (go e)))))))))
        (go p)))))

"C-M-k: the next sexp killed."
(define* kill-sexp (subr pure () command)
  (lambda ()
    (lambda ((b buffer))
      (let* ((t (extract b text)) (p (extract b point)) (e (forward-sexp t p)))
        (if (< e 0)
            (say b "No sexp after point")
            (product (buffer (with-text b (rope-delete t p e) p))
                     (cmds (list (kill-push (rope-substring t p e))))
                     (message "")))))))

"Whether `pos` is in a string or a comment."
(define in-text? (->* (rope int) bool)
  (lambda (t pos)
    (let ((st (scan-at t pos))) (or (>= (extract st string-at) 0) (extract st comment)))))

"The match of the paren next to point, for showing: before point a close,
its open; at point an open, its close. -1 if neither."
(define paren-match (->* (rope int) int)
  (lambda (t p)
    (let ((n (rope-length t)))
      (cond ((and (> p 0) (char-in? (rope-ref t (- p 1)) ")]") (not (in-text? t (- p 1))))
             (let ((st (scan-at t (- p 1))))
               (if (pair? (extract st opens)) (car (extract st opens)) -1)))
            ((and (< p n) (char-in? (rope-ref t p) "([") (not (in-text? t p)))
             (let ((e (sexp-end t p))) (if (< e 0) -1 (- e 1))))
            (else -1)))))

;;; ------------------------------------------------------------ paredit

"Paredit's keys are on, in FX-26 buffers (M-x paredit-mode)."
(define paredit-on (ref bool @ed) (new #f))

(define* edit-text (subr spin (buffer int int string int) outcome)
  ;; `b` with `from`..`to` replaced by `s`, point at `p`.
  (lambda (b from to s p)
    (let ((t (extract b text)))
      (done (with-text b (rope-insert (rope-delete t from to) from s) p)))))

"(: a pair, point between; in a string or comment, just the character."
(define* paredit-open (subr pure () command)
  (lambda ()
    (lambda ((b buffer))
      (let ((t (extract b text)) (p (extract b point)))
        (if (in-text? t p)
            (edit-text b p p "(" (+ p 1))
            (edit-text b p p "()" (+ p 1)))))))

"): past the close of the list point is in, the spaces before it gone."
(define* paredit-close (subr pure () command)
  (lambda ()
    (lambda ((b buffer))
      (let* ((t (extract b text)) (p (extract b point)))
        (if (in-text? t p)
            (edit-text b p p ")" (+ p 1))
            (let ((open (up-list t p)))
              (if (< open 0)
                  (say b "Not in a list")
                  (let ((e (sexp-end t open)))
                    (if (< e 0)
                        (say b "The list is not closed")
                        ;; Spaces between the last item and the close, gone.
                        (let* ((close (- e 1))
                               (keep (letrec ((back (->* (int) int)
                                                (lambda (i) (if (and (> i (+ open 1)) (char-whitespace? (rope-ref t (- i 1)))) (back (- i 1)) i))))
                                       (back close))))
                          (if (< keep close)
                              (done (with-text b (rope-delete t keep close) (+ keep 1)))
                              (done (with-point b e)))))))))))))

"\": a pair; in a string, past its end if at it, else an escaped quote."
(define* paredit-doublequote (subr pure () command)
  (lambda ()
    (lambda ((b buffer))
      (let* ((t (extract b text)) (p (extract b point)) (st (scan-at t p)))
        (cond ((extract st comment) (edit-text b p p "\"" (+ p 1)))
              ((>= (extract st string-at) 0)
               (if (and (< p (rope-length t)) (char=? (rope-ref t p) #\"))
                   (done (with-point b (+ p 1)))
                   (edit-text b p p "\\\"" (+ p 2))))
              (else (edit-text b p p "\"\"" (+ p 1))))))))

"DEL keeping the balance: an empty pair goes as one; a delimiter of a pair
that is not empty is gone back over."
(define* paredit-backward-delete (subr pure () command)
  (lambda ()
    (lambda ((b buffer))
      (let* ((t (extract b text)) (p (extract b point)) (n (rope-length t)))
        (if (= p 0)
            (say b "Beginning of buffer")
            (let ((c (rope-ref t (- p 1))) (after (if (< p n) (rope-ref t p) #\space)))
              (cond ((and (char=? c #\") (char=? after #\") (in-text? t p))
                     ;; An empty string, as one.
                     (edit-text b (- p 1) (+ p 1) "" (- p 1)))
                    ((in-text? t (- p 1))
                     ;; In a string: an empty one goes; its opening quote is gone back over.
                     (cond ((and (char=? c #\") (char=? after #\")) (edit-text b (- p 1) (+ p 1) "" (- p 1)))
                           ((char=? c #\") (done (with-point b (- p 1))))
                           (else (edit-text b (- p 1) p "" (- p 1)))))
                    ((and (char-in? c "([") (char-in? after ")]")) (edit-text b (- p 1) (+ p 1) "" (- p 1)))
                    ((char-in? c "([)]\"") (done (with-point b (- p 1))))
                    (else (edit-text b (- p 1) p "" (- p 1))))))))))

"C-d keeping the balance, as DEL does backwards."
(define* paredit-forward-delete (subr pure () command)
  (lambda ()
    (lambda ((b buffer))
      (let* ((t (extract b text)) (p (extract b point)) (n (rope-length t)))
        (if (>= p n)
            (say b "End of buffer")
            (let ((c (rope-ref t p)) (before (if (> p 0) (rope-ref t (- p 1)) #\space)))
              (cond ((and (char-in? c ")]") (char-in? before "([")) (edit-text b (- p 1) (+ p 1) "" (- p 1)))
                    ((and (char=? c #\") (char=? before #\") (in-text? t p)) (edit-text b (- p 1) (+ p 1) "" (- p 1)))
                    ((and (char-in? c "([)]\"") (not (in-text? t p))) (done (with-point b (+ p 1))))
                    (else (edit-text b p (+ p 1) "" p)))))))))

"C-k keeping the balance: to the end of the line, or of the list point is
in if it closes first."
(define* paredit-kill (subr pure () command)
  (lambda ()
    (lambda ((b buffer))
      (let* ((t (extract b text)) (p (extract b point))
             (eol (rope-line-end t (rope-line-of t p)))
             (open (up-list t p))
             (close (if (< open 0) -1 (- (sexp-end t open) 1)))
             (to (if (and (>= close 0) (< close eol)) close eol))
             ;; Not into a sexp that goes on past the line: whole sexps only.
             (to (letrec ((go (->* (int) int)
                            (lambda (i)
                              (let ((j (skip-space t i)))
                                (if (>= j to) to
                                    (let ((e (sexp-end t j))) (if (or (< e 0) (> e to)) (max i (min e (rope-length t))) (go e))))))))
                   (if (= p eol) (min (rope-length t) (+ eol 1)) (go p)))))
        (if (<= to p)
            (say b "Nothing to kill here")
            (product (buffer (with-text b (rope-delete t p to) p))
                     (cmds (list (kill-push (rope-substring t p to))))
                     (message "")))))))

;;; ------------------------------------------------------------ structural edits

"C-right: the list point is in takes in the sexp after it."
(define* slurp-forward (subr pure () command)
  (lambda ()
    (lambda ((b buffer))
      (let* ((t (extract b text)) (p (extract b point)) (open (up-list t p)))
        (if (< open 0) (say b "Not in a list")
            (let* ((e (sexp-end t open)) (next (if (< e 0) -1 (forward-sexp t e))))
              (if (< next 0) (say b "Nothing after the list to take in")
                  (let ((close (rope-substring t (- e 1) e)))
                    ;; The close moved to after the next sexp.
                    (done (with-text b (rope-insert (rope-delete t (- e 1) e) (- next 1) close) p))))))))))

"C-left: the list point is in gives out its last sexp."
(define* barf-forward (subr pure () command)
  (lambda ()
    (lambda ((b buffer))
      (let* ((t (extract b text)) (p (extract b point)) (open (up-list t p)))
        (if (< open 0) (say b "Not in a list")
            (let* ((e (sexp-end t open)) (cs (children t (+ open 1) (if (< e 0) (rope-length t) e))))
              (if (or (< e 0) (null? cs)) (say b "Nothing in the list to give out")
                  (let* ((last (letrec ((l (->* (sexp-spans) sexp-span) (lambda (cs) (if (null? (cdr cs)) (car cs) (l (cdr cs))))))
                                 (l cs)))
                         (before (letrec ((back (->* (int) int)
                                            (lambda (i) (if (and (> i (+ open 1)) (char-whitespace? (rope-ref t (- i 1)))) (back (- i 1)) i))))
                                   (back (extract last start))))
                         (close (rope-substring t (- e 1) e))
                         (t2 (rope-insert (rope-delete t (- e 1) e) before close)))
                    (done (with-text b t2 (min p before)))))))))))

"M-s: the list point is in, its parens taken away."
(define* splice-sexp (subr pure () command)
  (lambda ()
    (lambda ((b buffer))
      (let* ((t (extract b text)) (p (extract b point)) (open (up-list t p)))
        (if (< open 0) (say b "Not in a list")
            (let ((e (sexp-end t open)))
              (if (< e 0) (say b "The list is not closed")
                  (done (with-text b (rope-delete (rope-delete t (- e 1) e) open (+ open 1)) (- p 1))))))))))

"M-r: the sexp at point in place of the list it is in."
(define* raise-sexp (subr pure () command)
  (lambda ()
    (lambda ((b buffer))
      (let* ((t (extract b text)) (p (skip-space (extract b text) (extract b point))) (open (up-list t p)))
        (if (< open 0) (say b "Not in a list")
            (let ((e (sexp-end t open)) (here (sexp-end t p)))
              (if (or (< e 0) (< here 0)) (say b "Nothing to raise")
                  (done (with-text b (rope-insert (rope-delete t open e) open (rope-substring t p here)) open)))))))))

"M-(: the sexp after point wrapped in a list, point inside before it."
(define* wrap-round (subr pure () command)
  (lambda ()
    (lambda ((b buffer))
      (let* ((t (extract b text)) (p (skip-space (extract b text) (extract b point))) (e (sexp-end t p)))
        (if (< e 0)
            (edit-text b p p "()" (+ p 1))
            (done (with-text b (rope-insert (rope-insert t e ")") p "(") (+ p 1))))))))
