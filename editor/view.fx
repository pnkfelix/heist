;;; view.fx: a window's view of a buffer (cahoots' `(yank actor view)`
;;; and `(yank actor columns)`, c337e2a).
;;;
;;; A view is an actor of the display class: it runs only when no key
;;; waits, and is told each snapshot of its buffer with one key, so of a
;;; burst of keys it lays out only the last. It keeps the last snapshot,
;;; to lay out again when its window changes size. What it shows -- rows,
;;; a mode line, and where the cursor is -- it reports through a closure
;;; the frame gave it, so it need not know the frame.

"A view's report: its window, its rows, its mode line's text, and the
cursor's row and column in it."
(define-type reporter (subr turn-eff (int rows string int int) cmd))
(define-type view
  (productof (window int) (report reporter) (top int) (height int) (width int)
             (hscroll int)                        ; the first column shown
             (last (sumof (none unit) (some snapshot)))))

(define tab-width int 8)

"Where the character at `i` of `s` shows: the columns before it, tabs
taken to the next stop."
(define* column-of (subr spin (string int) int)
  (lambda (s i)
    (letrec ((go (subr spin (int int) int)
               (lambda (j col)
                 (if (>= j i)
                     col
                     (go (+ j 1) (if (char=? (string-ref s j) #\tab)
                                     (* tab-width (+ 1 (quotient col tab-width)))
                                     (+ col 1)))))))
      (go 0 0))))

"`s` as it shows: each tab as spaces to the next stop."
(define* expand-tabs (subr spin (string) string)
  (lambda (s)
    (letrec ((go (subr spin (int int (listof char acyclic)) (listof char acyclic))
               ;; From `j`, at column `col`, the characters shown, last first.
               (lambda (j col acc)
                 (cond ((>= j (string-length s)) acc)
                       ((char=? (string-ref s j) #\tab)
                        (let ((next (* tab-width (+ 1 (quotient col tab-width)))))
                          (go (+ j 1) next (pad (- next col) acc))))
                       (else (go (+ j 1) (+ col 1) (cons (string-ref s j) acc))))))
             (pad (subr spin (int (listof char acyclic)) (listof char acyclic))
               (lambda (n acc) (if (<= n 0) acc (pad (- n 1) (cons #\space acc))))))
      (list->string (reverse (go 0 0 nil))))))

"The spans of line `text` (from `ls` to `le` in the buffer) that show the
snapshot's highlighted match."
(define* highlight-spans (subr spin (snapshot int int string) spans)
  (lambda (snap ls le text)
    (let ((hs (max (extract snap highlight-start) ls))
          (he (min (extract snap highlight-end) le)))
      (if (and (>= (extract snap highlight-start) 0) (< hs he))
          (list (product (start (column-of text (- hs ls))) (end (column-of text (- he ls))) (face 'isearch)))
          nil))))

"The faces of `fs` (sorted by start) that reach into `from`..`to`."
(define* faces-between (subr spin (text-faces int int) text-faces)
  (lambda (fs from to)
    (cond ((null? fs) nil)
          ((>= (extract (car fs) start) to) nil)
          ((<= (extract (car fs) end) from) (faces-between (cdr fs) from to))
          (else (cons (car fs) (faces-between (cdr fs) from to))))))

(define* append-faces (subr spin (text-faces text-faces) text-faces)
  (lambda (a b) (if (null? a) b (cons (car a) (append-faces (cdr a) b)))))
(define* merge-by-start (subr spin (text-faces text-faces) text-faces)
  (lambda (a b)
    (cond ((null? a) b)
          ((null? b) a)
          ((<= (extract (car a) start) (extract (car b) start)) (cons (car a) (merge-by-start (cdr a) b)))
          (else (cons (car b) (merge-by-start a (cdr b)))))))

"Faces `top` laid over faces `base` (both sorted, positions in the text):
where they overlap, `top`'s win, and `base`'s are cut around them."
(define* overlay-faces (subr spin (text-faces text-faces) text-faces)
  (lambda (base top)
    (letrec ((cut (subr spin (text-face text-faces) text-faces)
                    ;; `f`'s pieces outside every face of `top`.
                    (lambda (f top)
                      (cond ((null? top) (list f))
                            ((<= (extract (car top) end) (extract f start)) (cut f (cdr top)))
                            ((>= (extract (car top) start) (extract f end)) (list f))
                            (else
                             (append-faces
                              (if (< (extract f start) (extract (car top) start))
                                  (list (product (start (extract f start)) (end (extract (car top) start)) (face (extract f face))))
                                  nil)
                              (if (> (extract f end) (extract (car top) end))
                                  (cut (product (start (extract (car top) end)) (end (extract f end)) (face (extract f face))) (cdr top))
                                  nil))))))
             (all (subr spin (text-faces) text-faces)
               (lambda (bs) (if (null? bs) nil (append-faces (cut (car bs) top) (all (cdr bs)))))))
      (merge-by-start (all base) top))))

"The spans of line `text` (from `ls` to `le` in the buffer): the faces `fs`
the syntax gave, under the uses marked (M-?) and the parens matched, under
a search's match."
(define* line-spans (subr spin (snapshot text-faces text-faces int int string) spans)
  (lambda (snap fs over ls le text)
    (let ((hl (highlight-spans snap ls le text)))
      (if (pair? hl)
          hl
          (letrec ((go (subr spin (text-faces) spans)
                     (lambda (fs)
                       (if (null? fs)
                           nil
                           (let* ((f (car fs))
                                  (a (max ls (extract f start)))
                                  (b (min le (extract f end))))
                             (if (< a b)
                                 (cons (product (start (column-of text (- a ls))) (end (column-of text (- b ls)))
                                                (face (extract f face)))
                                       (go (cdr fs)))
                                 (go (cdr fs))))))))
            (go (overlay-faces (faces-between fs ls (+ le 1)) (faces-between over ls (+ le 1)))))))))

"Row `w` wide of a line shown as `shown` with spans `ss`, from column `hs`."
(define* scrolled-row (subr spin (int string spans int) row)
  (lambda (w shown ss hs)
    (if (= hs 0)
        (make-row w shown ss)
        (make-row w
                  (if (> (string-length shown) hs) (substring shown hs (string-length shown)) "")
                  (letrec ((go (subr spin (spans) spans)
                             (lambda (ss)
                               (cond ((null? ss) nil)
                                     ((<= (extract (car ss) end) hs) (go (cdr ss)))
                                     (else (cons (product (start (max 0 (- (extract (car ss) start) hs)))
                                                          (end (- (extract (car ss) end) hs))
                                                          (face (extract (car ss) face)))
                                                 (go (cdr ss))))))))
                    (go ss))))))

"`v`'s rows for snapshot `snap`, scrolled to show point: the view after,
and the command that reports it."
(define* lay-out (subr turn-eff (view snapshot) (reply view))
  (lambda (v snap)
    (let* ((t (extract snap text))
           (h (max 1 (extract v height)))
           (w (max 1 (extract v width)))
           (pline (rope-line-of t (extract snap point)))
           (ann (extract snap annotation))
           ;; Point off the window: recentered, as Emacs does.
           (top (if (or (< pline (extract v top)) (>= pline (+ (extract v top) h)))
                    (max 0 (- pline (quotient h 2)))
                    (extract v top)))
           (start (rope-line-start t pline))
           (line-text (rope-substring t start (rope-line-end t pline)))
           (true-column (column-of line-text (- (extract snap point) start)))
           ;; The cursor off the window sideways: scrolled to put it in the middle.
           (hs (if (and (>= true-column (extract v hscroll)) (< true-column (+ (extract v hscroll) (- w 1))))
                   (extract v hscroll)
                   (if (< true-column (- w 1)) 0 (- true-column (quotient w 2)))))
           (column (- true-column hs))
           ;; Over the syntax's faces: the uses marked, and the paren next to
           ;; point with its match.
           (pm (paren-match t (extract snap point)))
           (here (cond ((< pm 0) -1)
                       ((< pm (extract snap point)) (- (extract snap point) 1))
                       (else (extract snap point))))
           (over (merge-by-start (extract snap marks)
                                 (if (< pm 0) nil
                                     (list (product (start (min pm here)) (end (+ 1 (min pm here))) (face 'paren))
                                           (product (start (max pm here)) (end (+ 1 (max pm here))) (face 'paren))))))
           (shown-from (rope-line-start t top))
           (shown-faces (faces-between (extract ann faces) shown-from
                                       (rope-line-end t (min (- (rope-line-count t) 1) (+ top h)))))
           (lines (letrec ((go (subr turn-eff (int) rows)
                             (lambda (i)
                               (if (>= i h)
                                   nil
                                   (let ((n (+ top i)))
                                     (cons (if (< n (rope-line-count t))
                                               (let* ((ls (rope-line-start t n))
                                                      (le (rope-line-end t n))
                                                      (text (rope-substring t ls le)))
                                                 (scrolled-row w (expand-tabs text) (line-spans snap shown-faces over ls le text) hs))
                                               (blank-row w))
                                           (go (+ i 1))))))))
                    (go 0)))
           (mode (string-append (if (extract snap modified) "-**- " "---- ")
                                (extract snap name)
                                "   L" (int->string (+ pline 1))
                                (if (string=? (extract ann problem) "")
                                    ""
                                    (string-append "   ! " (extract ann problem) " (L"
                                                   (int->string (+ 1 (rope-line-of t (max 0 (extract ann problem-at)))))
                                                   ")"))))
           (v2 (product (window (extract v window)) (report (extract v report)) (top top)
                        (height (extract v height)) (width (extract v width)) (hscroll hs)
                        (last (sum some snap)))))
      (reply-with v2 (list ((extract v report) (extract v window) lines mode (- pline top) column))))))

"Message for a view: a snapshot of its buffer."
(define* view-snapshot (subr pure (snapshot) (msg view))
  (lambda (snap) (lambda ((v view)) (lay-out v snap))))

"Message for a view: its window's text area is now `h` rows by `w`."
(define* view-resize (subr pure (int int) (msg view))
  (lambda (h w)
    (lambda ((v view))
      (let ((v2 (product (window (extract v window)) (report (extract v report)) (top (extract v top))
                         (height h) (width w) (hscroll (extract v hscroll)) (last (extract v last)))))
        (tagcase (extract v last)
          (some snap (lay-out v2 snap))
          (none u (same v2)))))))

"A new view, of the display class, for window `id`."
(define* make-view (subr (alloc @ed) (int reporter int int) (actor view))
  (lambda (id report h w)
    (spawn-actor (string-append "view " (int->string id))
                 (product (window id) (report report) (top 0) (height h) (width w) (hscroll 0)
                          (last (the (sumof (none unit) (some snapshot)) (sum none #u)))))))
