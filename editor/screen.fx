;;; screen.fx: what the terminal should show, and getting it there
;;; (yank's `(yank screen)`, cahoots c337e2a, as values).
;;;
;;; A screen is rows of text, each with spans of faces, and a cursor.
;;; Unlike yank's, it is immutable: a view gives the frame its rows as
;;; values, the frame puts them together, and `screen-update` compares the
;;; new screen with the last one shown and gives the escape sequences that
;;; redraw only the rows that differ, as one string to write.
;;;
;;; Faces are symbols. `face-sgr` gives the SGR parameters that draw one
;;; ("1" bold, "7" reverse, "38;5;n" a color).

(define-type face symbol)
"Columns `start` to `end` of a row, drawn in `face`."
(define-type span (productof (start int) (end int) (face face)))
(define-type spans (listof span acyclic))
"A row: exactly as many characters as the screen has columns, none a
control character; and its spans, in order, not overlapping. Columns no
span covers are in the default face."
(define-type row (productof (text string) (spans spans)))
(define-type rows (listof row acyclic))
(define-type screen (productof (height int) (width int) (rows rows) (cursor-row int) (cursor-column int)))

(hide
  (define-type strings (listof string acyclic))
  (define push (subr pure (string strings) strings) (lambda (x acc) (cons x acc)))

  ;; `c`, or a space if it is a control character: sent to the terminal
  ;; it would move the cursor.
  (define shown (subr pure (char) char)
    (lambda (c) (if (or (char<? c #\space) (char=? c #\delete)) #\space c)))

  (define spaces (subr spin (int) string)
    (lambda (n)
      (letrec ((go (subr spin (int (listof char acyclic)) (listof char acyclic))
                 (lambda (n acc) (if (<= n 0) acc (go (- n 1) (cons #\space acc))))))
        (list->string (go n nil)))))

  (define span=? (subr pure (span span) bool)
    (lambda (a b)
      (and (= (extract a start) (extract b start)) (= (extract a end) (extract b end))
           (symbol=? (extract a face) (extract b face)))))

  (define spans=? (subr spin (spans spans) bool)
    (lambda (a b)
      (cond ((null? a) (null? b))
            ((null? b) #f)
            (else (and (span=? (car a) (car b)) (spans=? (cdr a) (cdr b)))))))

  (define row=? (subr spin (row row) bool)
    (lambda (a b)
      (and (string=? (extract a text) (extract b text)) (spans=? (extract a spans) (extract b spans)))))

  (define move-to (subr pure (int int) string)
    (lambda (row col)
      (string-append "\x1b;[" (int->string (+ row 1)) ";" (int->string (+ col 1)) "H")))

  (define sgr (subr pure (face) string)
    (lambda (f) (string-append "\x1b;[" (face-sgr f) "m")))

  ;; Row `r`'s pieces, onto `acc` (last first): the move to its start, then
  ;; its text a span at a time, each in its face.
  (define row-pieces (subr spin (int row strings) strings)
    (lambda (r rw acc)
      (let ((text (extract rw text)))
        (letrec ((go (subr spin (int spans strings) strings)
                   ;; From column `c`, the spans left.
                   (lambda (c ss acc)
                     (cond ((null? ss)
                            (if (< c (string-length text))
                                (push (substring text c (string-length text)) (push (sgr 'default) acc))
                                acc))
                           (else
                            (let* ((s (car ss))
                                   (from (max c (min (extract s start) (string-length text))))
                                   (to (max from (min (extract s end) (string-length text))))
                                   (acc (if (< c from)
                                            (push (substring text c from) (push (sgr 'default) acc))
                                            acc)))
                              (go to (cdr ss)
                                  (if (< from to)
                                      (push (substring text from to) (push (sgr (extract s face)) acc))
                                      acc))))))))
          (push "\x1b;[0m" (go 0 (extract rw spans) (push (move-to r 0) acc))))))))

"The SGR parameters of a face."
(define face-sgr (subr pure (face) string)
  (lambda (f)
    (case f
      ((default) "0")
      ((mode-line) "0;7")
      ((mode-line-inactive) "0;2;7")
      ((region) "0;7")
      ((isearch) "0;30;45")
      ((minibuffer-prompt) "0;1;36")
      ((error) "0;1;31")
      ((keyword) "0;1;35")
      ((comment) "0;2")
      ((string) "0;32")
      ((function-name) "0;1;34")
      ((type) "0;36")
      ((use) "0;4")
      ((binder) "0;1;4")
      ((paren) "0;1;7")
      (else "0"))))

"A row of `width` columns from `text`: cut or padded with spaces, control
characters shown as spaces; and its spans, cut to the width."
(define make-row (subr spin (int string spans) row)
  (lambda (width text ss)
    (let* ((n (string-length text))
           (fitted (if (>= n width) (substring text 0 width) (string-append text (spaces (- width n)))))
           (clean (list->string
                   (letrec ((go (subr spin (int (listof char acyclic)) (listof char acyclic))
                              (lambda (i acc) (if (< i 0) acc (go (- i 1) (cons (shown (string-ref fitted i)) acc))))))
                     (go (- (string-length fitted) 1) nil))))
           (cut (letrec ((go (subr spin (spans) spans)
                           (lambda (ss)
                             (cond ((null? ss) nil)
                                   ((>= (extract (car ss) start) width) nil)
                                   (else (cons (product (start (extract (car ss) start))
                                                        (end (min width (extract (car ss) end)))
                                                        (face (extract (car ss) face)))
                                               (go (cdr ss))))))))
                  (go ss))))
      (product (text clean) (spans cut)))))

"A row of `text` in one face."
(define face-row (subr spin (int string face) row)
  (lambda (width text f) (make-row width text (list (product (start 0) (end width) (face f))))))

(define blank-row (subr spin (int) row) (lambda (width) (make-row width "" nil)))

(define make-screen (subr pure (int int rows int int) screen)
  (lambda (h w rs cr cc)
    (product (height h) (width w) (rows rs) (cursor-row cr) (cursor-column cc))))

"The screen before anything is shown: 0 by 0."
(define no-screen screen (product (height 0) (width 0) (rows nil) (cursor-row 0) (cursor-column 0)))

"The escape sequences that change the terminal from showing `old` to
showing `new`; with `old` `no-screen`, all of `new`. \"\" if nothing
changed."
(define screen-update (subr spin (screen screen) string)
  (lambda (old new)
    (let* ((same-size (and (= (extract old height) (extract new height))
                           (= (extract old width) (extract new width))))
           (changed
            (letrec ((go (subr spin (int rows rows strings) strings)
                       (lambda (r news olds acc)
                         (if (null? news)
                             acc
                             (let ((same (and same-size (pair? olds) (row=? (car news) (car olds)))))
                               (go (+ r 1) (cdr news) (if (pair? olds) (cdr olds) olds)
                                   (if same acc (row-pieces r (car news) acc))))))))
              (go 0 (extract new rows) (extract old rows) nil)))
           (cursor-same (and (= (extract old cursor-row) (extract new cursor-row))
                             (= (extract old cursor-column) (extract new cursor-column)))))
      (if (and same-size (null? changed) cursor-same)
          ""
          (apply string-append
                 (append (list "\x1b;[?25l" (if same-size "" "\x1b;[0m\x1b;[2J"))
                         (reverse changed)
                         (list (move-to (extract new cursor-row) (extract new cursor-column))
                               "\x1b;[?25h")))))))
