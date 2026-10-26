;;; buffer.fx: buffers, and the commands that edit them (cahoots'
;;; `(yank actor buffer)` and `(yank actor commands)`, c337e2a).
;;;
;;; A buffer is an actor whose state is a value: its text a persistent
;;; rope, its point and mark, and its undo history -- the texts it had,
;;; which share most of themselves with the text it has. A command is code
;;; run in a turn of the buffer's: a procedure from the buffer to the
;;; buffer after it, what to do, and a message for the echo area.

"What a buffer's subscribers (its views) are sent after each command."
(define-type snapshot
  (productof (name string) (text rope) (point int) (mark int) (revision int) (modified bool)
             (highlight-start int) (highlight-end int)))
(define-type subscriber (subr turn-eff (snapshot) cmd))
(define-type subscription (productof (id int) (send subscriber)))
"A text the buffer had, and its point then."
(define-type undo-entry (productof (text rope) (point int)))
(define-type buffer
  (productof (name string) (file string) (text rope) (point int)
             (mark int)                                 ; -1: none set
             (revision int) (modified bool)
             (undo (listof undo-entry acyclic))
             (subscribers (listof subscription acyclic))
             (highlight-start int) (highlight-end int)  ; a match shown (C-s); -1: none
             (origin int)))                             ; where a search began
"What a command gives: the buffer after it, what to do, and a message for
the echo area (\"\" for none)."
(define-type outcome (productof (buffer buffer) (cmds cmds) (message string)))
(define-type command (subr turn-eff (buffer) outcome))

(define* new-buffer (subr pure (string string rope) buffer)
  (lambda (name file text)
    (product (name name) (file file) (text text) (point 0) (mark -1) (revision 0) (modified #f)
             (undo nil) (subscribers nil) (highlight-start -1) (highlight-end -1) (origin 0))))

(define* snapshot-of (subr pure (buffer) snapshot)
  (lambda (b)
    (product (name (extract b name)) (text (extract b text)) (point (extract b point))
             (mark (extract b mark)) (revision (extract b revision)) (modified (extract b modified))
             (highlight-start (extract b highlight-start)) (highlight-end (extract b highlight-end)))))

"`b` with all its fields given."
(define* buffer-of
  (subr pure (buffer rope int int int bool (listof undo-entry acyclic) (listof subscription acyclic)) buffer)
  (lambda (b text point mark revision modified undo subs)
    (product (name (extract b name)) (file (extract b file)) (text text) (point point) (mark mark)
             (revision revision) (modified modified) (undo undo) (subscribers subs)
             (highlight-start (extract b highlight-start)) (highlight-end (extract b highlight-end))
             (origin (extract b origin)))))

"`b` with a match shown from `hs` to `he` (-1: none), and a search's origin."
(define* with-search (subr pure (buffer int int int) buffer)
  (lambda (b hs he origin)
    (product (name (extract b name)) (file (extract b file)) (text (extract b text)) (point (extract b point))
             (mark (extract b mark)) (revision (extract b revision)) (modified (extract b modified))
             (undo (extract b undo)) (subscribers (extract b subscribers))
             (highlight-start hs) (highlight-end he) (origin origin))))

"How many texts the undo history keeps."
(define undo-limit int 1000)

(define* take (subr pure (int (listof undo-entry acyclic)) (listof undo-entry acyclic))
  (lambda (n l)
    (letrec ((go (subr pure (int (listof undo-entry acyclic)) (listof undo-entry acyclic))
               (lambda (n l) (if (or (<= n 0) (null? l)) nil (cons (car l) (go (- n 1) (cdr l)))))))
      (go n l))))

"`b` with text `t` and point `p`, its old text kept for undo."
(define* with-text (subr pure (buffer rope int) buffer)
  (lambda (b t p)
    (buffer-of b t (max 0 (min p (rope-length t)))
               (min (extract b mark) (rope-length t))
               (+ 1 (extract b revision)) #t
               (cons (product (text (extract b text)) (point (extract b point)))
                     (take undo-limit (extract b undo)))
               (extract b subscribers))))

(define* with-point (subr pure (buffer int) buffer)
  (lambda (b p)
    (buffer-of b (extract b text) (max 0 (min p (rope-length (extract b text)))) (extract b mark)
               (extract b revision) (extract b modified) (extract b undo) (extract b subscribers))))

(define* with-mark (subr pure (buffer int) buffer)
  (lambda (b m)
    (buffer-of b (extract b text) (extract b point) m (extract b revision) (extract b modified)
               (extract b undo) (extract b subscribers))))

(define* done (subr pure (buffer) outcome)
  (lambda (b) (product (buffer b) (cmds nil) (message ""))))

(define* say (subr pure (buffer string) outcome)
  (lambda (b m) (product (buffer b) (cmds nil) (message m))))

;;; ------------------------------------------------------------ the kill ring

"The kill ring, newest first. Kills push onto it after their turn; yanks
read it in theirs."
(define kill-ring (ref strings @ed) (new nil))

(define* kill-push (subr pure (string) cmd)
  (lambda (s) (lambda () (set kill-ring (cons s (get kill-ring))))))

;;; ------------------------------------------------------------ commands

(define* insert-string (subr spin (string) command)
  (lambda (s)
    (lambda ((b buffer))
      (done (with-text b (rope-insert (extract b text) (extract b point) s)
                       (+ (extract b point) (string-length s)))))))

(define* delete-backward (subr pure () command)
  (lambda ()
    (lambda ((b buffer))
      (let ((p (extract b point)))
        (if (= p 0)
            (say b "Beginning of buffer")
            (done (with-text b (rope-delete (extract b text) (- p 1) p) (- p 1))))))))

(define* delete-forward (subr pure () command)
  (lambda ()
    (lambda ((b buffer))
      (let ((p (extract b point)))
        (if (>= p (rope-length (extract b text)))
            (say b "End of buffer")
            (done (with-text b (rope-delete (extract b text) p (+ p 1)) p)))))))

(define* move-by (subr pure (int) command)
  (lambda (n)
    (lambda ((b buffer))
      (let ((p (+ (extract b point) n)))
        (cond ((< p 0) (say (with-point b 0) "Beginning of buffer"))
              ((> p (rope-length (extract b text))) (say (with-point b p) "End of buffer"))
              (else (done (with-point b p))))))))

(define* line-start (subr pure () command)
  (lambda ()
    (lambda ((b buffer))
      (let ((t (extract b text)))
        (done (with-point b (rope-line-start t (rope-line-of t (extract b point)))))))))

(define* line-end (subr pure () command)
  (lambda ()
    (lambda ((b buffer))
      (let ((t (extract b text)))
        (done (with-point b (rope-line-end t (rope-line-of t (extract b point)))))))))

(define* buffer-start (subr pure () command)
  (lambda () (lambda ((b buffer)) (done (with-mark (with-point b 0) (extract b point))))))

(define* buffer-end (subr pure () command)
  (lambda ()
    (lambda ((b buffer)) (done (with-mark (with-point b (rope-length (extract b text))) (extract b point))))))

"Down `n` lines (up, if negative), keeping the column where the line is
long enough."
(define* move-lines (subr pure (int) command)
  (lambda (n)
    (lambda ((b buffer))
      (let* ((t (extract b text))
             (p (extract b point))
             (line (rope-line-of t p))
             (column (- p (rope-line-start t line)))
             (target (max 0 (min (- (rope-line-count t) 1) (+ line n)))))
        (if (= target line)
            (say b (if (< n 0) "Beginning of buffer" "End of buffer"))
            (done (with-point b (min (+ (rope-line-start t target) column) (rope-line-end t target)))))))))

(define* word-char? (subr pure (char) bool)
  (lambda (c) (or (char-alphabetic? c) (char-numeric? c))))

"Over the next word (the one before, if `dir` is -1)."
(define* move-word (subr pure (int) command)
  (lambda (dir)
    (lambda ((b buffer))
      (let* ((t (extract b text))
             (n (rope-length t)))
        (letrec ((at (subr spin (int) bool)                   ; a word character at the step from p?
                   (lambda (p) (let ((i (if (> dir 0) p (- p 1))))
                                 (and (>= i 0) (< i n) (word-char? (rope-ref t i))))))
                 (in-range (subr pure (int) bool)
                   (lambda (p) (if (> dir 0) (< p n) (> p 0))))
                 (skip-non (subr spin (int) int)
                   (lambda (p) (if (and (in-range p) (not (at p))) (skip-non (+ p dir)) p)))
                 (skip-word (subr spin (int) int)
                   (lambda (p) (if (and (in-range p) (at p)) (skip-word (+ p dir)) p))))
          (done (with-point b (skip-word (skip-non (extract b point))))))))))

"Set the mark at point."
(define* set-mark (subr pure () command)
  (lambda () (lambda ((b buffer)) (say (with-mark b (extract b point)) "Mark set"))))

"Point and mark swapped."
(define* exchange-point-and-mark (subr pure () command)
  (lambda ()
    (lambda ((b buffer))
      (if (< (extract b mark) 0)
          (say b "No mark set in this buffer")
          (done (with-mark (with-point b (extract b mark)) (extract b point)))))))

"The region's text killed: taken out, and put on the kill ring."
(define* kill-region (subr pure () command)
  (lambda ()
    (lambda ((b buffer))
      (let ((m (extract b mark)) (p (extract b point)))
        (if (< m 0)
            (say b "The mark is not set now, so there is no region")
            (let ((from (min m p)) (to (max m p)))
              (product (buffer (with-mark (with-text b (rope-delete (extract b text) from to) from) from))
                       (cmds (list (kill-push (rope-substring (extract b text) from to))))
                       (message ""))))))))

"The region's text copied to the kill ring."
(define* copy-region (subr pure () command)
  (lambda ()
    (lambda ((b buffer))
      (let ((m (extract b mark)) (p (extract b point)))
        (if (< m 0)
            (say b "The mark is not set now, so there is no region")
            (product (buffer b)
                     (cmds (list (kill-push (rope-substring (extract b text) (min m p) (max m p)))))
                     (message "Copied")))))))

"The rest of the line killed, or the newline if at its end."
(define* kill-line (subr pure () command)
  (lambda ()
    (lambda ((b buffer))
      (let* ((t (extract b text))
             (p (extract b point))
             (end (rope-line-end t (rope-line-of t p)))
             (to (if (= p end) (min (rope-length t) (+ p 1)) end)))
        (if (= p to)
            (say b "End of buffer")
            (product (buffer (with-text b (rope-delete t p to) p))
                     (cmds (list (kill-push (rope-substring t p to))))
                     (message "")))))))

"The newest kill inserted at point, the mark left before it."
(define* yank (subr pure () command)
  (lambda ()
    (lambda ((b buffer))
      (let ((ring (get kill-ring)))
        (if (null? ring)
            (say b "Kill ring is empty")
            (let ((p (extract b point)) (s (car ring)))
              (done (with-mark (with-text b (rope-insert (extract b text) p s) (+ p (string-length s))) p))))))))

"The text as it was before the last change."
(define* undo (subr pure () command)
  (lambda ()
    (lambda ((b buffer))
      (let ((u (extract b undo)))
        (if (null? u)
            (say b "No further undo information")
            (say (buffer-of b (extract (car u) text) (extract (car u) point) (extract b mark)
                            (+ 1 (extract b revision)) #t (cdr u) (extract b subscribers))
                 "Undo"))))))

"Save: the buffer's text to its file, after the turn."
(define* save-buffer (subr pure () command)
  (lambda ()
    (lambda ((b buffer))
      (let ((file (extract b file)))
        (if (string=? file "")
            (say b "This buffer has no file")
            (let ((text (rope->string (extract b text))))
              (product
               (buffer (buffer-of b (extract b text) (extract b point) (extract b mark) (extract b revision)
                                  #f (extract b undo) (extract b subscribers)))
               (cmds (list (lambda () (begin (write-file file (string->utf8 text)) #u))))
               (message (string-append "Wrote " file)))))))))

(define* keyboard-quit (subr pure () command)
  (lambda () (lambda ((b buffer)) (say (with-mark b -1) "Quit"))))

"For trying a failing command: takes the car of the empty list."
(define* fail-on-purpose (subr pure () command)
  (lambda () (lambda ((b buffer)) (done (with-point b (car (the (listof int acyclic) nil)))))))

;;; ------------------------------------------------------------ searching

"Where `needle` is next in `hay` from `from` on, or -1."
(define* search-forward-in (subr pure (string string int) int)
  (lambda (hay needle from)
    (if (> from (string-length hay)) -1 (string-search hay needle from))))

"Where `needle` is last in `hay` ending at or before `limit`, or -1."
(define* search-backward-in (subr spin (string string int) int)
  (lambda (hay needle limit)
    (letrec ((go (subr spin (int int) int)
               (lambda (from best)
                 (let ((i (search-forward-in hay needle from)))
                   (if (or (< i 0) (> (+ i (string-length needle)) limit)) best (go (+ i 1) i))))))
      (go 0 -1))))

"What a search tells the frame: whether it failed."
(define-type search-report (subr turn-eff (bool) cmd))

"A search begun at point: point kept as where to go back to on C-g."
(define* isearch-begin (subr pure () command)
  (lambda () (lambda ((b buffer)) (done (with-search b -1 -1 (extract b point))))))

"Search for `needle`, forward or back. `again`: for the next match after
the one shown (C-s, C-r again), not the one at it (a character typed).
Point goes to the match's end (its start, going back), and it is shown."
(define* isearch-step (subr pure (string bool bool search-report) command)
  (lambda (needle forward again report)
    (lambda ((b buffer))
      (let* ((hay (rope->string (extract b text)))
             (n (string-length needle))
             (hs (extract b highlight-start))
             (shown (>= hs 0))
             (p (extract b point))
             (origin (extract b origin))
             (i (cond ((= n 0) -1)
                      (forward (search-forward-in hay needle (cond (again p) (shown hs) (else p))))
                      (else (search-backward-in hay needle
                                                (cond (again (if shown (- (+ hs n) 1) p))
                                                      (shown (+ hs n))
                                                      (else (+ p n))))))))
        (if (< i 0)
            (product (buffer (if (= n 0) (with-search b -1 -1 origin) b)) (cmds (list (report (> n 0)))) (message ""))
            (product (buffer (with-search (with-point b (if forward (+ i n) i)) i (+ i n) origin))
                     (cmds (list (report #f)))
                     (message "")))))))

"The search ended: point stays, the mark set where it began."
(define* isearch-exit (subr pure () command)
  (lambda ()
    (lambda ((b buffer)) (done (with-mark (with-search b -1 -1 0) (extract b origin))))))

"Back where the search began, nothing shown: before searching again."
(define* isearch-abort-quietly (subr pure () command)
  (lambda ()
    (lambda ((b buffer)) (done (with-point (with-search b -1 -1 (extract b origin)) (extract b origin))))))

"The search given up: point back where it began."
(define* isearch-abort (subr pure () command)
  (lambda ()
    (lambda ((b buffer)) (say (with-point (with-search b -1 -1 0) (extract b origin)) "Quit"))))

;;; ------------------------------------------------------------ messages to a buffer

"A subscriber added, and sent a snapshot now."
(define* subscribe (subr pure (int subscriber) (msg buffer))
  (lambda (id s)
    (lambda ((b buffer))
      (reply-with (buffer-of b (extract b text) (extract b point) (extract b mark) (extract b revision)
                             (extract b modified) (extract b undo)
                             (cons (product (id id) (send s)) (extract b subscribers)))
                  (list (s (snapshot-of b)))))))

"The subscriber `id` taken off."
(define* unsubscribe (subr pure (int) (msg buffer))
  (lambda (id)
    (lambda ((b buffer))
      (same (buffer-of b (extract b text) (extract b point) (extract b mark) (extract b revision)
                       (extract b modified) (extract b undo)
                       (letrec ((go (subr spin ((listof subscription acyclic)) (listof subscription acyclic))
                                  (lambda (ss) (cond ((null? ss) nil)
                                                     ((= (extract (car ss) id) id) (go (cdr ss)))
                                                     (else (cons (car ss) (go (cdr ss))))))))
                         (go (extract b subscribers))))))))

"Each subscriber's command, sent `b`'s snapshot."
(define* notify (subr turn-eff (buffer) cmds)
  (lambda (b)
    (let ((snap (snapshot-of b)))
      (letrec ((go (subr turn-eff ((listof subscription acyclic)) cmds)
                 (lambda (ss) (if (null? ss) nil (cons ((extract (car ss) send) snap) (go (cdr ss)))))))
        (go (extract b subscribers))))))
