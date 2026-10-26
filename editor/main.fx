;;; main.fx: the editor's first slice -- the terminal, and the scheduler
;;; between keys (cahoots' `(yank actor main)`), with one buffer, one view
;;; and a frame, as actors (core.fx).
;;;
;;;   fixpt run editor/main.fx -- FILE
;;;
;;; A key goes to the frame, which looks it up and sends the buffer the
;;; command bound to it, as code run in a turn of the buffer's; the buffer
;;; sends each subscriber (the view) a snapshot; the view lays out what it
;;; shows and sends that to the frame; the frame draws. A command that
;;; fails says why in the echo area, and leaves the buffer as it was.

(define-effect world (maxeff (io stdout) (io terminal) (io fs-read) (io fs-write)))
(define core ((proj (load-module "core.fx") @ed world)))
(import core spawn-actor tell tell! run-turns! turns-waiting? actor-state same reply-with
        on-turn-failure! (type actor msg reply cmd cmds) (effect turn-eff cmd-eff))
(define rope-m (load-module "rope.fx"))
(import rope-m empty-rope string->rope rope->string rope-length rope-insert rope-delete
        rope-substring rope-line-start rope-line-end rope-line-of rope-line-count (type rope))
(define keys-m (load-module "keys.fx"))
(import keys-m read-key key->string keys->string (type key keys byte-source))
(define screen-m (load-module "screen.fx"))
(import screen-m no-screen make-row face-row blank-row make-screen screen-update (type row rows screen span spans face))

;;; ------------------------------------------------------------ buffers

"What a buffer's subscribers are sent after each command: its text and
point at a revision."
(define-type snapshot
  (productof (name string) (text rope) (point int) (revision int) (modified bool)))
(define-type subscriber (subr turn-eff (snapshot) cmd))
(define-type buffer
  (productof (name string) (file string) (text rope) (point int) (revision int) (modified bool)
             (subscribers (listof subscriber acyclic))))
"What a command gives: the buffer after it, what to do, and a message for
the echo area (\"\" for none)."
(define-type outcome (productof (buffer buffer) (cmds cmds) (message string)))
(define-type command (subr turn-eff (buffer) outcome))

(define* snapshot-of (subr pure (buffer) snapshot)
  (lambda (b)
    (product (name (extract b name)) (text (extract b text)) (point (extract b point))
             (revision (extract b revision)) (modified (extract b modified)))))

(define* with-text (subr pure (buffer rope int) buffer)
  (lambda (b t p)
    (product (name (extract b name)) (file (extract b file)) (text t) (point p)
             (revision (+ 1 (extract b revision))) (modified #t) (subscribers (extract b subscribers)))))

(define* with-point (subr pure (buffer int) buffer)
  (lambda (b p)
    (product (name (extract b name)) (file (extract b file)) (text (extract b text))
             (point (max 0 (min p (rope-length (extract b text)))))
             (revision (extract b revision)) (modified (extract b modified))
             (subscribers (extract b subscribers)))))

(define* done (subr pure (buffer) outcome)
  (lambda (b) (product (buffer b) (cmds nil) (message ""))))

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
            (product (buffer b) (cmds nil) (message "Beginning of buffer"))
            (done (with-text b (rope-delete (extract b text) (- p 1) p) (- p 1))))))))

(define* delete-forward (subr pure () command)
  (lambda ()
    (lambda ((b buffer))
      (let ((p (extract b point)))
        (if (>= p (rope-length (extract b text)))
            (product (buffer b) (cmds nil) (message "End of buffer"))
            (done (with-text b (rope-delete (extract b text) p (+ p 1)) p)))))))

(define* move-by (subr pure (int) command)
  (lambda (n) (lambda ((b buffer)) (done (with-point b (+ (extract b point) n))))))

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

"Down `n` lines (up, if negative), keeping the column where the line is
long enough."
(define* move-lines (subr pure (int) command)
  (lambda (n)
    (lambda ((b buffer))
      (let* ((t (extract b text))
             (p (extract b point))
             (line (rope-line-of t p))
             (column (- p (rope-line-start t line)))
             (target (+ line n)))
        (if (or (< target 0) (>= target (rope-line-count t)))
            (product (buffer b) (cmds nil) (message (if (< n 0) "Beginning of buffer" "End of buffer")))
            (done (with-point b (min (+ (rope-line-start t target) column) (rope-line-end t target)))))))))

"Save: the buffer's text to its file, after the turn."
(define* save-buffer (subr pure () command)
  (lambda ()
    (lambda ((b buffer))
      (let ((file (extract b file)) (text (rope->string (extract b text))))
        (product
         (buffer (product (name (extract b name)) (file file) (text (extract b text)) (point (extract b point))
                          (revision (extract b revision)) (modified #f) (subscribers (extract b subscribers))))
         (cmds (list (lambda () (begin (write-file file (string->utf8 text)) #u))))
         (message (string-append "Wrote " file)))))))

(define* keyboard-quit (subr pure () command)
  (lambda () (lambda ((b buffer)) (product (buffer b) (cmds nil) (message "Quit")))))

"For testing a failing command: takes the car of the empty list."
(define* fail-on-purpose (subr pure () command)
  (lambda ()
    (lambda ((b buffer))
      (done (with-point b (car (the (listof int acyclic) nil)))))))

;;; ------------------------------------------------------------ the keymap

"What a key sequence does: a command run in the buffer, a prefix waiting
for more, quitting the editor, or nothing."
(define-type action (sumof (run command) (prefix unit) (exit unit) (undefined unit)))

(define* binding (subr spin (keys) action)
  (lambda (ks)
    (let ((name (keys->string ks)))
      (case name
        (("C-f" "<right>") (sum run (move-by 1)))
        (("C-b" "<left>") (sum run (move-by -1)))
        (("C-n" "<down>") (sum run (move-lines 1)))
        (("C-p" "<up>") (sum run (move-lines -1)))
        (("C-a" "<home>") (sum run (line-start)))
        (("C-e" "<end>") (sum run (line-end)))
        (("DEL") (sum run (delete-backward)))
        (("C-d" "<delete>") (sum run (delete-forward)))
        (("RET") (sum run (insert-string "\n")))
        (("TAB") (sum run (insert-string "  ")))
        (("C-g") (sum run (keyboard-quit)))
        (("C-x") (sum prefix #u))
        (("C-x C-s") (sum run (save-buffer)))
        (("C-x C-c") (sum exit #u))
        (("C-c !") (sum run (fail-on-purpose)))
        (("C-c") (sum prefix #u))
        (else
         (if (and (pair? ks) (null? (cdr ks)))
             (typecase (car ks)
               (char c (sum run (insert-string (char->string c))))
               (else y (sum undefined #u)))
             (sum undefined #u)))))))

;;; ------------------------------------------------------------ the frame

(define-type frame
  (productof (buffer (actor buffer)) (height int) (width int)
             (rows rows) (cursor-row int) (cursor-column int)
             (echo string) (prefix keys) (shown screen)))

"Set while the editor runs; the frame's C-x C-c clears it."
(define running (ref bool @ed) (new #t))

(define* frame-with (subr pure (frame rows int int string keys screen) frame)
  (lambda (f rs cr cc echo prefix shown)
    (product (buffer (extract f buffer)) (height (extract f height)) (width (extract f width))
             (rows rs) (cursor-row cr) (cursor-column cc) (echo echo) (prefix prefix) (shown shown))))

"The frame drawn: the view's rows, then the echo area, as a command that
writes what changed."
(define* draw (subr spin (frame) (reply frame))
  (lambda (f)
    (let* ((s (make-screen (extract f height) (extract f width)
                           (append (extract f rows) (list (make-row (extract f width) (extract f echo) nil)))
                           (extract f cursor-row) (extract f cursor-column)))
           (out (screen-update (extract f shown) s)))
      (reply-with (frame-with f (extract f rows) (extract f cursor-row) (extract f cursor-column)
                              (extract f echo) (extract f prefix) s)
                  (if (string=? out "") nil (list (lambda () (begin (write-out out) #u))))))))

"Message for the frame: show `m` in the echo area (and draw)."
(define* echo (subr pure (string) (msg frame))
  (lambda (m)
    (lambda ((f frame))
      (draw (frame-with f (extract f rows) (extract f cursor-row) (extract f cursor-column)
                        m (extract f prefix) (extract f shown))))))

"Message for the frame: the view's rows and cursor."
(define* view-shows (subr pure (rows int int) (msg frame))
  (lambda (rs cr cc)
    (lambda ((f frame)) (draw (frame-with f rs cr cc (extract f echo) (extract f prefix) (extract f shown))))))

"A command for the buffer: run, its message sent back to the frame's echo
area, and the buffer's subscribers sent a snapshot when it changed."
(define* in-buffer (subr pure ((actor frame) command) (msg buffer))
  (lambda (fr c)
    (lambda ((b buffer))
      (let* ((o (c b))
             (b2 (extract o buffer))
             (snap (snapshot-of b2))
             (notes (letrec ((go (subr turn-eff ((listof subscriber acyclic)) cmds)
                               (lambda (ss) (if (null? ss) nil (cons ((car ss) snap) (go (cdr ss)))))))
                      (go (extract b2 subscribers))))
             (m (extract o message)))
        (reply-with b2 (append (extract o cmds)
                               (append notes (list (tell fr (echo m))))))))))

"Message for the frame: a key typed."
(define* key-typed (subr pure ((actor frame) key) (msg frame))
  (lambda (self k)
    (lambda ((f frame))
      (let* ((ks (append (extract f prefix) (list k)))
             (a (binding ks)))
        (tagcase a
          (run c (reply-with (frame-with f (extract f rows) (extract f cursor-row) (extract f cursor-column)
                                         (extract f echo) nil (extract f shown))
                             (list (tell (extract f buffer) (in-buffer self c)))))
          (prefix u (draw (frame-with f (extract f rows) (extract f cursor-row) (extract f cursor-column)
                                      (string-append (keys->string ks) "-") ks (extract f shown))))
          (exit u (reply-with f (list (lambda () (set running #f)))))
          (undefined u (draw (frame-with f (extract f rows) (extract f cursor-row) (extract f cursor-column)
                                         (string-append (keys->string ks) " is undefined") nil
                                         (extract f shown)))))))))

;;; ------------------------------------------------------------ the view

(define-type view (productof (frame (actor frame)) (top int) (height int) (width int)))

"Message for the view: a snapshot of its buffer, laid out and sent to the
frame -- the text's lines from `top`, scrolled to show point, and the mode
line."
(define* view-snapshot (subr pure ((actor frame) snapshot) (msg view))
  (lambda (fr snap)
    (lambda ((v view))
      (let* ((t (extract snap text))
             (h (extract v height))
             (w (extract v width))
             (pline (rope-line-of t (extract snap point)))
             (top (cond ((< pline (extract v top)) pline)
                        ((>= pline (+ (extract v top) h)) (+ (- pline h) 1))
                        (else (extract v top))))
             (lines (letrec ((go (subr turn-eff (int) rows)
                               (lambda (i)
                                 (if (>= i h)
                                     nil
                                     (let ((n (+ top i)))
                                       (cons (if (< n (rope-line-count t))
                                                 (make-row w (rope-substring t (rope-line-start t n) (rope-line-end t n)) nil)
                                                 (blank-row w))
                                             (go (+ i 1))))))))
                      (go 0)))
             (mode (face-row w (string-append (if (extract snap modified) "-**- " "---- ")
                                              (extract snap name)
                                              "   L" (int->string (+ pline 1)))
                             'mode-line))
             (column (min (- w 1) (- (extract snap point) (rope-line-start t pline)))))
        (reply-with (product (frame (extract v frame)) (top top) (height h) (width w))
                    (list (tell fr (view-shows (append lines (list mode)) (- pline top) column))))))))

"Message for a buffer: add a subscriber, and send it a snapshot now."
(define* subscribe (subr pure (subscriber) (msg buffer))
  (lambda (s)
    (lambda ((b buffer))
      (reply-with (product (name (extract b name)) (file (extract b file)) (text (extract b text))
                           (point (extract b point)) (revision (extract b revision))
                           (modified (extract b modified))
                           (subscribers (cons s (extract b subscribers))))
                  (list (s (snapshot-of b)))))))

;;; ------------------------------------------------------------ the terminal

"The next byte typed, or #f if none comes within `timeout` ms (0: only
one already there)."
(define* next-byte (subr (maxeff (io stdin) (io clock) nondet spin) (int) (union false int))
  (lambda (timeout)
    (let ((of (lambda ((r (sumof (byte u8) (eof unit) (failed io-error))))
                (the (union false int) (tagcase r (byte u (u8->int u)) (else y #f))))))
      (if (<= timeout 0)
          (if (stdin-ready?) (of (read-byte)) (the (union false int) #f))
          (pselect ((read-byte) r (of r))
                   ((sleep-until (i64+ (clock) (int->i64 (* timeout 1000000)))) u (the (union false int) #f)))))))

"Send the frame the keys typed, waiting up to `timeout` ms for the first.
Whether any came."
(define* send-keys! (subr (maxeff cmd-eff (io stdin) (io clock)) ((actor frame) int) bool)
  (lambda (fr timeout)
    (let ((k (read-key next-byte timeout)))
      (typecase k
        (bool f #f)
        (else y (begin (tell! fr (key-typed fr y))
                       (send-keys! fr 0)
                       #t))))))

(define* size (subr (io terminal) () (productof (rows int) (columns int)))
  (lambda ()
    (tagcase (terminal-size)
      (size s s)
      (else y (product (rows 24) (columns 80))))))

(define* file-text (subr (maxeff (io fs-read) spin) (string) rope)
  (lambda (file)
    (tagcase (read-file file)
      (data d (tagcase (utf8->string d) (text s (string->rope s)) (else y empty-rope)))
      (else y empty-rope))))

(define* base-name (subr spin (string) string)
  (lambda (file)
    (letrec ((go (subr spin (int) string)
               (lambda (i)
                 (cond ((< i 0) file)
                       ((char=? (string-ref file i) #\/) (substring file (+ i 1) (string-length file)))
                       (else (go (- i 1)))))))
      (go (- (string-length file) 1)))))

"Turns while any wait, keys read between batches; with none waiting, wait
for a key (and every half second look at the terminal's size)."
(define* run-loop (subr (maxeff cmd-eff (io stdin) (io clock) (io terminal)) ((actor frame)) unit)
  (lambda (fr)
    (begin
      (run-turns! 100)
      (cond ((not (get running)) #u)
            ((turns-waiting?) (begin (send-keys! fr 0) (run-loop fr)))
            (else (begin (send-keys! fr 500) (run-loop fr)))))))

(define* main (subr (maxeff cmd-eff (io stdin) (io clock) (io terminal) (io args) (alloc @a)) () int)
  (lambda ()
    (let* ((as (the (listof string @a) (args)))
           (file (if (pair? as) (car as) "scratch.txt"))
           (sz (size))
           (h (extract sz rows))
           (w (extract sz columns))
           (b (spawn-actor "buffer"
                           (product (name (base-name file)) (file file) (text (file-text file)) (point 0)
                                    (revision 0) (modified #f) (subscribers (the (listof subscriber acyclic) nil)))))
           (fr (spawn-actor "frame"
                            (product (buffer b) (height h) (width w) (rows (the rows nil))
                                     (cursor-row 0) (cursor-column 0) (echo "") (prefix (the keys nil))
                                     (shown no-screen))))
           (v (spawn-actor "view" (product (frame fr) (top 0) (height (- h 2)) (width w)))))
      (begin
        (on-turn-failure! (lambda ((who string) (why string)) (tell! fr (echo (string-append who ": " why)))))
        (terminal-raw)
        (write-out "\x1b;[?1049h")
        (tell! b (subscribe (lambda ((s snapshot)) (tell v (view-snapshot fr s)))))
        (run-loop fr)
        (write-out "\x1b;[?1049l")
        (terminal-restore)
        0))))
