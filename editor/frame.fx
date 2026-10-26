;;; frame.fx: the frame -- windows, the echo area and minibuffer, keys and
;;; the commands they name (cahoots' `(yank actor frame)` and
;;; `(yank actor frame-base)`, c337e2a).
;;;
;;; A key goes to the frame, which looks it up: a command on the buffer is
;;; sent to the selected window's buffer, as code run in a turn there; a
;;; command on the frame (windows, files, buffers) runs in the frame's own
;;; turn. Each window has a view; each view reports what it shows, and the
;;; frame puts the windows and the echo area together into a screen, which
;;; the painter, an actor of the display class, writes once per burst.

(define-type window
  (productof (id int) (buffer (actor buffer)) (view (actor view)) (height int)
             (rows rows) (mode string) (cursor-row int) (cursor-column int)))
(define-type windows (listof window acyclic))
(define-type buffer-info (productof (name string) (file string) (actor (actor buffer))))
(define-type buffer-infos (listof buffer-info acyclic))
"The minibuffer while it reads: its prompt, the text so far and point in
it, and what to do with the text when RET is typed."
(define-type minibuffer
  (productof (prompt string) (text string) (point int) (then frame-action-of-string)))
"An incremental search: its direction, its text, and whether it fails."
(define-type isearch (productof (forward bool) (text string) (failing bool)))
"What the bottom line is doing: showing the echo area, reading in the
minibuffer, or searching."
(define-type mini-state (sumof (none unit) (reading minibuffer) (searching isearch)))
(define-type frame
  (productof (height int) (width int) (windows windows) (selected int) (buffers buffer-infos)
             (next-id int) (echo string) (prefix keys)
             (mini mini-state)
             (painter (actor screen))))
"A command on the frame: run in the frame's turn, given the frame actor."
(define-type frame-action (subr turn-eff ((actor frame) frame) (reply frame)))
(define-type frame-action-of-string (subr turn-eff ((actor frame) frame string) (reply frame)))
"What a command name is bound to: a command on the selected window's
buffer, or one on the frame."
(define-type action (sumof (on-buffer command) (on-frame frame-action)))

"Set while the editor runs; C-x C-c clears it."
(define running (ref bool @ed) (new #t))

;;; ------------------------------------------------------------ the frame's fields

"Whether two buffer actors are one: their states are one cell."
(define* same-actor? (subr pure ((actor buffer) (actor buffer)) bool)
  (lambda (a b) (eq? (extract a state) (extract b state))))


(define* frame-of
  (subr pure (frame windows int buffer-infos int string keys mini-state) frame)
  (lambda (f ws sel bufs next echo prefix mini)
    (product (height (extract f height)) (width (extract f width)) (windows ws) (selected sel)
             (buffers bufs) (next-id next) (echo echo) (prefix prefix) (mini mini)
             (painter (extract f painter)))))

(define* with-echo (subr pure (frame string) frame)
  (lambda (f m)
    (frame-of f (extract f windows) (extract f selected) (extract f buffers) (extract f next-id)
              m (extract f prefix) (extract f mini))))

(define* with-prefix (subr pure (frame keys) frame)
  (lambda (f ks)
    (frame-of f (extract f windows) (extract f selected) (extract f buffers) (extract f next-id)
              (extract f echo) ks (extract f mini))))

(define* with-mini (subr pure (frame mini-state) frame)
  (lambda (f m)
    (frame-of f (extract f windows) (extract f selected) (extract f buffers) (extract f next-id)
              (extract f echo) (extract f prefix) m)))

(define no-mini mini-state (sum none #u))

(define* window-of (subr pure (window (actor buffer) (actor view) int int) window)
  (lambda (w b v id h)
    (product (id id) (buffer b) (view v) (height h) (rows (extract w rows)) (mode (extract w mode))
             (cursor-row (extract w cursor-row)) (cursor-column (extract w cursor-column)))))

(define* selected-window (subr spin (frame) window)
  (lambda (f)
    (letrec ((go (subr spin (windows) window)
               (lambda (ws)
                 (cond ((null? (cdr ws)) (car ws))
                       ((= (extract (car ws) id) (extract f selected)) (car ws))
                       (else (go (cdr ws)))))))
      (go (extract f windows)))))

;;; ------------------------------------------------------------ drawing

"The painter: the screen shown last; told a new one, it writes what
changed."
(define* paint (subr pure (screen) (msg screen))
  (lambda (new)
    (lambda ((old screen))
      (let ((out (screen-update old new)))
        (reply-with new (if (string=? out "") nil (list (lambda () (begin (write-out out) #u)))))))))

"`n` rows of `rs`, cut, or padded with blank ones."
(define* fit-rows (subr spin (int int rows) rows)
  (lambda (n w rs)
    (cond ((<= n 0) nil)
          ((null? rs) (cons (blank-row w) (fit-rows (- n 1) w nil)))
          (else (cons (car rs) (fit-rows (- n 1) w (cdr rs)))))))

"The frame's screen: each window's rows and mode line, then the echo area
or minibuffer; and the command that has the painter show it."
(define* draw (subr turn-eff (frame) (reply frame))
  (lambda (f)
    (let* ((w (extract f width))
           (sel (extract f selected))
           (body (letrec ((go (subr turn-eff (windows int) (productof (rows rows) (row int) (column int)))
                            ;; The rows from window list `ws` on, starting at screen row `r`; and
                            ;; the selected window's cursor.
                            (lambda (ws r)
                              (if (null? ws)
                                  (product (rows nil) (row 0) (column 0))
                                  (let* ((win (car ws))
                                         (h (extract win height))
                                         (rest (go (cdr ws) (+ r h)))
                                         (mine (append (fit-rows (- h 1) w (extract win rows))
                                                       (list (face-row w (extract win mode)
                                                                       (if (= (extract win id) sel)
                                                                           'mode-line 'mode-line-inactive)))))
                                         (here (= (extract win id) sel)))
                                    (product (rows (append mine (extract rest rows)))
                                             (row (if here (+ r (extract win cursor-row)) (extract rest row)))
                                             (column (if here (extract win cursor-column) (extract rest column)))))))))
                   (go (extract f windows) 0)))
           (last-row (- (extract f height) 1))
           (bottom (tagcase (extract f mini)
                     (reading m (product (text (string-append (extract m prompt) (extract m text)))
                                         (column (+ (string-length (extract m prompt)) (extract m point)))))
                     (searching i (product (text (string-append (if (extract i failing) "Failing " "")
                                                                (if (extract i forward) "I-search: " "I-search backward: ")
                                                                (extract i text)))
                                           (column -1)))
                     (none u (product (text (extract f echo)) (column -1)))))
           (s (make-screen (extract f height) w
                           (append (extract body rows) (list (make-row w (extract bottom text) nil)))
                           (if (>= (extract bottom column) 0) last-row (extract body row))
                           (if (>= (extract bottom column) 0) (min (- w 1) (extract bottom column))
                               (extract body column)))))
      (reply-with f (list (tell-latest (extract f painter) "paint" (paint s)))))))

;;; ------------------------------------------------------------ running commands

"Message for the frame: `m` in the echo area."
(define* echo (subr pure (string) (msg frame))
  (lambda (m) (lambda ((f frame)) (draw (with-echo f m)))))

"A command for the buffer: run, its subscribers sent a snapshot, and its
message sent to the frame's echo area."
(define* in-buffer (subr pure ((actor frame) command) (msg buffer))
  (lambda (fr c)
    (lambda ((b buffer))
      (let* ((o (c b))
             (b2 (extract o buffer))
             (m (extract o message)))
        (reply-with b2 (append (extract o cmds)
                               (append (notify b2)
                                       (if (string=? m "") nil (list (tell fr (echo m)))))))))))

(define* run-action (subr turn-eff ((actor frame) frame action) (reply frame))
  (lambda (fr f a)
    (tagcase a
      (on-buffer c (reply-with f (list (tell (extract (selected-window f) buffer) (in-buffer fr c)))))
      (on-frame g (g fr f)))))

;;; ------------------------------------------------------------ windows

"The windows' heights, the text area shared as evenly as can be, each
height counting its mode line; and each view told its new size."
(define* relayout (subr turn-eff (frame windows) (productof (windows windows) (cmds cmds)))
  (lambda (f ws)
    (let* ((n (length ws))
           (total (- (extract f height) 1))
           (each (quotient total (max 1 n)))
           (extra (- total (* each (max 1 n)))))
      (letrec ((go (subr turn-eff (windows int) (productof (windows windows) (cmds cmds)))
                 (lambda (ws i)
                   (if (null? ws)
                       (product (windows nil) (cmds nil))
                       (let* ((win (car ws))
                              (h (if (= i 0) (+ each extra) each))
                              (rest (go (cdr ws) (+ i 1))))
                         (product (windows (cons (window-of win (extract win buffer) (extract win view) (extract win id) h)
                                                 (extract rest windows)))
                                  (cmds (cons (tell (extract win view) (view-resize (- h 1) (extract f width)))
                                              (extract rest cmds)))))))))
        (go ws 0)))))

"Message for the frame: window `id`'s view shows `rs`."
(define* window-shows (subr pure (int rows string int int) (msg frame))
  (lambda (id rs mode cr cc)
    (lambda ((f frame))
      (if (letrec ((has (subr spin (windows) bool)
                     (lambda (ws) (and (pair? ws) (or (= (extract (car ws) id) id) (has (cdr ws)))))))
            (has (extract f windows)))
          (draw (frame-of f
                          (letrec ((go (subr spin (windows) windows)
                                     (lambda (ws)
                                       (cond ((null? ws) nil)
                                             ((= (extract (car ws) id) id)
                                              (let ((w (car ws)))
                                                (cons (product (id id) (buffer (extract w buffer)) (view (extract w view))
                                                               (height (extract w height)) (rows rs) (mode mode)
                                                               (cursor-row cr) (cursor-column cc))
                                                      (cdr ws))))
                                             (else (cons (car ws) (go (cdr ws))))))))
                            (go (extract f windows)))
                          (extract f selected) (extract f buffers) (extract f next-id)
                          (extract f echo) (extract f prefix) (extract f mini)))
          ;; A view replaced since: what it shows is no window's.
          (same f)))))

"What a view of window `id` reports to: the frame, told what it shows."
(define* reporter-for (subr pure ((actor frame)) reporter)
  (lambda (fr)
    (lambda ((id int) (rs rows) (mode string) (cr int) (cc int))
      (tell fr (window-shows id rs mode cr cc)))))

"A new window of buffer `b`, number `id`, `h` rows high; and the commands
that make its view display-class, and subscribe it to the buffer."
(define* new-window (subr turn-eff ((actor frame) frame (actor buffer) int int) (productof (window window) (cmds cmds)))
  (lambda (fr f b id h)
    (let ((v (make-view id (reporter-for fr) (- h 1) (extract f width))))
      (product (window (product (id id) (buffer b) (view v) (height h) (rows nil) (mode "")
                                (cursor-row 0) (cursor-column 0)))
               (cmds (list (lambda () (set-class! v display))
                           (tell b (subscribe id (lambda ((s snapshot)) (tell-latest v "snapshot" (view-snapshot s)))))))))))

"The selected window made to show buffer `b`: a new view, and the old one
unsubscribed."
(define* show-buffer (subr turn-eff ((actor frame) frame (actor buffer)) (reply frame))
  (lambda (fr f b)
    (let* ((old (selected-window f))
           (id (extract f next-id))
           (made (new-window fr f b id (extract old height)))
           (ws (letrec ((go (subr spin (windows) windows)
                          (lambda (ws)
                            (cond ((null? ws) nil)
                                  ((= (extract (car ws) id) (extract old id)) (cons (extract made window) (cdr ws)))
                                  (else (cons (car ws) (go (cdr ws))))))))
                 (go (extract f windows)))))
      (reply-with (frame-of f ws id (extract f buffers) (+ id 1) (extract f echo) (extract f prefix) (extract f mini))
                  (cons (tell (extract old buffer) (unsubscribe (extract old id))) (extract made cmds))))))

;;; ------------------------------------------------------------ frame commands

(define* split-window (subr pure () frame-action)
  (lambda ()
    (lambda ((fr (actor frame)) (f frame))
      (let ((old (selected-window f)))
        (if (< (quotient (extract old height) 2) 2)
            (draw (with-echo f "Window too small for splitting"))
            (let* ((id (extract f next-id))
                   (made (new-window fr f (extract old buffer) id (quotient (extract old height) 2)))
                   (ws (letrec ((go (subr spin (windows) windows)
                                  (lambda (ws)
                                    (cond ((null? ws) nil)
                                          ((= (extract (car ws) id) (extract old id))
                                           (cons (car ws) (cons (extract made window) (cdr ws))))
                                          (else (cons (car ws) (go (cdr ws))))))))
                         (go (extract f windows))))
                   (laid (relayout f ws)))
              (reply-with (frame-of f (extract laid windows) (extract f selected) (extract f buffers) (+ id 1)
                                    (extract f echo) (extract f prefix) (extract f mini))
                          (append (extract made cmds) (extract laid cmds)))))))))

(define* other-window (subr pure () frame-action)
  (lambda ()
    (lambda ((fr (actor frame)) (f frame))
      (let ((ws (extract f windows)))
        (letrec ((after (subr spin (windows) int)
                   (lambda (l)
                     (cond ((null? l) (extract (car ws) id))
                           ((= (extract (car l) id) (extract f selected))
                            (if (null? (cdr l)) (extract (car ws) id) (extract (car (cdr l)) id)))
                           (else (after (cdr l)))))))
          (draw (frame-of f ws (after ws) (extract f buffers) (extract f next-id)
                          (extract f echo) (extract f prefix) (extract f mini))))))))

(define* delete-other-windows (subr pure () frame-action)
  (lambda ()
    (lambda ((fr (actor frame)) (f frame))
      (let* ((keep (selected-window f))
             (gone (letrec ((go (subr turn-eff (windows) cmds)
                              (lambda (ws)
                                (cond ((null? ws) nil)
                                      ((= (extract (car ws) id) (extract keep id)) (go (cdr ws)))
                                      (else (cons (tell (extract (car ws) buffer) (unsubscribe (extract (car ws) id)))
                                                  (go (cdr ws))))))))
                     (go (extract f windows))))
             (laid (relayout f (list keep))))
        (reply-with (frame-of f (extract laid windows) (extract keep id) (extract f buffers) (extract f next-id)
                              (extract f echo) (extract f prefix) (extract f mini))
                    (append gone (extract laid cmds)))))))

(define* delete-window (subr pure () frame-action)
  (lambda ()
    (lambda ((fr (actor frame)) (f frame))
      (if (null? (cdr (extract f windows)))
          (draw (with-echo f "Attempt to delete minibuffer or sole ordinary window"))
          (let* ((gone (selected-window f))
                 (ws (letrec ((go (subr spin (windows) windows)
                                (lambda (ws)
                                  (cond ((null? ws) nil)
                                        ((= (extract (car ws) id) (extract gone id)) (go (cdr ws)))
                                        (else (cons (car ws) (go (cdr ws))))))))
                       (go (extract f windows))))
                 (laid (relayout f ws)))
            (reply-with (frame-of f (extract laid windows) (extract (car ws) id) (extract f buffers)
                                  (extract f next-id) (extract f echo) (extract f prefix) (extract f mini))
                        (cons (tell (extract gone buffer) (unsubscribe (extract gone id))) (extract laid cmds))))))))

"A command on the buffer that depends on the selected window's height:
`(make lines)`, given the lines the window shows."
(define* with-window-lines (subr pure ((subr (read @globals) (int) command)) frame-action)
  (lambda (make)
    (lambda ((fr (actor frame)) (f frame))
      (let ((win (selected-window f)))
        (reply-with f (list (tell (extract win buffer) (in-buffer fr (make (max 1 (- (extract win height) 3)))))))))))

"Read a string in the minibuffer, after `prompt`, starting as `initial`;
then `then` of it."
(define* read-string (subr turn-eff (frame string string frame-action-of-string) (reply frame))
  (lambda (f prompt initial then)
    (draw (with-mini (with-echo f "")
                     (sum reading (product (prompt prompt) (text initial) (point (string-length initial))
                                           (then then)))))))

(define* find-buffer (subr spin (buffer-infos string) (sumof (none unit) (found buffer-info)))
  (lambda (bs name)
    (cond ((null? bs) (sum none #u))
          ((string=? (extract (car bs) name) name) (sum found (car bs)))
          (else (find-buffer (cdr bs) name)))))

(define* find-file-buffer (subr spin (buffer-infos string) (sumof (none unit) (found buffer-info)))
  (lambda (bs file)
    (cond ((null? bs) (sum none #u))
          ((string=? (extract (car bs) file) file) (sum found (car bs)))
          (else (find-file-buffer (cdr bs) file)))))

"A name for a buffer of `base` no other has: base, base<2>, …"
(define* unique-name (subr spin (buffer-infos string) string)
  (lambda (bs base)
    (letrec ((go (subr spin (int) string)
               (lambda (n)
                 (let ((name (if (= n 1) base (string-append base "<" (int->string n) ">"))))
                   (tagcase (find-buffer bs name) (none u name) (found b (go (+ n 1))))))))
      (go 1))))

"Message for the frame: buffer `b` made (a file read, a listing), to be
known by name and shown in the selected window."
(define* buffer-made (subr pure ((actor frame) string string (actor buffer)) (msg frame))
  (lambda (fr name file b)
    (lambda ((f frame))
      (let ((f2 (frame-of f (extract f windows) (extract f selected)
                          (append (extract f buffers) (list (product (name name) (file file) (actor b))))
                          (extract f next-id) (extract f echo) (extract f prefix) (extract f mini))))
        (show-buffer fr f2 b)))))

"The text of `file`: its contents; empty, and whether it was found."
(define* file-text (subr (maxeff (io fs-read) spin) (string) (productof (text rope) (found bool)))
  (lambda (file)
    (tagcase (read-file file)
      (data d (tagcase (utf8->string d)
                (text s (product (text (string->rope s)) (found #t)))
                (else y (product (text empty-rope) (found #t)))))
      (else y (product (text empty-rope) (found #f))))))

(define* find-file (subr pure () frame-action)
  (lambda ()
    (lambda ((fr (actor frame)) (f frame))
      (let ((dir (let ((b (selected-window f)))
                   (letrec ((dir-of (subr spin (buffer-infos) string)
                              (lambda (bs)
                                (cond ((null? bs) "")
                                      ((same-actor? (extract (car bs) actor) (extract b buffer))
                                       (directory-of (extract (car bs) file)))
                                      (else (dir-of (cdr bs)))))))
                     (dir-of (extract f buffers))))))
        (read-string f "Find file: " dir
                     (lambda ((fr (actor frame)) (f frame) (file string))
                       (tagcase (find-file-buffer (extract f buffers) file)
                         (found info (show-buffer fr f (extract info actor)))
                         (none u
                           (let ((name (unique-name (extract f buffers) (base-name file))))
                             (reply-with f
                                         (list (lambda ()
                                                 (let* ((got (file-text file))
                                                        (b (spawn-actor name (new-buffer name file (extract got text)))))
                                                   (begin
                                                     (tell! fr (buffer-made fr name file b))
                                                     (if (extract got found) #u (tell! fr (echo "(New file)")))))))))))))))))

(define* switch-to-buffer (subr pure () frame-action)
  (lambda ()
    (lambda ((fr (actor frame)) (f frame))
      (let* ((current (extract (selected-window f) buffer))
             (other (letrec ((go (subr spin (buffer-infos) string)
                               (lambda (bs)
                                 (cond ((null? bs) "")
                                       ((same-actor? (extract (car bs) actor) current) (go (cdr bs)))
                                       (else (extract (car bs) name))))))
                      (go (extract f buffers)))))
        (read-string f (string-append "Switch to buffer" (if (string=? other "") "" (string-append " (default " other ")")) ": ")
                     ""
                     (lambda ((fr (actor frame)) (f frame) (name string))
                       (let ((name (if (string=? name "") other name)))
                         (tagcase (find-buffer (extract f buffers) name)
                           (found info (show-buffer fr f (extract info actor)))
                           (none u
                             (let ((b (spawn-actor name (new-buffer name "" empty-rope))))
                               (reply-with f (list (lambda () (tell! fr (buffer-made fr name "" b)))))))))))))))

"Message for a buffer: its text replaced, as one change."
(define* replace-text (subr pure (rope) (msg buffer))
  (lambda (t)
    (lambda ((b buffer))
      (let ((b2 (buffer-of b t 0 -1 (+ 1 (extract b revision)) #f (extract b undo) (extract b subscribers))))
        (reply-with b2 (notify b2))))))

"*Buffer List*: each buffer's name, whether modified, and its file."
(define* list-buffers (subr pure () frame-action)
  (lambda ()
    (lambda ((fr (actor frame)) (f frame))
      (let* ((lines (letrec ((go (subr turn-eff (buffer-infos) strings)
                               (lambda (bs)
                                 (if (null? bs)
                                     nil
                                     (let* ((info (car bs))
                                            (st (actor-state (extract info actor)))
                                            (name (extract info name)))
                                       (cons (string-append (if (extract st modified) " * " "   ")
                                                            name
                                                            (if (< (string-length name) 24)
                                                                (substring "                        " 0 (- 24 (string-length name)))
                                                                " ")
                                                            (int->string (rope-length (extract st text))) "\t"
                                                            (extract info file) "\n")
                                             (go (cdr bs))))))))
                      (go (extract f buffers))))
             (text (string->rope (apply string-append (the strings (cons " M Name                    Size\tFile\n" lines)))))
             (name "*Buffer List*"))
        (tagcase (find-buffer (extract f buffers) name)
          (found info (reply-with f (list (tell (extract info actor) (replace-text text))
                                          (tell fr (lambda ((f frame)) (show-buffer fr f (extract info actor)))))))
          (none u (let ((b (spawn-actor name (new-buffer name "" text))))
                    (reply-with f (list (lambda () (tell! fr (buffer-made fr name "" b))))))))))))

(define* save-buffers-kill-editor (subr pure () frame-action)
  (lambda () (lambda ((fr (actor frame)) (f frame)) (reply-with f (list (lambda () (set running #f)))))))

;;; ------------------------------------------------------------ searching

"Message for the frame: the search's latest step failed, or did not."
(define* isearch-status (subr pure (bool) (msg frame))
  (lambda (failing)
    (lambda ((f frame))
      (tagcase (extract f mini)
        (searching i (draw (with-mini f (sum searching (product (forward (extract i forward)) (text (extract i text))
                                                                (failing failing))))))
        (else y (same f))))))

(define* search-reporter (subr pure ((actor frame)) search-report)
  (lambda (fr) (lambda ((failing bool)) (tell fr (isearch-status failing)))))

"C-s, C-r: a search begun, in the selected window's buffer."
(define* isearch (subr pure (bool) frame-action)
  (lambda (forward)
    (lambda ((fr (actor frame)) (f frame))
      (let ((r (draw (with-mini (with-echo f "")
                                (sum searching (product (forward forward) (text "") (failing #f)))))))
        (reply-with (extract r state)
                    (cons (tell (extract (selected-window f) buffer) (in-buffer fr (isearch-begin)))
                          (extract r cmds)))))))

;;; ------------------------------------------------------------ commands by name, and keys

(define-type named (productof (name string) (action action)))

(define* buffer-command (subr pure (string command) named)
  (lambda (name c) (product (name name) (action (sum on-buffer c)))))
(define* frame-command (subr pure (string frame-action) named)
  (lambda (name g) (product (name name) (action (sum on-frame g)))))

(define-rec
;; Every command, by Emacs's name; a command by its name; and M-x,
;; which runs one by name.
  (commands (->* () (listof named acyclic))
  (lambda ()
    (list (buffer-command "forward-char" (move-by 1))
          (buffer-command "backward-char" (move-by -1))
          (buffer-command "next-line" (move-lines 1))
          (buffer-command "previous-line" (move-lines -1))
          (buffer-command "move-beginning-of-line" (line-start))
          (buffer-command "move-end-of-line" (line-end))
          (buffer-command "forward-word" (move-word 1))
          (buffer-command "backward-word" (move-word -1))
          (buffer-command "beginning-of-buffer" (buffer-start))
          (buffer-command "end-of-buffer" (buffer-end))
          (frame-command "scroll-up-command" (with-window-lines (lambda ((n int)) (move-lines n))))
          (frame-command "scroll-down-command" (with-window-lines (lambda ((n int)) (move-lines (- 0 n)))))
          (buffer-command "delete-backward-char" (delete-backward))
          (buffer-command "delete-char" (delete-forward))
          (buffer-command "newline" (insert-string "\n"))
          (buffer-command "indent-for-tab-command" (insert-string "\t"))
          (buffer-command "set-mark-command" (set-mark))
          (buffer-command "exchange-point-and-mark" (exchange-point-and-mark))
          (buffer-command "kill-region" (kill-region))
          (buffer-command "kill-ring-save" (copy-region))
          (buffer-command "kill-line" (kill-line))
          (buffer-command "yank" (yank))
          (buffer-command "undo" (undo))
          (buffer-command "keyboard-quit" (keyboard-quit))
          (buffer-command "save-buffer" (save-buffer))
          (buffer-command "fail-on-purpose" (fail-on-purpose))
          (frame-command "isearch-forward" (isearch #t))
          (frame-command "isearch-backward" (isearch #f))
          (frame-command "find-file" (find-file))
          (frame-command "switch-to-buffer" (switch-to-buffer))
          (frame-command "list-buffers" (list-buffers))
          (frame-command "split-window-below" (split-window))
          (frame-command "other-window" (other-window))
          (frame-command "delete-other-windows" (delete-other-windows))
          (frame-command "delete-window" (delete-window))
          (frame-command "execute-extended-command" (execute-extended-command))
          (frame-command "save-buffers-kill-terminal" (save-buffers-kill-editor)))))

  (command-named (->* (string) (sumof (none unit) (found action)))
  (lambda (name)
    (letrec ((go (subr spin ((listof named acyclic)) (sumof (none unit) (found action)))
               (lambda (cs)
                 (cond ((null? cs) (sum none #u))
                       ((string=? (extract (car cs) name) name) (sum found (extract (car cs) action)))
                       (else (go (cdr cs)))))))
      (go (commands)))))
  (execute-extended-command (->* () frame-action)
  (lambda ()
    (lambda ((fr (actor frame)) (f frame))
      (read-string f "M-x " ""
                   (lambda ((fr (actor frame)) (f frame) (name string))
                     (tagcase (command-named name)
                       (found a (run-action fr f a))
                       (none u (draw (with-echo f (string-append "No command named " name)))))))))))

"The global keymap: key sequences, as `keys->string` writes them, and the
names of their commands."
(define keymap (listof (productof (keys string) (command string)) acyclic)
  (list (product (keys "C-f") (command "forward-char")) (product (keys "<right>") (command "forward-char"))
        (product (keys "C-b") (command "backward-char")) (product (keys "<left>") (command "backward-char"))
        (product (keys "C-n") (command "next-line")) (product (keys "<down>") (command "next-line"))
        (product (keys "C-p") (command "previous-line")) (product (keys "<up>") (command "previous-line"))
        (product (keys "C-a") (command "move-beginning-of-line")) (product (keys "<home>") (command "move-beginning-of-line"))
        (product (keys "C-e") (command "move-end-of-line")) (product (keys "<end>") (command "move-end-of-line"))
        (product (keys "M-f") (command "forward-word")) (product (keys "M-b") (command "backward-word"))
        (product (keys "M-<") (command "beginning-of-buffer")) (product (keys "M->") (command "end-of-buffer"))
        (product (keys "C-v") (command "scroll-up-command")) (product (keys "<next>") (command "scroll-up-command"))
        (product (keys "M-v") (command "scroll-down-command")) (product (keys "<prior>") (command "scroll-down-command"))
        (product (keys "DEL") (command "delete-backward-char"))
        (product (keys "C-d") (command "delete-char")) (product (keys "<delete>") (command "delete-char"))
        (product (keys "RET") (command "newline")) (product (keys "TAB") (command "indent-for-tab-command"))
        (product (keys "C-SPC") (command "set-mark-command"))
        (product (keys "C-x C-x") (command "exchange-point-and-mark"))
        (product (keys "C-w") (command "kill-region")) (product (keys "M-w") (command "kill-ring-save"))
        (product (keys "C-k") (command "kill-line")) (product (keys "C-y") (command "yank"))
        (product (keys "C-_") (command "undo")) (product (keys "C-/") (command "undo"))
        (product (keys "C-x u") (command "undo"))
        (product (keys "C-g") (command "keyboard-quit"))
        (product (keys "C-s") (command "isearch-forward")) (product (keys "C-r") (command "isearch-backward"))
        (product (keys "C-x C-s") (command "save-buffer"))
        (product (keys "C-x C-f") (command "find-file"))
        (product (keys "C-x b") (command "switch-to-buffer"))
        (product (keys "C-x C-b") (command "list-buffers"))
        (product (keys "C-x 2") (command "split-window-below"))
        (product (keys "C-x o") (command "other-window"))
        (product (keys "C-x 1") (command "delete-other-windows"))
        (product (keys "C-x 0") (command "delete-window"))
        (product (keys "M-x") (command "execute-extended-command"))
        (product (keys "C-x C-c") (command "save-buffers-kill-terminal"))
        (product (keys "C-c !") (command "fail-on-purpose"))))

"The prefixes: key sequences that are the start of longer bindings."
(define prefixes strings (list "C-x" "C-c"))

"What `ks` does: a command, more keys to come, or nothing."
(define* binding (subr spin (keys) (sumof (command action) (prefix unit) (undefined unit)))
  (lambda (ks)
    (let ((s (keys->string ks)))
      (letrec ((bound (subr spin ((listof (productof (keys string) (command string)) acyclic)) string)
                 (lambda (m) (cond ((null? m) "")
                                   ((string=? (extract (car m) keys) s) (extract (car m) command))
                                   (else (bound (cdr m))))))
               (prefix? (subr spin (strings) bool)
                 (lambda (ps) (and (pair? ps) (or (string=? (car ps) s) (prefix? (cdr ps)))))))
        (let ((name (bound keymap)))
          (cond ((not (string=? name ""))
                 (tagcase (command-named name) (found a (sum command a)) (none u (sum undefined #u))))
                ((prefix? prefixes) (sum prefix #u))
                ((and (pair? ks) (null? (cdr ks)))
                 (typecase (car ks)
                   (char c (sum command (sum on-buffer (insert-string (char->string c)))))
                   (else y (sum undefined #u))))
                (else (sum undefined #u))))))))

;;; ------------------------------------------------------------ keys

"A key typed while the minibuffer reads."
(define* minibuffer-key (subr turn-eff ((actor frame) frame minibuffer key) (reply frame))
  (lambda (fr f m k)
    (let* ((text (extract m text)) (p (extract m point)) (n (string-length text))
           (edit (lambda ((t string) (q int))
                   (draw (with-mini f (sum reading (product (prompt (extract m prompt)) (text t) (point q)
                                                            (then (extract m then))))))))
           (name (key->string k)))
      (typecase k
        (char c (edit (string-append (substring text 0 p) (char->string c) (substring text p n)) (+ p 1)))
        (else y
          (case name
            (("RET") ((extract m then) fr (with-mini f no-mini) text))
            (("C-g") (draw (with-echo (with-mini f no-mini) "Quit")))
            (("DEL") (if (= p 0) (same f) (edit (string-append (substring text 0 (- p 1)) (substring text p n)) (- p 1))))
            (("C-d") (if (= p n) (same f) (edit (string-append (substring text 0 p) (substring text (+ p 1) n)) p)))
            (("C-a" "<home>") (edit text 0))
            (("C-e" "<end>") (edit text n))
            (("C-b" "<left>") (edit text (max 0 (- p 1))))
            (("C-f" "<right>") (edit text (min n (+ p 1))))
            (("C-k") (edit (substring text 0 p) p))
            (else (same f))))))))

"A key typed with no minibuffer or search: looked up, with any prefix."
(define* dispatch-key (subr turn-eff ((actor frame) frame key) (reply frame))
  (lambda (fr f k)
          (let* ((ks (append (extract f prefix) (list k)))
                 (cleared (with-echo (with-prefix f nil) "")))
            (tagcase (binding ks)
              (command a (let ((r (run-action fr cleared a)))
                           ;; The echo area cleared, and shown so, if it said something.
                           (if (string=? (extract f echo) "")
                               r
                               (reply-with (extract r state)
                                           (append (extract r cmds) (extract (draw (extract r state)) cmds))))))
              (prefix u (draw (with-echo (with-prefix f ks) (string-append (keys->string ks) "-"))))
              (undefined u (draw (with-echo (with-prefix f nil)
                                            (string-append (keys->string ks) " is undefined"))))))))

"A key typed while searching."
(define* isearch-key (subr turn-eff ((actor frame) frame isearch key) (reply frame))
  (lambda (fr f i k)
    (let* ((b (extract (selected-window f) buffer))
           (report (search-reporter fr))
           (fwd (extract i forward))
           (text (extract i text))
           (step (lambda ((t string) (forward bool) (again bool) (reset bool))
                   (let ((r (draw (with-mini f (sum searching (product (forward forward) (text t)
                                                                       (failing (extract i failing))))))))
                     (reply-with (extract r state)
                                 (append (if reset (list (tell b (in-buffer fr (isearch-abort-quietly)))) nil)
                                         (cons (tell b (in-buffer fr (isearch-step t forward again report)))
                                               (extract r cmds)))))))
           (leave (lambda ((c command))
                    (let ((r (draw (with-mini f no-mini))))
                      (reply-with (extract r state) (cons (tell b (in-buffer fr c)) (extract r cmds)))))))
      (typecase k
        (char c (step (string-append text (char->string c)) fwd #f #f))
        (else y
          (case (key->string k)
            (("C-s") (step text #t #t #f))
            (("C-r") (step text #f #t #f))
            (("DEL") (if (= (string-length text) 0)
                         (same f)
                         (step (substring text 0 (- (string-length text) 1)) fwd #f #t)))
            (("RET") (leave (isearch-exit)))
            (("C-g") (leave (isearch-abort)))
            (else
             ;; Any other key ends the search, and then does what it does.
             (let* ((ended (leave (isearch-exit)))
                    (r (dispatch-key fr (extract ended state) k)))
               (reply-with (extract r state) (append (extract ended cmds) (extract r cmds)))))))))))

"Message for the frame: a key typed."
(define* key-typed (subr pure ((actor frame) key) (msg frame))
  (lambda (fr k)
    (lambda ((f frame))
      (tagcase (extract f mini)
        (reading m (minibuffer-key fr f m k))
        (searching i (isearch-key fr f i k))
        (none u (dispatch-key fr f k))))))

"Message for the frame: the terminal is now `h` rows by `w`."
(define* resized (subr pure (int int) (msg frame))
  (lambda (h w)
    (lambda ((f frame))
      (let* ((f2 (product (height h) (width w) (windows (extract f windows)) (selected (extract f selected))
                          (buffers (extract f buffers)) (next-id (extract f next-id)) (echo (extract f echo))
                          (prefix (extract f prefix)) (mini (extract f mini)) (painter (extract f painter))))
             (laid (relayout f2 (extract f windows)))
             (f3 (frame-of f2 (extract laid windows) (extract f selected) (extract f buffers) (extract f next-id)
                           (extract f echo) (extract f prefix) (extract f mini))))
        (reply-with f3 (append (extract laid cmds) (extract (draw f3) cmds)))))))

"Message for the frame: its first window, on buffer `b`."
(define* first-window (subr pure ((actor frame) string string (actor buffer)) (msg frame))
  (lambda (fr name file b)
    (lambda ((f frame))
      (let* ((made (new-window fr f b (extract f next-id) (- (extract f height) 1)))
             (id (extract f next-id))
             (f2 (frame-of f (list (extract made window)) id
                           (list (product (name name) (file file) (actor b)))
                           (+ id 1) (extract f echo) (extract f prefix) (extract f mini))))
        (reply-with f2 (extract made cmds))))))
