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
(lambda ((m-base (load-input-moduleof "base.fx"))
         (m-buffer (load-input-moduleof "buffer.fx" m-base))
         (m-resolve (load-input-moduleof "resolve.fx" m-base m-buffer))
         (m-syntax (load-input-moduleof "syntax.fx" m-base m-buffer m-resolve))
         (m-sexp (load-input-moduleof "sexp.fx" m-base m-buffer m-resolve m-syntax))
         (m-flow (load-input-moduleof "flow.fx" m-base m-buffer m-resolve m-syntax m-sexp))
         (m-index (load-input-moduleof "index.fx" m-base m-buffer m-resolve m-syntax m-sexp m-flow))
         (m-view (load-input-moduleof "view.fx" m-base m-buffer m-resolve m-syntax m-sexp m-flow m-index)))
(module
(hide (include m-base) (include m-buffer) (include m-resolve) (include m-syntax) (include m-sexp) (include m-flow) (include m-index) (include m-view))

(define-type window
  (productof (id int) (buffer (actor buffer)) (view (actor view)) (height int)
             (rows rows) (mode string) (cursor-row int) (cursor-column int)))
(define-type windows (listof window acyclic))
(define-type buffer-info (productof (name string) (file string) (actor (actor buffer))))
(define-type buffer-infos (listof buffer-info acyclic))
"What TAB completes the minibuffer's text from: nothing, the names of
files, or names given."
(define-type completion (sumof (nothing unit) (files unit) (names (listof string acyclic))))
"The minibuffer while it reads: its prompt, the text so far and point in
it, and what to do with the text when RET is typed; what TAB completes
from, and what the last TAB said (shown after the text)."
(define-type minibuffer
  (productof (prompt string) (text string) (point int) (then frame-action-of-string)
             (complete completion) (hint string)))
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

"*Messages*: once main has made it, a list of it alone."
(define messages-buffer (ref (listof (actor buffer) acyclic) @ed) (new nil))
"The message last put in *Messages*, while the echo area still shows it."
(define echo-logged (ref string @ed) (new ""))
"What eldoc (eldoc.fx) said last: shown, but not a message to keep."
(define eldoc-said (ref string @ed) (new ""))

"`last`, a line of *Messages*, as `m` repeated: 1 if it is `m`, n if it is
`m [n times]`, else 0."
(define* times-said (subr spin (string string) int)
  (lambda (last m)
    (let ((n (string-length last)) (k (string-length m)))
      (cond ((string=? last m) 1)
            ((and (> n (+ k 9)) (string=? (substring last 0 (+ k 2)) (string-append m " ["))
                  (string=? (substring last (- n 7) n) " times]"))
             (parse-nat (substring last (+ k 2) (- n 7)) 10))
            (else 0)))))

"Message for *Messages*: `m` added as its last line, or, if that line is
`m` already, counted again (`m [2 times]`), as Emacs's are. Point, at
the end, stays at the end; the buffer is never modified, nor undone."
(define* log-message (subr pure (string) (msg buffer))
  (lambda (m)
    (lambda ((b buffer))
      (let* ((t (extract b text))
             (n (rope-length t))
             (from (if (= n 0) 0 (rope-line-start t (rope-line-of t (- n 1)))))
             (k (if (= n 0) 0 (times-said (rope-substring t from (- n 1)) m)))
             (t2 (if (> k 0)
                     (rope-insert (rope-delete t from n) from
                                  (string-append m " [" (int->string (+ k 1)) " times]\n"))
                     (rope-insert t n (string-append m "\n"))))
             (p (extract b point))
             (b2 (buffer-of b t2 (if (>= p (if (> k 0) from n)) (rope-length t2) p) (extract b mark)
                            (+ 1 (extract b revision)) #f nil (extract b subscribers))))
        (reply-with b2 (notify b2))))))

"A command: the echo area's `m` kept in *Messages* -- unless it is empty,
or a prefix's keys (`prefixed`), or eldoc's, or kept already."
(define* log-echo (subr pure (string bool) cmd)
  (lambda (m prefixed)
    (lambda ()
      (cond ((string=? m "") (set echo-logged ""))
            ((or prefixed (string=? m (get echo-logged)) (string=? m (get eldoc-said))) #u)
            (else (begin (set echo-logged m)
                    (let ((bs (get messages-buffer))) (if (pair? bs) (tell! (car bs) (log-message m)) #u))))))))

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
                     (reading m (let* ((all (string-append (extract m prompt) (extract m text) (extract m hint)))
                                       (column (+ (string-length (extract m prompt)) (extract m point)))
                                       ;; Its start left off, if point would be past the right edge.
                                       (skip (max 0 (- column (- w 2)))))
                                  (product (text (substring all skip (string-length all))) (column (- column skip)))))
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
      (reply-with f (list (tell-latest (extract f painter) "paint" (paint s))
                          (log-echo (extract f echo) (pair? (extract f prefix))))))))

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

"The selected window split, the new window below showing buffer `b`,
the selected one staying selected."
(define* split-showing (subr turn-eff ((actor frame) frame (actor buffer)) (reply frame))
  (lambda (fr f b)
    (let ((old (selected-window f)))
        (if (< (quotient (extract old height) 2) 2)
            (draw (with-echo f "Window too small for splitting"))
            (let* ((id (extract f next-id))
                   (made (new-window fr f b id (quotient (extract old height) 2)))
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
                          (append (extract made cmds) (extract laid cmds))))))))

(define* split-window (subr pure () frame-action)
  (lambda ()
    (lambda ((fr (actor frame)) (f frame))
      (split-showing fr f (extract (selected-window f) buffer)))))

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

"Read a string in the minibuffer, after `prompt`, starting as `initial`,
TAB completing it from `c`; then `then` of it."
(define* read-completing (subr turn-eff (frame string string completion frame-action-of-string) (reply frame))
  (lambda (f prompt initial c then)
    (draw (with-mini (with-echo f "")
                     (sum reading (product (prompt prompt) (text initial) (point (string-length initial))
                                           (then then) (complete c) (hint "")))))))

(define no-completion completion (sum nothing #u))

"Read a string in the minibuffer, after `prompt`, starting as `initial`;
then `then` of it."
(define* read-string (subr turn-eff (frame string string frame-action-of-string) (reply frame))
  (lambda (f prompt initial then) (read-completing f prompt initial no-completion then)))

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
      (let* ((f2 (frame-of f (extract f windows) (extract f selected)
                           (append (extract f buffers) (list (product (name name) (file file) (actor b))))
                           (extract f next-id) (extract f echo) (extract f prefix) (extract f mini)))
             (r (show-buffer fr f2 b)))
        (reply-with (extract r state)
                    (append (attach-syntax b name) (append (index-directory-of file) (extract r cmds))))))))

"File name `name` as typed in the minibuffer, resolved against `dir` (a
buffer's directory) unless it is absolute, as Emacs's default-directory
does. (No `~`: FX-26 reads no environment, so no HOME; Heist's
fx26-for-yank.md, R7.)"
(define* expand-file-name (subr spin (string string) string)
  (lambda (name dir)
    (if (and (> (string-length name) 0) (char=? (string-ref name 0) #\/))
        name
        (string-append dir name))))

"The text of `file`: its contents; empty, and whether it was found."
(define* file-text (subr (maxeff (io fs-read) spin) (string) (productof (text rope) (found bool)))
  (lambda (file)
    (tagcase (read-file file)
      (data d (tagcase (utf8->string d)
                (text s (product (text (string->rope s)) (found #t)))
                (else y (product (text empty-rope) (found #t)))))
      (else y (product (text empty-rope) (found #f))))))

"What kind of buffer one named `name` is, for its keys: a directory's
listing (its name ends in `/`), or none."
(define* buffer-kind (subr spin (string) string)
  (lambda (name)
    (let ((n (string-length name)))
      (if (and (> n 0) (char=? (string-ref name (- n 1)) #\/)) "<listing>" ""))))

"Directory `dir` (ending in `/`) with `..` and `.` steps taken out."
(define* simplify-directory (subr spin (string) string)
  (lambda (dir)
    (letrec ((parts (subr spin (int int strings) strings)
                    ;; The names between slashes, from `i`, the current from `start`, last first.
                    (lambda (i start acc)
                      (cond ((>= i (string-length dir)) acc)
                            ((char=? (string-ref dir i) #\/)
                             (let ((p (substring dir start i)))
                               (parts (+ i 1) (+ i 1)
                                      (cond ((or (string=? p "") (string=? p ".")) acc)
                                            ((and (string=? p "..") (pair? acc) (not (string=? (car acc) ".."))) (cdr acc))
                                            (else (cons p acc))))))
                            (else (parts (+ i 1) start acc)))))
             (join (subr spin (strings string) string)
                   (lambda (l s) (if (null? l) s (join (cdr l) (string-append (car l) "/" s))))))
      (string-append (if (and (> (string-length dir) 0) (char=? (string-ref dir 0) #\/)) "/" "")
                     (join (parts 0 0 nil) "")))))

"The listing of directory `dir`: its path, then a line a name, a
directory's with a `/`."
(define* listing-text (subr (maxeff (io fs-read) spin) (string) string)
  (lambda (dir)
    (tagcase (the (sumof (names (listof string @pf)) (failed io-error)) (list-dir dir))
      (names ns
        (letrec ((go (->* ((listof string @pf)) strings)
                   (lambda (l)
                     (if (null? l) nil
                         (cons (string-append "  " (car l)
                                              (tagcase (the (sumof (names (listof string @pf)) (failed io-error))
                                                            (list-dir (string-append dir (car l))))
                                                (names x "/") (failed e ""))
                                              "\n")
                               (go (cdr l)))))))
          (apply string-append (the strings (cons (string-append "  " dir ":\n  ../\n") (go ns))))))
      (failed e (string-append "  " dir ":\n  " (extract e detail) "\n")))))

"Visit `file`: the buffer that visits it, shown; else, in a command, the
file read into a new buffer -- or, if it is a directory, its listing."
(define* visit-file (subr turn-eff ((actor frame) frame string) (reply frame))
  (lambda (fr f file)
    (tagcase (find-file-buffer (extract f buffers) file)
      (found info (show-buffer fr f (extract info actor)))
      (none u
        (tagcase (find-file-buffer (extract f buffers) (string-append file "/"))
          (found info (show-buffer fr f (extract info actor)))
          (none u2
            (reply-with f
                        (list (lambda ()
                                (if (tagcase (the (sumof (names (listof string @pf)) (failed io-error)) (list-dir file))
                                      (names ns #t) (failed e #f))
                                    (let* ((dir (simplify-directory (string-append file "/")))
                                           (name (string-append (base-name (substring dir 0 (- (string-length dir) 1))) "/"))
                                           (t (string->rope (listing-text dir)))
                                           ;; Point at the first name after `../`.
                                           (b (spawn-actor name (with-point (new-buffer name dir t) (+ 2 (rope-line-start t 2))))))
                                      (tell! fr (buffer-made fr name dir b)))
                                    (let* ((name (unique-name (extract f buffers) (base-name file)))
                                           (got (file-text file))
                                           (b (spawn-actor name (new-buffer name file (extract got text)))))
                                      (begin
                                        (tell! fr (buffer-made fr name file b))
                                        (if (extract got found) #u (tell! fr (echo "(New file)")))))))))))))))

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
        (read-completing f "Find file: " dir (sum files #u)
                     (lambda ((fr (actor frame)) (f frame) (typed string))
                       (let* ((file (expand-file-name typed dir))
                              (n (string-length file)))
                         ;; A directory's name with or without its last `/`.
                         (visit-file fr f (if (and (> n 1) (char=? (string-ref file (- n 1)) #\/))
                                              (substring file 0 (- n 1))
                                              file)))))))))

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
        (read-completing f (string-append "Switch to buffer" (if (string=? other "") "" (string-append " (default " other ")")) ": ")
                     ""
                     (sum names (letrec ((go (subr spin (buffer-infos) strings)
                                               (lambda (bs) (if (null? bs) nil (cons (extract (car bs) name) (go (cdr bs)))))))
                                  (go (extract f buffers))))
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
                                                            (let ((size (int->string (rope-length (extract st text)))))
                                                              (string-append size (if (< (string-length size) 8)
                                                                                      (substring "        " 0 (- 8 (string-length size)))
                                                                                      " ")))
                                                            (extract info file) "\n")
                                             (go (cdr bs))))))))
                      (go (extract f buffers))))
             (text (string->rope (apply string-append (the strings (cons " M Name                    Size    File\n" lines)))))
             (name "*Buffer List*"))
        (tagcase (find-buffer (extract f buffers) name)
          (found info (reply-with f (list (tell (extract info actor) (replace-text text))
                                          (tell fr (lambda ((f frame)) (show-buffer fr f (extract info actor)))))))
          (none u (let ((b (spawn-actor name (new-buffer name "" text))))
                    (reply-with f (list (lambda () (tell! fr (buffer-made fr name "" b))))))))))))

"C-x C-c: the editor ended -- after asking, if a buffer visiting a file
has changes not saved."
(define* save-buffers-kill-editor (subr pure () frame-action)
  (lambda ()
    (lambda ((fr (actor frame)) (f frame))
      (let ((unsaved (letrec ((go (subr turn-eff (buffer-infos) strings)
                                (lambda (bs)
                                  (cond ((null? bs) nil)
                                        ((and (not (string=? (extract (car bs) file) ""))
                                              (extract (actor-state (extract (car bs) actor)) modified))
                                         (cons (extract (car bs) name) (go (cdr bs))))
                                        (else (go (cdr bs)))))))
                       (go (extract f buffers)))))
        (if (null? unsaved)
            (reply-with f (list (lambda () (set running #f))))
            (read-string f (string-append "Modified buffers exist (" (car unsaved)
                                          (if (pair? (cdr unsaved)) ", …" "") "); exit anyway? (yes or no) ")
                         ""
                         (lambda ((fr (actor frame)) (f frame) (answer string))
                           (if (string=? answer "yes")
                               (reply-with f (list (lambda () (set running #f))))
                               (draw (with-echo f ""))))))))))

;;; ------------------------------------------------------------ definitions

"Where M-. has been from, newest first: a buffer and its point, for M-,."
(define-type place (productof (buffer (actor buffer)) (point int)))
(define places (ref (listof place acyclic) @ed) (new nil))

"Whether `c` can be in a symbol, as FX-26 reads one."
(define* symbol-char? (subr pure (char) bool)
  (lambda (c)
    (not (or (char-whitespace? c) (char-in? c "()[]\";'`,")))))

"The symbol point is in or just after, in `t`; \"\" if none."
(define* symbol-at (subr spin (rope int) string)
  (lambda (t p)
    (let ((n (rope-length t)))
      (letrec ((back (subr spin (int) int)
                 (lambda (i) (if (and (> i 0) (symbol-char? (rope-ref t (- i 1)))) (back (- i 1)) i)))
               (fwd (subr spin (int) int)
                 (lambda (i) (if (and (< i n) (symbol-char? (rope-ref t i))) (fwd (+ i 1)) i))))
        (let ((a (back p)) (b (fwd p)))
          (if (< a b) (rope-substring t a b) ""))))))

"Message for a buffer: point to `p`."
(define* goto-position (subr pure (int) command)
  (lambda (p) (lambda ((b buffer)) (done (with-point b p)))))

"The buffer that defines `name`, and where: the selected one first, then
the others in order."
(define* find-definition (subr turn-eff (frame (actor buffer) string) (sumof (none unit) (found place)))
  (lambda (f current name)
    (letrec ((in (subr spin (definitions) int)
               (lambda (ds) (cond ((null? ds) -1)
                                  ((string=? (extract (car ds) name) name) (extract (car ds) start))
                                  (else (in (cdr ds))))))
             (look (subr turn-eff ((actor buffer)) int)
               (lambda (b) (in (extract (extract (actor-state b) annotation) definitions))))
             (others (subr turn-eff (buffer-infos) (sumof (none unit) (found place)))
               (lambda (bs)
                 (if (null? bs)
                     (sum none #u)
                     (let ((at (look (extract (car bs) actor))))
                       (if (>= at 0)
                           (sum found (product (buffer (extract (car bs) actor)) (point at)))
                           (others (cdr bs))))))))
      (let ((here (look current)))
        (if (>= here 0)
            (sum found (product (buffer current) (point here)))
            (others (extract f buffers)))))))

"Go to place `pl`: its buffer shown in the selected window (if it is not),
and point there."
(define* go-to-place (subr turn-eff ((actor frame) frame place) (reply frame))
  (lambda (fr f pl)
    (let* ((b (extract pl buffer))
           (r (if (same-actor? b (extract (selected-window f) buffer)) (same f) (show-buffer fr f b))))
      (reply-with (extract r state)
                  (append (extract r cmds) (list (tell b (in-buffer fr (goto-position (extract pl point))))))))))

"Where Fixpt's built-in module files are, from the editor's directory:
`fx26:name` is this directory's `name`."
(define fixpt-sources string "../fixpt/crates/fixpt-fx26/src/")

"The file a `load-module` in `from` names as `f`: a built-in one in Fixpt's
sources, another beside `from`."
(define* linked-file (subr spin (string string) string)
  (lambda (from f)
    (if (and (> (string-length f) 5) (string=? (substring f 0 5) "fx26:"))
        (string-append fixpt-sources (substring f 5 (string-length f)))
        (string-append (directory-of from) f))))

(define* definition-in (subr spin (definitions string) int)
  (lambda (ds name)
    (cond ((null? ds) -1)
          ((string=? (extract (car ds) name) name) (extract (car ds) start))
          (else (definition-in (cdr ds) name)))))

"Visit `file` at the definition of `name` there (its start if there is
none): in the buffer that visits it, or, read and analysed in a command,
in a new one."
(define* visit-definition (subr turn-eff ((actor frame) frame string string) (reply frame))
  (lambda (fr f file name)
    (tagcase (find-file-buffer (extract f buffers) file)
      (found info
        (let ((st (actor-state (extract info actor))))
          (go-to-place fr f (product (buffer (extract info actor))
                                     (point (max 0 (definition-in (extract (extract st annotation) definitions) name)))))))
      (none u
        (let ((bname (unique-name (extract f buffers) (base-name file))))
          (reply-with f
                      (list (lambda ()
                              (let* ((got (file-text file))
                                     (at (if (extract got found)
                                             (definition-in (extract (analyze (rope->string (extract got text)) 0) definitions) name)
                                             -1))
                                     (b (spawn-actor bname (new-buffer bname file (extract got text)))))
                                (begin
                                  (tell! fr (buffer-made fr bname file b))
                                  (tell! b (in-buffer fr (goto-position (max 0 at))))
                                  (if (extract got found) #u
                                      (tell! fr (echo (string-append "No file " file))))))))))))))

"FX-26's special forms: what the checker reads itself, as expressions,
definitions and declarations, not procedures (Fixpt's parse.rs, the heads
its expressions are told by; top.rs, KEYWORDS; syn.rs)."
(define special-forms strings
  (list "lambda" "vlambda" "rlambda" "plambda" "dlambda" "proj" "if" "cond" "case" "else" "=>" "and" "or"
        "let" "let*" "letrec" "letrena" "letreap" "begin" "the" "quote" "quasiquote" "tagcase" "typecase"
        "product" "extract" "sum" "with" "select" "prompt" "goto" "comefrom" "await"
        "confirm-length" "confirm-nat" "acyclic" "convention" "extend"
        "spawn" "spawn-monitored" "send" "receive" "self" "par" "race" "attempt" "pselect"
        "define" "define*" "define-rec" "define-type" "define-generative"
        "define-effect" "define-convention" "define-datatype" "module" "module-parameters"
        "load-module" "import" "make-bloblet" "rmake-bloblet" "bloblet-ref" "bloblet-set!"
        "bloblet-freeze" "bloblet-byte" "bloblet-set-byte!" "bloblet-bytes" "blobref-at" "blobref+"
        "blobref-owner" "blobref-offset" "blobref-get" "blobref-set!" "blobref-index" "blobref-length"
        "blobref-variant!"))

"FX-26's type syntax: the forms a type is written with, its effects, and
its base types (parse.rs, TYPE_FORMS and its effect atoms; check.rs)."
(define type-syntax strings
  (list "subr" "vsubr" "->" "->*" "poly" "mu" "listof" "nlist" "pairof" "arrayof" "narrayof" "productof"
        "sumof" "union" "ref" "icell" "bloblet" "place" "moduleof" "proves" "items" "composable"
        "oneshot" "prompt-tag" "mark-key" "dletrec" "nat"
        "pure" "spin" "maxeff" "read" "write" "alloc" "io" "region" "effect" "type" "init" "const"
        "int" "bool" "string" "unit" "char" "symbol" "false" "f32" "f64" "i8" "u8" "i32" "u32" "i64" "u64"
        "bytevector" "tword" "wcell" "wglobal"))

"M-. on a name the program does not define: said to be a special form or
type syntax of FX-26, if it is; else one of its standard names, with its
type, if Fixpt's table of them (standard.rs, where the checker learns
their types) has it. Read in a command."
(define* say-standard (subr pure ((actor frame) string) cmd)
  (lambda (fr name)
    (lambda ()
      (cond ((member? name special-forms)
             (tell! fr (echo (string-append name " is a special form of FX-26, so has no definition here"))))
            ((member? name type-syntax)
             (tell! fr (echo (string-append name " is type syntax of FX-26, so has no definition here"))))
            (else
             (let* ((got (file-text (string-append fixpt-sources "standard.rs")))
                    (s (if (extract got found) (rope->string (extract got text)) ""))
                    (key (string-append "(\"" name "\", \""))
                    (at (string-search s key 0))
                    (to (if (< at 0) -1 (string-search s "\")," (+ at (string-length key))))))
               (tell! fr (echo (if (< to 0)
                                   (string-append "No definition of " name " found")
                                   (string-append name " is built in to FX-26, so has no definition here: "
                                                  (substring s (+ at (string-length key)) to)))))))))))

"Go to place `pl`; or, if a name imported from a file is there, on to its
definition in that file."
(define* land (subr turn-eff ((actor frame) frame place) (reply frame))
  (lambda (fr f pl)
    (let* ((st (actor-state (extract pl buffer)))
           (lk (letrec ((go (subr spin (links) string)
                          (lambda (ls) (cond ((null? ls) "")
                                             ((= (extract (car ls) start) (extract pl point)) (extract (car ls) file))
                                             (else (go (cdr ls)))))))
                 (go (extract (extract st annotation) links)))))
      (if (string=? lk "")
          (go-to-place fr f pl)
          (visit-definition fr f (linked-file (extract st file) lk) (symbol-at (extract st text) (+ 1 (extract pl point))))))))

"M-.: the definition of the name at point. Its binder in this text, if it
is here; else a definition in a buffer, else in the index; a standard
name, said to be one (`say-standard`); through an `import`, on to the file
the name comes from."
(define* find-definition-at-point (subr pure () frame-action)
  (lambda ()
    (lambda ((fr (actor frame)) (f frame))
      (let* ((current (extract (selected-window f) buffer))
             (st (actor-state current))
             (name (symbol-at (extract st text) (extract st point)))
             (bound (tagcase (reference-at st) (found r (extract r binder-start)) (none u -1)))
             (from (lambda ((r (reply frame)))
                     ;; Where M-. was from, kept for M-,.
                     (reply-with (extract r state)
                                 (cons (lambda () (set places (cons (product (buffer current) (point (extract st point)))
                                                                    (get places))))
                                       (extract r cmds))))))
        (cond
          ((string=? name "") (draw (with-echo f "No name at point")))
          ((>= bound 0) (from (land fr f (product (buffer current) (point bound)))))
          (else
           (tagcase (find-definition f current name)
             (found pl (from (land fr f pl)))
             (none u
               (tagcase (index-lookup name)
                 (found hit
                   (from (visit-definition fr f
                                           (if (string=? (extract hit link) "")
                                               (extract hit file)
                                               (linked-file (extract hit file) (extract hit link)))
                                           name)))
                 (none u2 (reply-with f (list (say-standard fr name)))))))))))))

"M-,: back to where the last M-. was from."
(define* pop-definition (subr pure () frame-action)
  (lambda ()
    (lambda ((fr (actor frame)) (f frame))
      (let ((ps (get places)))
        (if (null? ps)
            (draw (with-echo f "No previous location"))
            (let ((r (go-to-place fr f (car ps))))
              (reply-with (extract r state) (cons (lambda () (set places (cdr (get places)))) (extract r cmds)))))))))

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

"Message for buffer `self`: its text written to its file, in a command;
then the buffer marked saved and the frame told so -- or, if the write
failed, told why, and the buffer left modified."
(define* save-buffer-to (subr pure ((actor frame) (actor buffer)) (msg buffer))
  (lambda (fr self)
    (lambda ((b buffer))
      (let ((file (extract b file)) (rev (extract b revision)) (text (rope->string (extract b text))))
        (if (string=? file "")
            (reply-with b (list (tell fr (echo "This buffer has no file"))))
            (reply-with b (list (lambda ()
                                  (tagcase (write-file file (string->utf8 text))
                                    (done u (begin (tell! self (marked-saved rev))
                                              (tell! fr (echo (string-append "Wrote " file)))))
                                    (failed e (tell! fr (echo (string-append "Could not write " file ": "
                                                                             (extract e detail))))))))))))))

"C-x C-s: the selected buffer saved."
(define* save-buffer (subr pure () frame-action)
  (lambda ()
    (lambda ((fr (actor frame)) (f frame))
      (let ((b (extract (selected-window f) buffer))) (reply-with f (list (tell b (save-buffer-to fr b))))))))

(define-type named (productof (name string) (action action)))
"Commands and keys that files after this one add (`define-command!`,
`define-key!`), looked up after the built-in ones: how the editor is
extended, as Emacs's is, by tables it consults each time."
(define more-commands (ref (listof named acyclic) @ed) (new nil))
(define more-keys (ref (listof (productof (keys string) (command string)) acyclic) @ed) (new nil))
"Keys bound in buffers of one name only (*xref*'s RET), or of one kind
(`buffer-kind`), looked up first."
(define buffer-keys (ref (listof (productof (buffer string) (keys string) (command string)) acyclic) @ed) (new nil))

"What C-h k does with the keys it read (as `keys->string` writes them)
and the name of their command (\"\": none): help.fx makes it show a
description; until then, the echo area says the name."
(define key-describer (ref (subr pure (string string) frame-action) @ed)
  (new (lambda ((ks string) (name string))
         (lambda ((fr (actor frame)) (f frame))
           (draw (with-echo f (if (string=? name "") (string-append ks " is undefined")
                                  (string-append ks " runs the command " name))))))))

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
            (buffer-command "newline" (newline-and-indent))
            (buffer-command "indent-for-tab-command" (indent-for-tab))
            (buffer-command "set-mark-command" (set-mark))
            (buffer-command "exchange-point-and-mark" (exchange-point-and-mark))
            (buffer-command "kill-region" (kill-region))
            (buffer-command "kill-ring-save" (copy-region))
            (buffer-command "kill-line" (kill-line))
            (buffer-command "yank" (yank))
            (buffer-command "undo" (undo))
            (buffer-command "keyboard-quit" (keyboard-quit))
            (frame-command "save-buffer" (save-buffer))
            (buffer-command "fail-on-purpose" (fail-on-purpose))
            (frame-command "isearch-forward" (isearch #t))
            (frame-command "isearch-backward" (isearch #f))
            (frame-command "xref-find-definitions" (find-definition-at-point))
            (frame-command "xref-go-back" (pop-definition))
            (buffer-command "xref-find-references" (show-uses))
            (buffer-command "next-use" (next-mark 1))
            (buffer-command "previous-use" (next-mark -1))
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
        (go (append (commands) (get more-commands))))))
  (execute-extended-command (->* () frame-action)
    (lambda ()
      (lambda ((fr (actor frame)) (f frame))
        (read-completing f "M-x " ""
                     (sum names (letrec ((go (subr spin ((listof named acyclic)) strings)
                                               (lambda (cs) (if (null? cs) nil (cons (extract (car cs) name) (go (cdr cs)))))))
                                  (go (append (commands) (get more-commands)))))
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
        (product (keys "M-.") (command "xref-find-definitions")) (product (keys "M-,") (command "xref-go-back"))
        (product (keys "M-?") (command "xref-find-references"))
        (product (keys "M-n") (command "next-use")) (product (keys "M-p") (command "previous-use"))
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

"Paredit's keys, while M-x paredit-mode has it on."
(define paredit-keys (listof (productof (keys string) (command string)) acyclic)
  (list (product (keys "(") (command "paredit-open-round"))
        (product (keys ")") (command "paredit-close-round"))
        (product (keys "\"") (command "paredit-doublequote"))
        (product (keys "DEL") (command "paredit-backward-delete"))
        (product (keys "C-d") (command "paredit-forward-delete"))
        (product (keys "C-k") (command "paredit-kill"))))

"The prefixes: key sequences that are the start of longer bindings."
(define prefixes strings (list "C-x" "C-c" "M-g" "C-h" "ESC" "C-x ESC" "C-c ESC" "C-h ESC"))

"The name of the command `ks` is bound to in buffer `buffer-name`, or \"\"."
(define* binding-name (subr (maxeff (read @ed) spin) (keys string) string)
  (lambda (ks buffer-name)
    (let ((s (keys->string ks)))
      (letrec ((bound (subr spin ((listof (productof (keys string) (command string)) acyclic)) string)
                 (lambda (m) (cond ((null? m) "")
                                   ((string=? (extract (car m) keys) s) (extract (car m) command))
                                   (else (bound (cdr m)))))))
        (let ((n (letrec ((local (subr spin ((listof (productof (buffer string) (keys string) (command string)) acyclic)) string)
                            (lambda (m) (cond ((null? m) "")
                                              ((and (or (string=? (extract (car m) buffer) buffer-name)
                                                        (string=? (extract (car m) buffer) (buffer-kind buffer-name)))
                                                    (string=? (extract (car m) keys) s))
                                               (extract (car m) command))
                                              (else (local (cdr m)))))))
                   (local (get buffer-keys)))))
          (cond ((not (string=? n "")) n)
                ;; Paredit's keys, while it is on, in FX-26 buffers.
                ((and (get paredit-on) (fx26-file? buffer-name)
                      (not (string=? (bound paredit-keys) "")))
                 (bound paredit-keys))
                ((not (string=? (bound keymap) "")) (bound keymap))
                (else (bound (get more-keys)))))))))

"What `ks` does: a command, more keys to come, or nothing."
(define* binding (subr (maxeff (read @ed) spin) (keys string) (sumof (command action) (prefix unit) (undefined unit)))
  (lambda (ks buffer-name)
    (let ((s (keys->string ks)) (name (binding-name ks buffer-name)))
      (letrec ((prefix? (subr spin (strings) bool)
                 (lambda (ps) (and (pair? ps) (or (string=? (car ps) s) (prefix? (cdr ps)))))))
        (cond ((not (string=? name ""))
               (tagcase (command-named name) (found a (sum command a)) (none u (sum undefined #u))))
              ((prefix? prefixes) (sum prefix #u))
              ((and (pair? ks) (null? (cdr ks)))
               (typecase (car ks)
                 (char c (sum command (sum on-buffer (self-insert c))))
                 (else y (sum undefined #u))))
              (else (sum undefined #u)))))))

;;; ------------------------------------------------------------ keys

"`m` with text `t`, point at `q`, and hint `h`."
(define* mini-with (subr pure (minibuffer string int string) minibuffer)
  (lambda (m t q h)
    (product (prompt (extract m prompt)) (text t) (point q) (then (extract m then))
             (complete (extract m complete)) (hint h))))

"Whether `s` starts with `pre`."
(define* starts-with? (subr spin (string string) bool)
  (lambda (s pre)
    (and (<= (string-length pre) (string-length s)) (string=? (substring s 0 (string-length pre)) pre))))

"TAB on `typed`, among `names`: the longest start that all the names
starting with it share, and what to say after it -- nothing, or no
match, the sole completion, or the names it could be."
(define* complete-among (subr spin (string strings) (productof (text string) (hint string)))
  (lambda (typed names)
    (let ((ms (letrec ((go (subr spin (strings) strings)
                         (lambda (l) (cond ((null? l) nil)
                                           ((starts-with? (car l) typed) (cons (car l) (go (cdr l))))
                                           (else (go (cdr l)))))))
                (go names))))
      (if (null? ms)
          (product (text typed) (hint " [No match]"))
          (let ((shared (letrec ((common (subr spin (string strings) string)
                                   (lambda (pre l)
                                     (if (null? l) pre
                                         (let ((s (car l)))
                                           (letrec ((upto (subr spin (int) int)
                                                      (lambda (i) (if (and (< i (string-length pre)) (< i (string-length s))
                                                                           (char=? (string-ref pre i) (string-ref s i)))
                                                                      (upto (+ i 1)) i))))
                                             (common (substring pre 0 (upto 0)) (cdr l))))))))
                          (common (car ms) (cdr ms)))))
            (cond ((> (string-length shared) (string-length typed)) (product (text shared) (hint "")))
                  ((null? (cdr ms)) (product (text typed) (hint " [Sole completion]")))
                  (else (product (text typed)
                                 (hint (string-append " {" (letrec ((join (subr spin (strings) string)
                                                                        (lambda (l) (if (null? (cdr l)) (car l)
                                                                                        (string-append (car l) " | " (join (cdr l)))))))
                                                             (join ms))
                                                      "}"))))))))))

"Message for the frame: TAB's completion of `typed` in the minibuffer,
`text` and `hint`, if it still reads `typed`."
(define* mini-completed (subr pure (string string string) (msg frame))
  (lambda (typed text hint)
    (lambda ((f frame))
      (tagcase (extract f mini)
        (reading m (if (string=? (extract m text) typed)
                       (draw (with-mini f (sum reading (mini-with m text (string-length text) hint))))
                       (same f)))
        (else y (same f))))))

"TAB on file name `typed`: completed among the names in its directory,
in a command; a sole completion that is a directory gets a `/`."
(define* complete-file (subr pure ((actor frame) string) cmd)
  (lambda (fr typed)
    (lambda ()
      (let* ((dir (directory-of typed))
             (base (substring typed (string-length dir) (string-length typed)))
             (names (tagcase (the (sumof (names (listof string @pf)) (failed io-error)) (list-dir (if (string=? dir "") "." dir)))
                      (names ns (letrec ((copy (->* ((listof string @pf)) strings)
                                           (lambda (l) (if (null? l) nil (cons (car l) (copy (cdr l)))))))
                                  (copy ns)))
                      (failed e nil)))
             (c (complete-among base names))
             (text (string-append dir (extract c text)))
             (dir? (and (member? (extract c text) names)
                        (tagcase (the (sumof (names (listof string @pf)) (failed io-error)) (list-dir text))
                          (names ns #t) (failed e #f)))))
        (tell! fr (mini-completed typed (if dir? (string-append text "/") text)
                                  (if dir? "" (extract c hint))))))))

"A key typed while the minibuffer reads."
(define* minibuffer-key (subr turn-eff ((actor frame) frame minibuffer key) (reply frame))
  (lambda (fr f m k)
    (let* ((text (extract m text)) (p (extract m point)) (n (string-length text))
           (edit (lambda ((t string) (q int)) (draw (with-mini f (sum reading (mini-with m t q ""))))))
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
            (("TAB")
             (tagcase (extract m complete)
               (nothing u (same f))
               (files u (reply-with f (list (complete-file fr text))))
               (names ns (let ((c (complete-among text ns)))
                           (draw (with-mini f (sum reading (mini-with m (extract c text) (string-length (extract c text))
                                                                      (extract c hint)))))))))
            (else (same f))))))))

"Keys `ks` then `k`: after ESC, `k` with Meta instead (ESC x is M-x, as
in Emacs, for terminals without a Meta key)."
(define* keys-then (subr spin (keys key) keys)
  (lambda (ks k)
    (cond ((null? ks) (list k))
          ((and (null? (cdr ks)) (key=? (car ks) 'ESC)) (list (meta-key k)))
          (else (cons (car ks) (keys-then (cdr ks) k))))))

"Whether `ks` is C-h k and the keys it describes."
(define* describing? (subr pure (keys) bool)
  (lambda (ks)
    (and (pair? ks) (key=? (car ks) 'C-h) (pair? (cdr ks)) (key=? (car (cdr ks)) #\k) (pair? (cdr (cdr ks))))))

"A key typed with no minibuffer or search: looked up, with any prefix.
After C-h k, the keys are described (`key-describer`), not run."
(define* dispatch-key (subr turn-eff ((actor frame) frame key) (reply frame))
  (lambda (fr f k)
    (let* ((ks (keys-then (extract f prefix) k))
           (cleared (with-echo (with-prefix f nil) ""))
           (bname (extract (actor-state (extract (selected-window f) buffer)) name)))
      (if (describing? ks)
          (let* ((rest (cdr (cdr ks)))
                 (describe (lambda ((name string))
                             (run-action fr cleared (sum on-frame ((get key-describer) (keys->string rest) name))))))
            (tagcase (binding rest bname)
              (prefix u (draw (with-echo (with-prefix f ks) (string-append "Describe key: " (keys->string rest) "-"))))
              (command a (let ((n (binding-name rest bname)))
                           (describe (if (string=? n "") "self-insert-command" n))))
              (undefined u (describe ""))))
        (tagcase (binding ks bname)
          (command a (let ((r (run-action fr cleared a)))
                       ;; The echo area cleared, and shown so, if it said something.
                       (if (string=? (extract f echo) "")
                           r
                           (reply-with (extract r state)
                                       (append (extract r cmds) (extract (draw (extract r state)) cmds))))))
          (prefix u (draw (with-echo (with-prefix f ks) (string-append (keys->string ks) "-"))))
          (undefined u (draw (with-echo (with-prefix f nil)
                                        (string-append (keys->string ks) " is undefined")))))))))

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
                           (cons (product (name name) (file file) (actor b)) (extract f buffers))
                           (+ id 1) (extract f echo) (extract f prefix) (extract f mini))))
        (reply-with f2 (append (attach-syntax b name) (append (index-directory-of file) (extract made cmds))))))))

"A command added by name, for M-x and keys."
(define* define-command! (subr (maxeff (read @ed) (write @ed)) (string action) unit)
  (lambda (name a) (set more-commands (cons (product (name name) (action a)) (get more-commands)))))

"Keys bound to a command's name."
(define* define-key! (subr (maxeff (read @ed) (write @ed)) (string string) unit)
  (lambda (ks name) (set more-keys (cons (product (keys ks) (command name)) (get more-keys)))))

"Keys bound in buffers named `buffer` only."
(define* define-buffer-key! (subr (maxeff (read @ed) (write @ed)) (string string string) unit)
  (lambda (buffer ks name)
    (set buffer-keys (cons (product (buffer buffer) (keys ks) (command name)) (get buffer-keys)))))

;;; ------------------------------------------------------------ sexps and paredit (sexp.fx)

(define* paredit-mode (subr pure () frame-action)
  (lambda ()
    (lambda ((fr (actor frame)) (f frame))
      (let ((on (not (get paredit-on))))
        (reply-with (extract (draw (with-echo f (if on "Paredit mode enabled (in FX-26 buffers)" "Paredit mode disabled"))) state)
                    (cons (lambda () (set paredit-on on))
                          (extract (draw (with-echo f (if on "Paredit mode enabled (in FX-26 buffers)" "Paredit mode disabled"))) cmds)))))))

(hide (define frame-reg-1 (define-command! "paredit-mode" (sum on-frame (paredit-mode)))))
(hide (define frame-reg-2 (define-command! "forward-sexp" (sum on-buffer (sexp-motion forward-sexp "No sexp after point")))))
(hide (define frame-reg-3 (define-command! "backward-sexp" (sum on-buffer (sexp-motion backward-sexp "No sexp before point")))))
(hide (define frame-reg-4 (define-command! "backward-up-list" (sum on-buffer (sexp-motion up-list "Not in a list")))))
(hide (define frame-reg-5 (define-command! "down-list" (sum on-buffer (sexp-motion down-list "No list after point")))))
(hide (define frame-reg-6 (define-command! "kill-sexp" (sum on-buffer (kill-sexp)))))
(hide (define frame-reg-7 (define-command! "paredit-open-round" (sum on-buffer (paredit-open)))))
(hide (define frame-reg-8 (define-command! "paredit-close-round" (sum on-buffer (paredit-close)))))
(hide (define frame-reg-9 (define-command! "paredit-doublequote" (sum on-buffer (paredit-doublequote)))))
(hide (define frame-reg-10 (define-command! "paredit-backward-delete" (sum on-buffer (paredit-backward-delete)))))
(hide (define frame-reg-11 (define-command! "paredit-forward-delete" (sum on-buffer (paredit-forward-delete)))))
(hide (define frame-reg-12 (define-command! "paredit-kill" (sum on-buffer (paredit-kill)))))
(hide (define frame-reg-13 (define-command! "paredit-forward-slurp-sexp" (sum on-buffer (slurp-forward)))))
(hide (define frame-reg-14 (define-command! "paredit-forward-barf-sexp" (sum on-buffer (barf-forward)))))
(hide (define frame-reg-15 (define-command! "paredit-splice-sexp" (sum on-buffer (splice-sexp)))))
(hide (define frame-reg-16 (define-command! "paredit-raise-sexp" (sum on-buffer (raise-sexp)))))
(hide (define frame-reg-17 (define-command! "paredit-wrap-round" (sum on-buffer (wrap-round)))))
(hide (define frame-reg-18 (define-key! "C-M-f" "forward-sexp")))
(hide (define frame-reg-19 (define-key! "C-M-b" "backward-sexp")))
(hide (define frame-reg-20 (define-key! "C-M-u" "backward-up-list")))
(hide (define frame-reg-21 (define-key! "C-M-d" "down-list")))
(hide (define frame-reg-22 (define-key! "C-M-k" "kill-sexp")))
(hide (define frame-reg-23 (define-key! "C-<right>" "paredit-forward-slurp-sexp")))
(hide (define frame-reg-24 (define-key! "C-<left>" "paredit-forward-barf-sexp")))
(hide (define frame-reg-25 (define-key! "M-s" "paredit-splice-sexp")))
(hide (define frame-reg-26 (define-key! "M-r" "paredit-raise-sexp")))
(hide (define frame-reg-27 (define-key! "M-(" "paredit-wrap-round")))

;;; ------------------------------------------------------------ lines, files, buffers

"The number `s` writes in decimal, or -1 (FX-26 has no string->int yet:
Fixpt's TODO §75)."
(define* digits-value (subr spin (string) int)
  (lambda (s)
    (letrec ((go (subr spin (int int) int)
               (lambda (i acc)
                 (cond ((>= i (string-length s)) acc)
                       ((char-numeric? (string-ref s i)) (go (+ i 1) (+ (* 10 acc) (- (char->integer (string-ref s i)) 48))))
                       (else -1)))))
      (if (= (string-length s) 0) -1 (go 0 0)))))

(define* goto-line-command (subr pure () frame-action)
  (lambda ()
    (lambda ((fr (actor frame)) (f frame))
      (read-string f "Goto line: " ""
                   (lambda ((fr (actor frame)) (f frame) (s string))
                     (let ((n (digits-value s)))
                       (if (< n 1)
                           (draw (with-echo f "Not a line number"))
                           (reply-with f (list (tell (extract (selected-window f) buffer) (in-buffer fr (goto-line n))))))))))))

"C-x C-w: the buffer written to another file, which it visits from then on."
(define* write-file-command (subr pure () frame-action)
  (lambda ()
    (lambda ((fr (actor frame)) (f frame))
      (let ((b (extract (selected-window f) buffer)))
        (read-completing f "Write file: " (directory-of (extract (actor-state b) file)) (sum files #u)
                     (lambda ((fr (actor frame)) (f frame) (typed string))
                       (let ((file (expand-file-name typed (directory-of (extract (actor-state b) file)))))
                         (reply-with (frame-of f (extract f windows) (extract f selected)
                                               (letrec ((go (subr spin (buffer-infos) buffer-infos)
                                                          (lambda (bs) (cond ((null? bs) nil)
                                                                             ((same-actor? (extract (car bs) actor) b)
                                                                              (cons (product (name (base-name file)) (file file) (actor b)) (cdr bs)))
                                                                             (else (cons (car bs) (go (cdr bs))))))))
                                                 (go (extract f buffers)))
                                               (extract f next-id) (extract f echo) (extract f prefix) (extract f mini))
                                     (list (tell b (in-buffer fr (set-visited-file file)))
                                           (tell b (save-buffer-to fr b)))))))))))

"C-x k: a buffer killed (the selected one, by default): no longer listed,
and the windows that show it showing another, or *scratch* made anew."
(define* kill-buffer-command (subr pure () frame-action)
  (lambda ()
    (lambda ((fr (actor frame)) (f frame))
      (let ((current (extract (actor-state (extract (selected-window f) buffer)) name)))
        (read-string f (string-append "Kill buffer (default " current "): ") ""
                     (lambda ((fr (actor frame)) (f frame) (name string))
                       (let ((name (if (string=? name "") current name)))
                         (tagcase (find-buffer (extract f buffers) name)
                           (none u (draw (with-echo f (string-append "No buffer named " name))))
                           (found info
                             (let* ((gone (extract info actor))
                                    (rest (letrec ((go (subr spin (buffer-infos) buffer-infos)
                                                     (lambda (bs) (cond ((null? bs) nil)
                                                                        ((same-actor? (extract (car bs) actor) gone) (go (cdr bs)))
                                                                        (else (cons (car bs) (go (cdr bs))))))))
                                            (go (extract f buffers))))
                                    (f2 (frame-of f (extract f windows) (extract f selected) rest (extract f next-id)
                                                  (string-append "Killed " name) (extract f prefix) (extract f mini))))
                               (if (null? rest)
                                   ;; The last: *scratch* made, then shown where it was.
                                   (let ((b (spawn-actor "*scratch*" (new-buffer "*scratch*" "" empty-rope))))
                                     (reply-with f2 (list (lambda () (tell! fr (buffer-made fr "*scratch*" "" b))))))
                                   ;; Each window that showed it shows the first other buffer.
                                   (let ((other (extract (car rest) actor)))
                                     (letrec ((swap (subr turn-eff (frame windows) (reply frame))
                                                (lambda (f ws)
                                                  (cond ((null? ws) (draw f))
                                                        ((same-actor? (extract (car ws) buffer) gone)
                                                         (let* ((sel (frame-of f (extract f windows) (extract (car ws) id) (extract f buffers)
                                                                               (extract f next-id) (extract f echo) (extract f prefix) (extract f mini)))
                                                                (r (show-buffer fr sel other))
                                                                (back (frame-of (extract r state) (extract (extract r state) windows)
                                                                                (if (= (extract (car ws) id) (extract f selected))
                                                                                    (extract (extract r state) selected) (extract f selected))
                                                                                (extract f buffers) (extract (extract r state) next-id)
                                                                                (extract f echo) (extract f prefix) (extract f mini)))
                                                                (more (swap back (cdr ws))))
                                                           (reply-with (extract more state) (append (extract r cmds) (extract more cmds)))))
                                                        (else (swap f (cdr ws)))))))
                                       (swap f2 (extract f2 windows)))))))))))))))

(hide (define frame-reg-28 (define-command! "kill-word" (sum on-buffer (kill-word 1)))))
(hide (define frame-reg-29 (define-command! "backward-kill-word" (sum on-buffer (kill-word -1)))))
(hide (define frame-reg-30 (define-command! "open-line" (sum on-buffer (open-line)))))
(hide (define frame-reg-31 (define-command! "goto-line" (sum on-frame (goto-line-command)))))
(hide (define frame-reg-32 (define-command! "write-file" (sum on-frame (write-file-command)))))
(hide (define frame-reg-33 (define-command! "kill-buffer" (sum on-frame (kill-buffer-command)))))
(hide (define frame-reg-34 (define-key! "M-d" "kill-word")))
(hide (define frame-reg-35 (define-key! "M-DEL" "backward-kill-word")))
(hide (define frame-reg-36 (define-key! "C-o" "open-line")))
(hide (define frame-reg-37 (define-key! "M-g g" "goto-line")))
(hide (define frame-reg-38 (define-key! "M-g M-g" "goto-line")))
(hide (define frame-reg-39 (define-key! "C-x C-w" "write-file")))
(hide (define frame-reg-40 (define-key! "C-x k" "kill-buffer")))
))
