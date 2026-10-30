;;; files.fx: working across several files and buffers.
;;;
;;;   C-x d, C-x C-f DIR   a listing of a directory (Yank's dired): each
;;;                        name's kind and permissions, size, time (UTC)
;;;   RET, f, e, o, ^      in a listing: the file on this line visited (o:
;;;                        in another window); ^ the directory above
;;;   m, u, DEL, U, d      marked *, unmarked (DEL: up a line first), all
;;;                        unmarked; flagged D
;;;   x, D                 those flagged D deleted; D: those marked, or
;;;                        this line's -- after asking; a directory whole
;;;   R, C, +              those marked, or this line's, renamed (moved) or
;;;                        copied; a directory made, and its parents
;;;   g in a listing       the listing read again, marks and point kept
;;;   RET in *Buffer List* the buffer on this line, shown
;;;   C-x s                each file changed and not saved, saved if you say so
;;;   M-x revert-buffer    the buffer's file read again
;;;   C-x d, M-x dired     a directory read, and its listing visited
;;;   C-x C-d              a directory's names (`ls -F`), shown in *Directory*
(module-parameters ((m-base (load-moduleof "base.fx"))
                    (m-buffer (load-moduleof "buffer.fx" m-base))
                    (m-resolve (load-moduleof "resolve.fx" m-base m-buffer))
                    (m-syntax (load-moduleof "syntax.fx" m-base m-buffer m-resolve))
                    (m-sexp (load-moduleof "sexp.fx" m-base m-buffer m-resolve m-syntax))
                    (m-index (load-moduleof "index.fx" m-base m-buffer m-resolve m-syntax m-sexp))
                    (m-view (load-moduleof "view.fx" m-base m-buffer m-resolve m-syntax m-sexp m-index))
                    (m-frame (load-moduleof "frame.fx" m-base m-buffer m-resolve m-syntax m-sexp m-index m-view))
                    (m-calls (load-moduleof "calls.fx" m-base m-buffer m-resolve m-syntax m-sexp m-index m-view m-frame))
                    (m-process (load-moduleof "process.fx" m-base m-buffer m-resolve m-syntax m-sexp m-index m-view m-frame m-calls))))
(hide (define kit-strings (load-module "../kit/strings.fx"))
      (import kit-strings string-prefix?)
      (define kit-lists (load-module "../kit/lists.fx"))
      (import kit-lists map any))

"The text of the line point is on in `st`, and its number."
(define* point-line (subr spin (buffer) (productof (text string) (line int)))
  (lambda (st)
    (let* ((t (extract st text)) (i (rope-line-of t (extract st point))))
      (product (text (rope-substring t (rope-line-start t i) (rope-line-end t i))) (line i)))))

"RET, f, e in a listing: the name on this line visited, relative to the
directory the listing is of; o, in another window."
(define* listing-visit (subr pure (bool) frame-action)
  (lambda (other)
    (lambda ((fr (actor frame)) (f frame))
      (let* ((st (actor-state (extract (selected-window f) buffer)))
             (l (point-line st))
             (s (extract l text))
             (dir (extract st file)))
        (tagcase (if (= (extract l line) 0) (sum none #u) (listing-name s))
          (none u (draw (with-echo f "No file on this line")))
          (some name
            (let ((file (if (string=? name "..") (simplify-directory (string-append dir "../")) (string-append dir name))))
              (if other
                  (and-then fr ((other-window-or-split) fr f) (lambda ((fr (actor frame)) (f frame)) (visit-file fr f file)))
                  (visit-file fr f file)))))))))

"^ in a listing: the directory above listed."
(define* listing-up (subr pure () frame-action)
  (lambda ()
    (lambda ((fr (actor frame)) (f frame))
      (let ((dir (extract (actor-state (extract (selected-window f) buffer)) file)))
        (if (string=? dir "/")
            (draw (with-echo f "No directory above /"))
            (visit-file fr f (simplify-directory (string-append dir "../"))))))))

"A listing's names and their marks: those of its lines with a mark."
(define* listing-marks (subr spin (rope) (listof (productof (name string) (mark char)) acyclic))
  (lambda (t)
    (letrec ((go (subr spin (int) (listof (productof (name string) (mark char)) acyclic))
               (lambda (line)
                 (if (>= line (- (rope-line-count t) 1)) nil
                     (let ((s (rope-substring t (rope-line-start t line) (rope-line-end t line))))
                       (tagcase (listing-name s)
                         (some name (if (and (> (string-length s) 0) (not (char=? (string-ref s 0) #\space)) (not (string=? name "..")))
                                        (cons (product (name name) (mark (string-ref s 0))) (go (+ line 1)))
                                        (go (+ line 1))))
                         (none u (go (+ line 1)))))))))
      (go 2))))

"Message for a listing: its text made `t`, point on line `line`, at its
name. Not a change: not modified, not undone."
(define* listing-refilled (subr pure (rope int) (msg buffer))
  (lambda (t line)
    (lambda ((b buffer))
      (let* ((n (max 0 (min line (- (rope-line-count t) 1))))
             (b2 (buffer-of b t (min (rope-line-end t n) (+ (rope-line-start t n) listing-name-column)) -1
                            (+ 1 (extract b revision)) #f (extract b undo) (extract b subscribers))))
        (reply-with b2 (notify b2))))))

"In a command: listing buffer `b` (of `dir`) made again, its marks kept
(`marks`), point at the file `at`, else at the first."
(define* listing-refill! (subr cmd-eff ((actor buffer) string (listof (productof (name string) (mark char)) acyclic) string) unit)
  (lambda (b dir marks at)
    (let ((l (listing-of dir marks at)))
      (tell! b (listing-refilled (string->rope (extract l text)) (extract l line))))))

"g in a listing (Yank's dired-revert): the directory listed again, its
marks kept on the files still there, point at the file it was at."
(define* dired-revert (subr pure () frame-action)
  (lambda ()
    (lambda ((fr (actor frame)) (f frame))
      (let* ((b (extract (selected-window f) buffer))
             (st (actor-state b))
             (here (tagcase (listing-name (extract (point-line st) text)) (some n n) (none u "")))
             (marks (listing-marks (extract st text))))
        (reply-with f (list (lambda () (listing-refill! b (extract st file) marks here))))))))

"U in a listing: every mark and flag taken off."
(define* dired-unmark-all (subr pure () command)
  (lambda ()
    (lambda ((b buffer))
      (let* ((t (extract b text))
             (t2 (letrec ((go (subr spin (rope int) rope)
                            (lambda (t line)
                              (if (>= line (- (rope-line-count t) 1)) t
                                  (let ((ls (rope-line-start t line)))
                                    (go (if (and (< ls (rope-length t)) (not (char=? (rope-ref t ls) #\space)))
                                            (rope-insert (rope-delete t ls (+ ls 1)) ls " ")
                                            t)
                                        (+ line 1)))))))
                   (go t 2))))
        (done (buffer-of b t2 (extract b point) (extract b mark) (+ 1 (extract b revision)) (extract b modified)
                         (extract b undo) (extract b subscribers)))))))

"The names a listing's command acts on: those marked *, else the one on
point's line."
(define* listing-targets (subr spin (buffer) strings)
  (lambda (st)
    (let ((marked (letrec ((go (subr spin ((listof (productof (name string) (mark char)) acyclic)) strings)
                             (lambda (ms) (cond ((null? ms) nil)
                                                ((char=? (extract (car ms) mark) #\*) (cons (extract (car ms) name) (go (cdr ms))))
                                                (else (go (cdr ms)))))))
                    (go (listing-marks (extract st text))))))
      (if (pair? marked) marked
          (let ((l (point-line st)))
            (tagcase (if (< (extract l line) 2) (sum none #u) (listing-name (extract l text)))
              (some n (if (string=? n "..") nil (list n)))
              (none u nil)))))))

"Names `ns` said: the one, or how many."
(define* describe-names (subr spin (strings) string)
  (lambda (ns) (if (and (pair? ns) (null? (cdr ns))) (car ns) (string-append (int->string (length ns)) " files"))))

"What the listings' file operations do: read and change the files, and
read the names `list-dir` gives (at @pf)."
(define-effect fs-eff (maxeff (io fs-read) (io fs-write) (read @pf) (alloc @pf) spin))
"What a file operation gave: done, or why not."
(define-type fs-outcome (sumof (done unit) (failed string)))
(define* fs-outcome-of (subr pure (string (sumof (done unit) (failed io-error))) fs-outcome)
  (lambda (path r) (tagcase r (done u (sum done #u)) (failed e (sum failed (string-append path ": " (extract e detail)))))))
(define* directory? (subr (io fs-read) (string) bool)
  (lambda (path) (tagcase (the (sumof (info file-facts) (failed io-error)) (file-info path))
                   (info i (tagcase (extract i kind) (directory u #t) (else y #f)))
                   (failed e #f))))

"`path` deleted, and if it is a directory (not a link to one), what is in
it first (rm -r)."
(define* delete-tree (subr fs-eff (string) fs-outcome)
  (lambda (path)
    (if (directory? path)
        (tagcase (the (sumof (names (listof string @pf)) (failed io-error)) (list-dir path))
          (names ns (letrec ((go (subr fs-eff ((listof string @pf)) fs-outcome)
                                   (lambda (l) (if (null? l) (fs-outcome-of path (delete-directory path))
                                                   (tagcase (delete-tree (string-append path "/" (car l)))
                                                     (done u (go (cdr l)))
                                                     (failed m (sum failed m)))))))
                      (go ns)))
          (failed e (sum failed (string-append path ": " (extract e detail)))))
        (fs-outcome-of path (delete-file path)))))

"`from` copied to `to`, and if it is a directory, what is in it (cp -R)."
(define* copy-tree (subr fs-eff (string string) fs-outcome)
  (lambda (from to)
    (if (directory? from)
        (tagcase (create-directory to)
          (done u (tagcase (the (sumof (names (listof string @pf)) (failed io-error)) (list-dir from))
                    (names ns (letrec ((go (subr fs-eff ((listof string @pf)) fs-outcome)
                                             (lambda (l) (if (null? l) (sum done #u)
                                                             (tagcase (copy-tree (string-append from "/" (car l)) (string-append to "/" (car l)))
                                                               (done u (go (cdr l)))
                                                               (failed m (sum failed m)))))))
                                (go ns)))
                    (failed e (sum failed (string-append from ": " (extract e detail))))))
          (failed e (sum failed (string-append to ": " (extract e detail)))))
        (fs-outcome-of from (copy-file from to)))))

"Directory `path` made, and its parents that are not (mkdir -p)."
(define* make-directories (subr fs-eff (string) fs-outcome)
  (lambda (path)
    (let ((n (string-length path)))
      (letrec ((go (subr fs-eff (int) fs-outcome)
                 ;; Each prefix of `path` ending at a `/` (or its end), from `i`.
                 (lambda (i)
                   (cond ((> i n) (sum done #u))
                         ((or (= i n) (char=? (string-ref path i) #\/))
                          (let ((p (substring path 0 i)))
                            (if (or (string=? p "") (directory? p))
                                (go (+ i 1))
                                (tagcase (fs-outcome-of p (create-directory p))
                                  (done u (go (+ i 1)))
                                  (failed m (sum failed m))))))
                         (else (go (+ i 1)))))))
        (go 1)))))

"Each of `ns` done by `op`, in order; the first failure stops it."
(define* each-file (subr fs-eff (strings (subr fs-eff (string) fs-outcome)) fs-outcome)
  (lambda (ns op)
    (if (null? ns) (sum done #u)
        (tagcase (op (car ns)) (done u (each-file (cdr ns) op)) (failed m (sum failed m))))))

"After a listing's operation: the listing of `dir` made again, marks
`marks` kept, and `said` (or the failure) in the echo area."
(define* after-listing-op! (subr cmd-eff ((actor frame) (actor buffer) string (listof (productof (name string) (mark char)) acyclic) string fs-outcome string) unit)
  (lambda (fr b dir marks at outcome said)
    (begin (listing-refill! b dir marks at)
      (tell! fr (echo (tagcase outcome (done u said) (failed m m)))))))

"A question answered y or n, then `yes` done."
(define* if-yes (subr turn-eff (frame string frame-action) (reply frame))
  (lambda (f question yes)
    (read-string f (string-append question "(y or n) ") ""
                 (lambda ((fr (actor frame)) (f frame) (answer string))
                   (if (string=? answer "y") (yes fr f) (draw (with-echo f "")))))))

"D in a listing: the files marked deleted, or the one on point's line,
after asking; x, those flagged D. A directory with what is in it."
(define* dired-delete (subr pure (bool) frame-action)
  (lambda (flagged)
    (lambda ((fr (actor frame)) (f frame))
      (let* ((b (extract (selected-window f) buffer))
             (st (actor-state b))
             (dir (extract st file))
             (marks (listing-marks (extract st text)))
             (ns (if flagged
                     (letrec ((go (subr spin ((listof (productof (name string) (mark char)) acyclic)) strings)
                                (lambda (ms) (cond ((null? ms) nil)
                                                   ((char=? (extract (car ms) mark) #\D) (cons (extract (car ms) name) (go (cdr ms))))
                                                   (else (go (cdr ms)))))))
                       (go marks))
                     (listing-targets st))))
        (cond ((and flagged (null? ns)) (draw (with-echo f "(No deletions requested)")))
              ((null? ns) (draw (with-echo f "No file on this line")))
              (else
               (if-yes f (string-append "Delete " (describe-names ns) (if flagged " flagged? " "? "))
                       (lambda ((fr (actor frame)) (f frame))
                         (reply-with f (list (lambda ()
                                               (after-listing-op! fr b dir marks ""
                                                                  (each-file ns (lambda ((n string)) (delete-tree (string-append dir n))))
                                                                  (string-append "Deleted " (describe-names ns))))))))))))))

"R (`copy` #f) and C (#t) in a listing: the files marked, or the one on
point's line, renamed (moved) or copied to a name read: one, to it (into
it, if a directory); several, into the directory read."
(define* dired-move-or-copy (subr pure (bool) frame-action)
  (lambda (copy)
    (lambda ((fr (actor frame)) (f frame))
      (let* ((b (extract (selected-window f) buffer))
             (st (actor-state b))
             (dir (extract st file))
             (marks (listing-marks (extract st text)))
             (ns (listing-targets st)))
        (if (null? ns)
            (draw (with-echo f "No file on this line"))
            (read-completing f (string-append (if copy "Copy " "Rename ") (describe-names ns) " to: ") dir (sum files #u)
                             (lambda ((fr (actor frame)) (f frame) (typed string))
                               (let ((to (if (and (> (string-length typed) 0) (char=? (string-ref typed 0) #\/)) typed (string-append dir typed))))
                                 (reply-with f (list (lambda ()
                                                       (let* ((into (directory? to))
                                                              (target (lambda ((n string))
                                                                        (if into (string-append to (if (char=? (string-ref to (- (string-length to) 1)) #\/) "" "/") n) to)))
                                                              ;; A directory into itself, or below itself, would
                                                              ;; never end (cp -R makes z/z/z/...).
                                                              (inside (lambda ((n string))
                                                                        (let ((src (simplify-directory (string-append dir n "/")))
                                                                              (dst (simplify-directory (string-append (target n) "/"))))
                                                                          (and (>= (string-length dst) (string-length src))
                                                                               (string=? (substring dst 0 (string-length src)) src)))))
                                                              (outcome (cond ((and (pair? (cdr ns)) (not into))
                                                                              (sum failed (string-append to " is not a directory")))
                                                                             ((any inside ns)
                                                                              (sum failed (string-append "Cannot " (if copy "copy " "move ")
                                                                                                         (describe-names ns)
                                                                                                         " into itself")))
                                                                             (else
                                                                           (each-file ns (lambda ((n string))
                                                                                           (if copy
                                                                                               (copy-tree (string-append dir n) (target n))
                                                                                               (fs-outcome-of (string-append dir n)
                                                                                                              (rename-file (string-append dir n) (target n))))))))))
                                                         (after-listing-op! fr b dir marks "" outcome
                                                                            (string-append (if copy "Copied " "Moved ") (describe-names ns)))))))))))))))

"+ in a listing: a directory made, and its parents if need be."
(define* dired-create-directory (subr pure () frame-action)
  (lambda ()
    (lambda ((fr (actor frame)) (f frame))
      (let* ((b (extract (selected-window f) buffer))
             (st (actor-state b))
             (dir (extract st file))
             (marks (listing-marks (extract st text))))
        (read-completing f "Create directory: " dir (sum files #u)
                         (lambda ((fr (actor frame)) (f frame) (typed string))
                           (let ((path (if (and (> (string-length typed) 0) (char=? (string-ref typed 0) #\/)) typed (string-append dir typed))))
                             (reply-with f (list (lambda ()
                                                   (after-listing-op! fr b dir marks (base-name path) (make-directories path)
                                                                      (string-append "Created " path))))))))))))

"The buffer *Buffer List* names on line `s` (line `line` of it) -- the
longest name the line has after its flags -- if there is one."
(define* buffer-named-on (subr spin (buffer-infos string int) (sumof (none unit) (found buffer-info)))
  (lambda (bs s line)
    (let ((rest (if (< (string-length s) 3) "" (substring s 3 (string-length s)))))
      (letrec ((go (subr spin (buffer-infos (sumof (none unit) (found buffer-info))) (sumof (none unit) (found buffer-info)))
                 (lambda (bs best)
                   (if (null? bs) best
                       (let ((name (extract (car bs) name)))
                         (go (cdr bs)
                             (if (and (string-prefix? (string-append name " ") rest)
                                      (tagcase best
                                        (found b (> (string-length name) (string-length (extract b name))))
                                        (none u #t)))
                                 (sum found (car bs))
                                 best)))))))
        (if (= line 0) (sum none #u) (go bs (sum none #u)))))))

"RET (and f) in *Buffer List*: the buffer on this line shown in this
window; o, in another."
(define* buffer-list-visit (subr pure (bool) frame-action)
  (lambda (other)
    (lambda ((fr (actor frame)) (f frame))
      (let ((l (point-line (actor-state (extract (selected-window f) buffer)))))
        (tagcase (buffer-named-on (extract f buffers) (extract l text) (extract l line))
          (found info (if other (show-other-window fr f (extract info actor)) (show-buffer fr f (extract info actor))))
          (none u (draw (with-echo f "No buffer on this line"))))))))

"In a list whose items start on line `first` (*Buffer List*'s 1, a
listing's 2): this line's flag (column 0) made `c` -- in *Buffer List*
D, to be killed by x, S, to be saved; in a listing * marked, D flagged to
delete; a space, neither -- then point moved `move` lines, to column
`column`; or, if `before`, moved up a line first (DEL). Not a change of
the buffer's: not modified, not undone."
(define* line-flag (subr pure (int int char int bool) command)
  (lambda (first column c move before)
    (lambda ((b buffer))
      (let* ((t (extract b text))
             (last (- (rope-line-count t) 2))         ; the last item's line (the text ends with a newline)
             (here (rope-line-of t (extract b point)))
             (line (if before (max first (- here 1)) here))
             (at (lambda ((t2 rope) (n int)) (min (rope-line-end t2 n) (+ (rope-line-start t2 n) column)))))
        (if (or (< line first) (> line last))
            (done (with-point b (at t (max first (min last line)))))
            (let* ((ls (rope-line-start t line))
                   (t2 (rope-insert (rope-delete t ls (+ ls 1)) ls (char->string c)))
                   (to (if before line (max first (min last (+ line move))))))
              (done (buffer-of b t2 (at t2 to) (extract b mark) (+ 1 (extract b revision)) (extract b modified)
                               (extract b undo) (extract b subscribers)))))))))
(define* buffer-list-flag (subr pure (char int bool) command)
  (lambda (c move before) (line-flag 1 0 c move before)))

"x in *Buffer List*: each buffer flagged S saved, each flagged D killed;
then the list made again."
(define* buffer-list-execute (subr pure () frame-action)
  (lambda ()
    (lambda ((fr (actor frame)) (f frame))
      (let* ((t (extract (actor-state (extract (selected-window f) buffer)) text))
             (flagged (lambda ((flag char))
                        (letrec ((go (subr spin (int buffer-infos) buffer-infos)
                                   (lambda (line acc)
                                     (if (>= line (rope-line-count t)) acc
                                         (let ((s (rope-substring t (rope-line-start t line) (rope-line-end t line))))
                                           (go (+ line 1)
                                               (if (and (> (string-length s) 0) (char=? (string-ref s 0) flag))
                                                   (tagcase (buffer-named-on (extract f buffers) s line)
                                                     (found info (cons info acc))
                                                     (none u acc))
                                                   acc)))))))
                          (go 1 nil))))
             (to-save (flagged #\S))
             (saves (letrec ((go (subr turn-eff (buffer-infos) cmds)
                               (lambda (bs) (if (null? bs) nil
                                                (cons (tell (extract (car bs) actor) (save-buffer-to fr (extract (car bs) actor)))
                                                      (go (cdr bs)))))))
                      (go to-save)))
             (killed (letrec ((go (subr turn-eff (frame buffer-infos) (reply frame))
                                (lambda (f bs) (if (null? bs) (draw f)
                                                   (and-then fr (kill-buffer-info fr f (car bs))
                                                             (lambda ((fr (actor frame)) (f frame)) (go f (cdr bs))))))))
                       (go f (flagged #\D))))
             (listed ((list-buffers-saving (map (lambda ((i buffer-info)) (extract i actor)) to-save)) fr (extract killed state))))
        (reply-with (extract listed state) (append saves (append (extract killed cmds) (extract listed cmds))))))))

"g in *Buffer List*: the list made again, point on the same line."
(define* buffer-list-refresh (subr pure () frame-action)
  (lambda ()
    (lambda ((fr (actor frame)) (f frame))
      (let* ((b (extract (selected-window f) buffer))
             (line (extract (point-line (actor-state b)) line))
             (r ((list-buffers) fr f)))
        (reply-with (extract r state) (append (extract r cmds) (list (tell b (in-buffer fr (goto-line (+ line 1)))))))))))

"Message for a buffer: its text replaced by `t`, read again from its file:
point kept where it can be, not modified, the old text kept for undo."
(define* reverted (subr pure (rope) (msg buffer))
  (lambda (t)
    (lambda ((b buffer))
      (let* ((b1 (with-text b t (extract b point)))
             (b2 (buffer-of b1 t (extract b1 point) (extract b1 mark) (extract b1 revision) #f
                            (all-modified (extract b1 undo)) (extract b1 subscribers))))
        (reply-with b2 (notify b2))))))

"M-x revert-buffer, g in a listing: the selected buffer's file (or
directory) read again."
(define* revert-buffer (subr pure () frame-action)
  (lambda ()
    (lambda ((fr (actor frame)) (f frame))
      (let* ((b (extract (selected-window f) buffer))
             (file (extract (actor-state b) file))
             (n (string-length file)))
        (cond ((= n 0) (draw (with-echo f "Buffer does not visit a file")))
              ((char=? (string-ref file (- n 1)) #\/)
               (reply-with f (list (lambda () (tell! b (reverted (string->rope (listing-text file))))))))
              (else
               (reply-with f (list (lambda ()
                                     (let ((got (file-text file)))
                                       (if (extract got found)
                                           (begin (tell! b (reverted (extract got text)))
                                             (tell! fr (echo (string-append "Reverted " file))))
                                           (tell! fr (echo (string-append "No file " file))))))))))))))

"The buffers visiting files (not listings) changed and not saved."
(define* unsaved-buffers (subr turn-eff (buffer-infos) buffer-infos)
  (lambda (bs)
    (cond ((null? bs) nil)
          ((let* ((file (extract (car bs) file)) (n (string-length file)))
             (and (> n 0) (not (char=? (string-ref file (- n 1)) #\/))
                  (extract (actor-state (extract (car bs) actor)) modified)))
           (cons (car bs) (unsaved-buffers (cdr bs))))
          (else (unsaved-buffers (cdr bs))))))

"C-x s: each of `todo` asked about, and saved if the answer is y; ! saves
it and the rest, q the rest not. `saved`: how many so far."
(define* save-some (subr turn-eff ((actor frame) frame buffer-infos int) (reply frame))
  (lambda (fr f todo saved)
    (let ((save (lambda ((info buffer-info)) (tell (extract info actor) (save-buffer-to fr (extract info actor))))))
      (if (null? todo)
          (draw (with-echo f (if (= saved 0) "(No files need saving)"
                                 (string-append "Saved " (int->string saved) (if (= saved 1) " file" " files")))))
          (read-string f (string-append "Save file " (extract (car todo) file) "? (y, n, !, q) ") ""
                       (lambda ((fr (actor frame)) (f frame) (answer string))
                         (cond ((string=? answer "y")
                                (let ((r (save-some fr f (cdr todo) (+ saved 1))))
                                  (reply-with (extract r state) (cons (save (car todo)) (extract r cmds)))))
                               ((string=? answer "!")
                                (let ((r (save-some fr f nil (+ saved (length todo)))))
                                  (reply-with (extract r state)
                                              (append (letrec ((go (subr turn-eff (buffer-infos) cmds)
                                                                     (lambda (bs) (if (null? bs) nil (cons (save (car bs)) (go (cdr bs)))))))
                                                        (go todo))
                                                      (extract r cmds)))))
                               ((string=? answer "q") (save-some fr f nil saved))
                               (else (save-some fr f (cdr todo) saved)))))))))

(define* save-some-buffers (subr pure () frame-action)
  (lambda ()
    (lambda ((fr (actor frame)) (f frame)) (save-some fr f (unsaved-buffers (extract f buffers)) 0))))

"Directory name `typed`, absolute, without its last `/`."
(define* typed-directory (subr spin (string string) string)
  (lambda (typed dir)
    (let* ((d (expand-file-name typed dir)) (n (string-length d)))
      (if (and (> n 1) (char=? (string-ref d (- n 1)) #\/)) (substring d 0 (- n 1)) d))))

"C-x d: a directory read, and its listing visited."
(define* dired (subr pure () frame-action)
  (lambda ()
    (lambda ((fr (actor frame)) (f frame))
      (let ((dir (selected-directory f)))
        (read-completing f "Dired (directory): " dir (sum files #u)
                         (lambda ((fr (actor frame)) (f frame) (typed string))
                           (visit-file fr f (typed-directory typed dir))))))))

"C-x C-d: a directory read, and its names (`ls -F`) shown in *Directory*,
the selected window staying selected."
(define* list-directory (subr pure () frame-action)
  (lambda ()
    (lambda ((fr (actor frame)) (f frame))
      (let ((dir (selected-directory f)))
        (read-completing f "List directory: " dir (sum files #u)
                         (lambda ((fr (actor frame)) (f frame) (typed string))
                           (let ((d (string-append (typed-directory typed dir) "/")))
                             (run-in-buffer fr f "*Directory*" "command" (list "ls" "-F" d) d
                                            (string-append "Directory " d "\n") #f))))))))

(define-command! "dired" (sum on-frame (dired)))
(define-command! "list-directory" (sum on-frame (list-directory)))
(define-key! "C-x d" "dired")
(define-key! "C-x C-d" "list-directory")
(define-command! "dired-find-file" (sum on-frame (listing-visit #f)))
(define-command! "dired-find-file-other-window" (sum on-frame (listing-visit #t)))
(define-command! "dired-up-directory" (sum on-frame (listing-up)))
(define-command! "dired-mark" (sum on-buffer (line-flag 2 listing-name-column #\* 1 #f)))
(define-command! "dired-unmark" (sum on-buffer (line-flag 2 listing-name-column #\space 1 #f)))
(define-command! "dired-unmark-backward" (sum on-buffer (line-flag 2 listing-name-column #\space -1 #t)))
(define-command! "dired-unmark-all-marks" (sum on-buffer (dired-unmark-all)))
(define-command! "dired-flag-file-deletion" (sum on-buffer (line-flag 2 listing-name-column #\D 1 #f)))
(define-command! "dired-do-flagged-delete" (sum on-frame (dired-delete #t)))
(define-command! "dired-do-delete" (sum on-frame (dired-delete #f)))
(define-command! "dired-do-rename" (sum on-frame (dired-move-or-copy #f)))
(define-command! "dired-do-copy" (sum on-frame (dired-move-or-copy #t)))
(define-command! "dired-create-directory" (sum on-frame (dired-create-directory)))
(define-command! "dired-revert" (sum on-frame (dired-revert)))
(define-command! "Buffer-menu-this-window" (sum on-frame (buffer-list-visit #f)))
(define-command! "Buffer-menu-other-window" (sum on-frame (buffer-list-visit #t)))
(define-command! "Buffer-menu-delete" (sum on-buffer (buffer-list-flag #\D 1 #f)))
(define-command! "Buffer-menu-delete-backwards" (sum on-buffer (buffer-list-flag #\D -1 #f)))
(define-command! "Buffer-menu-save" (sum on-buffer (buffer-list-flag #\S 1 #f)))
(define-command! "Buffer-menu-unmark" (sum on-buffer (buffer-list-flag #\space 1 #f)))
(define-command! "Buffer-menu-backup-unmark" (sum on-buffer (buffer-list-flag #\space -1 #t)))
(define-command! "Buffer-menu-execute" (sum on-frame (buffer-list-execute)))
(define-command! "Buffer-menu-refresh" (sum on-frame (buffer-list-refresh)))
(define-command! "revert-buffer" (sum on-frame (revert-buffer)))
(define-command! "save-some-buffers" (sum on-frame (save-some-buffers)))
(define-buffer-key! "<listing>" "RET" "dired-find-file")
(define-buffer-key! "<listing>" "g" "dired-revert")
(define-buffer-key! "<listing>" "m" "dired-mark")
(define-buffer-key! "<listing>" "u" "dired-unmark")
(define-buffer-key! "<listing>" "DEL" "dired-unmark-backward")
(define-buffer-key! "<listing>" "U" "dired-unmark-all-marks")
(define-buffer-key! "<listing>" "d" "dired-flag-file-deletion")
(define-buffer-key! "<listing>" "x" "dired-do-flagged-delete")
(define-buffer-key! "<listing>" "D" "dired-do-delete")
(define-buffer-key! "<listing>" "R" "dired-do-rename")
(define-buffer-key! "<listing>" "C" "dired-do-copy")
(define-buffer-key! "<listing>" "+" "dired-create-directory")
(define-buffer-key! "<listing>" "f" "dired-find-file")
(define-buffer-key! "<listing>" "e" "dired-find-file")
(define-buffer-key! "<listing>" "o" "dired-find-file-other-window")
(define-buffer-key! "<listing>" "^" "dired-up-directory")
(define-buffer-key! "<listing>" "n" "next-line")
(define-buffer-key! "<listing>" "SPC" "next-line")
(define-buffer-key! "<listing>" "p" "previous-line")
(define-buffer-key! "<listing>" "q" "quit-window")
(define-buffer-key! "*Buffer List*" "RET" "Buffer-menu-this-window")
(define-buffer-key! "*Buffer List*" "f" "Buffer-menu-this-window")
(define-buffer-key! "*Buffer List*" "o" "Buffer-menu-other-window")
(define-buffer-key! "*Buffer List*" "d" "Buffer-menu-delete")
(define-buffer-key! "*Buffer List*" "k" "Buffer-menu-delete")
(define-buffer-key! "*Buffer List*" "C-d" "Buffer-menu-delete-backwards")
(define-buffer-key! "*Buffer List*" "s" "Buffer-menu-save")
(define-buffer-key! "*Buffer List*" "u" "Buffer-menu-unmark")
(define-buffer-key! "*Buffer List*" "DEL" "Buffer-menu-backup-unmark")
(define-buffer-key! "*Buffer List*" "x" "Buffer-menu-execute")
(define-buffer-key! "*Buffer List*" "g" "Buffer-menu-refresh")
(define-buffer-key! "*Buffer List*" "n" "next-line")
(define-buffer-key! "*Buffer List*" "SPC" "next-line")
(define-buffer-key! "*Buffer List*" "p" "previous-line")
(define-buffer-key! "*Buffer List*" "q" "quit-window")
(define-key! "C-x s" "save-some-buffers")
