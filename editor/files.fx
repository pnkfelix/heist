;;; files.fx: working across several files and buffers.
;;;
;;;   RET in a listing     the file or directory on this line, visited
;;;                        (C-x C-f on a directory makes a listing)
;;;   g in a listing       the listing read again
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
      (import kit-lists map))

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
        (if (or (= (extract l line) 0) (< (string-length s) 3))
            (draw (with-echo f "No file on this line"))
            (let* ((name (substring s 2 (string-length s)))
                   (n (string-length name))
                   (file (string-append dir (if (char=? (string-ref name (- n 1)) #\/) (substring name 0 (- n 1)) name))))
              (if other
                  (and-then fr ((other-window-or-split) fr f) (lambda ((fr (actor frame)) (f frame)) (visit-file fr f file)))
                  (visit-file fr f file))))))))

"^ in a listing: the directory above listed."
(define* listing-up (subr pure () frame-action)
  (lambda ()
    (lambda ((fr (actor frame)) (f frame))
      (let ((dir (extract (actor-state (extract (selected-window f) buffer)) file)))
        (if (string=? dir "/")
            (draw (with-echo f "No directory above /"))
            (visit-file fr f (simplify-directory (string-append dir "../"))))))))

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

"In *Buffer List*: this line's flag (column 0) made `c` -- D, to be
killed by x; S, to be saved; a space, neither -- then point moved `move`
lines; or, `move` -1 and `before`, moved up first (DEL). Not a change of
the buffer's: not modified, not undone."
(define* buffer-list-flag (subr pure (char int bool) command)
  (lambda (c move before)
    (lambda ((b buffer))
      (let* ((t (extract b text))
             (last (- (rope-line-count t) 2))         ; the last buffer's line (the text ends with a newline)
             (here (rope-line-of t (extract b point)))
             (line (if before (max 1 (- here 1)) here)))
        (if (or (< line 1) (> line last))
            (done (with-point b (rope-line-start t (max 1 (min last line)))))
            (let* ((ls (rope-line-start t line))
                   (t2 (rope-insert (rope-delete t ls (+ ls 1)) ls (char->string c)))
                   (to (if before line (max 1 (min last (+ line move))))))
              (done (buffer-of b t2 (rope-line-start t2 to) (extract b mark) (+ 1 (extract b revision)) (extract b modified)
                               (extract b undo) (extract b subscribers)))))))))

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
(define-buffer-key! "<listing>" "g" "revert-buffer")
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
