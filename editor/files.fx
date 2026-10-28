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

"The text of the line point is on in `st`, and its number."
(define* point-line (subr spin (buffer) (productof (text string) (line int)))
  (lambda (st)
    (let* ((t (extract st text)) (i (rope-line-of t (extract st point))))
      (product (text (rope-substring t (rope-line-start t i) (rope-line-end t i))) (line i)))))

"RET in a listing: the name on this line visited, relative to the
directory the first line gives."
(define* listing-visit (subr pure () frame-action)
  (lambda ()
    (lambda ((fr (actor frame)) (f frame))
      (let* ((st (actor-state (extract (selected-window f) buffer)))
             (l (point-line st))
             (s (extract l text))
             (dir (extract st file)))
        (if (or (= (extract l line) 0) (< (string-length s) 3))
            (draw (with-echo f "No file on this line"))
            (let* ((name (substring s 2 (string-length s)))
                   (n (string-length name)))
              (visit-file fr f (string-append dir (if (char=? (string-ref name (- n 1)) #\/) (substring name 0 (- n 1)) name)))))))))

"RET in *Buffer List*: the buffer named on this line shown -- the
longest name the line has after its flags."
(define* buffer-list-visit (subr pure () frame-action)
  (lambda ()
    (lambda ((fr (actor frame)) (f frame))
      (let* ((st (actor-state (extract (selected-window f) buffer)))
             (l (point-line st))
             (s (extract l text))
             (rest (if (< (string-length s) 3) "" (substring s 3 (string-length s))))
             (best (letrec ((go (subr spin (buffer-infos (sumof (none unit) (found buffer-info))) (sumof (none unit) (found buffer-info)))
                              (lambda (bs best)
                                (if (null? bs) best
                                    (let ((name (extract (car bs) name)))
                                      (go (cdr bs)
                                          (if (and (starts-with? rest (string-append name " "))
                                                   (tagcase best
                                                     (found b (> (string-length name) (string-length (extract b name))))
                                                     (none u #t)))
                                              (sum found (car bs))
                                              best)))))))
                     (go (extract f buffers) (sum none #u)))))
        (tagcase best
          (found info (if (= (extract l line) 0)
                          (draw (with-echo f "No buffer on this line"))
                          (show-buffer fr f (extract info actor))))
          (none u (draw (with-echo f "No buffer on this line"))))))))

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
(define-command! "dired-find-file" (sum on-frame (listing-visit)))
(define-command! "Buffer-menu-this-window" (sum on-frame (buffer-list-visit)))
(define-command! "revert-buffer" (sum on-frame (revert-buffer)))
(define-command! "save-some-buffers" (sum on-frame (save-some-buffers)))
(define-buffer-key! "<listing>" "RET" "dired-find-file")
(define-buffer-key! "<listing>" "g" "revert-buffer")
(define-buffer-key! "*Buffer List*" "RET" "Buffer-menu-this-window")
(define-key! "C-x s" "save-some-buffers")
