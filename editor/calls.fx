;;; calls.fx: the *xref* buffer -- places listed, a line each (`file:line:
;;; text`), RET on one visiting it -- and C-c t, the type at point.
;;;
;;; What a call can call (C-c e) and what calls a lambda (C-c r) are the
;;; CFA's (cfa.fx), which lists them here.
(module-parameters ((m-base (load-moduleof "base.fx"))
                    (m-buffer (load-moduleof "buffer.fx" m-base))
                    (m-resolve (load-moduleof "resolve.fx" m-base m-buffer))
                    (m-syntax (load-moduleof "syntax.fx" m-base m-buffer m-resolve))
                    (m-sexp (load-moduleof "sexp.fx" m-base m-buffer m-resolve m-syntax))
                    (m-index (load-moduleof "index.fx" m-base m-buffer m-resolve m-syntax m-sexp))
                    (m-view (load-moduleof "view.fx" m-base m-buffer m-resolve m-syntax m-sexp m-index))
                    (m-frame (load-moduleof "frame.fx" m-base m-buffer m-resolve m-syntax m-sexp m-index m-view))))
(hide (define kit-lists (load-module "../kit/lists.fx"))
      (import kit-lists member? map remove))
(hide (define kit-strings (load-module "../kit/strings.fx"))
      (import kit-strings string-split))

"Each visited buffer's file and text, for the analysis."
(define* buffer-texts (subr turn-eff (buffer-infos) (listof (productof (file string) (text string)) acyclic))
  (lambda (bs)
    (if (null? bs) nil
        (let ((st (actor-state (extract (car bs) actor))))
          (if (string=? (extract (car bs) file) "")
              (buffer-texts (cdr bs))
              (cons (product (file (extract (car bs) file)) (text (rope->string (extract st text))))
                    (buffer-texts (cdr bs))))))))

"A place, `file` at `start`, as an *xref* line: `file:line: text of the
line`; the text the buffers have (`texts`), else the file's."
(define* place-line (subr (maxeff (io fs-read) spin) (string int (listof (productof (file string) (text string)) acyclic) string) string)
  (lambda (file start texts what)
    (let* ((t (string->rope (letrec ((go (subr (maxeff (io fs-read) spin) ((listof (productof (file string) (text string)) acyclic)) string)
                                       (lambda (ts) (cond ((null? ts) (text-of-file file))
                                                          ((string=? (extract (car ts) file) file) (extract (car ts) text))
                                                          (else (go (cdr ts)))))))
                              (go texts))))
           (line (rope-line-of t start)))
      (string-append (base-name file) ":" (int->string (+ line 1)) ": " what "  "
                     (rope-substring t (rope-line-start t line) (min (rope-line-end t line) (+ (rope-line-start t line) 80)))
                     "\n"))))

"Message for the frame: *xref* to say `text`, and be shown."
(define* show-xref (subr pure ((actor frame) string) (msg frame))
  (lambda (fr text)
    (lambda ((f frame))
      (let ((name "*xref*"))
        (tagcase (find-buffer (extract f buffers) name)
          (found info (reply-with f (list (tell (extract info actor) (replace-text (string->rope text)))
                                          (tell fr (lambda ((f frame)) (show-buffer fr f (extract info actor)))))))
          (none u (let ((b (spawn-actor name (new-buffer name "" (string->rope text)))))
                    (reply-with f (list (lambda () (tell! fr (buffer-made fr name "" b))))))))))))

"Message for the frame: visit `file` at `pos`."
(define* visit-position (subr pure ((actor frame) string int) (msg frame))
  (lambda (fr file pos)
    (lambda ((f frame))
      (tagcase (find-file-buffer (extract f buffers) file)
        (found info (go-to-place fr f (product (buffer (extract info actor)) (point pos))))
        (none u
          (let ((bname (unique-name (extract f buffers) (base-name file))))
            (reply-with f (list (lambda ()
                                  (let* ((got (file-text file))
                                         (b (spawn-actor bname (new-buffer bname file (extract got text)))))
                                    (begin (tell! fr (buffer-made fr bname file b))
                                      (tell! b (in-buffer fr (goto-position pos))))))))))))))

"RET in *xref*: visit the place on the line point is on."
(define* xref-visit (subr pure () frame-action)
  (lambda ()
    (lambda ((fr (actor frame)) (f frame))
      (let* ((st (actor-state (extract (selected-window f) buffer)))
             (t (extract st text))
             (n (rope-line-of t (extract st point)))
             (line (rope-substring t (rope-line-start t n) (rope-line-end t n)))
             (c1 (string-search line ":" 0))
             (c2 (if (< c1 0) -1 (string-search line ":" (+ c1 1)))))
        (if (< c2 0)
            (draw (with-echo f "No place on this line"))
            (let* ((header (rope-substring t 0 (rope-line-end t 0)))
                   ;; Names relative to the directory the first line gives.
                   (dir (if (and (> (string-length header) 3) (string=? (substring header 0 3) "In "))
                            (substring header 3 (string-length header))
                            ""))
                   (file (string-append dir (substring line 0 c1)))
                   (lineno (letrec ((digits (->* (int int) int)
                                      (lambda (i acc) (if (and (< i c2) (char-numeric? (string-ref line i)))
                                                          (digits (+ i 1) (+ (* 10 acc) (- (char->integer (string-ref line i)) 48)))
                                                          acc))))
                             (digits (+ c1 1) 0))))
              (reply-with f (list (lambda ()
                                    (let* ((got (file-text file))
                                           (pos (rope-line-start (extract got text) (max 0 (- lineno 1)))))
                                      (tell! fr (visit-position fr file pos))))))))))))

(define-command! "xref-visit" (sum on-frame (xref-visit)))
(define-buffer-key! "*xref*" "RET" "xref-visit")
(define-buffer-key! "*xref*" "n" "next-line")
(define-buffer-key! "*xref*" "p" "previous-line")
(define-buffer-key! "*xref*" "q" "quit-window")

;;; ------------------------------------------------------------ the type at point (C-c t)

"The words of `s`: what is between its spaces, none empty."
(define* words (subr spin (string) strings)
  (lambda (s) (remove (lambda ((w string)) (string=? w "")) (string-split s #\space))))

"The files of the program `file` is part of, in order: those its
directory's `program` file lists (one a line), if it has one, and `file`
among them; else `file` alone."
(define* program-files-of (subr (maxeff (io fs-read) spin) (string) strings)
  (lambda (file)
    (let* ((dir (directory-of file))
           (listing (text-of-file (string-append dir "program")))
           (names (map (lambda ((l string)) (string-append dir l))
                       (remove (lambda ((l string)) (string=? l "")) (string-split listing #\newline)))))
      (if (member? file names string=?) names (list file)))))

"Message for a buffer: `a`..`e` marked, in face `face`, alone."
(define* mark-span (subr pure (int int face) command)
  (lambda (a e fc) (lambda ((b buffer)) (done (with-marks b (list (product (start a) (end e) (face fc))))))))

"C-c t: the type the checker gives the expression at point, shown and
said; or why the program does not check."
(define* type-at-point (subr pure () frame-action)
  (lambda ()
    (lambda ((fr (actor frame)) (f frame))
      (let* ((b (extract (selected-window f) buffer))
             (st (actor-state b))
             (file (extract st file))
             (p (extract st point))
             (texts (buffer-texts (extract f buffers))))
        (if (not (fx26-file? file))
            (draw (with-echo f "Not an FX-26 file"))
            (reply-with f
                        (list (lambda ()
                                (let* ((files (program-files-of file))
                                       (text-for (lambda ((name string))
                                                   (letrec ((go (->* ((listof (productof (file string) (text string)) acyclic)) string)
                                                              (lambda (ts) (cond ((null? ts) (text-of-file name))
                                                                                 ((string=? (extract (car ts) file) name) (extract (car ts) text))
                                                                                 (else (go (cdr ts)))))))
                                                     (go texts))))
                                       ;; The program's text, each file's after a newline, and where this file starts in it.
                                       (joined (letrec ((go (->* (strings int strings int)
                                                                 (productof (pieces strings) (offset int)))
                                                          (lambda (fs at acc offset)
                                                            (if (null? fs)
                                                                (product (pieces (reverse acc)) (offset offset))
                                                                (let ((t (string-append (text-for (car fs)) "\n")))
                                                                  (go (cdr fs) (+ at (string-length t)) (cons t acc)
                                                                      (if (string=? (car fs) file) at offset)))))))
                                                 (go files 0 nil 0)))
                                       (offset (extract joined offset))
                                       (answer (type-at (apply string-append (extract joined pieces)) (+ offset p)))
                                       (sp1 (string-search answer " " 0))
                                       (sp2 (string-search answer " " (+ sp1 1)))
                                       (sp3 (string-search answer " " (+ sp2 1)))
                                       (num (lambda ((from int) (to int))
                                              (letrec ((go (subr spin (int int) int)
                                                         (lambda (i acc) (if (>= i to) acc
                                                                             (go (+ i 1) (+ (* 10 acc) (- (char->integer (string-ref answer i)) 48)))))))
                                                (go from 0)))))
                                  (if (string=? (substring answer 0 (max 0 sp1)) "error")
                                      (let ((a (- (num (+ sp1 1) sp2) offset)) (e (- (num (+ sp2 1) sp3) offset))
                                            (why (substring answer (+ sp3 1) (string-length answer))))
                                        (if (and (>= a 0) (<= e (string-length (text-for file))))
                                            (begin (tell! b (in-buffer fr (mark-span a e 'error)))
                                              (tell! fr (echo (string-append "Does not check: " why))))
                                            (tell! fr (echo (string-append "The program does not check (another file): " why)))))
                                      (let ((a (- (num 0 sp1) offset)) (e (- (num (+ sp1 1) sp2) offset))
                                            (ty (substring answer (+ sp2 1) (string-length answer))))
                                        (begin (tell! b (in-buffer fr (mark-span a e 'use)))
                                          (tell! fr (echo ty))))))))))))))

(define-command! "type-at-point" (sum on-frame (type-at-point)))
(define-key! "C-c t" "type-at-point")
