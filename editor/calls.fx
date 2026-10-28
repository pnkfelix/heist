;;; calls.fx: what a call can call, and what calls a lambda, by the flow
;;; analysis (flow.fx) of the program a file is part of: the `.fx` files of
;;; its directory, those visited as their buffers have them.
;;;
;;;   C-c e  the lambdas the call at point can call: the one, or a list
;;;   C-c r  the calls that can call the lambda point is in, listed
;;;
;;; A list is the buffer *xref*, a line a place (`file:line: text`); RET on
;;; one visits it. The analysis runs on demand, in a command after the
;;; frame's turn: on the editor's own twelve files it takes about 20 ms,
;;; after reading them.
(module-parameters ((m-base (load-moduleof "base.fx"))
                    (m-buffer (load-moduleof "buffer.fx" m-base))
                    (m-resolve (load-moduleof "resolve.fx" m-base m-buffer))
                    (m-syntax (load-moduleof "syntax.fx" m-base m-buffer m-resolve))
                    (m-sexp (load-moduleof "sexp.fx" m-base m-buffer m-resolve m-syntax))
                    (m-flow (load-moduleof "flow.fx" m-base m-buffer m-resolve m-syntax m-sexp))
                    (m-index (load-moduleof "index.fx" m-base m-buffer m-resolve m-syntax m-sexp m-flow))
                    (m-view (load-moduleof "view.fx" m-base m-buffer m-resolve m-syntax m-sexp m-flow m-index))
                    (m-frame (load-moduleof "frame.fx" m-base m-buffer m-resolve m-syntax m-sexp m-flow m-index m-view))))

"The files of the program `file` is part of, as program-files: read with
Fixpt's reader, from the buffers that visit them if any (`texts`: file
and text), else from the files."
(define* program-of (subr (maxeff cmd-eff spin (alloc @pf)) (string (listof (productof (file string) (text string)) acyclic))
                          (productof (files program-files) (texts (listof (productof (file string) (text string)) acyclic))))
  (lambda (file texts)
    (let ((dir (directory-of file)))
      (tagcase (the (sumof (names (listof string @pf)) (failed io-error)) (list-dir (if (string=? dir "") "." dir)))
        (names ns
          (letrec ((text-for (->* (string) string)
                     (lambda (f) (letrec ((go (->* ((listof (productof (file string) (text string)) acyclic)) string)
                                            (lambda (ts) (cond ((null? ts) (text-of-file f))
                                                               ((string=? (extract (car ts) file) f) (extract (car ts) text))
                                                               (else (go (cdr ts)))))))
                                   (go texts))))
                   (go (->* ((listof string @pf))
                            (productof (files program-files) (texts (listof (productof (file string) (text string)) acyclic))))
                     (lambda (l)
                       (cond ((null? l) (product (files nil) (texts nil)))
                             ((fx26-file? (car l))
                              (let* ((f (string-append dir (car l)))
                                     (s (text-for f))
                                     (rest (go (cdr l))))
                                (product (files (cons (product (file f) (forms (eager-state-syntax
                                                                                (eager-feed (eager-feed-string (eager-start-fx26) s) #\newline))))
                                                      (extract rest files)))
                                         (texts (cons (product (file f) (text s)) (extract rest texts))))))
                             (else (go (cdr l)))))))
            (go ns)))
        (else y (product (files nil) (texts nil)))))))

"Each visited buffer's file and text, for the analysis."
(define* buffer-texts (subr turn-eff (buffer-infos) (listof (productof (file string) (text string)) acyclic))
  (lambda (bs)
    (if (null? bs) nil
        (let ((st (actor-state (extract (car bs) actor))))
          (if (string=? (extract (car bs) file) "")
              (buffer-texts (cdr bs))
              (cons (product (file (extract (car bs) file)) (text (rope->string (extract st text))))
                    (buffer-texts (cdr bs))))))))

"A place as an *xref* line: `file:line: text of the line`."
(define* place-line (subr spin (fl-span (listof (productof (file string) (text string)) acyclic) string) string)
  (lambda (sp texts what)
    (let* ((t (string->rope (letrec ((go (->* ((listof (productof (file string) (text string)) acyclic)) string)
                                       (lambda (ts) (cond ((null? ts) "")
                                                          ((string=? (extract (car ts) file) (extract sp file)) (extract (car ts) text))
                                                          (else (go (cdr ts)))))))
                              (go texts))))
           (line (rope-line-of t (extract sp start))))
      (string-append (base-name (extract sp file)) ":" (int->string (+ line 1)) ": " what "  "
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

(define* span-contains? (subr pure (fl-span string int) bool)
  (lambda (sp file p) (and (string=? (extract sp file) file) (<= (extract sp start) p) (<= p (extract sp end)))))
(define* span-size (subr pure (fl-span) int) (lambda (sp) (- (extract sp end) (extract sp start))))

"A frame command running the flow analysis of the selected buffer's
program, then `answer` of it, the buffer's file and point, and the
texts: a message for the frame."
(define* with-flow (subr pure ((subr cmd-eff ((actor frame) string int (listof (productof (file string) (text string)) acyclic)) unit))
                         frame-action)
  (lambda (answer)
    (lambda ((fr (actor frame)) (f frame))
      (let* ((b (extract (selected-window f) buffer))
             (st (actor-state b))
             (file (extract st file))
             (p (extract st point))
             (texts (buffer-texts (extract f buffers))))
        (if (not (fx26-file? file))
            (draw (with-echo f "Not an FX-26 file"))
            (reply-with f (list (lambda ()
                                  (let ((prog (program-of file texts)))
                                    (begin (analyze-flow (extract prog files))
                                      (answer fr file p (extract prog texts))))))))))))

"C-c e: the lambdas the call at point can call."
(define* callees-at-point (subr pure () frame-action)
  (lambda ()
    (with-flow
     (lambda ((fr (actor frame)) (file string) (p int) (texts (listof (productof (file string) (text string)) acyclic)))
       ;; The innermost call whose operator is at point; else whose span is.
       (let* ((calls (flow-calls))
              (best (letrec ((go (->* ((listof call-result acyclic) (listof call-result acyclic)) (listof call-result acyclic))
                               (lambda (cs best)
                                 (cond ((null? cs) best)
                                       ((and (span-contains? (extract (car cs) span) file p)
                                             (or (null? best) (< (span-size (extract (car cs) span)) (span-size (extract (car best) span)))))
                                        (go (cdr cs) (list (car cs))))
                                       (else (go (cdr cs) best))))))
                      (go calls nil))))
         (if (null? best)
             (tell! fr (echo "No call at point"))
             (let* ((c (car best)) (ls (extract c callees)))
               (cond ((and (= (length ls) 1) (not (extract c unknown)))
                      (tell! fr (visit-position fr (extract (extract (car ls) span) file) (extract (extract (car ls) span) start))))
                     ((and (null? ls) (not (extract c unknown)))
                      (tell! fr (echo "This call reaches no lambda of the program (a standard procedure?)")))
                     (else
                      (tell! fr (show-xref fr
                                           (string-append
                                            "In " (directory-of file) "\n"
                                            "Lambdas the call can call"
                                            (if (extract c unknown) " (and code not known)" "") ":\n"
                                            (letrec ((lines (->* ((listof callee acyclic)) string)
                                                       (lambda (l) (if (null? l) ""
                                                                       (string-append (place-line (extract (car l) span) texts (extract (car l) name))
                                                                                      (lines (cdr l)))))))
                                              (lines ls))))))))))))))

"C-c r: the calls that can call the lambda point is in."
(define* callers-at-point (subr pure () frame-action)
  (lambda ()
    (with-flow
     (lambda ((fr (actor frame)) (file string) (p int) (texts (listof (productof (file string) (text string)) acyclic)))
       (let* ((lambdas (get fl-lambda-array))
              (best (letrec ((go (->* (int int) int)
                               (lambda (i best)
                                 (if (>= i (array-length lambdas)) best
                                     (let ((sp (extract (array-ref lambdas i) span)))
                                       (go (+ i 1)
                                           (if (and (span-contains? sp file p)
                                                    (or (< best 0) (< (span-size sp) (span-size (extract (array-ref lambdas best) span)))))
                                               i best)))))))
                      (go 0 -1))))
         (if (< best 0)
             (tell! fr (echo "Not in a lambda"))
             (let* ((target (extract (array-ref lambdas best) span))
                    (callers (letrec ((go (->* ((listof call-result acyclic)) (listof call-result acyclic))
                                        (lambda (cs)
                                          (cond ((null? cs) nil)
                                                ((letrec ((has (->* ((listof callee acyclic)) bool)
                                                            (lambda (l) (and (pair? l)
                                                                             (or (and (string=? (extract (extract (car l) span) file) (extract target file))
                                                                                      (= (extract (extract (car l) span) start) (extract target start)))
                                                                                 (has (cdr l)))))))
                                                   (has (extract (car cs) callees)))
                                                 (cons (car cs) (go (cdr cs))))
                                                (else (go (cdr cs)))))))
                               (go (flow-calls)))))
               (tell! fr (show-xref fr
                                    (string-append
                                     "In " (directory-of file) "\n"
                                     "Calls that can call " (extract (array-ref lambdas best) name)
                                     (if (array-ref (get fl-escaped) best) " (it escapes: code not known may too)" "")
                                     ":\n"
                                     (letrec ((lines (->* ((listof call-result acyclic)) string)
                                                (lambda (l) (if (null? l) ""
                                                                (string-append (place-line (extract (car l) span) texts "")
                                                                               (lines (cdr l)))))))
                                       (lines callers))))))))))))

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

(define-command! "flow-callees" (sum on-frame (callees-at-point)))
(define-command! "flow-callers" (sum on-frame (callers-at-point)))
(define-command! "xref-visit" (sum on-frame (xref-visit)))
(define-key! "C-c e" "flow-callees")
(define-key! "C-c r" "flow-callers")
(define-buffer-key! "*xref*" "RET" "xref-visit")

;;; ------------------------------------------------------------ the type at point (C-c t)

(define* reverse-strings (subr pure (strings) strings)
  (lambda (l) (letrec ((go (subr pure (strings strings) strings) (lambda (l acc) (if (null? l) acc (go (cdr l) (cons (car l) acc))))))
                (go l nil))))

"The files of the program `file` is part of, in order: those its
directory's `program` file lists (one a line), if it has one, and `file`
among them; else `file` alone."
(define* program-files-of (subr (maxeff (io fs-read) spin) (string) strings)
  (lambda (file)
    (let* ((dir (directory-of file))
           (listing (text-of-file (string-append dir "program")))
           (names (letrec ((lines (subr spin (int int strings) strings)
                             ;; The lines of `listing` from `i`, the current one from `start`.
                             (lambda (i start acc)
                               (cond ((>= i (string-length listing))
                                      (reverse-strings (if (> i start) (cons (string-append dir (substring listing start i)) acc) acc)))
                                     ((char=? (string-ref listing i) #\newline)
                                      (lines (+ i 1) (+ i 1) (if (> i start) (cons (string-append dir (substring listing start i)) acc) acc)))
                                     (else (lines (+ i 1) start acc))))))
                    (lines 0 0 nil))))
      (if (member? file names) names (list file)))))

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
                                                                (product (pieces (reverse-strings acc)) (offset offset))
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
