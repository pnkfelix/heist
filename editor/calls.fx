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
(define* place-line (subr spin (span (listof (productof (file string) (text string)) acyclic) string) string)
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

(define* span-contains? (subr pure (span string int) bool)
  (lambda (sp file p) (and (string=? (extract sp file) file) (<= (extract sp start) p) (<= p (extract sp end)))))
(define* span-size (subr pure (span) int) (lambda (sp) (- (extract sp end) (extract sp start))))

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
