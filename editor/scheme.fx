;;; scheme.fx: s7st (../s7st/: R7RS Scheme, interpreted in FX-26) in the
;;; editor -- a REPL, and Scheme buffers' forms run in it.
;;;
;;;   M-x run-s7st, s7st  the REPL, in *s7st*: RET runs what is typed after
;;;                       the prompt, once its data are whole (else a new
;;;                       line); each value written after its output
;;;   C-c C-c in *s7st*   what runs, interrupted
;;;   M-p, M-n in *s7st*  the input before (after) in the history
;;;   C-x C-e             the sexp before point run, its value in the echo
;;;                       area (in a Scheme buffer: .scm, .sld, .ss, .sps)
;;;   C-M-x               the top-level form around point, run
;;;   C-c C-b, C-c C-l    the buffer's forms run, as `load` runs a file's
;;;   C-c C-r             the region's forms run
;;;   C-c C-z             to *s7st*
;;;
;;; The interpreter's state is at @sc, which only commands may write; so
;;; what it runs, it runs in commands, `s7-slice` steps at a time, from
;;; the main loop (`s7-poll!`), keys read between slices. What it writes
;;; goes to *s7st*, if there is one.

(define s7-prompt string "s7st> ")
(define s7-slice int 20000)
"*s7st*, once made."
(define s7-repl (ref (listof (actor buffer) acyclic) @ed) (new nil))
"Where in *s7st* output goes: before the prompt, if one is shown; and
where what is typed and not yet run starts, after the prompt."
(define s7-output-at (ref int @ed) (new 0))
(define s7-input-start (ref int @ed) (new 0))
"Who is told how what runs ends: the REPL (which writes each value), the
echo area (of a frame), or nobody."
(define-type s7-client (sumof (none unit) (repl unit) (echo (actor frame))))
(define s7-client-now (ref s7-client @ed) (new (the s7-client (sum none #u))))
"What was written while the echo area's client ran, for it to show."
(define s7-echo-output (ref string @ed) (new ""))
(define s7-started (ref bool @ed) (new #f))
"The directory *s7st*'s relative file names are relative to: that of the
buffer selected when it was made."
(define s7-repl-directory (ref string @ed) (new ""))
"Inputs run in the REPL, the last first; and which M-p last showed (-1: none)."
(define s7-history (ref strings @ed) (new nil))
(define s7-history-at (ref int @ed) (new -1))

"The interpreter made ready, the first time. \"\", or what went wrong."
(define* s7-ensure-started! (subr cmd-eff () string)
  (lambda ()
    (if (get s7-started) ""
        (begin (set s7-started #t) (s7-init!)))))

"Message for *s7st*: `s` put where output goes (before the prompt, and
anything typed after it); if `prompted`, `s` ends with a new prompt, which
output then goes before. Point stays after it if it was there or later, as
comint keeps it. Output is no change of the user's."
(define* s7-repl-insert (subr pure (string bool) (msg buffer))
  (lambda (s prompted)
    (lambda ((b buffer))
      (let* ((t (extract b text))
             (at (min (get s7-output-at) (rope-length t)))
             (n (string-length s))
             (p (extract b point))
             (input (get s7-input-start))
             (b1 (with-text b (rope-insert t at s) (if (>= p at) (+ p n) p)))
             (b2 (buffer-of b1 (extract b1 text) (extract b1 point) (extract b1 mark) (extract b1 revision)
                            (extract b modified) (extract b undo) (extract b1 subscribers))))
        (reply-with b2 (cons (lambda ()
                               (begin
                                 (set s7-output-at (if prompted (- (+ at n) (string-length s7-prompt)) (+ at n)))
                                 (set s7-input-start (if (or prompted (>= input at)) (max (+ at n) (+ input n)) input))))
                             (notify b2)))))))
(define* s7-repl-say! (subr cmd-eff (string bool) unit)
  (lambda (s prompted)
    (let ((r (get s7-repl)))
      (if (or (null? r) (string=? s "")) #u (tell! (car r) (s7-repl-insert s prompted))))))

"What runs has ended: `value` (written, \"\" for none) or `error`."
(define* s7-finished! (subr cmd-eff (string string) unit)
  (lambda (value error)
    (let ((client (get s7-client-now)))
      (begin
        (set s7-client-now (sum none #u))
        (tagcase client
          (repl u (s7-repl-say! (string-append (s7-fresh-line) (if (string=? error "") "" (string-append "Error: " error "\n")) s7-prompt) #t))
          (echo fr (let ((out (one-line (get s7-echo-output))))
                     (begin
                       (s7-repl-say! (string-append (s7-fresh-line) (if (string=? error "") "" (string-append "Error: " error "\n"))) #f)
                       (tell! fr (echo (string-append (if (string=? out "") "" (string-append out " "))
                                                      (if (string=? error "") (string-append "=> " value) (string-append "Error: " error))))))))
          (none u #u))))))

"A slice of what runs run, its output written, and its end told; whether
it still runs."
(define* s7-poll! (subr cmd-eff () bool)
  (lambda ()
    (if (not (s7-busy?)) #f
        (let* ((status (s7-continue! s7-slice))
               (out (s7-take-output!)))
          (begin
            (if (string=? out "") #u
                (begin (s7-repl-say! out #f)
                  (tagcase (get s7-client-now)
                    (echo fr (set s7-echo-output (string-append (get s7-echo-output) out)))
                    (else y #u))))
            (tagcase status
              (running u #t)
              (done v (begin (s7-finished! (if (s7-shown? v) (s7-show v #t) "") "") #f))
              (failed m (begin (s7-finished! "" m) #f))))))))

"Text `text` (of `file`, \"\" if none) run for `client`, relative file
names relative to `dir`; `echo`: each value written, as the REPL writes
them. What to say if it cannot be: it is busy, or the text does not read."
(define* s7-start-for! (subr cmd-eff (string string string bool s7-client) string)
  (lambda (text file dir echo client)
    (let ((why (s7-ensure-started!)))
      (cond ((not (string=? why "")) (string-append "s7st did not start: " why))
            ((s7-busy?) "s7st is busy: C-c C-c in *s7st* interrupts it")
            (else (tagcase (begin (set s7-directory dir) (s7-start! text file echo))
                    (bad m (string-append "Error: " m))
                    (none u (begin (set s7-client-now client) (set s7-echo-output "") ""))))))))

;;; ------------------------------------------------------------ the REPL

(define s7-banner string
  ";; s7st: R7RS Scheme, interpreted in FX-26. RET runs what is typed once it is whole;\n;; C-c C-c interrupts; M-p and M-n go through the history. (docs/s7st.md)\n")

"A buffer's next state, with nothing else to do."
(define* done-reply (subr turn-eff (buffer) (reply buffer))
  (lambda (b) (reply-with b (notify b))))

"M-x run-s7st: *s7st* shown in the selected window, made if need be."
(define* run-s7st (subr pure () frame-action)
  (lambda ()
    (lambda ((fr (actor frame)) (f frame))
      (tagcase (find-buffer (extract f buffers) "*s7st*")
        (found info (show-buffer fr f (extract info actor)))
        (none u
          (reply-with f (list (let ((dir (selected-directory f))) (lambda () (set s7-repl-directory dir)))
                              (lambda ()
                                (let* ((text (string-append s7-banner s7-prompt))
                                       (n (string-length text))
                                       (b (spawn-actor "*s7st*" (new-buffer "*s7st*" "" (string->rope text)))))
                                  (begin
                                    (set s7-repl (list b))
                                    (set s7-output-at (string-length s7-banner))
                                    (set s7-input-start n)
                                    (tell! b (lambda ((st buffer)) (done-reply (with-point st n))))
                                    (tell! fr (buffer-made fr "*s7st*" "" b))
                                    (let ((why (s7-ensure-started!)))
                                      (if (string=? why "") #u (s7-repl-say! (string-append ";; s7st did not start: " why "\n") #f)))))))))))))
"Input `input`, ending at `end`, run if it is whole."
(define* s7-submit! (subr cmd-eff (string int) unit)
  (lambda (input end)
    (let ((why (s7-ensure-started!)))
      (cond ((not (string=? why "")) (s7-repl-say! (string-append ";; s7st did not start: " why "\n") #f))
            ((s7-busy?) #u)
            (else
             (tagcase (s7-input-state input)
               (incomplete u #u)
               (else y
                 (begin
                   (set s7-input-start end)
                   (set s7-output-at end)
                   (set s7-history-at -1)
                   (if (string=? (one-line input) "") #u (set s7-history (cons input (get s7-history))))
                   (let ((said (s7-start-for! input "" (get s7-repl-directory) #t (sum repl #u))))
                     (if (string=? said "") #u (s7-repl-say! (string-append said "\n" s7-prompt) #t)))))))))))

"RET in *s7st*: a new line; and what is typed after the prompt run, if
its data are whole."
(define* s7-send-input (subr pure () command)
  (lambda ()
    (lambda ((b buffer))
      (let* ((t (extract b text))
             (n (rope-length t))
             (from (min (get s7-input-start) n))
             (input (rope-substring t from n)))
        (product (buffer (with-text b (rope-insert t n "\n") (+ n 1)))
                 (cmds (list (lambda () (s7-submit! input (+ n 1)))))
                 (message ""))))))
(define* s7-nth-string (subr spin (strings int) string)
  (lambda (l i) (cond ((null? l) "") ((= i 0) (car l)) (else (s7-nth-string (cdr l) (- i 1))))))

"M-p (`dir` 1), M-n (-1) in *s7st*: what is typed replaced by the input
before (after) the one shown last."
(define* s7-history-step (subr pure (int) command)
  (lambda (dir)
    (lambda ((b buffer))
      (let* ((h (get s7-history))
             (i (+ (get s7-history-at) dir))
             (t (extract b text))
             (n (rope-length t))
             (from (min (get s7-input-start) n)))
        (cond ((null? h) (say b "No history"))
              ((< i -1) (say b "End of history"))
              ((>= i (list-length h)) (say b "Beginning of history"))
              (else
               (let ((s (if (< i 0) "" (s7-nth-string h i))))
                 (product (buffer (with-text b (rope-insert (rope-delete t from n) from s) (+ from (string-length s))))
                          (cmds (list (lambda () (set s7-history-at i))))
                          (message "")))))))))
"C-c C-c in *s7st*: what runs, stopped."
(define* s7-interrupt (subr pure () frame-action)
  (lambda ()
    (lambda ((fr (actor frame)) (f frame))
      (let ((r (draw (with-echo f "Interrupted"))))
        (reply-with (extract r state)
                    (cons (lambda ()
                            (if (s7-busy?)
                                (begin
                                  (s7-interrupt!)
                                  (s7-repl-say! (s7-take-output!) #f)
                                  (tagcase (get s7-client-now)
                                    (repl u (s7-repl-say! (string-append (s7-fresh-line) ";; interrupted\n" s7-prompt) #t))
                                    (else y #u))
                                  (set s7-client-now (sum none #u)))
                                #u))
                          (extract r cmds)))))))

"Eldoc in a Scheme buffer (eldoc.fx): what s7st knows of the name at
point, else of the operator of the call around it."
(define* s7-eldoc (subr pure ((actor frame) string string) cmd)
  (lambda (fr here op)
    (lambda ()
      (if (not (string=? (s7-ensure-started!) "")) #u
          (let ((s (s7-describe here)))
            (tell! fr (eldoc-show (if (string=? s "") (s7-describe op) s))))))))
(set scheme-eldoc (list s7-eldoc))

;;; ------------------------------------------------------------ Scheme buffers

"Whether a buffer named `name` holds Scheme: .scm, .sld, .ss or .sps."
(define* scheme-file? (subr spin (string) bool)
  (lambda (name)
    (let ((ends (lambda ((x string))
                  (let ((n (string-length name)) (k (string-length x)))
                    (and (> n k) (string=? (substring name (- n k) n) x))))))
      (or (ends ".scm") (ends ".sld") (ends ".ss") (ends ".sps")))))

"A frame action running text the selected buffer gives (`pick`: its text
and point and mark to the text and the file it is said to be of, or the
reason there is none)."
(define* s7-run-from-buffer
  (subr pure ((subr (maxeff spin (read @globals)) (rope int int string) (sumof (text (productof (text string) (file string))) (none string))))
        frame-action)
  (lambda (pick)
    (lambda ((fr (actor frame)) (f frame))
      (let* ((st (actor-state (extract (selected-window f) buffer))))
        (tagcase (pick (extract st text) (extract st point) (extract st mark) (extract st file))
          (none why (draw (with-echo f why)))
          (text x (reply-with f (list (lambda ()
                                        (let ((said (s7-start-for! (extract x text) (extract x file) (directory-of (extract st file)) #f (sum echo fr))))
                                          (if (string=? said "") #u (tell! fr (echo said)))))))))))))

"The start of the top-level form around point `p`: the last line at or
before its line that begins with `(`; -1 if none."
(define* s7-defun-start (subr spin (rope int) int)
  (lambda (t p)
    (letrec ((go (subr spin (int) int)
               (lambda (line)
                 (if (< line 0) -1
                     (let ((s (rope-line-start t line)))
                       (if (and (< s (rope-length t)) (char=? (rope-ref t s) #\())
                           s
                           (go (- line 1))))))))
      (go (rope-line-of t (min p (rope-length t)))))))

(define-command! "run-s7st" (sum on-frame (run-s7st)))
(define-command! "s7st" (sum on-frame (run-s7st)))
(define-command! "run-scheme" (sum on-frame (run-s7st)))
(define-command! "s7st-send-input" (sum on-buffer (s7-send-input)))
(define-command! "s7st-interrupt" (sum on-frame (s7-interrupt)))
(define-command! "s7st-previous-input" (sum on-buffer (s7-history-step 1)))
(define-command! "s7st-next-input" (sum on-buffer (s7-history-step -1)))
(define-command! "s7st-eval-last-sexp"
  (sum on-frame (s7-run-from-buffer (lambda ((t rope) (p int) (m int) (file string))
                                      (let ((a (backward-sexp t p)))
                                        (if (< a 0) (sum none "No sexp before point")
                                            (sum text (product (text (rope-substring t a p)) (file "")))))))))
(define-command! "s7st-eval-defun"
  (sum on-frame (s7-run-from-buffer (lambda ((t rope) (p int) (m int) (file string))
                                      (let ((a (s7-defun-start t p)))
                                        (if (< a 0) (sum none "No top-level form here")
                                            (let ((e (forward-sexp t a)))
                                              (if (< e 0) (sum none "The form here is not closed")
                                                  (sum text (product (text (rope-substring t a e)) (file "")))))))))))
(define-command! "s7st-eval-buffer"
  (sum on-frame (s7-run-from-buffer (lambda ((t rope) (p int) (m int) (file string))
                                      (sum text (product (text (rope->string t)) (file file)))))))
(define-command! "s7st-eval-region"
  (sum on-frame (s7-run-from-buffer (lambda ((t rope) (p int) (m int) (file string))
                                      (if (< m 0) (sum none "The mark is not set")
                                          (sum text (product (text (rope-substring t (min p m) (max p m))) (file ""))))))))
(define-buffer-key! "*s7st*" "RET" "s7st-send-input")
(define-buffer-key! "*s7st*" "C-c C-c" "s7st-interrupt")
(define-buffer-key! "*s7st*" "M-p" "s7st-previous-input")
(define-buffer-key! "*s7st*" "M-n" "s7st-next-input")
(define-buffer-key! "*s7st*" "C-x C-e" "s7st-eval-last-sexp")
(define-buffer-key! "<scheme>" "C-x C-e" "s7st-eval-last-sexp")
(define-buffer-key! "<scheme>" "C-M-x" "s7st-eval-defun")
(define-buffer-key! "<scheme>" "C-c C-b" "s7st-eval-buffer")
(define-buffer-key! "<scheme>" "C-c C-l" "s7st-eval-buffer")
(define-buffer-key! "<scheme>" "C-c C-r" "s7st-eval-region")
(define-buffer-key! "<scheme>" "C-c C-z" "run-s7st")

(define-doc! "run-s7st" "Show *s7st*, s7st's REPL, making it if need be.\nIts RET runs what is typed after the prompt once its data are whole; C-c C-c interrupts what runs.")
(define-doc! "s7st" "Show *s7st*, s7st's REPL (run-s7st).")
(define-doc! "run-scheme" "Show *s7st*, s7st's REPL (run-s7st).")
(define-doc! "s7st-send-input" "In *s7st*: a new line, and what is typed after the prompt run, if its data are whole.")
(define-doc! "s7st-interrupt" "Stop what s7st runs.")
(define-doc! "s7st-previous-input" "In *s7st*: what is typed replaced by the input before, in the history.")
(define-doc! "s7st-next-input" "In *s7st*: what is typed replaced by the input after, in the history.")
(define-doc! "s7st-eval-last-sexp" "Run the sexp before point in s7st; its value in the echo area, its output in *s7st*.")
(define-doc! "s7st-eval-defun" "Run the top-level form around point in s7st; its value in the echo area.")
(define-doc! "s7st-eval-buffer" "Run the buffer's forms in s7st, as `load` runs a file's.")
(define-doc! "s7st-eval-region" "Run the region's forms in s7st.")
