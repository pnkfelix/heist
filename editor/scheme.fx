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
;;;   TAB in *s7st*,      the name before point completed, from those
;;;   M-TAB               s7st's top level sees
;;;   M-.                 in a Scheme buffer, as in an FX-26 one: its
;;;                       binder, or a definition in a buffer (from s7st's
;;;                       analysis of each Scheme buffer, which also gives
;;;                       its faces); else what s7st knows of the name
;;;
;;; s7st runs in a process of its own, `bin/s7st --serve`, started the
;;; first time it is asked for, so that the editor does not compile it
;;; when it starts, and a program that fails or does not end cannot stop
;;; the editor. s7st/main.fx says its requests and answers, a line each;
;;; the main loop looks for its answers every 50 ms while one is awaited
;;; (`s7-poll!`). What it writes goes to *s7st*, if there is one.
(module-parameters ((m-base (load-moduleof "base.fx"))
                    (m-buffer (load-moduleof "buffer.fx" m-base))
                    (m-resolve (load-moduleof "resolve.fx" m-base m-buffer))
                    (m-syntax (load-moduleof "syntax.fx" m-base m-buffer m-resolve))
                    (m-sexp (load-moduleof "sexp.fx" m-base m-buffer m-resolve m-syntax))
                    (m-index (load-moduleof "index.fx" m-base m-buffer m-resolve m-syntax m-sexp))
                    (m-view (load-moduleof "view.fx" m-base m-buffer m-resolve m-syntax m-sexp m-index))
                    (m-frame (load-moduleof "frame.fx" m-base m-buffer m-resolve m-syntax m-sexp m-index m-view))
                    (m-calls (load-moduleof "calls.fx" m-base m-buffer m-resolve m-syntax m-sexp m-index m-view m-frame))
                    (m-process (load-moduleof "process.fx" m-base m-buffer m-resolve m-syntax m-sexp m-index m-view m-frame m-calls))
                    (m-files (load-moduleof "files.fx" m-base m-buffer m-resolve m-syntax m-sexp m-index m-view m-frame m-calls m-process))
                    (m-help (load-moduleof "help.fx" m-base m-buffer m-resolve m-syntax m-sexp m-index m-view m-frame m-calls m-process m-files))
                    (m-eldoc (load-moduleof "eldoc.fx" m-base m-buffer m-resolve m-syntax m-sexp m-index m-view m-frame m-calls m-process m-files m-help))))
(hide (define kit-lists (load-module "../kit/lists.fx"))
      (import kit-lists map))
(hide (define kit-strings (load-module "../kit/strings.fx"))
      (import kit-strings string-split))

(define s7-prompt string "s7st> ")
"The server's process, once started; whether it has said it is ready; and
what it has written of a line not yet ended."
(define s7-server (ref ints @ed) (new nil))
(define s7-ready (ref bool @ed) (new #f))
(define s7-partial (ref string @ed) (new ""))
"*s7st*, once made."
(define s7-repl (ref (listof (actor buffer) acyclic) @ed) (new nil))
"Where in *s7st* output goes: before the prompt, if one is shown; and
where what is typed and not yet run starts, after the prompt."
(define s7-output-at (ref int @ed) (new 0))
(define s7-input-start (ref int @ed) (new 0))
"Who is told how what runs ends: the REPL (which writes each value), the
echo area (of a frame), or nobody (nothing runs)."
(define-type s7-client (sumof (none unit) (repl unit) (echo (actor frame))))
(define s7-client-now (ref s7-client @ed) (new (the s7-client (sum none #u))))
"The REPL's input sent and not yet started, and where it ends."
(define s7-submitted (ref string @ed) (new ""))
(define s7-submitted-end (ref int @ed) (new 0))
"What was written while the echo area's client ran, for it to show."
(define s7-echo-output (ref string @ed) (new ""))
"Who a `describe` awaited answers to: eldoc in a frame, or M-. there,
about a name."
(define-type s7-describing (productof (frame (actor frame)) (m-dot bool) (name string)))
(define s7-describe-for (ref (listof s7-describing acyclic) @ed) (new nil))
"A note at a place of a buffer: its span and text (cfa.fx keeps the CFA's)."
(define-type s7-note (productof (start int) (end int) (text string)))
"The notes a field says: lines `start end text`."
(define* s7-notes-of (subr spin (string) (listof s7-note acyclic))
  (lambda (s)
    (letrec ((lines (subr spin (int int (listof s7-note acyclic)) (listof s7-note acyclic))
               (lambda (i start acc)
                 (cond ((or (>= i (string-length s)) (char=? (string-ref s i) #\newline))
                        (let* ((line (substring s start (min i (string-length s))))
                               (sp1 (string-search line " " 0))
                               (sp2 (if (< sp1 0) -1 (string-search line " " (+ sp1 1))))
                               (acc2 (the (listof s7-note acyclic) (if (< sp2 0) acc
                                         (cons (product (start (max 0 (parse-nat (substring line 0 sp1) 10)))
                                                        (end (max 0 (parse-nat (substring line (+ sp1 1) sp2) 10)))
                                                        (text (substring line (+ sp2 1) (string-length line))))
                                               acc)))))
                          (if (>= i (string-length s)) (reverse acc2) (lines (+ i 1) (+ i 1) acc2))))
                       (else (lines (+ i 1) start acc))))))
      (lines 0 0 nil))))

"The analyses asked for and not yet answered: each request's key, and the
buffer and revision it is of."
(define-type s7-pending-analysis (productof (key int) (buffer (actor buffer)) (revision int)))
(define s7-analyses (ref (listof s7-pending-analysis acyclic) @ed) (new nil))
(define s7-next-key (ref int @ed) (new 0))
"A completion asked for: the frame, the buffer, and where its prefix is."
(define-type s7-completing (productof (frame (actor frame)) (buffer (actor buffer)) (start int) (end int) (prefix string)))
(define s7-completion (ref (listof s7-completing acyclic) @ed) (new nil))
"The directory *s7st*'s relative file names are relative to: that of the
buffer selected when it was made."
(define s7-repl-directory (ref string @ed) (new ""))
"Inputs run in the REPL, the last first; and which M-p last showed (-1: none)."
(define s7-history (ref strings @ed) (new nil))
(define s7-history-at (ref int @ed) (new -1))

;;; ------------------------------------------------------------ the server

"`s` with backslashes, newlines and tabs escaped, as the server's lines
have them; and back."
(define* s7-escape (subr spin (string) string)
  (lambda (s)
    (letrec ((go (subr spin (int (listof char acyclic)) (listof char acyclic))
               (lambda (i acc)
                 (if (>= i (string-length s)) acc
                     (let ((c (string-ref s i)))
                       (go (+ i 1) (cond ((char=? c #\\) (cons #\\ (cons #\\ acc)))
                                         ((char=? c #\newline) (cons #\n (cons #\\ acc)))
                                         ((char=? c #\tab) (cons #\t (cons #\\ acc)))
                                         (else (cons c acc)))))))))
      (list->string (reverse (go 0 nil))))))
(define* s7-unescape (subr spin (string) string)
  (lambda (s)
    (let ((n (string-length s)))
      (letrec ((go (subr spin (int (listof char acyclic)) (listof char acyclic))
                 (lambda (i acc)
                   (cond ((>= i n) acc)
                         ((and (char=? (string-ref s i) #\\) (< (+ i 1) n))
                          (let ((c (string-ref s (+ i 1))))
                            (go (+ i 2) (cons (cond ((char=? c #\n) #\newline) ((char=? c #\t) #\tab) (else c)) acc))))
                         (else (go (+ i 1) (cons (string-ref s i) acc)))))))
        (list->string (reverse (go 0 nil)))))))

"The server's process: started (`../bin/s7st --serve`, from editor/, where
the editor runs) if it is not. Whether there is one."
(define* s7-server-up! (subr cmd-eff () bool)
  (lambda ()
    (or (pair? (get s7-server))
        (tagcase (process-start (list "../bin/s7st" "--serve") "")
          (started id (begin (set s7-server (list id)) (set s7-ready #f) (set s7-partial "") #t))
          (failed e #f)))))
"Request `word` sent, with `fields`."
(define* s7-send! (subr cmd-eff (string strings) unit)
  (lambda (word fields)
    (let ((s (get s7-server)))
      (if (null? s) #u
          (letrec ((join (subr spin (strings) string)
                     (lambda (l) (cond ((null? l) "") ((null? (cdr l)) (s7-escape (car l)))
                                       (else (string-append (s7-escape (car l)) "\t" (join (cdr l))))))))
            (begin (process-write (car s) (string-append word " " (join fields) "\n")) #u))))))

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
          (repl u (s7-repl-say! (string-append (if (string=? error "") "" (string-append "Error: " error "\n")) s7-prompt) #t))
          (echo fr (let ((out (one-line (get s7-echo-output))))
                     (begin
                       (if (string=? error "") #u (s7-repl-say! (string-append "Error: " error "\n") #f))
                       (tell! fr (echo (string-append (if (string=? out "") "" (string-append out " "))
                                                      (if (string=? error "") (string-append "=> " value) (string-append "Error: " error))))))))
          (none u #u))))))

"The fields of an answer's rest, `s`: split at its tabs, each unescaped."
(define* s7-fields (subr spin (string) strings)
  (lambda (s) (map s7-unescape (string-split s #\tab))))
"Integer `s`, perhaps negative; 0 if it is none."
(define* s7-integer (subr spin (string) int)
  (lambda (s)
    (if (and (> (string-length s) 0) (char=? (string-ref s 0) #\-))
        (- 0 (max 0 (parse-nat (substring s 1 (string-length s)) 10)))
        (max 0 (parse-nat s 10)))))
(define* s7-nth-field (subr spin (strings int) string)
  (lambda (l i) (cond ((null? l) "") ((= i 0) (car l)) (else (s7-nth-field (cdr l) (- i 1))))))

"The annotation an `analysis` answer's fields say, of revision `rev`."
(define* s7-annotation (subr spin (strings int) annotation)
  (lambda (fs rev)
    (let* ((ints (lambda ((s string)) (letrec ((go (subr spin (strings) ints)
                                                    (lambda (l) (if (null? l) nil (cons (s7-integer (car l)) (go (cdr l)))))))
                                         (go (words s)))))
           (faces (letrec ((go (subr spin (ints) text-faces)
                             (lambda (l)
                               (if (or (null? l) (null? (cdr l)) (null? (cdr (cdr l)))) nil
                                   (cons (product (start (car l)) (end (car (cdr l)))
                                                  (face (let ((c (car (cdr (cdr l)))))
                                                          (cond ((= c 0) 'keyword) ((= c 1) 'function-name) ((= c 2) 'string) (else 'comment)))))
                                         (go (cdr (cdr (cdr l)))))))))
                    (go (ints (s7-nth-field fs 1)))))
           (defs (letrec ((go (subr spin (strings) definitions)
                            (lambda (l)
                              (if (or (null? l) (null? (cdr l)) (null? (cdr (cdr l)))) nil
                                  (cons (product (name (car l)) (start (s7-integer (car (cdr l)))) (end (s7-integer (car (cdr (cdr l))))))
                                        (go (cdr (cdr (cdr l)))))))))
                   (go (words (s7-nth-field fs 2)))))
           (refs (letrec ((go (subr spin (ints) references)
                            (lambda (l)
                              (if (or (null? l) (null? (cdr l)) (null? (cdr (cdr l))) (null? (cdr (cdr (cdr l))))) nil
                                  (cons (product (start (car l)) (end (car (cdr l)))
                                                 (binder-start (car (cdr (cdr l)))) (binder-end (car (cdr (cdr (cdr l))))))
                                        (go (cdr (cdr (cdr (cdr l))))))))))
                   (go (ints (s7-nth-field fs 3)))))
           (problem (s7-nth-field fs 4))
           (at (s7-integer (s7-nth-field fs 5))))
      (product (revision rev)
               (faces (if (< at 0) faces (merge-faces faces (list (product (start at) (end (+ at 1)) (face 'error))))))
               (definitions defs) (references refs) (links nil) (problem problem) (problem-at at)))))

"The longest prefix strings `l` share."
(define* s7-common-prefix (subr spin (strings) string)
  (lambda (l)
    (if (null? l) ""
        (letrec ((two (subr spin (string string int) int)
                   (lambda (a b i) (if (and (< i (string-length a)) (< i (string-length b)) (char=? (string-ref a i) (string-ref b i)))
                                       (two a b (+ i 1)) i)))
                 (go (subr spin (string strings) string)
                   (lambda (p l) (if (null? l) p (go (substring p 0 (two p (car l) 0)) (cdr l))))))
          (go (car l) (cdr l))))))
"Completions `names` of the prefix `c` asked for, done: the prefix made
their common one, and the rest said."
(define* s7-complete-with! (subr cmd-eff (s7-completing strings) unit)
  (lambda (c names)
    (let* ((fr (extract c frame))
           (common (s7-common-prefix names))
           (prefix (extract c prefix)))
      (if (null? names)
          (tell! fr (echo (string-append "No completions for " prefix)))
          (begin
            (if (> (string-length common) (string-length prefix))
                (tell! (extract c buffer)
                       (in-buffer fr (lambda ((b buffer))
                                       (let ((t (extract b text)) (a (extract c start)) (e (extract c end)))
                                         (if (and (<= e (rope-length t)) (string=? (rope-substring t a e) prefix))
                                             (done (with-text b (rope-insert (rope-delete t a e) a common) (+ a (string-length common))))
                                             (done b))))))
                #u)
            (tell! fr (echo (if (null? (cdr names)) (if (> (string-length common) (string-length prefix)) "" "Sole completion")
                                (one-line (letrec ((go (subr spin (strings int) string)
                                                         (lambda (l k) (cond ((null? l) "") ((= k 0) " ...")
                                                                             (else (string-append (car l) " " (go (cdr l) (- k 1))))))))
                                            (go names 12)))))))))))

"An answer of the server's, `line`, acted on."
(define* s7-answer! (subr cmd-eff (string) unit)
  (lambda (line)
    (let* ((sp (string-search line " " 0))
           (word (if (< sp 0) line (substring line 0 sp)))
           (fields (the strings (if (< sp 0) (list "") (s7-fields (substring line (+ sp 1) (string-length line))))))
           (text (car fields)))
      (cond
        ((string=? word "ready")
         (begin (set s7-ready #t)
           (if (string=? text "") #u (s7-repl-say! (string-append ";; s7st did not start: " text "\n") #f))))
        ((string=? word "started")
         (tagcase (get s7-client-now)
           (repl u (let ((input (get s7-submitted)))
                     (begin
                       (set s7-input-start (get s7-submitted-end))
                       (set s7-output-at (get s7-submitted-end))
                       (set s7-history-at -1)
                       (if (string=? (one-line input) "") #u (set s7-history (cons input (get s7-history)))))))
           (else y #u)))
        ((string=? word "incomplete") (set s7-client-now (sum none #u)))
        ((string=? word "busy")
         (tagcase (get s7-client-now)
           (echo fr (begin (set s7-client-now (sum none #u)) (tell! fr (echo "s7st is busy: C-c C-c in *s7st* interrupts it"))))
           (else y (set s7-client-now (sum none #u)))))
        ((string=? word "out")
         (begin (s7-repl-say! text #f)
           (tagcase (get s7-client-now)
             (echo fr (set s7-echo-output (string-append (get s7-echo-output) text)))
             (else y #u))))
        ((string=? word "value") (s7-finished! text ""))
        ((string=? word "error") (s7-finished! "" text))
        ((string=? word "interrupted")
         (let ((client (get s7-client-now)))
           (begin (set s7-client-now (sum none #u))
             (tagcase client
               (repl u (s7-repl-say! (string-append ";; interrupted\n" s7-prompt) #t))
               (echo fr (tell! fr (echo "Interrupted")))
               (none u #u)))))
        ((string=? word "describe")
         (let ((ds (get s7-describe-for)))
           (if (null? ds) #u
               (let ((d (car ds)))
                 (begin
                   (set s7-describe-for nil)
                   (if (extract d m-dot)
                       (tell! (extract d frame)
                              (echo (if (string=? text "") (string-append "No definition of " (extract d name) " found")
                                        (string-append "No definition of " (extract d name) " in a buffer; in s7st it is " text))))
                       (tell! (extract d frame) (eldoc-show text))))))))
        ((string=? word "analysis")
         (let ((key (s7-integer text)))
           (letrec ((find (subr spin ((listof s7-pending-analysis acyclic)) (sumof (none unit) (found s7-pending-analysis)))
                      (lambda (l) (cond ((null? l) (sum none #u)) ((= (extract (car l) key) key) (sum found (car l))) (else (find (cdr l))))))
                    (drop (subr spin ((listof s7-pending-analysis acyclic)) (listof s7-pending-analysis acyclic))
                      (lambda (l) (cond ((null? l) nil) ((= (extract (car l) key) key) (cdr l)) (else (cons (car l) (drop (cdr l))))))))
             (tagcase (find (get s7-analyses))
               (found a (begin (set s7-analyses (drop (get s7-analyses)))
                          (tell! (extract a buffer) (annotate (s7-annotation fields (extract a revision))))))
               (none u #u)))))
        ((string=? word "completions")
         (let ((cs (get s7-completion)))
           (if (null? cs) #u
               (begin (set s7-completion nil)
                 (s7-complete-with! (car cs) (if (string=? text "") nil fields))))))
        (else #u)))))

"The server's answers so far acted on. Whether one is still awaited, for
the main loop to look again in 50 ms."
(define* s7-poll! (subr cmd-eff () bool)
  (lambda ()
    (let ((s (get s7-server)))
      (if (null? s) #f
          (let ((text (string-append (get s7-partial) (process-output (car s)))))
            (letrec ((lines (subr cmd-eff (int) unit)
                       (lambda (from)
                         (let ((e (string-search text "\n" from)))
                           (if (< e 0) (set s7-partial (substring text from (string-length text)))
                               (begin (s7-answer! (substring text from e)) (lines (+ e 1))))))))
              (begin
                (lines 0)
                (tagcase (process-status (car s))
                  (running u #u)
                  (else y (begin (set s7-server nil)
                            (tagcase (get s7-client-now)
                              (none u #u)
                              (else z (s7-finished! "" "s7st's process ended")))
                            (s7-repl-say! ";; s7st's process ended; it starts again when next asked for\n" #f))))
                (and (pair? (get s7-server))
                     (or (not (get s7-ready))
                         (pair? (get s7-describe-for))
                         (pair? (get s7-analyses))
                         (pair? (get s7-completion))
                         (tagcase (get s7-client-now) (none u #f) (else z #t)))))))))))

"The server stopped (the editor ends)."
(define* s7-stop! (subr cmd-eff () unit)
  (lambda ()
    (let ((s (get s7-server)))
      (if (null? s) #u (begin (process-close-input (car s)) (process-signal (car s) 1) (set s7-server nil))))))

"Text `text` (of `file`, \"\" if none) sent to run for `client`, relative
file names relative to `dir`; `repl`: only if its data are whole, each
value written. What to say if it cannot be (\"\": nothing)."
(define* s7-run! (subr cmd-eff (string string string bool s7-client) string)
  (lambda (text file dir repl client)
    (cond ((tagcase (get s7-client-now) (none u #f) (else y #t)) "s7st is busy: C-c C-c in *s7st* interrupts it")
          ((not (s7-server-up!)) "s7st could not be started (../bin/s7st)")
          (else (begin
                  (set s7-client-now client)
                  (set s7-echo-output "")
                  (s7-send! "run" (list (if repl "repl" "quiet") dir file text))
                  (if (get s7-ready) "" "Starting s7st..."))))))

;;; ------------------------------------------------------------ the REPL

(define s7-banner string
  ";; s7st: R7RS Scheme, interpreted in FX-26. RET runs what is typed once it is whole;\n;; C-c C-c interrupts; M-p and M-n go through the history. (docs/s7st.md)\n")

"A buffer's next state, with nothing else to do."
(define* done-reply (subr turn-eff (buffer) (reply buffer))
  (lambda (b) (reply-with b (notify b))))

"M-x run-s7st: *s7st* shown in the selected window, made if need be; and
s7st started."
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
                                    (if (s7-server-up!) #u
                                        (s7-repl-say! ";; s7st could not be started (../bin/s7st)\n" #f))))))))))))
"Input `input`, ending at `end`, sent to run if it is whole."
(define* s7-submit! (subr cmd-eff (string int) unit)
  (lambda (input end)
    (begin
      (set s7-submitted input)
      (set s7-submitted-end end)
      (let ((said (s7-run! input "" (get s7-repl-directory) #t (sum repl #u))))
        (cond ((string=? said "") #u)
              ((string=? said "Starting s7st...") #u)
              (else (s7-repl-say! (string-append ";; " said "\n") #f)))))))

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
      (reply-with f (list (lambda ()
                            (tagcase (get s7-client-now)
                              (none u (tell! fr (echo "s7st runs nothing")))
                              (else y (s7-send! "interrupt" nil)))))))))

"Eldoc in a Scheme buffer (eldoc.fx), where the CFA found nothing at
point (cfa.fx): what s7st knows of the name at point, or of the operator
of the call around it -- if s7st runs."
(define* s7-eldoc (subr pure ((actor frame) (actor buffer) int int string string) cmd)
  (lambda (fr b rev p here op)
    (lambda ()
      (if (and (pair? (get s7-server)) (get s7-ready))
          (begin (set s7-describe-for (list (product (frame fr) (m-dot #f) (name here)))) (s7-send! "describe" (list here op)))
          #u))))
(set scheme-eldoc (list s7-eldoc))

"M-. on a name a Scheme buffer defines nowhere: what s7st knows of it."
(define* s7-no-definition (subr pure ((actor frame) string) cmd)
  (lambda (fr name)
    (lambda ()
      (if (and (pair? (get s7-server)) (get s7-ready))
          (begin (set s7-describe-for (list (product (frame fr) (m-dot #t) (name name)))) (s7-send! "describe" (list name "")))
          (tell! fr (echo (string-append "No definition of " name " found")))))))
(set scheme-no-definition (list s7-no-definition))

;;; ------------------------------------------------------------ analysis, completion

"A Scheme buffer's analysis actor's state: its buffer, and the revision
last sent to be analysed."
(define-type s7-analysis-state (productof (buffer (actor buffer)) (revision int)))
"Message for an analysis actor: a snapshot of its buffer, sent to s7st to
be analysed (the server started if need be) unless it is of the revision
sent last. The answer comes to `s7-answer!`."
(define* s7-analysis-snapshot (subr pure (snapshot) (msg s7-analysis-state))
  (lambda (snap)
    (lambda ((st s7-analysis-state))
      (let ((rev (extract snap revision)) (b (extract st buffer)))
        (if (= rev (extract st revision))
            (same st)
            (reply-with (product (buffer b) (revision rev))
                        (list (lambda ()
                                (if (s7-server-up!)
                                    (let ((key (get s7-next-key)))
                                      (begin
                                        (set s7-next-key (+ key 1))
                                        (set s7-analyses (cons (product (key key) (buffer b) (revision rev)) (get s7-analyses)))
                                        (s7-send! "analyze" (list (int->string key) (extract snap name) (rope->string (extract snap text))))))
                                    #u)))))))))
"A Scheme buffer's analysis actor, idle, subscribed to it."
(define* s7-attach (subr (maxeff (alloc @ed) (read @globals)) ((actor buffer) string) cmds)
  (lambda (b name)
    (let ((sx (spawn-actor (string-append "s7st analysis of " name) (product (buffer b) (revision -1)))))
      (list (lambda () (set-class! sx idle))
            (tell b (subscribe -1 (lambda ((s snapshot)) (tell-latest sx "snapshot" (s7-analysis-snapshot s)))))))))
(set scheme-attach (list s7-attach))

"Completion (TAB in *s7st*, M-TAB in a Scheme buffer): the name before
point completed from those s7st's top level sees."
(define* s7-complete (subr pure () frame-action)
  (lambda ()
    (lambda ((fr (actor frame)) (f frame))
      (let* ((b (extract (selected-window f) buffer))
             (st (actor-state b))
             (t (extract st text))
             (p (extract st point))
             (a (name-start t p))
             (prefix (rope-substring t a p)))
        (if (string=? prefix "")
            (draw (with-echo f "Nothing to complete"))
            (reply-with f (list (lambda ()
                                  (if (s7-server-up!)
                                      (begin (set s7-completion (list (product (frame fr) (buffer b) (start a) (end p) (prefix prefix))))
                                        (s7-send! "complete" (list prefix))
                                        (if (get s7-ready) #u (tell! fr (echo "Starting s7st..."))))
                                      (tell! fr (echo "s7st could not be started (../bin/s7st)")))))))))))

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
                                        (let ((said (s7-run! (extract x text) (extract x file) (directory-of (extract st file)) #f (sum echo fr))))
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
(define-command! "s7st-complete" (sum on-frame (s7-complete)))
(define-buffer-key! "*s7st*" "TAB" "s7st-complete")
(define-buffer-key! "*s7st*" "M-TAB" "s7st-complete")
(define-buffer-key! "<scheme>" "M-TAB" "s7st-complete")
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
(define-doc! "s7st-complete" "Complete the name before point from those s7st's top level sees (TAB in *s7st*, M-TAB in a Scheme buffer).")
