;;; process.fx: programs run beside the editor, their output in a buffer
;;; (Fixpt's `process-*` primitives, Heist's FIXPT-CHANGES.md F4).
;;;
;;;   M-x compile, C-c c  a shell command, its output in *compilation*
;;;   M-x grep            a grep command, its output in *grep*
;;;   C-x `, M-g n, M-g p the next (previous) place the output names, visited
;;;   RET in either       the place on this line, visited
;;;   g in either         its command run again, where it ran (M-x recompile)
;;;   C-c C-k             the compilation interrupted
;;;   M-!                 a shell command, its output in *Shell Command Output*
;;;   M-x shell           a shell, in *shell*: RET sends the line, C-c C-c
;;;                       interrupts what it runs
;;;
;;; A process's output is asked for, never waited for: the main loop polls
;;; each running one (`poll-processes!`), every 50 ms while any runs, and
;;; tells its buffer what came. Fixpt cannot yet wait for a process in a
;;; `pselect`; F4 says what that would take.

"A program running: its number, the buffer its output goes to, the frame
(for the echo area), what it is (\"compilation\", \"command\", \"shell\"),
and where in the buffer its output has reached, after which is the input
typed and not yet sent."
(define-type running-process
  (productof (id int) (buffer (actor buffer)) (frame (actor frame)) (kind string) (input-start int)))
(define live-processes (ref (listof running-process acyclic) @ed) (new nil))

(define* process-of (subr (maxeff (read @ed) spin) ((actor buffer)) (sumof (none unit) (found running-process)))
  (lambda (b)
    (letrec ((go (->* ((listof running-process acyclic)) (sumof (none unit) (found running-process)))
               (lambda (ps) (cond ((null? ps) (sum none #u))
                                  ((same-actor? (extract (car ps) buffer) b) (sum found (car ps)))
                                  (else (go (cdr ps)))))))
      (go (get live-processes)))))

"The processes but number `id`; and with its input starting at `at`."
(define* without-process (subr spin (int (listof running-process acyclic)) (listof running-process acyclic))
  (lambda (id ps)
    (cond ((null? ps) nil)
          ((= (extract (car ps) id) id) (cdr ps))
          (else (cons (car ps) (without-process id (cdr ps)))))))
(define* set-input-start! (subr (maxeff (read @ed) (write @ed) spin) (int int) unit)
  (lambda (id at)
    (set live-processes
         (letrec ((go (subr spin ((listof running-process acyclic)) (listof running-process acyclic))
                    (lambda (ps)
                      (cond ((null? ps) nil)
                            ((= (extract (car ps) id) id)
                             (let ((p (car ps)))
                               (cons (product (id id) (buffer (extract p buffer)) (frame (extract p frame))
                                              (kind (extract p kind)) (input-start at))
                                     (cdr ps))))
                            (else (cons (car ps) (go (cdr ps))))))))
           (go (get live-processes))))))

"The process numbered `id`, if it runs."
(define* process-of-id (subr (maxeff (read @ed) spin) (int) (sumof (none unit) (found running-process)))
  (lambda (id)
    (letrec ((go (->* ((listof running-process acyclic)) (sumof (none unit) (found running-process)))
               (lambda (ps) (cond ((null? ps) (sum none #u))
                                  ((= (extract (car ps) id) id) (sum found (car ps)))
                                  (else (go (cdr ps)))))))
      (go (get live-processes)))))

"Message for a buffer: process `id`'s output `s`, put where its output
has reached, before any input typed after it; point kept after it if it
was there or later (as comint does); and the process told where its
output now ends. The buffer is no more modified than it was."
(define* process-insert (subr pure (int string) (msg buffer))
  (lambda (id s)
    (lambda ((b buffer))
      (let* ((t (extract b text))
             (at (tagcase (process-of-id id)
                   (found p (min (extract p input-start) (rope-length t)))
                   (none u (rope-length t))))
             (n (string-length s))
             (p (extract b point))
             (b1 (with-text b (rope-insert t at s) (if (>= p at) (+ p n) p)))
             ;; Output is no change of the user's: modified only if it was.
             (b2 (buffer-of b1 (extract b1 text) (extract b1 point) (extract b1 mark) (extract b1 revision)
                            (extract b modified) (extract b1 undo) (extract b1 subscribers))))
        (reply-with b2 (cons (lambda () (set-input-start! id (+ at n))) (notify b2)))))))

"What is said in its buffer when a process ends, and in the echo area."
(define* end-words (subr spin (string bool int) (productof (line string) (echo string)))
  (lambda (kind exited code)
    (let ((how (cond ((and exited (= code 0)) "finished")
                     (exited (string-append "exited abnormally with code " (int->string code)))
                     (else (string-append "killed by signal " (int->string code))))))
      (cond ((and (string=? kind "grep") exited (<= code 1))
             (let ((w (if (= code 0) "Grep finished with matches found" "Grep finished with no matches found")))
               (product (line (string-append "\n" w "\n")) (echo w))))
            ((string=? kind "grep")
             (product (line (string-append "\nGrep " how "\n")) (echo (string-append "Grep " how))))
            ((string=? kind "compilation")
             (product (line (string-append "\nCompilation " how "\n")) (echo (string-append "Compilation " how))))
            ((string=? kind "shell") (product (line (string-append "\nProcess shell " how "\n")) (echo "")))
            (else (product (line "") (echo (if (and exited (= code 0)) "" (string-append "Shell command " how)))))))))

"Process `p`'s output sent to its buffer; if it has ended, that said,
and it dropped."
(define* poll-one! (subr cmd-eff (running-process) unit)
  (lambda (p)
    (let* ((id (extract p id))
           (status (process-status id))
           (out (process-output id))
           (ended (lambda ((exited bool) (code int))
                    (let ((w (end-words (extract p kind) exited code)))
                      (begin
                        (if (string=? (extract w line) "") #u (tell! (extract p buffer) (process-insert id (extract w line))))
                        (if (string=? (extract w echo) "") #u (tell! (extract p frame) (echo (extract w echo))))
                        ;; Dropped after the buffer's turns that use where its output reached.
                        (tell! (extract p buffer)
                               (lambda ((b buffer))
                                 (reply-with b (list (lambda () (set live-processes (without-process id (get live-processes)))))))))))))
      (begin
        (if (string=? out "") #u (tell! (extract p buffer) (process-insert id out)))
        (tagcase status
          (running u #u)
          (exited c (ended #t c))
          (signalled s (ended #f s))
          (unknown u (ended #f 0)))))))

"Each running process's output sent to its buffer, and those that have
ended said so and dropped. Whether any still runs."
(define* poll-processes! (subr cmd-eff () bool)
  (lambda ()
    (begin
      (letrec ((each (subr cmd-eff ((listof running-process acyclic)) unit)
                 (lambda (ps) (if (null? ps) #u (begin (poll-one! (car ps)) (each (cdr ps)))))))
        (each (get live-processes)))
      (pair? (get live-processes)))))

"Every process sent signal `sig` (the editor ending: 1, a hangup)."
(define* signal-processes! (subr cmd-eff (int) unit)
  (lambda (sig)
    (letrec ((each (subr cmd-eff ((listof running-process acyclic)) unit)
               (lambda (ps) (if (null? ps) #u (begin (process-signal (extract (car ps) id) sig) (each (cdr ps)))))))
      (each (get live-processes)))))

"Program `argv` started in `dir`, its output to buffer `b`."
(define* start-process! (subr cmd-eff ((actor frame) (actor buffer) string strings string int) unit)
  (lambda (fr b kind argv dir at)
    (tagcase (process-start argv dir)
      (started id (set live-processes (cons (product (id id) (buffer b) (frame fr) (kind kind) (input-start at))
                                            (get live-processes))))
      (failed e (tell! fr (echo (string-append "Could not start " (car argv) ": " (extract e detail))))))))

;;; ------------------------------------------------------------ showing a buffer elsewhere

"Whether a window shows buffer `b`."
(define* shown? (subr spin (windows (actor buffer)) bool)
  (lambda (ws b) (and (pair? ws) (or (same-actor? (extract (car ws) buffer) b) (shown? (cdr ws) b)))))

"Buffer `b` shown in a window, the selected one staying selected: one
that shows it already; else the first other window; else the selected
one split, the new window below showing it (Emacs's `display-buffer`)."
(define* display-buffer (subr turn-eff ((actor frame) frame (actor buffer)) (reply frame))
  (lambda (fr f b)
    (let ((ws (extract f windows)) (sel (extract f selected)))
      (cond ((shown? ws b) (draw f))
            ((null? (cdr ws)) (split-showing fr f b))
            (else
             (let* ((old (letrec ((go (subr spin (windows) window)
                                    (lambda (ws) (if (= (extract (car ws) id) sel) (go (cdr ws)) (car ws)))))
                           (go ws)))
                    (id (extract f next-id))
                    (made (new-window fr f b id (extract old height)))
                    (ws2 (letrec ((go (subr spin (windows) windows)
                                        (lambda (ws)
                                          (cond ((null? ws) nil)
                                                ((= (extract (car ws) id) (extract old id)) (cons (extract made window) (cdr ws)))
                                                (else (cons (car ws) (go (cdr ws))))))))
                           (go ws))))
               (reply-with (frame-of f ws2 sel (extract f buffers) (+ id 1) (extract f echo) (extract f prefix) (extract f mini))
                           (cons (tell (extract old buffer) (unsubscribe (extract old id))) (extract made cmds)))))))))

"Message for the frame: buffer `b` made, known by name, and shown
elsewhere (`display-buffer`)."
(define* buffer-made-elsewhere (subr pure ((actor frame) string (actor buffer)) (msg frame))
  (lambda (fr name b)
    (lambda ((f frame))
      (display-buffer fr (frame-of f (extract f windows) (extract f selected)
                                   (append (extract f buffers) (list (product (name name) (file "") (actor b))))
                                   (extract f next-id) (extract f echo) (extract f prefix) (extract f mini))
                      b))))

"Message for a buffer: its text replaced by `s`, point at its end if
`at-end`, else at its start."
(define* reset-text (subr pure (string bool) (msg buffer))
  (lambda (s at-end)
    (lambda ((b buffer))
      (let ((b2 (buffer-of b (string->rope s) (if at-end (string-length s) 0) -1 (+ 1 (extract b revision)) #f
                           nil (extract b subscribers))))
        (reply-with b2 (notify b2))))))

"Program `argv` run in `dir`, its output in buffer `name` after `header`
(the buffer made, or emptied and its process stopped), shown elsewhere --
or, if `pop` (a shell), in the selected window, point at its end."
(define* run-in-buffer (subr turn-eff ((actor frame) frame string string strings string string bool) (reply frame))
  (lambda (fr f name kind argv dir header pop)
    (begin
      (tagcase (find-buffer (extract f buffers) name)
        (found info
          (let* ((b (extract info actor))
                 (r (if pop (show-buffer fr f b) (display-buffer fr f b))))
            (reply-with (extract r state)
                        (append (list (lambda ()
                                        (begin
                                          (tagcase (process-of b)
                                            (found p (begin (process-signal (extract p id) 15)
                                                       (set live-processes (without-process (extract p id) (get live-processes)))))
                                            (none u #u))
                                          (tell! b (reset-text header pop))
                                          (start-process! fr b kind argv dir (string-length header)))))
                                (extract r cmds)))))
        (none u
          (reply-with f (list (lambda ()
                                (let ((b (spawn-actor name (buffer-of (new-buffer name "" (string->rope header))
                                                                      (string->rope header) (if pop (string-length header) 0)
                                                                      -1 0 #f nil nil))))
                                  (begin (tell! fr (if pop (buffer-made fr name "" b) (buffer-made-elsewhere fr name b)))
                                    (start-process! fr b kind argv dir (string-length header))))))))))))

"The directory of the selected window's buffer's file (\"\": the
editor's own)."
(define* selected-directory (subr turn-eff (frame) string)
  (lambda (f)
    (let ((b (extract (selected-window f) buffer)))
      (letrec ((go (subr spin (buffer-infos) string)
                 (lambda (bs)
                   (cond ((null? bs) "")
                         ((same-actor? (extract (car bs) actor) b) (directory-of (extract (car bs) file)))
                         (else (go (cdr bs)))))))
        (go (extract f buffers))))))

;;; ------------------------------------------------------------ compiling

(define last-compile-command (ref string @ed) (new "make -k "))
(define last-grep-command (ref string @ed) (new "grep -nH -e "))
"The buffer whose places `next-error` visits (*compilation*, *grep*),
and where in it it has reached."
(define next-error-buffer (ref string @ed) (new "*compilation*"))
(define compile-error-at (ref int @ed) (new 0))

"Shell command `cmd` run in `dir`, its output in buffer `name` after a
header saying where it ran (which the places it names are relative to);
`next-error` to visit them, from after the header."
(define* run-compilation (subr turn-eff ((actor frame) frame string string string string) (reply frame))
  (lambda (fr f name kind cmd dir)
    (let* ((header (string-append "-*- mode: " kind "; default-directory: \"" dir "\" -*-\n"
                                  (if (string=? kind "grep") "Grep" "Compilation") " started\n\n" cmd "\n"))
           (r (run-in-buffer fr f name kind (list "/bin/sh" "-c" cmd) dir header #f)))
      (reply-with (extract r state)
                  (cons (lambda () (begin (set next-error-buffer name) (set compile-error-at (string-length header))))
                        (extract r cmds))))))

"The directory an output buffer's header gives, from text `t`."
(define* output-directory (subr spin (rope) string)
  (lambda (t)
    (let* ((first (rope-substring t 0 (rope-line-end t 0)))
           (key "default-directory: \"")
           (a (string-search first key 0)))
      (if (< a 0) ""
          (let* ((from (+ a (string-length key)))
                 (e (string-search first "\"" from)))
            (if (< e 0) "" (substring first from e)))))))

"M-x compile: a command read, run by the shell in the buffer's
directory, its output in *compilation*."
(define* compile (subr pure () frame-action)
  (lambda ()
    (lambda ((fr (actor frame)) (f frame))
      (let ((dir (selected-directory f)))
        (read-string f "Compile command: " (get last-compile-command)
                     (lambda ((fr (actor frame)) (f frame) (cmd string))
                       (let ((r (run-compilation fr f "*compilation*" "compilation" cmd dir)))
                         (reply-with (extract r state)
                                     (cons (lambda () (set last-compile-command cmd)) (extract r cmds))))))))))

"g in *compilation* or *grep*, M-x recompile: its command run again, where
it ran before (its header says what and where)."
(define* recompile (subr pure () frame-action)
  (lambda ()
    (lambda ((fr (actor frame)) (f frame))
      (let* ((here (extract (actor-state (extract (selected-window f) buffer)) name))
             (name (if (or (string=? here "*compilation*") (string=? here "*grep*")) here (get next-error-buffer))))
        (tagcase (find-buffer (extract f buffers) name)
          (none u (draw (with-echo f "No compilation to run again")))
          (found info
            (let* ((t (extract (actor-state (extract info actor)) text))
                   (cmd (rope-substring t (rope-line-start t 3) (rope-line-end t 3))))
              (run-compilation fr f name (if (string=? name "*grep*") "grep" "compilation") cmd (output-directory t)))))))))

"M-x grep: a grep command read and run, as M-x compile runs one, its
output in *grep*."
(define* grep (subr pure () frame-action)
  (lambda ()
    (lambda ((fr (actor frame)) (f frame))
      (let ((dir (selected-directory f)))
        (read-string f "Run grep (like this): " (get last-grep-command)
                     (lambda ((fr (actor frame)) (f frame) (cmd string))
                       (let ((r (run-compilation fr f "*grep*" "grep" cmd dir)))
                         (reply-with (extract r state)
                                     (cons (lambda () (set last-grep-command cmd)) (extract r cmds))))))))))

"M-!: a command read, run by the shell, its output in *Shell Command
Output*."
(define* shell-command (subr pure () frame-action)
  (lambda ()
    (lambda ((fr (actor frame)) (f frame))
      (let ((dir (selected-directory f)))
        (read-string f "Shell command: " ""
                     (lambda ((fr (actor frame)) (f frame) (cmd string))
                       (run-in-buffer fr f "*Shell Command Output*" "command" (list "/bin/sh" "-c" cmd) dir "" #f)))))))

"M-x shell: a shell in *shell*, reading what RET sends."
(define* shell (subr pure () frame-action)
  (lambda ()
    (lambda ((fr (actor frame)) (f frame))
      (tagcase (find-buffer (extract f buffers) "*shell*")
        (found info
          (if (pair? (letrec ((go (->* ((listof running-process acyclic)) (listof running-process acyclic))
                                    (lambda (ps) (cond ((null? ps) nil)
                                                       ((same-actor? (extract (car ps) buffer) (extract info actor)) ps)
                                                       (else (go (cdr ps)))))))
                       (go (get live-processes))))
              (show-buffer fr f (extract info actor))
              (run-in-buffer fr f "*shell*" "shell" (list "/bin/sh" "-i") (selected-directory f) "" #t)))
        (none u (run-in-buffer fr f "*shell*" "shell" (list "/bin/sh" "-i") (selected-directory f) "" #t))))))

"RET in a process's buffer: the text after its output sent to it, with a
newline."
(define* send-input (subr pure () command)
  (lambda ()
    (lambda ((b buffer))
      (let ((t (extract b text)))
        (tagcase (letrec ((go (->* ((listof running-process acyclic)) (sumof (none unit) (found running-process)))
                                (lambda (ps) (cond ((null? ps) (sum none #u))
                                                   ((string=? (extract (actor-state (extract (car ps) buffer)) name) (extract b name))
                                                    (sum found (car ps)))
                                                   (else (go (cdr ps)))))))
                   (go (get live-processes)))
          (none u (say b "No process"))
          (found p
            (let* ((n (rope-length t))
                   (from (min (extract p input-start) n))
                   (line (rope-substring t from n))
                   (b2 (with-text b (rope-insert t n "\n") (+ n 1))))
              (product (buffer b2)
                       (cmds (list (lambda () (begin (process-write (extract p id) (string-append line "\n"))
                                                (set-input-start! (extract p id) (+ n 1))))))
                       (message "")))))))))

"A signal sent to the process of the selected window's buffer."
(define* signal-process (subr pure (int string) frame-action)
  (lambda (sig what)
    (lambda ((fr (actor frame)) (f frame))
      (tagcase (process-of (extract (selected-window f) buffer))
        (found p (let ((r (draw (with-echo f what))))
                   (reply-with (extract r state) (cons (lambda () (process-signal (extract p id) sig)) (extract r cmds)))))
        (none u (draw (with-echo f "No process")))))))

;;; ------------------------------------------------------------ places in output

"A place a line of output names, as compilers and grep write one."
(define-type location (productof (file string) (line int) (column int)))

"The first place line `s` names: `FILE:LINE`, then `:COLUMN` perhaps;
FILE a word with a `.` or `/` in it, so that a time (10:30) is none."
(define* line-location (subr spin (string) (sumof (none unit) (found location)))
  (lambda (s)
    (let ((n (string-length s)))
      (letrec ((digits (subr spin (int) int)
                 ;; Where the digits from `i` end.
                 (lambda (i) (if (and (< i n) (char-numeric? (string-ref s i))) (digits (+ i 1)) i)))
               (number (subr spin (int int) int)
                 (lambda (i e) (letrec ((go (subr spin (int int) int)
                                          (lambda (i acc) (if (>= i e) acc (go (+ i 1) (+ (* 10 acc) (- (char->integer (string-ref s i)) 48)))))))
                                 (go i 0))))
               (word-start (subr spin (int) int)
                 (lambda (i) (if (and (> i 0) (not (char-in? (string-ref s (- i 1)) " \t\"'(:"))) (word-start (- i 1)) i)))
               (has-dot-or-slash? (subr spin (int int) bool)
                 (lambda (i e) (and (< i e) (or (char-in? (string-ref s i) "./") (has-dot-or-slash? (+ i 1) e)))))
               (at (subr spin (int) (sumof (none unit) (found location)))
                 (lambda (i)
                   (cond ((>= (+ i 1) n) (sum none #u))
                         ((and (char=? (string-ref s i) #\:) (char-numeric? (string-ref s (+ i 1))))
                          (let* ((w (word-start i))
                                 (le (digits (+ i 1)))
                                 (ce (if (and (< (+ le 1) n) (char=? (string-ref s le) #\:) (char-numeric? (string-ref s (+ le 1))))
                                         (digits (+ le 1))
                                         -1)))
                            (if (has-dot-or-slash? w i)
                                (sum found (product (file (substring s w i)) (line (number (+ i 1) le))
                                                    (column (if (< ce 0) 0 (number (+ le 1) ce)))))
                                (at (+ i 1)))))
                         (else (at (+ i 1)))))))
        (at 0)))))

"Message for the frame: `file` visited at line `line` (from 1) and column
`column` (from 1; 0 none), in the selected window -- or, if that shows
`away`, in another, split off if there is none."
(define* visit-location (subr pure ((actor frame) string int int (actor buffer)) (msg frame))
  (lambda (fr file line column away)
    (lambda ((f frame))
      (let* ((f2 (cond ((not (same-actor? (extract (selected-window f) buffer) away)) (same f))
                       ((null? (cdr (extract f windows))) (split-showing fr f away))
                       (else (same f))))
             (f3 (extract f2 state))
             (f4 (if (same-actor? (extract (selected-window f3) buffer) away)
                     (frame-of f3 (extract f3 windows)
                               (letrec ((go (subr spin (windows) int)
                                          (lambda (ws) (cond ((null? ws) (extract f3 selected))
                                                             ((same-actor? (extract (car ws) buffer) away) (go (cdr ws)))
                                                             (else (extract (car ws) id))))))
                                 (go (extract f3 windows)))
                               (extract f3 buffers) (extract f3 next-id) (extract f3 echo) (extract f3 prefix) (extract f3 mini))
                     f3))
             (pos-in (lambda ((t rope))
                       (let ((ls (rope-line-start t (max 0 (- line 1)))))
                         (min (+ ls (max 0 (- column 1))) (rope-line-end t (max 0 (- line 1))))))))
        (tagcase (find-file-buffer (extract f4 buffers) file)
          (found info
            (let ((r (go-to-place fr f4 (product (buffer (extract info actor))
                                                 (point (pos-in (extract (actor-state (extract info actor)) text)))))))
              (reply-with (extract r state) (append (extract f2 cmds) (extract r cmds)))))
          (none u
            (let ((bname (unique-name (extract f4 buffers) (base-name file))))
              (reply-with f4 (append (extract f2 cmds)
                                     (list (lambda ()
                                             (let* ((got (file-text file))
                                                    (b (spawn-actor bname (new-buffer bname file (extract got text)))))
                                               (if (extract got found)
                                                   (begin (tell! fr (buffer-made fr bname file b))
                                                     (tell! b (in-buffer fr (goto-position (pos-in (extract got text))))))
                                                   (tell! fr (echo (string-append "No file " file))))))))))))))))

"The directory in `s` after `key`, between quotes (` or ', and '), with
a `/` after it; \"\" if `key` is not in `s`."
(define* quoted-directory (subr spin (string string) string)
  (lambda (s key)
    (let ((a (string-search s key 0)))
      (if (< a 0) ""
          (let* ((from (+ (+ a (string-length key)) 1))
                 (e (string-search s "'" from)))
            (if (or (< e 0) (> from (string-length s))) ""
                (string-append (substring s from e) "/")))))))

"The directory names on line `i` of output `t` are relative to: the last
`Entering directory 'D'` before it not left again (as make, and the
editor's tests, say), else the one its header gives."
(define* directory-at (subr spin (rope int) string)
  (lambda (t i)
    (letrec ((go (subr spin (int int) string)
               ;; Line `j` and before, `left` directories left and not yet entered.
               (lambda (j left)
                 (if (< j 0)
                     (output-directory t)
                     (let* ((s (rope-substring t (rope-line-start t j) (rope-line-end t j)))
                            (in (quoted-directory s "Entering directory "))
                            (out (quoted-directory s "Leaving directory ")))
                       (cond ((not (string=? out "")) (go (- j 1) (+ left 1)))
                             ((string=? in "") (go (- j 1) left))
                             ((= left 0) in)
                             (else (go (- j 1) (- left 1)))))))))
      (go (- i 1) 0))))

"The place line `i` of compilation buffer `b` names, visited; and the
line shown as the current one there. Whether there was one."
(define* visit-line-of (subr turn-eff ((actor frame) (actor buffer) int) (sumof (none unit) (found cmds)))
  (lambda (fr b i)
    (let* ((t (extract (actor-state b) text))
           (a (rope-line-start t i))
           (e (rope-line-end t i)))
      (tagcase (line-location (rope-substring t a e))
        (none u (sum none #u))
        (found l
          (sum found (list (lambda ()
                             (let ((file (expand-file-name (extract l file) (directory-at t i))))
                               (begin (set compile-error-at (+ e 1))
                                 (set next-error-buffer (extract (actor-state b) name))
                                 (tell! b (in-buffer fr (lambda ((b buffer)) (done (with-marks (with-point b a)
                                                                                                (list (product (start a) (end e) (face 'use))))))))
                                 (tell! fr (visit-location fr file (extract l line) (extract l column) b))))))))))))

"C-x `: the next place *compilation* names after the last visited (`dir`
1); M-g p: the one before (-1)."
(define* next-error (subr pure (int) frame-action)
  (lambda (dir)
    (lambda ((fr (actor frame)) (f frame))
      (tagcase (find-buffer (extract f buffers) (get next-error-buffer))
        (none u (draw (with-echo f "No compilation buffer")))
        (found info
          (let* ((b (extract info actor))
                 (t (extract (actor-state b) text))
                 (last (rope-line-count t))
                 (from (rope-line-of t (min (get compile-error-at) (rope-length t))))
                 ;; Going back, from the line before the one visited last.
                 (start (if (> dir 0) from (- from 2))))
            (letrec ((go (subr turn-eff (int) (reply frame))
                       (lambda (i)
                         (if (or (< i 0) (>= i last))
                             (draw (with-echo f (if (> dir 0) "No more errors" "No earlier errors")))
                             (tagcase (visit-line-of fr b i)
                               (found cs (reply-with f cs))
                               (none u (go (+ i dir))))))))
              (go start))))))))

"RET in *compilation*: the place on point's line visited."
(define* compile-goto-error (subr pure () frame-action)
  (lambda ()
    (lambda ((fr (actor frame)) (f frame))
      (let* ((b (extract (selected-window f) buffer))
             (st (actor-state b)))
        (tagcase (visit-line-of fr b (rope-line-of (extract st text) (extract st point)))
          (found cs (reply-with f cs))
          (none u (draw (with-echo f "No place on this line"))))))))

(define-command! "compile" (sum on-frame (compile)))
(define-command! "shell-command" (sum on-frame (shell-command)))
(define-command! "shell" (sum on-frame (shell)))
(define-command! "next-error" (sum on-frame (next-error 1)))
(define-command! "previous-error" (sum on-frame (next-error -1)))
(define-command! "compile-goto-error" (sum on-frame (compile-goto-error)))
(define-command! "kill-compilation" (sum on-frame (signal-process 2 "Interrupted")))
(define-command! "comint-send-input" (sum on-buffer (send-input)))
(define-command! "comint-interrupt-subjob" (sum on-frame (signal-process 2 "")))
(define-key! "C-c c" "compile")
(define-key! "M-!" "shell-command")
(define-key! "C-x `" "next-error")
(define-key! "M-g n" "next-error")
(define-key! "M-g M-n" "next-error")
(define-key! "M-g p" "previous-error")
(define-key! "M-g M-p" "previous-error")
(define-buffer-key! "*compilation*" "RET" "compile-goto-error")
(define-buffer-key! "*compilation*" "C-c C-k" "kill-compilation")
(define-command! "grep" (sum on-frame (grep)))
(define-command! "recompile" (sum on-frame (recompile)))
(define-buffer-key! "*compilation*" "g" "recompile")
(define-buffer-key! "*grep*" "g" "recompile")
(define-buffer-key! "*grep*" "RET" "compile-goto-error")
(define-buffer-key! "*grep*" "C-c C-k" "kill-compilation")
(define-buffer-key! "*shell*" "RET" "comint-send-input")
(define-buffer-key! "*shell*" "C-c C-c" "comint-interrupt-subjob")
