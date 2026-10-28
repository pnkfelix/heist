;;; help.fx: the editor describing itself, from its tables of commands
;;; and keys (`commands`, `more-commands`, `keymap`, `more-keys`,
;;; `buffer-keys`) and of what each command does (`command-docs`).
;;;
;;;   M-x apropos, C-h a    the commands whose names have each word typed,
;;;                         their keys, and what they do, in *Apropos*
;;;   M-x help, C-h ?       the help commands, in *Help*
;;;   C-h C-h               (help-for-help)
;;;   C-h f                 a command, its keys, and what it does, in *Help*
;;;   C-h k                 the same, for the command a key sequence runs
;;;   C-h w                 the keys a command is on, in the echo area
;;;   C-h b                 every key bound here, and its command, in *Help*
;;;
;;; FX-26 keeps no docstrings at run time, so what a command does is said
;;; again here, a line for each (`define-doc!`); a file adding commands
;;; adds their lines too.
(lambda ((m-base (load-input-moduleof "base.fx"))
         (m-buffer (load-input-moduleof "buffer.fx" m-base))
         (m-resolve (load-input-moduleof "resolve.fx" m-base m-buffer))
         (m-syntax (load-input-moduleof "syntax.fx" m-base m-buffer m-resolve))
         (m-sexp (load-input-moduleof "sexp.fx" m-base m-buffer m-resolve m-syntax))
         (m-flow (load-input-moduleof "flow.fx" m-base m-buffer m-resolve m-syntax m-sexp))
         (m-index (load-input-moduleof "index.fx" m-base m-buffer m-resolve m-syntax m-sexp m-flow))
         (m-view (load-input-moduleof "view.fx" m-base m-buffer m-resolve m-syntax m-sexp m-flow m-index))
         (m-frame (load-input-moduleof "frame.fx" m-base m-buffer m-resolve m-syntax m-sexp m-flow m-index m-view))
         (m-calls (load-input-moduleof "calls.fx" m-base m-buffer m-resolve m-syntax m-sexp m-flow m-index m-view m-frame))
         (m-process (load-input-moduleof "process.fx" m-base m-buffer m-resolve m-syntax m-sexp m-flow m-index m-view m-frame m-calls))
         (m-files (load-input-moduleof "files.fx" m-base m-buffer m-resolve m-syntax m-sexp m-flow m-index m-view m-frame m-calls m-process)))
(module
(hide (include m-base) (include m-buffer) (include m-resolve) (include m-syntax) (include m-sexp) (include m-flow) (include m-index) (include m-view) (include m-frame) (include m-calls) (include m-process) (include m-files))

(define-type command-doc (productof (name string) (doc string)))
"What each command does, in a line or two, by its name."
(define command-docs (ref (listof command-doc acyclic) @ed) (new nil))

(define* define-doc! (subr (maxeff (read @ed) (write @ed)) (string string) unit)
  (lambda (name doc) (set command-docs (cons (product (name name) (doc doc)) (get command-docs)))))

"What command `name` does, or \"\"."
(define* doc-of (subr (maxeff (read @ed) spin) (string) string)
  (lambda (name)
    (letrec ((go (subr spin ((listof command-doc acyclic)) string)
               (lambda (ds) (cond ((null? ds) "")
                                  ((string=? (extract (car ds) name) name) (extract (car ds) doc))
                                  (else (go (cdr ds)))))))
      (go (get command-docs)))))

"Every command's name."
(define command-names (->* () strings)
  (lambda ()
    (letrec ((go (subr spin ((listof named acyclic)) strings)
               (lambda (cs) (if (null? cs) nil (cons (extract (car cs) name) (go (cdr cs)))))))
      (go (append (commands) (get more-commands))))))

"`ss` sorted, as `string<?` orders them."
(define* sorted (subr spin (strings) strings)
  (lambda (ss)
    (letrec ((insert (subr spin (string strings) strings)
               (lambda (s ss) (if (or (null? ss) (string<? s (car ss))) (cons s ss) (cons (car ss) (insert s (cdr ss)))))))
      (if (null? ss) nil (insert (car ss) (sorted (cdr ss)))))))

"The words of `s`, split at its spaces."
(define* words (subr spin (string) strings)
  (lambda (s)
    (let ((i (string-search s " " 0)))
      (cond ((< i 0) (if (string=? s "") nil (list s)))
            ((= i 0) (words (substring s 1 (string-length s))))
            (else (cons (substring s 0 i) (words (substring s (+ i 1) (string-length s)))))))))

"The keys command `name` is on: everywhere, then in buffers of one name
or kind (\"RET (in *grep*)\")."
(define* keys-of (subr (maxeff (read @ed) spin) (string) strings)
  (lambda (name)
    (letrec ((global (subr spin ((listof (productof (keys string) (command string)) acyclic)) strings)
               (lambda (m) (cond ((null? m) nil)
                                 ((string=? (extract (car m) command) name) (cons (extract (car m) keys) (global (cdr m))))
                                 (else (global (cdr m))))))
             (local (subr spin ((listof (productof (buffer string) (keys string) (command string)) acyclic)) strings)
               (lambda (m) (cond ((null? m) nil)
                                 ((string=? (extract (car m) command) name)
                                  (cons (string-append (extract (car m) keys) " (in " (extract (car m) buffer) ")")
                                        (local (cdr m))))
                                 (else (local (cdr m)))))))
      (append (global keymap) (append (global (get more-keys)) (local (get buffer-keys)))))))

"`ss` joined, `sep` between."
(define* joined (subr spin (strings string) string)
  (lambda (ss sep)
    (cond ((null? ss) "")
          ((null? (cdr ss)) (car ss))
          (else (string-append (car ss) (string-append sep (joined (cdr ss) sep)))))))

"`s` with spaces after it to `n` columns (32 at most), and one at least."
(define* padded (subr pure (string int) string)
  (lambda (s n)
    (let ((l (string-length s)))
      (if (< l n) (string-append s (substring "                                " 0 (- n l))) (string-append s " ")))))

"Buffer `name` given text `text` and shown elsewhere, point at its start:
made, or its text replaced."
(define* show-help (subr turn-eff ((actor frame) frame string string) (reply frame))
  (lambda (fr f name text)
    (let ((t (string->rope text)))
      (tagcase (find-buffer (extract f buffers) name)
        (found info (let ((r (display-buffer fr f (extract info actor))))
                      (reply-with (extract r state) (cons (tell (extract info actor) (replace-text t)) (extract r cmds)))))
        (none u (let ((b (spawn-actor name (new-buffer name "" t))))
                  (reply-with f (list (lambda () (tell! fr (buffer-made-elsewhere fr name b)))))))))))

"What *Help* says of command `name` after its first line: its keys, and
what it does."
(define* description (subr (maxeff (read @ed) spin) (string) string)
  (lambda (name)
    (let ((ks (keys-of name)) (doc (doc-of name)))
      (string-append (cond ((string=? name "self-insert-command") "It is on the characters that are not bound.\n")
                           ((null? ks) (string-append "It is on no key: M-x " name " runs it.\n"))
                           (else (string-append "It is on " (joined ks ", ") ".\n")))
                     "\n" (if (string=? doc "") "Not documented." doc) "\n"))))

"Whether `name` has each of `ws` in it."
(define* has-each? (subr spin (string strings) bool)
  (lambda (name ws)
    (or (null? ws) (and (>= (string-search name (car ws) 0) 0) (has-each? name (cdr ws))))))

"What *Apropos* says of commands `ns`: each name, its keys, and what it does."
(define* apropos-text (subr (maxeff (read @ed) spin) (strings) string)
  (lambda (ns)
    (if (null? ns)
        ""
        (let ((doc (doc-of (car ns))))
          (string-append (padded (car ns) 28) (joined (keys-of (car ns)) ", ") "\n"
                         (if (string=? doc "") "" (string-append "  " doc "\n"))
                         (apropos-text (cdr ns)))))))

"M-x apropos, C-h a: the commands whose names have each word typed in
them, sorted, each with its keys and what it does, in *Apropos*."
(define* apropos (subr pure () frame-action)
  (lambda ()
    (lambda ((fr (actor frame)) (f frame))
      (read-string f "Search for a command (word or list of words): " ""
                   (lambda ((fr (actor frame)) (f frame) (typed string))
                     (let* ((ws (words typed))
                            (found (letrec ((go (subr spin (strings) strings)
                                                  (lambda (ns)
                                                    (cond ((null? ns) nil)
                                                          ((has-each? (car ns) ws) (cons (car ns) (go (cdr ns))))
                                                          (else (go (cdr ns)))))))
                                     (go (sorted (command-names))))))
                       (cond ((null? ws) (draw (with-echo f "No words to search for")))
                             ((null? found) (draw (with-echo f (string-append "No command matches " typed))))
                             (else (show-help fr f "*Apropos*" (apropos-text found))))))))))

"C-h f: a command read, and described in *Help*."
(define* describe-function (subr pure () frame-action)
  (lambda ()
    (lambda ((fr (actor frame)) (f frame))
      (read-completing f "Describe command: " "" (sum names (command-names))
                       (lambda ((fr (actor frame)) (f frame) (name string))
                         (tagcase (command-named name)
                           (found a (show-help fr f "*Help*" (string-append name " is a command.\n" (description name))))
                           (none u (draw (with-echo f (string-append "No command named " name))))))))))

"C-h k: the keys typed next read (`dispatch-key` reads them), then
described by this."
(define* describe-key (subr pure () frame-action)
  (lambda ()
    (lambda ((fr (actor frame)) (f frame)) (draw (with-echo (with-prefix f (list 'C-h #\k)) "Describe key: ")))))

(define key-describer-set unit (set key-describer
     (lambda ((ks string) (name string))
       (lambda ((fr (actor frame)) (f frame))
         (if (string=? name "")
             (draw (with-echo f (string-append ks " is undefined")))
             (show-help fr f "*Help*" (string-append ks " runs the command " name ".\n" (description name))))))))

"C-h w: a command read, and the keys it is on said."
(define* where-is (subr pure () frame-action)
  (lambda ()
    (lambda ((fr (actor frame)) (f frame))
      (read-completing f "Where is command: " "" (sum names (command-names))
                       (lambda ((fr (actor frame)) (f frame) (name string))
                         (let ((ks (keys-of name)))
                           (draw (with-echo f (if (null? ks)
                                                  (string-append name " is not on any key")
                                                  (string-append name " is on " (joined ks ", ")))))))))))

"C-h b: the keys bound in the selected buffer, and then everywhere, with
their commands, in *Help*."
(define* describe-bindings (subr pure () frame-action)
  (lambda ()
    (lambda ((fr (actor frame)) (f frame))
      (let* ((bname (extract (actor-state (extract (selected-window f) buffer)) name))
             (line (lambda ((ks string) (name string)) (string-append (padded ks 16) name "\n")))
             (here (letrec ((go (subr spin ((listof (productof (buffer string) (keys string) (command string)) acyclic)) string)
                              (lambda (m)
                                (cond ((null? m) "")
                                      ((or (string=? (extract (car m) buffer) bname)
                                           (string=? (extract (car m) buffer) (buffer-kind bname)))
                                       (string-append (line (extract (car m) keys) (extract (car m) command)) (go (cdr m))))
                                      (else (go (cdr m)))))))
                     (go (get buffer-keys))))
             (global (letrec ((go (subr spin ((listof (productof (keys string) (command string)) acyclic)) string)
                                (lambda (m) (if (null? m) ""
                                                (string-append (line (extract (car m) keys) (extract (car m) command))
                                                               (go (cdr m)))))))
                       (string-append (go keymap) (go (reverse (get more-keys)))))))
        (show-help fr f "*Help*"
                   (string-append (if (string=? here "") ""
                                      (string-append "In " bname ":\n" (line "key" "binding") here "\n"))
                                  "Everywhere:\n" (line "key" "binding") global))))))

"M-x help, C-h ?, C-h C-h: the help commands, in *Help*."
(define* help-for-help (subr pure () frame-action)
  (lambda ()
    (lambda ((fr (actor frame)) (f frame))
      (show-help fr f "*Help*"
                 (string-append
                  "Help: C-h then one of these keys.\n\n"
                  "a  apropos: the commands whose names have the words typed\n"
                  "b  describe-bindings: the keys bound here, and their commands\n"
                  "f  describe-function: a command, its keys, and what it does\n"
                  "k  describe-key: the command a key sequence runs\n"
                  "w  where-is: the keys a command is on\n"
                  "?  help-for-help: this\n\n"
                  "M-x runs a command by its name; TAB completes it.\n"
                  "C-g quits a prefix, or the minibuffer.\n")))))

(hide (define help-reg-1 (define-command! "apropos" (sum on-frame (apropos)))))
(hide (define help-reg-2 (define-command! "apropos-command" (sum on-frame (apropos)))))
(hide (define help-reg-3 (define-command! "describe-function" (sum on-frame (describe-function)))))
(hide (define help-reg-4 (define-command! "describe-command" (sum on-frame (describe-function)))))
(hide (define help-reg-5 (define-command! "describe-key" (sum on-frame (describe-key)))))
(hide (define help-reg-6 (define-command! "where-is" (sum on-frame (where-is)))))
(hide (define help-reg-7 (define-command! "describe-bindings" (sum on-frame (describe-bindings)))))
(hide (define help-reg-8 (define-command! "help-for-help" (sum on-frame (help-for-help)))))
(hide (define help-reg-9 (define-command! "help" (sum on-frame (help-for-help)))))
(hide (define help-reg-10 (define-key! "C-h a" "apropos-command")))
(hide (define help-reg-11 (define-key! "C-h f" "describe-function")))
(hide (define help-reg-12 (define-key! "C-h k" "describe-key")))
(hide (define help-reg-13 (define-key! "C-h w" "where-is")))
(hide (define help-reg-14 (define-key! "C-h b" "describe-bindings")))
(hide (define help-reg-15 (define-key! "C-h ?" "help-for-help")))
(hide (define help-reg-16 (define-key! "C-h C-h" "help-for-help")))
(hide (define help-reg-17 (define-buffer-key! "*Help*" "q" "delete-window")))
(hide (define help-reg-18 (define-buffer-key! "*Apropos*" "q" "delete-window")))

;;; ------------------------------------------------------------ what each command does

(hide (define help-reg-19 (define-doc! "forward-char" "Point moved a character forward.")))
(hide (define help-reg-20 (define-doc! "backward-char" "Point moved a character back.")))
(hide (define help-reg-21 (define-doc! "next-line" "Point moved to the next line, its column kept where it can be.")))
(hide (define help-reg-22 (define-doc! "previous-line" "Point moved to the line before, its column kept where it can be.")))
(hide (define help-reg-23 (define-doc! "move-beginning-of-line" "Point moved to the start of its line.")))
(hide (define help-reg-24 (define-doc! "move-end-of-line" "Point moved to the end of its line.")))
(hide (define help-reg-25 (define-doc! "forward-word" "Point moved past the end of the next word.")))
(hide (define help-reg-26 (define-doc! "backward-word" "Point moved to the start of the word before.")))
(hide (define help-reg-27 (define-doc! "beginning-of-buffer" "Point moved to the start of the buffer.")))
(hide (define help-reg-28 (define-doc! "end-of-buffer" "Point moved to the end of the buffer.")))
(hide (define help-reg-29 (define-doc! "scroll-up-command" "Point moved a window's height of lines down.")))
(hide (define help-reg-30 (define-doc! "scroll-down-command" "Point moved a window's height of lines up.")))
(hide (define help-reg-31 (define-doc! "delete-backward-char" "The character before point deleted.")))
(hide (define help-reg-32 (define-doc! "delete-char" "The character after point deleted.")))
(hide (define help-reg-33 (define-doc! "newline" "A line break inserted, and the new line indented in FX-26 buffers.")))
(hide (define help-reg-34 (define-doc! "indent-for-tab-command" "The line indented, in FX-26 buffers, as its nesting says.")))
(hide (define help-reg-35 (define-doc! "self-insert-command" "The character typed inserted at point.")))
(hide (define help-reg-36 (define-doc! "set-mark-command" "The mark set at point.")))
(hide (define help-reg-37 (define-doc! "exchange-point-and-mark" "Point and the mark swapped.")))
(hide (define help-reg-38 (define-doc! "kill-region" "The text between point and the mark killed: deleted, and kept to yank.")))
(hide (define help-reg-39 (define-doc! "kill-ring-save" "The text between point and the mark kept to yank, not deleted.")))
(hide (define help-reg-40 (define-doc! "kill-line" "The rest of the line killed, or the line break if nothing is left.")))
(hide (define help-reg-41 (define-doc! "yank" "The text last killed inserted at point.")))
(hide (define help-reg-42 (define-doc! "undo" "The last change undone; again, the one before it.")))
(hide (define help-reg-43 (define-doc! "keyboard-quit" "What is going on stopped: a prefix, the mark, the minibuffer.")))
(hide (define help-reg-44 (define-doc! "save-buffer" "The selected buffer written to its file.")))
(hide (define help-reg-45 (define-doc! "fail-on-purpose" "A command that fails, to show the editor carries on after one.")))
(hide (define help-reg-46 (define-doc! "isearch-forward" "Text searched for forward, as it is typed.")))
(hide (define help-reg-47 (define-doc! "isearch-backward" "Text searched for backward, as it is typed.")))
(hide (define help-reg-48 (define-doc! "xref-find-definitions" "The definition of the name at point visited.")))
(hide (define help-reg-49 (define-doc! "xref-go-back" "Back to where the last M-. was typed.")))
(hide (define help-reg-50 (define-doc! "xref-find-references" "The uses of the name at point marked; M-n and M-p visit them.")))
(hide (define help-reg-51 (define-doc! "next-use" "Point moved to the next use marked.")))
(hide (define help-reg-52 (define-doc! "previous-use" "Point moved to the use marked before.")))
(hide (define help-reg-53 (define-doc! "find-file" "A file visited, or a directory listed; TAB completes the name.")))
(hide (define help-reg-54 (define-doc! "switch-to-buffer" "A buffer shown in the selected window, made if there is none of its name.")))
(hide (define help-reg-55 (define-doc! "list-buffers" "*Buffer List*: each buffer, whether modified, its size and its file.")))
(hide (define help-reg-56 (define-doc! "split-window-below" "The selected window split in two, one above the other.")))
(hide (define help-reg-57 (define-doc! "other-window" "The next window selected.")))
(hide (define help-reg-58 (define-doc! "delete-other-windows" "The selected window made the only one.")))
(hide (define help-reg-59 (define-doc! "delete-window" "The selected window removed.")))
(hide (define help-reg-60 (define-doc! "execute-extended-command" "A command read by its name, and run; TAB completes the name.")))
(hide (define help-reg-61 (define-doc! "save-buffers-kill-terminal" "The editor ended, after asking if a file has changes not saved.")))
(hide (define help-reg-62 (define-doc! "compile" "A shell command run, its output in *compilation*.")))
(hide (define help-reg-63 (define-doc! "recompile" "The last compilation's command run again, where it ran.")))
(hide (define help-reg-64 (define-doc! "grep" "A grep command run, its output in *grep*.")))
(hide (define help-reg-65 (define-doc! "next-error" "The next place the compilation or grep output names, visited.")))
(hide (define help-reg-66 (define-doc! "previous-error" "The place before, that the compilation or grep output names, visited.")))
(hide (define help-reg-67 (define-doc! "compile-goto-error" "The place named on this line of compilation or grep output, visited.")))
(hide (define help-reg-68 (define-doc! "kill-compilation" "The program running in this buffer interrupted.")))
(hide (define help-reg-69 (define-doc! "shell-command" "A shell command run, its output in *Shell Command Output*.")))
(hide (define help-reg-70 (define-doc! "shell" "A shell, in *shell*.")))
(hide (define help-reg-71 (define-doc! "comint-send-input" "The line typed in *shell* sent to the shell.")))
(hide (define help-reg-72 (define-doc! "comint-interrupt-subjob" "What the shell is running interrupted.")))
(hide (define help-reg-73 (define-doc! "dired" "A directory read, and its listing visited.")))
(hide (define help-reg-74 (define-doc! "list-directory" "A directory's names (ls -F) shown in *Directory*.")))
(hide (define help-reg-75 (define-doc! "dired-find-file" "The file or directory on this line of a listing visited.")))
(hide (define help-reg-76 (define-doc! "Buffer-menu-this-window" "The buffer on this line of *Buffer List* shown.")))
(hide (define help-reg-77 (define-doc! "revert-buffer" "The buffer's file, or directory, read again.")))
(hide (define help-reg-78 (define-doc! "save-some-buffers" "Each file changed and not saved, saved if you say so.")))
(hide (define help-reg-79 (define-doc! "paredit-mode" "Paredit turned on or off: parentheses and quotes kept balanced.")))
(hide (define help-reg-80 (define-doc! "forward-sexp" "Point moved past the next expression.")))
(hide (define help-reg-81 (define-doc! "backward-sexp" "Point moved to the start of the expression before.")))
(hide (define help-reg-82 (define-doc! "backward-up-list" "Point moved to the start of the list around it.")))
(hide (define help-reg-83 (define-doc! "down-list" "Point moved into the next list.")))
(hide (define help-reg-84 (define-doc! "kill-sexp" "The next expression killed.")))
(hide (define help-reg-85 (define-doc! "paredit-open-round" "A pair of parentheses inserted, point between them.")))
(hide (define help-reg-86 (define-doc! "paredit-close-round" "Point moved past the closing parenthesis of its list.")))
(hide (define help-reg-87 (define-doc! "paredit-doublequote" "A pair of double quotes inserted, or point moved past the closing one.")))
(hide (define help-reg-88 (define-doc! "paredit-backward-delete" "The character before point deleted, unless that unbalances.")))
(hide (define help-reg-89 (define-doc! "paredit-forward-delete" "The character after point deleted, unless that unbalances.")))
(hide (define help-reg-90 (define-doc! "paredit-kill" "The rest of the line killed, keeping lists balanced.")))
(hide (define help-reg-91 (define-doc! "paredit-forward-slurp-sexp" "The expression after the list around point brought into it.")))
(hide (define help-reg-92 (define-doc! "paredit-forward-barf-sexp" "The last expression of the list around point moved out of it.")))
(hide (define help-reg-93 (define-doc! "paredit-splice-sexp" "The list around point removed, its contents kept.")))
(hide (define help-reg-94 (define-doc! "paredit-raise-sexp" "The list around point replaced by the expression at point.")))
(hide (define help-reg-95 (define-doc! "paredit-wrap-round" "The expression at point wrapped in parentheses.")))
(hide (define help-reg-96 (define-doc! "kill-word" "The rest of the word at point killed.")))
(hide (define help-reg-97 (define-doc! "backward-kill-word" "The word before point killed.")))
(hide (define help-reg-98 (define-doc! "open-line" "A line break inserted after point.")))
(hide (define help-reg-99 (define-doc! "goto-line" "A line number read, and point moved to that line.")))
(hide (define help-reg-100 (define-doc! "write-file" "The buffer written to a file read, and visiting it from then on.")))
(hide (define help-reg-101 (define-doc! "kill-buffer" "A buffer removed.")))
(hide (define help-reg-102 (define-doc! "flow-callees" "What the definition at point calls, in *xref*.")))
(hide (define help-reg-103 (define-doc! "flow-callers" "What calls the definition at point, in *xref*.")))
(hide (define help-reg-104 (define-doc! "xref-visit" "The place on this line of *xref* visited.")))
(hide (define help-reg-105 (define-doc! "type-at-point" "The type of the expression at point, from Fixpt's checker.")))
(hide (define help-reg-106 (define-doc! "apropos" "The commands whose names have each word typed, their keys and what they do.")))
(hide (define help-reg-107 (define-doc! "apropos-command" "The commands whose names have each word typed, their keys and what they do.")))
(hide (define help-reg-108 (define-doc! "describe-function" "A command, its keys, and what it does, in *Help*.")))
(hide (define help-reg-109 (define-doc! "describe-command" "A command, its keys, and what it does, in *Help*.")))
(hide (define help-reg-110 (define-doc! "describe-key" "The command a key sequence runs, its keys, and what it does, in *Help*.")))
(hide (define help-reg-111 (define-doc! "where-is" "The keys a command is on, in the echo area.")))
(hide (define help-reg-112 (define-doc! "describe-bindings" "The keys bound in this buffer and everywhere, and their commands.")))
(hide (define help-reg-113 (define-doc! "help-for-help" "The help commands, in *Help*.")))
(hide (define help-reg-114 (define-doc! "help" "The help commands, in *Help*.")))
))
