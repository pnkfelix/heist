;;; eldoc.fx: what is at point, said in the echo area as point moves, as
;;; Emacs's eldoc and yank's flow analysis say it (docs/fx26-analysis.md,
;;; "On-the-fly information", step 1).
;;;
;;; When the editor has been idle a moment after a key, in an FX-26 buffer:
;;; `name: TYPE` for the name at point, or else for the operator of the
;;; call around point. The type is the one the text declares -- by the
;;; name's binder, its definition, or Fixpt's table of standard names --
;;; so no checker runs. A message a command gave stays; eldoc replaces only
;;; its own (`eldoc-said`, frame.fx), and *Messages* keeps none of it.
;;;
;;;   M-x eldoc-mode   eldoc off, or on (as the editor starts)
;;;
;;; Where the text declares no type, what the CFA found there, if it has
;;; analysed this revision (`flow-eldoc`, which cfa.fx sets): what can
;;; reach the variable, what the call can call.
;;;
;;; In a Scheme buffer, or *s7st*, `scheme-eldoc` says it (scheme.fx and
;;; cfa.fx set it): what the CFA found, else what s7st knows of the name.
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
                    (m-help (load-moduleof "help.fx" m-base m-buffer m-resolve m-syntax m-sexp m-index m-view m-frame m-calls m-process m-files))))
(hide (define kit-lists (load-module "../kit/lists.fx"))
      (import kit-lists member?)
      (define kit-strings (load-module "../kit/strings.fx"))
      (import kit-strings reverse-list->string))

(define eldoc-on (ref bool @ed) (new #t))
"A key was handled since eldoc last looked (main.fx's loop asks)."
(define eldoc-due (ref bool @ed) (new #f))
"Fixpt's standard.rs, once read (\"\": not yet)."
(define standard-text (ref string @ed) (new ""))

"What says what a Scheme name is (scheme.fx sets it): given the frame, the
buffer, its revision and point, the name at point and the operator of the
call around point, a command."
(define scheme-eldoc (ref (listof (subr pure ((actor frame) (actor buffer) int int string string) cmd) acyclic) @ed) (new nil))
"What the CFA found at a place (cfa.fx sets it): given the buffer, its
revision and a position, a note, or \"\"."
(define flow-eldoc (ref (listof (subr (maxeff spin (read @ed)) ((actor buffer) int int) string) acyclic) @ed) (new nil))
(define* flow-note (subr (maxeff spin (read @ed)) ((actor buffer) int int) string)
  (lambda (b rev p) (if (pair? (get flow-eldoc)) ((car (get flow-eldoc)) b rev p) "")))
(define* scheme-buffer? (subr spin (string) bool)
  (lambda (name) (or (string=? (buffer-kind name) "<scheme>") (string=? name "*s7st*"))))

"`s` on one line: each run of white space one space."
(define* one-line (subr spin (string) string)
  (lambda (s)
    (let ((n (string-length s)))
      (letrec ((go (subr spin (int bool (listof char acyclic)) (listof char acyclic))
                 (lambda (i space acc)
                   (cond ((>= i n) acc)
                         ((char-whitespace? (string-ref s i)) (go (+ i 1) #t acc))
                         (else (go (+ i 1) #f (cons (string-ref s i) (if (and space (pair? acc)) (cons #\space acc) acc))))))))
        (reverse-list->string (go 0 #f nil))))))

"What the text `t` declares of the name starting at `at`, as it follows
the name in the echo area: `: TYPE` where it is defined (`define`,
`define*`), bound (a `letrec` or `define-rec` binding) or a parameter (a
`lambda`'s or `plambda`'s); ` = TYPE` where a `define-type` names it;
else \"\"."
(define declared-type (->* (rope int) string)
  (lambda (t at)
    (let* ((name-end (sexp-end t at))
           (opens (extract (scan-at t at) opens))
           (head (lambda ((open int)) (symbol-at t (+ open 1))))
           (next (if (< name-end 0) -1 (skip-space t name-end)))
           (next-end (if (< next 0) -1 (sexp-end t next)))
           (ty (if (< next-end 0) "" (one-line (rope-substring t next next-end))))
           (typed (lambda ((s string)) (if (string=? ty "") "" (string-append s ty))))
           ;; Something after it: what follows the name is a type only if
           ;; a value follows that (`(define x 1)` declares none).
           (more (and (>= next-end 0)
                      (let ((j (skip-space t next-end)))
                        (and (< j (rope-length t)) (not (char-in? (rope-ref t j) ")]")))))))
      (cond ((or (< name-end 0) (null? opens)) "")
            ((member? (head (car opens)) (list "define" "define*") string=?) (if more (typed ": ") ""))
            ((string=? (head (car opens)) "define-type") (typed " = "))
            ;; First in its list: a binding, or a parameter -- in the list
            ;; of them that is the form's item `k` (0 its head).
            ((= (skip-space t (+ (car opens) 1)) at)
             (let* ((up (cdr opens))
                    (item? (lambda ((open int) (k int) (at int))
                             (letrec ((nth (subr spin (sexp-spans int) bool)
                                        (lambda (cs i) (and (pair? cs) (if (= i 0) (= (extract (car cs) start) at)
                                                                           (nth (cdr cs) (- i 1)))))))
                               (nth (children t (+ open 1) (rope-length t)) k)))))
               (cond ((and (pair? up) (string=? (head (car up)) "define-rec")) (typed ": "))
                     ((and (pair? up) (string=? (head (car up)) "vlambda") (item? (car up) 1 (car opens))) (typed ": "))
                     ((and (pair? up) (pair? (cdr up))
                           (let ((form (car (cdr up))))
                             (or (and (member? (head form) (list "lambda" "plambda" "letrec") string=?) (item? form 1 (car up)))
                                 (and (string=? (head form) "rlambda") (item? form 2 (car up))))))
                      (typed ": "))
                     (else ""))))
            (else "")))))

"Where the name `p` is in or just after starts in `t`."
(define* name-start (subr spin (rope int) int)
  (lambda (t p)
    (letrec ((back (subr spin (int) int)
               (lambda (i) (if (and (> i 0) (symbol-char? (rope-ref t (- i 1)))) (back (- i 1)) i))))
      (back p))))

"What eldoc can say of a name: nothing; this; or what a file (read in a
command) declares at a place; or what Fixpt's standard names give it."
(define-type eldoc-answer
  (sumof (none unit) (said string) (in-file (productof (file string) (at int) (name string))) (standard string)))

"What eldoc says of the name at `at` in buffer `current` (state `st`):
its binder's declaration if it is bound in this text (nothing, if that
declares no type); else its definition's, in a buffer or the index; else
a standard name's type."
(define* eldoc-answer-at (subr turn-eff (frame (actor buffer) buffer int) eldoc-answer)
  (lambda (f current st at)
    (let* ((t (extract st text))
           (name (symbol-at t at)))
      (if (or (string=? name "") (member? name special-forms string=?) (member? name type-syntax string=?)
              (char-numeric? (string-ref name 0)))
          (sum none #u)
          (let* ((here (declared-type t at))
                 (bound (letrec ((go (subr spin (references) int)
                                   (lambda (rs) (cond ((null? rs) -1)
                                                      ((and (<= (extract (car rs) start) at) (< at (extract (car rs) end)))
                                                       (extract (car rs) binder-start))
                                                      (else (go (cdr rs)))))))
                          (go (extract (extract st annotation) references)))))
            (cond ((not (string=? here "")) (sum said (string-append name here)))
                  ((>= bound 0)
                   (let ((d (declared-type t bound)))
                     (if (string=? d "") (sum none #u) (sum said (string-append name d)))))
                  (else
                   (tagcase (find-definition f current name)
                     (found pl (let ((d (declared-type (extract (actor-state (extract pl buffer)) text) (extract pl point))))
                                 (if (string=? d "") (sum none #u) (sum said (string-append name d)))))
                     (none u
                       (tagcase (index-lookup name)
                         (found hit (if (string=? (extract hit link) "")
                                        (sum in-file (product (file (extract hit file)) (at (extract hit at)) (name name)))
                                        (sum none #u)))
                         (none u2 (sum standard name))))))))))))

"Message for the frame: eldoc says `s` (\"\": nothing), if the echo area
holds nothing, or only what eldoc said before."
(define* eldoc-show (subr pure (string) (msg frame))
  (lambda (s)
    (lambda ((f frame))
      (let ((echo (extract f echo)))
        (if (or (string=? echo s) (not (or (string=? echo "") (string=? echo (get eldoc-said)))))
            (same f)
            (let ((r (draw (with-echo f s))))
              (reply-with (extract r state) (cons (lambda () (set eldoc-said s)) (extract r cmds)))))))))

"A command: name `name`'s type, as Fixpt's standard.rs gives it, said."
(define* say-standard-type (subr pure ((actor frame) string) cmd)
  (lambda (fr name)
    (lambda ()
      (let* ((s (if (string=? (get standard-text) "")
                    (let* ((got (file-text (string-append fixpt-sources "standard.rs")))
                           (s (if (extract got found) (rope->string (extract got text)) "-")))
                      (begin (set standard-text s) s))
                    (get standard-text)))
             (key (string-append "(\"" name "\", \""))
             (at (string-search s key 0))
             (to (if (< at 0) -1 (string-search s "\")," (+ at (string-length key))))))
        (tell! fr (eldoc-show (if (< to 0) ""
                                  (string-append name ": " (substring s (+ at (string-length key)) to)))))))))

"A command: what `file` declares at `at` of `name`, said."
(define* say-file-type (subr pure ((actor frame) string int string) cmd)
  (lambda (fr file at name)
    (lambda ()
      (let* ((got (file-text file))
             (d (if (extract got found) (declared-type (extract got text) at) "")))
        (tell! fr (eldoc-show (if (string=? d "") "" (string-append name d))))))))

"Message for the frame: the editor idle, so what is at point said -- of
the name at point, or else of the operator of the call around it."
(define* eldoc-now (subr pure ((actor frame)) (msg frame))
  (lambda (fr)
    (lambda ((f frame))
      (let* ((current (extract (selected-window f) buffer))
             (st (actor-state current)))
        (cond
          ((or (not (get eldoc-on)) (tagcase (extract f mini) (none u #f) (else y #t))) (same f))
          ((and (scheme-buffer? (extract st name)) (pair? (get scheme-eldoc)))
           (let* ((t (extract st text))
                  (p (extract st point))
                  (sc (scan-at t p)))
             (if (or (>= (extract sc string-at) 0) (extract sc comment))
                 ((eldoc-show "") f)
                 (reply-with f (list ((car (get scheme-eldoc)) fr current (extract st revision) p (symbol-at t (name-start t p))
                                                               (if (null? (extract sc opens)) ""
                                                                   (symbol-at t (skip-space t (+ 1 (car (extract sc opens))))))))))))
          ((not (fx26-file? (extract st name))) (same f))
          (else
            (let* ((t (extract st text))
                   (p (extract st point))
                   (sc (scan-at t p))
                   (here (if (or (>= (extract sc string-at) 0) (extract sc comment))
                             (sum none #u)
                             (eldoc-answer-at f current st (name-start t p))))
                   (answer (tagcase here
                             (none u (if (or (>= (extract sc string-at) 0) (extract sc comment)
                                             (null? (extract sc opens)))
                                         here
                                         (eldoc-answer-at f current st (skip-space t (+ 1 (car (extract sc opens)))))))
                             (else y here))))
              (tagcase answer
                (none u ((eldoc-show (if (or (>= (extract sc string-at) 0) (extract sc comment)) ""
                                         (flow-note current (extract st revision) p)))
                         f))
                (said s ((eldoc-show s) f))
                (in-file h (reply-with f (list (say-file-type fr (extract h file) (extract h at) (extract h name)))))
                (standard name (reply-with f (list (say-standard-type fr name))))))))))))

"M-x eldoc-mode: eldoc off, or on."
(define* eldoc-mode (subr pure () frame-action)
  (lambda ()
    (lambda ((fr (actor frame)) (f frame))
      (let ((on (not (get eldoc-on))))
        (let ((r (draw (with-echo f (if on "Eldoc mode enabled" "Eldoc mode disabled")))))
          (reply-with (extract r state) (cons (lambda () (set eldoc-on on)) (extract r cmds))))))))

(define-command! "eldoc-mode" (sum on-frame (eldoc-mode)))
(define-doc! "eldoc-mode" "Eldoc off, or on: the type of what is at point, said as point moves.")
