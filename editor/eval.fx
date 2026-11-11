;;; eval.fx: FX-26 run inside the editor, as Emacs's `eval-expression`
;;; runs Lisp (docs/fx26-for-yank.md, R4), by Fixpt's `stage` and sessions
;;; (fixpt/docs/fx26.md, "Staging code" and "Sessions").
;;;
;;;   M-:, M-x eval-expression   a form read in the minibuffer and run;
;;;                              what it gives in the echo area
;;;
;;; Every form runs in one session (`eval-session`), so a definition stays
;;; for the forms after it. A form sees the standard names and those of
;;; `eval-api` alone, nothing else of the editor.
;;;
;;; User code runs in a frame's turn, at `turn-eff`: it reads and
;;; allocates but writes nothing, so a fault in it (`car` of nil, `error`)
;;; is a failing turn, said in the echo area, and the editor goes on. What
;;; it wants done it gives back as an `ed-action`, which the editor does:
;;; a message, text inserted, a command or a key defined. A command it
;;; defines is a procedure giving an action, run in a turn in the same way.
;;;
;;; Checking makes code (the `stage` effect), so it runs in a command after
;;; the turn that read the form. A form's type must be given to check it:
;;; it is checked as an `ed-action`, then as a `unit`, `string`, `int`,
;;; `bool` and `char`, until one is accepted, and its value shown as that.
;;; A form of another type is run for what it does, and its type shown. A
;;; definition's initializer is run once in a turn before it is committed,
;;; so that a fault in it is a turn's; but for a `lambda`, which runs
;;; nothing. Not yet: stopping a form that does not end (C-g is read
;;; between turns), and anything of the editor's state for user code to
;;; read.
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
(hide (define kit-strings (load-module "../kit/strings.fx"))
      (import kit-strings written-string))

"What user code may do: what a turn may (`turn-eff`, core.fx), written
out, as `session-check` takes it."
(define-effect user-eff (maxeff spin nondet (read @globals) (read @ed) (alloc @ed)))

"What user code asks the editor to do."
(define-type ed-action
  (sumof (nothing unit)
         (message string)
         (insert string)
         (seq (listof ed-action acyclic))
         (command (productof (name string) (body (subr user-eff () ed-action))))
         (key (productof (keys string) (command string)))))

"What user code sees, beside the standard names."
(define-type eval-api-type
  (moduleof (val nothing ed-action)
            (val message (subr pure (string) ed-action))
            (val insert (subr pure (string) ed-action))
            (val then (subr pure (ed-action ed-action) ed-action))
            (val define-command (subr pure (string (subr user-eff () ed-action)) ed-action))
            (val define-key (subr pure (string string) ed-action))))
(define eval-api eval-api-type
  (module
    (define nothing ed-action (sum nothing #u))
    ;; `s` in the echo area.
    (define message (subr pure (string) ed-action) (lambda ((s string)) (sum message s)))
    ;; `s` inserted at point, in the selected window's buffer.
    (define insert (subr pure (string) ed-action) (lambda ((s string)) (sum insert s)))
    ;; `a`, then `b`.
    (define then (subr pure (ed-action ed-action) ed-action)
      (lambda ((a ed-action) (b ed-action)) (sum seq (the (listof ed-action acyclic) (list a b)))))
    ;; A command `name`, for M-x and keys, doing what `body` gives.
    (define define-command (subr pure (string (subr user-eff () ed-action)) ed-action)
      (lambda ((name string) (body (subr user-eff () ed-action))) (sum command (product (name name) (body body)))))
    ;; Keys `ks` (as `kbd` reads them) bound to the command `name`.
    (define define-key (subr pure (string string) ed-action)
      (lambda ((ks string) (name string)) (sum key (product (keys ks) (command name)))))))

(define eval-session (sessionof eval-api-type @ed) (make-session eval-api))

;;; ------------------------------------------------------------ doing actions

"Action `a` done in the frame's turn: the frame, and the commands after."
(define perform (subr turn-eff ((actor frame) frame ed-action) (reply frame))
  (lambda (fr f a)
    (tagcase a
      (nothing u (draw f))
      (message s (draw (with-echo f s)))
      (insert s (reply-with f (list (tell (extract (selected-window f) buffer) (in-buffer fr (insert-string s))))))
      (seq as (letrec ((go (subr turn-eff (frame cmds (listof ed-action acyclic)) (reply frame))
                             (lambda (f cs as)
                               (if (null? as)
                                   (let ((r (draw f))) (reply-with (extract r state) (append cs (extract r cmds))))
                                   (let ((r (perform fr f (car as))))
                                     (go (extract r state) (append cs (extract r cmds)) (cdr as)))))))
                (go f nil as)))
      (command c (reply-with f (list (lambda () (define-command! (extract c name) (sum on-frame (user-command (extract c body))))))))
      (key k (reply-with f (list (lambda () (define-key! (extract k keys) (extract k command)))))))))

"A command user code defined: `body` run, and what it gives done, in a
turn of the frame's after the one that ran the command, so that a fault
in it loses only that turn (not M-x's minibuffer closing)."
(define user-command (subr pure ((subr user-eff () ed-action)) frame-action)
  (lambda (body)
    (lambda ((fr (actor frame)) (f frame))
      (reply-with f (list (tell fr (lambda ((f frame)) (perform fr f (body)))))))))

;;; ------------------------------------------------------------ checking

"A form checked: what to do in the frame's turn; or refused, because it
is of another type (which), or for another reason (why)."
(define-type checked (sumof (run frame-action) (other string) (refused string)))

(define type-mismatch string " is expected here, and this is a ")

"A refusal: of another type, if it says so, else as it says."
(define* refusal (subr pure (stage-failure) checked)
  (lambda (why)
    (let* ((m (extract why message))
           (k (string-search m type-mismatch 0)))
      (if (< k 0)
          (sum refused m)
          (sum other (substring m (+ k (string-length type-mismatch)) (string-length m)))))))

"Definition `d` committed: what the echo area says."
(define* commit! (subr cmd-eff ((actor frame) (pending user-eff @ed)) unit)
  (lambda (fr d)
    (tagcase (session-commit! eval-session d (sum rerun #u))
      (defined n (tell! fr (echo n)))
      (failed why (tell! fr (echo (extract why message)))))))

"The initializer of definition `code`, if it runs something: not a
`lambda`. `(define name init)` or `(define name type init)`."
(define* initializer (subr pure (datum) (sumof (runs datum) (none unit)))
  (lambda (code)
    (letrec ((last (subr pure (datum) datum)
               (lambda (x) (if (and (pair? x) (pair? (cdr x))) (last (cdr x)) (if (pair? x) (car x) x)))))
      (let ((init (last code)))
        (if (and (pair? init) (symbol? (car init))
                 (or (string=? (symbol->string (car init)) "lambda")
                     (string=? (symbol->string (car init)) "plambda")))
            (sum none #u)
            (sum runs init))))))

"`(begin x #u)`: `x` run at `unit`, whatever its type."
(define* run-for-effect (subr pure (datum) datum)
  (lambda (x) (the datum (list (the datum 'begin) x (the datum '#u)))))

"Form `code` checked as an `ed-action`; a definition, whatever its type."
(define* check-action (subr cmd-eff (datum) checked)
  (lambda (code)
    (session-check eval-session user-eff ed-action code
      (c (tagcase c
           (expression p (sum run (lambda ((fr (actor frame)) (f frame)) (perform fr f (p)))))
           (definition d
             (let ((commit (lambda ((fr (actor frame)) (f frame)) (reply-with f (list (lambda () (commit! fr d)))))))
               (tagcase (initializer code)
                 (none u (sum run commit))
                 (runs init
                   (session-check eval-session user-eff unit (run-for-effect init)
                     (c (tagcase c
                          (expression p (sum run (lambda ((fr (actor frame)) (f frame)) (begin (p) (commit fr f)))))
                          (definition d2 (sum run commit))))
                     (why (refusal why)))))))))
      (why (refusal why)))))

"Form `code` checked as a `unit`: run, nothing said."
(define* check-unit (subr cmd-eff (datum) checked)
  (lambda (code)
    (session-check eval-session user-eff unit code
      (c (tagcase c
           (expression p (sum run (lambda ((fr (actor frame)) (f frame)) (begin (p) (draw f)))))
           (definition d (sum refused "a definition"))))
      (why (refusal why)))))

"Form `code` checked as a `string`: its written form said."
(define* check-string (subr cmd-eff (datum) checked)
  (lambda (code)
    (session-check eval-session user-eff string code
      (c (tagcase c
           (expression p (sum run (lambda ((fr (actor frame)) (f frame)) (draw (with-echo f (written-string (p)))))))
           (definition d (sum refused "a definition"))))
      (why (refusal why)))))

"Form `code` checked as an `int`."
(define* check-int (subr cmd-eff (datum) checked)
  (lambda (code)
    (session-check eval-session user-eff int code
      (c (tagcase c
           (expression p (sum run (lambda ((fr (actor frame)) (f frame)) (draw (with-echo f (int->string (p)))))))
           (definition d (sum refused "a definition"))))
      (why (refusal why)))))

"Form `code` checked as a `bool`."
(define* check-bool (subr cmd-eff (datum) checked)
  (lambda (code)
    (session-check eval-session user-eff bool code
      (c (tagcase c
           (expression p (sum run (lambda ((fr (actor frame)) (f frame)) (draw (with-echo f (if (p) "#t" "#f"))))))
           (definition d (sum refused "a definition"))))
      (why (refusal why)))))

"Form `code` checked as a `char`."
(define* check-char (subr cmd-eff (datum) checked)
  (lambda (code)
    (session-check eval-session user-eff char code
      (c (tagcase c
           (expression p (sum run (lambda ((fr (actor frame)) (f frame))
                                    (draw (with-echo f (string-append "#\\" (char->string (p))))))))
           (definition d (sum refused "a definition"))))
      (why (refusal why)))))

"Form `code`, of type `type`, run for what it does, its type said."
(define* check-other (subr cmd-eff (datum string) checked)
  (lambda (code type)
    (session-check eval-session user-eff unit (run-for-effect code)
      (c (tagcase c
           (expression p (sum run (lambda ((fr (actor frame)) (f frame))
                                    (begin (p) (draw (with-echo f (string-append "#<a " type ">")))))))
           (definition d (sum refused "a definition"))))
      ;; Refused at `unit` too: the form's own fault, as the checker says it.
      (why (sum refused (extract why message))))))

"`first`, unless it is of another type: then `next` of that type."
(define* or-else (subr cmd-eff (checked (subr cmd-eff (string) checked)) checked)
  (lambda (first next)
    (tagcase first
      (other type (next type))
      (run a first)
      (refused m first))))

"Form `code` checked at each type in turn."
(define* check-form (subr cmd-eff (datum) checked)
  (lambda (code)
    (or-else (check-action code)
      (lambda ((t string))
        (or-else (check-unit code)
          (lambda ((t string))
            (or-else (check-string code)
              (lambda ((t string))
                (or-else (check-int code)
                  (lambda ((t string))
                    (or-else (check-bool code)
                      (lambda ((t string))
                        (or-else (check-char code)
                          (lambda ((t string)) (check-other code t)))))))))))))))

;;; ------------------------------------------------------------ the command

"Text `text` read as one FX-26 form."
(define* read-form (subr (maxeff reader-eff spin) (string) (sumof (form datum) (bad string)))
  (lambda (text)
    (let ((st (eager-feed (eager-feed-string (eager-start-fx26) text) #\newline)))
      (case (eager-status st)
        ((complete)
         (let ((ds (eager-state-data st)))
           (cond ((null? ds) (sum bad "No form"))
                 ((pair? (cdr ds)) (sum bad "One form, please"))
                 (else (sum form (car ds))))))
        ((error) (sum bad (eager-state-message st)))
        (else (sum bad "End of file during parsing"))))))

"Text `text` read, checked, and run in the frame's turn."
(define* eval-text! (subr cmd-eff ((actor frame) string) unit)
  (lambda (fr text)
    (tagcase (read-form text)
      (bad m (tell! fr (echo m)))
      (form code
        (tagcase (check-form code)
          (run a (tell! fr (lambda ((f frame)) (a fr f))))
          (other type (tell! fr (echo type)))
          (refused m (tell! fr (echo m))))))))

"M-:: a form read in the minibuffer, run, and what it gives in the echo
area."
(define* eval-expression (subr pure () frame-action)
  (lambda ()
    (lambda ((fr (actor frame)) (f frame))
      (read-string f "Eval: " ""
                   (lambda ((fr (actor frame)) (f frame) (text string))
                     (let ((r (draw f)))
                       (reply-with (extract r state) (append (extract r cmds) (list (lambda () (eval-text! fr text)))))))))))

(define-command! "eval-expression" (sum on-frame (eval-expression)))
(define-key! "M-:" "eval-expression")
(define-doc! "eval-expression" "An FX-26 form read in the minibuffer and run in the editor; its value in the echo area.")
