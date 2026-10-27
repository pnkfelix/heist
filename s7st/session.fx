;;; session.fx: what a client of s7st calls.
;;;
;;;   (s7-init!)                 the interpreter made ready: once
;;;   (s7-input-state text)      whether text typed is all there: complete,
;;;                              incomplete (RET should not send it), bad
;;;   (s7-start! text file echo) the text's forms, to run; each value shown,
;;;                              as a REPL does, if `echo`
;;;   (s7-continue! fuel)        at most `fuel` steps run: still running,
;;;                              done (with the last value), or failed
;;;   (s7-take-output!)          what was written since last taken
;;;   (s7-interrupt!)            what runs stopped
;;;   (s7-eval-string! text)     all of that at once: the output, then the
;;;                              last value or the error (for tests)
;;;   (s7-describe name)         what a global is, in a line (for eldoc)
;;;   (set s7-directory dir)     what relative file names are relative to
;;;
;;; There is one interpreter: its globals are FX-26 globals.

"Where the machine is: stopped, when it has nothing to run."
(define s7-machine (ref s7-state @sc) (new (sum s-done s7-unspecified)))

(define-type s7-status (sumof (running unit) (done s7-value) (failed string)))
(define-type s7-input (sumof (complete unit) (incomplete unit) (bad string)))

"What a condition that nothing handled says: an error's message and its
irritants, written; anything else, written."
(define* s7-condition-message (subr s7-eff (s7-value) string)
  (lambda (obj)
    (tagcase obj
      (errobj e (letrec ((go (subr s7-eff (s7-values (listof string acyclic)) (listof string acyclic))
                               (lambda (l acc) (if (null? l) acc (go (cdr l) (cons (s7-show (car l) #t) (cons " " acc)))))))
                  (s7-concat (reverse (the (listof string acyclic)
                                           (go (s7-value->values (extract e irritants)) (list (extract e message))))))))
      (else y (string-append "uncaught exception: " (s7-show y #t))))))

"Whether `text` holds whole data, as a REPL's RET asks."
(define* s7-input-state (subr s7-eff (string) s7-input)
  (lambda (text)
    (tagcase (s7-read-all text "")
      (data d (sum complete #u))
      (stop r (tagcase r
                (incomplete u (sum incomplete #u))
                (bad b (sum bad (extract b message)))
                (else y (sum complete #u)))))))

"The same, in namespace `ns`."
(define* s7-start-in! (subr s7-eff (string string bool s7-ns) (sumof (none unit) (bad string)))
  (lambda (text file echo ns)
    (tagcase (s7-read-all text file)
      (data forms (begin (set s7-console-fresh #t)
                    (set s7-machine (s7-return-state s7-unspecified (list (sum k-top (product (forms forms) (echo echo) (text text) (ns ns))))
                                                          s7-no-dyn))
                    (sum none #u)))
      (stop r (sum bad (tagcase r
                         (incomplete u "the text ends inside a datum")
                         (bad b (string-append (s7-where (product (file file) (start (extract b at)) (end (extract b at))) text)
                                               (extract b message)))
                         (else y "")))))))

"The forms of `text` (from `file`, \"\" if typed) made what the machine
runs next, at top level, each value shown if `echo`. (none), or what is
wrong with it."
(define* s7-start! (subr s7-eff (string string bool) (sumof (none unit) (bad string)))
  (lambda (text file echo) (s7-start-in! text file echo s7-toplevel)))
(define* s7-busy? (subr (read @sc) () bool)
  (lambda () (not (s7-stopped? (get s7-machine)))))

"At most `fuel` steps run."
(define* s7-continue! (subr s7-eff (int) s7-status)
  (lambda (fuel)
    (let ((st (s7-run (get s7-machine) fuel)))
      (begin
        (set s7-machine st)
        (tagcase st
          (s-done v (begin (s7-flush-files!) (sum done v)))
          (s-failed f (begin (s7-flush-files!) (sum failed (s7-condition-message (extract f obj)))))
          (else y (sum running #u)))))))

"What `display` and its kin have written to the console since this was
last asked."
(define* s7-take-output! (subr s7-eff () string)
  (lambda ()
    (tagcase s7-console
      (port p (let ((s (s7-port-text p))) (begin (set (extract p out) nil) s)))
      (else y ""))))

(define* s7-interrupt! (subr s7-eff () unit)
  (lambda () (set s7-machine (sum s-done s7-unspecified))))

"`text` run to its end: what it wrote, then its last value (written) or
`Error: …`."
(define* s7-eval-string! (subr s7-eff (string) string)
  (lambda (text)
    (tagcase (s7-start! text "" #f)
      (bad m (string-append "Error: " m))
      (none u (letrec ((go (subr s7-eff () string)
                         (lambda ()
                           (tagcase (s7-continue! 100000)
                             (running u (go))
                             (done v (string-append (s7-take-output!) (if (s7-shown? v) (s7-show v #t) "")))
                             (failed m (string-append (s7-take-output!) "Error: " m))))))
                (go))))))

"How many arguments a procedure takes, in words."
(define* s7-arity-words (subr spin (int int) string)
  (lambda (min max)
    (cond ((= min max) (string-append (int->string min) (if (= min 1) " argument" " arguments")))
          ((< max 0) (string-append (int->string min) " or more arguments"))
          (else (string-append (int->string min) " to " (int->string max) " arguments")))))
"A closure's parameters, as a call: `(name a b . rest)`, each clause's."
(define* s7-signature (subr s7-eff (string s7-closure) string)
  (lambda (name c)
    (letrec ((params (subr spin (s7-symbols int bool (listof string acyclic)) (listof string acyclic))
               ;; Names `ns`, `left` of them required, then the rest's if `rest`; last first.
               (lambda (ns left rest acc)
                 (cond ((null? ns) acc)
                       ((> left 0) (params (cdr ns) (- left 1) rest (cons (string-append " " (s7-symbol-name (car ns))) acc)))
                       (rest (cons (string-append " . " (s7-symbol-name (car ns))) acc))
                       (else acc))))
             (clauses (subr s7-eff ((listof s7-clause acyclic) (listof string acyclic)) (listof string acyclic))
               (lambda (cs acc)
                 (if (null? cs) acc
                     (let ((l (extract (car cs) info)))
                       (clauses (cdr cs)
                                (cons (string-append "(" name (s7-concat (reverse (params (extract l names) (extract l required) (extract l rest) nil))) ")")
                                      (if (null? acc) acc (cons " | " acc)))))))))
      (s7-concat (reverse (clauses (extract c clauses) nil))))))
"What global `name` is, in a line: a procedure's parameters, a special
form, a macro, or a variable's value; \"\" if it is none of them."
(define* s7-describe (subr s7-eff (string) string)
  (lambda (name)
    (if (string=? name "") ""
        (tagcase (s7-ns-find s7-toplevel (string->symbol name))
          (none u "")
          (found cell
            (tagcase (get (extract cell syntax))
              (special k (string-append name ": a special form"))
              (macro m (string-append name ": a macro"))
              (none u (tagcase (get (extract cell value))
                        (undef u "")
                        (proc c (s7-signature name c))
                        (prim p (string-append name ": " (s7-arity-words (extract p min) (extract p max))))
                        (else v (let ((s (s7-show v #t)))
                                  (string-append name " = " (if (> (string-length s) 60) (string-append (substring s 0 60) "...") s))))))))))))

"The interpreter made ready: the special forms and the procedures written
in FX-26, then the prelude (prelude.fx) run. \"\", or what went wrong."
(define* s7-init! (subr s7-eff () string)
  (lambda ()
    (begin
      (s7-define-specials! s7-special-names)
      (s7-init-prims!)
      (s7-init-tables!)
      (s7-init-libraries!)
      (tagcase (s7-start-in! s7-prelude "prelude.scm" #f s7-builtins)
        (bad m m)
        (none u (letrec ((go (subr s7-eff () string)
                           (lambda ()
                             (tagcase (s7-continue! 1000000)
                               (running u (go))
                               (done v (begin (s7-take-output!) ""))
                               (failed m (string-append "prelude: " m))))))
                  (go)))))))
