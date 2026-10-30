;;; base.fx: what the editor's files share -- the modules they use, and
;;; the effect of what commands do outside. The editor is several files,
;;; each a module made once by editor.fx (`bin/heist-edit`) from the
;;; modules of those before it, in the order `program` lists them:
;;;   base.fx buffer.fx … frame.fx calls.fx process.fx main.fx
;;; This one takes none, but has state, so it too is made once.
(module-parameters ())

;; What Fixpt's own reader does to its regions: it keeps its state there,
;; and leaves a form it cannot read by an escape.
(define-effect reader-eff
  (maxeff (read @s) (write @s) (alloc @s) (read @m) (write @m) (alloc @m)
          (read @c) (write @c) (alloc @c) (read @e) (goto @e) (comefrom @e)))
(define-effect world (maxeff (io stdout) (io terminal) (io fs-read) (io fs-write) (io process) reader-eff
                             (read @pf) (alloc @pf)))                ; the files of a program, listed
(define core ((proj (load-module "core.fx") @ed world)))
(import core spawn-actor set-class! interactive display idle tell tell-latest tell! start! activity-running? abort-activity! run-turns!
        turns-waiting? interactive-waiting? actor-state actor-name same reply-with
        on-turn-failure! turns-run (type actor msg reply cmd cmds) (effect turn-eff cmd-eff))
(define rope-m (load-module "rope.fx"))
(import rope-m empty-rope string->rope rope->string rope-length rope-insert rope-delete rope-ref
        rope-substring rope-line-start rope-line-end rope-line-of rope-line-count (type rope))
(define keys-m (load-module "keys.fx"))
(import keys-m read-key key->string keys->string kbd key=? meta-key (type key keys byte-source))
(define regexp-m (load-module "regexp.fx"))
(import regexp-m make-regexp regexp-search regexp-match-at match-group regexp-fold-case? (type regexp rx-match))
(define screen-m (load-module "screen.fx"))
(import screen-m no-screen make-row face-row blank-row make-screen screen-update
        (type row rows screen span spans face))

(define-type strings (listof string acyclic))
(define-type ints (listof int acyclic))

"`s` with every `from` character replaced by `to`."
(define* string-replace-char (subr spin (string char char) string)
  (lambda (s from to)
    (list->string
     (letrec ((go (subr spin (int (listof char acyclic)) (listof char acyclic))
                (lambda (i acc)
                  (if (< i 0) acc
                      (go (- i 1) (cons (let ((c (string-ref s i))) (if (char=? c from) to c)) acc))))))
       (go (- (string-length s) 1) nil)))))

"Whether a file is Scheme: its name ends in .scm, .sld, .ss or .sps."
(define* scheme-name? (subr spin (string) bool)
  (lambda (name)
    (let ((ends (lambda ((x string))
                  (let ((n (string-length name)) (k (string-length x)))
                    (and (> n k) (string=? (substring name (- n k) n) x))))))
      (or (ends ".scm") (ends ".sld") (ends ".ss") (ends ".sps")))))
"The last part of a file name, after its last `/`."
(define* base-name (subr spin (string) string)
  (lambda (file)
    (letrec ((go (subr spin (int) string)
               (lambda (i)
                 (cond ((< i 0) file)
                       ((char=? (string-ref file i) #\/) (substring file (+ i 1) (string-length file)))
                       (else (go (- i 1)))))))
      (go (- (string-length file) 1)))))

"A file name's directory, with its last `/`; \"\" if it has none."
(define* directory-of (subr spin (string) string)
  (lambda (file)
    (letrec ((go (subr spin (int) string)
               (lambda (i)
                 (cond ((< i 0) "")
                       ((char=? (string-ref file i) #\/) (substring file 0 (+ i 1)))
                       (else (go (- i 1)))))))
      (go (- (string-length file) 1)))))

"Fixpt's own reader of FX-26 (`fx26:eager-reader.fx`), the one that reads
the editor itself: syntax with each form's span, in characters."
(define reader ((proj (load-module "fx26:eager-reader.fx") @s @e @m @c)))
(import reader eager-start-fx26 eager-feed-string eager-feed eager-status eager-state-syntax eager-context
        eager-state-message eager-state-position atom lst dotted vec (type syn syns state))
