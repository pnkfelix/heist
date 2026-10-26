;;; base.fx: what the editor's files share -- the modules they use, and
;;; the effect of what commands do outside. The editor is one program in
;;; several files, run in one session (`bin/heist-edit`), each file seeing
;;; the globals of those before it:
;;;   base.fx buffer.fx view.fx frame.fx main.fx

(define-effect world (maxeff (io stdout) (io terminal) (io fs-read) (io fs-write)))
(define core ((proj (load-module "core.fx") @ed world)))
(import core spawn-actor set-class! interactive display idle tell tell-latest tell! run-turns!
        turns-waiting? interactive-waiting? actor-state actor-name same reply-with
        on-turn-failure! turns-run (type actor msg reply cmd cmds) (effect turn-eff cmd-eff))
(define rope-m (load-module "rope.fx"))
(import rope-m empty-rope string->rope rope->string rope-length rope-insert rope-delete rope-ref
        rope-substring rope-line-start rope-line-end rope-line-of rope-line-count (type rope))
(define keys-m (load-module "keys.fx"))
(import keys-m read-key key->string keys->string kbd key=? (type key keys byte-source))
(define screen-m (load-module "screen.fx"))
(import screen-m no-screen make-row face-row blank-row make-screen screen-update
        (type row rows screen span spans face))

(define-type strings (listof string acyclic))

"`s` with every `from` character replaced by `to`."
(define* string-replace-char (subr spin (string char char) string)
  (lambda (s from to)
    (list->string
     (letrec ((go (subr spin (int (listof char acyclic)) (listof char acyclic))
                (lambda (i acc)
                  (if (< i 0) acc
                      (go (- i 1) (cons (let ((c (string-ref s i))) (if (char=? c from) to c)) acc))))))
       (go (- (string-length s) 1) nil)))))

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
