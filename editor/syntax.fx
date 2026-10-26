;;; syntax.fx: what an FX-26 buffer's text is, read by Fixpt's own reader
;;; (cahoots' syntax actor, `(yank actor syntax)`, in its first form).
;;;
;;; A party outside the text (DESIGN.md, "Boundaries"): an actor of the
;;; idle class, subscribed to its buffer, that reads each snapshot it is
;;; sent -- of a burst, only the last -- with `fx26:eager-reader.fx`, and
;;; sends the buffer an annotation of that revision: faces for keywords,
;;; types, the names definitions define, strings and comments; the
;;; definitions themselves, for M-.; and the read error, if any. The read
;;; is a command after the actor's turn, since the reader keeps state of
;;; its own; a turn may not change what others can see.
;;;
;;; The whole text is read again each time: about 150 ns a character, 9 ms
;;; for a 60 KB file. Reading only the list an edit is in is cahoots' next
;;; step, and this one's.

(define keywords strings
  (list "define" "define*" "define-rec" "define-type" "define-datatype" "define-effect"
        "define-generative" "lambda" "plambda" "vlambda" "rlambda" "let" "let*" "letrec"
        "letregion" "letrena" "letreap" "letfreeze" "if" "cond" "case" "and" "or" "begin"
        "tagcase" "typecase" "else" "the" "proj" "with" "module" "import" "hide" "include"
        "extend" "load-module" "load-input" "module-parameters" "set" "get" "new" "spawn"
        "spawn-monitored" "send" "receive" "pselect" "race" "par" "attempt" "prompt" "product"
        "sum" "extract" "quote" "quasiquote" "acyclic" "icell-get" "icell-put!" "self"))
(define type-words strings
  (list "subr" "poly" "productof" "sumof" "listof" "pairof" "arrayof" "ref" "union" "maxeff"
        "moduleof" "->" "->*" "vsubr" "icell" "addr" "inbox" "bytevectorof" "flatarrayof" "mu"
        "select" "nlist" "dlambda"))
(define definers strings
  (list "define" "define*" "define-type" "define-datatype" "define-effect" "define-generative"))

(define* member? (subr spin (string strings) bool)
  (lambda (s l) (and (pair? l) (or (string=? s (car l)) (member? s (cdr l))))))

(define* reverse-faces (subr pure (text-faces) text-faces)
  (lambda (l)
    (letrec ((go (subr pure (text-faces text-faces) text-faces)
               (lambda (l acc) (if (null? l) acc (go (cdr l) (cons (car l) acc))))))
      (go l nil))))

(define* reverse-definitions (subr pure (definitions) definitions)
  (lambda (l)
    (letrec ((go (subr pure (definitions definitions) definitions)
               (lambda (l acc) (if (null? l) acc (go (cdr l) (cons (car l) acc))))))
      (go l nil))))

"Comments and strings, found by scanning: sorted, not overlapping."
(define* lexical-faces (subr spin (string) text-faces)
  (lambda (s)
    (let ((n (string-length s)))
      (letrec ((line-end (subr spin (int) int)
                 (lambda (i) (if (or (>= i n) (char=? (string-ref s i) #\newline)) i (line-end (+ i 1)))))
               (string-end (subr spin (int) int)        ; just after the closing quote
                 (lambda (i)
                   (cond ((>= i n) n)
                         ((char=? (string-ref s i) #\\) (string-end (+ i 2)))
                         ((char=? (string-ref s i) #\") (+ i 1))
                         (else (string-end (+ i 1))))))
               (go (subr spin (int text-faces) text-faces)
                 (lambda (i acc)
                   (if (>= i n)
                       (reverse-faces acc)
                       (let ((c (string-ref s i)))
                         (cond ((char=? c #\;)
                                (let ((j (line-end i)))
                                  (go j (cons (product (start i) (end j) (face 'comment)) acc))))
                               ((char=? c #\")
                                (let ((j (string-end (+ i 1))))
                                  (go j (cons (product (start i) (end j) (face 'string)) acc))))
                               ;; A character literal: #\; and #\" are not a comment or a string.
                               ((and (char=? c #\#) (< (+ i 1) n) (char=? (string-ref s (+ i 1)) #\\))
                                (go (+ i 3) acc))
                               (else (go (+ i 1) acc))))))))
        (go 0 nil)))))

(define-type found (productof (faces text-faces) (definitions definitions)))

"What a definition's second item defines: a name, `(name …)` (a type
with parameters, Scheme's procedure form), or nothing (\"\")."
(define* defined-name (subr spin (syn) definition)
  (lambda (x)
    (tagcase x
      (atom (d a b) (typecase d (symbol s (product (name (symbol->string s)) (start a) (end b)))
                              (else y (product (name "") (start 0) (end 0)))))
      (lst (items d a b) (if (pair? items) (defined-name (car items)) (product (name "") (start 0) (end 0))))
      (else y (product (name "") (start 0) (end 0))))))

(define* add-face (subr pure (found int int face) found)
  (lambda (acc a b f)
    (product (faces (cons (product (start a) (end b) (face f)) (extract acc faces)))
             (definitions (extract acc definitions)))))

(define* add-definition (subr pure (found definition) found)
  (lambda (acc d) (product (faces (extract acc faces)) (definitions (cons d (extract acc definitions))))))

;; Keywords, type words and defined names, from the syntax read; and the
;; definitions, at the top level or one in (a module's, a `hide`'s). Faces
;; last first.
(define-rec
  (tree-faces (->* ((listof syn acyclic) int found) found)
  (lambda (forms depth acc)
    (if (null? forms)
        acc
        (tree-faces (cdr forms) depth (syn-faces (car forms) depth acc)))))

  (syn-faces (->* (syn int found) found)
  (lambda (x depth acc)
    (tagcase x
      (lst (items d a b)
        (let ((head (if (pair? items)
                        (tagcase (car items)
                          (atom (hd ha hb)
                            (typecase hd (symbol h (product (name (symbol->string h)) (start ha) (end hb)))
                                         (else y (product (name "") (start 0) (end 0)))))
                          (else y (product (name "") (start 0) (end 0))))
                        (product (name "") (start 0) (end 0)))))
          (let* ((name (extract head name))
                 (acc (cond ((member? name keywords)
                             (add-face acc (extract head start) (extract head end) 'keyword))
                            ((member? name type-words)
                             (add-face acc (extract head start) (extract head end) 'type))
                            (else acc)))
                 (acc (if (and (member? name definers) (pair? items) (pair? (cdr items)))
                          (let ((defined (defined-name (car (cdr items)))))
                            (if (string=? (extract defined name) "")
                                acc
                                (let ((acc (add-face acc (extract defined start) (extract defined end) 'function-name)))
                                  (if (<= depth 1) (add-definition acc defined) acc))))
                          acc)))
            (tree-faces (if (pair? items) (cdr items) items) (+ depth 1) acc))))
      (dotted (items tail d a b) (syn-faces tail (+ depth 1) (tree-faces items (+ depth 1) acc)))
      (vec (items d a b) (tree-faces items (+ depth 1) acc))
      (atom (d a b) acc)))))

"Two sorted lists of faces as one, a face of `a` before one of `b` that
starts where it does."
(define* merge-faces (subr spin (text-faces text-faces) text-faces)
  (lambda (a b)
    (cond ((null? a) b)
          ((null? b) a)
          ((<= (extract (car a) start) (extract (car b) start)) (cons (car a) (merge-faces (cdr a) b)))
          (else (cons (car b) (merge-faces a (cdr b)))))))

"Where the outermost construct still open in a read starts, from the
reader's context (its marks: innermost first, each `(name start …)`); -1
if none is."
(define* open-start (subr (maxeff (read @c) spin) ((listof datum @c)) int)
  (lambda (ctx)
    (letrec ((go (subr (maxeff (read @c) spin) ((listof datum @c) int) int)
               (lambda (l found)
                 (if (null? l)
                     found
                     (let ((e (car l)))
                       (go (cdr l)
                           (if (and (pair? e) (pair? (cdr e)) (symbol? (car e))
                                    (not (symbol=? (car e) 'top)) (not (symbol=? (car e) 'comment)))
                               (typecase (car (cdr e)) (int i i) (else y found))
                               found)))))))
      (go ctx -1))))

"A reader's state partway through a text, at `at`: since the reader
changes nothing (its states are values), it can be resumed from there for
any text that is the same before `at`."
(define-type checkpoint (productof (at int) (state state)))
(define-type checkpoints (listof checkpoint acyclic))
"What a syntax actor keeps between reads: the text read last, and the
checkpoints in it, in order."
(define-type memory (productof (text string) (checkpoints checkpoints)))
(define no-memory memory (product (text "") (checkpoints nil)))

"Where `a` and `b` first differ (the shorter's length if one is the start
of the other)."
(define* first-difference (subr spin (string string) int)
  (lambda (a b)
    (let ((n (min (string-length a) (string-length b))))
      (letrec ((go (subr spin (int) int)
                 (lambda (i) (if (or (>= i n) (not (char=? (string-ref a i) (string-ref b i)))) i (go (+ i 1))))))
        (go 0)))))

"The checkpoints of `cs` at or before `d`, in order."
(define* checkpoints-before (subr spin (checkpoints int) checkpoints)
  (lambda (cs d)
    (cond ((null? cs) nil)
          ((> (extract (car cs) at) d) nil)
          (else (cons (car cs) (checkpoints-before (cdr cs) d))))))

(define* last-checkpoint (subr spin (checkpoints checkpoint) checkpoint)
  (lambda (cs default) (if (null? cs) default (if (null? (cdr cs)) (car cs) (last-checkpoint (cdr cs) default)))))

"Text `s` read from `from` on, given the reader's state there: the state at
the end, and a checkpoint at each line after `from`, newest first, onto
`acc`. Any position would do; a state there is good for any text that is
the same before it."
(define* read-from (subr (maxeff reader-eff spin) (string int state checkpoints)
                         (productof (state state) (checkpoints checkpoints)))
  (lambda (s from st acc)
    (let ((n (string-length s)))
      (letrec ((boundary (subr spin (int) int)        ; the next line start after i; or n
                 (lambda (i)
                   (cond ((>= i n) n)
                         ((char=? (string-ref s (- i 1)) #\newline) i)
                         (else (boundary (+ i 1))))))
               (go (subr (maxeff reader-eff spin) (int state checkpoints) (productof (state state) (checkpoints checkpoints)))
                 (lambda (i st acc)
                   (if (>= i n)
                       (product (state st) (checkpoints acc))
                       (let* ((j (boundary (+ i 1)))
                              (st2 (eager-feed-string st (substring s i j))))
                         (go j st2 (if (< j n) (cons (product (at j) (state st2)) acc) acc)))))))
        (go from st acc)))))

(define* reverse-checkpoints (subr pure (checkpoints) checkpoints)
  (lambda (l)
    (letrec ((go (subr pure (checkpoints checkpoints) checkpoints)
               (lambda (l acc) (if (null? l) acc (go (cdr l) (cons (car l) acc))))))
      (go l nil))))

"What text `s` of revision `rev` is, from the reader's state `st` at its
end."
(define* annotation-of (subr (maxeff reader-eff spin) (string int state) annotation)
  (lambda (s rev st)
    (let* ((status (eager-status st))
           (found (tree-faces (eager-state-syntax st) 0 (product (faces nil) (definitions nil))))
           (problem (case status
                      ((error) (eager-state-message st))
                      ((incomplete) "a form is not closed")
                      (else "")))
           (at (case status
                 ((error) (min (eager-state-position st) (max 0 (- (string-length s) 1))))
                 ((incomplete) (max 0 (open-start (eager-context st))))
                 (else -1)))
           (tree (reverse-faces (extract found faces)))
           (marked (if (< at 0) tree
                       (merge-faces tree (list (product (start at) (end (+ at 1)) (face 'error)))))))
      (product (revision rev) (faces (merge-faces (lexical-faces s) marked))
               (definitions (reverse-definitions (extract found definitions)))
               (problem problem) (problem-at at)))))

"Text `s`, of revision `rev`, read -- from the last checkpoint before where
it first differs from the text read last -- and what it is; and the
memory for next time."
(define* analyze-incremental (subr (maxeff reader-eff spin) (string int memory) (productof (annotation annotation) (memory memory)))
  (lambda (s rev mem)
    (let* ((d (first-difference (extract mem text) s))
           (kept (checkpoints-before (extract mem checkpoints) d))
           (base (last-checkpoint kept (product (at 0) (state (eager-start-fx26)))))
           (read (read-from s (extract base at) (extract base state) (reverse-checkpoints kept)))
           (st (eager-feed (extract read state) #\newline)))
      (product (annotation (annotation-of s rev st))
               (memory (product (text s) (checkpoints (reverse-checkpoints (extract read checkpoints)))))))))

"Text `s`, of revision `rev`, read whole, and what it is."
(define* analyze (subr (maxeff reader-eff spin) (string int) annotation)
  (lambda (s rev) (extract (analyze-incremental s rev no-memory) annotation)))

(define-type syntax-state (productof (buffer (actor buffer)) (revision int) (memory (ref memory @ed))))

"Message for a syntax actor: a snapshot of its buffer, read after the turn
unless it is of the revision read last."
(define* syntax-snapshot (subr pure (snapshot) (msg syntax-state))
  (lambda (snap)
    (lambda ((st syntax-state))
      (let ((rev (extract snap revision)) (b (extract st buffer)))
        (if (= rev (extract st revision))
            (same st)
            (let ((text (extract snap text)) (cell (extract st memory)))
              (reply-with (product (buffer b) (revision rev) (memory cell))
                          (list (lambda ()
                                  (let ((r (analyze-incremental (rope->string text) rev (get cell))))
                                    (begin (set cell (extract r memory))
                                           (tell! b (annotate (extract r annotation))))))))))))))

"Whether a file is FX-26: its name ends in `.fx`."
(define* fx26-file? (subr pure (string) bool)
  (lambda (name)
    (let ((n (string-length name)))
      (and (> n 3) (string=? (substring name (- n 3) n) ".fx")))))

"For an FX-26 buffer, a syntax actor, and the commands that make it idle
and subscribe it; for another, none."
(define* attach-syntax (subr (alloc @ed) ((actor buffer) string) cmds)
  (lambda (b name)
    (if (fx26-file? name)
        (let ((sx (spawn-actor (string-append "syntax of " name)
                               (product (buffer b) (revision -1) (memory (the (ref memory @ed) (new no-memory)))))))
          (list (lambda () (set-class! sx idle))
                (tell b (subscribe -1 (lambda ((s snapshot)) (tell-latest sx "snapshot" (syntax-snapshot s)))))))
        nil)))
