;;; core.fx: actors, the messages between them, and turns (cahoots'
;;; `(yank actor core)`, c337e2a, typed).
;;;
;;; An actor has a mailbox and a state. Every message is code: a
;;; procedure of the actor's state, run in a *turn* of the actor's, one
;;; message at a time. `tell` never runs the receiver; the message waits
;;; in its mailbox until the scheduler (`run-turns!`) takes it.
;;;
;;; A turn is a transaction, and the types say so. A message's effect is
;;; `turn-eff`, which is cancellable: it may read, allocate and loop, but
;;; not write what others can see, nor do I/O. What it wants done -- sends,
;;; output, anything that changes the world -- it returns as commands, with
;;; the actor's next state. The scheduler runs the turn under `attempt`:
;;; if it ends well, the state is kept and the commands run, in order; if
;;; it fails (`error`, `car` of `nil`, …), nothing happens, the actor keeps
;;; the state it had, and the failure goes to the failure handler.
;;;
;;; All actors share one heap, so a message may close over anything, and
;;; a snapshot sent to another actor is a pointer, not a copy.
;;;
;;; Loaded at the client's region `ed`, where the scheduler's state lives,
;;; and the client's effect `world`, what its commands do outside:
;;;   (define core ((proj (load-module "core.fx") @ed (io stdout))))

(module-parameters ((ed region) (world effect)))

"What a turn may do: read, allocate (an actor spawned, a closure made),
loop, and nothing another could see."
(define-effect turn-eff (maxeff spin nondet (read @globals) (read ed) (alloc ed)))
"What a command may do, run after a turn that ended well."
(define-effect cmd-eff (maxeff spin nondet (read @globals) (read ed) (write ed) (alloc ed) world))

(define-type cmd (subr cmd-eff () unit))
(define-type cmds (listof cmd acyclic))
"A turn's outcome: the actor's next state, and what to do."
(define-type (reply (s type)) (productof (state s) (cmds cmds)))
"A message to an actor of state `s`."
(define-type (msg (s type)) (subr turn-eff (s) (reply s)))
"A message in a mailbox, with its key: a message told with a key
(`tell-latest`) takes the place of any waiting with that key. \"\" for none."
(define-type (envelope (s type)) (productof (key string) (msg (msg s))))
(define-type (msgs (s type)) (listof (envelope s) acyclic))
"An actor: its name, its state, its mailbox (a queue: `in` newest first,
`out` oldest first), whether it is in the run queue, and its scheduling
class (`interactive`, `display`, `idle`)."
(define-type (actor (s type))
  (productof (name string) (state (ref s ed))
             (in (ref (msgs s) ed)) (out (ref (msgs s) ed)) (queued (ref bool ed))
             (class (ref int ed))))

"Scheduling classes. Interactive actors (the frame, buffers) run first;
display actors (views) only when no interactive one waits, so a burst of
keys is laid out once, at its end; idle actors only when neither waits."
(define interactive int 0)
(define display int 1)
(define idle int 2)

(hide
  (define-type runner (subr cmd-eff () unit))
  (define-type runners (listof runner acyclic))
  ;; A run queue per class, of actors with mail, as a runner each: `qin`
  ;; newest first, `qout` oldest first.
  (define qin (arrayof runners ed) (make-array 3 nil))
  (define qout (arrayof runners ed) (make-array 3 nil))
  ;; Told each turn that fails: the actor's name, and what the failure said.
  (define failed (ref (subr cmd-eff (string string) unit) ed)
    (new (lambda ((who string) (why string)) #u)))
  (define turn-count (ref int ed) (new 0))

  (define enqueue! (subr (maxeff (read ed) (write ed)) (int runner) unit)
    (lambda (c r) (array-set! qin c (cons r (array-ref qin c)))))

  (define class-empty? (subr (read ed) (int) bool)
    (lambda (c) (and (null? (array-ref qin c)) (null? (array-ref qout c)))))

  ;; The next runner of class `c`, if any.
  (define dequeue-of! (subr (maxeff (read ed) (write ed)) (int) (union false runner))
    (lambda (c)
      (begin
        (if (null? (array-ref qout c))
            (begin (array-set! qout c (reverse (array-ref qin c))) (array-set! qin c nil))
            #u)
        (let ((o (array-ref qout c)))
          (if (null? o) #f (begin (array-set! qout c (cdr o)) (car o)))))))

  ;; The first class with a runner waiting, or -1.
  (define first-class (subr (read ed) () int)
    (lambda ()
      (cond ((not (class-empty? interactive)) interactive)
            ((not (class-empty? display)) display)
            ((not (class-empty? idle)) idle)
            (else -1))))

  (define run-cmds (subr cmd-eff (cmds) unit)
    (lambda (cs)
      (letrec ((go (subr cmd-eff (cmds) unit)
                 (lambda (cs) (if (null? cs) #u (begin ((car cs)) (go (cdr cs)))))))
        (go cs))))

  ;; `es` without the envelopes of key `k`.
  (define without-key (poly ((s type)) (subr spin (string (msgs s)) (msgs s)))
    (plambda ((s type))
      (lambda (k es)
        (letrec ((go (subr spin ((msgs s)) (msgs s))
                   (lambda (es)
                     (cond ((null? es) nil)
                           ((string=? (extract (car es) key) k) (go (cdr es)))
                           (else (cons (car es) (go (cdr es))))))))
          (go es))))))

"Each failing turn is told to `handler`: the actor's name, and the failure."
(define on-turn-failure! (subr (write ed) ((subr cmd-eff (string string) unit)) unit)
  (lambda (handler) (set failed handler)))

"A new actor, named `name` (for messages), of state `init`, interactive.
It takes messages at once, and runs once the scheduler gets to them."
(define spawn-actor (poly ((s type)) (subr (alloc ed) (string s) (actor s)))
  (plambda ((s type))
    (lambda (name init)
      (product (name name) (state (new init)) (in (new nil)) (out (new nil)) (queued (new #f))
               (class (new interactive))))))

"`a`'s scheduling class from now on."
(define set-class! (poly ((s type)) (subr (write ed) ((actor s) int) unit))
  (plambda ((s type)) (lambda (a c) (set (extract a class) c))))

(define actor-name (poly ((s type)) (subr pure ((actor s)) string))
  (plambda ((s type)) (lambda (a) (extract a name))))

"The actor's state, as of its last turn."
(define actor-state (poly ((s type)) (subr (read ed) ((actor s)) s))
  (plambda ((s type)) (lambda (a) (get (extract a state)))))

"The reply of a turn that changes nothing and does nothing."
(define same (poly ((s type)) (subr pure (s) (reply s)))
  (plambda ((s type)) (lambda (st) (product (state st) (cmds nil)))))

"The reply of a turn: the next state, and what to do."
(define reply-with (poly ((s type)) (subr pure (s cmds) (reply s)))
  (plambda ((s type)) (lambda (st cs) (product (state st) (cmds cs)))))

(define-rec
  ;; Envelope `e` put in `a`'s mailbox (any waiting with its key taken
  ;; out), and `a` in its class's run queue if it was not.
  (deliver! (poly ((s type)) (subr cmd-eff ((actor s) (envelope s)) unit))
    (plambda ((s type))
      (lambda (a e)
        (let ((k (extract e key)))
          (begin
            (if (string=? k "")
                #u
                (begin (set (extract a in) ((proj without-key s) k (get (extract a in))))
                       (set (extract a out) ((proj without-key s) k (get (extract a out))))))
            (set (extract a in) (cons e (get (extract a in))))
            (if (get (extract a queued))
                #u
                (begin (set (extract a queued) #t)
                       (enqueue! (get (extract a class)) (lambda () ((proj run-one s) a))))))))))
  ;; One turn of `a`: its oldest message, under `attempt`.
  (run-one (poly ((s type)) (subr cmd-eff ((actor s)) unit))
    (plambda ((s type))
      (lambda (a)
        (begin
          (if (null? (get (extract a out)))
              (begin (set (extract a out) (reverse (get (extract a in)))) (set (extract a in) nil))
              #u)
          (let ((o (get (extract a out))))
            (if (null? o)
                (set (extract a queued) #f)
                (let* ((m (extract (car o) msg))
                       (st (get (extract a state)))
                       (outcome (attempt (the (sumof (ok (reply s)) (lost string)) (sum ok (m st)))
                                         (lambda ((why string)) (the (sumof (ok (reply s)) (lost string)) (sum lost why))))))
                  (begin
                    (set (extract a out) (cdr o))
                    (set turn-count (+ (get turn-count) 1))
                    (tagcase outcome
                      (ok r (begin (set (extract a state) (extract r state))
                                   (run-cmds (extract r cmds))))
                      (lost why ((get failed) (extract a name) why)))
                    ;; Its turn again later, if it has more mail.
                    (if (and (null? (get (extract a in))) (null? (get (extract a out))))
                        (set (extract a queued) #f)
                        (enqueue! (get (extract a class)) (lambda () ((proj run-one s) a)))))))))))))

"A command: send `m` to `a`, once the turn that returns it ends well."
(define tell (poly ((s type)) (subr pure ((actor s) (msg s)) cmd))
  (plambda ((s type)) (lambda (a m) (lambda () ((proj deliver! s) a (product (key "") (msg m)))))))

"A command: send `m` to `a`, in place of any message waiting there that
was told with key `k` -- for what only the latest of matters (a snapshot)."
(define tell-latest (poly ((s type)) (subr pure ((actor s) string (msg s)) cmd))
  (plambda ((s type)) (lambda (a k m) (lambda () ((proj deliver! s) a (product (key k) (msg m)))))))

"Send `m` to `a` now, from outside any turn (the terminal's keys, say)."
(define tell! (poly ((s type)) (subr cmd-eff ((actor s) (msg s)) unit))
  (plambda ((s type)) (lambda (a m) ((proj deliver! s) a (product (key "") (msg m))))))

"Run turns until none wait, or `limit` have run, or, with a limit (not
-1), one of a display or idle actor has run, so that the caller can see
to keys between them. The number run."
(define run-turns! (subr cmd-eff (int) int)
  (lambda (limit)
    (letrec ((go (subr cmd-eff (int) int)
               (lambda (n)
                 (if (= n limit)
                     n
                     (let ((c (first-class)))
                       (if (< c 0)
                           n
                           (let ((r (dequeue-of! c)))
                             (if (procedure? r)
                                 (begin (r)
                                        (if (and (>= limit 0) (> c interactive)) (+ n 1) (go (+ n 1))))
                                 n))))))))
      (go 0))))

"Whether turns of an interactive actor wait."
(define interactive-waiting? (subr (read ed) () bool)
  (lambda () (not (class-empty? interactive))))

(define turns-waiting? (subr (read ed) () bool)
  (lambda () (>= (first-class) 0)))

(define turns-run (subr (read ed) () int) (lambda () (get turn-count)))
