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
(define-type (msgs (s type)) (listof (msg s) acyclic))
"An actor: its name, its state, its mailbox (a queue: `in` newest first,
`out` oldest first), and whether it is in the run queue."
(define-type (actor (s type))
  (productof (name string) (state (ref s ed))
             (in (ref (msgs s) ed)) (out (ref (msgs s) ed)) (queued (ref bool ed))))

(hide
  (define-type runner (subr cmd-eff () unit))
  (define-type runners (listof runner acyclic))
  ;; The run queue of actors with mail, as a runner each: `rin` newest
  ;; first, `rout` oldest first.
  (define rin (ref runners ed) (new nil))
  (define rout (ref runners ed) (new nil))
  ;; Told each turn that fails: the actor's name, and what the failure said.
  (define failed (ref (subr cmd-eff (string string) unit) ed)
    (new (lambda ((who string) (why string)) #u)))
  (define turn-count (ref int ed) (new 0))

  (define enqueue! (subr (maxeff (read ed) (write ed)) (runner) unit)
    (lambda (r) (set rin (cons r (get rin)))))

  ;; The next runner, if any.
  (define dequeue! (subr (maxeff (read ed) (write ed)) () (union false runner))
    (lambda ()
      (begin
        (if (null? (get rout))
            (begin (set rout (reverse (get rin))) (set rin nil))
            #u)
        (let ((o (get rout)))
          (if (null? o) #f (begin (set rout (cdr o)) (car o)))))))

  (define run-cmds (subr cmd-eff (cmds) unit)
    (lambda (cs)
      (letrec ((go (subr cmd-eff (cmds) unit)
                 (lambda (cs) (if (null? cs) #u (begin ((car cs)) (go (cdr cs)))))))
        (go cs)))))

"Each failing turn is told to `handler`: the actor's name, and the failure."
(define on-turn-failure! (subr (write ed) ((subr cmd-eff (string string) unit)) unit)
  (lambda (handler) (set failed handler)))

"A new actor, named `name` (for messages), of state `init`. It takes
messages at once, and runs once the scheduler gets to them."
(define spawn-actor (poly ((s type)) (subr (alloc ed) (string s) (actor s)))
  (plambda ((s type))
    (lambda (name init)
      (product (name name) (state (new init)) (in (new nil)) (out (new nil)) (queued (new #f))))))

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
  ;; Message `m` put in `a`'s mailbox, and `a` in the run queue if it
  ;; was not.
  (deliver! (poly ((s type)) (subr cmd-eff ((actor s) (msg s)) unit))
    (plambda ((s type))
      (lambda (a m)
        (begin
          (set (extract a in) (cons m (get (extract a in))))
          (if (get (extract a queued))
              #u
              (begin (set (extract a queued) #t)
                     (enqueue! (lambda () ((proj run-one s) a)))))))))
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
                (let* ((m (car o))
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
                        (enqueue! (lambda () ((proj run-one s) a)))))))))))))

"A command: send `m` to `a`, once the turn that returns it ends well."
(define tell (poly ((s type)) (subr pure ((actor s) (msg s)) cmd))
  (plambda ((s type)) (lambda (a m) (lambda () ((proj deliver! s) a m)))))

"Send `m` to `a` now, from outside any turn (the terminal's keys, say)."
(define tell! (poly ((s type)) (subr cmd-eff ((actor s) (msg s)) unit))
  (plambda ((s type)) (lambda (a m) ((proj deliver! s) a m))))

"Run turns until none wait, or `limit` have run (`-1`: no limit). The
number run."
(define run-turns! (subr cmd-eff (int) int)
  (lambda (limit)
    (letrec ((go (subr cmd-eff (int) int)
               (lambda (n)
                 (if (= n limit)
                     n
                     (let ((r (dequeue!)))
                       (if (procedure? r) (begin (r) (go (+ n 1))) n))))))
      (go 0))))

(define turns-waiting? (subr (read ed) () bool)
  (lambda () (not (and (null? (get rin)) (null? (get rout))))))

(define turns-run (subr (read ed) () int) (lambda () (get turn-count)))
