;;; main.fx: the terminal, and the scheduler between keys (cahoots'
;;; `(yank actor main)`, c337e2a). Run last of the files `program` lists,
;;; by `bin/heist-edit FILE`.
;;;
;;; Turns run while any wait, a batch at a time, keys typed meanwhile read
;;; between batches and sent to the frame. A batch stops after a turn of a
;;; view or the painter (display class), so a key waits for at most one
;;; such turn. With none waiting, it waits for a key, and every half second
;;; looks at the terminal's size; with processes running (process.fx), it
;;; looks for their output every 50 ms, and for s7st's answers while one is
;;; awaited (scheme.fx).

"The next byte typed, or #f if none comes within `timeout` ms (0: only
one already there)."
(define* next-byte (subr (maxeff (io stdin) (io clock) (read @ed) (write @ed) nondet spin) (int) (union false int))
  (lambda (timeout)
    (let ((of (lambda ((r (sumof (byte u8) (eof unit) (failed io-error))))
                (the (union false int)
                     (tagcase r
                       (byte u (u8->int u))
                       ;; The input ended (or failed): the editor ends.
                       (else y (begin (set running #f) #f)))))))
      (if (<= timeout 0)
          (if (stdin-ready?) (of (read-byte)) (the (union false int) #f))
          (pselect ((read-byte) r (of r))
            ((sleep-until (i64+ (clock) (int->i64 (* timeout 1000000)))) u (the (union false int) #f)))))))

"The keys typed and not yet sent, oldest first; and the activity of the
one being handled (-1: none). A key is sent to the frame as an activity,
the next only when its activity is done -- its commands, the buffers'
turns, a file read -- so keys typed ahead apply in order to what the keys
before them made (C-x C-f's buffer). C-g gives up the one being handled,
and those waiting."
(define pending-keys (ref keys @ed) (new nil))
(define current-key (ref int @ed) (new -1))

"Send the frame the next key waiting, if the last is done."
(define* pump-keys! (subr cmd-eff ((actor frame)) unit)
  (lambda (fr)
    (let ((ks (get pending-keys)))
      (if (or (null? ks) (and (>= (get current-key) 0) (activity-running? (get current-key))))
          #u
          (begin (set pending-keys (cdr ks))
            (set eldoc-due #t)
            (set current-key (start! fr (key-typed fr (car ks)))))))))

"Read the keys typed, waiting up to `timeout` ms for the first, into the
queue; C-g at once. Whether any came."
(define* send-keys! (subr (maxeff cmd-eff (io stdin) (io clock)) ((actor frame) int) bool)
  (lambda (fr timeout)
    (let ((k (read-key next-byte timeout)))
      (typecase k
        (bool f #f)
        (else y
          (begin
            (if (key=? y 'C-g)
                (begin
                  (if (>= (get current-key) 0) (abort-activity! (get current-key)) #u)
                  (set pending-keys (list y))
                  (set current-key -1))
                (set pending-keys (append (get pending-keys) (list y))))
            (send-keys! fr 0)
            #t))))))

(define* terminal-dimensions (subr (io terminal) () (productof (rows int) (columns int)))
  (lambda ()
    (tagcase (terminal-size)
      (size s s)
      (else y (product (rows 24) (columns 80))))))

(define* run-loop (subr (maxeff cmd-eff (io stdin) (io clock) (io terminal)) ((actor frame) int int) unit)
  (lambda (fr rows columns)
    (let* ((polling (poll-processes!))
           (scheming (s7-poll!)))
      (pump-keys! fr)
      (run-turns! 100)
      (cond ((not (get running)) #u)
            ((or (turns-waiting?) (pair? (get pending-keys))) (begin (send-keys! fr 0) (run-loop fr rows columns)))
            ;; Processes' output looked for every 50 ms while any runs;
            ;; after a key, eldoc's turn when 100 ms pass with no other.
            ((send-keys! fr (cond ((or polling scheming) 50) ((get eldoc-due) 100) (else 500))) (run-loop fr rows columns))
            ((not (get running)) #u)
            ((get eldoc-due) (begin (set eldoc-due #f) (tell! fr (eldoc-now fr)) (run-loop fr rows columns)))
            (else
             (let ((now (terminal-dimensions)))
               (if (and (= (extract now rows) rows) (= (extract now columns) columns))
                   (run-loop fr rows columns)
                   (begin (tell! fr (resized (extract now rows) (extract now columns)))
                     (run-loop fr (extract now rows) (extract now columns))))))))))

(define* main (subr (maxeff cmd-eff (io stdin) (io clock) (io terminal) (io args) (alloc @a)) () int)
  (lambda ()
    (let* ((as (the (listof string @a) (args)))
           (file (if (pair? as) (car as) ""))
           (name (if (string=? file "") "*scratch*" (base-name file)))
           (got (if (string=? file "") (product (text empty-rope) (found #t)) (file-text file)))
           (sz (terminal-dimensions))
           (h (extract sz rows))
           (w (extract sz columns))
           (painter (spawn-actor "painter" no-screen))
           (messages (spawn-actor "*Messages*" (new-buffer "*Messages*" "" empty-rope)))
           (b (spawn-actor name (new-buffer name file (extract got text))))
           (fr (spawn-actor "frame"
                            (product (height h) (width w) (windows (the windows nil)) (selected 0)
                                     (buffers (the buffer-infos (list (product (name "*Messages*") (file "") (actor messages))))) (next-id 1) (echo "")
                                     (prefix (the keys nil)) (mini no-mini) (painter painter)))))
      (begin
        (set-class! painter display)
        (set messages-buffer (list messages))
        (let ((ix (spawn-actor "index" (product (directories (the strings nil)) (pending (the strings nil))
                                                (files (the (listof indexed acyclic) nil))))))
          (begin (set-class! ix idle) (set the-index (list ix))))
        (on-turn-failure! (lambda ((who string) (why string)) (tell! fr (echo (string-append who ": " why)))))
        (terminal-raw)
        (write-out "\x1b;[?1049h")
        (tell! fr (first-window fr name file b))
        (if (extract got found) #u (tell! fr (echo "(New file)")))
        (run-loop fr h w)
        (signal-processes! 1)
        (s7-stop!)
        (write-out "\x1b;[?1049l")
        (terminal-restore)
        0))))
