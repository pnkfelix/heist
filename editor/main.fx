;;; main.fx: the terminal, and the scheduler between keys (cahoots'
;;; `(yank actor main)`, c337e2a). Run after base.fx, buffer.fx, view.fx
;;; and frame.fx, by `bin/heist-edit FILE`.
;;;
;;; Turns run while any wait, a batch at a time, keys typed meanwhile read
;;; between batches and sent to the frame. A batch stops after a turn of a
;;; view or the painter (display class), so a key waits for at most one
;;; such turn. With none waiting, it waits for a key, and every half second
;;; looks at the terminal's size.

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

"Send the frame the keys typed, waiting up to `timeout` ms for the first.
Whether any came."
(define* send-keys! (subr (maxeff cmd-eff (io stdin) (io clock)) ((actor frame) int) bool)
  (lambda (fr timeout)
    (let ((k (read-key next-byte timeout)))
      (typecase k
        (bool f #f)
        (else y (begin (tell! fr (key-typed fr y))
                       (send-keys! fr 0)
                       #t))))))

(define* terminal-dimensions (subr (io terminal) () (productof (rows int) (columns int)))
  (lambda ()
    (tagcase (terminal-size)
      (size s s)
      (else y (product (rows 24) (columns 80))))))

(define* run-loop (subr (maxeff cmd-eff (io stdin) (io clock) (io terminal)) ((actor frame) int int) unit)
  (lambda (fr rows columns)
    (begin
      (run-turns! 100)
      (cond ((not (get running)) #u)
            ((turns-waiting?) (begin (send-keys! fr 0) (run-loop fr rows columns)))
            ((send-keys! fr 500) (run-loop fr rows columns))
            ((not (get running)) #u)
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
           (b (spawn-actor name (new-buffer name file (extract got text))))
           (fr (spawn-actor "frame"
                            (product (height h) (width w) (windows (the windows nil)) (selected 0)
                                     (buffers (the buffer-infos nil)) (next-id 1) (echo "")
                                     (prefix (the keys nil)) (mini no-mini) (painter painter)))))
      (begin
        (set-class! painter display)
        (on-turn-failure! (lambda ((who string) (why string)) (tell! fr (echo (string-append who ": " why)))))
        (terminal-raw)
        (write-out "\x1b;[?1049h")
        (tell! fr (first-window fr name file b))
        (if (extract got found) #u (tell! fr (echo "(New file)")))
        (run-loop fr h w)
        (write-out "\x1b;[?1049l")
        (terminal-restore)
        0))))
