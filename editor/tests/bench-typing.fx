;;; Typing, timed: the frame, a buffer of a large file, its view and the
;;; painter, as the editor runs them, the screen written to stdout (send
;;; it to /dev/null). Run after base.fx … frame.fx:
;;;   fixpt run base.fx buffer.fx view.fx frame.fx tests/bench-typing.fx -- FILE > /dev/null
(define* bench-main (subr (maxeff cmd-eff (io args) (io clock) (io stderr) (alloc @a)) () int)
  (lambda ()
    (let* ((as (the (listof string @a) (args)))
           (file (car as))
           (got (file-text file))
           (painter (spawn-actor "painter" no-screen))
           (b (spawn-actor "big" (new-buffer "big" file (extract got text))))
           (fr (spawn-actor "frame"
                            (product (height 50) (width 120) (windows (the windows nil)) (selected 0)
                                     (buffers (the buffer-infos nil)) (next-id 1) (echo "")
                                     (prefix (the keys nil)) (mini no-mini) (painter painter))))
           (ms (lambda ((from i64)) (i64->int (i64-quotient (i64- (clock) from) (int->i64 1000))))))
      (begin
        (set-class! painter display)
        (tell! fr (first-window fr "big" file b))
        (run-turns! -1)
        ;; Into the middle of the file.
        (letrec ((down (subr cmd-eff (int) unit)
                   (lambda (n) (if (= n 0) #u (begin (tell! fr (key-typed fr 'C-n)) (down (- n 1)))))))
          (down 1000))
        (run-turns! -1)
        ;; A burst: 200 keys sent at once, then the turns run, as typing
        ;; ahead does.
        (let ((t0 (clock)))
          (begin
            (letrec ((burst (subr cmd-eff (int) unit)
                       (lambda (n) (if (= n 0) #u (begin (tell! fr (key-typed fr #\x)) (burst (- n 1)))))))
              (burst 200))
            (run-turns! -1)
            (write-err (string-append "burst of 200 keys: " (int->string (ms t0)) " us in all, "
                                      (int->string (quotient (ms t0) 200)) " us a key\n"))))
        ;; One at a time: each key's turns run to the end, drawn, before the next.
        (let ((t0 (clock)))
          (begin
            (letrec ((one (subr cmd-eff (int) unit)
                       (lambda (n) (if (= n 0) #u (begin (tell! fr (key-typed fr #\y)) (run-turns! -1) (one (- n 1)))))))
              (one 200))
            (write-err (string-append "200 keys one at a time: " (int->string (quotient (ms t0) 200)) " us a key\n"))))
        0))))
(define main bench-main)
