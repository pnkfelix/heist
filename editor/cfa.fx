;;; cfa.fx: the CFA (../cfa/: a flow analysis of FX-26 and Scheme) in the
;;; editor.
;;;
;;;   C-c f   what the CFA found at point: what can reach the variable,
;;;           what the call can call (in an FX-26 or a Scheme buffer)
;;;
;;; The CFA runs in a process of its own, `bin/cfa --serve`, started the
;;; first time C-c f is used, as s7st's is (scheme.fx); cfa/serve.fx says
;;; its requests and answers. From then on, each FX-26 and Scheme buffer's
;;; every revision is sent to it as it is made (`flow-attach`), and its
;;; notes asked for; the main loop looks for its answers every 50 ms while
;;; one is awaited (`cfa-poll!`). A file's world -- what is analysed with
;;; it: its directory's `.fx` files, or the Scheme file alone -- is read
;;; from the buffers sent, and else from the files.
(module-parameters ((m-base (load-moduleof "base.fx"))
                    (m-buffer (load-moduleof "buffer.fx" m-base))
                    (m-resolve (load-moduleof "resolve.fx" m-base m-buffer))
                    (m-syntax (load-moduleof "syntax.fx" m-base m-buffer m-resolve))
                    (m-sexp (load-moduleof "sexp.fx" m-base m-buffer m-resolve m-syntax))
                    (m-flow (load-moduleof "flow.fx" m-base m-buffer m-resolve m-syntax m-sexp))
                    (m-index (load-moduleof "index.fx" m-base m-buffer m-resolve m-syntax m-sexp m-flow))
                    (m-view (load-moduleof "view.fx" m-base m-buffer m-resolve m-syntax m-sexp m-flow m-index))
                    (m-frame (load-moduleof "frame.fx" m-base m-buffer m-resolve m-syntax m-sexp m-flow m-index m-view))
                    (m-calls (load-moduleof "calls.fx" m-base m-buffer m-resolve m-syntax m-sexp m-flow m-index m-view m-frame))
                    (m-process (load-moduleof "process.fx" m-base m-buffer m-resolve m-syntax m-sexp m-flow m-index m-view m-frame m-calls))
                    (m-files (load-moduleof "files.fx" m-base m-buffer m-resolve m-syntax m-sexp m-flow m-index m-view m-frame m-calls m-process))
                    (m-help (load-moduleof "help.fx" m-base m-buffer m-resolve m-syntax m-sexp m-flow m-index m-view m-frame m-calls m-process m-files))
                    (m-eldoc (load-moduleof "eldoc.fx" m-base m-buffer m-resolve m-syntax m-sexp m-flow m-index m-view m-frame m-calls m-process m-files m-help))
                    (m-scheme (load-moduleof "scheme.fx" m-base m-buffer m-resolve m-syntax m-sexp m-flow m-index m-view m-frame m-calls m-process m-files m-help m-eldoc))))

"The server's process, if it runs; whether it said it is ready; what it
wrote after its last whole line."
(define cfa-server (ref ints @ed) (new nil))
(define cfa-ready (ref bool @ed) (new #f))
(define cfa-partial (ref string @ed) (new ""))
"Each buffer's notes, from its latest analysis: the revision they are of."
(define-type cfa-buffer-notes (productof (buffer (actor buffer)) (revision int) (notes (listof s7-note acyclic))))
(define cfa-notes (ref (listof cfa-buffer-notes acyclic) @ed) (new nil))
"The notes asked for and not yet given: each request's key, and the buffer
and revision it is of."
(define-type cfa-pending (productof (key int) (buffer (actor buffer)) (revision int)))
(define cfa-requests (ref (listof cfa-pending acyclic) @ed) (new nil))
(define cfa-next-key (ref int @ed) (new 0))
"Who waits for a buffer's notes, to be told what is at point: a frame, the
buffer, the revision and the point."
(define-type cfa-asking (productof (frame (actor frame)) (buffer (actor buffer)) (revision int) (point int)))
(define cfa-askers (ref (listof cfa-asking acyclic) @ed) (new nil))

(define* cfa-server-up! (subr cmd-eff () bool)
  (lambda ()
    (or (pair? (get cfa-server))
        (tagcase (process-start (list "../bin/cfa" "--serve") "")
          (started id (begin (set cfa-server (list id)) (set cfa-ready #f) (set cfa-partial "") #t))
          (failed e #f)))))
(define* cfa-send! (subr cmd-eff (string strings) unit)
  (lambda (word fields)
    (let ((s (get cfa-server)))
      (if (null? s) #u
          (letrec ((join (subr spin (strings) string)
                     (lambda (l) (cond ((null? l) "") ((null? (cdr l)) (s7-escape (car l)))
                                       (else (string-append (s7-escape (car l)) "\t" (join (cdr l))))))))
            (begin (process-write (car s) (string-append word " " (join fields) "\n")) #u))))))

"Revision `rev` of file `file`, buffer `b`, text `text`, sent to be
analysed, and its notes asked for."
(define* cfa-send-revision! (subr cmd-eff ((actor buffer) string int string) unit)
  (lambda (b file rev text)
    (let ((key (get cfa-next-key)))
      (begin
        (set cfa-next-key (+ key 1))
        (set cfa-requests (cons (product (key key) (buffer b) (revision rev)) (get cfa-requests)))
        (cfa-send! "file" (list file text))
        (cfa-send! "notes" (list (int->string key) file))))))

"The note at `p` of buffer `b`'s notes of revision `rev`: the narrowest
whose span holds `p` (or ends at it); \"\" if none, or none of `rev`."
(define* cfa-note-at (subr (maxeff spin (read @ed)) ((actor buffer) int int) string)
  (lambda (b rev p)
    (letrec ((buffer (subr spin ((listof cfa-buffer-notes acyclic)) string)
               (lambda (l) (cond ((null? l) "")
                                 ((same-actor? (extract (car l) buffer) b)
                                  (if (= (extract (car l) revision) rev) (note (extract (car l) notes) "" -1) ""))
                                 (else (buffer (cdr l))))))
             (note (subr spin ((listof s7-note acyclic) string int) string)
               (lambda (l best size)
                 (cond ((null? l) best)
                       ((and (<= (extract (car l) start) p) (<= p (extract (car l) end))
                             (or (< size 0) (< (- (extract (car l) end) (extract (car l) start)) size)))
                        (note (cdr l) (extract (car l) text) (- (extract (car l) end) (extract (car l) start))))
                       (else (note (cdr l) best size))))))
      (buffer (get cfa-notes)))))

"The askers whose notes have come, told; the others kept."
(define* cfa-tell-askers! (subr cmd-eff () unit)
  (lambda ()
    (set cfa-askers
         (letrec ((go (subr cmd-eff ((listof cfa-asking acyclic)) (listof cfa-asking acyclic))
                    (lambda (l)
                      (if (null? l) nil
                          (let* ((a (car l))
                                 (have (letrec ((h (subr spin ((listof cfa-buffer-notes acyclic)) bool)
                                                  (lambda (ns) (and (pair? ns) (or (and (same-actor? (extract (car ns) buffer) (extract a buffer))
                                                                                        (= (extract (car ns) revision) (extract a revision)))
                                                                                   (h (cdr ns)))))))
                                         (h (get cfa-notes)))))
                            (if have
                                (let ((n (cfa-note-at (extract a buffer) (extract a revision) (extract a point))))
                                  (begin (tell! (extract a frame) (echo (if (string=? n "") "The CFA found nothing at point" n)))
                                    (go (cdr l))))
                                (cons a (go (cdr l)))))))))
           (go (get cfa-askers))))))

"An answer of the server's, `line`, acted on."
(define* cfa-answer! (subr cmd-eff (string) unit)
  (lambda (line)
    (let* ((sp (string-search line " " 0))
           (word (if (< sp 0) line (substring line 0 sp)))
           (fields (the strings (if (< sp 0) (list "") (s7-fields (substring line (+ sp 1) (string-length line)))))))
      (cond
        ((string=? word "ready") (set cfa-ready #t))
        ((string=? word "notes")
         (let ((key (s7-integer (car fields))))
           (letrec ((find (subr spin ((listof cfa-pending acyclic)) (sumof (none unit) (found cfa-pending)))
                      (lambda (l) (cond ((null? l) (sum none #u)) ((= (extract (car l) key) key) (sum found (car l))) (else (find (cdr l))))))
                    (drop (subr spin ((listof cfa-pending acyclic)) (listof cfa-pending acyclic))
                      (lambda (l) (cond ((null? l) nil) ((= (extract (car l) key) key) (cdr l)) (else (cons (car l) (drop (cdr l))))))))
             (tagcase (find (get cfa-requests))
               (found r (let ((b (extract r buffer)))
                          (begin
                            (set cfa-requests (drop (get cfa-requests)))
                            (set cfa-notes (cons (product (buffer b) (revision (extract r revision)) (notes (s7-notes-of (s7-nth-field fields 2))))
                                                 (letrec ((others (subr spin ((listof cfa-buffer-notes acyclic)) (listof cfa-buffer-notes acyclic))
                                                                    (lambda (l) (cond ((null? l) nil) ((same-actor? (extract (car l) buffer) b) (others (cdr l)))
                                                                                      (else (cons (car l) (others (cdr l))))))))
                                                   (others (get cfa-notes)))))
                            (cfa-tell-askers!))))
               (none u #u)))))
        (else #u)))))

"The server's answers so far acted on. Whether one is still awaited, for
the main loop to look again in 50 ms."
(define* cfa-poll! (subr cmd-eff () bool)
  (lambda ()
    (let ((s (get cfa-server)))
      (if (null? s) #f
          (let ((text (string-append (get cfa-partial) (process-output (car s)))))
            (letrec ((lines (subr cmd-eff (int) unit)
                       (lambda (from)
                         (let ((e (string-search text "\n" from)))
                           (if (< e 0) (set cfa-partial (substring text from (string-length text)))
                               (begin (cfa-answer! (substring text from e)) (lines (+ e 1))))))))
              (begin
                (lines 0)
                (tagcase (process-status (car s))
                  (running u #u)
                  (else y (begin (set cfa-server nil) (set cfa-requests nil) (set cfa-askers nil))))
                (and (pair? (get cfa-server)) (or (not (get cfa-ready)) (pair? (get cfa-requests)))))))))))

"The server stopped (the editor ends)."
(define* cfa-stop! (subr cmd-eff () unit)
  (lambda ()
    (let ((s (get cfa-server)))
      (if (null? s) #u (begin (process-close-input (car s)) (process-signal (car s) 1) (set cfa-server nil))))))

;;; ------------------------------------------------------------ buffers

"A buffer's CFA actor's state: its buffer, its file, and the revision last
sent."
(define-type cfa-state (productof (buffer (actor buffer)) (file string) (revision int)))
"Message for a CFA actor: a snapshot of its buffer, sent to the CFA if it
runs, unless it is of the revision sent last."
(define* cfa-snapshot (subr pure (snapshot) (msg cfa-state))
  (lambda (snap)
    (lambda ((st cfa-state))
      (let ((rev (extract snap revision)))
        (if (= rev (extract st revision))
            (same st)
            (reply-with (product (buffer (extract st buffer)) (file (extract st file)) (revision rev))
                        (list (lambda ()
                                (if (pair? (get cfa-server))
                                    (cfa-send-revision! (extract st buffer) (extract st file) rev (rope->string (extract snap text)))
                                    #u)))))))))
"A buffer's CFA actor, idle, subscribed to it."
(define* cfa-attach (subr (maxeff (alloc @ed) (read @globals)) ((actor buffer) string) cmds)
  (lambda (b file)
    (let ((cx (spawn-actor (string-append "CFA of " file) (product (buffer b) (file file) (revision -1)))))
      (list (lambda () (set-class! cx idle))
            (tell b (subscribe -1 (lambda ((s snapshot)) (tell-latest cx "snapshot" (cfa-snapshot s)))))))))
(set flow-attach (list cfa-attach))

"C-c f: the CFA's note at point; the server started, and this revision of
the buffer sent, if need be."
(define* cfa-at-point (subr pure () frame-action)
  (lambda ()
    (lambda ((fr (actor frame)) (f frame))
      (let* ((b (extract (selected-window f) buffer))
             (st (actor-state b))
             (file (extract st file))
             (rev (extract st revision))
             (p (extract st point)))
        (if (not (or (fx26-file? file) (scheme-name? file)))
            (draw (with-echo f "Not an FX-26 or Scheme file"))
            (reply-with f
                        (list (lambda ()
                                (let ((n (cfa-note-at b rev p)))
                                  (cond ((not (string=? n "")) (tell! fr (echo n)))
                                        ((not (cfa-server-up!)) (tell! fr (echo "The CFA could not be started (../bin/cfa)")))
                                        (else
                                         (begin
                                           (set cfa-askers (cons (product (frame fr) (buffer b) (revision rev) (point p)) (get cfa-askers)))
                                           (if (letrec ((sent (subr spin ((listof cfa-pending acyclic)) bool)
                                                              (lambda (l) (and (pair? l) (or (and (same-actor? (extract (car l) buffer) b)
                                                                                                  (= (extract (car l) revision) rev))
                                                                                             (sent (cdr l)))))))
                                                 (sent (get cfa-requests)))
                                               #u
                                               (cfa-send-revision! b file rev (rope->string (extract st text))))
                                           (tell! fr (echo "The CFA is analysing..."))
                                           (cfa-tell-askers!)))))))))))))

(define-command! "cfa-at-point" (sum on-frame (cfa-at-point)))
(define-key! "C-c f" "cfa-at-point")
