;;; cfa.fx: the CFA (../cfa/: a flow analysis of FX-26 and Scheme) in the
;;; editor.
;;;
;;;   C-c f   what the CFA found at point: what can reach the variable,
;;;           what the call can call
;;;   C-c e   the lambdas the call at point can call: the one visited, or
;;;           a list in *xref*
;;;   C-c r   the calls that can call the lambda point is in, in *xref*
;;;   C-c d   what the variable or call at point is in each context (each
;;;           call site of a small procedure, at depth 0), where they differ
;;;   eldoc   what the CFA found at point, where the text declares no type
;;;           (FX-26), or in place of s7st's description (Scheme)
;;;
;;; In an FX-26 or a Scheme buffer. The CFA runs in a process of its own,
;;; `bin/cfa --serve`, as s7st does (scheme.fx); cfa/serve.fx says its
;;; requests and answers. It is started by the first C-c f, C-c e or C-c r,
;;; or by a Scheme buffer, as s7st is. From then on, each FX-26 and Scheme
;;; buffer's every revision is sent to it as it is made (`flow-attach`),
;;; and its notes asked for; the main loop looks for its answers every 50
;;; ms while one is awaited (`cfa-poll!`). A file's world -- what is
;;; analysed with it: its directory's `.fx` files, or the Scheme file alone
;;; -- is read from the buffers sent, and else from the files.
(module-parameters ((m-base (load-moduleof "base.fx"))
                    (m-buffer (load-moduleof "buffer.fx" m-base))
                    (m-resolve (load-moduleof "resolve.fx" m-base m-buffer))
                    (m-syntax (load-moduleof "syntax.fx" m-base m-buffer m-resolve))
                    (m-sexp (load-moduleof "sexp.fx" m-base m-buffer m-resolve m-syntax))
                    (m-index (load-moduleof "index.fx" m-base m-buffer m-resolve m-syntax m-sexp))
                    (m-view (load-moduleof "view.fx" m-base m-buffer m-resolve m-syntax m-sexp m-index))
                    (m-frame (load-moduleof "frame.fx" m-base m-buffer m-resolve m-syntax m-sexp m-index m-view))
                    (m-calls (load-moduleof "calls.fx" m-base m-buffer m-resolve m-syntax m-sexp m-index m-view m-frame))
                    (m-process (load-moduleof "process.fx" m-base m-buffer m-resolve m-syntax m-sexp m-index m-view m-frame m-calls))
                    (m-files (load-moduleof "files.fx" m-base m-buffer m-resolve m-syntax m-sexp m-index m-view m-frame m-calls m-process))
                    (m-help (load-moduleof "help.fx" m-base m-buffer m-resolve m-syntax m-sexp m-index m-view m-frame m-calls m-process m-files))
                    (m-eldoc (load-moduleof "eldoc.fx" m-base m-buffer m-resolve m-syntax m-sexp m-index m-view m-frame m-calls m-process m-files m-help))
                    (m-scheme (load-moduleof "scheme.fx" m-base m-buffer m-resolve m-syntax m-sexp m-index m-view m-frame m-calls m-process m-files m-help m-eldoc))))

"The server's process, if it runs; whether it said it is ready; what it
wrote after its last whole line."
(define cfa-server (ref ints @ed) (new nil))
(define cfa-ready (ref bool @ed) (new #f))
(define cfa-partial (ref string @ed) (new ""))
"The revision of each file sent last."
(define-type cfa-sent-file (productof (file string) (revision int)))
(define cfa-sent (ref (listof cfa-sent-file acyclic) @ed) (new nil))
"Each buffer's notes, from its latest analysis: the revision they are of."
(define-type cfa-buffer-notes (productof (buffer (actor buffer)) (revision int) (notes (listof s7-note acyclic))))
(define cfa-notes (ref (listof cfa-buffer-notes acyclic) @ed) (new nil))
"The notes asked for and not yet given: each request's key, and the buffer
and revision it is of."
(define-type cfa-pending (productof (key int) (buffer (actor buffer)) (revision int)))
(define cfa-requests (ref (listof cfa-pending acyclic) @ed) (new nil))
"The queries (C-c e, C-c r) asked and not yet answered: each request's
key, the frame, and the buffers' texts as they were, to list places by."
(define-type cfa-texts (listof (productof (file string) (text string)) acyclic))
(define-type cfa-query (productof (key int) (frame (actor frame)) (dir string) (texts cfa-texts)))
(define cfa-queries (ref (listof cfa-query acyclic) @ed) (new nil))
(define cfa-next-key (ref int @ed) (new 0))
"Who waits for a buffer's notes, to be told what is at point: a frame, the
buffer, the revision and the point."
(define-type cfa-asking (productof (frame (actor frame)) (buffer (actor buffer)) (revision int) (point int)))
(define cfa-askers (ref (listof cfa-asking acyclic) @ed) (new nil))

(define* cfa-file? (subr spin (string) bool) (lambda (f) (or (fx26-file? f) (scheme-name? f))))

(define* cfa-server-up! (subr cmd-eff () bool)
  (lambda ()
    (or (pair? (get cfa-server))
        (tagcase (process-start (list "../bin/cfa" "--serve") "")
          (started id (begin (set cfa-server (list id)) (set cfa-ready #f) (set cfa-partial "") (set cfa-sent nil) #t))
          (failed e #f)))))
(define* cfa-send! (subr cmd-eff (string strings) unit)
  (lambda (word fields)
    (let ((s (get cfa-server)))
      (if (null? s) #u
          (letrec ((join (subr spin (strings) string)
                     (lambda (l) (cond ((null? l) "") ((null? (cdr l)) (s7-escape (car l)))
                                       (else (string-append (s7-escape (car l)) "\t" (join (cdr l))))))))
            (begin (process-write (car s) (string-append word " " (join fields) "\n")) #u))))))
(define* cfa-new-key! (subr cmd-eff () int)
  (lambda () (let ((k (get cfa-next-key))) (begin (set cfa-next-key (+ k 1)) k))))

"Revision `rev` of `file`, text `text`, sent, unless it was last."
(define* cfa-send-file! (subr cmd-eff (string int string) unit)
  (lambda (file rev text)
    (if (letrec ((sent (subr spin ((listof cfa-sent-file acyclic)) bool)
                       (lambda (l) (and (pair? l) (or (and (string=? (extract (car l) file) file) (= (extract (car l) revision) rev))
                                                      (sent (cdr l)))))))
          (sent (get cfa-sent)))
        #u
        (begin
          (set cfa-sent (cons (product (file file) (revision rev))
                              (letrec ((others (subr spin ((listof cfa-sent-file acyclic)) (listof cfa-sent-file acyclic))
                                                 (lambda (l) (cond ((null? l) nil) ((string=? (extract (car l) file) file) (others (cdr l)))
                                                                   (else (cons (car l) (others (cdr l))))))))
                                (others (get cfa-sent)))))
          (cfa-send! "file" (list file text))))))
"Revision `rev` of buffer `b`, of `file`, sent, and its notes asked for."
(define* cfa-send-revision! (subr cmd-eff ((actor buffer) string int string) unit)
  (lambda (b file rev text)
    (if (letrec ((asked (subr spin ((listof cfa-pending acyclic)) bool)
                        (lambda (l) (and (pair? l) (or (and (same-actor? (extract (car l) buffer) b) (= (extract (car l) revision) rev))
                                                       (asked (cdr l)))))))
          (asked (get cfa-requests)))
        #u
        (let ((key (cfa-new-key!)))
          (begin
            (cfa-send-file! file rev text)
            (set cfa-requests (cons (product (key key) (buffer b) (revision rev)) (get cfa-requests)))
            (cfa-send! "notes" (list (int->string key) file)))))))
"Every visited FX-26 and Scheme buffer's revision sent, if it was not."
(define* cfa-send-buffers! (subr cmd-eff (buffer-infos) unit)
  (lambda (bs)
    (if (null? bs) #u
        (let ((file (extract (car bs) file)))
          (begin
            (if (cfa-file? file)
                (let ((st (actor-state (extract (car bs) actor))))
                  (cfa-send-revision! (extract (car bs) actor) file (extract st revision) (rope->string (extract st text))))
                #u)
            (cfa-send-buffers! (cdr bs)))))))

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
(set flow-eldoc (list cfa-note-at))

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

"The places an answer's fields give from the `i`th: four fields each, file,
start, end and name."
(define-type cfa-place (productof (file string) (start int) (end int) (name string)))
(define* cfa-places (subr spin (strings int) (listof cfa-place acyclic))
  (lambda (fields i)
    (let ((f (lambda ((k int)) (s7-nth-field fields k))))
      (if (string=? (f i) "") nil
          (cons (product (file (f i)) (start (s7-integer (f (+ i 1)))) (end (s7-integer (f (+ i 2)))) (name (f (+ i 3))))
                (cfa-places fields (+ i 4)))))))
(define* cfa-xref-lines (subr (maxeff (io fs-read) spin) ((listof cfa-place acyclic) cfa-texts) string)
  (lambda (ps texts)
    (if (null? ps) ""
        (string-append (place-line (extract (car ps) file) (extract (car ps) start) texts (extract (car ps) name))
                       (cfa-xref-lines (cdr ps) texts)))))

"Query `key`'s asker, taken off those waiting."
(define* cfa-take-query! (subr cmd-eff (int) (sumof (none unit) (found cfa-query)))
  (lambda (key)
    (letrec ((find (subr spin ((listof cfa-query acyclic)) (sumof (none unit) (found cfa-query)))
               (lambda (l) (cond ((null? l) (sum none #u)) ((= (extract (car l) key) key) (sum found (car l))) (else (find (cdr l))))))
             (drop (subr spin ((listof cfa-query acyclic)) (listof cfa-query acyclic))
               (lambda (l) (cond ((null? l) nil) ((= (extract (car l) key) key) (cdr l)) (else (cons (car l) (drop (cdr l))))))))
      (let ((q (find (get cfa-queries)))) (begin (set cfa-queries (drop (get cfa-queries))) q)))))

"An answer of the server's, `line`, acted on."
(define* cfa-answer! (subr cmd-eff (string) unit)
  (lambda (line)
    (let* ((sp (string-search line " " 0))
           (word (if (< sp 0) line (substring line 0 sp)))
           (fields (the strings (if (< sp 0) (list "") (s7-fields (substring line (+ sp 1) (string-length line))))))
           (key (s7-integer (car fields))))
      (cond
        ((string=? word "ready") (set cfa-ready #t))
        ((string=? word "notes")
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
             (none u #u))))
        ((string=? word "callees")
         (tagcase (cfa-take-query! key)
           (found q
             (let ((fr (extract q frame)) (unknown (string=? (s7-nth-field fields 3) "1")) (ps (cfa-places fields 4)))
               (cond ((string=? (s7-nth-field fields 2) "0") (tell! fr (echo "No call at point")))
                     ((and (pair? ps) (null? (cdr ps)) (not unknown))
                      (tell! fr (visit-position fr (extract (car ps) file) (extract (car ps) start))))
                     ((and (null? ps) (not unknown)) (tell! fr (echo "This call reaches no lambda of the program (a primitive?)")))
                     (else (tell! fr (show-xref fr (string-append "In " (extract q dir) "\n"
                                                                  "Lambdas the call can call" (if unknown " (and code not known)" "") ":\n"
                                                                  (cfa-xref-lines ps (extract q texts)))))))))
           (none u #u)))
        ((string=? word "contexts")
         (tagcase (cfa-take-query! key)
           (found q (let ((t (s7-nth-field fields 2)) (fr (extract q frame)))
                      (if (string=? t "") (tell! fr (echo "Every context sees the same here"))
                          (tell! fr (show-xref fr (string-append "In " (extract q dir) "\n"
                                                                 (letrec ((lines (subr spin (int int) string)
                                                                                   ;; Each ` ; `-separated part a line.
                                                                                   (lambda (i from)
                                                                                     (let ((k (string-search t " ; " from)))
                                                                                       (if (< k 0) (string-append (substring t from (string-length t)) "\n")
                                                                                           (string-append (substring t from k) "\n" (lines i (+ k 3))))))))
                                                                   (lines 0 0))))))))
           (none u #u)))
        ((string=? word "callers")
         (tagcase (cfa-take-query! key)
           (found q
             (let ((fr (extract q frame)))
               (if (string=? (s7-nth-field fields 2) "0") (tell! fr (echo "Not in a lambda"))
                   (tell! fr (show-xref fr (string-append "In " (extract q dir) "\n"
                                                          "Calls that can call " (s7-nth-field fields 3)
                                                          (if (string=? (s7-nth-field fields 4) "1") " (it escapes: code not known may too)" "")
                                                          ":\n"
                                                          (cfa-xref-lines (cfa-places fields 5) (extract q texts))))))))
           (none u #u)))
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
                  (else y (begin (set cfa-server nil) (set cfa-requests nil) (set cfa-askers nil) (set cfa-queries nil))))
                (and (pair? (get cfa-server))
                     (or (not (get cfa-ready)) (pair? (get cfa-requests)) (pair? (get cfa-queries)))))))))))

"The server stopped (the editor ends)."
(define* cfa-stop! (subr cmd-eff () unit)
  (lambda ()
    (let ((s (get cfa-server)))
      (if (null? s) #u (begin (process-close-input (car s)) (process-signal (car s) 1) (abandon-process! (car s))
                         (set cfa-server nil))))))

;;; ------------------------------------------------------------ buffers

"A buffer's CFA actor's state: its buffer, its file, and the revision last
seen."
(define-type cfa-state (productof (buffer (actor buffer)) (file string) (revision int)))
"Message for a CFA actor: a snapshot of its buffer, sent to the CFA if it
runs (a Scheme buffer's starts it), unless it is of the revision last seen."
(define* cfa-snapshot (subr pure (snapshot) (msg cfa-state))
  (lambda (snap)
    (lambda ((st cfa-state))
      (let ((rev (extract snap revision)) (file (extract st file)))
        (if (= rev (extract st revision))
            (same st)
            (reply-with (product (buffer (extract st buffer)) (file file) (revision rev))
                        (list (lambda ()
                                (if (or (pair? (get cfa-server)) (and (scheme-name? file) (cfa-server-up!)))
                                    (cfa-send-revision! (extract st buffer) file rev (rope->string (extract snap text)))
                                    #u)))))))))
"A buffer's CFA actor, idle, subscribed to it."
(define* cfa-attach (subr (maxeff (alloc @ed) (read @globals)) ((actor buffer) string) cmds)
  (lambda (b file)
    (let ((cx (spawn-actor (string-append "CFA of " file) (product (buffer b) (file file) (revision -1)))))
      (list (lambda () (set-class! cx idle))
            (tell b (subscribe -1 (lambda ((s snapshot)) (tell-latest cx "snapshot" (cfa-snapshot s)))))))))
(set flow-attach (list cfa-attach))

"Whether note `n` says no more than that a name holds the procedure of
that name (`sq: sq`): what s7st says of it is more."
(define* cfa-self-note? (subr spin (string) bool)
  (lambda (n) (let ((i (string-search n ": " 0)))
                (and (> i 0) (string=? (substring n 0 i) (substring n (+ i 2) (string-length n)))))))
"Eldoc in a Scheme buffer: what the CFA found at point, if it analysed
this revision and it says more than the name; else what s7st says
(scheme.fx)."
(define* cfa-scheme-eldoc (subr pure ((actor frame) (actor buffer) int int string string) cmd)
  (lambda (fr b rev p here op)
    (lambda ()
      (let ((note (cfa-note-at b rev p)))
        (if (or (string=? note "") (cfa-self-note? note)) ((s7-eldoc fr b rev p here op)) (tell! fr (eldoc-show note)))))))
(set scheme-eldoc (list cfa-scheme-eldoc))

;;; ------------------------------------------------------------ commands

"A frame command on the selected buffer, an FX-26 or Scheme file's: the
server started, every buffer's latest revision sent, then `then` of the
frame, the buffer, its file, revision and point, and the buffers' texts."
(define* with-cfa (subr pure ((subr cmd-eff ((actor frame) (actor buffer) string int int cfa-texts) unit)) frame-action)
  (lambda (then)
    (lambda ((fr (actor frame)) (f frame))
      (let* ((b (extract (selected-window f) buffer))
             (st (actor-state b))
             (file (extract st file))
             (bs (extract f buffers))
             (texts (buffer-texts bs)))
        (if (not (cfa-file? file))
            (draw (with-echo f "Not an FX-26 or Scheme file"))
            (reply-with f (list (lambda ()
                                  (if (cfa-server-up!)
                                      (begin (cfa-send-buffers! bs)
                                        (then fr b file (extract st revision) (extract st point) texts))
                                      (tell! fr (echo "The CFA could not be started (../bin/cfa)")))))))))))

"C-c f: the CFA's note at point."
(define* cfa-at-point (subr pure () frame-action)
  (lambda ()
    (with-cfa (lambda ((fr (actor frame)) (b (actor buffer)) (file string) (rev int) (p int) (texts cfa-texts))
                (let ((n (cfa-note-at b rev p)))
                  (if (not (string=? n "")) (tell! fr (echo n))
                      (begin
                        (set cfa-askers (cons (product (frame fr) (buffer b) (revision rev) (point p)) (get cfa-askers)))
                        (tell! fr (echo "The CFA is analysing..."))
                        (cfa-tell-askers!))))))))

"C-c e and C-c r: query `word` of the server at point, its answer listed."
(define* cfa-query-at-point (subr pure (string) frame-action)
  (lambda (word)
    (with-cfa (lambda ((fr (actor frame)) (b (actor buffer)) (file string) (rev int) (p int) (texts cfa-texts))
                (let ((key (cfa-new-key!)))
                  (begin
                    (set cfa-queries (cons (product (key key) (frame fr) (dir (directory-of file)) (texts texts)) (get cfa-queries)))
                    (cfa-send! word (list (int->string key) file (int->string p)))
                    (tell! fr (echo "The CFA is analysing..."))))))))

(define-command! "cfa-at-point" (sum on-frame (cfa-at-point)))
(define-command! "cfa-callees" (sum on-frame (cfa-query-at-point "callees")))
(define-command! "cfa-callers" (sum on-frame (cfa-query-at-point "callers")))
(define-command! "cfa-contexts" (sum on-frame (cfa-query-at-point "contexts")))
(define-key! "C-c f" "cfa-at-point")
(define-key! "C-c e" "cfa-callees")
(define-key! "C-c r" "cfa-callers")
(define-key! "C-c d" "cfa-contexts")
