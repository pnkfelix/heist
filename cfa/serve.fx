;;; serve.fx: the CFA as a server (`bin/cfa --serve`), for a client such as
;;; the editor: requests on standard input, answers on standard output, a
;;; line each, as s7st's server's (s7st/main.fx): a word, a space, then
;;; fields separated by tabs, each with its backslashes, newlines and tabs
;;; escaped (\\, \n, \t).
;;;
;;; The dataset is texts by file name, of either language. A file's world
;;; is what is analysed with it: an FX-26 file's, every `.fx` file of its
;;; directory (as editor/calls.fx has it); a Scheme file's, itself. A text
;;; the dataset has is used in place of the file's.
;;;
;;; Requests:
;;;   file PATH TEXT      the dataset's text of PATH, now TEXT
;;;   forget PATH         PATH's text out of the dataset (the file's used)
;;;   notes KEY PATH      PATH's notes, answered once its world is analysed
;;;                       as the dataset has it now; KEY is given back
;;;   callees KEY PATH POS  the lambdas the innermost call around POS (in
;;;                       PATH, characters) can call, answered so too
;;;   callers KEY PATH POS  the calls that can call the innermost lambda
;;;                       around POS
;;;   contexts KEY PATH POS what the innermost variable or call around POS
;;;                       is in each context, where contexts differ
;;;   depth N             the depth of analyses from now (m-CFA; 0: 0CFA)
;;;   status              how the analysis that runs is doing
;;; Answers:
;;;   ready WHY           started: WHY empty, or why it did not
;;;   status WORLD TEXT   a `status`'s answer: the world analysed (empty:
;;;                       none), and engine.fx's `cf-status`
;;;   notes KEY PATH NOTES  each a line `start end text` (notes.fx)
;;;   callees KEY PATH FOUND UNKNOWN PLACE…
;;;                       FOUND 1 if there is a call around POS, else 0;
;;;                       UNKNOWN 1 if it may call code not known; each
;;;                       PLACE, a lambda it can call: four fields, PATH
;;;                       START END NAME
;;;   contexts KEY PATH TEXT  a `contexts`'s answer: notes.fx's context
;;;                       note there (`x: in line 4: inc ; in line 5: dec`),
;;;                       empty if none
;;;   callers KEY PATH FOUND NAME ESCAPED PLACE…
;;;                       the lambda's NAME (FOUND 0: none around POS);
;;;                       ESCAPED 1 if code not known may call it too; each
;;;                       PLACE a call that can call it, PATH START END and
;;;                       an empty NAME
;;;
;;; An analysis runs a slice at a time, requests read between slices: one
;;; that changes its world stops it, and it starts again.

(define* cf-text-of-file (subr (maxeff (io fs-read) spin) (string) string)
  (lambda (f) (tagcase (read-file f) (data d (tagcase (utf8->string d) (text s s) (else y ""))) (else y ""))))
"The number `s` writes in decimal (0 if none)."
(define* cf-decimal (subr spin (string) int)
  (lambda (s) (letrec ((go (subr spin (int int) int)
                         (lambda (i acc) (if (>= i (string-length s)) acc
                                             (let ((d (- (char->integer (string-ref s i)) 48)))
                                               (if (and (>= d 0) (<= d 9)) (go (+ i 1) (+ (* acc 10) d)) acc))))))
                (go 0 0))))
"Whether `path` names a Scheme file, by its name."
(define* cf-scheme-file? (subr spin (string) bool)
  (lambda (p) (let ((n (string-length p)))
                (letrec ((ends (subr spin (strings) bool)
                           (lambda (l) (and (pair? l) (or (and (>= n (string-length (car l))) (string=? (substring p (- n (string-length (car l))) n) (car l)))
                                                          (ends (cdr l)))))))
                  (ends (list ".scm" ".sld" ".ss" ".sps" ".sch"))))))

(define-effect cf-serve-eff (maxeff fx-eff sc-eff (io fs-read) (io stdout) (io stdin) spin))

(define-type cf-text (productof (path string) (text string)))
(define-type cf-file-notes-of (productof (path string) (notes cf-notes)))
"A place in a file: a lambda's (named) or a call's."
(define-type cf-place (productof (path string) (start int) (end int) (name string)))
"What an analysed world keeps: each file's notes; each lambda, by number,
its place and whether it escaped; each call, its place, the lambdas it can
call, and whether it may call code not known."
(define-type cf-lambda-found (productof (place cf-place) (escaped bool)))
(define-type cf-call-found (productof (place cf-place) (callees ints) (unknown bool)))
(define-type cf-world-notes
  (productof (key string) (files (listof cf-file-notes-of acyclic)) (contexts (listof cf-file-notes-of acyclic))
             (lambdas (arrayof cf-lambda-found @cf)) (calls (listof cf-call-found acyclic))))
"A request waiting for its world: `notes`, `callees` or `callers`."
(define-type cf-request-of (productof (kind string) (key string) (path string) (pos int)))
(define-type cf-job (productof (key string) (paths strings)))

(define cf-dataset (ref (listof cf-text acyclic) @cf) (new nil))
"Worlds analysed as the dataset has them: their files' notes."
(define cf-analysed (ref (listof cf-world-notes acyclic) @cf) (new nil))
(define cf-pending (ref (listof cf-request-of acyclic) @cf) (new nil))
(define cf-job-now (ref (sumof (none unit) (job cf-job)) @cf) (new (the (sumof (none unit) (job cf-job)) (sum none #u))))
(define cf-serve-depth (ref int @cf) (new 0))

;;; ------------------------------------------------------------ lines

"`s` with backslashes, newlines and tabs escaped; and back."
(define* cf-escape (subr spin (string) string)
  (lambda (s)
    (letrec ((go (subr spin (int (listof char acyclic)) (listof char acyclic))
               (lambda (i acc)
                 (if (>= i (string-length s)) acc
                     (let ((c (string-ref s i)))
                       (go (+ i 1) (cond ((char=? c #\\) (cons #\\ (cons #\\ acc)))
                                         ((char=? c #\newline) (cons #\n (cons #\\ acc)))
                                         ((char=? c #\tab) (cons #\t (cons #\\ acc)))
                                         (else (cons c acc)))))))))
      (reverse-list->string (go 0 nil)))))
(define* cf-unescape (subr spin (string) string)
  (lambda (s)
    (letrec ((go (subr spin (int (listof char acyclic)) (listof char acyclic))
               (lambda (i acc)
                 (cond ((>= i (string-length s)) acc)
                       ((and (char=? (string-ref s i) #\\) (< (+ i 1) (string-length s)))
                        (let ((c (string-ref s (+ i 1))))
                          (go (+ i 2) (cons (cond ((char=? c #\n) #\newline) ((char=? c #\t) #\tab) (else c)) acc))))
                       (else (go (+ i 1) (cons (string-ref s i) acc)))))))
      (reverse-list->string (go 0 nil)))))
(define* cf-answer (subr (maxeff spin (io stdout)) (string strings) unit)
  (lambda (word fields)
    (begin (write-out (string-append word " " (string-join (letrec ((go (subr spin (strings) strings)
                                                                      (lambda (l) (if (null? l) nil (cons (cf-escape (car l)) (go (cdr l)))))))
                                                             (go fields)) "\t")
                                     "\n"))
      #u)))

;;; ------------------------------------------------------------ worlds

"The world of `path`: its key."
(define* cf-world-key (subr spin (string) string)
  (lambda (p) (if (cf-scheme-file? p) (string-append "scheme:" p) (string-append "fx26:" (cf-directory-of p)))))
"The files of world `key`, sorted."
(define* cf-world-files (subr (maxeff (io fs-read) spin (alloc @cf)) (string) strings)
  (lambda (key)
    (if (and (>= (string-length key) 7) (string=? (substring key 0 7) "scheme:"))
        (list (substring key 7 (string-length key)))
        (let ((dir (substring key 5 (string-length key))))
          (tagcase (the (sumof (names (listof string @cf)) (failed io-error)) (list-dir (if (string=? dir "") "." dir)))
            (names ns (letrec ((go (subr (maxeff spin (read @cf) (read @globals)) ((listof string @cf) strings) strings)
                                     (lambda (l acc) (cond ((null? l) acc)
                                                           ((let ((n (string-length (car l)))) (and (> n 3) (string=? (substring (car l) (- n 3) n) ".fx")))
                                                            (go (cdr l) (cons (string-append dir (car l)) acc)))
                                                           (else (go (cdr l) acc))))))
                        (list-sort string<? (go ns nil))))
            (else y nil))))))
(define* cf-dataset-text (subr (maxeff (io fs-read) spin (read @cf)) (string) string)
  (lambda (p) (letrec ((go (subr (maxeff (io fs-read) spin (read @cf)) ((listof cf-text acyclic)) string)
                         (lambda (l) (cond ((null? l) (cf-text-of-file p))
                                           ((string=? (extract (car l) path) p) (extract (car l) text))
                                           (else (go (cdr l)))))))
                (go (get cf-dataset)))))

"World `key` out of those analysed (its dataset changed), and its
analysis, if it runs, stopped."
(define* cf-invalidate! (subr cf-eff (string) unit)
  (lambda (key)
    (begin
      (set cf-analysed (letrec ((go (subr spin ((listof cf-world-notes acyclic)) (listof cf-world-notes acyclic))
                                  (lambda (l) (cond ((null? l) nil) ((string=? (extract (car l) key) key) (go (cdr l)))
                                                    (else (cons (car l) (go (cdr l))))))))
                         (go (get cf-analysed))))
      (tagcase (get cf-job-now)
        (job j (if (string=? (extract j key) key) (set cf-job-now (sum none #u)) #u))
        (else y #u)))))

"Notes `ns`, as an answer's field: a line each."
(define* cf-notes-field (subr spin (cf-notes) string)
  (lambda (ns) (string-join (letrec ((go (subr spin (cf-notes) strings)
                                     (lambda (l) (if (null? l) nil
                                                     (cons (string-append (int->string (extract (car l) start)) " " (int->string (extract (car l) end)) " "
                                                                          (extract (car l) text))
                                                           (go (cdr l)))))))
                            (go ns)) "\n")))

"Every world file `path` is of (its own, and those importing it, a
library) out of those analysed, and the analysis that runs, if it is of
one, stopped: `path`'s text changed."
(define* cf-invalidate-path! (subr cf-eff (string) unit)
  (lambda (path)
    (begin
      (set cf-analysed (letrec ((has (subr spin ((listof cf-file-notes-of acyclic)) bool)
                                  (lambda (l) (and (pair? l) (or (string=? (extract (car l) path) path) (has (cdr l))))))
                                (go (subr spin ((listof cf-world-notes acyclic)) (listof cf-world-notes acyclic))
                                  (lambda (l) (cond ((null? l) nil) ((has (extract (car l) files)) (go (cdr l)))
                                                    (else (cons (car l) (go (cdr l))))))))
                         (go (get cf-analysed))))
      (tagcase (get cf-job-now)
        (job j (if (member? path (extract j paths) string=?) (set cf-job-now (sum none #u)) #u))
        (else y #u))
      (cf-invalidate! (cf-world-key path)))))
(define* cf-world-notes-of (subr (maxeff spin (read @cf)) (string) (sumof (none unit) (some cf-world-notes)))
  (lambda (key) (letrec ((go (subr (maxeff (read @cf) spin) ((listof cf-world-notes acyclic)) (sumof (none unit) (some cf-world-notes)))
                           (lambda (l) (cond ((null? l) (sum none #u))
                                             ((string=? (extract (car l) key) key) (sum some (car l)))
                                             (else (go (cdr l)))))))
                  (go (get cf-analysed)))))

(define* cf-place-fields (subr spin (cf-place) strings)
  (lambda (p) (list (extract p path) (int->string (extract p start)) (int->string (extract p end)) (extract p name))))
(define* cf-place-holds? (subr spin (cf-place string int) bool)
  (lambda (p path pos) (and (string=? (extract p path) path) (<= (extract p start) pos) (<= pos (extract p end)))))
(define* cf-place-size (subr pure (cf-place) int) (lambda (p) (- (extract p end) (extract p start))))
(define* cf-flag (subr pure (bool) string) (lambda (b) (if b "1" "0")))

"The answer to request `r`, of world `w` analysed."
(define* cf-answer-request! (subr (maxeff spin (io stdout) (read @cf)) (cf-request-of cf-world-notes) unit)
  (lambda (r w)
    (let ((path (extract r path)) (pos (extract r pos)) (kind (extract r kind)))
      (cond
        ((string=? kind "notes")
         (cf-answer "notes" (list (extract r key) path
                                  (letrec ((find (subr spin ((listof cf-file-notes-of acyclic)) cf-notes)
                                                 (lambda (l) (cond ((null? l) nil)
                                                                   ((string=? (extract (car l) path) path) (extract (car l) notes))
                                                                   (else (find (cdr l)))))))
                                    (cf-notes-field (find (extract w files)))))))
        ((string=? kind "contexts")
         ;; The narrowest context note around `pos`.
         (cf-answer "contexts"
                    (list (extract r key) path
                          (letrec ((find (subr spin ((listof cf-file-notes-of acyclic)) cf-notes)
                                         (lambda (l) (cond ((null? l) nil) ((string=? (extract (car l) path) path) (extract (car l) notes)) (else (find (cdr l))))))
                                   (best (subr spin (cf-notes string int) string)
                                     (lambda (l t size)
                                       (cond ((null? l) t)
                                             ((and (<= (extract (car l) start) pos) (<= pos (extract (car l) end))
                                                   (or (< size 0) (< (- (extract (car l) end) (extract (car l) start)) size)))
                                              (best (cdr l) (extract (car l) text) (- (extract (car l) end) (extract (car l) start))))
                                             (else (best (cdr l) t size))))))
                            (best (find (extract w contexts)) "" -1)))))
        ((string=? kind "callees")
         ;; The innermost call around `pos`.
         (let ((best (letrec ((go (subr spin ((listof cf-call-found acyclic) (sumof (none unit) (call cf-call-found))) (sumof (none unit) (call cf-call-found)))
                                (lambda (l best)
                                  (cond ((null? l) best)
                                        ((and (cf-place-holds? (extract (car l) place) path pos)
                                              (tagcase best (call b (< (cf-place-size (extract (car l) place)) (cf-place-size (extract b place)))) (else y #t)))
                                         (go (cdr l) (sum call (car l))))
                                        (else (go (cdr l) best))))))
                       (go (extract w calls) (sum none #u)))))
           (tagcase best
             (call c (cf-answer "callees"
                                (append (list (extract r key) path "1" (cf-flag (extract c unknown)))
                                        (letrec ((go (subr (maxeff spin (read @cf)) (ints) strings)
                                                   (lambda (l) (if (null? l) nil
                                                                   (append (cf-place-fields (extract (array-ref (extract w lambdas) (car l)) place)) (go (cdr l)))))))
                                          (go (extract c callees))))))
             (else y (cf-answer "callees" (list (extract r key) path "0" "0"))))))
        ((string=? kind "callers")
         ;; The innermost lambda around `pos`.
         (let* ((ls (extract w lambdas))
                (best (letrec ((go (subr (maxeff spin (read @cf)) (int int) int)
                                 (lambda (i best)
                                   (if (>= i (array-length ls)) best
                                       (let ((p (extract (array-ref ls i) place)))
                                         (go (+ i 1)
                                             (if (and (cf-place-holds? p path pos)
                                                      (or (< best 0) (< (cf-place-size p) (cf-place-size (extract (array-ref ls best) place)))))
                                                 i best)))))))
                        (go 0 -1))))
           (if (< best 0)
               (cf-answer "callers" (list (extract r key) path "0" "" "0"))
               (cf-answer "callers"
                          (append (list (extract r key) path "1" (extract (extract (array-ref ls best) place) name)
                                        (cf-flag (extract (array-ref ls best) escaped)))
                                  (letrec ((go (subr spin ((listof cf-call-found acyclic)) strings)
                                             (lambda (l) (cond ((null? l) nil)
                                                               ((member? best (extract (car l) callees) =)
                                                                (append (cf-place-fields (extract (car l) place)) (go (cdr l))))
                                                               (else (go (cdr l)))))))
                                    (go (extract w calls))))))))
        (else #u)))))

"The requests whose worlds are analysed, answered; the others kept."
(define* cf-answer-pending! (subr (maxeff cf-eff (io stdout)) () unit)
  (lambda ()
    (set cf-pending
         (letrec ((go (subr (maxeff cf-eff (io stdout)) ((listof cf-request-of acyclic)) (listof cf-request-of acyclic))
                    (lambda (l)
                      (if (null? l) nil
                          (let ((r (car l)))
                            (tagcase (cf-world-notes-of (cf-world-key (extract r path)))
                              (some w (begin (cf-answer-request! r w) (go (cdr l))))
                              (else y (cons r (go (cdr l))))))))))
           (go (get cf-pending))))))

"An analysis started, if none runs and a request waits for one."
(define* cf-schedule! (subr cf-serve-eff () unit)
  (lambda ()
    (tagcase (get cf-job-now)
      (job j #u)
      (else y
        (if (null? (get cf-pending)) #u
            (let* ((key (cf-world-key (extract (car (get cf-pending)) path)))
                   (scheme (and (>= (string-length key) 7) (string=? (substring key 0 7) "scheme:")))
                   (texts-of (lambda ((ps strings))
                               (letrec ((go (subr (maxeff (io fs-read) spin (read @cf)) (strings) strings)
                                              (lambda (l) (if (null? l) nil (cons (cf-dataset-text (car l)) (go (cdr l)))))))
                                 (go ps))))
                   (own (cf-world-files key))
                   ;; A Scheme file's world: the libraries it imports too (scheme.fx).
                   (paths (if scheme
                              (letrec ((go (subr spin ((listof sc-world-file acyclic)) strings)
                                             (lambda (l) (if (null? l) nil (cons (extract (car l) path) (go (cdr l)))))))
                                (go (sc-world-files own (texts-of own))))
                              own))
                   (texts (texts-of paths)))
              (begin
                (if scheme
                    (cf-start! cf-scheme (sc-world paths texts) (get cf-serve-depth))
                    (cf-start! cf-fx26 (fx-world paths texts) (get cf-serve-depth)))
                (set cf-job-now (sum job (product (key key) (paths paths)))))))))))

"Where span `sp` is, as a place named `name`."
(define* cf-span-place (subr cf-eff (cf-span string) cf-place)
  (lambda (sp name) (product (path (cf-file-name (extract sp file))) (start (extract sp start)) (end (extract sp end)) (name name))))
"The world just analysed's lambdas, as places, and whether each escaped."
(define* cf-lambdas-found (subr cf-eff () (arrayof cf-lambda-found @cf))
  (lambda ()
    (let* ((ls (get cf-lambda-array))
           (a (the (arrayof cf-lambda-found @cf) (make-array (array-length ls) (product (place (product (path "") (start 0) (end 0) (name ""))) (escaped #f))))))
      (letrec ((go (subr cf-eff (int) (arrayof cf-lambda-found @cf))
                 (lambda (i) (if (>= i (array-length ls)) a
                                 (let ((info (array-ref ls i)))
                                   (begin (array-set! a i (product (place (cf-span-place (extract info span) (extract info name)))
                                                                   (escaped (= (table-ref (get cf-escaped) i 0) 1))))
                                     (go (+ i 1))))))))
        (go 0)))))
"The world just analysed's calls: each its place, the lambdas it can call
(each once), and whether it may call code not known."
(define* cf-calls-found (subr cf-eff () (listof cf-call-found acyclic))
  (lambda ()
    (letrec ((go (subr cf-eff ((listof call-info acyclic) int (listof cf-call-found acyclic)) (listof cf-call-found acyclic))
               (lambda (cs i acc)
                 (if (null? cs) acc
                     (let* ((ops (table-ref (get cf-callees) i nil))
                            (ls (delete-duplicates (map (lambda ((v int)) (closure-lambda (quotient v 4))) (filter closure-val? ops)) =)))
                       (go (cdr cs) (- i 1)
                           (cons (product (place (cf-span-place (extract (car cs) span) "")) (callees ls) (unknown (vals-has? ops cf-unknown)))
                                 acc)))))))
      (go (get cf-calls) (- (length (get cf-calls)) 1) nil))))

"A slice of the analysis that runs; if it is done, its world's notes kept,
and the requests waiting on them answered."
(define* cf-slice! (subr (maxeff cf-eff (io stdout)) () unit)
  (lambda ()
    (tagcase (get cf-job-now)
      (job j (if (cf-step! 2000)
                 (begin
                   (set cf-analysed (cons (product (key (extract j key))
                                                   (files (letrec ((go (subr cf-eff (strings) (listof cf-file-notes-of acyclic))
                                                                         (lambda (ps) (if (null? ps) nil
                                                                                          (let ((n (cf-file-notes (cf-file (car ps)))))
                                                                                            (cons (product (path (car ps)) (notes n)) (go (cdr ps))))))))
                                                            (go (extract j paths))))
                                                   (contexts (letrec ((go (subr cf-eff (strings) (listof cf-file-notes-of acyclic))
                                                                            (lambda (ps) (if (null? ps) nil
                                                                                             (let ((n (cf-file-context-notes (cf-file (car ps)))))
                                                                                               (cons (product (path (car ps)) (notes n)) (go (cdr ps))))))))
                                                               (go (extract j paths))))
                                                   (lambdas (cf-lambdas-found))
                                                   (calls (cf-calls-found)))
                                          (get cf-analysed)))
                   (set cf-job-now (sum none #u))
                   (cf-answer-pending!))
                 #u))
      (else y #u))))

(define* cf-serve-request! (subr cf-serve-eff (string) unit)
  (lambda (line)
    (let* ((sp (letrec ((go (subr spin (int) int) (lambda (i) (cond ((>= i (string-length line)) i) ((char=? (string-ref line i) #\space) i) (else (go (+ i 1)))))))
                 (go 0)))
           (word (substring line 0 sp))
           (fields (if (>= sp (string-length line)) nil
                       (letrec ((go (subr spin (strings) strings) (lambda (l) (if (null? l) nil (cons (cf-unescape (car l)) (go (cdr l)))))))
                         (go (string-split (substring line (+ sp 1) (string-length line)) #\tab)))))
           (field (lambda ((i int)) (letrec ((nth (subr spin (strings int) string) (lambda (l k) (cond ((null? l) "") ((= k 0) (car l)) (else (nth (cdr l) (- k 1)))))))
                                      (nth fields i)))))
      (cond
        ((string=? word "file")
         (let ((p (field 0)))
           (begin
             (set cf-dataset (cons (product (path p) (text (field 1)))
                                   (letrec ((go (subr spin ((listof cf-text acyclic)) (listof cf-text acyclic))
                                              (lambda (l) (cond ((null? l) nil) ((string=? (extract (car l) path) p) (go (cdr l))) (else (cons (car l) (go (cdr l))))))))
                                     (go (get cf-dataset)))))
             (cf-invalidate-path! p))))
        ((string=? word "forget")
         (let ((p (field 0)))
           (begin
             (set cf-dataset (letrec ((go (subr spin ((listof cf-text acyclic)) (listof cf-text acyclic))
                                        (lambda (l) (cond ((null? l) nil) ((string=? (extract (car l) path) p) (go (cdr l))) (else (cons (car l) (go (cdr l))))))))
                               (go (get cf-dataset))))
             (cf-invalidate-path! p))))
        ((or (string=? word "notes") (string=? word "callees") (string=? word "callers") (string=? word "contexts"))
         (begin (set cf-pending (append (get cf-pending) (list (product (kind word) (key (field 0)) (path (field 1)) (pos (cf-decimal (field 2)))))))
           (cf-answer-pending!)))
        ((string=? word "status")
         (cf-answer "status" (list (tagcase (get cf-job-now) (job j (extract j key)) (else y "")) (cf-status))))
        ((string=? word "depth")
         (begin (set cf-serve-depth (cf-decimal (field 0)))
           (set cf-analysed nil) (set cf-job-now (sum none #u))))
        (else #u)))))

"The server: requests read, and analyses run a slice at a time, requests
read between slices. Its exit status, when its input ends."
(define* cf-serve (subr cf-serve-eff () int)
  (lambda ()
    (let ((next (lambda ()
                  (tagcase (read-line)
                    (line l (begin (cf-serve-request! l) #t))
                    (else y #f)))))
      (begin
        (cf-schedule!)
        (tagcase (get cf-job-now)
          (job j (begin (cf-slice!) (if (stdin-ready?) (if (next) (cf-serve) 0) (cf-serve))))
          (else y (if (next) (cf-serve) 0)))))))
