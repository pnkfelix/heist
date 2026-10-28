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
;;;   depth N             the depth of analyses from now (m-CFA; 0: 0CFA)
;;; Answers:
;;;   ready WHY           started: WHY empty, or why it did not
;;;   notes KEY PATH NOTES  each a line `start end text` (notes.fx)
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
(define-type cf-world-notes (productof (key string) (files (listof cf-file-notes-of acyclic))))
(define-type cf-request-of (productof (key string) (path string)))
(define-type cf-job (productof (key string) (paths strings)))

(define cf-dataset (ref (listof cf-text acyclic) @cf) (new nil))
"Worlds analysed as the dataset has them: their files' notes."
(define cf-analysed (ref (listof cf-world-notes acyclic) @cf) (new nil))
(define cf-pending (ref (listof cf-request-of acyclic) @cf) (new nil))
(define cf-job-now (ref (sumof (none unit) (job cf-job)) @cf) (new (the (sumof (none unit) (job cf-job)) (sum none #u))))
(define cf-serve-depth (ref int @cf) (new 0))

;;; ------------------------------------------------------------ lines

(define* cf-escape (subr spin (string) string)
  (lambda (s)
    (letrec ((go (subr spin (int strings) strings)
               (lambda (i acc)
                 (if (>= i (string-length s)) (reverse acc)
                     (let ((c (string-ref s i)))
                       (go (+ i 1) (cons (cond ((char=? c #\\) "\\\\") ((char=? c #\newline) "\\n") ((char=? c #\tab) "\\t")
                                               (else (char->string c)))
                                         acc)))))))
      (cf-concat (go 0 nil) ""))))
(define* cf-unescape (subr spin (string) string)
  (lambda (s)
    (letrec ((go (subr spin (int strings) strings)
               (lambda (i acc)
                 (cond ((>= i (string-length s)) (reverse acc))
                       ((and (char=? (string-ref s i) #\\) (< (+ i 1) (string-length s)))
                        (let ((c (string-ref s (+ i 1))))
                          (go (+ i 2) (cons (cond ((char=? c #\n) "\n") ((char=? c #\t) "\t") (else (char->string c))) acc))))
                       (else (go (+ i 1) (cons (char->string (string-ref s i)) acc)))))))
      (cf-concat (go 0 nil) ""))))
"Line `s` split at `sep`."
(define* cf-split (subr spin (string char) strings)
  (lambda (s sep)
    (letrec ((go (subr spin (int int strings) strings)
               (lambda (i start acc)
                 (cond ((>= i (string-length s)) (reverse (the strings (cons (substring s start i) acc))))
                       ((char=? (string-ref s i) sep) (go (+ i 1) (+ i 1) (cons (substring s start i) acc)))
                       (else (go (+ i 1) start acc))))))
      (go 0 0 nil))))
(define* cf-answer (subr (maxeff spin (io stdout)) (string strings) unit)
  (lambda (word fields)
    (begin (write-out (string-append word " " (cf-concat (letrec ((go (subr spin (strings) strings)
                                                                      (lambda (l) (if (null? l) nil (cons (cf-escape (car l)) (go (cdr l)))))))
                                                             (go fields))
                                                           "\t")
                                     "\n"))
      #u)))

;;; ------------------------------------------------------------ worlds

(define* cf-directory-of (subr spin (string) string)
  (lambda (p) (letrec ((go (subr spin (int) string)
                         (lambda (i) (cond ((< i 0) "") ((char=? (string-ref p i) #\/) (substring p 0 (+ i 1))) (else (go (- i 1)))))))
                (go (- (string-length p) 1)))))
"The world of `path`: its key."
(define* cf-world-key (subr spin (string) string)
  (lambda (p) (if (cf-scheme-file? p) (string-append "scheme:" p) (string-append "fx26:" (cf-directory-of p)))))
(define* insert-string (subr spin (string strings) strings)
  (lambda (s l) (if (or (null? l) (string<? s (car l))) (cons s l) (cons (car l) (insert-string s (cdr l))))))
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
                                                            (go (cdr l) (insert-string (string-append dir (car l)) acc)))
                                                           (else (go (cdr l) acc))))))
                        (go ns nil)))
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

(define* cf-world-notes-of (subr (maxeff spin (read @cf)) (string) (sumof (none unit) (some (listof cf-file-notes-of acyclic))))
  (lambda (key) (letrec ((go (subr (maxeff (read @cf) spin) ((listof cf-world-notes acyclic)) (sumof (none unit) (some (listof cf-file-notes-of acyclic))))
                           (lambda (l) (cond ((null? l) (sum none #u))
                                             ((string=? (extract (car l) key) key) (sum some (extract (car l) files)))
                                             (else (go (cdr l)))))))
                  (go (get cf-analysed)))))

"Notes `ns`, as an answer's field: a line each."
(define* cf-notes-field (subr spin (cf-notes) string)
  (lambda (ns) (cf-concat (letrec ((go (subr spin (cf-notes) strings)
                                     (lambda (l) (if (null? l) nil
                                                     (cons (string-append (int->string (extract (car l) start)) " " (int->string (extract (car l) end)) " "
                                                                          (extract (car l) text))
                                                           (go (cdr l)))))))
                            (go ns))
                          "\n")))

"The requests whose worlds are analysed, answered; the others kept."
(define* cf-answer-pending! (subr (maxeff cf-eff (io stdout)) () unit)
  (lambda ()
    (set cf-pending
         (letrec ((go (subr (maxeff cf-eff (io stdout)) ((listof cf-request-of acyclic)) (listof cf-request-of acyclic))
                    (lambda (l)
                      (if (null? l) nil
                          (let ((r (car l)))
                            (tagcase (cf-world-notes-of (cf-world-key (extract r path)))
                              (some fs (begin
                                         (cf-answer "notes" (list (extract r key) (extract r path)
                                                                  (letrec ((find (subr spin ((listof cf-file-notes-of acyclic)) cf-notes)
                                                                                 (lambda (l) (cond ((null? l) nil)
                                                                                                   ((string=? (extract (car l) path) (extract r path)) (extract (car l) notes))
                                                                                                   (else (find (cdr l)))))))
                                                                    (cf-notes-field (find fs)))))
                                         (go (cdr l))))
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
                   (paths (cf-world-files key))
                   (texts (letrec ((go (subr (maxeff (io fs-read) spin (read @cf)) (strings) strings)
                                         (lambda (l) (if (null? l) nil (cons (cf-dataset-text (car l)) (go (cdr l)))))))
                            (go paths))))
              (begin
                (if (and (>= (string-length key) 7) (string=? (substring key 0 7) "scheme:"))
                    (cf-start! cf-scheme (sc-world paths texts) (get cf-serve-depth))
                    (cf-start! cf-fx26 (fx-world paths texts) (get cf-serve-depth)))
                (set cf-job-now (sum job (product (key key) (paths paths)))))))))))

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
                                                            (go (extract j paths)))))
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
                         (go (cf-split (substring line (+ sp 1) (string-length line)) #\tab)))))
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
             (cf-invalidate! (cf-world-key p)))))
        ((string=? word "forget")
         (let ((p (field 0)))
           (begin
             (set cf-dataset (letrec ((go (subr spin ((listof cf-text acyclic)) (listof cf-text acyclic))
                                        (lambda (l) (cond ((null? l) nil) ((string=? (extract (car l) path) p) (go (cdr l))) (else (cons (car l) (go (cdr l))))))))
                               (go (get cf-dataset))))
             (cf-invalidate! (cf-world-key p)))))
        ((string=? word "notes")
         (begin (set cf-pending (append (get cf-pending) (list (product (key (field 0)) (path (field 1))))))
           (cf-answer-pending!)))
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
