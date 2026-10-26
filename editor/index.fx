;;; index.fx: the definitions of the FX-26 files around those visited
;;; (cahoots' `(yank actor index)`, c337e2a, in its first form).
;;;
;;; An actor of the idle class. Told a directory, it lists the `.fx` files
;;; in it, and reads them one a turn -- each read a command after its turn,
;;; by Fixpt's own reader, as the syntax actor reads a buffer -- so keys
;;; are read between files. M-. looks in the buffers first, then here.

(define-type indexed (productof (file string) (definitions definitions) (links links)))
(define-type index-state
  (productof (directories strings) (pending strings) (files (listof indexed acyclic))))

"The index, once main has made it: a list of none or one, since an actor
cannot be in a union."
(define the-index (ref (listof (actor index-state) acyclic) @ed) (new nil))

(define* index-of (subr pure (index-state strings strings (listof indexed acyclic)) index-state)
  (lambda (st dirs pending files)
    (product (directories dirs) (pending pending) (files files))))

(define* text-of-file (subr (maxeff (io fs-read) spin) (string) string)
  (lambda (f)
    (tagcase (read-file f)
      (data d (tagcase (utf8->string d) (text s s) (else y "")))
      (else y ""))))

"Message for the index: the file read, and its definitions; then the next."
(define* index-entry (subr pure ((actor index-state) string annotation) (msg index-state))
  (lambda (ix file a)
    (lambda ((st index-state))
      (same (index-of st (extract st directories) (extract st pending)
                      (cons (product (file file) (definitions (extract a definitions)) (links (extract a links)))
                            (extract st files)))))))

"Message for the index: read the next file waiting, if any."
(define* index-next (subr pure ((actor index-state)) (msg index-state))
  (lambda (ix)
    (lambda ((st index-state))
      (let ((p (extract st pending)))
        (if (null? p)
            (same st)
            (let ((file (car p)))
              (reply-with (index-of st (extract st directories) (cdr p) (extract st files))
                          (list (lambda ()
                                  (begin
                                    (tell! ix (index-entry ix file (analyze (text-of-file file) 0)))
                                    (tell! ix (index-next ix))))))))))))

"Message for the index: these files to read too."
(define* index-files (subr pure ((actor index-state) strings) (msg index-state))
  (lambda (ix files)
    (lambda ((st index-state))
      (reply-with (index-of st (extract st directories) (append (extract st pending) files) (extract st files))
                  (if (null? (extract st pending)) (list (tell ix (index-next ix))) nil)))))

"Message for the index: the `.fx` files of directory `dir` (ending in
`/`), unless it has been told it already."
(define* index-directory (subr pure ((actor index-state) string) (msg index-state))
  (lambda (ix dir)
    (lambda ((st index-state))
      (if (member? dir (extract st directories))
          (same st)
          (reply-with (index-of st (cons dir (extract st directories)) (extract st pending) (extract st files))
                      (list (lambda ()
                              (tagcase (the (sumof (names (listof string @ix)) (failed io-error)) (list-dir dir))
                                (names ns
                                  (tell! ix (index-files ix
                                                         (letrec ((go (subr (maxeff (read @ix) spin) ((listof string @ix)) strings)
                                                                    (lambda (l)
                                                                      (cond ((null? l) nil)
                                                                            ((fx26-file? (car l)) (cons (string-append dir (car l)) (go (cdr l))))
                                                                            (else (go (cdr l)))))))
                                                           (go ns)))))
                                (else y #u)))))))))

"Where `name` is defined in the index: a file, a position, and the file a
name imported there comes from (\"\" if it is not imported)."
(define-type index-hit (productof (file string) (at int) (link string)))
(define* index-lookup (subr turn-eff (string) (sumof (none unit) (found index-hit)))
  (lambda (name)
    (let ((ixs (get the-index)))
      (if (null? ixs)
          (sum none #u)
          (letrec ((link-at (subr spin (links int) string)
                     (lambda (ls at) (cond ((null? ls) "")
                                           ((= (extract (car ls) start) at) (extract (car ls) file))
                                           (else (link-at (cdr ls) at)))))
                   (defs (subr spin (definitions) int)
                     (lambda (ds) (cond ((null? ds) -1)
                                        ((string=? (extract (car ds) name) name) (extract (car ds) start))
                                        (else (defs (cdr ds))))))
                   (files (subr spin ((listof indexed acyclic)) (sumof (none unit) (found index-hit)))
                     (lambda (fs)
                       (if (null? fs)
                           (sum none #u)
                           (let ((at (defs (extract (car fs) definitions))))
                             (if (>= at 0)
                                 (sum found (product (file (extract (car fs) file)) (at at)
                                                     (link (link-at (extract (car fs) links) at))))
                                 (files (cdr fs))))))))
            (files (extract (actor-state (car ixs)) files)))))))

"A command: the index told the directory of `file`, if it is an FX-26
file and there is an index."
(define* index-directory-of (subr turn-eff (string) cmds)
  (lambda (file)
    (let ((ixs (get the-index)) (dir (directory-of file)))
      (if (and (pair? ixs) (fx26-file? file) (not (string=? dir "")))
          (list (tell (car ixs) (index-directory (car ixs) dir)))
          nil))))
