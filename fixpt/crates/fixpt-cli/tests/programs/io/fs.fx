; Files and directories (Heist's FIXPT-CHANGES.md F5), relative to the
; working directory: what a path is, a directory made, a file copied,
; renamed, deleted, an empty directory deleted, and the failures of a
; missing path, a file that is no link, and a directory not empty.
(define-type file-kind (sumof (file unit) (directory unit) (symlink unit) (other unit)))
(define-type info-result
  (sumof (info (productof (kind file-kind) (size int) (modified int) (mode int)))
         (failed io-error)))
(define* say (subr (io stdout) (string) unit)
  (lambda (s) (begin (write-out (string-append s "\n")) #u)))
(define* what (subr (io fs-read) (string) string)
  (lambda (path)
    (tagcase (the info-result (file-info path))
      (info i (string-append
               path " "
               (tagcase (extract i kind)
                 (file u (string-append "file " (int->string (extract i size))))
                 (directory u "directory") (symlink u "symlink") (other u "other"))
               (if (and (> (extract i modified) 0) (> (extract i mode) 0))
                   ""
                   " (no time or mode)")))
      (failed e (string-append path (tagcase (extract e kind)
                                      (not-found u " not-found")
                                      (else y " failed")))))))
(define* done? (subr pure ((sumof (done unit) (failed io-error))) string)
  (lambda (r)
    (tagcase r
      (done u "done")
      (failed e (tagcase (extract e kind) (not-found u "not-found") (else y "failed"))))))
(define main (subr (maxeff (io fs-read) (io fs-write) (io stdout) (alloc @b) (read @b) spin
                           (read (globals say what done?)))
                   () int)
  (lambda ()
    (begin
      (write-file "a.txt" (the (bytevectorof @b) (string->utf8 "hello")))
      (say (what "a.txt"))
      (say (string-append "mkdir " (done? (create-directory "d"))))
      (say (what "d"))
      (say (string-append "copy " (done? (copy-file "a.txt" "d/b.txt"))))
      (say (what "d/b.txt"))
      (say (string-append "rename " (done? (rename-file "d/b.txt" "c.txt"))))
      (say (what "d/b.txt"))
      (say (what "c.txt"))
      (say (tagcase (read-symlink "c.txt")
             (target t (string-append "link " t))
             (failed e "no link")))
      (say (string-append "delete " (done? (delete-file "c.txt"))))
      (say (what "c.txt"))
      (say (string-append "delete again " (done? (delete-file "c.txt"))))
      (write-file "d/e.txt" (the (bytevectorof @b) (string->utf8 "")))
      (say (string-append "rmdir full " (done? (delete-directory "d"))))
      (delete-file "d/e.txt")
      (say (string-append "rmdir " (done? (delete-directory "d"))))
      (say (what "d"))
      0)))
