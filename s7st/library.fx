;;; library.fx: R7RS libraries -- `define-library` and `import`.
;;;
;;; A library is a namespace of its own (value.fx's `s7-ns`), its base the
;;; built-ins'. Importing it binds the importer's names to the cells of the
;;; names it exports, as `only`, `except`, `prefix` and `rename` say; so an
;;; importer sees what the library's definitions put in them, even if they
;;; run later. A standard library -- `(scheme …)`, `(srfi …)`, `(rnrs …)`,
;;; `(s7st …)` -- is the built-ins: every namespace sees them already.
;;;
;;; A library imported and not defined is looked for in a file, its name's
;;; parts a path: `(foo bar)` in `foo/bar.sld`, under each directory of
;;; `s7-library-path`. The machine (machine.fx's `s7-run-form`) loads it and
;;; tries the import again.

"Where a library's file is looked for: each directory, with its `/`
(\"\": `s7-directory`)."
(define s7-library-path (ref s7-strings @sc) (new (list "")))
"The library files loaded, so that one that does not define the library
it was loaded for is not loaded again."
(define s7-library-files (ref s7-strings @sc) (new nil))

(define* s7-member-string? (subr spin (string s7-strings) bool)
  (lambda (s l) (and (pair? l) (or (string=? (car l) s) (s7-member-string? s (cdr l))))))
"Directory `dir` added to where libraries are looked for, if it is not."
(define* s7-add-library-directory! (subr s7-eff (string) unit)
  (lambda (dir)
    (if (s7-member-string? dir (get s7-library-path)) #u
        (set s7-library-path (append (get s7-library-path) (list dir))))))

"Whether library name `v` names a standard library: the built-ins."
(define* s7-standard-library? (subr s7-eff (s7-value) bool)
  (lambda (v)
    (and (s7-symbol? (s7-car v))
         (let ((n (s7-symbol-name (s7-sym (s7-car v)))))
           (or (string=? n "scheme") (string=? n "srfi") (string=? n "rnrs") (string=? n "s7st"))))))
(define* s7-register-library! (subr s7-eff (s7-library) unit)
  (lambda (lib)
    (letrec ((drop (subr s7-eff ((listof s7-library acyclic)) (listof s7-library acyclic))
               (lambda (l) (cond ((null? l) nil) ((string=? (extract (car l) name) (extract lib name)) (cdr l))
                                 (else (cons (car l) (drop (cdr l))))))))
      (set s7-libraries (cons lib (drop (get s7-libraries)))))))

"What an import set gives: names bound to cells; or a standard library
whole (nothing to bind: every namespace sees the built-ins); or a library
neither defined nor standard (to be loaded), by name; or an error."
(define-type s7-imported
  (sumof (bindings (listof s7-ns-entry acyclic)) (plain unit) (missing s7-value) (bad string)))
(define* s7-entries-named (subr spin ((listof s7-ns-entry acyclic) symbol) bool)
  (lambda (l name) (and (pair? l) (or (eq? (extract (car l) name) name) (s7-entries-named (cdr l) name)))))
(define* s7-import-set (subr s7-eff (s7-value) s7-imported)
  (lambda (spec)
    (let* ((head (if (s7-symbol? (s7-car spec)) (s7-symbol-name (s7-sym (s7-car spec))) ""))
           (inner (lambda ()
                    (tagcase (s7-import-set (s7-cadr spec))
                      (plain u (sum bindings (s7-ns-entries s7-builtins)))
                      (else y y))))
           (names (s7-symbols-of (s7-value->values (s7-cddr spec)))))
      (cond
        ((string=? head "only")
         (tagcase (inner)
           (bindings bs (sum bindings (letrec ((keep (subr spin ((listof s7-ns-entry acyclic)) (listof s7-ns-entry acyclic))
                                                      (lambda (l) (cond ((null? l) nil)
                                                                        ((s7-memq-symbol (extract (car l) name) names) (cons (car l) (keep (cdr l))))
                                                                        (else (keep (cdr l)))))))
                                          (keep bs))))
           (else y y)))
        ((string=? head "except")
         (tagcase (inner)
           (bindings bs (sum bindings (letrec ((keep (subr spin ((listof s7-ns-entry acyclic)) (listof s7-ns-entry acyclic))
                                                      (lambda (l) (cond ((null? l) nil)
                                                                        ((s7-memq-symbol (extract (car l) name) names) (keep (cdr l)))
                                                                        (else (cons (car l) (keep (cdr l))))))))
                                          (keep bs))))
           (else y y)))
        ((string=? head "prefix")
         (let ((p (s7-symbol-name (s7-sym (s7-car (s7-cddr spec))))))
           (tagcase (inner)
             (bindings bs (sum bindings (letrec ((go (subr spin ((listof s7-ns-entry acyclic)) (listof s7-ns-entry acyclic))
                                                     (lambda (l) (if (null? l) nil
                                                                     (cons (product (name (string->symbol (string-append p (symbol->string (extract (car l) name)))))
                                                                                    (cell (extract (car l) cell)))
                                                                           (go (cdr l)))))))
                                          (go bs))))
             (else y y))))
        ((string=? head "rename")
         (let ((pairs (s7-value->values (s7-cddr spec))))
           (tagcase (inner)
             (bindings bs (sum bindings (letrec ((new-name (subr s7-eff (symbol s7-values) symbol)
                                                   (lambda (n ps) (cond ((null? ps) n)
                                                                        ((eq? (s7-sym (s7-car (car ps))) n) (s7-sym (s7-cadr (car ps))))
                                                                        (else (new-name n (cdr ps))))))
                                                 (go (subr s7-eff ((listof s7-ns-entry acyclic)) (listof s7-ns-entry acyclic))
                                                   (lambda (l) (if (null? l) nil
                                                                   (cons (product (name (new-name (extract (car l) name) pairs)) (cell (extract (car l) cell)))
                                                                         (go (cdr l)))))))
                                          (go bs))))
             (else y y))))
        ((s7-standard-library? spec) (sum plain #u))
        ((not (s7-pair? spec)) (sum bad "an import set is a library's name, or only, except, prefix or rename of one"))
        (else
         (tagcase (s7-find-library (s7-library-name spec))
           (none u (sum missing spec))
           (found lib (sum bindings (letrec ((go (subr s7-eff ((listof s7-export acyclic)) (listof s7-ns-entry acyclic))
                                                  (lambda (l) (if (null? l) nil
                                                                  (cons (product (name (extract (car l) external))
                                                                                 (cell (s7-ns-own-cell! (extract lib ns) (extract (car l) internal))))
                                                                        (go (cdr l)))))))
                                       (go (extract lib exports)))))))))))
"Import sets `specs`, all of them: their bindings together."
(define* s7-import-sets (subr s7-eff (s7-values) s7-imported)
  (lambda (specs)
    (letrec ((go (subr s7-eff (s7-values (listof s7-ns-entry acyclic)) s7-imported)
               (lambda (l acc)
                 (if (null? l) (sum bindings acc)
                     (tagcase (s7-import-set (car l))
                       (bindings bs (go (cdr l) (append bs acc)))
                       (plain u (go (cdr l) acc))
                       (else y y))))))
      (go specs nil))))
(define* s7-bind-all! (subr s7-eff (s7-ns (listof s7-ns-entry acyclic)) unit)
  (lambda (ns l)
    (if (null? l) #u (begin (s7-ns-bind! ns (extract (car l) name) (extract (car l) cell)) (s7-bind-all! ns (cdr l))))))

"Library `name`'s file, relative to a directory libraries are looked for
in: `(foo bar)`'s is `foo/bar.sld`."
(define* s7-library-relative-file (subr s7-eff (s7-value) string)
  (lambda (name)
    (letrec ((go (subr s7-eff (s7-values) string)
               (lambda (l) (cond ((null? l) ".sld")
                                 (else (string-append (if (s7-symbol? (car l)) (s7-symbol-name (s7-sym (car l))) (s7-show (car l) #f))
                                                      (if (null? (cdr l)) "" "/")
                                                      (go (cdr l))))))))
      (go (s7-value->values name)))))
"Library `name`'s file, if one of `s7-library-path`'s directories has it:
its name, its text, and the directory it was found under."
(define* s7-library-file (subr s7-eff (s7-value) (sumof (none unit) (found (productof (path string) (text string) (root string)))))
  (lambda (name)
    (let ((rel (s7-library-relative-file name)))
      (letrec ((try (subr s7-eff (s7-strings) (sumof (none unit) (found (productof (path string) (text string) (root string)))))
                 (lambda (roots)
                   (if (null? roots) (sum none #u)
                       (let ((path (string-append (car roots) rel)))
                         (tagcase (s7-file-text path)
                           (text t (sum found (product (path (s7-path path)) (text t) (root (car roots)))))
                           (failed m (try (cdr roots)))))))))
        (try (get s7-library-path))))))

"A library's declarations, `cond-expand`s opened: export, import, begin,
include and the rest, in order."
(define* s7-library-decls (subr s7-eff (s7-values) s7-values)
  (lambda (decls)
    (if (null? decls) nil
        (let ((d (car decls)))
          (if (s7-sym-named? (s7-car d) "cond-expand")
              (letrec ((first (subr s7-eff (s7-values) s7-values)
                         (lambda (cs) (cond ((null? cs) nil)
                                            ((s7-feature? (s7-car (car cs))) (s7-value->values (s7-cdr (car cs))))
                                            (else (first (cdr cs)))))))
                (append (s7-library-decls (first (s7-value->values (s7-cdr d)))) (s7-library-decls (cdr decls))))
              (cons d (s7-library-decls (cdr decls))))))))
"The declarations of `kind` (`export`, `import`, …): their items, together."
(define* s7-decl-items (subr s7-eff (s7-values string) s7-values)
  (lambda (decls kind)
    (cond ((null? decls) nil)
          ((s7-sym-named? (s7-car (car decls)) kind) (append (s7-value->values (s7-cdr (car decls))) (s7-decl-items (cdr decls) kind)))
          (else (s7-decl-items (cdr decls) kind)))))
"The forms a library's body runs: its `begin`s', and its `include`s."
(define* s7-library-body (subr s7-eff (s7-values) s7-values)
  (lambda (decls)
    (cond ((null? decls) nil)
          ((s7-sym-named? (s7-car (car decls)) "begin") (append (s7-value->values (s7-cdr (car decls))) (s7-library-body (cdr decls))))
          ;; The declaration itself, so that it keeps its place (and file).
          ((s7-sym-named? (s7-car (car decls)) "include") (cons (car decls) (s7-library-body (cdr decls))))
          ((s7-sym-named? (s7-car (car decls)) "include-ci")
           (cons (s7-cons (s7-kw "include") (s7-cdr (car decls))) (s7-library-body (cdr decls))))
          (else (s7-library-body (cdr decls))))))
"What `export` specs say: each name, and its outside name (`(rename a b)`)."
(define* s7-exports-of (subr s7-eff (s7-values) (listof s7-export acyclic))
  (lambda (specs)
    (cond ((null? specs) nil)
          ((s7-symbol? (car specs))
           (cons (product (external (s7-sym (car specs))) (internal (s7-sym (car specs)))) (s7-exports-of (cdr specs))))
          ((s7-sym-named? (s7-car (car specs)) "rename")
           (cons (product (external (s7-sym (s7-car (s7-cddr (car specs))))) (internal (s7-sym (s7-cadr (car specs)))))
                 (s7-exports-of (cdr specs))))
          (else (s7-exports-of (cdr specs))))))

(define* s7-init-libraries! (subr s7-eff () unit)
  (lambda ()
    (begin
      (s7-prim! "interaction-environment" 0 0 (lambda ((a s7-values)) (sum ok (sum env s7-toplevel))))
      (s7-prim! "scheme-report-environment" 0 1 (lambda ((a s7-values)) (sum ok (sum env s7-builtins))))
      (s7-prim! "null-environment" 0 1 (lambda ((a s7-values)) (sum ok (sum env s7-builtins))))
      (s7-prim! "environment" 0 -1
                (lambda ((a s7-values))
                  (let ((ns (s7-make-ns "environment" 256 (list s7-builtins))))
                    (tagcase (s7-import-sets a)
                      (bindings bs (begin (s7-bind-all! ns bs) (sum ok (sum env ns))))
                      (plain u (sum ok (sum env ns)))
                      (missing m (s7-fail "environment: no library named" (list m)))
                      (bad m (s7-fail (string-append "environment: " m) nil)))))))))
