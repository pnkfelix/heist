;;; smtlib.fx: the SMT-LIB2 command language, answering as z3 does
;;; (lockpick's `(lockpick smtlib)`).
;;;
;;; A session reads commands from a reader (sexp.fx) and runs each, its
;;; answers kept as text for whoever drives it to write (`smtlib-run!`).
;;; Errors are answered as (error "line L column C: message") and the
;;; commands after them still run, as with z3; a syntax error ends the
;;; session.
;;;
;;; Terms are parsed into term.fx's terms against an environment: the names
;;; declared or defined, which push and pop scope, and the names bound by
;;; let and by define-fun's parameters.
;;;
;;; A command's error is kept in the session (`fail!`) rather than raised:
;;; parsing writes the term store, so it cannot run under `attempt`. Each
;;; step checks `bad?` after the steps it depends on, and no term is built
;;; once one has failed, so no constructor sees ill-sorted arguments.

(module-parameters ((m-sat (load-moduleof "sat.fx")) (m-rat (load-moduleof "rat.fx"))
                    (m-term (load-moduleof "term.fx" m-sat m-rat))
                    (m-bv (load-moduleof "bv.fx" m-sat m-rat m-term))
                    (m-arith (load-moduleof "arith.fx" m-sat m-rat m-term))
                    (m-eval (load-moduleof "eval.fx" m-sat m-rat m-term))
                    (m-simplex (load-moduleof "simplex.fx" m-sat m-rat))
                    (m-blast (load-moduleof "blast.fx" m-sat m-rat m-term m-bv m-arith m-eval m-simplex))
                    (m-sexp (load-moduleof "sexp.fx" m-sat m-rat))
                    (m-smt (load-moduleof "smt.fx" m-sat m-rat m-term m-bv m-arith m-eval m-simplex m-blast))))

(hide (define kit-lists (load-module "../kit/lists.fx"))
      (import kit-lists map))

;;; ------------------------------------------------------------ the session

(define-type param (productof (name string) (sort int)))
(define-type params (listof param acyclic))
"A defined function: its parameters, sort and body; and the term of its
body for each list of arguments (by their ids)."
(define-type fun-def (productof (params params) (sort int) (body sexp) (cache (table string int @cb))))
"What a name is: nothing (popped), a constant (a term), or a defined
function. Each entry has a serial number, to tell it from another of the
same name."
(define-datatype entry
  (e-none)
  (e-const int int)
  (e-fun int fun-def))
(define-type undo (productof (name string) (before entry)))
(define-type def (productof (name string) (entry entry)))
(define-type local (productof (name string) (term int)))
(define-type locals (listof local acyclic))

(define-type session
  (productof
   (smt (ref smt @cb))
   (names (ref (table string entry @cb) @cb))
   (scopes (ref (listof (listof undo acyclic) acyclic) @cb))   ; one list per push
   (defs (ref (listof def acyclic) @cb))                      ; declared and defined names, newest first
   (out (ref strings @cb))                                    ; answers not yet taken, newest first
   (errout (ref strings @cb))                                 ; notes for the standard error
   (print-success (ref bool @cb))
   (errors (ref bool @cb))                                    ; whether a command failed
   (reals (ref bool @cb))                                     ; numerals are reals (a logic with reals, no integers)
   (serial (ref int @cb))
   (err (ref string @cb))))                                   ; the running command's error, or \"\"

(define* new-names (subr cb-eff () (table string entry @cb))
  (lambda () (the (table string entry @cb) (make-table string-hash string=?))))
(define* make-session (subr cb-eff () session)
  (lambda ()
    (product (smt (new (make-smt))) (names (new (new-names)))
             (scopes (new (the (listof (listof undo acyclic) acyclic) nil))) (defs (new (the (listof def acyclic) nil)))
             (out (new (the strings nil))) (errout (new (the strings nil)))
             (print-success (new #f)) (errors (new #f)) (reals (new #f)) (serial (new 0)) (err (new "")))))
(define* session-smt (subr (read @cb) (session) smt) (lambda (s) (get (extract s smt))))

"Answer text, for the session's output."
(define* out! (subr cb-eff (session string) unit) (lambda (s x) (set (extract s out) (cons x (get (extract s out))))))
"The output so far, which is then taken."
(define* session-take-output! (subr cb-eff (session) string)
  (lambda (s) (let ((o (get (extract s out)))) (begin (set (extract s out) nil) (string-concat (reverse-strings o))))))
(define* session-take-errors! (subr cb-eff (session) string)
  (lambda (s) (let ((o (get (extract s errout)))) (begin (set (extract s errout) nil) (string-concat (reverse-strings o))))))
(define* session-errors? (subr (read @cb) (session) bool) (lambda (s) (get (extract s errors))))

(define* bad? (subr (read @cb) (session) bool) (lambda (s) (not (string=? (get (extract s err)) ""))))
"The command fails, with this message (the first failure is the one said)."
(define* fail! (subr cb-eff (session string) int)
  (lambda (s m) (begin (if (bad? s) #u (set (extract s err) m)) 0)))
(define* str* (subr cb-eff (strings) string) (lambda (l) (string-concat l)))

(define* entry-serial (subr pure (entry) int)
  (lambda (e) (tagcase e (e-none () -1) (e-const (n t) n) (e-fun (n f) n))))
(define* lookup (subr cb-eff (session string) entry)
  (lambda (s name) (table-ref (get (extract s names)) name (e-none))))
(define* bound? (subr cb-eff (session string) bool)
  (lambda (s name) (tagcase (lookup s name) (e-none () #f) (e-const (n t) #t) (e-fun (n f) #t))))
(define* next-serial! (subr cb-eff (session) int)
  (lambda (s) (begin (set (extract s serial) (+ 1 (get (extract s serial)))) (get (extract s serial)))))

(define* bind! (subr cb-eff (session string entry) unit)
  (lambda (s name e)
    (if (bound? s name)
        (begin (fail! s (str* (list "invalid declaration, constant '" (symbol->smt-string name) "' already declared"))) #u)
        (let ((scopes (get (extract s scopes))))
          (begin
            (if (null? scopes) #u
                (set (extract s scopes) (cons (cons (product (name name) (before (e-none))) (car scopes)) (cdr scopes))))
            (table-set! (get (extract s names)) name e)
            (set (extract s defs) (cons (product (name name) (entry e)) (get (extract s defs)))))))))

(define* push-scope! (subr cb-eff (session) unit)
  (lambda (s) (begin (set (extract s scopes) (cons nil (get (extract s scopes)))) (smt-push! (session-smt s)))))
(define* pop-scope! (subr cb-eff (session) unit)
  (lambda (s)
    (begin
      (letrec ((go (subr cb-eff ((listof undo acyclic)) unit)
                 (lambda (l) (if (null? l) #u (begin (table-set! (get (extract s names)) (extract (car l) name) (extract (car l) before)) (go (cdr l)))))))
        (go (car (get (extract s scopes)))))
      (set (extract s defs)
           (letrec ((go (subr cb-eff ((listof def acyclic)) (listof def acyclic))
                      (lambda (ds) (cond ((null? ds) nil)
                                         ((= (entry-serial (lookup s (extract (car ds) name))) (entry-serial (extract (car ds) entry))) ds)
                                         (else (go (cdr ds)))))))
             (go (get (extract s defs)))))
      (set (extract s scopes) (cdr (get (extract s scopes))))
      (smt-pop! (session-smt s)))))

;;; ------------------------------------------------------------ sexps

(define* sym? (subr pure (sexp) bool) (lambda (x) (tagcase x (sx-sym (n) #t) (else y #f))))
(define* sym-name (subr pure (sexp) string) (lambda (x) (tagcase x (sx-sym (n) n) (else y ""))))
(define* is-sym? (subr pure (sexp string) bool) (lambda (x name) (tagcase x (sx-sym (n) (string=? n name)) (else y #f))))
(define* sxlist? (subr pure (sexp) bool) (lambda (x) (tagcase x (sx-list (l) #t) (else y #f))))
(define* items (subr pure (sexp) sexps) (lambda (x) (tagcase x (sx-list (l) l) (else y nil))))
(define* nat? (subr pure (sexp) bool) (lambda (x) (tagcase x (sx-num (n) #t) (else y #f))))
(define* nat-value (subr pure (sexp) int) (lambda (x) (tagcase x (sx-num (n) n) (else y 0))))
(define* nth (subr spin (sexps int) sexp) (lambda (l i) (if (= i 0) (car l) (nth (cdr l) (- i 1)))))
(define* len (subr spin (sexps) int) (lambda (l) (list-length l)))

;;; ------------------------------------------------------------ sorts

(define* parse-sort (subr cb-eff (session sexp) int)
  (lambda (s x)
    (cond ((is-sym? x "Bool") bool-sort)
          ((is-sym? x "Int") int-sort)
          ((is-sym? x "Real") real-sort)
          ((and (sxlist? x) (= 3 (len (items x))) (is-sym? (nth (items x) 0) "_") (is-sym? (nth (items x) 1) "BitVec")
                (nat? (nth (items x) 2)) (> (nat-value (nth (items x) 2)) 0))
           (bv-sort (nat-value (nth (items x) 2))))
          (else (fail! s (str* (list "unknown sort '" (sexp->string x) "'")))))))

;;; ------------------------------------------------------------ terms

(define* local-ref (subr spin (string locals) int)
  (lambda (name l) (cond ((null? l) -1) ((string=? (extract (car l) name) name) (extract (car l) term)) (else (local-ref name (cdr l))))))

"The terms the sexps stand for (stopping at a failure)."
(define parse-terms (subr cb-eff (session sexps locals) ints)
  (lambda (s xs locals)
    (if (or (null? xs) (bad? s)) nil
        (let ((t (parse-term s (car xs) locals)))
          (if (bad? s) nil (cons t (parse-terms s (cdr xs) locals)))))))

"The term x stands for, where locals are the names bound by let or as
parameters."
(define parse-term (subr cb-eff (session sexp locals) int)
  (lambda (s x locals)
    (tagcase x
      (sx-sym (name)
        (let ((l (local-ref name locals)))
          (if (>= l 0) l
              (tagcase (lookup s name)
                (e-const (n t) t)
                (e-fun (n f) (apply-fun s name f nil))
                (e-none ()
                  (cond ((string=? name "true") (true-term))
                        ((string=? name "false") (false-term))
                        (else (fail! s (string-append "unknown constant " (sexp->string x))))))))))
      (sx-bv (v w) (bv-const v w))
      (sx-num (n) (num-int n (if (get (extract s reals)) real-sort int-sort)))
      (sx-dec (q) (num q real-sort))
      (sx-str (str) (fail! s (string-append "invalid term " (sexp->string x))))
      (sx-list (l)
        (if (null? l) (fail! s (string-append "invalid term " (sexp->string x)))
            (let ((head (car l)))
              (cond
               ((is-sym? head "let")
                (if (not (and (= 3 (len l)) (sxlist? (nth l 1)))) (fail! s "invalid let")
                    (letrec ((bind (subr cb-eff (sexps locals) locals)
                               (lambda (bs acc)
                                 (if (or (null? bs) (bad? s)) acc
                                     (let ((b (car bs)))
                                       (if (not (and (sxlist? b) (= 2 (len (items b))) (sym? (nth (items b) 0))))
                                           (begin (fail! s "invalid let binding") acc)
                                           (let ((t (parse-term s (nth (items b) 1) locals)))
                                             (bind (cdr bs) (cons (product (name (sym-name (nth (items b) 0))) (term t)) acc)))))))))
                      (let ((bound (bind (items (nth l 1)) nil)))
                        (if (bad? s) 0 (parse-term s (nth l 2) (append-locals (reverse-locals bound) locals)))))))
               ((is-sym? head "!")
                (let ((t (parse-term s (nth l 1) locals)))
                  (if (bad? s) 0
                      (begin
                        (letrec ((go (subr cb-eff (sexps) unit)
                                   (lambda (attrs)
                                     (if (and (pair? attrs) (pair? (cdr attrs)))
                                         (begin (if (is-sym? (car attrs) ":named")
                                                    (bind! s (sym-name (car (cdr attrs))) (e-const (next-serial! s) t))
                                                    #u)
                                                (go (cdr (cdr attrs))))
                                         #u))))
                          (go (cdr (cdr l))))
                        t))))
               ((is-sym? head "_") (parse-indexed-constant s x))
               ((and (sxlist? head) (pair? (items head)) (is-sym? (car (items head)) "_"))
                (let ((args (parse-terms s (cdr l) locals)))
                  (if (bad? s) 0 (apply-indexed s head args))))
               ((and (sym? head) (null? (cdr l))) (fail! s "invalid function application, arguments missing"))
               ((sym? head)
                (let ((args (parse-terms s (cdr l) locals)) (name (sym-name head)))
                  (cond ((bad? s) 0)
                        ((>= (local-ref name locals) 0)
                         (fail! s (str* (list "invalid function application, " (sexp->string head) " is not a function"))))
                        (else
                         (tagcase (lookup s name)
                           (e-fun (n f) (apply-fun s name f args))
                           (e-const (n t) (fail! s (str* (list "invalid function application, " (sexp->string head) " is not a function"))))
                           (e-none () (apply-builtin s name args)))))))
               (else (fail! s (string-append "invalid term " (sexp->string x)))))))))))

(define* reverse-locals (subr spin (locals) locals)
  (lambda (l) (letrec ((go (subr spin (locals locals) locals) (lambda (l acc) (if (null? l) acc (go (cdr l) (cons (car l) acc))))))
                (go l nil))))
(define* append-locals (subr spin (locals locals) locals)
  (lambda (a b) (if (null? a) b (cons (car a) (append-locals (cdr a) b)))))
(define* ids-key (subr spin (ints) string)
  (lambda (l) (if (null? l) "" (string-append (int->string (car l)) (string-append " " (ids-key (cdr l)))))))

"A defined function applied: its body, with the parameters bound. The body
is parsed once for each list of arguments (the cache): definitions build
on each other, and parsing a body at each use parses the uses within it
again, exponentially."
(define apply-fun (subr cb-eff (session string fun-def ints) int)
  (lambda (s name f args)
    (let ((ps (extract f params)))
      (cond ((not (= (list-length ps) (list-length args)))
             (fail! s (string-append "invalid function application, wrong number of arguments for " (symbol->smt-string name))))
            ((letrec ((go (subr cb-eff (params ints) bool)
                        (lambda (ps as) (and (pair? ps) (or (not (= (extract (car ps) sort) (term-sort (car as)))) (go (cdr ps) (cdr as)))))))
               (go ps args))
             (fail! s (string-append "sort mismatch at argument of " (symbol->smt-string name))))
            (else
             (let ((key (ids-key args)))
               (if (table-has? (extract f cache) key) (table-ref (extract f cache) key 0)
                   (let ((t (parse-term s (extract f body)
                                        (letrec ((go (subr cb-eff (params ints) locals)
                                                   (lambda (ps as) (if (null? ps) nil (cons (product (name (extract (car ps) name)) (term (car as))) (go (cdr ps) (cdr as)))))))
                                          (go ps args)))))
                     (if (bad? s) 0 (begin (table-set! (extract f cache) key t) t))))))))))

;;; ------------------------------------------------------------ built-in functions

(define* check-sorts (subr cb-eff (session string ints int) bool)
  (lambda (s name args sort)
    (cond ((null? args) #t)
          ((not (= (term-sort (car args)) sort))
           (begin (fail! s (str* (list "Sort mismatch at argument for function " name ", supplied sort is " (sort->string (term-sort (car args)))))) #f))
          (else (check-sorts s name (cdr args) sort)))))
(define* check-arity (subr cb-eff (session string ints int) bool)
  (lambda (s name args n)
    (if (= (list-length args) n) #t (begin (fail! s (string-append "invalid number of arguments to " name)) #f))))
"An arithmetic function of at least n arguments, all numbers."
(define* arith-ok? (subr cb-eff (session string ints int) bool)
  (lambda (s name args n)
    (if (< (list-length args) n) (begin (fail! s (string-append "invalid number of arguments to " name)) #f)
        (letrec ((go (subr cb-eff (ints) bool)
                   (lambda (as) (cond ((null? as) #t)
                                      ((not (arith-sort? (term-sort (car as))))
                                       (begin (fail! s (str* (list "Sort mismatch at argument for function " name ", supplied sort is " (sort->string (term-sort (car as)))))) #f))
                                      (else (go (cdr as)))))))
          (go args)))))
(define* check-bv (subr cb-eff (session string int) bool)
  (lambda (s name a)
    (if (bv-sort? (term-sort a)) #t
        (begin (fail! s (str* (list "Sort mismatch at argument for function " name ", supplied sort is " (sort->string (term-sort a))))) #f))))
(define* arith-args? (subr cb-eff (ints) bool)
  (lambda (args) (and (pair? args) (letrec ((go (subr cb-eff (ints) bool) (lambda (l) (or (null? l) (and (arith-sort? (term-sort (car l))) (go (cdr l)))))))
                                     (go args)))))
"Integers among reals become reals (z3 does so; SMT-LIB's mixed logics ask
for to_real)."
(define* coerce (subr cb-eff (ints) ints)
  (lambda (args) (if (letrec ((go (subr cb-eff (ints) bool) (lambda (l) (and (pair? l) (or (= (term-sort (car l)) real-sort) (go (cdr l)))))))
                       (go args))
                     (the ints (map mk-to-real args)) args)))
"Chained relations: (= a b c) is (and (= a b) (= b c))."
(define* chain (subr cb-eff ((subr cb-eff (int int) int) ints) int)
  (lambda (mk args)
    (letrec ((go (subr cb-eff (ints ints) int)
               (lambda (as acc) (if (or (null? as) (null? (cdr as))) (mk-and (reverse-ints acc)) (go (cdr as) (cons (mk (car as) (car (cdr as))) acc))))))
      (go args nil))))
"Left-associative: (bvadd a b c) is (bvadd (bvadd a b) c)."
(define* fold-left2 (subr cb-eff ((subr cb-eff (int int) int) int ints) int)
  (lambda (mk acc as) (if (null? as) acc (fold-left2 mk (mk acc (car as)) (cdr as)))))
(define* bv-unary (subr cb-eff (session string ints (subr cb-eff (int) int)) int)
  (lambda (s name args mk) (if (and (check-arity s name args 1) (check-bv s name (car args))) (mk (car args)) 0)))
(define* bv-binary (subr cb-eff (session string ints (subr cb-eff (int int) int)) int)
  (lambda (s name args mk)
    (if (and (check-arity s name args 2) (check-bv s name (car args)) (check-sorts s name args (term-sort (car args))))
        (mk (car args) (car (cdr args))) 0)))
(define* bv-left (subr cb-eff (session string ints (subr cb-eff (int int) int)) int)
  (lambda (s name args mk)
    (cond ((null? args) (fail! s (string-append "invalid number of arguments to " name)))
          ((and (check-bv s name (car args)) (check-sorts s name args (term-sort (car args)))) (fold-left2 mk (car args) (cdr args)))
          (else 0))))

(define* apply-builtin (subr cb-eff (session string ints) int)
  (lambda (s name args)
    (let ((is (lambda ((n string)) (string=? name n))))
      (cond
       ((is "not") (if (and (check-arity s name args 1) (check-sorts s name args bool-sort)) (mk-not (car args)) 0))
       ((is "and") (if (check-sorts s name args bool-sort) (mk-and args) 0))
       ((is "or") (if (check-sorts s name args bool-sort) (mk-or args) 0))
       ((is "xor") (cond ((not (check-sorts s name args bool-sort)) 0)
                         ((null? args) (fail! s "invalid number of arguments to xor"))
                         (else (fold-left2 mk-xor (car args) (cdr args)))))
       ((is "=>") (cond ((not (check-sorts s name args bool-sort)) 0)
                        ((null? args) (fail! s "invalid number of arguments to =>"))
                        (else (letrec ((go (subr cb-eff (ints) int)
                                         (lambda (as) (if (null? (cdr as)) (car as) (go (cons (mk-implies (car (cdr as)) (car as)) (cdr (cdr as))))))))
                                (go (reverse-ints args))))))
       ((is "=") (cond ((< (list-length args) 2) (fail! s "invalid number of arguments to ="))
                       ((arith-args? args) (chain mk-arith-eq (coerce args)))
                       ((check-sorts s name args (term-sort (car args))) (chain mk-eq args))
                       (else 0)))
       ((is "distinct") (cond ((< (list-length args) 2) (fail! s "invalid number of arguments to distinct"))
                              ((arith-args? args) (mk-arith-distinct (coerce args)))
                              ((check-sorts s name args (term-sort (car args))) (mk-distinct args))
                              (else 0)))
       ((is "ite") (if (and (check-arity s name args 3) (check-sorts s name (list (car args)) bool-sort))
                       (let ((branches (if (arith-args? (cdr args)) (coerce (cdr args)) (cdr args))))
                         (if (check-sorts s name (cdr branches) (term-sort (car branches)))
                             (mk-ite (car args) (car branches) (car (cdr branches))) 0))
                       0))
       ((is "+") (if (arith-ok? s name args 1) (mk-add (coerce args)) 0))
       ((is "-") (if (arith-ok? s name args 1)
                     (let ((args (coerce args)))
                       (if (null? (cdr args)) (mk-neg (car args)) (fold-left2 (lambda ((a int) (b int)) (mk-sub a (list b))) (car args) (cdr args))))
                     0))
       ((is "*") (if (arith-ok? s name args 1)
                     (let ((t (mk-mul (coerce args))))
                       (if (term-op? t "*") (fail! s "combo: nonlinear arithmetic is not supported") t))
                     0))
       ((is "/") (if (arith-ok? s name args 2)
                     (letrec ((go (subr cb-eff (int ints) int)
                                (lambda (acc as)
                                  (if (null? as) acc
                                      (let ((d (mk-to-real (car as))))
                                        (if (and (num? d) (not (rat-zero? (num-value d))))
                                            (go (mk-div-real acc d) (cdr as))
                                            (fail! s "combo: division is supported by nonzero constants only")))))))
                       (go (mk-to-real (car args)) (cdr args)))
                     0))
       ((or (is "div") (is "mod"))
        (cond ((not (and (check-arity s name args 2) (check-sorts s name args int-sort))) 0)
              ((not (and (num? (car (cdr args))) (not (rat-zero? (num-value (car (cdr args)))))))
               (fail! s (str* (list "combo: " name " is supported by nonzero constants only"))))
              ((is "div") (mk-idiv (car args) (car (cdr args))))
              (else (mk-imod (car args) (car (cdr args))))))
       ((is "abs") (if (and (arith-ok? s name args 1) (check-arity s name args 1)) (mk-abs (car args)) 0))
       ((or (is "<=") (is "<") (is ">=") (is ">"))
        (if (arith-ok? s name args 2)
            (chain (cond ((is "<=") mk-le) ((is "<") mk-lt) ((is ">=") mk-ge) (else mk-gt)) (coerce args))
            0))
       ((is "to_real") (if (and (check-arity s name args 1) (check-sorts s name args int-sort)) (mk-to-real (car args)) 0))
       ((is "to_int") (if (and (check-arity s name args 1) (check-sorts s name args real-sort)) (mk-to-int (car args)) 0))
       ((is "is_int") (if (and (check-arity s name args 1) (check-sorts s name args real-sort)) (mk-is-int (car args)) 0))
       ((is "bvnot") (bv-unary s name args mk-bvnot))
       ((is "bvneg") (bv-unary s name args mk-bvneg))
       ((is "bvand") (bv-left s name args mk-bvand))
       ((is "bvor") (bv-left s name args mk-bvor))
       ((is "bvxor") (bv-left s name args mk-bvxor))
       ((is "bvadd") (bv-left s name args mk-bvadd))
       ((is "bvmul") (bv-left s name args mk-bvmul))
       ((is "bvsub") (bv-left s name args mk-bvsub))
       ((is "bvnand") (bv-binary s name args mk-bvnand))
       ((is "bvnor") (bv-binary s name args mk-bvnor))
       ((is "bvxnor") (bv-binary s name args mk-bvxnor))
       ((is "bvudiv") (bv-binary s name args mk-bvudiv))
       ((is "bvurem") (bv-binary s name args mk-bvurem))
       ((is "bvsdiv") (bv-binary s name args mk-bvsdiv))
       ((is "bvsrem") (bv-binary s name args mk-bvsrem))
       ((is "bvsmod") (bv-binary s name args mk-bvsmod))
       ((is "bvshl") (bv-binary s name args mk-bvshl))
       ((is "bvlshr") (bv-binary s name args mk-bvlshr))
       ((is "bvashr") (bv-binary s name args mk-bvashr))
       ((is "bvcomp") (bv-binary s name args mk-bvcomp))
       ((is "bvult") (bv-binary s name args mk-bvult))
       ((is "bvule") (bv-binary s name args mk-bvule))
       ((is "bvugt") (bv-binary s name args mk-bvugt))
       ((is "bvuge") (bv-binary s name args mk-bvuge))
       ((is "bvslt") (bv-binary s name args mk-bvslt))
       ((is "bvsle") (bv-binary s name args mk-bvsle))
       ((is "bvsgt") (bv-binary s name args mk-bvsgt))
       ((is "bvsge") (bv-binary s name args mk-bvsge))
       ((is "concat")
        (cond ((null? args) (fail! s "invalid number of arguments to concat"))
              ((letrec ((go (subr cb-eff (ints) bool) (lambda (l) (or (null? l) (and (check-bv s name (car l)) (go (cdr l)))))))
                 (go args))
               (fold-left2 mk-concat (car args) (cdr args)))
              (else 0)))
       (else (fail! s (string-append "unknown function/constant " (symbol->smt-string name))))))))

"(_ bvN w)"
(define* parse-indexed-constant (subr cb-eff (session sexp) int)
  (lambda (s x)
    (let ((l (items x)))
      (if (and (= 3 (len l)) (sym? (nth l 1)) (nat? (nth l 2)) (> (nat-value (nth l 2)) 0))
          (let* ((name (sym-name (nth l 1))) (n (string-length name)))
            (if (and (> n 2) (string=? "bv" (substring name 0 2))
                     (letrec ((go (subr cb-eff (int) bool) (lambda (i) (or (= i n) (and (digit? (string-ref name i)) (go (+ i 1)))))))
                       (go 2)))
                (bv-const (decimal (substring name 2 n)) (nat-value (nth l 2)))
                (fail! s (string-append "unknown indexed constant " (sexp->string x)))))
          (fail! s (string-append "invalid indexed constant " (sexp->string x)))))))

"An index as z3 takes it: a numeral, or a symbol that reads as an integer
(-3: SMT-LIB numerals have no sign). Whether it is one, and its value."
(define-type index (productof (ok bool) (value int)))
(define* index-integer (subr cb-eff (sexp) index)
  (lambda (x)
    (tagcase x
      (sx-num (n) (product (ok #t) (value n)))
      (sx-sym (name)
        (let* ((n (string-length name)) (neg (and (> n 1) (char=? (string-ref name 0) #\-))) (from (if neg 1 0)))
          (if (and (> n from) (letrec ((go (subr cb-eff (int) bool) (lambda (i) (or (= i n) (and (digit? (string-ref name i)) (go (+ i 1)))))))
                                (go from)))
              (let ((v (decimal (substring name from n)))) (product (ok #t) (value (if neg (- 0 v) v))))
              (product (ok #f) (value 0)))))
      (else y (product (ok #f) (value 0))))))

"((_ name index ...) args ...)"
(define* apply-indexed (subr cb-eff (session sexp ints) int)
  (lambda (s head args)
    (let* ((h (items head)) (name (if (pair? (cdr h)) (sym-name (car (cdr h))) "")) (indices (if (pair? (cdr h)) (cdr (cdr h)) nil)))
      (if (or (string=? name "at-most") (string=? name "at-least") (string=? name "pbeq") (string=? name "pble") (string=? name "pbge"))
          (pseudo-boolean s name indices args head)
          (apply-bv-indexed s head name indices args)))))

"z3's cardinality and pseudo-Boolean constraints: ((_ at-most k) b ...),
((_ at-least k) b ...), and ((_ pbeq k c1 ... cn) b1 ... bn), likewise pble
and pbge: the sum of the ci for the bi true is = k, <= k, >= k. A
coefficient c < 0 is -c for (not b), with k raised by -c. With all of them
1 or -1, or few in all (64), b counts c times in a cardinality constraint,
else the sum is made in integer arithmetic: its encoding grows with the
copies times the bound."
(define* pseudo-boolean (subr cb-eff (session string sexps ints sexp) int)
  (lambda (s name indices args head)
    (let ((is (letrec ((go (subr cb-eff (sexps) ints)
                         (lambda (l) (if (null? l) nil (let ((i (index-integer (car l)))) (if (extract i ok) (cons (extract i value) (go (cdr l))) (cons 0 nil))))))
                         (all (subr cb-eff (sexps) bool) (lambda (l) (or (null? l) (and (extract (index-integer (car l)) ok) (all (cdr l)))))))
                 (if (all indices) (go indices) nil))))
      (cond
       ((or (null? indices) (null? is)) (fail! s (string-append "invalid indexed function " (sexp->string head))))
       ((not (letrec ((go (subr cb-eff (ints) bool) (lambda (l) (or (null? l) (and (term-bool? (car l)) (go (cdr l))))))) (go args)))
        (fail! s (string-append "Sort mismatch at argument for function " (sexp->string head))))
       (else
        (let* ((k (car is))
               (card? (or (string=? name "at-most") (string=? name "at-least")))
               (cs (if card? (the ints (map (lambda ((a int)) 1) args)) (cdr is))))
          (if (not (and (= (list-length cs) (list-length args)) (or (not card?) (null? (cdr is)))))
              (fail! s (string-append "invalid number of arguments to " (sexp->string head)))
              (if (and (> (letrec ((go (subr cb-eff (ints int) int) (lambda (l t) (if (null? l) t (go (cdr l) (+ t (if (< (car l) 0) (- 0 (car l)) (car l)))))))) (go cs 0)) 64)
                       (not (letrec ((go (subr cb-eff (ints) bool) (lambda (l) (or (null? l) (and (or (= (car l) 1) (= (car l) -1)) (go (cdr l))))))) (go cs))))
                  ;; kt first: lockpick's `let` under Twobit (inits right to left).
                  (let* ((kt (num-int k int-sort))
                         (total (mk-add (letrec ((go (subr cb-eff (ints ints) ints)
                                                     (lambda (cs as) (if (null? cs) nil
                                                                         (let ((t (mk-ite (car as) (num-int (car cs) int-sort) (num-int 0 int-sort)))) (cons t (go (cdr cs) (cdr as))))))))
                                          (go cs args)))))
                    (cond ((string=? name "pbeq") (mk-arith-eq total kt)) ((string=? name "pble") (mk-le total kt)) (else (mk-ge total kt))))
                  (letrec ((copies (subr cb-eff (int int ints) ints) (lambda (n x l) (if (= n 0) l (copies (- n 1) x (cons x l)))))
                           (go (subr cb-eff (ints ints int ints) int)
                             (lambda (cs as k ts)
                               (cond ((null? cs)
                                      (cond ((or (string=? name "at-most") (string=? name "pble")) (mk-card 0 k ts))
                                            ((or (string=? name "at-least") (string=? name "pbge")) (mk-card k no-bound ts))
                                            (else (mk-card k k ts))))
                                     ((< (car cs) 0) (go (cdr cs) (cdr as) (- k (car cs)) (copies (- 0 (car cs)) (mk-not (car as)) ts)))
                                     (else (go (cdr cs) (cdr as) k (copies (car cs) (car as) ts)))))))
                    (go cs args k nil))))))))))

(define* apply-bv-indexed (subr cb-eff (session sexp string sexps ints) int)
  (lambda (s head name indices args)
    (cond
     ((not (and (not (string=? name "")) (pair? indices)
                (letrec ((go (subr cb-eff (sexps) bool) (lambda (l) (or (null? l) (and (nat? (car l)) (go (cdr l))))))) (go indices))))
      (fail! s (string-append "invalid indexed function " (sexp->string head))))
     ((not (check-arity s name args 1)) 0)
     ((not (check-bv s name (car args))) 0)
     (else
      (let* ((a (car args)) (k (nat-value (car indices))) (w (term-width a)))
        (cond
         ((string=? name "extract")
          (if (not (= 2 (len indices))) (fail! s "invalid extract")
              (let ((hi (nat-value (car indices))) (lo (nat-value (car (cdr indices)))))
                (if (and (<= lo hi) (< hi w)) (mk-extract hi lo a) (fail! s "invalid extract, indices out of range")))))
         ((string=? name "zero_extend") (mk-zero-extend k a))
         ((string=? name "sign_extend") (mk-sign-extend k a))
         ((string=? name "repeat") (if (= k 0) (fail! s "invalid repeat, count must be positive") (mk-repeat k a)))
         ((string=? name "rotate_left") (mk-rotate-left k a))
         ((string=? name "rotate_right") (mk-rotate-right k a))
         (else (fail! s (string-append "unknown indexed function " (sexp->string head))))))))))

;;; ------------------------------------------------------------ writing values

"As z3: 2.0, (- 2.0), (/ 1.0 3.0), (- (/ 1.0 3.0))."
(define* real->string (subr cb-eff (rat) string)
  (lambda (q)
    (if (rat< q rat-0) (str* (list "(- " (real->string (rat-neg q)) ")"))
        (let ((n (int->string (rat-num q))) (d (rat-den q)))
          (if (= d 1) (string-append n ".0") (str* (list "(/ " n ".0 " (int->string d) ".0)")))))))
(define* value->string (subr cb-eff (rat int) string)
  (lambda (v sort)
    (cond ((sort-bool? sort) (if (rat-true? v) "true" "false"))
          ((bv-sort? sort) (bv->string (rat-num v) (bv-sort-width sort)))
          ((= sort int-sort) (sexp->string (sx-num (rat-num v))))
          (else (real->string v)))))

;;; ------------------------------------------------------------ commands

(define* success (subr cb-eff (session) unit) (lambda (s) (if (get (extract s print-success)) (out! s "success\n") #u)))

(define known-options strings
  (list ":produce-models" ":produce-unsat-cores" ":produce-assignments" ":produce-proofs"
        ":produce-unsat-assumptions" ":random-seed" ":verbosity" ":global-declarations"
        ":interactive-mode" ":incremental" ":regular-output-channel"
        ":diagnostic-output-channel" ":reproducible-resource-limit"))
(define* member-string? (subr spin (string strings) bool)
  (lambda (x l) (and (pair? l) (or (string=? x (car l)) (member-string? x (cdr l))))))

"QF_LRA, QF_RDL, QF_UFNRA and the like; not QF_AUFLIRA."
(define* real-logic? (subr spin (string) bool)
  (lambda (name)
    (let ((has? (lambda ((part string))
                  (let ((n (string-length name)) (k (string-length part)))
                    (letrec ((go (subr spin (int) bool) (lambda (i) (and (<= (+ i k) n) (or (string=? part (substring name i (+ i k))) (go (+ i 1)))))))
                      (go 0))))))
      (and (or (has? "RA") (has? "RDL")) (not (has? "IRA"))))))

(define* write-answer (subr cb-eff (session int) unit)
  (lambda (s answer)
    (let ((problem (smt-problem (session-smt s))))
      (if (not (string=? problem "")) (begin (fail! s problem) #u)
          (out! s (cond ((= answer sat-sat) "sat\n") ((= answer sat-unsat) "unsat\n") (else "unknown\n")))))))

(define* need-model (subr cb-eff (session) bool)
  (lambda (s) (if (smt-model-available? (session-smt s)) #t (begin (fail! s "model is not available") #f))))

(define* declare! (subr cb-eff (session string sexps sexp) unit)
  (lambda (s name arg-sorts sort-sexp)
    (if (pair? arg-sorts) (begin (fail! s "combo: functions with arguments are not supported yet") #u)
        (let ((sort (parse-sort s sort-sexp)))
          (if (bad? s) #u
              (begin (bind! s name (e-const (next-serial! s) (make-var name sort)))
                     (if (bad? s) #u (success s))))))))

;; What a command comes to.
(define cmd-go int 0)
(define cmd-exit int 1)

(define* run-command (subr cb-eff (session sexp) int)
  (lambda (s cmd)
    (let ((l (items cmd)))
      (if (not (and (sxlist? cmd) (pair? l) (sym? (car l)))) (begin (fail! s "invalid command, symbol expected") cmd-go)
          (let* ((name (sym-name (car l))) (is (lambda ((n string)) (string=? name n))) (n (len l)) (smt (session-smt s)))
            (cond
             ((is "set-logic")
              (begin (if (and (> n 1) (sym? (nth l 1))) (set (extract s reals) (real-logic? (sym-name (nth l 1)))) #u)
                     (success s) cmd-go))
             ((is "set-info") (begin (success s) cmd-go))
             ((is "set-option")
              (let ((key (if (> n 1) (sym-name (nth l 1)) "")))
                (begin
                  (cond ((string=? key ":print-success")
                         (set (extract s print-success) (and (> n 2) (is-sym? (nth l 2) "true"))))
                        ((string=? key ":timeout")
                         (smt-set-timeout! smt (if (and (> n 2) (nat? (nth l 2)) (< (nat-value (nth l 2)) 4294967295)) (nat-value (nth l 2)) -1)))
                        ((member-string? key known-options) #u)
                        (else (begin (fail! s (str* (list "unknown parameter '"
                                                          (if (and (> (string-length key) 0) (char=? (string-ref key 0) #\:)) (substring key 1 (string-length key))
                                                              (if (> n 1) (sexp->string (nth l 1)) ""))
                                                          "'")))
                                     #u)))
                  (if (bad? s) #u (success s))
                  cmd-go)))
             ((is "get-option")
              (let ((key (if (> n 1) (sym-name (nth l 1)) "")))
                (begin (out! s (cond ((string=? key ":print-success") (if (get (extract s print-success)) "true\n" "false\n"))
                                     ((string=? key ":produce-models") "true\n")
                                     (else "unsupported\n")))
                       cmd-go)))
             ((is "get-info")
              (let ((key (if (> n 1) (sym-name (nth l 1)) "")))
                (begin
                  (cond ((string=? key ":name") (out! s "(:name \"combo\")\n"))
                        ((string=? key ":version") (out! s "(:version \"0.1\")\n"))
                        ((string=? key ":reason-unknown") (out! s (str* (list "(:reason-unknown " (sexp->string (sx-str (smt-reason-unknown smt))) ")\n"))))
                        ((string=? key ":all-statistics")
                         (out! s (str* (list "("
                                             (letrec ((go (subr cb-eff ((listof stat acyclic) bool) string)
                                                        (lambda (kvs first?)
                                                          (if (null? kvs) ""
                                                              (str* (list (if first? "" "\n ") ":" (extract (car kvs) name) " " (int->string (extract (car kvs) value)) (go (cdr kvs) #f)))))))
                                               (go (smt-stats smt) #t))
                                             ")\n"))))
                        (else (out! s "unsupported\n")))
                  cmd-go)))
             ((is "declare-const")
              (begin (if (and (= 3 n) (sym? (nth l 1))) (declare! s (sym-name (nth l 1)) nil (nth l 2)) (begin (fail! s "invalid declaration") #u))
                     cmd-go))
             ((is "declare-fun")
              (begin (if (and (= 4 n) (sym? (nth l 1)) (sxlist? (nth l 2))) (declare! s (sym-name (nth l 1)) (items (nth l 2)) (nth l 3))
                         (begin (fail! s "invalid declaration") #u))
                     cmd-go))
             ((is "define-fun")
              (begin
                (if (not (and (= 5 n) (sym? (nth l 1)) (sxlist? (nth l 2)))) (begin (fail! s "invalid function definition") #u)
                    (let ((ps (letrec ((go (subr cb-eff (sexps) params)
                                         (lambda (ps)
                                           (cond ((or (null? ps) (bad? s)) nil)
                                                 ((not (and (sxlist? (car ps)) (= 2 (len (items (car ps)))) (sym? (nth (items (car ps)) 0))))
                                                  (begin (fail! s "invalid function definition, parameter expected") nil))
                                                 (else (let ((sort (parse-sort s (nth (items (car ps)) 1))))
                                                         (cons (product (name (sym-name (nth (items (car ps)) 0))) (sort sort)) (go (cdr ps)))))))))
                                (go (items (nth l 2))))))
                      (if (bad? s) #u
                          (let ((sort (parse-sort s (nth l 3))) (body (nth l 4)))
                            (if (bad? s) #u
                                ;; Check the body now, with the parameters as variables.
                                (let ((t (parse-term s body (letrec ((go (subr cb-eff (params) locals)
                                                                       (lambda (ps) (if (null? ps) nil
                                                                                        (let ((v (make-var (extract (car ps) name) (extract (car ps) sort))))
                                                                                          (cons (product (name (extract (car ps) name)) (term v)) (go (cdr ps))))))))
                                                              (go ps)))))
                                  (cond ((bad? s) #u)
                                        ((not (= (term-sort t) sort)) (begin (fail! s "invalid function definition, sort mismatch") #u))
                                        (else
                                         (let ((cache (the (table string int @cb) (make-table string-hash string=?))))
                                           (begin
                                             (if (null? ps) (table-set! cache "" t) #u)
                                             (bind! s (sym-name (nth l 1)) (e-fun (next-serial! s) (product (params ps) (sort sort) (body body) (cache cache))))
                                             (if (bad? s) #u (success s))))))))))))
                cmd-go))
             ((is "assert")
              (begin
                (if (not (= 2 n)) (begin (fail! s "invalid assert command") #u)
                    (let ((t (parse-term s (nth l 1) nil)))
                      (cond ((bad? s) #u)
                            ((not (term-bool? t)) (begin (fail! s "invalid assert command, term is not Boolean") #u))
                            (else (begin (smt-assert! smt t) (success s))))))
                cmd-go))
             ((is "push")
              (let ((k (if (> n 1) (nth l 1) (sx-num 1))))
                (begin (if (not (nat? k)) (begin (fail! s "invalid push command") #u)
                           (begin (letrec ((go (subr cb-eff (int) unit) (lambda (i) (if (= i (nat-value k)) #u (begin (push-scope! s) (go (+ i 1)))))))
                                    (go 0))
                                  (success s)))
                       cmd-go)))
             ((is "pop")
              (let ((k (if (> n 1) (nth l 1) (sx-num 1))))
                (begin (cond ((not (nat? k)) (begin (fail! s "invalid pop command") #u))
                             ((> (nat-value k) (list-length (get (extract s scopes))))
                              (begin (fail! s "invalid pop command, argument is greater than the current stack depth") #u))
                             (else (begin (letrec ((go (subr cb-eff (int) unit) (lambda (i) (if (= i (nat-value k)) #u (begin (pop-scope! s) (go (+ i 1)))))))
                                            (go 0))
                                          (success s))))
                       cmd-go)))
             ((is "check-sat") (begin (write-answer s (smt-check smt nil)) cmd-go))
             ((is "check-sat-assuming")
              (begin
                (if (not (and (= 2 n) (sxlist? (nth l 1)))) (begin (fail! s "invalid check-sat-assuming command") #u)
                    (let ((ts (parse-terms s (items (nth l 1)) nil)))
                      (cond ((bad? s) #u)
                            ((not (letrec ((go (subr cb-eff (ints) bool) (lambda (l) (or (null? l) (and (term-bool? (car l)) (go (cdr l))))))) (go ts)))
                             (begin (fail! s "invalid check-sat-assuming command, Boolean expected") #u))
                            (else (write-answer s (smt-check smt ts))))))
                cmd-go))
             ((is "get-model")
              (begin
                (if (need-model s)
                    (begin
                      (out! s "(\n")
                      (letrec ((go (subr cb-eff ((listof def acyclic)) unit)
                                 (lambda (ds)
                                   (if (null? ds) #u
                                       (let ((dn (symbol->smt-string (extract (car ds) name))))
                                         (begin
                                           (tagcase (extract (car ds) entry)
                                             (e-const (k t)
                                               (if (var-term? t)
                                                   (out! s (str* (list "  (define-fun " dn " () " (sort->string (term-sort t)) "\n    "
                                                                       (value->string (smt-value smt t) (term-sort t)) ")\n")))
                                                   #u))
                                             (e-fun (k f)
                                               (if (null? (extract f params))
                                                   (out! s (str* (list "  (define-fun " dn " () " (sort->string (extract f sort)) "\n    " (sexp->string (extract f body)) ")\n")))
                                                   #u))
                                             (e-none () #u))
                                           (go (cdr ds))))))))
                        (go (reverse-defs (get (extract s defs)))))
                      (out! s ")\n"))
                    #u)
                cmd-go))
             ((is "get-value")
              (begin
                (cond ((not (and (= 2 n) (sxlist? (nth l 1)) (pair? (items (nth l 1))))) (begin (fail! s "invalid get-value command") #u))
                      ((not (need-model s)) #u)
                      (else
                       (let ((ts (parse-terms s (items (nth l 1)) nil)))
                         (if (bad? s) #u
                             (begin
                               (out! s "(")
                               (letrec ((go (subr cb-eff (sexps ints bool) unit)
                                          (lambda (xs ts first?)
                                            (if (null? xs) #u
                                                (begin (out! s (str* (list (if first? "" "\n ") "(" (sexp->string (car xs)) " "
                                                                           (value->string (smt-value smt (car ts)) (term-sort (car ts))) ")")))
                                                       (go (cdr xs) (cdr ts) #f))))))
                                 (go (items (nth l 1)) ts #t))
                               (out! s ")\n"))))))
                cmd-go))
             ((is "echo") (begin (out! s (string-append (if (> n 1) (tagcase (nth l 1) (sx-str (x) x) (else y "")) "") "\n")) cmd-go))
             ((is "reset")
              (begin (set (extract s smt) (make-smt))
                     (set (extract s names) (new-names))
                     (set (extract s scopes) nil)
                     (set (extract s defs) nil)
                     (set (extract s print-success) #f)
                     (success s)
                     cmd-go))
             ((is "reset-assertions")
              (begin
                (letrec ((go (subr cb-eff () unit) (lambda () (if (null? (get (extract s scopes))) #u (begin (pop-scope! s) (go))))))
                  (go))
                ;; Level 0's assertions go with a new context; its names stay.
                (let ((new-smt (make-smt)))
                  (begin (smt-set-timeout! new-smt (smt-timeout (session-smt s))) (set (extract s smt) new-smt)))
                (success s)
                cmd-go))
             ((is "exit") cmd-exit)
             (else
              ;; As z3: a note on the standard error too.
              (begin (out! s "unsupported\n")
                     (set (extract s errout) (cons (str* (list "; " (sexp->string (car l)) "\n")) (get (extract s errout))))
                     cmd-go))))))))

(define* reverse-defs (subr spin ((listof def acyclic)) (listof def acyclic))
  (lambda (l) (letrec ((go (subr spin ((listof def acyclic) (listof def acyclic)) (listof def acyclic)) (lambda (l acc) (if (null? l) acc (go (cdr l) (cons (car l) acc))))))
                (go l nil))))

;;; ------------------------------------------------------------ the loop

;; Where a run stops.
(define run-more int 0)                ; it has read all the text fed: more may come
(define run-end int 1)                 ; the end of the input, or exit
(define run-stop int 2)                ; a syntax error: nothing after it runs

(define* report! (subr cb-eff (session sexp-reader string) unit)
  (lambda (s r message)
    (begin (set (extract s errors) #t)
           (out! s (str* (list "(error \"line " (int->string (sexp-reader-line r)) " column " (int->string (max 0 (- (sexp-reader-column r) 1))) ": " message "\")\n"))))))

"Run the commands the reader has, until it needs more text, the input
ends, or a command exits; the answers are the session's output."
(define* smtlib-run! (subr cb-eff (session sexp-reader) int)
  (lambda (s r)
    (tagcase (sexp-read r)
      (r-more () run-more)
      (r-eof () run-end)
      (r-error (m line col) (begin (set (extract s errors) #t)
                                   (out! s (str* (list "(error \"line " (int->string line) " column " (int->string (max 0 (- col 1))) ": " m "\")\n")))
                                   run-stop))
      (r-datum (cmd)
        (let ((what (begin (set (extract s err) "") (run-command s cmd))))
          (begin
            (if (bad? s) (report! s r (get (extract s err))) #u)
            (set (extract s err) "")
            (if (= what cmd-exit) run-end (smtlib-run! s r))))))))
