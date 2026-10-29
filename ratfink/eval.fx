;;; eval.fx: symbolic evaluation of Scheme programs: shakedown's
;;; `(shakedown eval)`.
;;;
;;; An expression is compiled once to a procedure of a frame and a context
;;; (core.fx's rf-proc), which computes its value; the value may be
;;; symbolic. An if whose test is symbolic evaluates both arms, under the
;;; test and its negation, and merges what they give.
;;;
;;; Frames are arrays: slot 0 holds the enclosing frame, and the others the
;;; variables, at indexes found when compiling. Globals are cells (one-slot
;;; arrays), so that the store can log writes to either.
;;;
;;; The unwinding bound: a procedure's activation counts against it when the
;;; procedure is already active, further out, and evaluation has gone into a
;;; symbolic branch since then.
;;;
;;; Contracts (define/contract, contracts-for), loops with invariants, and
;;; libraries are as shakedown has them: see its eval.sld, whose comments
;;; are kept here where the code is.
;;;
;;; Order: where shakedown's code compiles parts of a form in a `let`'s
;;; inits, they are compiled here in the order Twobit runs them (right to
;;; left), since compiling makes aliases and temporaries whose names a
;;; playback program shows.

(module-parameters ((m-core (load-moduleof "core.fx")) (m-term (load-moduleof "term.fx" m-core))
                    (m-value (load-moduleof "value.fx" m-core m-term))
                    (m-print (load-moduleof "print.fx" m-core))
                    (m-syntax (load-moduleof "syntax.fx" m-core m-print))
                    (m-numbers (load-moduleof "numbers.fx" m-core))
                    (m-reader (load-moduleof "reader.fx" m-core m-numbers))
                    (m-machine (load-moduleof "machine.fx" m-core m-term m-value))
                    (m-prims (load-moduleof "prims.fx" m-core m-term m-value m-print m-syntax m-numbers m-reader m-machine))
                    (m-hashtables (load-moduleof "hashtables.fx" m-core m-term m-value m-print m-syntax m-numbers m-reader m-machine m-prims))
                    (m-ports (load-moduleof "ports.fx" m-core m-term m-value m-print m-syntax m-numbers m-reader m-machine m-prims m-hashtables))
                    (m-prelude (load-moduleof "prelude.fx" m-core m-numbers m-reader))
                    (m-library (load-moduleof "library.fx" m-core m-print m-syntax m-numbers m-reader))))

;;; ------------------------------------------------------------ small things

(define L1 (subr rf-st (rf-value) rf-value) (lambda (a) (rf-list1 a)))
(define L2 (subr rf-st (rf-value rf-value) rf-value) (lambda (a b) (rf-list2 a b)))
(define L3 (subr rf-st (rf-value rf-value rf-value) rf-value) (lambda (a b c) (rf-list3 a b c)))
(define L4 (subr rf-st (rf-value rf-value rf-value rf-value) rf-value) (lambda (a b c d) (rf-cons a (rf-list3 b c d))))
(define head-is? (subr rf-st (rf-value symbol) bool)
  (lambda (x s) (and (rf-pair? x) (rf-eqv? (rf-car x) (rf-sym s)))))
(define str-of-sym (subr rf-st (rf-value) string) (lambda (v) (symbol->string (rf-sym-of v))))

"shakedown's (error (string-append \"shakedown: \" message) form)."
(define syntax-error (subr rf-eff (string rf-value) void)
  (lambda (message form) (rf-error (string-append "ratfink: " message) (list form))))

;;; ------------------------------------------------------------ globals

(define new-genv (subr rf-st ((sumof (none unit) (some rf-genv))) rf-genv)
  (lambda (parent)
    (product (cells (the (table symbol rf-slots @rf) (make-table symbol-hash symbol=?)))
             (macros (the (table symbol rf-maybe-macro @rf) (make-table symbol-hash symbol=?)))
             (parent parent))))
"The global environment being compiled in, and the built-in one."
(define globals (ref rf-genv @rf) (new (new-genv (sum none #u))))
(define builtin-genv (ref rf-genv @rf) (new (get globals)))

(define new-cell (subr rf-st (rf-value) rf-slots) (lambda (v) (the rf-slots (make-array 1 v))))
"The cell of name, in genv or what it inherits from; one of genv's own,
unbound, if there is none."
(define global-cell-in (subr rf-st (symbol rf-genv) rf-slots)
  (lambda (name genv)
    (letrec ((find (subr rf-st (rf-genv) (sumof (none unit) (some rf-slots)))
               (lambda (g)
                 (if (table-has? (extract g cells) name)
                     (sum some (table-ref (extract g cells) name no-slots))
                     (tagcase (extract g parent) (some p (find p)) (none u (sum none #u)))))))
      (tagcase (find genv)
        (some c c)
        (none u (let ((cell (new-cell rf-unbound))) (begin (table-set! (extract genv cells) name cell) cell)))))))
(define global-cell (subr rf-st (symbol) rf-slots) (lambda (name) (global-cell-in name (get globals))))
(define global-macro (subr rf-st (symbol rf-genv) (sumof (none unit) (some rf-macro)))
  (lambda (name genv)
    (tagcase (table-ref (extract genv macros) name (sum none #u))
      (some m (sum some m))
      (none u (tagcase (extract genv parent) (some p (global-macro name p)) (none u (sum none #u)))))))
"A cell of genv's own for name (not inherited), new if need be."
(define own-cell! (subr rf-st (symbol rf-genv) rf-slots)
  (lambda (name genv)
    (if (table-has? (extract genv cells) name) (table-ref (extract genv cells) name no-slots)
        (let ((cell (new-cell rf-unbound))) (begin (table-set! (extract genv cells) name cell) cell)))))
(define define-global! (subr rf-st (symbol rf-value) unit)
  (lambda (name v)
    (begin (table-set! (extract (get globals) macros) name (sum none #u))
           (array-set! (global-cell name) 0 v))))
(define define-global-macro! (subr rf-st (symbol rf-macro) unit)
  (lambda (name m) (table-set! (extract (get globals) macros) name (sum some m))))

;;; ------------------------------------------------------------ proofs

(define-type proof
  (productof (name symbol) (unwind int) (split bool) (stubs symbols) (for-contract (sumof (none unit) (some symbol)))
             (body rf-value) (source rf-value) (library rf-value)))
(define-type proofs (listof proof acyclic))
(define the-proofs (ref proofs @rf) (new nil))
(define all-proofs (subr rf-st () proofs) (lambda () (the proofs (reverse (get the-proofs)))))

;;; ------------------------------------------------------------ compile-time environments

(define var-depth (subr rf-st (rf-cenv) int)
  (lambda (cenv) (cond ((null? cenv) 0) (else (tagcase (car cenv) (vframe v (+ 1 (var-depth (cdr cenv)))) (sframe s (var-depth (cdr cenv))))))))

"What x means in cenv: a local variable, a macro, or a global."
(define-type resolution
  (sumof (var (productof (depth int) (index int))) (macro rf-macro) (global (productof (name symbol) (genv rf-genv)))))
(define resolve (subr rf-st (rf-cenv symbol) resolution)
  (lambda (cenv x)
    (letrec ((loop (subr rf-st (rf-cenv int) resolution)
               (lambda (frames depth)
                 (if (null? frames)
                     (if (alias? x)
                         (let ((r (resolve-in (alias-cenv x) (alias-symbol x) (alias-genv x))))
                           (tagcase r
                             ;; The macro's environment is inside this one.
                             (var v (sum var (product (depth (+ (extract v depth) (- (var-depth cenv) (var-depth (alias-cenv x))))) (index (extract v index)))))
                             (else y r)))
                         (tagcase (global-macro x (get globals))
                           (some m (sum macro m))
                           (none u (sum global (product (name x) (genv (get globals)))))))
                     (tagcase (car frames)
                       (vframe vf
                         (letrec ((find (subr rf-st (symbols int) resolution)
                                    (lambda (vars i)
                                      (cond ((null? vars) (loop (cdr frames) (+ depth 1)))
                                            ((eq? (car vars) x) (sum var (product (depth depth) (index i))))
                                            (else (find (cdr vars) (+ i 1)))))))
                           (find (get (extract vf vars)) 1)))
                       (sframe sf
                         (letrec ((find (subr rf-st ((listof (productof (name symbol) (macro rf-macro)) acyclic)) resolution)
                                    (lambda (ms) (cond ((null? ms) (loop (cdr frames) depth))
                                                       ((eq? (extract (car ms) name) x) (sum macro (extract (car ms) macro)))
                                                       (else (find (cdr ms)))))))
                           (find (get sf)))))))))
      (loop cenv 0))))
"As resolve, with genv as the global environment."
(define resolve-in (subr rf-st (rf-cenv symbol rf-genv) resolution)
  (lambda (cenv x genv)
    (let ((outer (get globals)))
      (begin (set globals genv)
             (let ((r (resolve cenv x))) (begin (set globals outer) r))))))
(define resolve-value (subr rf-st (rf-cenv rf-value) (sumof (none unit) (some resolution)))
  (lambda (cenv x) (tagcase x (sym s (sum some (resolve cenv s))) (else y (sum none #u)))))
"The special form or global name a form's head is, if it is one: '|| if not."
(define head-keyword (subr rf-st (rf-cenv rf-value) symbol)
  (lambda (cenv head)
    (tagcase (resolve-value cenv head)
      (some r (tagcase r (global g (extract g name)) (else y '||)))
      (none u '||))))
(define lookup (subr rf-st (rf-cenv symbol) (sumof (none unit) (some (productof (depth int) (index int)))))
  (lambda (cenv x) (tagcase (resolve cenv x) (var v (sum some v)) (else y (sum none #u)))))

(define expand (subr rf-eff (rf-cenv rf-macro rf-value) rf-value)
  (lambda (cenv m x) (expand-macro m x syntax-error)))
(define frame-up (subr rf-st (rf-slots int) rf-slots)
  (lambda (env depth) (if (= depth 0) env (frame-up (rf-slots-of (array-ref env 0)) (- depth 1)))))
(define constant (subr rf-st (rf-value) rf-proc) (lambda (v) (lambda ((env rf-slots) (ctx rf-ctx)) v)))

;;; ------------------------------------------------------------ compiling

"A loop with an invariant whose body an expression is in tail position of."
(define-type tail-loop (sumof (none unit) (some rf-loop)))
(define no-tail tail-loop (sum none #u))
"A special form's compiler: of the form, the compile-time environment and
the hint (what the value will be bound to, or #f)."
(define-type special (subr rf-eff (rf-value rf-cenv rf-value) rf-proc))
(define special-forms (ref (table symbol special @rf) @rf) (new (the (table symbol special @rf) (make-table symbol-hash symbol=?))))
(define special-form (subr rf-st (symbol) (sumof (none unit) (some special)))
  (lambda (name) (if (table-has? (get special-forms) name) (sum some (table-ref (get special-forms) name (lambda ((x rf-value) (c rf-cenv) (h rf-value)) (constant x)))) (sum none #u))))
(define define-special! (subr rf-st (symbol special) unit)
  (lambda (name proc) (table-set! (get special-forms) name proc)))
"The tail of the special form being compiled."
(define form-tail (ref tail-loop @rf) (new no-tail))
"A special form defined by rewriting into others."
(define define-rewrite! (subr rf-st (symbol (subr rf-eff (rf-value) rf-value)) unit)
  (lambda (name rewrite)
    (define-special! name (lambda ((x rf-value) (cenv rf-cenv) (hint rf-value))
                            (let ((tail (get form-tail)))
                              (compile (rewrite x) cenv hint tail))))))

"Compile expression x in cenv; hint names what the value will be bound to;
tail is the loop with an invariant whose body x is in tail position of."
(define compile (subr rf-eff (rf-value rf-cenv rf-value tail-loop) rf-proc)
  (lambda (x cenv hint tail)
    (tagcase x
      (sym s (compile-reference x cenv))
      (pair p
        (let ((r (resolve-value cenv (array-ref p 0))))
          (tagcase r
            (some res
              (tagcase res
                (macro m (compile (expand cenv m x) cenv hint tail))
                (global g (tagcase (special-form (extract g name))
                            (some sp (begin (set form-tail tail) (sp x cenv hint)))
                            (none u (compile-application x cenv tail))))
                (else y (compile-application x cenv tail))))
            (none u (compile-application x cenv tail)))))
      (null u (begin (syntax-error "empty combination" x) (constant x)))
      (else y (constant x)))))
(define compile0 (subr rf-eff (rf-value rf-cenv) rf-proc) (lambda (x cenv) (compile x cenv rf-false no-tail)))

"The loop with an invariant that a variable reference names, if any."
(define loop-named (subr rf-st (rf-cenv resolution) tail-loop)
  (lambda (cenv r)
    (tagcase r
      (var v
        (letrec ((find (subr rf-st (rf-cenv int) tail-loop)
                   (lambda (frames depth)
                     (cond ((null? frames) no-tail)
                           (else (tagcase (car frames)
                                   (sframe s (find (cdr frames) depth))
                                   (vframe vf
                                     (if (> depth 0) (find (cdr frames) (- depth 1))
                                         (letrec ((at (subr rf-st ((listof rf-loop-at acyclic)) tail-loop)
                                                    (lambda (l) (cond ((null? l) no-tail)
                                                                      ((= (extract (car l) index) (extract v index)) (sum some (extract (car l) loop)))
                                                                      (else (at (cdr l)))))))
                                           (at (get (extract vf loops))))))))))))
          (find cenv (extract v depth))))
      (else y no-tail))))
(define some-loop? (subr rf-st (tail-loop) bool) (lambda (t) (tagcase t (some l #t) (none u #f))))

(define abstraction (ref string @rf) (new ""))

(define compile-reference (subr rf-eff (rf-value rf-cenv) rf-proc)
  (lambda (x cenv)
    (let ((r (resolve cenv (rf-sym-of x))))
      (begin
        (if (some-loop? (loop-named cenv r))
            (syntax-error "a loop with an invariant can only be called, in tail position" (strip x)) #u)
        (tagcase r
          (var v
            (let ((depth (extract v depth)) (i (extract v index)))
              (lambda ((env rf-slots) (ctx rf-ctx))
                (let ((val (array-ref (frame-up env depth) i)))
                  (if (rf-unassigned? val)
                      (begin (fail! ctx 'error (string-append (datum->string x) ": used before it was assigned")) val)
                      val)))))
          (macro m (begin (syntax-error "a macro used as a variable" (strip x)) (constant x)))
          (global g
            (begin
              ;; A program that can mutate pairs has them merged as unions.
              (if (or (eq? (extract g name) 'set-car!) (eq? (extract g name) 'set-cdr!)) (set-pairs-mutable! #t) #u)
              (let ((cell (global-cell-in (extract g name) (extract g genv))))
                (lambda ((env rf-slots) (ctx rf-ctx))
                  (let ((val (array-ref cell 0)))
                    (if (rf-unbound? val)
                        (begin
                          ;; Larceny would not compile the playback program.
                          (if (string=? (get abstraction) "")
                              (set abstraction "the program refers to a variable it does not define") #u)
                          (fail! ctx 'error (string-append "undefined variable: " (datum->string x)))
                          val)
                        val)))))))))))

(define compile-application (subr rf-eff (rf-value rf-cenv tail-loop) rf-proc)
  (lambda (x cenv tail)
    (let* ((r (resolve-value cenv (rf-car x)))
           (loop (tagcase r (some res (loop-named cenv res)) (none u no-tail))))
      (tagcase loop
        (some l (if (tagcase tail (some t (eq? (extract t invariants) (extract l invariants))) (none u #f))
                    (compile-back-edge x cenv l)
                    (begin (syntax-error "a loop with an invariant can only be called, in tail position" (strip x)) (constant x))))
        (none u (compile-call x cenv))))))

(define compile-call (subr rf-eff (rf-value rf-cenv) rf-proc)
  (lambda (x cenv)
    ;; shakedown's (let ((f …) (args …) (located? …)) …): args first.
    (let* ((located? (not (string=? (source-location x) "")))
           (args (map (lambda ((a rf-value)) (compile0 a cenv)) (rf-elements (rf-cdr x))))
           (f (compile0 (rf-car x) cenv)))
      (lambda ((env rf-slots) (ctx rf-ctx))
        (let* ((fv (f env ctx))
               (vs (map (lambda ((a rf-proc)) (a env ctx)) args)))
          (begin
            (if located? (note-source! x) #u)
            (apply-value ctx fv vs x)))))))

(define at-source! (subr rf-st (rf-value) unit)
  (lambda (x) (if (string=? (source-location x) "") #u (note-source! x))))

(define compile-sequence (subr rf-eff (rf-vals rf-cenv tail-loop) rf-proc)
  (lambda (forms cenv tail)
    (if (null? forms) (constant rf-unspecified)
        (let ((procs (letrec ((loop (subr rf-eff (rf-vals) (listof rf-proc acyclic))
                                (lambda (forms)
                                  (if (null? (cdr forms))
                                      (list (compile (car forms) cenv rf-false tail))
                                      (let ((p (compile0 (car forms) cenv))) (cons p (loop (cdr forms))))))))
                       (loop forms))))
          (lambda ((env rf-slots) (ctx rf-ctx))
            (letrec ((loop (subr rf-eff ((listof rf-proc acyclic)) rf-value)
                       (lambda (procs) (if (null? (cdr procs)) ((car procs) env ctx) (begin ((car procs) env ctx) (loop (cdr procs)))))))
              (loop procs)))))))

"A definition found scanning a body: its name and expression."
(define-type def (productof (name symbol) (expr rf-value)))
(define-type defs (listof def acyclic))
(define-type scanned (productof (defs defs) (exprs rf-vals)))

"The definitions at the start of a body, spliced, with macro uses expanded;
macros it defines go in sf, variables in vf, as they are found."
(define scan-body (subr rf-eff (rf-vals rf-cenv rf-sframe rf-vframe) scanned)
  (lambda (forms cenv sf vf)
    (letrec ((loop (subr rf-eff (rf-vals defs) scanned)
               (lambda (forms defs)
                 (if (null? forms) (product (defs (the defs (reverse defs))) (exprs nil))
                     (let* ((form (car forms))
                            (r (if (rf-pair? form) (resolve-value cenv (rf-car form)) (sum none #u)))
                            (keyword (tagcase r (some res (tagcase res (global g (extract g name)) (else y '||))) (none u '||)))
                            (m (tagcase r (some res (tagcase res (macro m (the rf-maybe-macro (sum some m))) (else y (the rf-maybe-macro (sum none #u))))) (none u (sum none #u)))))
                       (tagcase m
                         (some mac (loop (cons (expand cenv mac form) (cdr forms)) defs))
                         (none u
                           (cond ((eq? keyword 'begin) (loop (vals-append (rf-elements (rf-cdr form)) (cdr forms)) defs))
                                 ((or (eq? keyword 'include) (eq? keyword 'include-ci))
                                  (loop (vals-append (included-forms form syntax-error) (cdr forms)) defs))
                                 ((eq? keyword 'define-values)
                                  (loop (vals-append (define-values->defines form) (cdr forms)) defs))
                                 ((eq? keyword 'define)
                                  (let ((d (normalize-define form)))
                                    (begin (set (extract vf vars) (append (get (extract vf vars)) (list (extract d name))))
                                           (loop (cdr forms) (cons d defs)))))
                                 ((eq? keyword 'define-syntax)
                                  (begin
                                    (if (and (rf-list? form) (= (rf-length form) 3) (rf-symbol? (rf-cadr form))) #u
                                        (syntax-error "bad define-syntax" (strip form)))
                                    (set sf (cons (product (name (rf-sym-of (rf-cadr form))) (macro (make-macro (rf-caddr form) cenv)))
                                                  (get sf)))
                                    (loop (cdr forms) defs)))
                                 (else (product (defs (the defs (reverse defs))) (exprs forms)))))))))))
      (loop forms nil))))

(define make-macro (subr rf-eff (rf-value rf-cenv) rf-macro)
  (lambda (spec cenv) (make-syntax-rules spec cenv (get globals) syntax-error)))

(define normalize-define (subr rf-eff (rf-value) def)
  (lambda (form)
    (cond ((and (rf-pair? (rf-cdr form)) (rf-symbol? (rf-cadr form)))
           (product (name (rf-sym-of (rf-cadr form)))
                    (expr (if (rf-pair? (rf-cddr form)) (rf-caddr form) (L3 (q 'if) rf-false rf-false)))))
          ((and (rf-pair? (rf-cdr form)) (rf-pair? (rf-cadr form)))
           (let ((target (rf-cadr form)))
             ;; Curried define: (define ((f a) b) …).
             (normalize-define (L3 (q 'define) (rf-car target) (rf-cons (q 'lambda) (rf-cons (rf-cdr target) (rf-cddr form)))))))
          (else (begin (syntax-error "bad define" form) (product (name '||) (expr rf-false)))))))

"A body's frame size and code: its frame holds params and its internal
definitions, assigned in order, as letrec* does."
(define-type sized (productof (size int) (proc rf-proc)))
(define compile-body (subr rf-eff (rf-vals rf-cenv symbols tail-loop) sized)
  (lambda (forms cenv params tail)
    (let* ((vf (the rf-vframe (product (vars (new params)) (loops (new nil)))))
           (sf (the rf-sframe (new nil)))
           (cenv (the rf-cenv (cons (sum sframe sf) (cons (sum vframe vf) cenv))))
           (s (scan-body forms cenv sf vf))
           (vars (get (extract vf vars)))
           (inits (map (lambda ((d def))
                         (let* ((i (tagcase (lookup cenv (extract d name)) (some v (extract v index)) (none u 0)))
                                (code (compile (extract d expr) cenv (rf-sym (extract d name)) no-tail)))
                           (product (index i) (code code))))
                       (extract s defs)))
           (body (compile-sequence (extract s exprs) cenv tail)))
      (product (size (list-length vars))
               (proc (if (null? inits) body
                         (lambda ((env rf-slots) (ctx rf-ctx))
                           (begin
                             (for-each (lambda ((init (productof (index int) (code rf-proc))))
                                         (let ((v ((extract init code) env ctx))) (write! ctx env (extract init index) v)))
                                       inits)
                             (body env ctx)))))))))

"Formals: the required names, and the rest's (|| if none)."
(define-type formals (productof (req symbols) (rest symbol)))
(define parse-formals (subr rf-eff (rf-value) formals)
  (lambda (fs)
    (letrec ((loop (subr rf-eff (rf-value symbols) formals)
               (lambda (f req)
                 (tagcase f
                   (null u (product (req (symbols-reverse req)) (rest '||)))
                   (sym s (product (req (symbols-reverse req)) (rest s)))
                   (pair p (if (rf-symbol? (array-ref p 0)) (loop (array-ref p 1) (cons (rf-sym-of (array-ref p 0)) req))
                               (begin (syntax-error "bad formals" fs) (product (req nil) (rest '||)))))
                   (else x (begin (syntax-error "bad formals" fs) (product (req nil) (rest '||))))))))
      (loop fs nil))))
(define has-rest? (subr rf-st (formals) bool) (lambda (f) (not (eq? (extract f rest) '||))))
(define formals-names (subr rf-st (formals) symbols)
  (lambda (f) (if (has-rest? f) (append (extract f req) (list (extract f rest))) (extract f req))))

(define compile-lambda (subr rf-eff (rf-value rf-cenv rf-value) rf-proc)
  (lambda (x cenv hint)
    (begin
      (if (and (rf-pair? (rf-cdr x)) (rf-pair? (rf-cddr x))) #u (syntax-error "bad lambda" x))
      (let* ((f (parse-formals (rf-cadr x)))
             (b (compile-body (rf-elements (rf-cddr x)) cenv (formals-names f) no-tail))
             (code (the rf-code (product (name (strip-name (if (rf-symbol? hint) (rf-sym-of hint) 'lambda)))
                                         (required (list-length (extract f req))) (rest (has-rest? f))
                                         (size (extract b size)) (body (extract b proc))))))
        (lambda ((env rf-slots) (ctx rf-ctx)) (sum closure (product (code code) (env env))))))))

"A frame of size+1 slots, its enclosing frame env, noted as allocated."
(define new-frame (subr rf-st (int rf-slots) rf-slots)
  (lambda (size env)
    (let ((frame (note-allocation! (the rf-slots (make-array (+ size 1) rf-unassigned)))))
      (begin (array-set! frame 0 (sum frame env)) frame))))

"(let ((v init) …) body …) without a name; bindings as (name init)."
(define compile-let (subr rf-eff (rf-vals rf-vals rf-cenv tail-loop) rf-proc)
  (lambda (bindings body cenv tail)
    (let* ((vars (map (lambda ((b rf-value)) (rf-sym-of (rf-car b))) bindings))
           (inits (map (lambda ((b rf-value)) (compile (rf-cadr b) cenv (rf-car b) no-tail)) bindings))
           (sb (compile-body body cenv vars tail))
           (size (extract sb size)) (proc (extract sb proc)))
      (lambda ((env rf-slots) (ctx rf-ctx))
        (let ((frame (new-frame size env)))
          (letrec ((loop (subr rf-eff ((listof rf-proc acyclic) int) unit)
                     (lambda (inits i) (if (null? inits) #u (begin (array-set! frame i ((car inits) env ctx)) (loop (cdr inits) (+ i 1)))))))
            (begin (loop inits 1) (proc frame ctx))))))))

(define check-bindings (subr rf-eff (rf-value rf-value) unit)
  (lambda (bindings x)
    (if (and (rf-list? bindings)
             (letrec ((ok (subr rf-st (rf-value) bool)
                        (lambda (bs) (or (rf-null? bs)
                                         (let ((b (rf-car bs)))
                                           (and (rf-pair? b) (rf-symbol? (rf-car b)) (rf-list? b) (<= 1 (rf-length b)) (<= (rf-length b) 2)
                                                (ok (rf-cdr bs))))))))
               (ok bindings)))
        #u
        (syntax-error "bad bindings" x))))
(define binding-init (subr rf-st (rf-value) rf-value)
  (lambda (b) (if (rf-pair? (rf-cdr b)) (rf-cadr b) (L3 (q 'if) rf-false rf-false))))

;;; ------------------------------------------------------------ special forms

"Whether to note the branches of ifs being compiled: not the prelude's."
(define tracing? (ref bool @rf) (new #t))

"A variable for a rewrite, which no program can name; fresh for each."
(define temp-count (ref int @rf) (new 0))
(define fresh-temp (subr rf-st () rf-value)
  (lambda () (begin (set temp-count (+ 1 (get temp-count)))
                    (rf-sym (string->symbol (string-append " temp" (int->string (get temp-count))))))))
(define temp? (subr rf-st (rf-value) bool)
  (lambda (x) (tagcase x (sym s (let ((n (symbol->string s))) (and (> (string-length n) 5) (string=? (substring n 0 5) " temp")))) (else y #f))))
"The test of an if, for a trace, or #f for one of a rewrite's."
(define traced-test (subr rf-eff (rf-value) rf-value)
  (lambda (test)
    (let ((t (strip test)))
      (if (letrec ((mentions? (subr rf-st (rf-value) bool)
                     (lambda (t) (or (temp? t) (and (rf-pair? t) (or (mentions? (rf-car t)) (mentions? (rf-cdr t))))))))
            (mentions? t))
          rf-false t))))

(define install-core-forms! (subr rf-st () unit)
  (lambda ()
    (begin
      (define-special! 'quote (lambda ((x rf-value) (cenv rf-cenv) (hint rf-value)) (constant (strip (rf-cadr x)))))
      (define-special! 'if
        (lambda ((x rf-value) (cenv rf-cenv) (hint rf-value))
          (begin
            (if (and (<= 3 (rf-length x)) (<= (rf-length x) 4)) #u (syntax-error "bad if" x))
            (let* ((tail (get form-tail))
                   (src (if (get tracing?) (traced-test (rf-cadr x)) rf-false))
                   (test (compile0 (rf-cadr x) cenv))
                   (then (compile (rf-caddr x) cenv hint tail))
                   (else (if (rf-pair? (rf-cdddr x)) (compile (rf-cadddr x) cenv hint tail) (constant rf-unspecified))))
              (lambda ((env rf-slots) (ctx rf-ctx))
                (let ((c (truth (test env ctx))))
                  (cond ((rf-true? c) (then env ctx))
                        ((rf-false? c) (else env ctx))
                        (else
                         (begin
                           (if (rf-false? src) #u (note-branch! ctx c src))
                           (join ctx (list (make-arm c (lambda ((ctx rf-ctx)) (then env ctx)))
                                           (make-arm (t-not c) (lambda ((ctx rf-ctx)) (else env ctx))))
                                 #t))))))))))
      (define-special! 'lambda compile-lambda)
      (define-special! 'begin
        (lambda ((x rf-value) (cenv rf-cenv) (hint rf-value)) (compile-sequence (rf-elements (rf-cdr x)) cenv (get form-tail))))
      (define-special! 'set!
        (lambda ((x rf-value) (cenv rf-cenv) (hint rf-value))
          (begin
            (if (and (= (rf-length x) 3) (rf-symbol? (rf-cadr x))) #u (syntax-error "bad set!" x))
            (let* ((value (compile (rf-caddr x) cenv (rf-cadr x) no-tail))
                   (r (resolve cenv (rf-sym-of (rf-cadr x)))))
              (tagcase r
                (var v (let ((depth (extract v depth)) (i (extract v index)))
                         (lambda ((env rf-slots) (ctx rf-ctx))
                           (let ((val (value env ctx))) (begin (write! ctx (frame-up env depth) i val) rf-unspecified)))))
                (macro m (begin (syntax-error "set! of a macro" (strip x)) (constant rf-unspecified)))
                (global g (let ((cell (global-cell-in (extract g name) (extract g genv))))
                            (lambda ((env rf-slots) (ctx rf-ctx))
                              (let ((val (value env ctx))) (begin (write! ctx cell 0 val) rf-unspecified))))))))))
      (define-special! 'define
        (lambda ((x rf-value) (cenv rf-cenv) (hint rf-value)) (begin (syntax-error "define is not allowed here" (strip x)) (constant x))))
      (define-special! 'define-values
        (lambda ((x rf-value) (cenv rf-cenv) (hint rf-value)) (begin (syntax-error "define-values is not allowed here" (strip x)) (constant x))))
      ;; (include file …), include-ci: the files' forms, read when compiling, as a begin.
      (define-special! 'include compile-include)
      (define-special! 'include-ci compile-include)
      ;; load, which reads at run time, only at the top level.
      (define-special! 'load
        (lambda ((x rf-value) (cenv rf-cenv) (hint rf-value))
          (if (rf-unbound? (array-ref (global-cell 'load) 0))
              (begin (syntax-error "load is supported only at the top level, of a string" (strip x)) (constant x))
              (compile-application x cenv (get form-tail)))))
      (define-special! 'define-syntax
        (lambda ((x rf-value) (cenv rf-cenv) (hint rf-value)) (begin (syntax-error "define-syntax is not allowed here" (strip x)) (constant x))))
      (define-special! 'let-syntax (compile-let-syntax #f))
      (define-special! 'letrec-syntax (compile-let-syntax #t))
      (define-special! 'let
        (lambda ((x rf-value) (cenv rf-cenv) (hint rf-value))
          (let ((tail (get form-tail)))
            (cond ((and (rf-pair? (rf-cdr x)) (rf-symbol? (rf-cadr x)))
                   ;; Named let.
                   (let ((name (rf-cadr x)) (bindings (rf-caddr x)) (body (rf-cdddr x)))
                     (begin
                       (check-bindings bindings x)
                       (if (pair? (extract (loop-clauses body) clauses))
                           (compile-loop x cenv)
                           (compile (rf-cons (L3 (q 'letrec) (L1 (L2 name (rf-cons (q 'lambda) (rf-cons (rf-list (map rf-car (rf-elements bindings))) body)))) name)
                                             (rf-list (map binding-init (rf-elements bindings))))
                                    cenv hint tail)))))
                  ((rf-pair? (rf-cdr x))
                   (begin
                     (check-bindings (rf-cadr x) x)
                     (compile-let (map (lambda ((b rf-value)) (L2 (rf-car b) (binding-init b))) (rf-elements (rf-cadr x)))
                                  (rf-elements (rf-cddr x)) cenv tail)))
                  (else (begin (syntax-error "bad let" x) (constant x)))))))
      (define-rewrite! 'let*
        (lambda ((x rf-value))
          (let ((bindings (rf-cadr x)) (body (rf-cddr x)))
            (begin
              (check-bindings bindings x)
              (if (or (rf-null? bindings) (rf-null? (rf-cdr bindings)))
                  (rf-cons (q 'let) (rf-cons bindings body))
                  (L3 (q 'let) (L1 (rf-car bindings)) (rf-cons (q 'let*) (rf-cons (rf-cdr bindings) body))))))))
      (define-special! 'letrec compile-letrec)
      (define-special! 'letrec* compile-letrec)
      (define-rewrite! 'and
        (lambda ((x rf-value))
          (cond ((rf-null? (rf-cdr x)) rf-true)
                ((rf-null? (rf-cddr x)) (rf-cadr x))
                (else (L4 (q 'if) (rf-cadr x) (rf-cons (q 'and) (rf-cddr x)) rf-false)))))
      (define-rewrite! 'or
        (lambda ((x rf-value))
          (cond ((rf-null? (rf-cdr x)) rf-false)
                ((rf-null? (rf-cddr x)) (rf-cadr x))
                (else (let ((temp (fresh-temp)))
                        (L3 (q 'let) (L1 (L2 temp (rf-cadr x))) (L4 (q 'if) temp temp (rf-cons (q 'or) (rf-cddr x)))))))))
      (define-rewrite! 'when (lambda ((x rf-value)) (L3 (q 'if) (rf-cadr x) (rf-cons (q 'begin) (rf-cddr x)))))
      (define-rewrite! 'unless
        (lambda ((x rf-value)) (L4 (q 'if) (rf-cadr x) (L3 (q 'if) rf-false rf-false) (rf-cons (q 'begin) (rf-cddr x)))))
      (define-rewrite! 'cond
        (lambda ((x rf-value))
          (letrec ((loop (subr rf-eff (rf-value) rf-value)
                     (lambda (clauses)
                       (if (rf-null? clauses) (L3 (q 'if) rf-false rf-false)
                           (let ((clause (rf-car clauses)) (rest (rf-cdr clauses)))
                             (begin
                               (if (rf-pair? clause) #u (syntax-error "bad cond clause" clause))
                               (cond ((keyword? (rf-car clause) 'else) (rf-cons (q 'begin) (rf-cdr clause)))
                                     ((rf-null? (rf-cdr clause)) (let ((r (loop rest))) (L3 (q 'or) (rf-car clause) r)))
                                     ((keyword? (rf-cadr clause) '=>)
                                      (let* ((temp (fresh-temp)) (r (loop rest)))
                                        (L3 (q 'let) (L1 (L2 temp (rf-car clause)))
                                            (L4 (q 'if) temp (L2 (rf-caddr clause) temp) r))))
                                     (else (let ((r (loop rest))) (L4 (q 'if) (rf-car clause) (rf-cons (q 'begin) (rf-cdr clause)) r))))))))))
            (loop (rf-cdr x)))))
      (define-rewrite! 'case
        (lambda ((x rf-value))
          (let ((temp (fresh-temp)))
            (L3 (q 'let) (L1 (L2 temp (rf-cadr x)))
                (rf-cons (q 'cond)
                         (rf-list (map (lambda ((clause rf-value))
                                         (if (keyword? (rf-car clause) 'else) clause
                                             (rf-cons (rf-cons (q 'or) (rf-list (map (lambda ((d rf-value)) (L3 (q 'eqv?) temp (L2 (q 'quote) d))) (rf-elements (rf-car clause)))))
                                                      (rf-cdr clause))))
                                       (rf-elements (rf-cddr x)))))))))
      (define-rewrite! 'do
        (lambda ((x rf-value))
          (let* ((specs (rf-elements (rf-cadr x))) (test (rf-car (rf-caddr x))) (result (rf-cdr (rf-caddr x)))
                 (body (rf-cdddr x)) (loop (rf-sym (string->symbol " do-loop"))))
            (L4 (q 'let) loop (rf-list (map (lambda ((s rf-value)) (L2 (rf-car s) (rf-cadr s))) specs))
                (L4 (q 'if) test
                    (rf-cons (q 'begin) (if (rf-null? result) (L1 (L3 (q 'if) rf-false rf-false)) result))
                    (rf-cons (q 'begin) (rf-append2 body (L1 (rf-cons loop (rf-list (map (lambda ((s rf-value)) (if (rf-pair? (rf-cddr s)) (rf-caddr s) (rf-car s))) specs)))))))))))
      (define-rewrite! 'quasiquote
        (lambda ((x rf-value))
          (letrec ((qq (subr rf-eff (rf-value int) rf-value)
                     (lambda (t depth)
                       (cond ((not (rf-pair? t))
                              (if (rf-vector? t)
                                  (L2 (q 'list->vector) (qq (rf-list (slots-list (rf-slots-of t))) depth))
                                  (L2 (q 'quote) t)))
                             ((keyword? (rf-car t) 'unquote)
                              (if (= depth 1) (rf-cadr t) (L3 (q 'list) (L2 (q 'quote) (q 'unquote)) (qq (rf-cadr t) (- depth 1)))))
                             ((keyword? (rf-car t) 'quasiquote)
                              (L3 (q 'list) (L2 (q 'quote) (q 'quasiquote)) (qq (rf-cadr t) (+ depth 1))))
                             ((and (rf-pair? (rf-car t)) (keyword? (rf-caar t) 'unquote-splicing) (= depth 1))
                              (L3 (q 'append) (rf-cadr (rf-car t)) (qq (rf-cdr t) depth)))
                             (else (L3 (q 'cons) (qq (rf-car t) depth) (qq (rf-cdr t) depth)))))))
            (qq (rf-cadr x) 1)))))))

(define compile-include (subr rf-eff (rf-value rf-cenv rf-value) rf-proc)
  (lambda (x cenv hint)
    (let ((tail (get form-tail)))
      (compile (rf-cons (q 'begin) (rf-list (included-forms x syntax-error))) cenv hint tail))))

"(let-syntax ((name spec) …) body …), and letrec-syntax."
(define compile-let-syntax (subr rf-st (bool) special)
  (lambda (recursive?)
    (lambda ((x rf-value) (cenv rf-cenv) (hint rf-value))
      (let ((tail (get form-tail)))
        (begin
          (if (and (rf-list? x) (<= 3 (rf-length x)) (rf-list? (rf-cadr x))) #u (syntax-error "bad let-syntax" (strip x)))
          (let* ((sf (the rf-sframe (new nil)))
                 (inner (the rf-cenv (cons (sum sframe sf) cenv))))
            (begin
              (set sf (map (lambda ((b rf-value))
                             (begin
                               (if (and (rf-list? b) (= (rf-length b) 2) (rf-symbol? (rf-car b))) #u (syntax-error "bad let-syntax binding" (strip b)))
                               (product (name (rf-sym-of (rf-car b))) (macro (make-macro (rf-cadr b) (if recursive? inner cenv))))))
                           (rf-elements (rf-cadr x))))
              (compile-let nil (rf-elements (rf-cddr x)) inner tail))))))))

(define compile-letrec (subr rf-eff (rf-value rf-cenv rf-value) rf-proc)
  (lambda (x cenv hint)
    (let ((tail (get form-tail)))
      (begin
        (check-bindings (rf-cadr x) x)
        (let* ((sb (compile-body (vals-append (map (lambda ((b rf-value)) (L3 (q 'define) (rf-car b) (binding-init b))) (rf-elements (rf-cadr x)))
                                              (rf-elements (rf-cddr x)))
                                 cenv nil tail))
               (size (extract sb size)) (proc (extract sb proc)))
          (lambda ((env rf-slots) (ctx rf-ctx)) (proc (new-frame size env) ctx)))))))

;;; ------------------------------------------------------------ exceptions, multiple values, parameters

"(k ctx vs) with the list of values v is: once for each member of a union
that has several values in some member."
(define spread (subr rf-eff (rf-ctx rf-value (subr rf-eff (rf-ctx rf-vals) rf-value)) rf-value)
  (lambda (ctx v k)
    (let ((values-of (lambda ((m rf-value)) (tagcase m (multiple vs vs) (else x (the rf-vals (list m)))))))
      (if (and (rf-union? v) (letrec ((any (subr rf-st (rf-members) bool) (lambda (ms) (and (pair? ms) (or (rf-multiple? (extract (car ms) v)) (any (cdr ms)))))))
                               (any (union-members v))))
          (join-union ctx v (lambda ((ctx rf-ctx) (m rf-value)) (k ctx (values-of m))))
          (k ctx (values-of v))))))

"The values vs for formals f, in the order of their names: the required
ones, then the list of the rest."
(define bind-values (subr rf-eff (rf-ctx formals rf-vals rf-value) rf-vals)
  (lambda (ctx f vs src)
    (let ((n (list-length (extract f req))))
      (begin
        (if (if (has-rest? f) (>= (list-length vs) n) (= (list-length vs) n)) #u
            (fail! ctx 'error (describe-call src (string-append "wrong number of values: " (int->string (list-length vs))))))
        (if (has-rest? f) (vals-append (vals-head vs n) (list (rf-list (vals-tail vs n)))) vs)))))

(define define-values-count (ref int @rf) (new 0))
"(define-values formals e), as definitions: of a variable no program can
name, holding the list of the values, and then of each formal."
(define define-values->defines (subr rf-eff (rf-value) rf-vals)
  (lambda (x)
    (begin
      (if (and (rf-list? x) (= (rf-length x) 3)) #u (syntax-error "bad define-values" (strip x)))
      (set define-values-count (+ 1 (get define-values-count)))
      (let* ((t (rf-sym (string->symbol (string-append " values " (int->string (get define-values-count))))))
             (names (formals-names (parse-formals (rf-cadr x)))))
        (cons (L3 (q 'define) t (L3 call-with-values-value (L3 (q 'lambda) rf-nil (rf-caddr x))
                                   (L3 (q 'lambda) (rf-cadr x) (rf-cons (primitive-named 'list) (rf-list (map rf-sym names))))))
              (letrec ((loop (subr rf-st (symbols int) rf-vals)
                         (lambda (names i)
                           (if (null? names) nil
                               (cons (L3 (q 'define) (rf-sym (car names)) (L3 (primitive-named 'list-ref) t (rf-int i)))
                                     (loop (cdr names) (+ i 1)))))))
                (loop names 0)))))))

"Parameters: a parameter is a primitive of no arguments that reads a cell
of its own. parameterize stores into the cell (logged, not watched), and
puts the old value back after the body, or when its path ends."
(define-type parameter (productof (prim rf-value) (cell rf-slots) (converter rf-value)))
(define parameters (ref (listof parameter acyclic) @rf) (new nil))
(define parameter-of (subr rf-st (rf-value) (sumof (none unit) (some parameter)))
  (lambda (p)
    (letrec ((find (subr rf-st ((listof parameter acyclic)) (sumof (none unit) (some parameter)))
               (lambda (l) (cond ((null? l) (sum none #u))
                                 ((rf-eqv? (extract (car l) prim) p) (sum some (car l)))
                                 (else (find (cdr l)))))))
      (find (get parameters)))))

(define install-control-forms! (subr rf-st () unit)
  (lambda ()
    (begin
      ;; (guard (var clause …) body …): the clauses as cond's, with var bound
      ;; to what the body raised; if none applies, it is raised again.
      (define-special! 'guard
        (lambda ((x rf-value) (cenv rf-cenv) (hint rf-value))
          (begin
            (if (and (rf-list? x) (rf-pair? (rf-cdr x)) (rf-list? (rf-cadr x)) (rf-pair? (rf-cadr x)) (rf-symbol? (rf-car (rf-cadr x)))) #u
                (syntax-error "bad guard" (strip x)))
            (let* ((var (rf-car (rf-cadr x)))
                   (body (compile-let nil (rf-elements (rf-cddr x)) cenv no-tail))
                   (handler (compile (L3 (q 'lambda) (L1 var) (rf-cons (q 'cond) (rf-append2 (rf-cdr (rf-cadr x)) (L1 (L2 (q 'else) (L2 reraise var))))))
                                     cenv hint no-tail)))
              (lambda ((env rf-slots) (ctx rf-ctx))
                (let ((h (handler env ctx)))
                  (catching ctx (lambda ((ctx rf-ctx)) (body env ctx)) (lambda ((ctx rf-ctx) (v rf-value)) (apply-value ctx h (list v) x)) (sum none #u))))))))
      (define-special! 'let-values
        (lambda ((x rf-value) (cenv rf-cenv) (hint rf-value))
          (let ((tail (get form-tail)))
            (begin
              (if (and (rf-list? x) (<= 3 (rf-length x)) (rf-list? (rf-cadr x))
                       (letrec ((ok (subr rf-st (rf-value) bool) (lambda (bs) (or (rf-null? bs) (and (rf-list? (rf-car bs)) (= (rf-length (rf-car bs)) 2) (ok (rf-cdr bs)))))))
                         (ok (rf-cadr x))))
                  #u (syntax-error "bad let-values" (strip x)))
              (let* ((fs (map (lambda ((b rf-value)) (parse-formals (rf-car b))) (rf-elements (rf-cadr x))))
                     (inits (map (lambda ((b rf-value)) (compile0 (rf-cadr b) cenv)) (rf-elements (rf-cadr x))))
                     (sb (compile-body (rf-elements (rf-cddr x)) cenv (apply-append-symbols (map formals-names fs)) tail))
                     (size (extract sb size)) (proc (extract sb proc)))
                (lambda ((env rf-slots) (ctx rf-ctx))
                  (letrec ((next (subr rf-eff ((listof rf-proc acyclic) (listof formals acyclic) rf-vals rf-ctx) rf-value)
                             (lambda (inits fs acc ctx)
                               (if (null? inits)
                                   (let ((frame (new-frame size env)))
                                     (letrec ((fill (subr rf-eff (int rf-vals) unit)
                                                (lambda (i vs) (if (null? vs) #u (begin (array-set! frame i (car vs)) (fill (+ i 1) (cdr vs)))))))
                                       (begin (fill 1 (vals-reverse acc)) (proc frame ctx))))
                                   (spread ctx ((car inits) env ctx)
                                           (lambda ((ctx rf-ctx) (vs rf-vals))
                                             (next (cdr inits) (cdr fs) (vals-append (vals-reverse (bind-values ctx (car fs) vs x)) acc) ctx)))))))
                    (next inits fs nil ctx))))))))
      (define-rewrite! 'case-lambda
        (lambda ((x rf-value))
          (begin
            (if (and (rf-list? x) (letrec ((ok (subr rf-st (rf-value) bool)
                                              (lambda (cs) (or (rf-null? cs) (and (rf-pair? (rf-car cs)) (rf-list? (rf-cdar cs)) (rf-pair? (rf-cdar cs)) (ok (rf-cdr cs)))))))
                                     (ok (rf-cdr x))))
                #u (syntax-error "bad case-lambda" (strip x)))
            (let ((args (rf-sym (string->symbol " case-lambda args")))
                  (n (rf-sym (string->symbol " case-lambda n"))))
              (L3 (q 'lambda) args
                  (L3 (q 'let) (L1 (L2 n (L2 (primitive-named 'length) args)))
                      (rf-cons (q 'cond)
                               (rf-append2
                                (rf-list (map (lambda ((c rf-value))
                                                (let ((f (parse-formals (rf-car c))))
                                                  (L2 (L3 (if (has-rest? f) (primitive-named '>=) (primitive-named '=)) n (rf-int (list-length (extract f req))))
                                                      (L3 apply-value* (rf-cons (q 'lambda) c) args))))
                                              (rf-elements (rf-cdr x))))
                                (L1 (L2 (q 'else) (L2 no-clause args)))))))))))
      (define-rewrite! 'let*-values
        (lambda ((x rf-value))
          (begin
            (if (and (rf-list? x) (<= 3 (rf-length x)) (rf-list? (rf-cadr x))) #u (syntax-error "bad let*-values" (strip x)))
            (if (or (rf-null? (rf-cadr x)) (rf-null? (rf-cdr (rf-cadr x))))
                (rf-cons (q 'let-values) (rf-cdr x))
                (L3 (q 'let-values) (L1 (rf-car (rf-cadr x))) (rf-cons (q 'let*-values) (rf-cons (rf-cdr (rf-cadr x)) (rf-cddr x))))))))
      ;; SRFI 8's (receive formals expression body …).
      (define-rewrite! 'receive
        (lambda ((x rf-value))
          (begin
            (if (and (rf-list? x) (<= 4 (rf-length x))) #u (syntax-error "bad receive" (strip x)))
            (rf-cons (q 'let-values) (rf-cons (L1 (L2 (rf-cadr x) (rf-caddr x))) (rf-cdddr x))))))
      (define-special! 'parameterize
        (lambda ((x rf-value) (cenv rf-cenv) (hint rf-value))
          (begin
            (if (and (rf-list? x) (<= 3 (rf-length x)) (rf-list? (rf-cadr x))
                     (letrec ((ok (subr rf-st (rf-value) bool) (lambda (bs) (or (rf-null? bs) (and (rf-list? (rf-car bs)) (= (rf-length (rf-car bs)) 2) (ok (rf-cdr bs)))))))
                       (ok (rf-cadr x))))
                #u (syntax-error "bad parameterize" (strip x)))
            ;; shakedown's (let ((ps …) (vs …) (body …)) …): body, vs, ps.
            (let* ((body (compile-let nil (rf-elements (rf-cddr x)) cenv no-tail))
                   (vs (map (lambda ((b rf-value)) (compile0 (rf-cadr b) cenv)) (rf-elements (rf-cadr x))))
                   (ps (map (lambda ((b rf-value)) (compile0 (rf-car b) cenv)) (rf-elements (rf-cadr x)))))
              (lambda ((env rf-slots) (ctx rf-ctx))
                (let* ((pvs (map2 (lambda ((p rf-proc) (v rf-proc)) (let* ((pv (p env ctx)) (vv (v env ctx))) (L2 pv vv))) ps vs))
                       (entries (map (lambda ((pv rf-value))
                                       (tagcase (parameter-of (rf-car pv))
                                         (some e e)
                                         (none u (begin (fail! ctx 'error (describe-call x "not a parameter")) (product (prim rf-false) (cell no-slots) (converter rf-false))))))
                                     pvs))
                       (news (map2 (lambda ((pv rf-value) (e parameter))
                                     (if (rf-false? (extract e converter)) (rf-cadr pv) (apply-value ctx (extract e converter) (list (rf-cadr pv)) x)))
                                   pvs entries))
                       (olds (map (lambda ((e parameter)) (array-ref (extract e cell) 0)) entries))
                       (restore! (lambda () (for-each2 (lambda ((e parameter) (old rf-value)) (store! (extract e cell) 0 old)) entries olds))))
                  (begin
                    (for-each2 (lambda ((e parameter) (new rf-value)) (store! (extract e cell) 0 new)) entries news)
                    (let ((r (rf-protect
                              (lambda ()
                                (letrec ((wind (subr rf-eff ((listof parameter acyclic) rf-vals) rf-value)
                                           (lambda (es olds)
                                             (if (null? es) (body env ctx)
                                                 (rewinding (extract (car es) cell) 0 (car olds) (lambda () (wind (cdr es) (cdr olds))))))))
                                  (wind entries olds)))
                              restore!)))
                      (begin (restore!) r))))))))))))
(define apply-append-symbols-eval (subr rf-st ((listof symbols acyclic)) symbols)
  (lambda (ls) (if (null? ls) nil (append (car ls) (apply-append-symbols-eval (cdr ls))))))

(define install-control-globals! (subr rf-st () unit)
  (lambda ()
    (begin
      ;; (call/cc f), escape-only.
      (let ((call/cc-value
             (make-primitive 'call/cc
                             (lambda ((ctx rf-ctx) (args rf-vals) (src rf-value))
                               (begin
                                 (if (= (list-length args) 1) #u (fail! ctx 'error (describe-call src "wrong number of arguments")))
                                 (let* ((tag (the (ref unit @rf) (new #u)))
                                        (k (make-primitive 'continuation
                                                           (lambda ((ctx rf-ctx) (vs rf-vals) (src rf-value))
                                                             (escape! ctx tag (if (and (pair? vs) (null? (cdr vs))) (car vs) (sum multiple vs)))))))
                                   (catching ctx (lambda ((ctx rf-ctx)) (apply-value ctx (car args) (list k) src))
                                             (lambda ((ctx rf-ctx) (v rf-value)) v) (sum some tag))))))))
        (begin (define-global! 'call/cc call/cc-value)
               (define-global! 'call-with-current-continuation call/cc-value)))
      (define-global! 'with-exception-handler
        (make-primitive 'with-exception-handler
                        (lambda ((ctx rf-ctx) (args rf-vals) (src rf-value))
                          (begin
                            (if (= (list-length args) 2) #u (fail! ctx 'error (describe-call src "wrong number of arguments")))
                            (with-handler (car args) (lambda () (apply-value ctx (car (cdr args)) nil src)))))))
      (define-global! 'call-with-values call-with-values-value)
      (define-global! 'make-parameter
        (make-primitive 'make-parameter
                        (lambda ((ctx rf-ctx) (args rf-vals) (src rf-value))
                          (begin
                            (if (and (<= 1 (list-length args)) (<= (list-length args) 2)) #u (fail! ctx 'error (describe-call src "wrong number of arguments")))
                            (let* ((converter (if (pair? (cdr args)) (car (cdr args)) rf-false))
                                   (cell (new-cell (if (rf-false? converter) (car args) (apply-value ctx converter (list (car args)) src))))
                                   ;; Called with a value, as Larceny lets it be, it takes the value.
                                   (p (make-primitive 'parameter
                                                      (lambda ((ctx rf-ctx) (args rf-vals) (src rf-value))
                                                        (cond ((null? args) (array-ref cell 0))
                                                              ((null? (cdr args))
                                                               (begin (store! cell 0 (if (rf-false? converter) (car args) (apply-value ctx converter args src)))
                                                                      rf-unspecified))
                                                              (else (begin (fail! ctx 'error (describe-call src "wrong number of arguments")) rf-unspecified)))))))
                              (begin (set parameters (cons (product (prim p) (cell cell) (converter converter)) (get parameters)))
                                     p)))))))))

;;; ------------------------------------------------------------ loops with invariants

(define loop-clause-names symbols (list 'invariant 'decreases 'modifies 'shape))
"The clauses a named let's body starts with, and the body after them."
(define-type loop-split (productof (clauses rf-vals) (body rf-vals)))
(define loop-clauses (subr rf-eff (rf-value) loop-split)
  (lambda (body)
    (letrec ((loop (subr rf-eff (rf-value rf-vals) loop-split)
               (lambda (forms clauses)
                 (if (and (rf-pair? forms) (rf-pair? (rf-car forms)) (rf-symbol? (rf-caar forms))
                          (symbols-member? (strip-name (rf-sym-of (rf-caar forms))) loop-clause-names))
                     (loop (rf-cdr forms) (cons (rf-car forms) clauses))
                     (product (clauses (vals-reverse clauses)) (body (rf-elements forms)))))))
      (loop body nil))))

"A modifies clause: its label, its target (a global's cell, a closure of
the formals, or code of a frame), its shape (or #f), its description, and
the part of the target it names."
(define-type mod-target (sumof (cell rf-slots) (closure rf-value) (code rf-proc)))
(define-type mod-part (sumof (none unit) (field symbol) (slot mod-target)))
(define-type modifies-clause (productof (label string) (target mod-target) (shape rf-value) (description string) (part mod-part)))
(define-type shape-of (productof (var symbol) (shape rf-value)))

(define compile-loop (subr rf-eff (rf-value rf-cenv) rf-proc)
  (lambda (x cenv)
    (let* ((name (rf-cadr x))
           (bindings (map (lambda ((b rf-value)) (L2 (rf-car b) (binding-init b))) (rf-elements (rf-caddr x))))
           (vars (map (lambda ((b rf-value)) (rf-sym-of (rf-car b))) bindings))
           (n (list-length vars))
           (split (loop-clauses (rf-cdddr x)))
           (clauses (extract split clauses))
           (of (lambda ((what symbol)) (filter (lambda ((c rf-value)) (eq? (strip-name (rf-sym-of (rf-car c))) what)) clauses)))
           (lname (symbol->string (strip-name (rf-sym-of name))))
           (lp (the rf-loop (product (name lname) (arity n) (invariants (new nil)) (decreases (new (sum none #u))) (state (new (sum none #u))))))
           (outer (the rf-vframe (product (vars (new (list (rf-sym-of name)))) (loops (new nil)))))
           (cenv-loop (the rf-cenv (cons (sum vframe outer) cenv)))
           (cenv-vars (the rf-cenv (cons (sum vframe (product (vars (new vars)) (loops (new nil)))) cenv-loop)))
           (expr (lambda ((e rf-value)) (compile0 e cenv-vars)))
           (inits (map (lambda ((b rf-value)) (compile (rf-cadr b) cenv (rf-car b) no-tail)) bindings)))
      (begin
        (if (null? (of 'invariant))
            (syntax-error "a loop with (decreases ...), (modifies ...) or (shape ...) needs (invariant ...)" (strip x)) #u)
        (set (extract outer loops) (list (product (index 1) (loop lp))))
        (set (extract lp invariants)
             (map (lambda ((e rf-value)) (product (expr e) (code (expr e))))
                  (apply-append-vals (map (lambda ((c rf-value)) (rf-elements (rf-cdr c))) (of 'invariant)))))
        (let ((d (of 'decreases)))
          (if (pair? d)
              (begin
                (if (and (null? (cdr d)) (= (rf-length (car d)) 2)) #u
                    (syntax-error "bad decreases (expected one (decreases e))" (strip (car d))))
                (set (extract lp decreases) (sum some (product (expr (rf-cadr (car d))) (code (expr (rf-cadr (car d))))))))
              #u))
        ;; shakedown's (let ((shapes …) (modifies …)) …): modifies first.
        (let* ((modifies (map (lambda ((c rf-value))
                                (begin
                                  (if (and (<= 2 (rf-length c)) (<= (rf-length c) 3) (or (rf-null? (rf-cddr c)) (shape? (strip (rf-caddr c))))) #u
                                      (syntax-error "bad modifies (expected (modifies e [shape]))" (strip c)))
                                  (let* ((e (rf-cadr c))
                                         (part (modifies-part e (lambda ((i rf-value)) (sum code (expr i))))))
                                    (product (label (string-append "(modifies " (datum->string e) ") of " lname))
                                             (target (cond ((and (rf-pair? e) (keyword? (rf-car e) 'global)) (the mod-target (sum cell (global-cell (strip-name (rf-sym-of (rf-cadr e)))))))
                                                           ((tagcase part (none u #f) (else y #t)) (the mod-target (sum code (expr (rf-cadr e)))))
                                                           (else (the mod-target (sum code (expr e))))))
                                             (shape (if (rf-pair? (rf-cddr c)) (strip (rf-caddr c)) rf-false))
                                             (description (datum->string e))
                                             (part part)))))
                              (of 'modifies)))
               (shapes (map (lambda ((c rf-value))
                              (begin
                                (if (and (= (rf-length c) 3) (memq-val? (rf-cadr c) (map rf-sym vars)) (shape? (strip (rf-caddr c)))) #u
                                    (syntax-error "bad shape (expected (shape variable shape))" (strip c)))
                                (product (var (rf-sym-of (rf-cadr c))) (shape (strip (rf-caddr c))))))
                            (of 'shape)))
               (sb (compile-body (extract split body) cenv-loop vars (sum some lp))))
          (lambda ((env rf-slots) (ctx rf-ctx))
            (let* ((frame (note-allocation! (let ((f (the rf-slots (make-array 2 rf-unassigned)))) (begin (array-set! f 0 (sum frame env)) f))))
                   (vals (map (lambda ((i rf-proc)) (i env ctx)) inits)))
              (run-loop ctx lp frame vars vals shapes modifies (extract sb size) (extract sb proc)))))))))

(define shape-assq (subr rf-st (symbol (listof shape-of acyclic)) rf-value)
  (lambda (v l) (cond ((null? l) rf-false) ((eq? (extract (car l) var) v) (extract (car l) shape)) (else (shape-assq v (cdr l))))))

(define run-loop (subr rf-eff (rf-ctx rf-loop rf-slots symbols rf-vals (listof shape-of acyclic) (listof modifies-clause acyclic) int rf-proc) rf-value)
  (lambda (ctx lp frame vars vals shapes modifies size body)
    (let* ((name (extract lp name))
           (vars-frame (lambda ((vs rf-vals)) (the rf-slots (list->array (the rf-vals (cons (the rf-value (sum frame frame)) vs)))))))
      (begin
        (set abstraction "the proof uses a loop invariant")
        (for-each (lambda ((inv rf-expr-code))
                    (check! ctx 'loop (string-append "invariant of " name " on entry: " (datum->string (extract inv expr)))
                            (truth ((extract inv code) (vars-frame vals) ctx))))
                  (get (extract lp invariants)))
        (let* ((targets (footprints ctx modifies (lambda ((t mod-target)) (tagcase t (code c (c (vars-frame vals) ctx)) (cell c rf-false) (closure c rf-false)))))
               (head (map2 (lambda ((var symbol) (v rf-value))
                             (let ((shape (let ((s (shape-assq var shapes)))
                                            (cond ((not (rf-false? s)) s)
                                                  ((int-like? v) (q 'integer))
                                                  ((bool-like? v) (q 'boolean))
                                                  (else (begin (fail! ctx 'unsupported (string-append name ": give (shape " (datum->string (rf-sym var)) " shape) for its variable"))
                                                               rf-false))))))
                               (generate ctx shape (string-append (datum->string (rf-sym var)) " in " name))))
                           vars vals)))
          (begin
            (havoc! ctx targets (string-append " in " name) " has no shape, so the loop cannot be checked")
            (for-each (lambda ((inv rf-expr-code)) (assume! ctx (truth ((extract inv code) (vars-frame head) ctx))))
                      (get (extract lp invariants)))
            (let* ((m (tagcase (get (extract lp decreases))
                        (none u rf-false)
                        (some d (let* ((label (string-append "(decreases " (datum->string (extract d expr)) ") of " name))
                                       (m (measure ctx label ((extract d code) (vars-frame head) ctx))))
                                  (begin (check! ctx 'loop (string-append label " is not negative") (t-<= (rf-int 0) m))
                                         m)))))
                   (outer (get (extract lp state))))
              (begin
                (set (extract lp state) (sum some (product (measure m) (frame frame))))
                (let ((r (rf-protect
                          (lambda ()
                            (watching-writes 'loop
                                             (string-append name (if (null? targets) " writes to something it did not allocate"
                                                                     " writes to something it did not allocate or name in (modifies ...)"))
                                             (targets-allowed targets)
                                             (lambda ()
                                               (let ((f (note-allocation! (the rf-slots (make-array (+ size 1) rf-unassigned)))))
                                                 (begin
                                                   (array-set! f 0 (sum frame frame))
                                                   (letrec ((fill (subr rf-st (int rf-vals) unit) (lambda (i vs) (if (null? vs) #u (begin (array-set! f i (car vs)) (fill (+ i 1) (cdr vs)))))))
                                                     (fill 1 head))
                                                   (body f ctx))))))
                          (lambda () (set (extract lp state) outer)))))
                  (begin (set (extract lp state) outer) r))))))))))

"(loop e …) in tail position of the loop's body: check the invariant and the
measure, and end the path, which the head covers."
(define compile-back-edge (subr rf-eff (rf-value rf-cenv rf-loop) rf-proc)
  (lambda (x cenv lp)
    (let ((args (map (lambda ((a rf-value)) (compile0 a cenv)) (rf-elements (rf-cdr x)))))
      (lambda ((env rf-slots) (ctx rf-ctx))
        (let* ((vals (map (lambda ((a rf-proc)) (a env ctx)) args))
               (state (tagcase (get (extract lp state)) (some s s) (none u (product (measure rf-false) (frame no-slots)))))
               (frame (the rf-slots (list->array (the rf-vals (cons (the rf-value (sum frame (extract state frame))) vals)))))
               (name (extract lp name)))
          (begin
            (if (= (list-length vals) (extract lp arity)) #u (fail! ctx 'error (describe-call x "wrong number of arguments")))
            (for-each (lambda ((inv rf-expr-code))
                        (check! ctx 'loop (string-append "invariant of " name " at " (datum->string x) ": " (datum->string (extract inv expr)))
                                (truth ((extract inv code) frame ctx))))
                      (get (extract lp invariants)))
            (tagcase (get (extract lp decreases))
              (some d (let ((label (string-append "(decreases " (datum->string (extract d expr)) ") of " name)))
                        (check! ctx 'loop (string-append label " at " (datum->string x))
                                (t-< (measure ctx label ((extract d code) frame ctx)) (extract state measure)))))
              (none u #u))
            (assume! ctx rf-false)
            rf-unspecified))))))

;;; ------------------------------------------------------------ checks and symbolic values

(define check-label (subr rf-eff (rf-value) string)
  (lambda (x) (if (and (rf-pair? (rf-cddr x)) (rf-string? (rf-caddr x))) (rf-str-of (rf-caddr x)) (datum->string x))))

"One of the values: a fresh index picks it."
(define choose (subr rf-eff (rf-ctx rf-vals string) rf-value)
  (lambda (ctx values description)
    (let ((k (fresh-index! ctx (list-length values) (string-append "index of " description))))
      (choice ctx k values))))
"The element of values that index k picks: merged, or, in a proof that
splits, a join."
(define choice (subr rf-eff (rf-ctx rf-value rf-vals) rf-value)
  (lambda (ctx k values)
    (if (splitting-now?)
        (join ctx (letrec ((loop (subr rf-eff (int rf-vals) arms)
                             (lambda (j vs) (if (null? vs) nil
                                                (let ((v (car vs)))
                                                  (let ((g (t-= k (rf-int j)))) (cons (make-arm g (lambda ((ctx rf-ctx)) v)) (loop (+ j 1) (cdr vs)))))))))
                    (loop 0 values))
              #f)
        (letrec ((loop (subr rf-eff (int rf-value) rf-value)
                   (lambda (j acc) (if (< j 0) acc (loop (- j 1) (let ((g (t-= k (rf-int j)))) (merge g (vals-ref values j) acc)))))))
          (loop (- (list-length values) 2) (vals-ref values (- (list-length values) 1)))))))
"A list of the first len of elements, for a fresh len."
(define bounded-list (subr rf-eff (rf-ctx rf-vals string) rf-value)
  (lambda (ctx elements description)
    (let* ((n (list-length elements))
           (len (fresh-index! ctx (+ n 1) (string-append "length of " description))))
      (choice ctx len (letrec ((loop (subr rf-st (int rf-vals) rf-vals) (lambda (i acc) (if (< i 0) acc (loop (- i 1) (cons (rf-list (vals-head elements i)) acc))))))
                        (loop n nil))))))

"Shapes: integer, boolean, error, (one-of datum …), (list-of n shape),
(pair shape shape), (or shape …)."
(define shape? (subr rf-st (rf-value) bool)
  (lambda (s)
    (cond ((memq-val? s (list (q 'integer) (q 'boolean) (q 'error))) #t)
          ((and (rf-pair? s) (rf-list? s))
           (let ((h (rf-car s)))
             (cond ((rf-eqv? h (q 'one-of)) (rf-pair? (rf-cdr s)))
                   ((rf-eqv? h (q 'list-of)) (and (= (rf-length s) 3) (rf-exact-integer? (rf-cadr s)) (>= (rf-int-of (rf-cadr s)) 0) (shape? (rf-caddr s))))
                   ((rf-eqv? h (q 'pair)) (and (= (rf-length s) 3) (shape? (rf-cadr s)) (shape? (rf-caddr s))))
                   ((rf-eqv? h (q 'or)) (and (rf-pair? (rf-cdr s)) (all-shapes? (rf-cdr s))))
                   (else #f))))
          (else #f))))
(define all-shapes? (subr rf-st (rf-value) bool)
  (lambda (l) (or (rf-null? l) (and (shape? (rf-car l)) (all-shapes? (rf-cdr l))))))

"A symbolic value of a shape; parts in order, left to right, as playback
makes them."
(define generate (subr rf-eff (rf-ctx rf-value string) rf-value)
  (lambda (ctx shape description)
    (letrec ((in-order (subr rf-eff (rf-vals string) rf-vals)
               (lambda (shapes name)
                 (letrec ((loop (subr rf-eff (rf-vals int) rf-vals)
                            (lambda (shapes i)
                              (if (null? shapes) nil
                                  (let ((v (generate ctx (car shapes)
                                                     (if (string=? name "") description
                                                         (string-append name " " (int->string i) " of " description)))))
                                    (cons v (loop (cdr shapes) (+ i 1))))))))
                   (loop shapes 0)))))
      (cond ((rf-eqv? shape (q 'integer)) (fresh-constant! ctx sort-int description))
            ((rf-eqv? shape (q 'boolean)) (fresh-constant! ctx sort-bool description))
            ((rf-eqv? shape (q 'error)) (make-error-value (rf-str description) rf-nil (rf-str description)))
            (else
             (let ((h (rf-car shape)))
               (cond ((rf-eqv? h (q 'one-of)) (choose ctx (rf-elements (rf-cdr shape)) description))
                     ((rf-eqv? h (q 'list-of))
                      (bounded-list ctx (in-order (letrec ((mk (subr rf-st (int) rf-vals) (lambda (i) (if (<= i 0) nil (cons (rf-caddr shape) (mk (- i 1)))))))
                                                    (mk (rf-int-of (rf-cadr shape))))
                                                  "element")
                                    description))
                     ((rf-eqv? h (q 'pair)) (let ((parts (in-order (rf-elements (rf-cdr shape)) "part"))) (rf-cons (car parts) (car (cdr parts)))))
                     (else (choose ctx (in-order (rf-elements (rf-cdr shape)) "") description)))))))))

(define fits (subr rf-eff (rf-value rf-value) rf-value)
  (lambda (shape v)
    (cond ((rf-union? v) (t-or* (map (lambda ((m rf-member)) (let ((x (fits shape (extract m v)))) (t-and (extract m g) x))) (union-members v))))
          ((rf-eqv? shape (q 'integer)) (rf-bool (int-like? v)))
          ((rf-eqv? shape (q 'boolean)) (rf-bool (bool-like? v)))
          ((rf-eqv? shape (q 'error)) (rf-bool (error-value? v)))
          (else
           (let ((h (rf-car shape)))
             (cond ((rf-eqv? h (q 'one-of)) (t-or* (map (lambda ((d rf-value)) (equal-value v d)) (rf-elements (rf-cdr shape)))))
                   ((rf-eqv? h (q 'list-of))
                    (letrec ((loop (subr rf-eff (rf-value int) rf-value)
                               (lambda (v k)
                                 (cond ((rf-union? v) (t-or* (map (lambda ((m rf-member)) (let ((x (loop (extract m v) k))) (t-and (extract m g) x))) (union-members v))))
                                       ((rf-null? v) rf-true)
                                       ((rf-pair? v) (if (< k (rf-int-of (rf-cadr shape)))
                                                         (let* ((a (fits (rf-caddr shape) (rf-car v))) (d (loop (rf-cdr v) (+ k 1)))) (t-and a d))
                                                         rf-false))
                                       (else rf-false)))))
                      (loop v 0)))
                   ((rf-eqv? h (q 'pair)) (if (rf-pair? v) (let* ((a (fits (rf-cadr shape) (rf-car v))) (d (fits (rf-caddr shape) (rf-cdr v)))) (t-and a d)) rf-false))
                   (else (t-or* (map (lambda ((s rf-value)) (fits s v)) (rf-elements (rf-cdr shape)))))))))))

(define define-any! (subr rf-st (symbol int) unit)
  (lambda (name sort)
    (begin
      (define-special! name
        (lambda ((x rf-value) (cenv rf-cenv) (hint rf-value))
          (let ((description (if (rf-false? hint) (datum->string x) (string-append (datum->string hint) " = " (datum->string x)))))
            (lambda ((env rf-slots) (ctx rf-ctx)) (fresh-constant! ctx sort description)))))
      (define-global! name (make-primitive name (lambda ((ctx rf-ctx) (args rf-vals) (src rf-value)) (fresh-constant! ctx sort (datum->string src))))))))

(define install-check-forms! (subr rf-st () unit)
  (lambda ()
    (begin
      (define-special! 'assert
        (lambda ((x rf-value) (cenv rf-cenv) (hint rf-value))
          (let* ((label (check-label x)) (test (compile0 (rf-cadr x) cenv)))
            (lambda ((env rf-slots) (ctx rf-ctx))
              (let ((ok (truth (test env ctx))))
                (begin (at-source! x) (check! ctx 'assert label ok) rf-unspecified))))))
      (define-special! 'assume
        (lambda ((x rf-value) (cenv rf-cenv) (hint rf-value))
          (let ((test (compile0 (rf-cadr x) cenv)))
            (lambda ((env rf-slots) (ctx rf-ctx))
              (let ((ok (truth (test env ctx))))
                (begin (at-source! x) (assume! ctx ok) rf-unspecified))))))
      (define-special! 'cover
        (lambda ((x rf-value) (cenv rf-cenv) (hint rf-value))
          (let* ((label (check-label x)) (test (compile0 (rf-cadr x) cenv)))
            (lambda ((env rf-slots) (ctx rf-ctx))
              (let ((ok (truth (test env ctx))))
                (begin (at-source! x) (cover! ctx label ok) rf-unspecified))))))
      (define-any! 'any-integer sort-int)
      (define-any! 'any-boolean sort-bool)
      (define-global! 'any-of
        (make-primitive 'any-of
                        (lambda ((ctx rf-ctx) (args rf-vals) (src rf-value))
                          (if (null? args) (begin (fail! ctx 'error (describe-call src "no values to choose from")) rf-unspecified)
                              (choose ctx args (datum->string src))))))
      (define-global! 'any-list
        (make-primitive 'any-list
                        (lambda ((ctx rf-ctx) (args rf-vals) (src rf-value))
                          (begin
                            (if (and (= (list-length args) 2) (rf-exact-integer? (car args))) #u
                                (fail! ctx 'error (describe-call src "expected a concrete length and a procedure")))
                            (let ((n (rf-int-of (car args))) (make (car (cdr args))))
                              (bounded-list ctx
                                            (letrec ((loop (subr rf-eff (int) rf-vals)
                                                       (lambda (i) (if (= i n) nil (let ((x (apply-value ctx make nil src))) (cons x (loop (+ i 1))))))))
                                              (loop 0))
                                            (datum->string src)))))))
      (define-global! 'arbitrary
        (make-primitive 'arbitrary
                        (lambda ((ctx rf-ctx) (args rf-vals) (src rf-value))
                          (begin
                            (if (and (= (list-length args) 1) (shape? (car args))) #u (fail! ctx 'error (describe-call src "expected a shape")))
                            (generate ctx (car args) (datum->string src))))))
      (define-global! 'fits?
        (make-primitive 'fits?
                        (lambda ((ctx rf-ctx) (args rf-vals) (src rf-value))
                          (begin
                            (if (and (= (list-length args) 2) (shape? (car args))) #u (fail! ctx 'error (describe-call src "expected a shape and a value")))
                            (fits (car args) (car (cdr args)))))))
      (define-global! 'apply
        (make-primitive 'apply
                        (lambda ((ctx rf-ctx) (args rf-vals) (src rf-value))
                          (if (null? args) (begin (fail! ctx 'error (describe-call src "wrong number of arguments")) rf-unspecified)
                              (letrec ((loop (subr rf-eff (rf-vals rf-vals) rf-value)
                                         (lambda (rest before)
                                           (if (null? (cdr rest))
                                               (spine ctx src (car rest) (lambda ((ctx rf-ctx) (xs rf-vals)) (apply-value ctx (car args) (vals-append (vals-reverse before) xs) src)))
                                               (loop (cdr rest) (cons (car rest) before))))))
                                (loop (cdr args) nil)))))))))

;;; ------------------------------------------------------------ applying procedures

(define apply-value (subr rf-eff (rf-ctx rf-value rf-vals rf-value) rf-value)
  (lambda (ctx f args src)
    (tagcase f
      (closure c (if (splittable? args)
                     (split-args ctx args (lambda ((ctx rf-ctx) (args rf-vals)) (apply-closure ctx c args src)))
                     (apply-closure ctx c args src)))
      (prim p ((extract p proc) ctx args src))
      (union ms (join-union ctx f (lambda ((ctx rf-ctx) (f rf-value)) (apply-value ctx f args src))))
      (else x (begin (fail! ctx 'error (describe-call src "not a procedure")) rf-unspecified)))))

"A closure applied to unions runs once for each choice of their members
(if there are not too many)."
(define max-call-split int 32)
(define splittable? (subr rf-st (rf-vals) bool)
  (lambda (args)
    (letrec ((loop (subr rf-st (rf-vals int bool) bool)
               (lambda (args n any?)
                 (cond ((null? args) (and any? (<= n max-call-split)))
                       ((rf-union? (car args)) (loop (cdr args) (* n (list-length (union-members (car args)))) #t))
                       (else (loop (cdr args) n any?))))))
      (loop args 1 #f))))
(define split-args (subr rf-eff (rf-ctx rf-vals (subr rf-eff (rf-ctx rf-vals) rf-value)) rf-value)
  (lambda (ctx args k)
    (letrec ((loop (subr rf-eff (rf-vals rf-vals rf-ctx) rf-value)
               (lambda (before after ctx)
                 (cond ((null? after) (k ctx (vals-reverse before)))
                       ((rf-union? (car after)) (join-union ctx (car after) (lambda ((ctx rf-ctx) (v rf-value)) (loop (cons v before) (cdr after) ctx))))
                       (else (loop (cons (car after) before) (cdr after) ctx))))))
      (loop nil args ctx))))

(define apply-closure (subr rf-eff (rf-ctx rf-closure rf-vals rf-value) rf-value)
  (lambda (ctx f args src)
    (let* ((code (extract f code))
           (required (extract code required))
           (n (list-length args)))
      (begin
        (if (if (extract code rest) (>= n required) (= n required)) #u
            (fail! ctx 'error (describe-call src "wrong number of arguments")))
        (let ((frame (new-frame (extract code size) (extract f env))))
          (begin
            (letrec ((loop (subr rf-st (int rf-vals) unit)
                       (lambda (i args)
                         (cond ((<= i required) (begin (array-set! frame i (car args)) (loop (+ i 1) (cdr args))))
                               ((extract code rest) (array-set! frame i (rf-list args)))
                               (else #u)))))
              (loop 1 args))
            (count-call! ctx)
            ((extract code body) frame (unwind ctx f src))))))))

"The context for an activation of closure f: the unwinding alist maps
closures to (depth . count)."
(define unwind (subr rf-eff (rf-ctx rf-closure rf-value) rf-ctx)
  (lambda (ctx f src)
    (let* ((alist (ctx-unwind ctx))
           (entry (letrec ((find (subr rf-st (rf-unwinds) (sumof (none unit) (some rf-unwind)))
                             (lambda (l) (cond ((null? l) (sum none #u)) ((eq? (extract (car l) f) f) (sum some (car l))) (else (find (cdr l)))))))
                    (find alist)))
           (depth (ctx-depth ctx)))
      (tagcase entry
        (none u (make-ctx (ctx-pc ctx) depth (cons (product (f f) (depth depth) (count 0)) alist)))
        (some e
          (if (> depth (extract e depth))
              (let ((count (+ (extract e count) 1))
                    (bound (session-unwind-bound)))
                (begin
                  (if (> count bound)
                      (fail! ctx 'unwind (string-append "unwinding " (symbol->string (extract (extract f code) name))
                                                        " more than " (int->string bound) " times"))
                      #u)
                  (make-ctx (ctx-pc ctx) depth (cons (product (f f) (depth depth) (count count)) alist))))
              ctx))))))

(define reraise rf-value
  (make-primitive 'raise (lambda ((ctx rf-ctx) (args rf-vals) (src rf-value)) (raise! ctx (car args) #f rf-true))))

(define call-with-values-value rf-value
  (make-primitive 'call-with-values
                  (lambda ((ctx rf-ctx) (args rf-vals) (src rf-value))
                    (begin
                      (if (= (list-length args) 2) #u (fail! ctx 'error (describe-call src "wrong number of arguments")))
                      (spread ctx (apply-value ctx (car args) nil src)
                              (lambda ((ctx rf-ctx) (vs rf-vals)) (apply-value ctx (car (cdr args)) vs src)))))))

(define apply-value* rf-value
  (make-primitive 'apply (lambda ((ctx rf-ctx) (args rf-vals) (src rf-value)) (apply-value ctx (car args) (rf-elements (car (cdr args))) src))))
(define no-clause rf-value
  (make-primitive 'case-lambda (lambda ((ctx rf-ctx) (args rf-vals) (src rf-value))
                                 (begin (fail! ctx 'error (describe-call src "no clause of case-lambda takes this many arguments")) rf-unspecified))))


;;; ------------------------------------------------------------ libraries

(define-type export-binding (productof (name symbol) (cell (sumof (none unit) (some rf-slots))) (macro (sumof (none unit) (some rf-macro)))))
(define-type library
  (productof (name rf-value) (genv rf-genv) (exports (listof export-binding acyclic)) (form rf-value) (defined symbols)))
(define libraries (ref (listof library acyclic) @rf) (new nil))
"The library being loaded (#f: none)."
(define current-library (ref rf-value @rf) (new rf-false))

"For playback: the libraries loaded, in order: name, form, defined."
(define-type loaded-library (productof (name rf-value) (form rf-value) (defined symbols)))
(define loaded-libraries (subr rf-st () (listof loaded-library acyclic))
  (lambda () (map (lambda ((l library)) (product (name (extract l name)) (form (extract l form)) (defined (extract l defined))))
                  (the (listof library acyclic) (reverse (get libraries))))))

(define find-library (subr rf-st (rf-value) (sumof (none unit) (some library)))
  (lambda (name)
    (letrec ((loop (subr rf-st ((listof library acyclic)) (sumof (none unit) (some library)))
               (lambda (ls) (cond ((null? ls) (sum none #u)) ((equal-datum? (extract (car ls) name) name) (sum some (car ls))) (else (loop (cdr ls)))))))
      (loop (get libraries)))))
(define known-library? (subr rf-eff (rf-value) bool)
  (lambda (name) (or (builtin-library? name) (tagcase (find-library name) (some l #t) (none u #f)) (not (string=? (find-library-file name) "")))))

"Library name, loaded from its file if need be."
(define get-library (subr rf-eff (rf-value rf-ctx) library)
  (lambda (name ctx)
    (tagcase (find-library name)
      (some l l)
      (none u
        (let ((file (find-library-file name)))
          (begin
            (if (string=? file "") (syntax-error "library not found (see --library-path)" name) #u)
            (for-each (lambda ((form rf-value))
                        (if (and (rf-pair? form) (keyword? (rf-car form) 'define-library))
                            (define-library! form (directory-of file) ctx)
                            (syntax-error (string-append "expected define-library in " file) form)))
                      (read-forms file))
            (tagcase (find-library name)
              (some l l)
              (none u (begin (syntax-error (string-append file " does not define library") name)
                             (product (name name) (genv (get globals)) (exports nil) (form rf-nil) (defined nil)))))))))))

(define import! (subr rf-eff (rf-value rf-ctx) unit)
  (lambda (set ctx)
    (let ((name (import-set-library set syntax-error)))
      (if (builtin-library? name) #u
          (let* ((lib (get-library name ctx))
                 (exports (extract lib exports)))
            (for-each (lambda ((b binding-name))
                        (let ((binding (letrec ((find (subr rf-st ((listof export-binding acyclic)) export-binding)
                                                  (lambda (l) (if (eq? (extract (car l) name) (extract b name)) (car l) (find (cdr l))))))
                                         (find exports))))
                          (tagcase (extract binding cell)
                            (some c (begin (table-set! (extract (get globals) macros) (extract b local) (sum none #u))
                                           (table-set! (extract (get globals) cells) (extract b local) c)))
                            (none u (table-set! (extract (get globals) macros) (extract b local) (extract binding macro))))))
                      (import-set-names set (map (lambda ((e export-binding)) (extract e name)) exports) syntax-error)))))))

"(define-library name declaration …), with includes relative to dir."
(define define-library! (subr rf-eff (rf-value string rf-ctx) unit)
  (lambda (x dir ctx)
    (begin
      (if (and (rf-list? x) (rf-pair? (rf-cdr x)) (rf-list? (rf-cadr x))) #u (syntax-error "bad define-library" (strip x)))
      (let* ((name (strip (rf-cadr x)))
             (decls (expand-declarations (rf-elements (rf-cddr x)) dir known-library? syntax-error))
             (bodies (apply-append-vals (map (lambda ((d rf-value)) (if (keyword? (rf-car d) 'begin) (rf-elements (rf-cdr d)) nil)) decls)))
             (defined (defined-names bodies syntax-error))
             (genv (new-genv (sum some (get builtin-genv))))
             (outer-genv (get globals))
             (outer-library (get current-library)))
        (begin
          (tagcase (find-library name) (some l (syntax-error "library defined twice" name)) (none u #u))
          (set globals genv)
          (set current-library name)
          ;; Its own definitions shadow what it inherits, from the start.
          (for-each (lambda ((v symbol)) (begin (own-cell! v genv) #u)) (extract defined vars))
          (let ((exports (the (ref (listof export-binding acyclic) @rf) (new nil))))
            (begin
              (rf-protect
               (lambda ()
                 (begin
                   (for-each (lambda ((d rf-value))
                               (let ((h (strip-name (rf-sym-of (rf-car d)))))
                                 (cond ((eq? h 'import) (for-each (lambda ((set rf-value)) (import! set ctx)) (rf-elements (rf-cdr d))))
                                       ((eq? h 'begin) (load-program! (rf-elements (rf-cdr d)) ctx))
                                       (else #u))))
                             decls)
                   (set exports
                        (map (lambda ((e binding-name))
                               (tagcase (global-macro (extract e name) genv)
                                 (some m (the export-binding (product (name (extract e local)) (cell (sum none #u)) (macro (sum some m)))))
                                 (none u (the export-binding (product (name (extract e local)) (cell (sum some (global-cell-in (extract e name) genv))) (macro (sum none #u)))))))
                             (parse-exports (apply-append-vals (map (lambda ((d rf-value)) (if (keyword? (rf-car d) 'export) (rf-elements (rf-cdr d)) nil)) decls))
                                            syntax-error)))
                   rf-unspecified))
               (lambda () (begin (set globals outer-genv) (set current-library outer-library))))
              (set globals outer-genv)
              (set current-library outer-library)
              (set libraries (cons (product (name name) (genv genv) (exports (get exports))
                                            (form (rf-cons (q 'define-library) (rf-cons name (rf-list decls))))
                                            (defined (extract defined vars)))
                                   (get libraries))))))))))

;;; ------------------------------------------------------------ proofs

"(define-proof (name option …) body …), an option (unwind n), (split),
(stub f …) or (for-contract f)."
(define define-proof! (subr rf-eff (rf-value) unit)
  (lambda (x)
    (begin
      (if (and (rf-pair? (rf-cdr x)) (rf-pair? (rf-cadr x)) (rf-symbol? (rf-car (rf-cadr x))) (rf-pair? (rf-cddr x))) #u
          (syntax-error "bad define-proof" x))
      (let ((name (strip-name (rf-sym-of (rf-car (rf-cadr x)))))
            (unwind (the (ref int @rf) (new -1)))
            (split (the (ref bool @rf) (new #f)))
            (stubs (the (ref symbols @rf) (new nil)))
            (for-contract (the (ref (sumof (none unit) (some symbol)) @rf) (new (sum none #u)))))
        (begin
          (for-each (lambda ((option rf-value))
                      (cond ((and (head-is? option 'unwind) (rf-pair? (rf-cdr option)) (rf-exact-integer? (rf-cadr option)))
                             (set unwind (rf-int-of (rf-cadr option))))
                            ((and (head-is? option 'split) (rf-null? (rf-cdr option))) (set split #t))
                            ((and (head-is? option 'stub) (rf-list? option) (letrec ((all (subr rf-st (rf-value) bool) (lambda (l) (or (rf-null? l) (and (rf-symbol? (rf-car l)) (all (rf-cdr l)))))))
                                                                             (all (rf-cdr option))))
                             (set stubs (append (get stubs) (map rf-sym-of (rf-elements (rf-cdr option))))))
                            ((and (head-is? option 'for-contract) (rf-pair? (rf-cdr option)) (rf-symbol? (rf-cadr option)) (rf-null? (rf-cddr option)))
                             (set for-contract (sum some (rf-sym-of (rf-cadr option)))))
                            (else (syntax-error "bad define-proof option" option))))
                    (rf-elements (strip (rf-cdr (rf-cadr x)))))
          (let ((body ((compile (rf-cons (q 'lambda) (rf-cons rf-nil (rf-cddr x))) nil (rf-sym name) no-tail) no-slots (make-ctx rf-true 0 nil))))
            (set the-proofs (cons (product (name name) (unwind (get unwind)) (split (get split)) (stubs (get stubs)) (for-contract (get for-contract))
                                           (body body) (source x) (library (get current-library)))
                                  (get the-proofs)))))))))

;;; ------------------------------------------------------------ contracts

(define-type labelled (productof (label string) (closure rf-value)))
(define-type pin (productof (kind symbol) (object rf-value) (index rf-value) (value rf-value)))
(define-type contract
  (productof (name symbol) (requires (listof labelled acyclic)) (ensures (listof labelled acyclic)) (olds rf-vals)
             (modifies (listof modifies-clause acyclic)) (shape rf-value) (decreases (sumof (none unit) (some labelled)))
             (raises rf-value) (signals (listof labelled acyclic)) (body rf-value) (pins (listof pin acyclic))))
(define contracts (ref (listof contract acyclic) @rf) (new nil))
(define contract-defined? (subr rf-st (symbol) bool)
  (lambda (name) (letrec ((f (subr rf-st ((listof contract acyclic)) bool) (lambda (l) (and (pair? l) (or (eq? (extract (car l) name) name) (f (cdr l)))))))
                   (f (get contracts)))))
"The measure of the call of mode-for-contract being checked, or #f."
(define contract-measure (ref rf-value @rf) (new rf-false))
(define measure (subr rf-eff (rf-ctx string rf-value) rf-value)
  (lambda (ctx label v) (if (int-like? v) v (begin (fail! ctx 'error (string-append label ": not an integer")) v))))

"The proof being checked, for how calls of contracts work."
(define mode-stubs (ref symbols @rf) (new nil))
(define mode-for-contract (ref (sumof (none unit) (some symbol)) @rf) (new (sum none #u)))
(define contract-calls (ref int @rf) (new 0))
(define begin-proof-mode! (subr rf-st ((sumof (none unit) (some proof))) unit)
  (lambda (p)
    (begin
      (set mode-stubs (tagcase p (some pr (extract pr stubs)) (none u nil)))
      (set mode-for-contract (tagcase p (some pr (extract pr for-contract)) (none u (sum none #u))))
      (set abstraction "")
      (set contract-measure rf-false)
      (set contract-calls 0))))
(define proof-abstraction (subr rf-st () string) (lambda () (get abstraction)))
(define proof-contract-calls (subr rf-st () int) (lambda () (get contract-calls)))
(define for-contract-is? (subr rf-st (symbol) bool)
  (lambda (name) (tagcase (get mode-for-contract) (some n (eq? n name)) (none u #f))))

"Record accessors by their record type and field index, for pins."
(define-type accessor-field (productof (prim rf-value) (rtd rf-rtd) (index int)))
(define accessor-fields (ref (listof accessor-field acyclic) @rf) (new nil))

(define list-head-vals (subr rf-st (rf-vals int) rf-vals) (lambda (l k) (vals-head l k)))

"(define/contract (f . formals) clause … body …), or with existing the
closure f already is, (contract (f . formals) clause …) in contracts-for."
(define define-contract! (subr rf-eff (rf-value rf-ctx rf-value) unit)
  (lambda (x ctx existing)
    (begin
      (if (and (rf-list? x) (rf-pair? (rf-cdr x)) (rf-pair? (rf-cadr x)) (rf-symbol? (rf-car (rf-cadr x)))) #u
          (syntax-error (if (rf-false? existing) "bad define/contract" "bad contract") x))
      (let* ((name (strip-name (rf-sym-of (rf-car (rf-cadr x)))))
             (formals (rf-cdr (rf-cadr x)))
             (closure (lambda ((formals rf-value) (e rf-value))
                        ((compile (L3 (q 'lambda) formals e) nil (rf-sym name) no-tail) no-slots ctx)))
             (label (lambda ((what string) (e rf-value)) (string-append what " of " (symbol->string name) ": " (datum->string e))))
             (requires (the (ref (listof labelled acyclic) @rf) (new nil)))
             ;; ensures and signals as (variable . e), modifies as (e . shape-list).
             (ensures (the (ref rf-vals @rf) (new nil)))
             (signals (the (ref rf-vals @rf) (new nil)))
             (modifies (the (ref rf-vals @rf) (new nil)))
             (shape (the (ref rf-value @rf) (new rf-false)))
             (decreases (the (ref (sumof (none unit) (some labelled)) @rf) (new (sum none #u))))
             (raises (the (ref rf-value @rf) (new rf-false))))
        (letrec ((loop (subr rf-eff (rf-value) unit)
                   (lambda (forms)
                     (let ((clause (if (and (rf-pair? forms) (rf-pair? (rf-car forms)) (rf-symbol? (rf-caar forms))) (strip-name (rf-sym-of (rf-caar forms))) '||)))
                       (cond ((eq? clause 'requires)
                              (begin (set requires (append (get requires) (map (lambda ((e rf-value)) (product (label (label "precondition" e)) (closure (closure formals e))))
                                                                              (rf-elements (rf-cdar forms)))))
                                     (loop (rf-cdr forms))))
                             ((eq? clause 'ensures)
                              (let ((c (rf-car forms)))
                                (begin
                                  (if (and (rf-pair? (rf-cdr c)) (rf-pair? (rf-cadr c)) (rf-symbol? (rf-car (rf-cadr c))) (rf-null? (rf-cdr (rf-cadr c)))) #u
                                      (syntax-error "bad ensures (expected (ensures (result) e ...))" c))
                                  (set ensures (vals-append (get ensures) (map (lambda ((e rf-value)) (rf-cons (rf-car (rf-cadr c)) e)) (rf-elements (rf-cddr c)))))
                                  (loop (rf-cdr forms)))))
                             ((eq? clause 'signals)
                              (let ((c (rf-car forms)))
                                (begin
                                  (if (and (rf-pair? (rf-cdr c)) (rf-pair? (rf-cadr c)) (rf-symbol? (rf-car (rf-cadr c))) (rf-null? (rf-cdr (rf-cadr c)))) #u
                                      (syntax-error "bad signals (expected (signals (e) e ...))" c))
                                  (set signals (vals-append (get signals) (map (lambda ((e rf-value)) (rf-cons (rf-car (rf-cadr c)) e)) (rf-elements (rf-cddr c)))))
                                  (loop (rf-cdr forms)))))
                             ((eq? clause 'raises)
                              (begin
                                (if (and (= (rf-length (rf-car forms)) 2) (shape? (strip (rf-cadr (rf-car forms))))) #u
                                    (syntax-error "bad raises (expected a shape)" (rf-car forms)))
                                (set raises (strip (rf-cadr (rf-car forms))))
                                (loop (rf-cdr forms))))
                             ((eq? clause 'modifies)
                              (let ((c (rf-car forms)))
                                (begin
                                  (if (and (<= 2 (rf-length c)) (<= (rf-length c) 3) (or (rf-null? (rf-cddr c)) (shape? (strip (rf-caddr c))))) #u
                                      (syntax-error "bad modifies (expected (modifies e [shape]))" c))
                                  (set modifies (vals-append (get modifies) (list (rf-cons (rf-cadr c) (strip (rf-cddr c))))))
                                  (loop (rf-cdr forms)))))
                             ((eq? clause 'returns)
                              (begin
                                (if (and (= (rf-length (rf-car forms)) 2) (shape? (rf-cadr (rf-car forms)))) #u
                                    (syntax-error "bad returns (expected a shape)" (rf-car forms)))
                                (set shape (strip (rf-cadr (rf-car forms))))
                                (loop (rf-cdr forms))))
                             ((eq? clause 'decreases)
                              (begin
                                (if (= (rf-length (rf-car forms)) 2) #u (syntax-error "bad decreases (expected (decreases e))" (rf-car forms)))
                                (set decreases (sum some (product (label (string-append "(decreases " (datum->string (rf-cadr (rf-car forms))) ") of " (symbol->string name)))
                                                                  (closure (closure formals (rf-cadr (rf-car forms)))))))
                                (loop (rf-cdr forms))))
                             (else
                              (begin
                                (if (and (rf-null? forms) (rf-false? existing)) (syntax-error "define/contract without a body" x) #u)
                                (if (and (rf-pair? forms) (not (rf-false? existing))) (syntax-error "contract with a body" x) #u)
                                (if (and (pair? (get signals)) (rf-false? (get raises))) (syntax-error "signals without (raises shape)" x) #u)
                                (let* ((ex (extract-olds (map rf-cdr (vals-append (get ensures) (get signals)))))
                                       (es (extract ex exprs)) (olds (extract ex olds))
                                       (old-vars (rf-list (map (lambda ((o old-entry)) (rf-sym (extract o var))) olds)))
                                       (n-ensures (list-length (get ensures)))
                                       (conditions (lambda ((what string) (ps rf-vals) (es rf-vals))
                                                     (map2 (lambda ((p rf-value) (e rf-value))
                                                             (product (label (label what (rf-cdr p)))
                                                                      (closure (closure (rf-cons (rf-car p) (rf-append2 old-vars formals)) e))))
                                                           ps es)))
                                       (pins (pins-of (get ensures) (list-head-vals es n-ensures)
                                                      (lambda ((p rf-value) (e rf-value)) (closure (rf-cons (rf-car p) (rf-append2 old-vars formals)) e))))
                                       (ens (conditions "postcondition" (get ensures) (list-head-vals es n-ensures)))
                                       (sigs (conditions "raise condition" (get signals) (vals-tail es n-ensures)))
                                       (mods (map (lambda ((m rf-value)) (modifies-target name formals closure m)) (get modifies)))
                                       (old-closures (map (lambda ((o old-entry)) (closure formals (extract o expr))) olds))
                                       (body (if (rf-false? existing)
                                                 ((compile (rf-cons (q 'lambda) (rf-cons formals forms)) nil (rf-sym name) no-tail) no-slots ctx)
                                                 existing))
                                       (c (the contract (product (name name) (requires (get requires)) (ensures ens) (olds old-closures) (modifies mods)
                                                                 (shape (get shape)) (decreases (get decreases)) (raises (get raises)) (signals sigs)
                                                                 (body body) (pins pins)))))
                                  (begin
                                    (set contracts (cons c (get contracts)))
                                    (define-global! name (make-primitive name (lambda ((ctx rf-ctx) (args rf-vals) (src rf-value)) (call-contracted ctx c args src)))))))))))))
          (loop (rf-cddr x)))))))

"A stub writes what its postconditions say a place it modifies holds. A pin
is a postcondition (= place e) (or eq?, eqv?, equal?, either way round),
place (vector-ref v i) or (accessor x)."
(define pins-of (subr rf-eff (rf-vals rf-vals (subr rf-eff (rf-value rf-value) rf-value)) (listof pin acyclic))
  (lambda (ps es closure)
    (letrec ((expand-head (subr rf-eff (rf-value) rf-value)
               (lambda (x)
                 (tagcase (if (rf-pair? x) (resolve-value nil (rf-car x)) (sum none #u))
                   (some r (tagcase r (macro m (expand-head (expand nil m x))) (else y x)))
                   (none u x))))
             (place (subr rf-eff (rf-value rf-value) (sumof (none unit) (some pin)))
               (lambda (p x)
                 (let ((x (expand-head x)))
                   (if (and (rf-pair? x) (rf-list? x))
                       (cond ((and (= (rf-length x) 3) (eq? (head-keyword nil (rf-car x)) 'vector-ref))
                              ;; shakedown's (vector 'vector o i): Twobit makes i first.
                              (let* ((i (closure p (rf-caddr x))) (o (closure p (rf-cadr x))))
                                (sum some (product (kind 'vector) (object o) (index i) (value rf-false)))))
                             ((and (= (rf-length x) 2) (rf-symbol? (rf-car x)))
                              (let* ((i (closure p (rf-car x))) (o (closure p (rf-cadr x))))
                                (sum some (product (kind 'field) (object o) (index i) (value rf-false)))))
                             (else (sum none #u)))
                       (sum none #u)))))
             (loop (subr rf-eff (rf-vals rf-vals (listof pin acyclic)) (listof pin acyclic))
               (lambda (ps es acc)
                 (if (null? ps) (the (listof pin acyclic) (reverse acc))
                     (let* ((e (expand-head (car es)))
                            (p (car ps))
                            (pin (the (sumof (none unit) (some pin)) (if (and (rf-pair? e) (rf-list? e) (= (rf-length e) 3)
                                          (symbols-member? (head-keyword nil (rf-car e)) (list '= 'eq? 'eqv? 'equal?)))
                                     ;; shakedown's (let ((a …) (b …)) …): b first.
                                     (let* ((b (place p (rf-caddr e))) (a (place p (rf-cadr e))))
                                       (tagcase a
                                         (some pa (the (sumof (none unit) (some pin)) (sum some (product (kind (extract pa kind)) (object (extract pa object)) (index (extract pa index)) (value (closure p (rf-caddr e)))))))
                                         (none u (tagcase b
                                                   (some pb (the (sumof (none unit) (some pin)) (sum some (product (kind (extract pb kind)) (object (extract pb object)) (index (extract pb index)) (value (closure p (rf-cadr e)))))))
                                                   (none u (sum none #u))))))
                                     (sum none #u)))))
                       (loop (cdr ps) (cdr es) (tagcase pin (some x (cons x acc)) (none u acc))))))))
      (loop ps es nil))))

"Write the pins of c after a stub has havocked its targets and assumed its
postconditions."
(define-type place-write (productof (vec rf-slots) (i int) (value rf-value)))
(define write-pins! (subr rf-eff (rf-ctx contract (listof footprint-of acyclic) rf-vals rf-value) unit)
  (lambda (ctx c targets env src)
    (let ((places (map (lambda ((pin pin))
                         ;; shakedown's (let ((object …) (index …) (value …)) …): value first.
                         (let* ((value (apply-value ctx (extract pin value) env src))
                                (index (apply-value ctx (extract pin index) env src))
                                (object (apply-value ctx (extract pin object) env src)))
                           (if (eq? (extract pin kind) 'vector)
                               (if (and (rf-vector? object) (rf-exact-integer? index) (< -1 (rf-int-of index)) (< (rf-int-of index) (array-length (rf-slots-of object))))
                                   (the (sumof (none unit) (some place-write)) (sum some (product (vec (rf-slots-of object)) (i (rf-int-of index)) (value value))))
                                   (sum none #u))
                               (tagcase (accessor-field-of index)
                                 (some f (if (and (rf-inst? object) (same-rtd? (instance-rtd object) (extract f rtd)))
                                             (the (sumof (none unit) (some place-write)) (sum some (product (vec (instance-fields object)) (i (extract f index)) (value value))))
                                             (sum none #u)))
                                 (none u (sum none #u))))))
                       (extract c pins))))
      (for-each (lambda ((p (sumof (none unit) (some place-write))))
                  (tagcase p
                    (some w (let* ((vec (extract w vec)) (i (extract w i))
                                   (g (t-or* (map (lambda ((gx allowed-target))
                                                    (if (tagcase (extract gx t)
                                                          (field f (and (eq? (extract f object) vec) (= (extract f index) i)))
                                                          (whole v (eq? v vec)))
                                                        (extract gx g) rf-false))
                                                  (targets-allowed targets)))))
                              (if (rf-false? g) #u
                                  (write! ctx vec i (merge g (extract w value) (array-ref vec i))))))
                    (none u #u)))
                places))))
(define accessor-field-of (subr rf-st (rf-value) (sumof (none unit) (some accessor-field)))
  (lambda (p)
    (letrec ((find (subr rf-st ((listof accessor-field acyclic)) (sumof (none unit) (some accessor-field)))
               (lambda (l) (cond ((null? l) (sum none #u)) ((rf-eqv? (extract (car l) prim) p) (sum some (car l))) (else (find (cdr l)))))))
      (find (get accessor-fields)))))

"(contracts-for library-name form …): contracts for procedures the library
defines, given outside it, in its namespace."
(define contracts-for! (subr rf-eff (rf-value rf-ctx) unit)
  (lambda (x ctx)
    (begin
      (if (and (rf-list? x) (rf-pair? (rf-cdr x)) (rf-list? (strip (rf-cadr x)))) #u (syntax-error "bad contracts-for" (strip x)))
      (let* ((lib (get-library (strip (rf-cadr x)) ctx))
             (outer-genv (get globals))
             (outer-library (get current-library))
             (restore! (lambda () (begin (set globals outer-genv) (set current-library outer-library)))))
        (begin
          (set globals (extract lib genv))
          (set current-library (extract lib name))
          (rf-protect
           (lambda ()
             (begin
               (for-each
                (lambda ((form rf-value))
                  (if (and (rf-pair? form) (keyword? (rf-car form) 'contract))
                      (let* ((f (if (and (rf-pair? (rf-cdr form)) (rf-pair? (rf-cadr form))) (rf-cadr form) rf-false))
                             (name (if (and (rf-pair? f) (rf-symbol? (rf-car f))) (strip-name (rf-sym-of (rf-car f))) '||))
                             (v (if (and (not (eq? name '||)) (table-has? (extract (get globals) cells) name))
                                    (array-ref (table-ref (extract (get globals) cells) name no-slots) 0)
                                    rf-false)))
                        (begin
                          (if (rf-closure? v) #u
                              (syntax-error "contract for what the library does not define as a procedure" (strip form)))
                          (define-contract! form ctx v)))
                      (load-program! (list form) ctx)))
                (rf-elements (rf-cddr x)))
               rf-unspecified))
           restore!)
          (restore!))))))

"(modifies e [shape]): e is (global name), or an expression of the formals
giving a vector, a record or a list of them; m is (e . shape-list)."
(define modifies-target (subr rf-eff (symbol rf-value (subr rf-eff (rf-value rf-value) rf-value) rf-value) modifies-clause)
  (lambda (name formals closure m)
    (let* ((e (rf-car m))
           (part (modifies-part e (lambda ((i rf-value)) (sum closure (closure formals i))))))
      (product (label (string-append "(modifies " (datum->string e) ") of " (symbol->string name)))
               (target (cond ((and (rf-pair? e) (keyword? (rf-car e) 'global))
                              (begin
                                (if (and (= (rf-length e) 2) (rf-symbol? (rf-cadr e))) #u (syntax-error "bad modifies (expected (global name))" e))
                                (the mod-target (sum cell (global-cell (strip-name (rf-sym-of (rf-cadr e))))))))
                             ((tagcase part (none u #f) (else y #t)) (the mod-target (sum closure (closure formals (rf-cadr e)))))
                             (else (the mod-target (sum closure (closure formals e))))))
               (shape (if (rf-pair? (rf-cdr m)) (rf-cadr m) rf-false))
               (description (datum->string e))
               (part part)))))

"For (field e name), the field; for (slot e i), the index's code; else none."
(define modifies-part (subr rf-eff (rf-value (subr rf-eff (rf-value) mod-target)) mod-part)
  (lambda (e compile)
    (cond ((and (rf-pair? e) (keyword? (rf-car e) 'field))
           (begin
             (if (and (rf-list? e) (= (rf-length e) 3) (rf-symbol? (strip (rf-caddr e)))) #u (syntax-error "bad modifies (expected (field e name))" (strip e)))
             (sum field (strip-name (rf-sym-of (rf-caddr e))))))
          ((and (rf-pair? e) (keyword? (rf-car e) 'slot))
           (begin
             (if (and (rf-list? e) (= (rf-length e) 3)) #u (syntax-error "bad modifies (expected (slot e i))" (strip e)))
             (sum slot (compile (rf-caddr e)))))
          (else (sum none #u)))))

"The slots-vectors a modifies clause names, on entry: the clause, and
(guard . target)s."
(define-type footprint-of (productof (clause modifies-clause) (targets (listof allowed-target acyclic))))
(define targets-allowed (subr rf-st ((listof footprint-of acyclic)) (listof allowed-target acyclic))
  (lambda (ts) (if (null? ts) nil (append (extract (car ts) targets) (targets-allowed (cdr ts))))))
(define-type maybe-target (productof (g rf-value) (t (sumof (none unit) (some target)))))
(define some-whole (subr rf-st (rf-slots) (sumof (none unit) (some target))) (lambda (v) (sum some (sum whole v))))
(define some-field (subr rf-st (rf-slots int) (sumof (none unit) (some target))) (lambda (v i) (sum some (sum field (product (object v) (index i))))))
(define no-target (sumof (none unit) (some target)) (sum none #u))

(define modifies-footprints (subr rf-eff (rf-ctx contract rf-vals rf-value) (listof footprint-of acyclic))
  (lambda (ctx c args src)
    (footprints ctx (extract c modifies)
                (lambda ((t mod-target)) (tagcase t (closure f (apply-value ctx f args src)) (cell c rf-false) (code p rf-false))))))

(define footprints (subr rf-eff (rf-ctx (listof modifies-clause acyclic) (subr rf-eff (mod-target) rf-value)) (listof footprint-of acyclic))
  (lambda (ctx ms value-of)
    (map (lambda ((m modifies-clause))
           (let* ((target (extract m target))
                  (part (extract m part))
                  (fp (tagcase target
                        (cell c (the (listof maybe-target acyclic) (list (product (g rf-true) (t (some-whole c))))))
                        (else y
                          (tagcase part
                            (field f (field-footprint rf-true (value-of target) f))
                            (slot s (slot-footprint ctx rf-true (value-of target) (value-of s) (extract m description)))
                            (none u (map (lambda ((e footprint-entry))
                                           (product (g (extract e g)) (t (tagcase (extract e obj) (some o (some-whole o)) (none u no-target)))))
                                         (footprint rf-true (value-of target)))))))))
             (begin
               (for-each (lambda ((g+vec maybe-target))
                           (tagcase (extract g+vec t)
                             (some x #u)
                             (none u (check! ctx 'contract-frame
                                             (string-append (extract m label)
                                                            (tagcase part
                                                              (field f (string-append " is a record with a field " (symbol->string f) ", or a list of them"))
                                                              (slot s " is a vector with the slot, or a list of them")
                                                              (none u " is a vector, a record or a list of them")))
                                             (t-not (extract g+vec g))))))
                         fp)
               (product (clause m)
                        (targets (apply-append-targets (map (lambda ((x maybe-target)) (tagcase (extract x t) (some t (the (listof allowed-target acyclic) (list (product (g (extract x g)) (t t))))) (none u (the (listof allowed-target acyclic) nil)))) fp)))))))
         ms)))
(define apply-append-targets (subr rf-st ((listof (listof allowed-target acyclic) acyclic)) (listof allowed-target acyclic))
  (lambda (ls) (if (null? ls) nil (append (car ls) (apply-append-targets (cdr ls))))))

"As field-footprint, for slot i of vectors (i a concrete integer)."
(define slot-footprint (subr rf-eff (rf-ctx rf-value rf-value rf-value string) (listof maybe-target acyclic))
  (lambda (ctx g v i description)
    (begin
      (if (rf-exact-integer? i) #u (fail! ctx 'unsupported (string-append "(modifies " description "): a symbolic slot")))
      (letrec ((loop (subr rf-eff (rf-members) (listof maybe-target acyclic))
                 (lambda (ms)
                   (if (null? ms) nil
                       (let ((g (extract (car ms) g)) (x (extract (car ms) v)))
                         (append (cond ((and (rf-vector? x) (< -1 (rf-int-of i)) (< (rf-int-of i) (array-length (rf-slots-of x))))
                                        (list (product (g g) (t (some-field (rf-slots-of x) (rf-int-of i))))))
                                       ((rf-pair? x) (let* ((a (slot-footprint ctx g (rf-car x) i description)) (d (slot-footprint ctx g (rf-cdr x) i description))) (append a d)))
                                       ((rf-null? x) nil)
                                       (else (list (product (g g) (t no-target)))))
                                 (loop (cdr ms))))))))
        (loop (guarded-members g v))))))

"As footprint does, for the field of records v names."
(define field-footprint (subr rf-eff (rf-value rf-value symbol) (listof maybe-target acyclic))
  (lambda (g v field)
    (letrec ((loop (subr rf-eff (rf-members) (listof maybe-target acyclic))
               (lambda (ms)
                 (if (null? ms) nil
                     (let ((g (extract (car ms) g)) (x (extract (car ms) v)))
                       (append (cond ((and (rf-inst? x) (symbols-member? field (extract (instance-rtd x) fields)))
                                      (let ((fs (extract (instance-rtd x) fields)))
                                        (list (product (g g) (t (some-field (instance-fields x) (- (list-length fs) (list-length (symbols-from field fs)))))))))
                                     ((rf-pair? x) (let* ((a (field-footprint g (rf-car x) field)) (d (field-footprint g (rf-cdr x) field))) (append a d)))
                                     ((rf-null? x) nil)
                                     (else (list (product (g g) (t no-target)))))
                               (loop (cdr ms))))))))
      (loop (guarded-members g v)))))
(define symbols-from (subr rf-st (symbol symbols) symbols)
  (lambda (s l) (cond ((null? l) nil) ((eq? (car l) s) l) (else (symbols-from s (cdr l))))))

(define old-values (subr rf-eff (rf-ctx contract rf-vals rf-value) rf-vals)
  (lambda (ctx c args src) (map (lambda ((o rf-value)) (apply-value ctx o args src)) (extract c olds))))

(define call-contracted (subr rf-eff (rf-ctx contract rf-vals rf-value) rf-value)
  (lambda (ctx c args src)
    (let* ((name (extract c name))
           (body (extract c body))
           (inside? (tagcase body
                      (closure b (letrec ((f (subr rf-st (rf-unwinds) bool) (lambda (l) (and (pair? l) (or (eq? (extract (car l) f) b) (f (cdr l)))))))
                                   (f (ctx-unwind ctx))))
                      (else x #f))))
      (cond ((or (symbols-member? name (get mode-stubs)) (and inside? (for-contract-is? name)))
             (call-stub ctx c args src))
            ((for-contract-is? name)
             (begin
               (set contract-calls (+ 1 (get contract-calls)))
               (for-each (lambda ((p labelled)) (assume! ctx (truth (apply-value ctx (extract p closure) args src)))) (extract c requires))
               (let* ((outer-measure (get contract-measure))
                      (m (tagcase (extract c decreases)
                           (some d (measure ctx (extract d label) (apply-value ctx (extract d closure) args src)))
                           (none u rf-false)))
                      (checked (if (rf-false? m) #u
                                   (begin (check! ctx 'contract (string-append (tagcase (extract c decreases) (some d (extract d label)) (none u "")) " is not negative")
                                                  (t-<= (rf-int 0) m))
                                          (set contract-measure m))))
                      (olds (old-values ctx c args src))
                      (targets (modifies-footprints ctx c args src))
                      (r (watching-writes 'contract-frame
                                          (string-append (symbol->string name) (if (null? targets) " writes to something it did not allocate"
                                                                                  " writes to something it did not allocate or name in (modifies ...)"))
                                          (targets-allowed targets)
                                          (lambda () (call-body ctx c args src olds (sum some (lambda ((ctx rf-ctx)) (check-leaves ctx c targets))))))))
                 (begin
                   (set contract-measure outer-measure)
                   (check-postconditions ctx c olds args r src)
                   (if (rf-false? (extract c shape)) #u
                       (check! ctx 'contract-frame
                               (string-append "the result of " (symbol->string name) " fits " (datum->string (L2 (q 'returns) (extract c shape))))
                               (fits (extract c shape) r)))
                   (check-leaves ctx c targets)
                   r))))
            (else
             (begin
               (check-preconditions ctx c args src)
               (let* ((olds (old-values ctx c args src))
                      (r (call-body ctx c args src olds (sum none #u))))
                 (begin (check-postconditions ctx c olds args r src) r))))))))

"What the stub would havoc, the body must leave in the shape."
(define check-leaves (subr rf-eff (rf-ctx contract (listof footprint-of acyclic)) unit)
  (lambda (ctx c targets)
    (for-each
     (lambda ((t footprint-of))
       (let ((shape (extract (extract t clause) shape)))
         (if (rf-false? shape) #u
             (check! ctx 'contract-frame
                     (string-append "what " (symbol->string (extract c name)) " leaves in " (extract (extract t clause) description) " fits " (datum->string shape))
                     (t-and* (map (lambda ((g+vec allowed-target))
                                    (t-implies (extract g+vec g) (t-and* (map (lambda ((v rf-value)) (fits shape v)) (target-values (extract g+vec t))))))
                                  (extract t targets)))))))
     targets)))
(define target-values (subr rf-st (target) rf-vals)
  (lambda (x) (tagcase x (field f (list (array-ref (extract f object) (extract f index)))) (whole v (slots-list v)))))

"A contract's procedure may raise to its caller only what its raises clause
allows, meeting its signals conditions."
(define call-body (subr rf-eff (rf-ctx contract rf-vals rf-value rf-vals (sumof (none unit) (some (subr rf-eff (rf-ctx) unit)))) rf-value)
  (lambda (ctx c args src olds on-raise)
    (let ((name (extract c name)) (shape (extract c raises)))
      (if (rf-false? shape)
          (barrier (raise-label name shape) (lambda () (apply-value ctx (extract c body) args src)))
          (catching ctx
                    (lambda ((ctx rf-ctx)) (apply-value ctx (extract c body) args src))
                    (lambda ((ctx rf-ctx) (v rf-value))
                      (begin
                        ;; What does not fit fails, as at a barrier.
                        (barrier (raise-label name shape)
                                 (lambda ()
                                   (begin
                                     (for-each (lambda ((m rf-member))
                                                 (begin (raise! ctx (extract m v) #f (let ((nf (t-not (fits shape (extract m v))))) (t-and (extract m g) nf))) #u))
                                               (guarded-members rf-true v))
                                     rf-unspecified)))
                        (for-each (lambda ((p labelled))
                                    (let ((ok (truth (apply-value ctx (extract p closure) (cons v (vals-append olds args)) src))))
                                      (begin (at-source! src) (check! ctx 'contract (extract p label) ok))))
                                  (extract c signals))
                        (tagcase on-raise (some f (f ctx)) (none u #u))
                        (raise! ctx v #f rf-true)))
                    (sum none #u))))))

(define raise-label (subr rf-eff (symbol rf-value) string)
  (lambda (name shape)
    (if (rf-false? shape)
        (string-append (symbol->string name) " raised an exception, which its contract does not allow")
        (string-append (symbol->string name) " raised what its " (datum->string (L2 (q 'raises) shape)) " does not allow"))))

(define call-stub (subr rf-eff (rf-ctx contract rf-vals rf-value) rf-value)
  (lambda (ctx c args src)
    (begin
      (set abstraction "the proof uses a contract as a stub")
      (check-preconditions ctx c args src)
      (tagcase (extract c decreases)
        (some d (if (and (not (rf-false? (get contract-measure))) (for-contract-is? (extract c name)))
                    (check! ctx 'contract (string-append (extract d label) " at " (datum->string src))
                            (t-< (measure ctx (extract d label) (apply-value ctx (extract d closure) args src)) (get contract-measure)))
                    #u))
        (none u #u))
      (if (rf-false? (extract c shape))
          (fail! ctx 'contract-frame (string-append (symbol->string (extract c name)) " has no (returns shape), so it cannot be used as a stub"))
          #u)
      (let* ((olds (old-values ctx c args src))
             (targets (modifies-footprints ctx c args src))
             (r (generate ctx (extract c shape) (string-append "result of " (datum->string src)))))
        (begin
          (havoc! ctx targets (string-append " after " (datum->string src)) " has no shape, so it cannot be used as a stub")
          (let ((returns (lambda ((ctx rf-ctx))
                           (begin
                             (for-each (lambda ((p labelled)) (assume! ctx (truth (apply-value ctx (extract p closure) (cons r (vals-append olds args)) src))))
                                       (extract c ensures))
                             (write-pins! ctx c targets (cons r (vals-append olds args)) src)
                             r))))
            (if (rf-false? (extract c raises))
                (returns ctx)
                ;; It raises, or not, by a fresh boolean.
                (let ((raises? (fresh-constant! ctx sort-bool (string-append "whether " (datum->string src) " raises"))))
                  (join ctx
                        (list (make-arm raises?
                                        (lambda ((ctx rf-ctx))
                                          (let ((e (generate ctx (extract c raises) (string-append "what " (datum->string src) " raises"))))
                                            (begin
                                              (for-each (lambda ((p labelled)) (assume! ctx (truth (apply-value ctx (extract p closure) (cons e (vals-append olds args)) src))))
                                                        (extract c signals))
                                              (raise! ctx e #f rf-true)))))
                              (make-arm (t-not raises?) returns))
                        #f)))))))))

"Havoc what modifies clauses name: each slot gets a new value of the shape
(under the target's guard)."
(define havoc! (subr rf-eff (rf-ctx (listof footprint-of acyclic) string string) unit)
  (lambda (ctx targets when no-shape)
    (for-each
     (lambda ((t footprint-of))
       (let ((shape (extract (extract t clause) shape)))
         (begin
           (if (rf-false? shape) (fail! ctx 'contract-frame (string-append (extract (extract t clause) label) no-shape)) #u)
           (for-each
            (lambda ((g+vec allowed-target))
              (let* ((x (extract g+vec t))
                     (vec (tagcase x (field f (extract f object)) (whole v v)))
                     (havoc-slot! (lambda ((i int) (description string))
                                    (let ((v (generate ctx shape (string-append description when))))
                                      (write! ctx vec i (merge (extract g+vec g) v (array-ref vec i)))))))
                (tagcase x
                  (field f (havoc-slot! (extract f index) (extract (extract t clause) description)))
                  (whole v (letrec ((loop (subr rf-eff (int) unit)
                                          (lambda (i) (if (>= i (array-length vec)) #u
                                                          (begin (havoc-slot! i (string-append "slot " (int->string i) " of " (extract (extract t clause) description)))
                                                                 (loop (+ i 1)))))))
                             (loop 0))))))
            (extract t targets)))))
     targets)))

"A contract's checks are placed at the call."
(define check-preconditions (subr rf-eff (rf-ctx contract rf-vals rf-value) unit)
  (lambda (ctx c args src)
    (for-each (lambda ((p labelled))
                (let ((ok (truth (apply-value ctx (extract p closure) args src))))
                  (begin (at-source! src) (check! ctx 'contract (extract p label) ok))))
              (extract c requires))))
(define check-postconditions (subr rf-eff (rf-ctx contract rf-vals rf-vals rf-value rf-value) unit)
  (lambda (ctx c olds args r src)
    (for-each (lambda ((p labelled))
                (let ((ok (truth (apply-value ctx (extract p closure) (cons r (vals-append olds args)) src))))
                  (begin (at-source! src) (check! ctx 'contract (extract p label) ok))))
              (extract c ensures))))

;;; ------------------------------------------------------------ records

"(define-record-type name (constructor field …) predicate (field accessor
[modifier]) …)"
(define define-record-type! (subr rf-eff (rf-value) unit)
  (lambda (x)
    (begin
      (if (and (<= 3 (rf-length x)) (rf-list? x)) #u (syntax-error "bad define-record-type" x))
      (let* ((type-name (if (rf-pair? (rf-cadr x)) (rf-car (rf-cadr x)) (rf-cadr x)))
             (ctor (rf-caddr x))
             (pred (rf-cadddr x))
             (specs (map (lambda ((s rf-value)) (if (rf-symbol? s) (L1 s) s)) (rf-elements (rf-cddddr x))))
             (fields (map (lambda ((s rf-value)) (rf-sym-of (rf-car s))) specs))
             (rt (make-record-type (rf-sym-of type-name) fields))
             (index (lambda ((field rf-value))
                      (letrec ((loop (subr rf-eff (symbols int) int)
                                 (lambda (fs i) (cond ((null? fs) (begin (syntax-error "not a field" field) 0))
                                                      ((eq? (car fs) (rf-sym-of field)) i)
                                                      (else (loop (cdr fs) (+ i 1)))))))
                        (loop fields 0)))))
        (begin
          (if (rf-false? ctor) #u
              (let* ((ctor-name (rf-sym-of (if (rf-pair? ctor) (rf-car ctor) ctor)))
                     (ctor-fields (if (rf-pair? ctor) (rf-elements (rf-cdr ctor)) (map rf-sym fields)))
                     (indexes (map index ctor-fields))
                     (n (list-length fields)))
                (define-global! ctor-name
                  (make-primitive ctor-name
                                  (lambda ((ctx rf-ctx) (args rf-vals) (src rf-value))
                                    (begin
                                      (if (= (list-length args) (list-length indexes)) #u (fail! ctx 'error (describe-call src "wrong number of arguments")))
                                      (let ((v (note-allocation! (the rf-slots (make-array n rf-unspecified)))))
                                        (begin (for-each2 (lambda ((i int) (a rf-value)) (array-set! v i a)) indexes args)
                                               (make-instance rt v)))))))))
          (define-global! (rf-sym-of pred)
            (make-primitive (rf-sym-of pred)
                            (lambda ((ctx rf-ctx) (args rf-vals) (src rf-value))
                              (begin
                                (if (= (list-length args) 1) #u (fail! ctx 'error (describe-call src "wrong number of arguments")))
                                (merge-members (map (lambda ((m rf-member)) (member (extract m g) (rf-bool (and (rf-inst? (extract m v)) (same-rtd? (instance-rtd (extract m v)) rt)))))
                                                    (guarded-members rf-true (car args))))))))
          (for-each
           (lambda ((spec rf-value))
             (let* ((i (index (rf-car spec)))
                    (instance-arg (lambda ((ctx rf-ctx) (src rf-value) (v rf-value))
                                    (if (and (rf-inst? v) (same-rtd? (instance-rtd v) rt)) #u
                                        (fail! ctx 'error (describe-call src (string-append "argument is not a " (datum->string type-name))))))))
               (begin
                 (if (rf-pair? (rf-cdr spec))
                     (let ((accessor (make-primitive (rf-sym-of (rf-cadr spec))
                                                     (lambda ((ctx rf-ctx) (args rf-vals) (src rf-value))
                                                       (begin
                                                         (if (= (list-length args) 1) #u (fail! ctx 'error (describe-call src "wrong number of arguments")))
                                                         (lift ctx args (lambda ((ctx rf-ctx) (args rf-vals))
                                                                          (begin (instance-arg ctx src (car args))
                                                                                 (array-ref (instance-fields (car args)) i)))))))))
                       (begin (set accessor-fields (cons (product (prim accessor) (rtd rt) (index i)) (get accessor-fields)))
                              (define-global! (rf-sym-of (rf-cadr spec)) accessor)))
                     #u)
                 (if (and (rf-pair? (rf-cdr spec)) (rf-pair? (rf-cddr spec)))
                     (define-global! (rf-sym-of (rf-caddr spec))
                       (make-primitive (rf-sym-of (rf-caddr spec))
                                       (lambda ((ctx rf-ctx) (args rf-vals) (src rf-value))
                                         (begin
                                           (if (= (list-length args) 2) #u (fail! ctx 'error (describe-call src "wrong number of arguments")))
                                           (lift ctx (list (car args))
                                                 (lambda ((ctx rf-ctx) (r rf-vals))
                                                   (begin (instance-arg ctx src (car r))
                                                          (write! ctx (instance-fields (car r)) i (car (cdr args)))
                                                          rf-unspecified)))))))
                     #u))))
           specs))))))

;;; ------------------------------------------------------------ top-level forms

(define extras (ref prim-entries @rf) (new nil))

"Evaluate a program's top-level forms in order, under ctx."
(define load-program! (subr rf-eff (rf-vals rf-ctx) unit)
  (lambda (forms ctx) (for-each (lambda ((form rf-value)) (top-level-form! form ctx)) forms)))

"Names a macro defines at top level are the names themselves, not renamed."
(define top-level-form! (subr rf-eff (rf-value rf-ctx) unit)
  (lambda (x ctx)
    (let* ((r (if (rf-pair? x) (resolve-value nil (rf-car x)) (sum none #u)))
           (m (tagcase r (some res (tagcase res (macro m (the rf-maybe-macro (sum some m))) (else y (the rf-maybe-macro (sum none #u))))) (none u (sum none #u))))
           (keyword (tagcase r (some res (tagcase res (global g (extract g name)) (else y '||))) (none u '||))))
      (tagcase m
        (some mac (top-level-form! (expand nil mac x) ctx))
        (none u
          (cond ((eq? keyword 'begin) (load-program! (rf-elements (rf-cdr x)) ctx))
                ((or (eq? keyword 'include) (eq? keyword 'include-ci) (eq? keyword 'load)) (load-program! (included-forms x syntax-error) ctx))
                ((eq? keyword 'import) (for-each (lambda ((set rf-value)) (import! set ctx)) (rf-elements (rf-cdr x))))
                ((eq? keyword 'define-library) (define-library! x (car (library-path)) ctx))
                ((eq? keyword 'cond-expand)
                 (load-program! (apply-append-vals (map (lambda ((d rf-value)) (rf-elements (rf-cdr d)))
                                                        (expand-declarations (list x) "." known-library? syntax-error)))
                                ctx))
                ((eq? keyword 'define)
                 (let ((d (normalize-define x)))
                   (define-global! (strip-name (extract d name))
                                   ((compile (extract d expr) nil (rf-sym (extract d name)) no-tail) no-slots ctx))))
                ((eq? keyword 'define-values) (load-program! (define-values->defines x) ctx))
                ((eq? keyword 'define-syntax)
                 (begin
                   (if (and (rf-list? x) (= (rf-length x) 3) (rf-symbol? (rf-cadr x))) #u (syntax-error "bad define-syntax" (strip x)))
                   (define-global-macro! (strip-name (rf-sym-of (rf-cadr x))) (make-macro (rf-caddr x) nil))))
                ((eq? keyword 'define-record-type) (define-record-type! (strip x)))
                ((eq? keyword 'define-proof) (define-proof! x))
                ((eq? keyword 'define/contract) (define-contract! x ctx rf-false))
                ((eq? keyword 'contracts-for) (contracts-for! x ctx))
                (else (begin ((compile0 x nil) no-slots ctx) #u))))))))

"Set up the special forms and the globals of this file, once."
(define installed? (ref bool @rf) (new #f))
(define install! (subr rf-st () unit)
  (lambda ()
    (if (get installed?) #u
        (begin
          (set installed? #t)
          (install-primitives!)
          (install-core-forms!)
          (install-control-forms!)
          (install-control-globals!)
          (install-check-forms!)
          (set-raise-hooks! apply-value show)
          ;; The globals defined in this file, kept when the globals are reset.
          (set extras (map (lambda ((name symbol)) (product (name name) (value (array-ref (global-cell name) 0))))
                           (list 'any-integer 'any-boolean 'any-of 'any-list 'arbitrary 'fits? 'apply
                                 'with-exception-handler 'call-with-values 'make-parameter 'call/cc
                                 'call-with-current-continuation)))))))

(define reset-globals! (subr rf-eff () unit)
  (lambda ()
    (begin
      (install!)
      (set globals (new-genv (sum none #u)))
      (set builtin-genv (get globals))
      (set libraries nil)
      (set current-library rf-false)
      (set the-proofs nil)
      (set contracts nil)
      (begin-proof-mode! (sum none #u))
      (for-each (lambda ((e prim-entry)) (define-global! (extract e name) (extract e value)))
                (append (primitives) (get extras) (hashtable-primitives apply-value) (port-primitives apply-value)))
      (begin-session! 0 #f)
      (set tracing? #f)
      (set-pairs-mutable! #f)
      (load-program! (prelude-forms) (make-ctx rf-true 0 nil))
      (set tracing? #t))))
