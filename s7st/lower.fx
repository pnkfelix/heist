;;; lower.fx: Scheme's core (value.fx's `s7-node`) lowered to FX-26, staged
;;; (Fixpt's `stage`) and run; and what runs top-level forms.
;;;
;;; Each top-level form is expanded (expand.fx), lowered to a datum of
;;; FX-26 code, checked and compiled against the module `s7-rt` (what
;;; machine.fx gives lowered code), and run. The code is
;;;   (lambda ((K …) (G …) (L …)) (let ((k0 (array-ref K 0)) … ) (lambda () BODY)))
;;; given the form's constants (K: quoted data, which must be the same
;;; object each time), the global cells it names (G) and its lambdas'
;;; descriptions (L), so that its text holds none of them. In BODY:
;;;   - a local is an FX-26 variable; one assigned (`set!`, a definition in
;;;     a body, `letrec`'s) is a box, `(ref %value @sc)`, read through
;;;     `%lref`, which says if it is not yet defined;
;;;   - a lambda is `(%proc lN (sum aR (lambda (…) …)))`, an FX-26 procedure
;;;     of its R arguments (up to four, one clause, no rest); else of their
;;;     list, `an`, its clauses tried in order. Its body first spends fuel
;;;     (`%tick`);
;;;   - a call is `(%callR f a …)`, or `(%calln f (list a …))`;
;;;   - a global is read through `%gref`, set and defined through `%gset!`
;;;     and `%gdefine!`.

;;; ------------------------------------------------------------ lowering

"A slot of a frame as lowered: the FX-26 variable it is, and whether that
is a box; and, if the slot is a procedure's, set once to a lambda where
its frame begins (a named `let`'s loop, a body's `define`), that
procedure as an FX-26 one (its `letrec`'s variable, and how many it
takes), which a call of it with as many calls directly."
(define-type s7-direct (productof (fn symbol) (arity int)))
(define-type s7-slot (productof (var symbol) (boxed bool) (direct (listof s7-direct acyclic))))
"A slot set once to a lambda, of one clause of at most four parameters,
where its frame begins: its index, and its lambdas."
(define-type s7-direct-slot (productof (index int) (lams (listof s7-lambda acyclic))))
(define-type s7-lframe (listof s7-slot acyclic))
(define-type s7-lframes (listof s7-lframe acyclic))
"What a form's lowering has gathered: its constants, cells and lambdas,
last first, and how many of each; and a counter for its variables."
(define-type s7-lowering
  (productof (consts (ref s7-values @sc)) (nconsts (ref int @sc))
             (cells (ref (listof s7-global acyclic) @sc)) (ncells (ref int @sc))
             (lams (ref (listof (listof s7-lambda acyclic) acyclic) @sc)) (nlams (ref int @sc))
             (vars (ref int @sc))))
(define* s7-new-lowering (subr (alloc @sc) () s7-lowering)
  (lambda ()
    (product (consts (the (ref s7-values @sc) (new nil))) (nconsts (the (ref int @sc) (new 0)))
             (cells (the (ref (listof s7-global acyclic) @sc) (new nil))) (ncells (the (ref int @sc) (new 0)))
             (lams (the (ref (listof (listof s7-lambda acyclic) acyclic) @sc) (new nil))) (nlams (the (ref int @sc) (new 0)))
             (vars (the (ref int @sc) (new 0))))))
(define* s7-numbered (subr spin (string int) symbol)
  (lambda (prefix n) (string->symbol (string-append prefix (int->string n)))))
"Procedure (or value) `name` of what lowered code runs on, as it names
it: a field of `T` (`s7-staged-tables`), not of the module, so that a
closure has `T` alone of them among its free values."
(define* s7-rt-op (subr (alloc @sc) (symbol) datum)
  (lambda (name) (list 'extract 'T name)))
"Entry `n` of table `table` (`k`, `g` or `l`) of the form's tables `T`, as
lowered code reads it: the tables are one free value of a closure, not an
entry each, so that most closures have few enough (8) to be made in line."
(define* s7-table-ref (subr (alloc @sc) (symbol int) datum)
  (lambda (table n) (list 'array-ref (list 'extract 'T table) n)))
"A fresh variable, `prefix` and a number."
(define* s7-fresh-var (subr (maxeff spin (read @sc) (write @sc)) (s7-lowering string) symbol)
  (lambda (cx prefix)
    (let ((n (get (extract cx vars)))) (begin (set (extract cx vars) (+ n 1)) (s7-numbered prefix n)))))
"Constant `v`, as lowered code reads it."
(define* s7-const-var (subr (maxeff spin (read @sc) (write @sc) (alloc @sc)) (s7-lowering s7-value) datum)
  (lambda (cx v)
    (let ((n (get (extract cx nconsts))))
      (begin (set (extract cx consts) (cons v (get (extract cx consts))))
        (set (extract cx nconsts) (+ n 1))
        (s7-table-ref 'k n)))))
"Cell `c`, as lowered code reads it: one entry for each cell."
(define* s7-cell-var (subr (maxeff spin (read @sc) (write @sc) (alloc @sc)) (s7-lowering s7-global) datum)
  (lambda (cx c)
    (let ((n (get (extract cx ncells))))
      (letrec ((find (subr spin ((listof s7-global acyclic) int) int)
                 ;; The index of `c` in `l`, whose first is number `i`, or -1.
                 (lambda (l i) (cond ((null? l) -1) ((eq? (extract (car l) value) (extract c value)) i) (else (find (cdr l) (- i 1)))))))
        (let ((i (find (get (extract cx cells)) (- n 1))))
          (if (>= i 0) (s7-table-ref 'g i)
              (begin (set (extract cx cells) (cons c (get (extract cx cells))))
                (set (extract cx ncells) (+ n 1))
                (s7-table-ref 'g n))))))))
(define* s7-lams-var (subr (maxeff spin (read @sc) (write @sc) (alloc @sc)) (s7-lowering (listof s7-lambda acyclic)) datum)
  (lambda (cx ls)
    (let ((n (get (extract cx nlams))))
      (begin (set (extract cx lams) (cons ls (get (extract cx lams))))
        (set (extract cx nlams) (+ n 1))
        (s7-table-ref 'l n)))))

"The slots of the frame `depth` out from node `n`'s that `n` assigns, onto
`acc`."
(define* s7-assigned (subr spin (s7-node int (listof int acyclic)) (listof int acyclic))
  (lambda (n depth acc)
    (letrec ((all (subr spin (s7-nodes int (listof int acyclic)) (listof int acyclic))
               (lambda (ns d acc) (if (null? ns) acc (all (cdr ns) d (s7-assigned (car ns) d acc))))))
      (tagcase (extract n form)
        (n-set-local x (s7-assigned (extract x value) depth
                                    (if (= (extract x depth) depth) (cons (extract x index) acc) acc)))
        (n-set-global x (s7-assigned (extract x value) depth acc))
        (n-define x (s7-assigned (extract x value) depth acc))
        (n-if x (s7-assigned (extract x else) depth (s7-assigned (extract x then) depth (s7-assigned (extract x test) depth acc))))
        (n-lambda ls (letrec ((each (subr spin ((listof s7-lambda acyclic) (listof int acyclic)) (listof int acyclic))
                                (lambda (ls acc) (if (null? ls) acc (each (cdr ls) (s7-assigned (extract (car ls) body) (+ depth 1) acc))))))
                       (each ls acc)))
        (n-seq ns (all ns depth acc))
        (n-call x (all (extract x args) depth (s7-assigned (extract x op) depth acc)))
        (n-scope x (s7-assigned (extract x body) (+ depth 1) acc))
        (else y acc)))))

"`(the (ref %value @sc) (new init))`."
(define* s7-box-datum (subr (alloc @sc) (datum) datum)
  (lambda (init) (list 'the '(ref %value @sc) (list 'new init))))
"`body` within `bindings` (a let's), if there are any."
(define* s7-let-datum (subr (alloc @sc) ((listof datum acyclic) datum) datum)
  (lambda (bindings body) (if (null? bindings) body (list 'let bindings body))))
(define* s7-call-op (subr (alloc @sc) (int) datum)
  (lambda (n) (s7-rt-op (cond ((= n 0) 'call0) ((= n 1) 'call1) ((= n 2) 'call2) ((= n 3) 'call3) (else 'call4)))))
(define* s7-proc-op (subr (alloc @sc) (int) datum)
  (lambda (n) (s7-rt-op (cond ((= n 0) 'proc0) ((= n 1) 'proc1) ((= n 2) 'proc2) ((= n 3) 'proc3) (else 'proc4)))))

"The fused call (machine.fx's) of global `c` with `k` arguments, by its
field of `T`, if `c` holds a built-in that has one, as `c` is now and the
built-ins are intact; and whether it has a test's own (`field?`)."
(define-type s7-fused (productof (field symbol) (test bool)))
(define* s7-fused-of (subr (read @sc) (s7-global int) (sumof (none unit) (some s7-fused)))
  (lambda (c k)
    (let ((f (lambda ((name symbol) (test bool)) (sum some (product (field name) (test test))))))
      (if (not (get s7-builtins-intact)) (sum none #u)
          (tagcase (get (extract c value))
            (prim p (let ((n (extract p name)))
                      (cond ((= k 2) (cond ((string=? n "+") (f 'add #f)) ((string=? n "-") (f 'sub #f)) ((string=? n "*") (f 'mul #f))
                                           ((string=? n "<") (f 'lt #t)) ((string=? n ">") (f 'gt #t)) ((string=? n "<=") (f 'le #t))
                                           ((string=? n ">=") (f 'ge #t)) ((string=? n "=") (f 'num= #t))
                                           ((or (string=? n "eq?") (string=? n "eqv?")) (f 'eq #t)) ((string=? n "cons") (f 'cons #f))
                                           (else (sum none #u))))
                            ((= k 1) (cond ((string=? n "car") (f 'car #f)) ((string=? n "cdr") (f 'cdr #f))
                                           ((string=? n "null?") (f 'null #t)) ((string=? n "pair?") (f 'pair #t))
                                           ((string=? n "not") (f 'not #t)) ((string=? n "zero?") (f 'zero #t))
                                           (else (sum none #u))))
                            (else (sum none #u)))))
            (else y (sum none #u)))))))
"`name`, a test's own: `name?`."
(define* s7-test-field (subr spin (symbol) symbol)
  (lambda (name) (string->symbol (string-append (symbol->string name) "?"))))
"A call of global `c` on `args`, `k` of them: fused, or by `gcallK`."
(define* s7-global-call (subr (maxeff spin (read @sc) (write @sc) (alloc @sc)) (s7-lowering s7-global (listof datum acyclic) int) datum)
  (lambda (cx c args k)
    (let ((cv (s7-cell-var cx c)))
      (tagcase (s7-fused-of c k)
        (some f (cons (s7-rt-op (extract f field)) (cons cv args)))
        (none u (if (<= k 4)
                    (cons (s7-rt-op (string->symbol (string-append "gcall" (int->string k)))) (cons cv args))
                    (list (s7-rt-op 'calln) (list (s7-rt-op 'gref) cv) (cons 'list args))))))))
"A call of `op` on `args`, `k` of them."
(define* s7-call-datum (subr (alloc @sc) (datum (listof datum acyclic) int) datum)
  (lambda (op args k)
    (if (<= k 4) (cons (s7-call-op k) (cons op args)) (list (s7-rt-op 'calln) op (cons 'list args)))))
"`k` fresh parameters' variables."
(define* s7-fresh-vars (subr (maxeff spin (read @sc) (write @sc) (alloc @sc)) (s7-lowering int) (listof symbol acyclic))
  (lambda (cx k)
    (letrec ((go (subr (maxeff spin (read @sc) (write @sc) (alloc @sc)) (int (listof symbol acyclic)) (listof symbol acyclic))
               (lambda (i acc) (if (>= i k) (reverse acc) (go (+ i 1) (cons (s7-fresh-var cx "p") acc))))))
      (go 0 nil))))
"The bindings `(p a)` of `ps` to `as`, in order."
(define* s7-zip-bindings (subr (maxeff spin (alloc @sc)) ((listof symbol acyclic) (listof datum acyclic)) (listof datum acyclic))
  (lambda (ps as)
    (if (or (null? ps) (null? as)) nil (cons (list (car ps) (car as)) (s7-zip-bindings (cdr ps) (cdr as))))))
"A lambda's frame, as lowered: `params` the variables its parameters
arrive in (the rest's too, if it has one); `size` its slots, those after
the parameters its body's definitions; the slots it assigns boxed, those
in `directs` procedures too. The frame, the bindings that make its boxes,
and each direct one's variable and lambda."
(define-type s7-raw (productof (fn symbol) (lam s7-lambda)))
(define-type s7-lambda-frame (productof (frame s7-lframe) (bindings (listof datum acyclic)) (raws (listof s7-raw acyclic))))
(define* s7-frame-of (subr s7-eff (s7-lowering (listof symbol acyclic) int (listof int acyclic) (listof s7-direct-slot acyclic)) s7-lambda-frame)
  (lambda (cx params size assigned directs)
    (letrec ((direct-of (subr spin (int (listof s7-direct-slot acyclic)) (sumof (none unit) (some s7-lambda)))
               (lambda (i ds) (cond ((null? ds) (sum none #u))
                                    ((= (extract (car ds) index) i) (sum some (car (extract (car ds) lams))))
                                    (else (direct-of i (cdr ds))))))
             (go (subr s7-eff (int (listof symbol acyclic) (listof s7-slot acyclic) (listof datum acyclic) (listof s7-raw acyclic)) s7-lambda-frame)
               (lambda (i ps slots bs raws)
                 (cond ((>= i size) (product (frame (reverse slots)) (bindings (reverse bs)) (raws (reverse raws))))
                       ((pair? ps)
                        (if (member? i assigned =)
                            (let ((v (s7-fresh-var cx "v")))
                              (go (+ i 1) (cdr ps) (cons (product (var v) (boxed #t) (direct nil)) slots) (cons (list v (s7-box-datum (car ps))) bs) raws))
                            (go (+ i 1) (cdr ps) (cons (product (var (car ps)) (boxed #f) (direct nil)) slots) bs raws)))
                       (else (let ((v (s7-fresh-var cx "v")))
                               (tagcase (direct-of i directs)
                                 (some l (let ((f (s7-fresh-var cx "f")))
                                           (go (+ i 1) nil (cons (product (var v) (boxed #t) (direct (list (product (fn f) (arity (extract l required)))))) slots)
                                               (cons (list v (s7-box-datum (s7-rt-op 'undef))) bs)
                                               (cons (product (fn f) (lam l)) raws))))
                                 (none u (go (+ i 1) nil (cons (product (var v) (boxed #t) (direct nil)) slots)
                                             (cons (list v (s7-box-datum (s7-rt-op 'undef))) bs) raws)))))))))
      (go 0 params nil nil nil))))
"How many times `i` is in `l`."
(define* s7-count-of (subr spin ((listof int acyclic) int) int)
  (lambda (l i) (letrec ((go (subr spin ((listof int acyclic) int) int)
                               (lambda (l n) (cond ((null? l) n) ((= (car l) i) (go (cdr l) (+ n 1))) (else (go (cdr l) n))))))
                  (go l 0))))
"The slots past the first `from` of the frame `body` begins that `body`
sets once, where it begins (an item of its sequence), to a lambda of one
clause of at most four parameters, and sets nowhere else (`assigned`)."
(define* s7-direct-slots (subr spin (s7-node int (listof int acyclic)) (listof s7-direct-slot acyclic))
  (lambda (body from assigned)
    (letrec ((go (subr spin (s7-nodes (listof s7-direct-slot acyclic)) (listof s7-direct-slot acyclic))
               (lambda (ns acc)
                 (if (null? ns) acc
                     (go (cdr ns)
                         (tagcase (extract (car ns) form)
                           (n-set-local x
                             (tagcase (extract (extract x value) form)
                               (n-lambda ls (if (and (= (extract x depth) 0) (>= (extract x index) from)
                                                     (= (s7-count-of assigned (extract x index)) 1)
                                                     (pair? ls) (null? (cdr ls)) (not (extract (car ls) rest))
                                                     (<= (extract (car ls) required) 4))
                                                (cons (product (index (extract x index)) (lams ls)) acc)
                                                acc))
                               (else y acc)))
                           (else y acc)))))))
      (tagcase (extract body form)
        (n-seq ns (go ns nil))
        (else y (go (list body) nil))))))
"What lowered code's procedures do, as staged code writes it: `s7-eff`."
(define s7-eff-datum datum
  '(maxeff (read @sc) (read @globals) (write @sc) (alloc @sc) (goto @sk) (comefrom @sk) spin
           (io fs-read) (io fs-write) (io clock) (io args) (io process) stage))
"The type of a direct procedure of `n` arguments."
(define* s7-raw-type (subr (maxeff spin (alloc @sc)) (int) datum)
  (lambda (n)
    (letrec ((go (subr (maxeff spin (alloc @sc)) (int (listof datum acyclic)) (listof datum acyclic))
               (lambda (i acc) (if (<= i 0) acc (go (- i 1) (cons '%value acc))))))
      (list 'subr s7-eff-datum (go n nil) '%value))))

(define-rec
  ;; Node `n` lowered, in `frames` (innermost first).
  (s7-lower (subr s7-eff (s7-node s7-lframes s7-lowering) datum)
  (lambda (n frames cx)
    (letrec ((all (subr s7-eff (s7-nodes) (listof datum acyclic))
               (lambda (ns) (if (null? ns) nil (let ((d (s7-lower (car ns) frames cx))) (cons d (all (cdr ns)))))))
             (slot (subr spin (s7-lframes int int) (sumof (none unit) (some s7-slot)))
               (lambda (fs depth index)
                 (cond ((null? fs) (sum none #u))
                       ((> depth 0) (slot (cdr fs) (- depth 1) index))
                       (else (letrec ((at (subr spin (s7-lframe int) (sumof (none unit) (some s7-slot)))
                                        (lambda (l i) (cond ((null? l) (sum none #u)) ((= i 0) (sum some (car l))) (else (at (cdr l) (- i 1)))))))
                               (at (car fs) index)))))))
      (tagcase (extract n form)
        (n-const v (s7-const-var cx v))
        (n-local l (tagcase (slot frames (extract l depth) (extract l index))
                     (some s (if (extract s boxed) (list (s7-rt-op 'lref) (extract s var) (s7-const-var cx (sum sym (extract l name)))) (extract s var)))
                     (none u (list (s7-rt-op 'fail-syntax) "a variable s7st cannot find"))))
        (n-global c (list (s7-rt-op 'gref) (s7-cell-var cx c)))
        (n-set-local x
          (tagcase (slot frames (extract x depth) (extract x index))
            (some s
              (let ((v (tagcase (extract (extract x value) form)
                         ;; A direct procedure's: the one closure of it, made
                         ;; here, where the slot gets it.
                         (n-lambda ls (if (and (pair? (extract s direct)) (= (extract x depth) 0))
                                          (let ((d (car (extract s direct))))
                                            (list (s7-proc-op (extract d arity)) (s7-lams-var cx ls) (extract d fn)))
                                          (s7-lower (extract x value) frames cx)))
                         (else y (s7-lower (extract x value) frames cx)))))
                (list 'begin (list 'set (extract s var) v) (s7-rt-op 'unspec))))
            (none u (list (s7-rt-op 'fail-syntax) "a variable s7st cannot find"))))
        (n-set-global x (let ((v (s7-lower (extract x value) frames cx))) (list (s7-rt-op 'gset!) (s7-cell-var cx (extract x cell)) v)))
        (n-define x (let ((v (s7-lower (extract x value) frames cx))) (list (s7-rt-op 'gdefine!) (s7-cell-var cx (extract x cell)) v)))
        (n-if x (let* ((test (extract x test))
                       ;; A fused test's own, giving a `bool`; else the value, tested.
                       (t (tagcase (extract test form)
                            (n-call c (tagcase (extract (extract c op) form)
                                        (n-global g
                                          (let ((k (list-length (extract c args))))
                                            (tagcase (s7-fused-of g k)
                                              (some f (if (extract f test)
                                                          (cons (s7-rt-op (s7-test-field (extract f field)))
                                                                (cons (s7-cell-var cx g) (all (extract c args))))
                                                          (list (s7-rt-op 'true?) (s7-lower test frames cx))))
                                              (none u (list (s7-rt-op 'true?) (s7-lower test frames cx))))))
                                        (else y (list (s7-rt-op 'true?) (s7-lower test frames cx)))))
                            (else y (list (s7-rt-op 'true?) (s7-lower test frames cx)))))
                       (a (s7-lower (extract x then) frames cx))
                       (b (s7-lower (extract x else) frames cx)))
                  (list 'if t a b)))
        (n-seq ns (cons 'begin (all ns)))
        (n-call x
          (let* ((args (all (extract x args)))
                 (k (list-length args)))
            (tagcase (extract (extract x op) form)
              ;; A lambda called where it is made, with what it takes (a
              ;; `let`, as the expander makes one): its body in a `let` of
              ;; its parameters, no closure made, nor a call.
              (n-lambda ls
                (if (and (pair? ls) (null? (cdr ls)) (not (extract (car ls) rest)) (= (extract (car ls) required) k))
                    (let* ((l (car ls))
                           (ps (s7-fresh-vars cx k)))
                      (s7-let-datum (s7-zip-bindings ps args) (s7-lower-body cx frames ps (extract l size) (extract l body))))
                    (s7-call-datum (s7-lower (extract x op) frames cx) args k)))
              ;; A direct procedure called with as many as it takes.
              (n-local l
                (tagcase (slot frames (extract l depth) (extract l index))
                  (some s (if (and (pair? (extract s direct)) (= (extract (car (extract s direct)) arity) k))
                              (cons (extract (car (extract s direct)) fn) args)
                              (s7-call-datum (s7-lower (extract x op) frames cx) args k)))
                  (none u (s7-call-datum (s7-lower (extract x op) frames cx) args k))))
              (n-global c (s7-global-call cx c args k))
              (else y (s7-call-datum (s7-lower (extract x op) frames cx) args k)))))
        (n-scope x (s7-lower-body cx frames nil (extract x size) (extract x body)))
        (n-lambda ls (s7-lower-lambda ls frames cx))
        (n-fail m (list (s7-rt-op 'fail-syntax) m))))))

  ;; A frame's body lowered, in `frames`: `params` the variables its first
  ;; slots arrive in, `size` its slots; its boxes made, and its direct
  ;; procedures, in a `letrec`, where it begins.
  (s7-lower-body (subr s7-eff (s7-lowering s7-lframes (listof symbol acyclic) int s7-node) datum)
  (lambda (cx frames params size body)
    (let* ((assigned (s7-assigned body 0 nil))
           (fr (s7-frame-of cx params size assigned (s7-direct-slots body (list-length params) assigned)))
           (inner (the s7-lframes (cons (extract fr frame) frames)))
           (raws (letrec ((go (subr s7-eff ((listof s7-raw acyclic)) (listof datum acyclic))
                                (lambda (rs)
                                  (if (null? rs) nil
                                      (let ((l (extract (car rs) lam)))
                                        (cons (list (extract (car rs) fn) (s7-raw-type (extract l required)) (s7-lower-raw l inner cx))
                                              (go (cdr rs))))))))
                   (go (extract fr raws))))
           (lowered (s7-lower body inner cx)))
      (s7-let-datum (extract fr bindings) (if (null? raws) lowered (list 'letrec raws lowered))))))
  ;; Lambda `l` (one clause, its parameters fixed) as an FX-26 procedure.
  (s7-lower-raw (subr s7-eff (s7-lambda s7-lframes s7-lowering) datum)
  (lambda (l frames cx)
    (let ((ps (s7-fresh-vars cx (extract l required))))
      (list 'lambda (map (lambda ((p symbol)) (the datum (list p '%value))) ps)
            (list 'begin (list (s7-rt-op 'tick)) (s7-lower-body cx frames ps (extract l size) (extract l body)))))))

  ;; Lambdas `ls` (a `case-lambda`'s clauses, or one) lowered.
  (s7-lower-lambda (subr s7-eff ((listof s7-lambda acyclic) s7-lframes s7-lowering) datum)
  (lambda (ls frames cx)
    (let ((lv (s7-lams-var cx ls))
          ;; Clause `l`'s body lowered, its parameters arriving in `params`.
          (body-of (lambda ((l s7-lambda) (params (listof symbol acyclic)))
                     (s7-lower-body cx frames params (extract l size) (extract l body))))
          (params (lambda ((n int))
                    (letrec ((go (subr s7-eff (int (listof symbol acyclic)) (listof symbol acyclic))
                               (lambda (i acc) (if (>= i n) (reverse acc) (go (+ i 1) (cons (s7-fresh-var cx "p") acc))))))
                      (go 0 nil)))))
      (if (and (pair? ls) (null? (cdr ls)) (not (extract (car ls) rest)) (<= (extract (car ls) required) 4))
          (let* ((l (car ls)) (ps (params (extract l required))) (body (body-of l ps)))
            (list (s7-proc-op (extract l required)) lv
                  (list 'lambda (map (lambda ((p symbol)) (the datum (list p '%value))) ps)
                        (list 'begin (list (s7-rt-op 'tick)) body))))
          (let ((args (s7-fresh-var cx "as")))
            (letrec ((clauses (subr s7-eff ((listof s7-lambda acyclic)) datum)
                       (lambda (cs)
                         (if (null? cs) (list (s7-rt-op 'no-clause) lv args)
                             (let* ((l (car cs)) (r (extract l required)) (rest (extract l rest))
                                    (ps (params (if rest (+ r 1) r)))
                                    (gets (letrec ((go (subr s7-eff ((listof symbol acyclic) int (listof datum acyclic)) (listof datum acyclic))
                                                         (lambda (ps i acc)
                                                           (cond ((null? ps) (reverse acc))
                                                                 ((< i r) (go (cdr ps) (+ i 1) (cons (list (car ps) (list (s7-rt-op 'arg) args i)) acc)))
                                                                 (else (go (cdr ps) (+ i 1) (cons (list (car ps) (list (s7-rt-op 'args-rest) args r)) acc)))))))
                                            (go ps 0 nil)))
                                    (body (body-of l ps))
                                    (next (clauses (cdr cs))))
                               (list 'if (list (s7-rt-op 'fits?) args r rest) (s7-let-datum gets body) next))))))
              (list (s7-rt-op 'procn) lv (list 'lambda (list (list args '(listof %value acyclic))) (list 'begin (list (s7-rt-op 'tick)) (clauses ls)))))))))))

"The values of list `l`, last first, `n` of them, as an array."
(define* s7-array-of (subr (maxeff spin (alloc @sc) (write @sc)) (s7-values int) (arrayof s7-value @sc))
  (lambda (l n)
    (let ((a (the (arrayof s7-value @sc) (make-array n s7-undefined))))
      (letrec ((fill (subr (maxeff spin (write @sc)) (s7-values int) unit)
                 (lambda (l i) (if (null? l) #u (begin (array-set! a i (car l)) (fill (cdr l) (- i 1)))))))
        (begin (fill l (- n 1)) a)))))
(define s7-no-cell s7-global (s7-new-cell (string->symbol " no cell")))
(define* s7-cell-array (subr (maxeff spin (alloc @sc) (write @sc)) ((listof s7-global acyclic) int) (arrayof s7-global @sc))
  (lambda (l n)
    (let ((a (the (arrayof s7-global @sc) (make-array n s7-no-cell))))
      (letrec ((fill (subr (maxeff spin (write @sc)) ((listof s7-global acyclic) int) unit)
                 (lambda (l i) (if (null? l) #u (begin (array-set! a i (car l)) (fill (cdr l) (- i 1)))))))
        (begin (fill l (- n 1)) a)))))
(define* s7-lams-array (subr (maxeff spin (alloc @sc) (write @sc)) ((listof (listof s7-lambda acyclic) acyclic) int) (arrayof (listof s7-lambda acyclic) @sc))
  (lambda (l n)
    (let ((a (the (arrayof (listof s7-lambda acyclic) @sc) (make-array n (the (listof s7-lambda acyclic) nil)))))
      (letrec ((fill (subr (maxeff spin (write @sc)) ((listof (listof s7-lambda acyclic) acyclic) int) unit)
                 (lambda (l i) (if (null? l) #u (begin (array-set! a i (car l)) (fill (cdr l) (- i 1)))))))
        (begin (fill l (- n 1)) a)))))
;;; ------------------------------------------------------------ staging

(define* s7-interleave (subr spin ((listof string acyclic) string) (listof string acyclic))
  (lambda (l sep) (if (or (null? l) (null? (cdr l))) l (cons (car l) (cons sep (s7-interleave (cdr l) sep))))))
"Datum `d` as text, for saying what code could not be compiled."
(define* s7-datum-text (subr spin (datum) string)
  (lambda (d)
    (typecase d
      (symbol s (symbol->string s))
      (int i (int->string i))
      (string s (string-append "\"" s "\""))
      (bool b (if b "#t" "#f"))
      (nil n "()")
      (pair p
        (letrec ((items (subr spin (datum (listof string acyclic)) (listof string acyclic))
                   (lambda (d acc)
                     (typecase d
                       (nil n (reverse acc))
                       (pair q (items (cdr q) (cons (s7-datum-text (car q)) acc)))
                       (else x (reverse (cons (string-append ". " (s7-datum-text x)) acc)))))))
          (string-append "(" (string-concatenate (s7-interleave (items p nil) " ")) ")")))
      (else x "?"))))

"The tables of the forms being staged (`s7-run-nodes`), which its code takes
as it is made (`%tables`); and the value it gives (`%result!`):
so that the type staged code is checked against is small, naming none of
s7st's types, each of which is printed whole for the check."
(define s7-staged-k (ref (arrayof s7-value @sc) @sc) (new (the (arrayof s7-value @sc) (make-array 0 s7-undefined))))
(define s7-staged-g (ref (arrayof s7-global @sc) @sc) (new (the (arrayof s7-global @sc) (make-array 0 s7-no-cell))))
(define s7-staged-l (ref (arrayof (listof s7-lambda acyclic) @sc) @sc)
  (new (the (arrayof (listof s7-lambda acyclic) @sc) (make-array 0 (the (listof s7-lambda acyclic) nil)))))
(define s7-staged-result (ref s7-value @sc) (new s7-unspecified))
(define* s7-staged-result! (subr s7-eff (s7-value) unit) (lambda (v) (set s7-staged-result v)))
"A top-level form's value `v`, shown as the REPL shows it (if it is shown)."
(define* s7-show! (subr s7-eff (s7-value) s7-value)
  (lambda (v)
    (begin
      (if (s7-shown? v)
          (begin (s7-port-write "" s7-console (s7-string (string-append (s7-fresh-line) (s7-show v #t) "\n"))) #u)
          #u)
      v)))

"What a form's code is given as it is made: its tables (`k`, `g`, `l`), and
what lowered code runs on (machine.fx's), as it names them."
(define-type s7-tables (productof (k (arrayof s7-value @sc)) (g (arrayof s7-global @sc)) (l (arrayof (listof s7-lambda acyclic) @sc)) (call0 (subr s7-eff (s7-value) s7-value)) (call1 (subr s7-eff (s7-value s7-value) s7-value)) (call2 (subr s7-eff (s7-value s7-value s7-value) s7-value)) (call3 (subr s7-eff (s7-value s7-value s7-value s7-value) s7-value)) (call4 (subr s7-eff (s7-value s7-value s7-value s7-value s7-value) s7-value)) (calln (subr s7-eff (s7-value (listof s7-value acyclic)) s7-value)) (proc0 (subr s7-eff ((listof s7-lambda acyclic) (subr s7-eff () s7-value)) s7-value)) (proc1 (subr s7-eff ((listof s7-lambda acyclic) (subr s7-eff (s7-value) s7-value)) s7-value)) (proc2 (subr s7-eff ((listof s7-lambda acyclic) (subr s7-eff (s7-value s7-value) s7-value)) s7-value)) (proc3 (subr s7-eff ((listof s7-lambda acyclic) (subr s7-eff (s7-value s7-value s7-value) s7-value)) s7-value)) (proc4 (subr s7-eff ((listof s7-lambda acyclic) (subr s7-eff (s7-value s7-value s7-value s7-value) s7-value)) s7-value)) (procn (subr s7-eff ((listof s7-lambda acyclic) (subr s7-eff ((listof s7-value acyclic)) s7-value)) s7-value)) (fits? (subr s7-eff ((listof s7-value acyclic) int bool) bool)) (arg (subr s7-eff ((listof s7-value acyclic) int) s7-value)) (args-rest (subr s7-eff ((listof s7-value acyclic) int) s7-value)) (no-clause (subr s7-eff ((listof s7-lambda acyclic) (listof s7-value acyclic)) s7-value)) (gref (subr s7-eff (s7-global) s7-value)) (gset! (subr s7-eff (s7-global s7-value) s7-value)) (gdefine! (subr s7-eff (s7-global s7-value) s7-value)) (lref (subr s7-eff ((ref s7-value @sc) s7-value) s7-value)) (true? (subr pure (s7-value) bool)) (fail-syntax (subr s7-eff (string) s7-value)) (tick (subr s7-eff () unit)) (unspec s7-value) (undef s7-value) (result! (subr s7-eff (s7-value) unit)) (show! (subr s7-eff (s7-value) s7-value)) (add (subr s7-eff (s7-global s7-value s7-value) s7-value)) (sub (subr s7-eff (s7-global s7-value s7-value) s7-value)) (mul (subr s7-eff (s7-global s7-value s7-value) s7-value)) (lt (subr s7-eff (s7-global s7-value s7-value) s7-value)) (lt? (subr s7-eff (s7-global s7-value s7-value) bool)) (gt (subr s7-eff (s7-global s7-value s7-value) s7-value)) (gt? (subr s7-eff (s7-global s7-value s7-value) bool)) (le (subr s7-eff (s7-global s7-value s7-value) s7-value)) (le? (subr s7-eff (s7-global s7-value s7-value) bool)) (ge (subr s7-eff (s7-global s7-value s7-value) s7-value)) (ge? (subr s7-eff (s7-global s7-value s7-value) bool)) (num= (subr s7-eff (s7-global s7-value s7-value) s7-value)) (num=? (subr s7-eff (s7-global s7-value s7-value) bool)) (car (subr s7-eff (s7-global s7-value) s7-value)) (cdr (subr s7-eff (s7-global s7-value) s7-value)) (null (subr s7-eff (s7-global s7-value) s7-value)) (null? (subr s7-eff (s7-global s7-value) bool)) (pair (subr s7-eff (s7-global s7-value) s7-value)) (pair? (subr s7-eff (s7-global s7-value) bool)) (not (subr s7-eff (s7-global s7-value) s7-value)) (not? (subr s7-eff (s7-global s7-value) bool)) (zero (subr s7-eff (s7-global s7-value) s7-value)) (zero? (subr s7-eff (s7-global s7-value) bool)) (eq (subr s7-eff (s7-global s7-value s7-value) s7-value)) (eq? (subr s7-eff (s7-global s7-value s7-value) bool)) (cons (subr s7-eff (s7-global s7-value s7-value) s7-value)) (gcall0 (subr s7-eff (s7-global) s7-value)) (gcall1 (subr s7-eff (s7-global s7-value) s7-value)) (gcall2 (subr s7-eff (s7-global s7-value s7-value) s7-value)) (gcall3 (subr s7-eff (s7-global s7-value s7-value s7-value) s7-value)) (gcall4 (subr s7-eff (s7-global s7-value s7-value s7-value s7-value) s7-value))))
(define* s7-staged-tables (subr s7-eff () s7-tables)
  (lambda () (product (k (get s7-staged-k)) (g (get s7-staged-g)) (l (get s7-staged-l)) (call0 s7-call0) (call1 s7-call1) (call2 s7-call2) (call3 s7-call3) (call4 s7-call4) (calln s7-calln) (proc0 s7-make-proc0) (proc1 s7-make-proc1) (proc2 s7-make-proc2) (proc3 s7-make-proc3) (proc4 s7-make-proc4) (procn s7-make-procn) (fits? s7-args-fit?) (arg s7-arg) (args-rest s7-args-rest) (no-clause s7-no-clause) (gref s7-global-ref) (gset! s7-global-set!) (gdefine! s7-global-define!) (lref s7-local-ref) (true? s7-true?) (fail-syntax s7-fail-syntax) (tick s7-tick!) (unspec s7-unspecified) (undef s7-undefined) (result! s7-staged-result!) (show! s7-show!) (add s7-fadd) (sub s7-fsub) (mul s7-fmul) (lt s7-flt) (lt? s7-flt?) (gt s7-fgt) (gt? s7-fgt?) (le s7-fle) (le? s7-fle?) (ge s7-fge) (ge? s7-fge?) (num= s7-fnum=) (num=? s7-fnum=?) (car s7-fcar) (cdr s7-fcdr) (null s7-fnull) (null? s7-fnull?) (pair s7-fpair) (pair? s7-fpair?) (not s7-fnot) (not? s7-fnot?) (zero s7-fzero) (zero? s7-fzero?) (eq s7-feq) (eq? s7-feq?) (cons s7-fcons) (gcall0 s7-gcall0) (gcall1 s7-gcall1) (gcall2 s7-gcall2) (gcall3 s7-gcall3) (gcall4 s7-gcall4))))

"What lowered code may name (machine.fx's), as it names it: sealed, its
types abstract, so that what staged code is checked against is small (a
type is printed whole for the check: `s7-value`'s is some 20 KB)."
(define-effect s7-rt-eff (maxeff s7-eff))
(define s7-rt
  (the (moduleof (abs %value type) (abs %global type) (abs %lams type)
                 (val %tables (subr s7-rt-eff () (productof (k (arrayof %value @sc)) (g (arrayof %global @sc)) (l (arrayof %lams @sc)) (call0 (subr s7-rt-eff (%value) %value)) (call1 (subr s7-rt-eff (%value %value) %value)) (call2 (subr s7-rt-eff (%value %value %value) %value)) (call3 (subr s7-rt-eff (%value %value %value %value) %value)) (call4 (subr s7-rt-eff (%value %value %value %value %value) %value)) (calln (subr s7-rt-eff (%value (listof %value acyclic)) %value)) (proc0 (subr s7-rt-eff (%lams (subr s7-rt-eff () %value)) %value)) (proc1 (subr s7-rt-eff (%lams (subr s7-rt-eff (%value) %value)) %value)) (proc2 (subr s7-rt-eff (%lams (subr s7-rt-eff (%value %value) %value)) %value)) (proc3 (subr s7-rt-eff (%lams (subr s7-rt-eff (%value %value %value) %value)) %value)) (proc4 (subr s7-rt-eff (%lams (subr s7-rt-eff (%value %value %value %value) %value)) %value)) (procn (subr s7-rt-eff (%lams (subr s7-rt-eff ((listof %value acyclic)) %value)) %value)) (fits? (subr s7-rt-eff ((listof %value acyclic) int bool) bool)) (arg (subr s7-rt-eff ((listof %value acyclic) int) %value)) (args-rest (subr s7-rt-eff ((listof %value acyclic) int) %value)) (no-clause (subr s7-rt-eff (%lams (listof %value acyclic)) %value)) (gref (subr s7-rt-eff (%global) %value)) (gset! (subr s7-rt-eff (%global %value) %value)) (gdefine! (subr s7-rt-eff (%global %value) %value)) (lref (subr s7-rt-eff ((ref %value @sc) %value) %value)) (true? (subr pure (%value) bool)) (fail-syntax (subr s7-rt-eff (string) %value)) (tick (subr s7-rt-eff () unit)) (unspec %value) (undef %value) (result! (subr s7-rt-eff (%value) unit)) (show! (subr s7-rt-eff (%value) %value)) (add (subr s7-rt-eff (%global %value %value) %value)) (sub (subr s7-rt-eff (%global %value %value) %value)) (mul (subr s7-rt-eff (%global %value %value) %value)) (lt (subr s7-rt-eff (%global %value %value) %value)) (lt? (subr s7-rt-eff (%global %value %value) bool)) (gt (subr s7-rt-eff (%global %value %value) %value)) (gt? (subr s7-rt-eff (%global %value %value) bool)) (le (subr s7-rt-eff (%global %value %value) %value)) (le? (subr s7-rt-eff (%global %value %value) bool)) (ge (subr s7-rt-eff (%global %value %value) %value)) (ge? (subr s7-rt-eff (%global %value %value) bool)) (num= (subr s7-rt-eff (%global %value %value) %value)) (num=? (subr s7-rt-eff (%global %value %value) bool)) (car (subr s7-rt-eff (%global %value) %value)) (cdr (subr s7-rt-eff (%global %value) %value)) (null (subr s7-rt-eff (%global %value) %value)) (null? (subr s7-rt-eff (%global %value) bool)) (pair (subr s7-rt-eff (%global %value) %value)) (pair? (subr s7-rt-eff (%global %value) bool)) (not (subr s7-rt-eff (%global %value) %value)) (not? (subr s7-rt-eff (%global %value) bool)) (zero (subr s7-rt-eff (%global %value) %value)) (zero? (subr s7-rt-eff (%global %value) bool)) (eq (subr s7-rt-eff (%global %value %value) %value)) (eq? (subr s7-rt-eff (%global %value %value) bool)) (cons (subr s7-rt-eff (%global %value %value) %value)) (gcall0 (subr s7-rt-eff (%global) %value)) (gcall1 (subr s7-rt-eff (%global %value) %value)) (gcall2 (subr s7-rt-eff (%global %value %value) %value)) (gcall3 (subr s7-rt-eff (%global %value %value %value) %value)) (gcall4 (subr s7-rt-eff (%global %value %value %value %value) %value))))))
    (module
      (define-type %value s7-value)
      (define-type %global s7-global)
      (define-type %lams (listof s7-lambda acyclic))
      (define %tables s7-staged-tables))))
"What a form's code is, staged: what, given its tables, makes its thunk."
(define-type s7-made (subr s7-eff () (subr s7-eff () unit)))

"Top-level forms `ns` (core), lowered together, staged and run, in order,
each value shown as the REPL shows it if `echo`: the last's value. One
stage for many forms, since a stage's cost is mostly its own, not its
code's (some 8 ms, against a quarter of one a definition)."
(define* s7-run-nodes (subr s7-eff (s7-nodes bool) s7-value)
  (lambda (ns echo)
    (let* ((cx (s7-new-lowering))
           (body (cons 'begin
                       (letrec ((go (subr s7-eff (s7-nodes) (listof datum acyclic))
                                  (lambda (ns)
                                    (if (null? ns) nil
                                        (let ((d (s7-lower (car ns) nil cx)))
                                          (cons (if echo (list (s7-rt-op 'show!) d) d) (go (cdr ns))))))))
                         (go ns))))
           (nk (get (extract cx nconsts))) (ng (get (extract cx ncells))) (nl (get (extract cx nlams)))
           (code (the datum (list 'lambda '()
                                  (list 'let '((T (%tables)))
                                        (list 'lambda '() (list (s7-rt-op 'result!) body)))))))
      (stage s7-rt pure s7-made code
        (p (begin
             (set s7-staged-k (s7-array-of (get (extract cx consts)) nk))
             (set s7-staged-g (s7-cell-array (get (extract cx cells)) ng))
             (set s7-staged-l (s7-lams-array (get (extract cx lams)) nl))
             (let ((run ((p))))
               (begin (run) (get s7-staged-result)))))
        (why (s7-error (string-append "s7st cannot compile this: " (extract why message) " in " (s7-datum-text code)) nil))))))

;;; ------------------------------------------------------------ top level

(define-rec
  ;; Library `name` (missing) loaded from its file; or the error why not.
  (s7-load-library! (subr s7-eff (s7-value) unit)
  (lambda (name)
    (tagcase (s7-library-file name)
      (none u (begin (s7-raise (s7-syntax-error (string-append "no library named " (s7-library-name name)
                                                               ", and no file " (s7-library-relative-file name) " where libraries are looked for"))
                               #f)
                #u))
      (found f
        (if (member? (extract f path) (get s7-library-files) string=?)
            (begin (s7-raise (s7-syntax-error (string-append (extract f path) " does not define " (s7-library-name name))) #f) #u)
            (begin
              (set s7-library-files (cons (extract f path) (get s7-library-files)))
              (s7-add-library-directory! (extract f root))
              (tagcase (s7-read-all (extract f text) (extract f path))
                (data fs (begin (s7-run-forms fs #f (extract f text) s7-toplevel) #u))
                (stop r (begin (s7-raise (sum errobj (product (kind 'read) (message (string-append "cannot read " (extract f path))) (irritants s7-nil)))
                                         #f)
                          #u)))))))))

  ;; Top-level forms `forms` run in namespace `ns`, from `text` (for where an
  ;; error is), each value shown if `echo`: the last's value. An `import` or a
  ;; `define-library` is done here, a library it names not yet defined loaded
  ;; first; anything else is expanded and run, or, if it has syntax errors,
  ;; the first raised.
  (s7-run-forms (subr s7-eff (s7-values bool string s7-ns) s7-value)
  (lambda (forms echo text ns)
    (letrec ((kind-of (subr s7-eff (s7-value) symbol)
               (lambda (x) (tagcase (s7-head-kind x nil) (b-special s s) (else y (string->symbol " none")))))
             ;; An `import` or a `define-library`, done here.
             (declare (subr s7-eff (s7-value symbol) s7-value)
               (lambda (x kind)
                 (begin
                   (set s7-current-ns ns)
                   (if (eq? kind 'import)
                       (tagcase (s7-import-sets (s7-value->values (s7-cdr x)))
                         (bindings bs (begin (s7-bind-all! ns bs) s7-unspecified))
                         (plain u s7-unspecified)
                         (missing name (begin (s7-load-library! name) (declare x kind)))
                         (bad m (s7-raise (s7-syntax-error (string-append "import: " m)) #f)))
                       (let* ((name (s7-cadr x))
                              (decls (s7-library-decls (s7-value->values (s7-cddr x)))))
                         (tagcase (s7-import-sets (s7-decl-items decls "import"))
                           (missing m (begin (s7-load-library! m) (declare x kind)))
                           (bad m (s7-raise (s7-syntax-error (string-append "define-library: " m)) #f))
                           (else imported
                             (let ((lib (s7-make-ns (s7-library-name name) 256 (list s7-builtins))))
                               (begin
                                 (tagcase imported (bindings bs (s7-bind-all! lib bs)) (else y #u))
                                 (s7-register-library! (product (name (s7-library-name name)) (ns lib)
                                                                (exports (s7-exports-of (s7-decl-items decls "export")))))
                                 (s7-run-forms (s7-library-body decls) #f text lib)
                                 (set s7-current-ns ns)
                                 s7-unspecified)))))))))
             ;; Whether form `x` may make what the forms after it are
             ;; expanded by (`load`, `eval`): the batch ends after it.
             (ends-batch? (subr s7-eff (s7-value) bool)
               (lambda (x)
                 (tagcase x
                   (pair p (tagcase (get (extract p car))
                             (sym s (let ((n (s7-unrename s))) (or (eq? n 'load) (eq? n 'eval))))
                             (else y #f)))
                   (else y #f))))
             ;; The forms from `fs` expanded, last first onto `acc`, `n` of
             ;; them, while they are neither declarations nor wrong, at most
             ;; 100; then run, and the error of the one that stopped them
             ;; raised, if one did; then the rest.
             (batch (subr s7-eff (s7-values s7-nodes int s7-value) s7-value)
               (lambda (fs acc n last)
                 (let ((run (lambda ((more s7-values))
                              (let ((v (if (null? acc) last (s7-run-nodes (reverse acc) echo))))
                                (go more v)))))
                   (if (or (null? fs) (>= n 100)
                           (let ((k (kind-of (car fs)))) (or (eq? k 'import) (eq? k 'define-library))))
                       (run fs)
                       (begin
                         (set s7-current-ns ns)
                         (set s7-syntax-errors nil)
                         (let* ((node (s7-expand-top (car fs)))
                                (errors (reverse (get s7-syntax-errors))))
                           (cond
                             ((pair? errors)
                              (begin
                                (if (null? acc) s7-unspecified (s7-run-nodes (reverse acc) echo))
                                (s7-raise (s7-syntax-error (string-append (s7-where (extract (car errors) span) text)
                                                                          (extract (car errors) message)))
                                          #f)))
                             ((ends-batch? (car fs))
                              (let ((v (s7-run-nodes (reverse (cons node acc)) echo)))
                                (go (cdr fs) v)))
                             (else (batch (cdr fs) (cons node acc) (+ n 1) last)))))))))
             (go (subr s7-eff (s7-values s7-value) s7-value)
               (lambda (fs last)
                 (cond ((null? fs) last)
                       ((let ((k (kind-of (car fs)))) (or (eq? k 'import) (eq? k 'define-library)))
                        (go (cdr fs) (declare (car fs) (kind-of (car fs)))))
                       (else (batch fs nil 0 last))))))
      (go forms s7-unspecified)))))

"How a run ended, or was paused: its value, the condition that stopped
it, or the rest of it to run."
(define-type s7-outcome (sumof (done s7-value) (failed s7-value) (paused s7-thunk)))
(define s7-stopped (ref (listof s7-outcome acyclic) @sc) (new nil))
"`thunk` run in a run's prompt: a continuation resumed (an abort to it
with code to run), in a prompt again; else how it stopped kept."
(define* s7-run-in (subr s7-eff (s7-thunk) s7-value)
  (lambda (thunk)
    (prompt s7-tag (thunk)
      (lambda ((j s7-jump))
        (tagcase j
          (go t (s7-run-in t))
          (pause t (begin (set s7-stopped (list (sum paused t))) s7-unspecified))
          (fail obj (begin (set s7-stopped (list (sum failed obj))) s7-unspecified))
          (exit v (begin (set s7-stopped (list (sum done v))) s7-unspecified)))))))
"`thunk` run, at most `fuel` procedures entered: how it ended, or the rest
of it."
(define* s7-drive-run (subr s7-eff (s7-thunk int) s7-outcome)
  (lambda (thunk fuel)
    (begin
      (set s7-fuel fuel)
      (set s7-stopped nil)
      (let* ((v (s7-run-in thunk)) (st (get s7-stopped)))
        (if (pair? st) (car st) (sum done v))))))

"`eval` and `load`, which run top-level forms."
(define* s7-init-eval! (subr s7-eff () unit)
  (lambda ()
    (begin
      (s7-prim! "eval" 1 2
        (lambda ((a s7-values))
          (sum ok (s7-run-forms (list (car a)) #f "" (tagcase (s7-arg2 a) (env n n) (else y (get s7-current-ns)))))))
      (s7-prim! "load" 1 2
        (lambda ((a s7-values))
          (tagcase (car a)
            (str s (tagcase (s7-file-text (get s))
                     (text t (tagcase (s7-read-all t (get s))
                               (data forms (sum ok (s7-run-forms forms #f t (tagcase (s7-arg2 a) (env n n) (else y s7-toplevel)))))
                               (stop r (sum raise (sum errobj (product (kind 'read) (message (string-append "load: cannot read " (get s)))
                                                                       (irritants s7-nil)))))))
                     (failed m (sum raise (sum errobj (product (kind 'file) (message (string-append "load: " m)) (irritants s7-nil)))))))
            (else y (s7-fail "load: not a file name" (list y)))))))))
