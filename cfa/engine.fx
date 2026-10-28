;;; engine.fx: the analysis -- m-CFA (Might, Smaragdakis and Van Horn, PLDI
;;; 2010) over the core (core.fx), as yank's `cfa.sld` does it, run a slice
;;; at a time.
;;;
;;; A contour is the last `m` call sites, newest first; a closure is a
;;; lambda and the contour it was made in; a call gives the callee the
;;; contour of the call site pushed onto the caller's, cut to `m`, and
;;; copies the lambda's free variables into it from the closure's. Locals
;;; are addressed by variable and contour; globals and allocation sites
;;; have one address each. At depth 0 every contour is the empty one: 0CFA.
;;;
;;; A task is a closure whose body is to be evaluated in its contour, or the
;;; top level (`cf-main`). Each cell keeps the tasks that read it; a cell
;;; that grows puts them on the worklist again, so a task runs again only
;;; when something it read changed. `cf-step!` runs tasks until its fuel is
;;; spent or none is left: the server answers requests between slices.
;;;
;;; An abstract value is a number: closure `c` as 4c, allocation site `s`
;;; as 4s+1, data of kind `k` as 4k+2, primitive `p` as 4p+3, and unknown
;;; (whatever code not known may give) as -1. A set of them: a sorted list.

(define-type vals (listof int acyclic))
(define cf-unknown int -1)

(define* vals-union (subr spin (vals vals) vals)
  (lambda (a b)
    (cond ((null? a) b)
          ((null? b) a)
          ((< (car a) (car b)) (cons (car a) (vals-union (cdr a) b)))
          ((< (car b) (car a)) (cons (car b) (vals-union a (cdr b))))
          (else (cons (car a) (vals-union (cdr a) (cdr b)))))))
(define* vals-has? (subr spin (vals int) bool)
  (lambda (s x) (and (pair? s) (or (= (car s) x) (and (< (car s) x) (vals-has? (cdr s) x))))))
(define* union-all (subr spin ((listof vals acyclic)) vals)
  (lambda (l) (if (null? l) nil (vals-union (car l) (union-all (cdr l))))))
(define* last-vals (subr spin ((listof vals acyclic)) vals)
  (lambda (l) (cond ((null? l) nil) ((null? (cdr l)) (car l)) (else (last-vals (cdr l))))))
(define* append-ints (subr spin (ints ints) ints) (lambda (a b) (if (null? a) b (cons (car a) (append-ints (cdr a) b)))))
(define* member-int? (subr spin (int ints) bool) (lambda (x l) (and (pair? l) (or (= (car l) x) (member-int? x (cdr l))))))
(define* closure-val? (subr pure (int) bool) (lambda (x) (and (>= x 0) (= (remainder x 4) 0))))
(define* site-val? (subr pure (int) bool) (lambda (x) (and (>= x 0) (= (remainder x 4) 1))))
(define* kind-val? (subr pure (int) bool) (lambda (x) (and (>= x 0) (= (remainder x 4) 2))))
(define* prim-val? (subr pure (int) bool) (lambda (x) (and (>= x 0) (= (remainder x 4) 3))))

(define* int-hash (subr pure (int) int) (lambda (k) (remainder (* (if (< k 0) (- 0 k) k) 2654435761) 2147483647)))
(define* int-same (subr pure (int int) bool) (lambda (a b) (= a b)))
(define-type int-table (table int int @cf))
(define-type vals-table (table int vals @cf))
(define-type ints-table (table int ints @cf))
(define* new-int-table (subr (alloc @cf) () int-table) (lambda () (make-table int-hash int-same)))
(define* new-vals-table (subr (alloc @cf) () vals-table) (lambda () (make-table int-hash int-same)))
(define* new-ints-table (subr (alloc @cf) () ints-table) (lambda () (make-table int-hash int-same)))

"The world being analysed: its lambdas and sites by number, the variables
the lambdas' bodies use but do not bind, and its language."
(define cf-lambda-array (ref (arrayof lambda-info @cf) @cf)
  (new (make-array 0 (product (span cf-no-span) (name "") (params nil) (rest -1) (body (k-none nil))))))
(define cf-site-array (ref (arrayof site-info @cf) @cf) (new (make-array 0 (product (span cf-no-span) (kind "") (tag "")))))
(define cf-free (ref (arrayof ints @cf) @cf) (new (make-array 0 nil)))
(define cf-tops (ref cores @cf) (new nil))
(define cf-language (ref cf-lang @cf) (new (product (name "") (model (lambda ((n string)) (m-data #f nil))))))
"The analysis's depth: how many call sites a contour keeps (0: 0CFA)."
(define cf-depth (ref int @cf) (new 0))

;; Contours and closures, interned.
(define cf-contour-ids (ref int-table @cf) (new (new-int-table)))
(define cf-contour-calls (ref ints-table @cf) (new (new-ints-table)))
(define cf-contour-count (ref int @cf) (new 1))
(define cf-closure-ids (ref int-table @cf) (new (new-int-table)))
(define cf-closure-lambda (ref int-table @cf) (new (new-int-table)))
(define cf-closure-contour (ref int-table @cf) (new (new-int-table)))
(define cf-closure-count (ref int @cf) (new 0))
;; Primitives and field labels, interned.
(define cf-prims (ref strings @cf) (new nil))     ; newest first
(define cf-prim-count (ref int @cf) (new 0))
(define cf-labels (ref (table string int @cf) @cf) (new (the (table string int @cf) (make-table string-hash string=?))))
(define cf-label-count (ref int @cf) (new 0))

;; The store: each cell's values, and the tasks that read it.
(define cf-cells (ref vals-table @cf) (new (new-vals-table)))
(define cf-readers (ref ints-table @cf) (new (new-ints-table)))
;; What the notes need: each reference's values and each call's callees,
;; over all contours; which lambdas and sites escaped; each site's labels.
(define cf-ref-vals (ref vals-table @cf) (new (new-vals-table)))
(define cf-callees (ref vals-table @cf) (new (new-vals-table)))
(define cf-escaped (ref int-table @cf) (new (new-int-table)))
(define cf-site-escaped (ref int-table @cf) (new (new-int-table)))
(define cf-site-labels (ref ints-table @cf) (new (new-ints-table)))

;; The worklist: tasks to run, oldest first (`front`, then `back` reversed),
;; those on it, and those ever made. The task running, whose reads are kept.
(define cf-main int -1)
(define cf-front (ref ints @cf) (new nil))
(define cf-back (ref ints @cf) (new nil))
(define cf-queued (ref int-table @cf) (new (new-int-table)))
(define cf-made (ref int-table @cf) (new (new-int-table)))
(define cf-current (ref int @cf) (new -1))
"How many tasks have run, in all."
(define cf-steps (ref int @cf) (new 0))

"How much the analysis holds, for its progress (`cf-status`): tasks on
the worklist; values in all cells together (facts); cells."
(define cf-queue-length (ref int @cf) (new 0))
(define cf-facts (ref int @cf) (new 0))
(define cf-cell-count (ref int @cf) (new 0))
(define* cf-enqueue! (subr cf-eff (int) unit)
  (lambda (t)
    (if (= (table-ref (get cf-queued) t 0) 1) #u
        (begin (table-set! (get cf-queued) t 1) (set cf-back (cons t (get cf-back)))
          (set cf-queue-length (+ (get cf-queue-length) 1))))))
"Task `t` made: on the worklist, the first time."
(define* cf-ensure-task! (subr cf-eff (int) unit)
  (lambda (t)
    (if (= (table-ref (get cf-made) t 0) 1) #u
        (begin (table-set! (get cf-made) t 1) (cf-enqueue! t)))))

;;; ------------------------------------------------------------ cells

"Cell keys: variable `v` in contour `c`, a site's field, a task's result."
(define* var-key (subr cf-eff (int int) int)
  (lambda (v c) (* 4 (+ (* v 16777216) (if (< v (get cf-global-count)) 0 c)))))
(define* field-key (subr pure (int int) int) (lambda (site label) (+ 1 (* 4 (+ (* site 16777216) label)))))
(define* result-key (subr pure (int) int) (lambda (task) (+ 2 (* 4 (+ task 1)))))

(define* cf-read (subr cf-eff (int) vals)
  (lambda (k)
    (let ((rs (table-ref (get cf-readers) k nil)) (t (get cf-current)))
      (begin
        (if (and (pair? rs) (= (car rs) t)) #u
            (if (letrec ((has (subr spin (ints) bool) (lambda (l) (and (pair? l) (or (= (car l) t) (has (cdr l)))))))
                  (has rs))
                #u
                (table-set! (get cf-readers) k (cons t rs))))
        (table-ref (get cf-cells) k nil)))))
"Cell `k` given `s` too: its readers to run again, if it grew."
(define* widen-to (subr (maxeff spin (read @cf)) (int) int)
  (lambda (k) (letrec ((go (subr spin ((listof (productof (kind int) (to int)) acyclic)) int)
                         (lambda (l) (cond ((null? l) -1) ((= (extract (car l) kind) k) (extract (car l) to)) (else (go (cdr l)))))))
                (go (get cf-widen)))))
"`s`, its kinds widened where too many of one widening are in it; and,
so that a cell only grows, a kind its widening is in already absorbed by
it (once a cell holds `symbol`, `'x` joining it changes nothing)."
(define* widen (subr cf-eff (vals) vals)
  (lambda (s)
    (if (null? (get cf-widen)) s
        (let ((wide (letrec ((go (subr cf-eff (vals int) int)
                               (lambda (l n) (cond ((null? l) n)
                                                   ((and (kind-val? (car l)) (>= (widen-to (quotient (car l) 4)) 0))
                                                    (go (cdr l) (if (vals-has? s (+ 2 (* 4 (widen-to (quotient (car l) 4))))) 9 (+ n 1))))
                                                   (else (go (cdr l) n))))))
                      (go s 0))))
          (if (<= wide 8) s
              (letrec ((go (subr cf-eff (vals) vals)
                         (lambda (s) (cond ((null? s) nil)
                                           ((and (kind-val? (car s)) (>= (widen-to (quotient (car s) 4)) 0))
                                            (vals-union (list (+ 2 (* 4 (widen-to (quotient (car s) 4))))) (go (cdr s))))
                                           (else (vals-union (list (car s)) (go (cdr s))))))))
                (go s)))))))
"Sites dropped from a cell that holds unknown, to escape once the task
that dropped them is done (`collapse`)."
(define cf-to-escape (ref vals @cf) (new nil))
"`s`, if it holds unknown, without its sites (yank's collapse, which keeps
only procedures; kinds kept here too, as they cost nothing to carry and
say what is known): a site with unknown is what code not known may give
anyway, so it escapes (later): what it holds is anything too, and what is
put in it escapes. Off unless asked for (`--collapse`): measured on the
editor's world it made 27 more notes hold unknown, for no time saved;
yank needed it on worlds that did not finish without it."
(define cf-collapse (ref bool @cf) (new #f))
(define* collapse (subr cf-eff (vals) vals)
  (lambda (s)
    (if (or (not (get cf-collapse)) (not (vals-has? s cf-unknown))) s
        (letrec ((go (subr cf-eff (vals) vals)
                   (lambda (l) (cond ((null? l) nil)
                                     ((site-val? (car l)) (begin (set cf-to-escape (cons (car l) (get cf-to-escape))) (go (cdr l))))
                                     (else (cons (car l) (go (cdr l))))))))
          (go s)))))
"The first cells to come to hold unknown, said: where unknown came from."
(define cf-unknown-firsts (ref strings @cf) (new nil))
(define* cf-unknown-event (subr cf-eff (int) string)
  (lambda (k)
    (let* ((space (remainder k 4)) (body (quotient k 4))
           (task (get cf-current))
           (where (if (< task 0) "top level"
                      (let ((l (if (< task (array-length (get cf-lambda-array))) task (table-ref (get cf-closure-lambda) task 0))))
                        (extract (array-ref (get cf-lambda-array) l) name)))))
      (string-append (cond ((= space 0) (let ((v (quotient body 16777216)))
                                          (string-append "variable " (int->string v) (if (< v (get cf-global-count)) " (global)" ""))))
                           ((= space 1) (let ((site (quotient body 16777216)))
                                          (string-append "field of " (extract (array-ref (get cf-site-array) site) kind) " site "
                                                         (int->string (extract (extract (array-ref (get cf-site-array) site) span) start)))))
                           (else "a result"))
                     " in " where))))
(define* cf-join! (subr cf-eff (int vals) unit)
  (lambda (k s)
    (if (null? s) #u
        (let* ((old (table-ref (get cf-cells) k nil)) (new (collapse (widen (vals-union old s)))))
          (if (= (length new) (length old)) #u
              (begin
                (if (and (vals-has? new cf-unknown) (not (vals-has? old cf-unknown)) (< (length (get cf-unknown-firsts)) 12))
                    (set cf-unknown-firsts (append (get cf-unknown-firsts) (list (cf-unknown-event k)))) #u)
                (set cf-facts (+ (get cf-facts) (- (length new) (length old))))
                (if (null? old) (set cf-cell-count (+ (get cf-cell-count) 1)) #u)
                (table-set! (get cf-cells) k new)
                (letrec ((go (subr cf-eff (ints) unit) (lambda (l) (if (null? l) #u (begin (cf-enqueue! (car l)) (go (cdr l)))))))
                  (go (table-ref (get cf-readers) k nil)))))))))
"A table of sets, `k`'s given `s` too (no readers: for the notes)."
(define* cf-note! (subr cf-eff (vals-table int vals) unit)
  (lambda (tbl k s) (if (null? s) #u (table-set! tbl k (vals-union (table-ref tbl k nil) s)))))

;;; ------------------------------------------------------------ interning

(define* pair-key (subr pure (int int) int) (lambda (a b) (+ (* a 16777216) b)))

;;; ------------------------------------------------------------ narrowing

"The narrowings of the branches being evaluated, innermost first."
(define cf-refine (ref (listof cf-narrowing acyclic) @cf) (new nil))
"The classes value `x` is of (`cf-narrowing`)."
(define* val-classes (subr cf-eff (int) strings)
  (lambda (x)
    (cond ((or (closure-val? x) (prim-val? x)) (list "procedure"))
          ((kind-val? x) (let ((n (cf-kind-name (quotient x 4))))
                           (if (and (> (string-length n) 1) (char=? (string-ref n 0) #\')) (list n "symbol") (list n))))
          ((site-val? x) (let ((info (array-ref (get cf-site-array) (quotient x 4))))
                           (if (string=? (extract info kind) "record")
                               (list "record" (string-append "record:" (extract info tag)))
                               (list (extract info kind)))))
          (else nil))))
"Whether kind `k` is what a kind named in `classes` widens to."
(define* widened-in? (subr cf-eff (int strings) bool)
  (lambda (k classes)
    (letrec ((go (subr cf-eff ((listof (productof (kind int) (to int)) acyclic)) bool)
               (lambda (l) (and (pair? l) (or (and (= (extract (car l) to) k) (cf-member? (cf-kind-name (extract (car l) kind)) classes))
                                              (go (cdr l)))))))
      (go (get cf-widen)))))
(define* any-member? (subr spin (strings strings) bool)
  (lambda (a b) (and (pair? a) (or (cf-member? (car a) b) (any-member? (cdr a) b)))))
"Values `s` of variable `v`'s field `path` (nil: the variable's own), as
the branches being evaluated narrow it."
(define* same-path? (subr spin (strings strings) bool)
  (lambda (a b) (cond ((null? a) (null? b)) ((null? b) #f) (else (and (string=? (car a) (car b)) (same-path? (cdr a) (cdr b)))))))
(define* narrow (subr cf-eff (int strings vals) vals)
  (lambda (v path s)
    (letrec ((apply-one (subr cf-eff (cf-narrowing vals) vals)
               (lambda (n s)
                 (cond ((null? s) nil)
                       ((= (car s) cf-unknown) (cons (car s) (apply-one n (cdr s))))
                       ((eq? (any-member? (val-classes (car s)) (extract n classes)) (extract n keep))
                        (cons (car s) (apply-one n (cdr s))))
                       ;; A widened kind (`symbol`) may be any it widened (`'add`):
                       ;; kept where one of those is.
                       ((and (extract n keep) (kind-val? (car s)) (widened-in? (quotient (car s) 4) (extract n classes)))
                        (cons (car s) (apply-one n (cdr s))))
                       (else (apply-one n (cdr s))))))
             (go (subr cf-eff ((listof cf-narrowing acyclic) vals) vals)
               (lambda (ns s) (cond ((null? ns) s)
                                    ((and (= (extract (car ns) var) v) (same-path? (extract (car ns) path) path))
                                     (go (cdr ns) (apply-one (car ns) s)))
                                    (else (go (cdr ns) s))))))
      (if (or (null? (get cf-refine)) (member-int? v (get cf-assigned)) (any-member? path (get cf-stored))) s (go (get cf-refine) s)))))
"The variable and field path core `x` reads (`(car (cdr v))`: v, cdr car),
if it reads one; var -1 if not."
(define-type cf-path (productof (var int) (path strings)))
(define* path-of (subr spin (core) cf-path)
  (lambda (x) (tagcase x
                (k-var (v r) (product (var v) (path nil)))
                (k-field (e label) (let ((p (path-of e))) (product (var (extract p var)) (path (append (extract p path) (list label))))))
                (else y (product (var -1) (path nil))))))
(define* take-ints (subr spin (int ints) ints)
  (lambda (n l) (if (or (<= n 0) (null? l)) nil (cons (car l) (take-ints (- n 1) (cdr l))))))

"The contour of calls `l`, numbered on first use."
(define* contour-of (subr cf-eff (ints) int)
  (lambda (l)
    (if (null? l) 0
        (let* ((rest (contour-of (cdr l))) (k (pair-key (car l) rest)) (id (table-ref (get cf-contour-ids) k -1)))
          (if (>= id 0) id
              (let ((n (get cf-contour-count)))
                (begin (set cf-contour-count (+ n 1))
                  (table-set! (get cf-contour-ids) k n)
                  (table-set! (get cf-contour-calls) n l)
                  n)))))))
"The closure of lambda `l` made in contour `c`: in the empty contour, the
lambda's own number; else one past them, numbered on first use."
(define* closure-of (subr cf-eff (int int) int)
  (lambda (l c)
    (if (= c 0) l
        (let* ((k (pair-key l c)) (id (table-ref (get cf-closure-ids) k -1)))
          (if (>= id 0) id
              (let ((n (+ (get cf-closure-count) (array-length (get cf-lambda-array)))))
                (begin (set cf-closure-count (+ (get cf-closure-count) 1))
                  (table-set! (get cf-closure-ids) k n)
                  (table-set! (get cf-closure-lambda) n l)
                  (table-set! (get cf-closure-contour) n c)
                  n)))))))
(define* closure-lambda (subr cf-eff (int) int)
  (lambda (cl) (if (< cl (array-length (get cf-lambda-array))) cl (table-ref (get cf-closure-lambda) cl -1))))
(define* closure-contour (subr cf-eff (int) int)
  (lambda (cl) (if (< cl (array-length (get cf-lambda-array))) 0 (table-ref (get cf-closure-contour) cl 0))))
"The contour call `call`, in contour `c`, gives its callee."
(define* push-contour (subr cf-eff (int int) int)
  (lambda (call c)
    (if (= (get cf-depth) 0) 0
        (contour-of (take-ints (get cf-depth) (cons call (table-ref (get cf-contour-calls) c nil)))))))

"Primitive `name`'s value."
(define* prim-val (subr cf-eff (string) int)
  (lambda (name)
    (let ((i (cf-index name (get cf-prims))))
      (+ 3 (* 4 (if (>= i 0) (- (- (get cf-prim-count) 1) i)
                    (let ((n (get cf-prim-count)))
                      (begin (set cf-prims (cons name (get cf-prims))) (set cf-prim-count (+ n 1)) n))))))))
(define* prim-name (subr cf-eff (int) string)
  (lambda (v) (letrec ((go (subr cf-eff (strings int) string)
                         (lambda (l i) (cond ((null? l) "?") ((= i 0) (car l)) (else (go (cdr l) (- i 1)))))))
                (go (get cf-prims) (- (- (get cf-prim-count) 1) (quotient v 4))))))
(define* label-id (subr cf-eff (string) int)
  (lambda (label)
    (let ((i (table-ref (get cf-labels) label -1)))
      (if (>= i 0) i
          (let ((n (get cf-label-count))) (begin (table-set! (get cf-labels) label n) (set cf-label-count (+ n 1)) n))))))
(define* kind-vals (subr cf-eff (strings) vals)
  (lambda (names)
    (cond ((null? names) nil)
          ((string=? (car names) "unknown") (vals-union (list cf-unknown) (kind-vals (cdr names))))
          (else (vals-union (list (+ 2 (* 4 (cf-kind (car names))))) (kind-vals (cdr names)))))))

;;; ------------------------------------------------------------ fields

"Field `label` of site `site`, read (made, so that the site knows it)."
(define* site-field (subr cf-eff (int string) vals)
  (lambda (site label)
    (let* ((l (label-id label)) (ls (table-ref (get cf-site-labels) site nil)))
      (begin
        (if (letrec ((has (subr spin (ints) bool) (lambda (x) (and (pair? x) (or (= (car x) l) (has (cdr x)))))))
              (has ls))
            #u
            (table-set! (get cf-site-labels) site (cons l ls)))
        (vals-union (cf-read (field-key site l))
                    (if (= (table-ref (get cf-site-escaped) site 0) 1) (list cf-unknown) nil))))))

"The field `label` of what `s` holds (unknown if it may be anything)."
(define* fields-of (subr cf-eff (vals string) vals)
  (lambda (s label)
    (cond ((null? s) nil)
          ((site-val? (car s)) (vals-union (site-field (quotient (car s) 4) label) (fields-of (cdr s) label)))
          ((= (car s) cf-unknown) (vals-union (list cf-unknown) (fields-of (cdr s) label)))
          (else (fields-of (cdr s) label)))))
"The payload of the sum sites in `s` of tag `tag` (any, for \"\")."
(define* payload-of (subr cf-eff (vals string) vals)
  (lambda (s tag)
    (cond ((null? s) nil)
          ((site-val? (car s))
           (let ((info (array-ref (get cf-site-array) (quotient (car s) 4))))
             (vals-union (if (and (string=? (extract info kind) "sum") (or (string=? tag "") (string=? (extract info tag) tag)))
                             (site-field (quotient (car s) 4) "payload")
                             nil)
                         (payload-of (cdr s) tag))))
          ((= (car s) cf-unknown) (vals-union (list cf-unknown) (payload-of (cdr s) tag)))
          (else (payload-of (cdr s) tag)))))

"Arguments `as` given, in contour `c`, to parameters `ps` (and the rest,
`rest`, if not -1)."
(define* pass-args (subr cf-eff (ints int (listof vals acyclic) int) unit)
  (lambda (ps rest as c)
    (cond ((null? ps) (if (>= rest 0) (cf-join! (var-key rest c) (union-all as)) #u))
          ((null? as) #u)
          (else (begin (cf-join! (var-key (car ps) c) (car as)) (pass-args (cdr ps) rest (cdr as) c))))))
"Where what escaped escaped: each primitive (or `unknown`, a call of code
not known; `store`, a store through unknown), and how many times it was
given a closure or site, for finding where unknown comes from."
(define cf-escape-sources (ref (listof (productof (name string) (count int)) acyclic) @cf) (new nil))
(define* cf-count-escape! (subr cf-eff (string vals) unit)
  (lambda (name s)
    (if (not (letrec ((any (subr spin (vals) bool) (lambda (l) (and (pair? l) (or (closure-val? (car l)) (site-val? (car l)) (= (car l) cf-unknown) (any (cdr l)))))))
               (any s)))
        #u
        (set cf-escape-sources
             (letrec ((go (subr spin ((listof (productof (name string) (count int)) acyclic)) (listof (productof (name string) (count int)) acyclic))
                            (lambda (l) (cond ((null? l) (list (product (name name) (count 1))))
                                              ((string=? (extract (car l) name) name) (cons (product (name name) (count (+ 1 (extract (car l) count)))) (cdr l)))
                                              (else (cons (car l) (go (cdr l))))))))
               (go (get cf-escape-sources)))))))
"The escapes' sources, most first, at most `n`, said."
(define* cf-escape-report (subr cf-eff (int) string)
  (lambda (n)
    (letrec ((insert (subr spin ((productof (name string) (count int)) (listof (productof (name string) (count int)) acyclic)) (listof (productof (name string) (count int)) acyclic))
               (lambda (x l) (if (or (null? l) (> (extract x count) (extract (car l) count))) (cons x l) (cons (car l) (insert x (cdr l))))))
             (sort (subr spin ((listof (productof (name string) (count int)) acyclic) (listof (productof (name string) (count int)) acyclic)) (listof (productof (name string) (count int)) acyclic))
               (lambda (l acc) (if (null? l) acc (sort (cdr l) (insert (car l) acc)))))
             (say (subr spin ((listof (productof (name string) (count int)) acyclic) int) string)
               (lambda (l k) (if (or (null? l) (= k 0)) ""
                                 (string-append (extract (car l) name) " " (int->string (extract (car l) count)) (if (or (null? (cdr l)) (= k 1)) "" ", ")
                                                (say (cdr l) (- k 1)))))))
      (string-append "escaped by: " (say (sort (get cf-escape-sources) nil) n)))))
"The elements of the lists `s`, a list of sets a position (car of each
pair site; a vector's elements at every position); past `cf-max-spine`
positions, or where the list may be any (unknown) or turns back on itself,
the rest are one, the last, and `open` says so. `ends`: the positions a
list may end before (one of `s` shorter than another, ending there)."
(define-type cf-positions (productof (elems (listof vals acyclic)) (open bool) (ends ints)))
(define* positions (subr cf-eff (vals) cf-positions)
  (lambda (s)
    (letrec ((sites (subr spin (vals) vals) (lambda (l) (cond ((null? l) nil) ((site-val? (car l)) (cons (car l) (sites (cdr l)))) (else (sites (cdr l))))))
             ;; Everything reachable from `s` by `cdr`: all its elements.
             (all (subr cf-eff (vals vals vals) vals)
               (lambda (s seen acc)
                 (let ((new (letrec ((go (subr spin (vals) vals) (lambda (l) (cond ((null? l) nil) ((member-int? (car l) seen) (go (cdr l))) (else (cons (car l) (go (cdr l))))))))
                              (go (sites s)))))
                   (if (null? new) (vals-union acc (if (vals-has? s cf-unknown) (list cf-unknown) nil))
                       (all (fields-of new "cdr") (append new seen)
                            (vals-union acc (vals-union (fields-of new "car") (vals-union (fields-of new "elt") (if (vals-has? s cf-unknown) (list cf-unknown) nil)))))))))
             (go (subr cf-eff (vals int vals) cf-positions)
               (lambda (s i seen)
                 (let ((ss (sites s)))
                   (cond ((and (null? ss) (not (vals-has? s cf-unknown))) (the cf-positions (product (elems nil) (open #f) (ends (list i)))))
                         ((or (vals-has? s cf-unknown) (>= i (- cf-max-spine 1))
                              (letrec ((any (subr spin (vals) bool) (lambda (l) (and (pair? l) (or (member-int? (car l) seen) (any (cdr l)))))))
                                (any ss))
                              (pair? (fields-of ss "elt")))
                          (product (elems (list (all s seen nil))) (open #t) (ends (list i))))
                         (else (let ((rest (go (fields-of ss "cdr") (+ i 1) (append ss seen)))
                                     ;; Something here that is no pair: a list may end here.
                                     (ends-here (letrec ((other (subr spin (vals) bool) (lambda (l) (and (pair? l) (or (not (site-val? (car l))) (other (cdr l)))))))
                                                  (other s))))
                                 (product (elems (cons (fields-of ss "car") (extract rest elems))) (open (extract rest open))
                                          (ends (if ends-here (cons i (extract rest ends)) (extract rest ends)))))))))))
      (go s 0 nil))))

"Every element of the lists `s`, whatever its position."
(define* all-elements (subr cf-eff (vals) vals)
  (lambda (s) (union-all (extract (positions s) elems))))

"The first `n` of `l`."
(define* take-vals (subr spin (int (listof vals acyclic)) (listof vals acyclic))
  (lambda (n l) (if (or (<= n 0) (null? l)) nil (cons (car l) (take-vals (- n 1) (cdr l))))))
"`as` without its first `n`."
(define* drop-vals (subr spin (int (listof vals acyclic)) (listof vals acyclic))
  (lambda (n l) (if (or (<= n 0) (null? l)) l (drop-vals (- n 1) (cdr l)))))

(define-rec
  ;; What `s` holds escapes to code not known: its closures may be called
  ;; with anything (their bodies evaluated where they were made, their
  ;; parameters unknown there), and what its sites hold escapes too, as
  ;; anything put in them later does, and reading them gives anything.
  (escape! (subr cf-eff (vals) unit)
    (lambda (s)
      (cond ((null? s) #u)
            ((closure-val? (car s))
             (let* ((cl (quotient (car s) 4)) (l (closure-lambda cl)) (c (closure-contour cl))
                    (info (array-ref (get cf-lambda-array) l)))
               (begin
                 (table-set! (get cf-escaped) l 1)
                 (letrec ((params (subr cf-eff (ints) unit)
                            (lambda (ps) (if (null? ps) #u (begin (cf-join! (var-key (car ps) c) (list cf-unknown)) (params (cdr ps)))))))
                   (params (extract info params)))
                 (if (>= (extract info rest) 0) (cf-join! (var-key (extract info rest) c) (list cf-unknown)) #u)
                 (cf-ensure-task! cl)
                 (escape! (cdr s)))))
            ((site-val? (car s))
             (let ((site (quotient (car s) 4)))
               (begin
                 (if (= (table-ref (get cf-site-escaped) site 0) 1) #u
                     (begin
                       (table-set! (get cf-site-escaped) site 1)
                       (letrec ((each (subr cf-eff (ints) unit)
                                  (lambda (ls) (if (null? ls) #u
                                                   (let ((k (field-key site (car ls))))
                                                     (begin (escape! (table-ref (get cf-cells) k nil))
                                                       (cf-join! k (list cf-unknown))
                                                       (each (cdr ls))))))))
                         (each (table-ref (get cf-site-labels) site nil)))))
                 (escape! (cdr s)))))
            (else (escape! (cdr s))))))
  ;; What `vs` holds that a `plambda` made, instantiated with `as`: its
  ;; binders given them, where it was made.
  (instantiate! (subr cf-eff (vals (listof vals acyclic)) unit)
    (lambda (vs as)
      (cond ((null? vs) #u)
            ((closure-val? (car vs))
             (let ((cl (quotient (car vs) 4)))
               (begin (pass-args (cf-poly-binders (get cf-poly-lambdas) (closure-lambda cl)) -1 as (closure-contour cl))
                 (instantiate! (cdr vs) as))))
            ((site-val? (car vs))
             (begin (pass-args (cf-poly-binders (get cf-poly-sites) (quotient (car vs) 4)) -1 as 0)
               (instantiate! (cdr vs) as)))
            (else (instantiate! (cdr vs) as)))))
  ;; Rest parameter `rest` of lambda `l`, in contour `c`, given the
  ;; arguments past its others, `extra`: the list its sites are, a site an
  ;; argument, the last the rest; or (none) the end of one.
  (pass-rest! (subr cf-eff (int int (listof vals acyclic) int) unit)
    (lambda (l rest extra c)
      (let ((site (cf-rest-site (get cf-rest-sites) l)) (null (kind-vals (list (get cf-null-kind)))))
        (cond ((< site 0) (cf-join! (var-key rest c) (union-all extra)))
              ((null? extra) (cf-join! (var-key rest c) null))
              (else (begin (spine! site extra) (cf-join! (var-key rest c) (list (+ 1 (* 4 site))))))))))
  ;; Elements `es` put in the list of sites from `site` (`cf-spine-sites!`):
  ;; one a site, those past the last into it, its `cdr` itself too.
  (spine! (subr cf-eff (int (listof vals acyclic)) unit)
    (lambda (site es)
      (letrec ((go (subr cf-eff (int (listof vals acyclic)) unit)
                 (lambda (i es)
                   (if (null? es) #u
                       (let ((s (the vals (list (+ 1 (* 4 (+ site i))))))
                             (null (kind-vals (list (get cf-null-kind)))))
                         (if (= i (- cf-max-spine 1))
                             (begin (store! s "car" (union-all es)) (store! s "cdr" (vals-union s null)))
                             (begin (store! s "car" (car es))
                               (store! s "cdr" (if (null? (cdr es)) null (list (+ 1 (* 4 (+ site (+ i 1)))))))
                               (go (+ i 1) (cdr es)))))))))
        (go 0 es))))
  ;; Field `label` of the sites in `targets` given `s`.
  (store! (subr cf-eff (vals string vals) unit)
    (lambda (targets label s)
      (cond ((null? targets) #u)
            ((site-val? (car targets))
             (let ((site (quotient (car targets) 4)))
               (begin
                 (site-field site label)
                 (cf-join! (field-key site (label-id label)) s)
                 (if (= (table-ref (get cf-site-escaped) site 0) 1) (escape! s) #u)
                 (store! (cdr targets) label s))))
            ((= (car targets) cf-unknown) (begin (cf-count-escape! "store" s) (escape! s) (store! (cdr targets) label s)))
            (else (store! (cdr targets) label s))))))

;;; ------------------------------------------------------------ evaluation

"An arm's variables, in contour `c`, given the payload: all of it, or
(`fields`) its product's fields by position."
(define* bind-arm (subr cf-eff (ints bool vals int) unit)
  (lambda (vars fields payload c)
    (cond ((null? vars) #u)
          ((not fields) (cf-join! (var-key (car vars) c) payload))
          (else (letrec ((go (subr cf-eff (ints int) unit)
                           (lambda (vs i) (if (null? vs) #u
                                              (begin (cf-join! (var-key (car vs) c) (fields-of payload (int->string i)))
                                                (go (cdr vs) (+ i 1)))))))
                  (go vars 1))))))

(define-rec
  ;; The value of `x` in contour `c`, in the store as it is, joining what it
  ;; does into it.
  (eval-core (subr cf-eff (core int) vals)
    (lambda (x c)
      (tagcase x
        (k-none (xs) (begin (eval-all xs c) nil))
        (k-const (k) (list (+ 2 (* 4 k))))
        (k-var (v r) (let ((s (narrow v nil (cf-read (var-key v c))))) (begin (if (>= r 0) (cf-note! (get cf-ref-vals) r s) #u) s)))
        (k-narrow (ns body)
          (let ((outer (get cf-refine)))
            (begin (set cf-refine (append ns outer))
              (let ((v (eval-core body c))) (begin (set cf-refine outer) v)))))
        (k-if (test yes then no else)
          (let* ((t (eval-core test c)) (outer (get cf-refine))
                 (a (begin (set cf-refine (append yes outer)) (eval-core then c)))
                 (b (begin (set cf-refine (append no outer)) (eval-core else c))))
            (begin (set cf-refine outer) (vals-union a b))))
        (k-prim (name) (list (prim-val name)))
        (k-lam (l) (let ((cl (closure-of l c)))
                     ;; Made: its body evaluated where it was made, whether or not
                     ;; it is called (the runtime calls some: handlers, branches).
                     (begin (cf-ensure-task! cl) (list (* 4 cl)))))
        (k-seq (xs) (last-vals (eval-all xs c)))
        (k-alt (xs) (union-all (eval-all xs c)))
        (k-bind (v e) (begin (cf-join! (var-key v c) (eval-core e c)) nil))
        (k-alloc (site inits)
          (begin
            (letrec ((go (subr cf-eff ((listof field-init acyclic)) unit)
                       (lambda (is) (if (null? is) #u
                                        (begin (store! (list (+ 1 (* 4 site))) (extract (car is) label) (eval-core (extract (car is) value) c))
                                          (go (cdr is)))))))
              (go inits))
            (list (+ 1 (* 4 site)))))
        (k-field (e label)
          (let ((s (fields-of (eval-core e c) label)) (p (path-of x)))
            (if (< (extract p var) 0) s (narrow (extract p var) (extract p path) s))))
        (k-store (e label v) (let* ((targets (eval-core e c)) (s (eval-core v c))) (begin (store! targets label s) nil)))
        (k-escape (xs) (let ((s (union-all (eval-all xs c)))) (begin (cf-count-escape! "given" s) (escape! s) (list cf-unknown))))
        (k-inst (e args)
          (let* ((vs (eval-core e c)) (as (eval-all args c)))
            (begin (instantiate! vs as) vs)))
        (k-case (e arms)
          (let ((subject (eval-core e c)))
            (union-all
             (letrec ((go (subr cf-eff ((listof arm acyclic)) (listof vals acyclic))
                        (lambda (as)
                          (if (null? as) nil
                              (let ((a (car as)))
                                (begin
                                  (bind-arm (extract a vars) (extract a fields) (payload-of subject (extract a tag)) c)
                                  (cons (eval-core (extract a body) c) (go (cdr as)))))))))
               (go arms)))))
        (k-app (call f args)
          (let* ((ops (eval-core f c)) (as (eval-all args c)))
            (begin
              (cf-note! (get cf-callees) call ops)
              (call-all call c ops as)))))))
  (eval-all (subr cf-eff (cores int) (listof vals acyclic))
    (lambda (xs c) (if (null? xs) nil (let ((v (eval-core (car xs) c))) (cons v (eval-all (cdr xs) c))))))
  ;; Each operator in `ops` called at `call`, in contour `c`, with `as`: the
  ;; union of their results.
  (call-all (subr cf-eff (int int vals (listof vals acyclic)) vals)
    (lambda (call c ops as)
      (cond ((null? ops) nil)
            ((closure-val? (car ops))
             (let* ((cl (quotient (car ops) 4))
                    (l (closure-lambda cl))
                    (made (closure-contour cl))
                    (c1 (push-contour call c))
                    (info (array-ref (get cf-lambda-array) l))
                    (task (closure-of l c1)))
               (begin
                 ;; Its free variables, copied from where it was made.
                 (if (= c1 made) #u
                     (letrec ((copy (subr cf-eff (ints) unit)
                                (lambda (vs) (if (null? vs) #u
                                                 (begin (cf-join! (var-key (car vs) c1) (cf-read (var-key (car vs) made)))
                                                   (copy (cdr vs)))))))
                       (copy (array-ref (get cf-free) l))))
                 (pass-args (extract info params) -1 as c1)
                 (if (>= (extract info rest) 0) (pass-rest! l (extract info rest) (drop-vals (length (extract info params)) as) c1) #u)
                 (cf-ensure-task! task)
                 (vals-union (cf-read (result-key task)) (call-all call c (cdr ops) as)))))
            ((prim-val? (car ops))
             (vals-union (call-prim call c (prim-name (car ops)) as) (call-all call c (cdr ops) as)))
            ((= (car ops) cf-unknown)
             (begin (cf-count-escape! "unknown" (union-all as)) (escape! (union-all as)) (vals-union (list cf-unknown) (call-all call c (cdr ops) as))))
            (else (call-all call c (cdr ops) as)))))
  ;; Primitive `name` called, as its language says.
  (call-prim (subr cf-eff (int int string (listof vals acyclic)) vals)
    (lambda (call c name as)
      (tagcase ((extract (get cf-language) model) name)
        (m-data (escapes kinds) (let ((r (kind-vals kinds)))
                                  (begin (if escapes (begin (cf-count-escape! name (union-all as)) (escape! (union-all as))) #u)
                                    (if (vals-has? r cf-unknown) (cf-count-escape! (string-append "gives ? " name) r) #u)
                                    r)))
        (m-pass () (union-all as))
        (m-apply ()
          ;; The last argument's elements by position: a call for each length
          ;; the list may have (where one of the lists may end), and, where it
          ;; may go on, one with its last as many times as any lambda may take.
          (if (null? as) nil
              (let* ((r (reverse as))
                     (middle (the (listof vals acyclic) (reverse (cdr (reverse (cdr as))))))
                     (ps (if (null? (cdr as)) (the cf-positions (product (elems nil) (open #f) (ends (list 0)))) (positions (car r))))
                     (ended (letrec ((go (subr cf-eff (ints) vals)
                                           (lambda (es) (if (null? es) nil
                                                            (vals-union (call-all call c (car as) (append middle (take-vals (car es) (extract ps elems))))
                                                                        (go (cdr es)))))))
                              (go (extract ps ends)))))
                (if (and (extract ps open) (pair? (extract ps elems)))
                    (vals-union ended
                                (call-all call c (car as)
                                          (append middle
                                                  (append (extract ps elems)
                                                          (letrec ((rep (subr spin (int) (listof vals acyclic)) (lambda (k) (if (<= k 0) nil (cons (last-vals (extract ps elems)) (rep (- k 1)))))))
                                                            (rep 16))))))
                    ended))))
        (m-calls (specs result escapes)
          (letrec ((nth (subr spin ((listof vals acyclic) int) vals)
                          (lambda (l k) (cond ((null? l) nil) ((= k 0) (car l)) (else (nth (cdr l) (- k 1))))))
                   ;; An argument spec's values, given the calls' results so far.
                   (arg (subr cf-eff (cf-arg (listof vals acyclic)) vals)
                     (lambda (a rs)
                       (tagcase a
                         (a-arg (i) (nth as i))
                         (a-elems (i) (all-elements (nth as i)))
                         (a-kinds (ks) (kind-vals ks))
                         (a-result (j) (nth rs j))
                         (a-union (l) (union-all (args l rs)))
                         (a-many (x) (arg x rs)))))
                   (args (subr cf-eff ((listof cf-arg acyclic) (listof vals acyclic)) (listof vals acyclic))
                     (lambda (l rs) (if (null? l) nil (cons (arg (car l) rs) (args (cdr l) rs)))))
                   ;; A call's arguments: an `a-many` as many times as any lambda may take.
                   (call-args (subr cf-eff ((listof cf-arg acyclic) (listof vals acyclic)) (listof vals acyclic))
                     (lambda (l rs)
                       (cond ((null? l) nil)
                             ((tagcase (car l) (a-many (x) #t) (else y #f))
                              (let ((v (arg (car l) rs)))
                                (letrec ((rep (subr spin (int) (listof vals acyclic)) (lambda (k) (if (<= k 0) nil (cons v (rep (- k 1)))))))
                                  (rep 16))))
                             (else (cons (arg (car l) rs) (call-args (cdr l) rs))))))
                   (run (subr cf-eff ((listof cf-callspec acyclic) (listof vals acyclic)) (listof vals acyclic))
                     (lambda (ss rs)
                       (if (null? ss) rs
                           (let ((r (call-all call c (nth as (extract (car ss) proc)) (call-args (extract (car ss) args) rs))))
                             (run (cdr ss) (append rs (list r))))))))
            (let ((rs (run specs nil)))
              (begin (escape! (union-all (args escapes rs))) (arg result rs)))))
        (m-map (kinds)
          (if (null? as) (kind-vals kinds)
              (let ((base (cf-call-result (get cf-call-results) call)))
                (if (< base 0)
                    ;; No list of its own: the elements, all at once; what it returns escapes.
                    (let ((elements (letrec ((go (subr cf-eff ((listof vals acyclic)) (listof vals acyclic))
                                                   (lambda (l) (if (null? l) nil (cons (all-elements (car l)) (go (cdr l)))))))
                                      (go (cdr as)))))
                      (begin (escape! (call-all call c (car as) elements)) (kind-vals kinds)))
                    ;; By position: the function called on each position's elements,
                    ;; what it returns there the list's, in this call's sites.
                    (let* ((ps (letrec ((go (subr cf-eff ((listof vals acyclic)) (listof cf-positions acyclic))
                                              (lambda (l) (if (null? l) nil (cons (positions (car l)) (go (cdr l)))))))
                                 (go (cdr as))))
                           (n (letrec ((go (subr spin ((listof cf-positions acyclic) int) int)
                                             (lambda (l m) (if (null? l) m (go (cdr l) (max m (length (extract (car l) elems))))))))
                                (go ps 0)))
                           (results (letrec ((nth (subr spin ((listof vals acyclic) int) vals)
                                                    (lambda (l k) (cond ((null? l) nil) ((= k 0) (car l)) (else (nth (cdr l) (- k 1))))))
                                             (go (subr cf-eff (int) (listof vals acyclic))
                                               (lambda (i) (if (>= i n) nil
                                                               (let ((r (call-all call c (car as)
                                                                                  (letrec ((args (subr spin ((listof cf-positions acyclic)) (listof vals acyclic))
                                                                                                   (lambda (l) (if (null? l) nil (cons (nth (extract (car l) elems) i) (args (cdr l)))))))
                                                                                    (args ps)))))
                                                                 (cons r (go (+ i 1))))))))
                                      (go 0))))
                      (begin (spine! base results)
                        (vals-union (kind-vals (list (get cf-null-kind))) (if (null? results) nil (list (+ 1 (* 4 base))))))))))))))
  ;; Task `t` run: its lambda's body evaluated in its contour, its result kept.
  (run-task! (subr cf-eff (int) unit)
    (lambda (t)
      (begin
        (set cf-current t)
        (if (= t cf-main)
            (begin (eval-all (get cf-tops) 0) #u)
            (cf-join! (result-key t) (eval-core (extract (array-ref (get cf-lambda-array) (closure-lambda t)) body)
                                                (closure-contour t))))
        (let ((es (get cf-to-escape))) (begin (set cf-to-escape nil) (escape! es)))
        (set cf-steps (+ (get cf-steps) 1))))))

;;; ------------------------------------------------------------ free variables

"The variables `x` refers to and binds (its lambdas' bodies and
parameters included), onto `refs` and `binds`."
(define-type refs-binds (productof (refs ints) (binds ints)))
(define-rec
  (refs-binds-of (subr cf-eff (core refs-binds) refs-binds)
    (lambda (x acc)
      (let ((bind (lambda ((vs ints) (acc refs-binds)) (product (refs (extract acc refs)) (binds (append-ints vs (extract acc binds)))))))
        (tagcase x
          (k-none (xs) (refs-binds-all xs acc))
          (k-var (v r) (product (refs (cons v (extract acc refs))) (binds (extract acc binds))))
          (k-lam (l) (let ((info (array-ref (get cf-lambda-array) l)))
                       (refs-binds-of (extract info body)
                                      (bind (if (>= (extract info rest) 0) (cons (extract info rest) (extract info params)) (extract info params))
                                            acc))))
          (k-app (call f args) (refs-binds-all args (refs-binds-of f acc)))
          (k-seq (xs) (refs-binds-all xs acc))
          (k-alt (xs) (refs-binds-all xs acc))
          (k-bind (v e) (refs-binds-of e (bind (list v) acc)))
          (k-alloc (site inits)
            (letrec ((go (subr cf-eff ((listof field-init acyclic) refs-binds) refs-binds)
                       (lambda (is acc) (if (null? is) acc (go (cdr is) (refs-binds-of (extract (car is) value) acc))))))
              (go inits acc)))
          (k-field (e label) (refs-binds-of e acc))
          (k-store (e label v) (refs-binds-of v (refs-binds-of e acc)))
          (k-escape (xs) (refs-binds-all xs acc))
          (k-inst (e args) (refs-binds-all args (refs-binds-of e acc)))
          (k-if (test yes then no else) (refs-binds-all (list test then else) acc))
          (k-narrow (ns body) (refs-binds-of body acc))
          (k-case (e arms)
            (letrec ((go (subr cf-eff ((listof arm acyclic) refs-binds) refs-binds)
                       (lambda (as acc)
                         (if (null? as) acc
                             (go (cdr as) (refs-binds-of (extract (car as) body) (bind (extract (car as) vars) acc)))))))
              (go arms (refs-binds-of e acc))))
          (else y acc)))))
  (refs-binds-all (subr cf-eff (cores refs-binds) refs-binds)
    (lambda (xs acc) (if (null? xs) acc (refs-binds-all (cdr xs) (refs-binds-of (car xs) acc))))))

"Lambda `l`'s free variables: those its body refers to, not bound in it,
not global."
(define* free-of (subr cf-eff (int) ints)
  (lambda (l)
    (let* ((info (array-ref (get cf-lambda-array) l))
           (rb (refs-binds-of (extract info body)
                              (product (refs nil) (binds (if (>= (extract info rest) 0) (cons (extract info rest) (extract info params))
                                                             (extract info params))))))
           (bound (extract rb binds)))
      (letrec ((go (subr cf-eff (ints ints) ints)
                 (lambda (rs acc)
                   (cond ((null? rs) acc)
                         ((or (< (car rs) (get cf-global-count)) (member-int? (car rs) bound) (member-int? (car rs) acc))
                          (go (cdr rs) acc))
                         (else (go (cdr rs) (cons (car rs) acc)))))))
        (go (extract rb refs) nil)))))

;;; ------------------------------------------------------------ running

"The list `l`, newest first, as an array oldest first."
(define* lambdas->array (subr cf-eff ((listof lambda-info acyclic)) (arrayof lambda-info @cf))
  (lambda (l)
    (let ((a (the (arrayof lambda-info @cf) (make-array (length l) (product (span cf-no-span) (name "") (params nil) (rest -1) (body (k-none nil)))))))
      (letrec ((go (subr cf-eff ((listof lambda-info acyclic) int) unit)
                 (lambda (l i) (if (null? l) #u (begin (array-set! a i (car l)) (go (cdr l) (- i 1)))))))
        (begin (go l (- (length l) 1)) a)))))
(define* sites->array (subr cf-eff ((listof site-info acyclic)) (arrayof site-info @cf))
  (lambda (l)
    (let ((a (the (arrayof site-info @cf) (make-array (length l) (product (span cf-no-span) (kind "") (tag ""))))))
      (letrec ((go (subr cf-eff ((listof site-info acyclic) int) unit)
                 (lambda (l i) (if (null? l) #u (begin (array-set! a i (car l)) (go (cdr l) (- i 1)))))))
        (begin (go l (- (length l) 1)) a)))))

"The world read (core.fx's numbering, and its top levels `tops`), of
language `lang`, to be analysed at depth `m` from the start: nothing run yet."
(define* cf-start! (subr cf-eff (cf-lang cores int) unit)
  (lambda (lang tops m)
    (begin
      (set cf-language lang) (set cf-tops tops) (set cf-depth m)
      (set cf-lambda-array (lambdas->array (get cf-lambdas)))
      (set cf-site-array (sites->array (get cf-sites)))
      (set cf-free (make-array (array-length (get cf-lambda-array)) nil))
      (letrec ((frees (subr cf-eff (int) unit)
                 (lambda (l) (if (>= l (array-length (get cf-lambda-array))) #u
                                 (begin (array-set! (get cf-free) l (free-of l)) (frees (+ l 1)))))))
        (frees 0))
      (set cf-contour-ids (new-int-table)) (set cf-contour-calls (new-ints-table)) (set cf-contour-count 1)
      (set cf-closure-ids (new-int-table)) (set cf-closure-lambda (new-int-table)) (set cf-closure-contour (new-int-table))
      (set cf-closure-count 0)
      (set cf-prims nil) (set cf-prim-count 0)
      (set cf-labels (the (table string int @cf) (make-table string-hash string=?))) (set cf-label-count 0)
      (set cf-cells (new-vals-table)) (set cf-readers (new-ints-table))
      (set cf-ref-vals (new-vals-table)) (set cf-callees (new-vals-table))
      (set cf-escaped (new-int-table)) (set cf-site-escaped (new-int-table)) (set cf-site-labels (new-ints-table))
      (set cf-front nil) (set cf-back nil) (set cf-queued (new-int-table)) (set cf-made (new-int-table))
      (set cf-steps 0) (set cf-to-escape nil)
      (set cf-queue-length 0) (set cf-facts 0) (set cf-cell-count 0) (set cf-escape-sources nil) (set cf-unknown-firsts nil)
      (cf-ensure-task! cf-main))))

"The analysis's progress, said: tasks run, on the worklist, and made;
facts (values in cells) and cells; contours and closures; the world's
lambdas, calls and sites."
(define* cf-status (subr cf-eff () string)
  (lambda ()
    (string-append "steps " (int->string (get cf-steps)) " queue " (int->string (get cf-queue-length))
                   " facts " (int->string (get cf-facts)) " cells " (int->string (get cf-cell-count))
                   " contours " (int->string (get cf-contour-count)) " closures " (int->string (get cf-closure-count))
                   " lambdas " (int->string (array-length (get cf-lambda-array))) " calls " (int->string (length (get cf-calls)))
                   " sites " (int->string (array-length (get cf-site-array))))))
"At most `fuel` tasks run. Whether the analysis is done: none left."
(define* cf-step! (subr cf-eff (int) bool)
  (lambda (fuel)
    (cond ((and (null? (get cf-front)) (null? (get cf-back))) #t)
          ((<= fuel 0) #f)
          ((null? (get cf-front)) (begin (set cf-front (reverse (get cf-back))) (set cf-back nil) (cf-step! fuel)))
          (else (let ((t (car (get cf-front))))
                  (begin (set cf-front (cdr (get cf-front)))
                    (table-set! (get cf-queued) t 0)
                    (set cf-queue-length (- (get cf-queue-length) 1))
                    (run-task! t)
                    (cf-step! (- fuel 1))))))))
