;;; machine.fx: the state of a symbolic evaluation: shakedown's
;;; `(shakedown machine)`.
;;;
;;; Evaluation runs under a context (core.fx's rf-ctx): the path condition,
;;; how many symbolic branches it is inside, and what the unwinding bound
;;; needs to know.
;;;
;;; A session is the evaluation of one proof. It collects
;;;   - assumptions: formulas true on every path considered. An (assume e)
;;;     adds pc => e; a check, once recorded, adds that it passed, since
;;;     evaluation does not go on past a failure;
;;;   - obligations: the checks. Each keeps the assumptions made before
;;;     it, its path condition, and its failure condition;
;;;   - the branches taken on symbolic conditions, for a trace;
;;;   - the symbolic constants made, each with a description and the path
;;;     condition it was made under (for playback).
;;;
;;; Where evaluation splits on a symbolic condition (join), each arm runs
;;; in turn, and the arms' values and stores are merged after. An arm that
;;; cannot go on (a failed check, a false assumption) aborts.
;;;
;;; Exceptions: a raise inside a guard ends its path there, but the path
;;; goes on at the guard's handler: the raise is noted in the guard (under
;;; what condition, what was raised, and what the store then held), and its
;;; path is escaped until the guard's body is done.
;;;
;;; Splitting (a proof's `(split)`): a join outside any other runs the rest
;;; of the proof once for each arm. shakedown calls Larceny's continuation
;;; again for each arm after the first; here the rest is a composable
;;; continuation, up to the proof's prompt (check.fx), resumed for each
;;; arm; when it returns (the proof's body done), the arm is `finished`.

(module-parameters ((m-core (load-moduleof "core.fx")) (m-term (load-moduleof "term.fx" m-core))
                    (m-value (load-moduleof "value.fx" m-core m-term))))

(hide (define kit-lists (load-module "../kit/lists.fx"))
      (import kit-lists map for-each filter))

;;; ------------------------------------------------------------ sessions

"A slot of the store, and a value: what a log keeps (the old value), what
a raise's store keeps (the value then), what winds keep (the value to put
back)."
(define-type slot-entry (productof (vec rf-slots) (i int) (val rf-value)))
(define-type slot-entries (listof slot-entry acyclic))
(define-type maybe-log (sumof (none unit) (some slot-entries)))
(define-type branch (productof (pc rf-value) (condition rf-value) (source rf-value)))
(define-type branches (listof branch acyclic))

"A check. kind is one of assert, cover, error, unwind, unsupported,
contract, contract-frame, loop; condition is when it fails (for a cover,
when it is satisfied)."
(define-type obligation
  (productof (kind symbol) (label string) (pc rf-value) (condition rf-value) (assumptions rf-vals)
             (branches branches) (source rf-value)))
(define-type obligations (listof obligation acyclic))

(define-type session
  (productof (assumptions (ref rf-vals @rf)) (obligations (ref obligations @rf)) (constants (ref rf-vals @rf))
             (log (ref maybe-log @rf)) (unwind-bound int) (branches (ref branches @rf))))
(define new-session (subr rf-st (int) session)
  (lambda (bound)
    (product (assumptions (new nil)) (obligations (new nil)) (constants (new nil)) (log (new (sum none #u)))
             (unwind-bound bound) (branches (new nil)))))
(define current (ref session @rf) (new (new-session 0)))

(define session-assumptions (subr rf-st () rf-vals) (lambda () (get (extract (get current) assumptions))))
(define session-obligations (subr rf-st () obligations) (lambda () (the obligations (reverse (get (extract (get current) obligations))))))
(define session-constants (subr rf-st () rf-vals) (lambda () (vals-reverse (get (extract (get current) constants)))))
(define session-unwind-bound (subr rf-st () int) (lambda () (extract (get current) unwind-bound)))
(define session-log (subr rf-st () maybe-log) (lambda () (get (extract (get current) log))))
(define set-session-log! (subr rf-st (maybe-log) unit) (lambda (l) (set (extract (get current) log) l)))
(define session-branches (subr rf-st () branches) (lambda () (get (extract (get current) branches))))
(define log-entries (subr rf-st (maybe-log) slot-entries) (lambda (l) (tagcase l (some es es) (none u nil))))

"Calls of closures on the path so far, and how many a path may make."
(define calls (ref int @rf) (new 0))
(define max-calls (ref int @rf) (new 10000000))
(define set-max-calls! (subr rf-st (int) unit) (lambda (n) (set max-calls n)))

;;; ------------------------------------------------------------ the rest of the machine's state

(define splitting? (ref bool @rf) (new #f))
(define splitting-now? (subr rf-st () bool) (lambda () (get splitting?)))
"A split with arms left: its arms, the rest of the proof, the state to
restore, and its context."
(define-type arm (productof (g rf-value) (k (subr rf-eff (rf-ctx) rf-value))))
(define-type arms (listof arm acyclic))
(define make-arm (subr rf-st (rf-value (subr rf-eff (rf-ctx) rf-value)) arm) (lambda (g k) (product (g g) (k k))))
(define-type split-state
  (productof (trail (sumof (none unit) (some slot-entries))) (split-pc rf-value) (assumptions rf-vals)
             (branches branches) (source rf-value) (calls int)))
(define-type a-split (productof (arms (ref arms @rf)) (k rf-kont) (state split-state) (ctx rf-ctx)))
(define splits (ref (listof a-split acyclic) @rf) (new nil))
"None, or the writes since the first split, latest first."
(define trail (ref (sumof (none unit) (some slot-entries)) @rf) (new (sum none #u)))
(define split-pc (ref rf-value @rf) (new rf-true))

"The handlers in force, innermost first: catchers (of guards, or with a tag
of call/cc's), handlers (procedures, from with-exception-handler), and
barriers."
(define-type raise-record (productof (cond rf-value) (raised rf-value) (store slot-entries)))
(define-type catcher
  (productof (raises (ref (listof raise-record acyclic) @rf)) (base (listof maybe-log acyclic)) (winds slot-entries)
             (tag (sumof (none unit) (some (ref unit @rf)))) (crossed (ref rf-value @rf))))
(define-type handler (sumof (catcher catcher) (proc rf-value) (barrier string)))
(define-type handler-list (listof handler acyclic))
(define handlers (ref handler-list @rf) (new nil))
"Slots to put back on the way out of a raise, innermost first."
(define winds (ref slot-entries @rf) (new nil))
"Where an exception has been raised and caught by a guard whose body is
still running: #f, or a Bool term."
(define escaped (ref rf-value @rf) (new rf-false))
"The logs of the joins and guards evaluation is inside, but the innermost."
(define outer-logs (ref (listof maybe-log acyclic) @rf) (new nil))
"The last form of the program's own source evaluation was at (#f: none)."
(define source (ref rf-value @rf) (new rf-false))
(define note-source! (subr rf-st (rf-value) unit) (lambda (x) (set source x)))

"Watching writes: a list of watches, innermost first, each a table of the
slots-vectors it allows writes to, and its check's label and kind."
(define-type allowance (sumof (allocated unit) (named (productof (whole rf-value) (slots (listof (productof (i int) (g rf-value)) acyclic))))))
(define no-allowance (productof (whole rf-value) (slots (listof (productof (i int) (g rf-value)) acyclic)))
  (product (whole rf-false) (slots nil)))
(define-type watch-table (eqtable rf-slots allowance @rf @rf))
(define-type a-watch (productof (table watch-table) (label string) (kind symbol)))
(define watch (ref (listof a-watch acyclic) @rf) (new nil))

"(apply-proc ctx f args src) applies a value, and (describe v) describes
one: set by eval.fx and prims.fx."
(define apply-proc (ref (subr rf-eff (rf-ctx rf-value rf-vals rf-value) rf-value) @rf)
  (new (lambda ((c rf-ctx) (f rf-value) (args rf-vals) (src rf-value)) rf-unspecified)))
(define describe (ref (subr rf-eff (rf-value) string) @rf) (new (lambda ((v rf-value)) "")))
(define set-raise-hooks! (subr rf-st ((subr rf-eff (rf-ctx rf-value rf-vals rf-value) rf-value) (subr rf-eff (rf-value) string)) unit)
  (lambda (apply show) (begin (set apply-proc apply) (set describe show))))

"Begin a proof's session; split? says whether symbolic joins outside any
other split."
(define begin-session! (subr rf-st (int bool) unit)
  (lambda (bound split?)
    (begin
      (set current (new-session bound))
      (set splitting? split?)
      (set splits nil)
      (set trail (sum none #u))
      (set split-pc rf-true)
      (set calls 0)
      (set watch nil)
      (set source rf-false)
      (set handlers nil)
      (set escaped rf-false)
      (set winds nil)
      (set outer-logs nil))))

;;; ------------------------------------------------------------ checks

(define abort-path (subr rf-eff () void) (lambda () (rf-signal! (sum abort #u))))

"The path condition, less the escaped paths."
(define path (subr rf-st (rf-ctx) rf-value)
  (lambda (ctx)
    (let ((pc (if (rf-true? (get split-pc)) (ctx-pc ctx) (t-and (get split-pc) (ctx-pc ctx)))))
      (if (rf-false? (get escaped)) pc (t-and pc (t-not (get escaped)))))))

(define add-assumption! (subr rf-st (rf-value) unit)
  (lambda (f)
    (if (rf-true? f) #u
        (set (extract (get current) assumptions) (cons f (get (extract (get current) assumptions)))))))

(define record! (subr rf-st (symbol string rf-value rf-value) unit)
  (lambda (kind label pc condition)
    (set (extract (get current) obligations)
         (cons (product (kind kind) (label label) (pc pc) (condition condition) (assumptions (session-assumptions))
                        (branches (session-branches)) (source (get source)))
               (get (extract (get current) obligations))))))

"Check that ok holds here. Evaluation goes on assuming it did; if it cannot
hold, this path ends. A failed check of kind error raises an error object,
if there is a handler."
(define check! (subr rf-eff (rf-ctx symbol string rf-value) unit)
  (lambda (ctx kind label ok)
    (let* ((pc (path ctx))
           (failure (t-and pc (t-not ok))))
      (begin
        (if (and (eq? kind 'error) (pair? (get handlers)))
            (begin (raise! ctx (make-error-value (rf-str label) rf-nil (rf-str label)) #f (t-not ok)) #u)
            (begin
              (if (or (eq? kind 'assert) (not (rf-false? failure))) (record! kind label pc failure) #u)
              (add-assumption! (t-not failure))))
        (if (rf-false? ok) (abort-path) #u)))))
(define fail! (subr rf-eff (rf-ctx symbol string) void)
  (lambda (ctx kind label) (begin (check! ctx kind label rf-false) (abort-path))))

"A branch on a symbolic condition, of the program's source."
(define note-branch! (subr rf-st (rf-ctx rf-value rf-value) unit)
  (lambda (ctx condition src)
    (set (extract (get current) branches)
         (cons (product (pc (path ctx)) (condition condition) (source src)) (get (extract (get current) branches))))))

(define assume! (subr rf-eff (rf-ctx rf-value) unit)
  (lambda (ctx ok)
    (begin (add-assumption! (t-implies (path ctx) ok))
           (if (rf-false? ok) (abort-path) #u))))

"A failure that does not depend on a path: reported as such, with no
source, path or model."
(define record-failure! (subr rf-st (symbol string) unit)
  (lambda (kind label)
    (set (extract (get current) obligations)
         (cons (product (kind kind) (label label) (pc rf-true) (condition rf-true) (assumptions nil) (branches nil) (source rf-false))
               (get (extract (get current) obligations))))))

(define cover! (subr rf-st (rf-ctx string rf-value) unit)
  (lambda (ctx label condition)
    (let* ((pc (path ctx)) (c (t-and (path ctx) condition)))
      (record! 'cover label pc c))))

;;; ------------------------------------------------------------ constants

"Constants (by id) to their description and path condition."
(define-type constant-info (productof (description string) (pc rf-value)))
(define constant-infos (ref (table int constant-info @rf) @rf)
  (new (the (table int constant-info @rf) (make-table id-hash id-same?))))
(define reset-constants! (subr rf-st () unit)
  (lambda () (set constant-infos (the (table int constant-info @rf) (make-table id-hash id-same?)))))

(define note-constant! (subr rf-st (rf-ctx rf-value string) rf-value)
  (lambda (ctx k description)
    (begin
      (set (extract (get current) constants) (cons k (get (extract (get current) constants))))
      (table-set! (get constant-infos) (tid k) (product (description description) (pc (path ctx))))
      k)))
(define fresh-constant! (subr rf-st (rf-ctx int string) rf-value)
  (lambda (ctx sort description) (note-constant! ctx (make-constant sort) description)))
"An Int constant in [0, n), and assumed to be."
(define fresh-index! (subr rf-eff (rf-ctx int string) rf-value)
  (lambda (ctx n description)
    (let* ((k (note-constant! ctx (make-index-constant n) description))
           (lo (t-<= (rf-int 0) k))
           (hi (t-< k (rf-int n))))
      (begin (assume! ctx (t-and lo hi)) k))))
"A constant's description, or \"\" if it has none."
(define constant-description (subr rf-st (rf-value) string)
  (lambda (k) (if (table-has? (get constant-infos) (tid k)) (extract (table-ref (get constant-infos) (tid k) (product (description "") (pc rf-true))) description) "")))
(define has-description? (subr rf-st (rf-value) bool) (lambda (k) (table-has? (get constant-infos) (tid k))))
(define constant-pc (subr rf-st (rf-value) rf-value)
  (lambda (k) (extract (table-ref (get constant-infos) (tid k) (product (description "") (pc rf-true))) pc)))

(define count-call! (subr rf-eff (rf-ctx) unit)
  (lambda (ctx)
    (begin
      (set calls (+ (get calls) 1))
      (if (> (get calls) (get max-calls))
          (fail! ctx 'unwind (string-append "more than " (int->string (get max-calls)) " calls on a path"))
          #u))))

;;; ------------------------------------------------------------ the store

(define logged? (subr rf-st (slot-entries rf-slots int) bool)
  (lambda (log vec i)
    (and (pair? log)
         (or (and (eq? (extract (car log) vec) vec) (= (extract (car log) i) i))
             (logged? (cdr log) vec i)))))

(define store! (subr rf-st (rf-slots int rf-value) unit)
  (lambda (vec i v)
    (begin
      (tagcase (session-log)
        (some log (if (logged? log vec i) #u
                      (set-session-log! (sum some (cons (product (vec vec) (i i) (val (array-ref vec i))) log)))))
        (none u #u))
      (tagcase (get trail)
        (some t (set trail (sum some (cons (product (vec vec) (i i) (val (array-ref vec i))) t))))
        (none u #u))
      (array-set! vec i v))))

"Note a new frame, vector or record's fields."
(define note-allocation! (subr rf-st (rf-slots) rf-slots)
  (lambda (vec)
    (begin (for-each (lambda ((w a-watch)) (eqtable-set! (extract w table) vec (sum allocated #u))) (get watch))
           vec)))

"A write by the program: checked, if writes are watched."
(define write! (subr rf-eff (rf-ctx rf-slots int rf-value) unit)
  (lambda (ctx vec i v)
    (begin
      (for-each (lambda ((w a-watch))
                  (let ((allowed (eqtable-ref (extract w table) vec (sum named no-allowance))))
                    (tagcase allowed
                      (allocated u #u)
                      (named n
                        (if (not (eqtable-has? (extract w table) vec))
                            (check! ctx (extract w kind) (extract w label) rf-false)
                            (check! ctx (extract w kind) (extract w label)
                                    (t-or (extract n whole) (slot-cond i (extract n slots)))))))))
                (get watch))
      (store! vec i v))))
(define slot-cond (subr rf-st (int (listof (productof (i int) (g rf-value)) acyclic)) rf-value)
  (lambda (i l) (cond ((null? l) rf-false) ((= (extract (car l) i) i) (extract (car l) g)) (else (slot-cond i (cdr l))))))

"One slot of a slots-vector, as a modifies clause's footprint has it for a
record's field."
(define-type field-target (productof (object rf-slots) (index int)))
(define-type target (sumof (whole rf-slots) (field field-target)))
(define-type allowed-target (productof (g rf-value) (t target)))

"(thunk), with writes watched under label (a check of kind kind); allowed
is a list of (guard . target) that may be written to as well."
(define watching-writes (subr rf-eff (symbol string (listof allowed-target acyclic) (subr rf-eff () rf-value)) rf-value)
  (lambda (kind label allowed thunk)
    (let ((outer (get watch))
          (table (the watch-table (make-eqtable (array-identity)))))
      (begin
        (for-each (lambda ((a allowed-target))
                    (let* ((vec (tagcase (extract a t) (whole v v) (field f (extract f object))))
                           (entry (tagcase (eqtable-ref table vec (sum named no-allowance))
                                    (named n n) (allocated u no-allowance))))
                      (eqtable-set! table vec
                        (tagcase (extract a t)
                          (field f
                            (let* ((i (extract f index))
                                   (slot (slot-cond i (extract entry slots))))
                              (sum named (product (whole (extract entry whole))
                                                  (slots (the (listof (productof (i int) (g rf-value)) acyclic)
                                                           (cons (product (i i) (g (t-or (extract a g) slot))) (extract entry slots))))))))
                          (whole v (sum named (product (whole (t-or (extract a g) (extract entry whole))) (slots (extract entry slots)))))))))
                  allowed)
        (set watch (cons (product (table table) (label label) (kind kind)) outer))
        (let ((result (rf-protect thunk (lambda () (set watch outer)))))
          (begin (set watch outer) result))))))

;;; ------------------------------------------------------------ joins

"Run (thunk), noting whether it aborted: its value, and whether it did."
(define-type outcome (productof (aborted bool) (value rf-value)))
(define catch-abort (subr rf-eff ((subr rf-eff () rf-value)) outcome)
  (lambda (thunk)
    (let* ((aborted (the (ref bool @rf) (new #f)))
           (v (rf-catch thunk (lambda ((s rf-signal)) (if (rf-abort? s) (begin (set aborted #t) rf-unspecified) (rf-signal! s))))))
      (product (aborted (get aborted)) (value v)))))

"An arm done: its guard, value, and writes #(vec i old new)."
(define-type write-entry (productof (vec rf-slots) (i int) (old rf-value) (new rf-value)))
(define-type done-arm (productof (g rf-value) (result rf-value) (writes (listof write-entry acyclic))))

"Evaluate each arm under its guard; the guards are disjoint and together
cover the path. The merged value of the arms that did not abort, after
merging what they stored. branch?: the join of an if's two arms."
(define join (subr rf-eff (rf-ctx arms bool) rf-value)
  (lambda (ctx arms branch?)
    (if (and (get splitting?) (tagcase (session-log) (none u #t) (some l #f)) (null? (get handlers)) (null? (get watch))
             (null? (get winds)) (rf-false? (get escaped)))
        (split ctx arms)
        (merging-join ctx arms branch?))))

(define merging-join (subr rf-eff (rf-ctx arms bool) rf-value)
  (lambda (ctx arms branch?)
    (let* ((outer-log (session-log))
           (pc (path ctx))
           (calls-before (get calls))
           (calls-after (the (ref int @rf) (new (get calls)))))
      (begin
        (set outer-logs (cons outer-log (get outer-logs)))
        (letrec ((loop (subr rf-eff (arms (listof done-arm acyclic)) rf-value)
                   (lambda (arms done)
                     (if (pair? arms)
                         (let* ((g (extract (car arms) g))
                                (arm-pc (if (and branch? (ruled-out? pc g)) rf-false (t-and pc g))))
                           (if (rf-false? arm-pc)
                               (loop (cdr arms) done)
                               (begin
                                 (set-session-log! (sum some nil))
                                 (set calls calls-before)
                                 (let* ((o (catch-abort (lambda () ((extract (car arms) k) (make-ctx arm-pc (+ (ctx-depth ctx) 1) (ctx-unwind ctx))))))
                                        (writes (undo-log! (log-entries (session-log)))))
                                   (begin
                                     (set calls-after (max (get calls-after) (get calls)))
                                     (loop (cdr arms)
                                           (if (extract o aborted) done
                                               (the (listof done-arm acyclic) (cons (product (g g) (result (extract o value)) (writes writes)) done)))))))))
                         (begin
                           (set-session-log! outer-log)
                           (set outer-logs (cdr (get outer-logs)))
                           (set calls (get calls-after))
                           (if (null? done)
                               (abort-path)
                               (let ((done (the (listof done-arm acyclic) (reverse done))))
                                 (begin (merge-stores! done)
                                        (merge-members (map (lambda ((d done-arm)) (member (extract d g) (extract d result))) done))))))))))
          (loop arms nil))))))

"Restore the logged slots; what the arm wrote to each."
(define undo-log! (subr rf-eff (slot-entries) (listof write-entry acyclic))
  (lambda (log)
    (map (lambda ((e slot-entry))
           (let ((new (array-ref (extract e vec) (extract e i))))
             (begin (array-set! (extract e vec) (extract e i) (extract e val))
                    (product (vec (extract e vec)) (i (extract e i)) (old (extract e val)) (new new)))))
         log)))

"Each slot that an arm wrote gets the merge of the arms' values: what each
wrote, or the old value if it did not write there."
(define merge-stores! (subr rf-eff ((listof done-arm acyclic)) unit)
  (lambda (done)
    (let ((slots (the (ref (listof write-entry acyclic) @rf) (new nil))))
      (begin
        (for-each (lambda ((d done-arm))
                    (for-each (lambda ((w write-entry))
                                (if (find-write (extract w vec) (extract w i) (get slots)) #u
                                    (set slots (cons w (get slots)))))
                              (extract d writes)))
                  done)
        (for-each
         (lambda ((slot write-entry))
           (let ((vec (extract slot vec)) (i (extract slot i)) (old (extract slot old)))
             (store! vec i
                     (merge-members
                      (map (lambda ((d done-arm))
                             (member (extract d g)
                                     (letrec ((find (subr rf-st ((listof write-entry acyclic)) rf-value)
                                                (lambda (ws) (cond ((null? ws) old)
                                                                   ((and (eq? (extract (car ws) vec) vec) (= (extract (car ws) i) i)) (extract (car ws) new))
                                                                   (else (find (cdr ws)))))))
                                       (find (extract d writes)))))
                           done)))))
         (get slots))))))
(define find-write (subr rf-st (rf-slots int (listof write-entry acyclic)) bool)
  (lambda (vec i l) (and (pair? l) (or (and (eq? (extract (car l) vec) vec) (= (extract (car l) i) i)) (find-write vec i (cdr l))))))

;;; ------------------------------------------------------------ ruling out arms
;;;
;;; Whether pc rules out g, found by trying each value of the index
;;; constants and boolean constants in g, when g has no other constants and
;;; they have few values together: against the conjuncts of pc that have no
;;; other constants either.

(define max-tried int 64)
(define-type kv (productof (k rf-value) (v rf-value)))

(define ruled-out? (subr rf-eff (rf-value rf-value) bool)
  (lambda (pc g)
    (let ((ks (constants-of g)))
      (and (pair? ks)
           (letrec ((count (subr rf-eff (rf-vals int) bool)
                      (lambda (ks n)
                        (cond ((null? ks) #t)
                              (else (tagcase (values-of (car ks))
                                      (some vs (let ((n (* n (list-length vs)))) (and (<= n max-tried) (count (cdr ks) n))))
                                      (none u #f)))))))
             (count ks 1))
           (let ((cs (the rf-vals (filter (lambda ((c rf-value)) (subset? (constants-of c) ks)) (few-valued-conjuncts pc)))))
             (not (letrec ((try (subr rf-eff (rf-vals (listof kv acyclic)) bool)
                             (lambda (left chosen)
                               (if (null? left)
                                   (let ((value-of (lambda ((k rf-value)) (kv-lookup k chosen)))
                                         (memo (new-term-memo)))
                                     (and (rf-true? (term-value g value-of memo))
                                          (every-term? (lambda ((c rf-value)) (rf-true? (term-value c value-of memo))) cs)))
                                   (letrec ((next (subr rf-eff (rf-vals) bool)
                                              (lambda (vs)
                                                (and (pair? vs)
                                                     (or (try (cdr left) (the (listof kv acyclic) (cons (product (k (car left)) (v (car vs))) chosen)))
                                                         (next (cdr vs)))))))
                                     (next (tagcase (values-of (car left)) (some vs vs) (none u nil))))))))
                    (try ks nil))))))))
(define kv-lookup (subr rf-st (rf-value (listof kv acyclic)) rf-value)
  (lambda (k l) (cond ((null? l) rf-false) ((rf-eqv? (extract (car l) k) k) (extract (car l) v)) (else (kv-lookup k (cdr l))))))
(define every-term? (subr rf-eff ((subr rf-eff (rf-value) bool) rf-vals) bool)
  (lambda (ok? l) (or (null? l) (and (ok? (car l)) (every-term? ok? (cdr l))))))
(define subset? (subr rf-st (rf-vals rf-vals) bool)
  (lambda (xs ys) (or (null? xs) (and (memq-val? (car xs) ys) (subset? (cdr xs) ys)))))

"The values a constant can take, if they are few."
(define values-of (subr rf-st (rf-value) (sumof (none unit) (some rf-vals)))
  (lambda (k)
    (let ((r (constant-range k)))
      (cond ((>= r 0) (letrec ((loop (subr rf-st (int rf-vals) rf-vals) (lambda (v acc) (if (< v 0) acc (loop (- v 1) (cons (rf-int v) acc))))))
                        (sum some (loop (- r 1) nil))))
            ((bool-term? k) (sum some (list rf-false rf-true)))
            (else (sum none #u))))))

"The constants of a term, remembered."
(define constants-table (ref (table int rf-vals @rf) @rf) (new (the (table int rf-vals @rf) (make-table id-hash id-same?))))
(define constants-of (subr rf-st (rf-value) rf-vals)
  (lambda (t)
    (cond ((not (rf-term? t)) nil)
          ((table-has? (get constants-table) (tid t)) (table-ref (get constants-table) (tid t) nil))
          (else (let ((ks (term-constants (list t)))) (begin (table-set! (get constants-table) (tid t) ks) ks))))))

"The conjuncts of pc whose constants all have few values, remembered for
each and: a path's condition is an and of the one before, so each join
looks only at what is new."
(define conjuncts-table (ref (table int rf-vals @rf) @rf) (new (the (table int rf-vals @rf) (make-table id-hash id-same?))))
(define few-valued-conjuncts (subr rf-st (rf-value) rf-vals)
  (lambda (pc)
    (cond ((not (rf-term? pc)) nil)
          ((op? op-and pc)
           (if (table-has? (get conjuncts-table) (tid pc))
               (table-ref (get conjuncts-table) (tid pc) nil)
               ;; The longest list (that of the and before) last, so as not
               ;; to copy it.
               (let* ((lists (the (listof rf-vals acyclic) (map (lambda ((a rf-value)) (few-valued-conjuncts a)) (targs pc))))
                      (longest (letrec ((loop (subr rf-st ((listof rf-vals acyclic) rf-vals) rf-vals)
                                          (lambda (ls best)
                                            (cond ((null? ls) best)
                                                  ((> (list-length (car ls)) (list-length best)) (loop (cdr ls) (car ls)))
                                                  (else (loop (cdr ls) best))))))
                                 (loop lists nil)))
                      (cs (letrec ((loop (subr rf-st ((listof rf-vals acyclic)) rf-vals)
                                     (lambda (ls)
                                       (cond ((null? ls) longest)
                                             ((eq? (car ls) longest) (loop (cdr ls)))
                                             (else (vals-append (car ls) (loop (cdr ls))))))))
                            (loop lists))))
                 (begin (table-set! (get conjuncts-table) (tid pc) cs) cs))))
          ((every-few? (constants-of pc)) (list pc))
          (else nil))))
(define every-few? (subr rf-st (rf-vals) bool)
  (lambda (l) (or (null? l) (and (tagcase (values-of (car l)) (some v #t) (none u #f)) (every-few? (cdr l))))))
(define reset-machine-tables! (subr rf-st () unit)
  (lambda ()
    (begin (set constants-table (the (table int rf-vals @rf) (make-table id-hash id-same?)))
           (set conjuncts-table (the (table int rf-vals @rf) (make-table id-hash id-same?))))))

;;; ------------------------------------------------------------ splitting

(define save-split-state (subr rf-st () split-state)
  (lambda ()
    (product (trail (get trail)) (split-pc (get split-pc)) (assumptions (session-assumptions))
             (branches (session-branches)) (source (get source)) (calls (get calls)))))

(define restore-split-state! (subr rf-st (split-state) unit)
  (lambda (state)
    (let ((to (tagcase (extract state trail) (some t t) (none u nil))))
      (begin
        (letrec ((loop (subr rf-st () unit)
                   (lambda ()
                     (let ((t (tagcase (get trail) (some t t) (none u nil))))
                       (if (or (eq? t to) (null? t)) #u
                           (let ((w (car t)))
                             (begin (array-set! (extract w vec) (extract w i) (extract w val))
                                    (set trail (sum some (cdr t)))
                                    (loop))))))))
          (loop))
        (set split-pc (extract state split-pc))
        (set (extract (get current) assumptions) (extract state assumptions))
        (set (extract (get current) branches) (extract state branches))
        (set source (extract state source))
        (set calls (extract state calls))))))

"A join that splits: the rest of the proof, up to its prompt, is kept, and
run for each arm, the first now."
(define split (subr rf-eff (rf-ctx arms) rf-value)
  (lambda (ctx arms)
    (begin
      (tagcase (get trail) (none u (set trail (sum some nil))) (some t #u))
      ((proj (proj call-with-composable-continuation @rk) rf-value rf-signal (maxeff rf-eff) rf-value (maxeff rf-eff))
       (lambda ((k rf-kont))
         (begin
           (set splits (cons (product (arms (new arms)) (k k) (state (save-split-state)) (ctx ctx)) (get splits)))
           ;; If every arm aborts, so does the path.
           (if (next-arm!) rf-unspecified (begin (abort-path) rf-unspecified))))
       rf-tag))))

"Go on with the next arm of the innermost split with arms left: the rest
of the proof is run with its value, and then the arm is finished (a
signal). #f if there is none."
(define next-arm! (subr rf-eff () bool)
  (lambda ()
    (if (null? (get splits)) #f
        (let* ((s (car (get splits)))
               (arms (get (extract s arms))))
          (if (null? arms)
              (begin (set splits (cdr (get splits))) (next-arm!))
              (begin
                (set (extract s arms) (cdr arms))
                (restore-split-state! (extract s state))
                (let* ((g (extract (car arms) g))
                       (ctx (extract s ctx))
                       (pc (if (ruled-out? (t-and (get split-pc) (ctx-pc ctx)) g)
                               rf-false
                               (t-and3 (get split-pc) (ctx-pc ctx) g))))
                  (if (rf-false? pc)
                      (next-arm!)
                      (begin
                        (set split-pc (t-and (get split-pc) g))
                        (let ((o (catch-abort (lambda () ((extract (car arms) k) (make-ctx (ctx-pc ctx) (+ (ctx-depth ctx) 1) (ctx-unwind ctx)))))))
                          (if (extract o aborted)
                              (next-arm!)
                              (let ((answer ((extract s k) (extract o value))))
                                (begin (rf-signal! (sum finished answer)) #t)))))))))))))

"After the evaluation of a proof's body (or its path's end): go on with
the arms of splits left, each under a prompt of its own."
(define finish-splits! (subr rf-eff () unit)
  (lambda ()
    (begin
      (letrec ((loop (subr rf-eff () unit)
                 (lambda ()
                   (let ((more (rf-catch (lambda () (if (next-arm!) rf-true rf-false))
                                         (lambda ((s rf-signal))
                                           (tagcase s (abort u rf-true) (finished v rf-true) (err e (rf-signal! s)))))))
                     (if (rf-true? more) (loop) #u)))))
        (loop))
      (set trail (sum none #u))
      (set split-pc rf-true))))

;;; ------------------------------------------------------------ exceptions

(define tagged? (subr rf-st (handler) bool)
  (lambda (h) (tagcase h (catcher c (tagcase (extract c tag) (some t #t) (none u #f))) (else x #f))))

"(thunk), with slot i of vec to be put back to old if a raise leaves it."
(define rewinding (subr rf-eff (rf-slots int rf-value (subr rf-eff () rf-value)) rf-value)
  (lambda (vec i old thunk)
    (let ((saved (get winds)))
      (begin
        (set winds (cons (product (vec vec) (i i) (val old)) saved))
        (let ((r (rf-protect thunk (lambda () (set winds saved)))))
          (begin (set winds saved) r))))))

"store as unwinding from here to a guard whose winds were base leaves it."
(define unwound (subr rf-st (slot-entries slot-entries) slot-entries)
  (lambda (store base)
    (letrec ((loop (subr rf-st (slot-entries slot-entries) slot-entries)
               (lambda (ws store)
                 (if (or (null? ws) (eq? ws base)) store
                     (let ((w (car ws)))
                       (loop (cdr ws)
                             (cons w (letrec ((drop (subr rf-st (slot-entries) slot-entries)
                                                (lambda (es)
                                                  (cond ((null? es) nil)
                                                        ((and (eq? (extract (car es) vec) (extract w vec)) (= (extract (car es) i) (extract w i))) (cdr es))
                                                        (else (cons (car es) (drop (cdr es))))))))
                                       (drop store)))))))))
      (loop (get winds) store))))

"Raise v where condition holds (#t: wherever this is reached), as raise or,
if continuable?, raise-continuable. What a handler gave a
raise-continuable; ends the path where it raised."
(define raise! (subr rf-eff (rf-ctx rf-value bool rf-value) rf-value)
  (lambda (ctx v continuable? condition)
    (let* ((where (t-and (path ctx) condition))
           ;; The call/cc catchers in front go: a raise is not for them.
           (passed (letrec ((loop (subr rf-st (handler-list handler-list) handler-list)
                              (lambda (hs acc) (if (and (pair? hs) (tagged? (car hs))) (loop (cdr hs) (cons (car hs) acc)) acc))))
                     (loop (get handlers) nil)))
           (hs (drop-handlers (get handlers) (list-length passed))))
      (cond ((rf-false? where) rf-unspecified)
            ((or (null? hs) (tagcase (car hs) (barrier l #t) (else x #f)))
             ;; Not caught: a failure, of kind error for an error object
             ;; (and anything, with no barrier).
             (begin
               (for-each (lambda ((m rf-member))
                           (begin
                             (cond ((error-value? (extract m v))
                                    (record! 'error (rf-str-of (error-value-label (extract m v))) where (extract m g)))
                                   ((null? hs)
                                    (record! 'error (string-append "uncaught raise: " ((get describe) (extract m v))) where (extract m g)))
                                   (else
                                    (record! 'contract (tagcase (car hs) (barrier l l) (else x "")) where (extract m g))))
                             (add-assumption! (t-not (extract m g)))))
                         (guarded-members where v))
               (if (rf-true? condition) (abort-path) #u)
               rf-unspecified))
            (else
             (tagcase (car hs)
               (catcher c
                 (begin
                   (for-each (lambda ((h handler)) (tagcase h (catcher p (set (extract p crossed) (t-or (get (extract p crossed)) where))) (else x #u)))
                             passed)
                   (catch! ctx c where v condition)))
               (else x
                 (if (rf-true? condition)
                     (call-handler* ctx v continuable? hs)
                     (join ctx (list (make-arm condition (lambda ((ctx rf-ctx)) (call-handler* ctx v #f hs)))
                                     (make-arm (t-not condition) (lambda ((ctx rf-ctx)) rf-unspecified)))
                           #f)))))))))
(define drop-handlers (subr rf-st (handler-list int) handler-list)
  (lambda (l n) (if (or (null? l) (<= n 0)) l (drop-handlers (cdr l) (- n 1)))))

"Note that v was raised (or escaped) to catcher c where it holds, and
escape the path there."
(define catch! (subr rf-eff (rf-ctx catcher rf-value rf-value rf-value) rf-value)
  (lambda (ctx c where v condition)
    (begin
      (set (extract c raises)
           (cons (product (cond where) (raised v) (store (unwound (store-since (extract c base)) (extract c winds))))
                 (get (extract c raises))))
      (set escaped (t-or (get escaped) where))
      ;; With condition #t, nothing of the path is left.
      (if (or (rf-true? condition) (rf-false? (path ctx))) (abort-path) #u)
      rf-unspecified)))

"Escape to the call/cc of tag with v: the catchers in between are crossed."
(define escape! (subr rf-eff (rf-ctx (ref unit @rf) rf-value) rf-value)
  (lambda (ctx tag v)
    (let ((where (path ctx)))
      (letrec ((loop (subr rf-eff (handler-list handler-list) rf-value)
                 (lambda (hs passed)
                   (cond ((null? hs)
                          (begin (check! ctx 'unsupported "calling a continuation after its call/cc returned" rf-false) rf-unspecified))
                         (else
                          (tagcase (car hs)
                            (barrier l (begin (check! ctx 'unsupported "a continuation called inside a contract's procedure, from outside it" rf-false)
                                              rf-unspecified))
                            (catcher c
                              (if (tagcase (extract c tag) (some t (eq? t tag)) (none u #f))
                                  (begin
                                    (for-each (lambda ((h handler)) (tagcase h (catcher p (set (extract p crossed) (t-or (get (extract p crossed)) where))) (else x #u)))
                                              passed)
                                    (catch! ctx c where v rf-true))
                                  (loop (cdr hs) (cons (car hs) passed))))
                            (else x (loop (cdr hs) passed))))))))
        (loop (get handlers) nil)))))

"Call the innermost handler, a procedure, with the handlers outside it in
force. A raise that is not continuable raises again if it returns."
(define call-handler* (subr rf-eff (rf-ctx rf-value bool handler-list) rf-value)
  (lambda (ctx v continuable? from)
    (let ((saved (get handlers)))
      (begin
        (set handlers (cdr from))
        (let ((r (rf-protect
                  (lambda ()
                    (let ((r ((get apply-proc) ctx (tagcase (car from) (proc p p) (else x rf-unspecified)) (list v) (rf-list1 (rf-sym 'raise)))))
                      (if continuable? r
                          (raise! ctx (make-error-value (rf-str "handler returned") (rf-list1 v) (rf-str "a handler returned from a raise"))
                                  #f rf-true))))
                  (lambda () (set handlers saved)))))
          (begin (set handlers saved) r))))))

"The slots written since outer-logs was base, with their values now."
(define store-since (subr rf-st ((listof maybe-log acyclic)) slot-entries)
  (lambda (base)
    (letrec ((up (subr rf-st ((listof maybe-log acyclic)) (listof maybe-log acyclic))
               (lambda (l) (if (or (eq? l base) (null? l)) nil (cons (car l) (up (cdr l))))))
             (loop (subr rf-st ((listof maybe-log acyclic) slot-entries) slot-entries)
               (lambda (logs acc)
                 (if (null? logs) acc
                     (loop (cdr logs)
                           (letrec ((add (subr rf-st (slot-entries slot-entries) slot-entries)
                                      (lambda (entries acc)
                                        (cond ((null? entries) acc)
                                              ((slot-in? (car entries) acc) (add (cdr entries) acc))
                                              (else (let ((vec (extract (car entries) vec)) (i (extract (car entries) i)))
                                                      (add (cdr entries) (cons (product (vec vec) (i i) (val (array-ref vec i))) acc))))))))
                             (add (log-entries (car logs)) acc)))))))
      (loop (cons (session-log) (up (get outer-logs))) nil))))

"The entry of list l for the slot entry e is about."
(define slot-in (subr rf-st (slot-entry slot-entries) (sumof (none unit) (some slot-entry)))
  (lambda (e l)
    (cond ((null? l) (sum none #u))
          ((and (eq? (extract (car l) vec) (extract e vec)) (= (extract (car l) i) (extract e i))) (sum some (car l)))
          (else (slot-in e (cdr l))))))
(define slot-in? (subr rf-st (slot-entry slot-entries) bool)
  (lambda (e l) (tagcase (slot-in e l) (some x #t) (none u #f))))

"A guard: (body ctx), and where it raised, (handle ctx v) with the raised
value v (merged, if several raises were caught). tag: a call/cc's, or
none."
(define catching (subr rf-eff (rf-ctx (subr rf-eff (rf-ctx) rf-value) (subr rf-eff (rf-ctx rf-value) rf-value) (sumof (none unit) (some (ref unit @rf)))) rf-value)
  (lambda (ctx body handle tag)
    (let* ((saved-escaped (get escaped))
           (saved-handlers (get handlers))
           (saved-log (session-log))
           (saved-outer (get outer-logs))
           (restore! (lambda ()
                       (begin (set handlers saved-handlers)
                              (set outer-logs saved-outer)
                              (set-session-log! saved-log)
                              (set escaped saved-escaped)))))
      (begin
        (set outer-logs (cons saved-log (get outer-logs)))
        (set-session-log! (sum some nil))
        (let ((c (the catcher (product (raises (new nil)) (base (get outer-logs)) (winds (get winds)) (tag tag) (crossed (new rf-false))))))
          (begin
            (set handlers (cons (sum catcher c) (get handlers)))
            (let* ((o (let* ((aborted (the (ref bool @rf) (new #f)))
                             (v (rf-catch (lambda () (body ctx))
                                          (lambda ((s rf-signal))
                                            (if (rf-abort? s) (begin (set aborted #t) rf-unspecified)
                                                (begin (restore!) (rf-signal! s)))))))
                        (the outcome (product (aborted (get aborted)) (value v)))))
                   (log (log-entries (session-log)))
                   (raises (the (listof raise-record acyclic) (reverse (get (extract c raises))))))
              (begin
                (restore!)
                ;; What went past it to a catcher outside stays escaped.
                (set escaped (t-or (get escaped) (get (extract c crossed))))
                ;; What the body wrote, logged as if written here.
                (tagcase (session-log)
                  (some outer
                    (set-session-log!
                     (sum some (letrec ((loop (subr rf-st (slot-entries slot-entries) slot-entries)
                                          (lambda (entries outer)
                                            (cond ((null? entries) outer)
                                                  ((slot-in? (car entries) outer) (loop (cdr entries) outer))
                                                  (else (loop (cdr entries) (cons (car entries) outer)))))))
                                 (loop log outer)))))
                  (none u #u))
                (if (null? raises)
                    (if (extract o aborted) (begin (abort-path) rf-unspecified) (extract o value))
                    (let* ((slots (letrec ((loop (subr rf-st ((listof raise-record acyclic) slot-entries) slot-entries)
                                             (lambda (rs acc)
                                               (if (null? rs) acc
                                                   (loop (cdr rs)
                                                         (letrec ((add (subr rf-st (slot-entries slot-entries) slot-entries)
                                                                    (lambda (es acc)
                                                                      (cond ((null? es) acc)
                                                                            ((slot-in? (car es) acc) (add (cdr es) acc))
                                                                            (else (add (cdr es) (cons (car es) acc)))))))
                                                           (add (extract (car rs) store) acc)))))))
                                    (loop raises log)))
                           (caught (t-or* (map (lambda ((r raise-record)) (extract r cond)) raises)))
                           (body-arm (if (extract o aborted) (the arms nil)
                                         (the arms (list (make-arm (t-not caught) (lambda ((ctx rf-ctx)) (extract o value))))))))
                      (join ctx
                            (the arms (append body-arm
                                    (list (make-arm caught
                                                   (lambda ((ctx rf-ctx))
                                                        (begin
                                                          ;; The store as each raise left it.
                                                          (for-each
                                                           (lambda ((slot slot-entry))
                                                             (let* ((vec (extract slot vec)) (i (extract slot i))
                                                                    (before (tagcase (slot-in slot log) (some e (extract e val)) (none u (array-ref vec i)))))
                                                               (store! vec i
                                                                       (merge-members
                                                                        (map (lambda ((r raise-record))
                                                                               (member (extract r cond)
                                                                                       (tagcase (slot-in slot (extract r store)) (some e (extract e val)) (none u before))))
                                                                             raises)))))
                                                           slots)
                                                          (handle ctx (merge-members (map (lambda ((r raise-record)) (member (extract r cond) (extract r raised))) raises)))))))))
                            #f)))))))))))

"(thunk) with handler proc in force (with-exception-handler)."
(define with-handler (subr rf-eff (rf-value (subr rf-eff () rf-value)) rf-value)
  (lambda (proc thunk)
    (let ((saved (get handlers)))
      (begin
        (set handlers (cons (sum proc proc) saved))
        (let ((r (rf-protect thunk (lambda () (set handlers saved)))))
          (begin (set handlers saved) r))))))

"(thunk), where a raise not caught inside it fails a check labelled label."
(define barrier (subr rf-eff (string (subr rf-eff () rf-value)) rf-value)
  (lambda (label thunk)
    (let ((saved (get handlers)))
      (begin
        (set handlers (list (sum barrier label)))
        (let ((r (rf-protect thunk (lambda () (set handlers saved)))))
          (begin (set handlers saved) r))))))

"(k ctx member) for each member of union u, under its guard."
(define join-union (subr rf-eff (rf-ctx rf-value (subr rf-eff (rf-ctx rf-value) rf-value)) rf-value)
  (lambda (ctx u k)
    (join ctx (map (lambda ((m rf-member)) (make-arm (extract m g) (lambda ((ctx rf-ctx)) (k ctx (extract m v)))))
                   (union-members u))
          #f)))
