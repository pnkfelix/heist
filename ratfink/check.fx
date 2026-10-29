;;; check.fx: checking the proofs of a program, and reporting: shakedown's
;;; `(shakedown check)`.
;;;
;;; Each proof is evaluated symbolically (a session of its own), and then
;;; each of its checks is put to the solver, in the order they were made.
;;; The assumptions only grow, so they are asserted once each, and each
;;; check is a push, its condition, check-sat and a pop.
;;;
;;; A check's status, as in Kani: SUCCESS, FAILURE (the solver's model is a
;;; counterexample), UNREACHABLE, UNDETERMINED, and for (cover e) SATISFIED
;;; or UNSATISFIABLE. A proof passes if it has no FAILURE and no
;;; UNDETERMINED.
;;;
;;; A proof's body runs under a prompt of rf-tag, up to which a split
;;; captures the rest of the proof (machine.fx).

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
                    (m-library (load-moduleof "library.fx" m-core m-print m-syntax m-numbers m-reader))
                    (m-smt (load-moduleof "smt.fx" m-core m-term m-print m-numbers m-reader))
                    (m-eval (load-moduleof "eval.fx" m-core m-term m-value m-print m-syntax m-numbers m-reader m-machine m-prims m-hashtables m-ports m-prelude m-library))
                    (m-playback (load-moduleof "playback.fx" m-core m-term m-value m-print m-syntax m-numbers m-reader m-machine m-prims m-hashtables m-ports m-prelude m-library m-eval))))

(hide (define kit-lists (load-module "../kit/lists.fx"))
      (import kit-lists map map2 for-each filter))
(hide (define kit-strings (load-module "../kit/strings.fx"))
      (import kit-strings string-pad-right))

"The options of check-forms, with shakedown's defaults: unwind 10,
timeout 10 (-1: none), playback \"\" (none), library-path (\".\"), proofs
none (all), split #f, max-calls 10000000, solver z3."
(define-type check-options
  (productof (unwind int) (timeout int) (verbose bool) (playback string) (library-path strings)
             (proofs (sumof (none unit) (some symbols))) (split bool) (max-calls int) (solver symbol)))
(define default-options check-options
  (product (unwind 10) (timeout 10) (verbose #f) (playback "") (library-path (list ".")) (proofs (sum none #u))
           (split #f) (max-calls 10000000) (solver 'z3)))

"What a report is written to."
(define-type writer (subr rf-eff (string) unit))

"A solver of the kind named: z3 (a process) or combo (in this process;
set by solver-combo.fx when it is linked in)."
(define combo-solver-maker (ref (sumof (none unit) (some (subr rf-eff (int) solver))) @rf) (new (sum none #u)))
(define set-combo-solver-maker! (subr rf-st ((subr rf-eff (int) solver)) unit) (lambda (f) (set combo-solver-maker (sum some f))))
(define start-solver (subr rf-eff (int symbol) solver)
  (lambda (timeout name)
    (if (eq? name 'z3) (start-z3 timeout)
        (tagcase (get combo-solver-maker)
          (some f (f timeout))
          (none u (begin (rf-error "ratfink: no in-process solver linked in" nil) (start-z3 timeout)))))))

"A check's outcome: the obligation, its status, the model of its constants,
the values for playback, and the trace (each branch's source and value)."
(define-type model-entry (productof (k rf-value) (v rf-value)))
(define-type model (listof model-entry acyclic))
(define-type trace-entry (productof (source rf-value) (value rf-value)))
"An input of a proof, as its value in a model is written."
(define-type input-text (productof (name rf-value) (text string)))
(define-type result
  (productof (ob obligation) (status symbol) (model model) (values rf-vals) (trace (listof trace-entry acyclic)) (has-trace bool)
             (inputs (listof input-text acyclic))))

"Check the proofs in a program's forms, writing a report with out. The
number of proofs that did not pass, or -1 if there were none."
(define check-forms (subr rf-eff (rf-vals writer check-options) int)
  (lambda (forms out options)
    (begin
      (set-library-path! (extract options library-path))
      (set-max-calls! (extract options max-calls))
      (if (string=? (extract options playback) "") #u (make-directory (extract options playback)))
      (check-program forms options out))))

(define make-directory (subr rf-eff (string) unit)
  (lambda (dir)
    (tagcase (process-start (list "mkdir" "-p" dir) "")
      (started id (letrec ((wait (subr rf-eff () unit)
                             (lambda () (tagcase (process-status id) (running u (begin (process-output id) (sleep-until (i64+ (clock) (int->i64 1000000))) (wait))) (else x #u)))))
                    (wait)))
      (failed e #u))))

(define selected (subr rf-eff (check-options) proofs)
  (lambda (options)
    (tagcase (extract options proofs)
      (none u (all-proofs))
      (some only
        (let ((ps (filter (lambda ((p proof)) (symbols-member? (extract p name) only)) (all-proofs))))
          (begin
            (for-each (lambda ((name symbol))
                        (if (symbols-member? name (map (lambda ((p proof)) (extract p name)) ps)) #u
                            (rf-error "ratfink: no such proof" (list (rf-sym name)))))
                      only)
            ps))))))

(define check-program (subr rf-eff (rf-vals check-options writer) int)
  (lambda (forms options out)
    (begin
      (reset-globals!)
      (begin-session! (extract options unwind) #f)
      (rf-catch (lambda () (begin (load-program! forms (make-ctx rf-true 0 nil)) rf-unspecified))
                (lambda ((s rf-signal)) (if (rf-abort? s) rf-unspecified (rf-signal! s))))
      (let* ((top-level (session-obligations))
             (top-constants (session-constants))
             (solver (start-solver (extract options timeout) (extract options solver)))
             (failed (+ (if (null? top-level) 0
                            (report-proof "(top level)" (check-all solver top-level top-constants) (extract options verbose) (sum none #u) out))
                        (letrec ((loop (subr rf-eff (proofs int) int)
                                   (lambda (ps failed)
                                     (if (null? ps) failed
                                         (loop (cdr ps) (+ failed (run-proof solver (car ps) top-constants options forms out)))))))
                          (loop (selected options) 0)))))
        (begin
          ((extract solver stop!))
          (let ((n (+ (list-length (selected options)) (if (null? top-level) 0 1))))
            (if (= n 0)
                (begin (out "No proofs to check.\n") -1)
                (begin (out (string-append (int->string n) (if (= n 1) " proof, " " proofs, ") (int->string failed) " failed.\n"))
                       failed))))))))

"1 if the proof failed, else 0."
(define run-proof (subr rf-eff (solver proof rf-vals check-options rf-vals writer) int)
  (lambda (solver p top-constants options forms out)
    (begin
      (begin-session! (if (>= (extract p unwind) 0) (extract p unwind) (extract options unwind)) (or (extract options split) (extract p split)))
      (begin-proof-mode! (sum some p))
      (reset-proof-inputs!)
      (rf-catch (lambda () (begin (apply-value (make-ctx rf-true 0 nil) (extract p body) nil (rf-sym (extract p name))) rf-unspecified))
                (lambda ((s rf-signal)) (tagcase s (abort u rf-unspecified) (finished v rf-unspecified) (err e (rf-signal! s)))))
      (finish-splits!)
      (check-contract-use! p)
      ((extract solver reset!))
      (report-proof (symbol->string (extract p name))
                    (check-all solver (session-obligations) (vals-append top-constants (session-constants)))
                    (extract options verbose)
                    (if (string=? (extract options playback) "") (sum none #u)
                        (sum some (product (dir (extract options playback)) (forms forms) (proof (extract p name))
                                           (abstraction (proof-abstraction)) (libraries (loaded-libraries)) (library (extract p library)))))
                    out))))

"Failures in how a proof uses contracts."
(define check-contract-use! (subr rf-eff (proof) unit)
  (lambda (p)
    (let ((checked (the symbols (apply append (map (lambda ((q proof)) (tagcase (extract q for-contract) (some n (the symbols (list n))) (none u (the symbols nil)))) (all-proofs))))))
      (begin
        (for-each (lambda ((name symbol))
                    (cond ((not (contract-defined? name))
                           (record-failure! 'contract-frame (string-append (symbol->string name) " is used as a stub, but has no contract")))
                          ((not (symbols-member? name checked))
                           (record-failure! 'contract-frame (string-append (symbol->string name) " is used as a stub, but no proof"
                                                                           " checks its contract (for-contract " (symbol->string name) ")")))
                          (else #u)))
                  (extract p stubs))
        (tagcase (extract p for-contract)
          (some target
            (cond ((not (contract-defined? target)) (record-failure! 'contract-frame (string-append (symbol->string target) " has no contract")))
                  ((= 0 (proof-contract-calls)) (record-failure! 'contract-frame (string-append "the proof never calls " (symbol->string target))))
                  (else #u)))
          (none u #u))))))

"Each obligation with its status, model and the rest; constants are all
the constants made, in order."
(define check-all (subr rf-eff (solver obligations rf-vals) (listof result acyclic))
  (lambda (s obligations constants)
    (begin
      (for-each (lambda ((k rf-value)) ((extract s declare!) k)) constants)
      (letrec ((loop (subr rf-eff (obligations rf-vals (listof result acyclic) (table int symbol @rf)) (listof result acyclic))
                 (lambda (obs asserted acc reached)
                   (if (null? obs) (the (listof result acyclic) (reverse acc))
                       (let* ((ob (car obs))
                              (assumptions (extract ob assumptions))
                              ;; Whether a path condition can hold is remembered
                              ;; while the assumptions are the same.
                              (reached (if (eq? assumptions asserted) reached (new-reached))))
                         (begin
                           ;; Assert the assumptions made since the last check.
                           (letrec ((add (subr rf-eff (rf-vals) unit)
                                      (lambda (as) (if (or (eq? as asserted) (null? as)) #u
                                                       (begin (add (cdr as)) ((extract s assert!) (car as)))))))
                             (add assumptions))
                           (let ((r (check-one s ob constants reached)))
                             (loop (cdr obs) assumptions (cons r acc) reached))))))))
        (loop obligations nil nil (new-reached))))))
(define new-reached (subr rf-st () (table int symbol @rf)) (lambda () (the (table int symbol @rf) (make-table id-hash id-same?))))

"Whether pc can hold, with the assumptions asserted, remembered."
(define reachable? (subr rf-eff (solver rf-value (table int symbol @rf)) symbol)
  (lambda (s pc reached)
    (let ((key (if (rf-term? pc) (tid pc) (if (rf-true? pc) -1 -2))))
      (if (table-has? reached key) (table-ref reached key 'unknown)
          (let ((a (extract (satisfiable s pc nil) answer)))
            (begin (table-set! reached key a) a))))))

(define-type sat-answer (productof (answer symbol) (model model)))
"Whether formula can hold, with the assumptions asserted; and if so, the
values of the constants."
(define satisfiable (subr rf-eff (solver rf-value rf-vals) sat-answer)
  (lambda (s formula constants)
    (if (rf-false? formula) (product (answer 'unsat) (model nil))
        (begin
          ((extract s push!))
          ((extract s assert!) formula)
          (let* ((answer ((extract s check)))
                 (m (if (eq? answer 'sat)
                        (map2 (lambda ((k rf-value) (v rf-value)) (product (k k) (v v))) constants ((extract s values) constants))
                        nil)))
            (begin ((extract s pop!)) (product (answer answer) (model m))))))))

(define no-result-model model nil)
(define check-one (subr rf-eff (solver obligation rf-vals (table int symbol @rf)) result)
  (lambda (s ob constants reached)
    (let* ((kind (extract ob kind)) (condition (extract ob condition))
           (sa (satisfiable s condition constants))
           (answer (extract sa answer)) (m (extract sa model))
           (plain (lambda ((status symbol)) (the result (product (ob ob) (status status) (model nil) (values nil) (trace nil) (has-trace #f) (inputs nil)))))
           (with-model (lambda ((status symbol))
                         (let ((relevant (term-constants (cons condition (extract ob assumptions)))))
                           (the result (product (ob ob) (status status)
                                    (model (filter (lambda ((e model-entry)) (memq-val? (extract e k) relevant)) m))
                                    (values (playback-values constants m))
                                    (trace (trace ob m))
                                    (has-trace #t)
                                    (inputs (input-texts m))))))))
      (cond ((eq? kind 'cover)
             (if (eq? answer 'sat) (with-model 'satisfied) (plain (if (eq? answer 'unsat) 'unsatisfiable 'undetermined))))
            ((eq? answer 'sat) (with-model 'failure))
            ((eq? answer 'unknown) (plain 'undetermined))
            ((and (eq? kind 'assert) (eq? 'unsat (reachable? s (extract ob pc) reached))) (plain 'unreachable))
            (else (plain 'success))))))

"The proof's inputs, their values in a model written."
(define input-texts (subr rf-eff (model) (listof input-text acyclic))
  (lambda (m)
    (let ((value-of (model-value m)))
      (map (lambda ((i proof-input)) (product (name (extract i name)) (text ((get input-renderer) (concrete (extract i value) value-of) (extract i type)))))
           (get proof-inputs)))))
"A value as it is in a model."
(define concrete (subr rf-st (rf-value (subr rf-st (rf-value) rf-value)) rf-value)
  (lambda (v value-of)
    (tagcase v
      (term t (term-value v value-of (new-term-memo)))
      (choice t (term->symbol (term-value (sum term t) value-of (new-term-memo))))
      (union ms (letrec ((find (subr rf-st (rf-members) rf-value)
                           (lambda (l) (cond ((null? l) rf-unspecified)
                                             ((rf-true? (term-value (extract (car l) g) value-of (new-term-memo))) (concrete (extract (car l) v) value-of))
                                             (else (find (cdr l)))))))
                  (find ms)))
      (pair s (rf-cons (concrete (rf-car v) value-of) (concrete (rf-cdr v) value-of)))
      (vec s (sum vec (list->array (map (lambda ((e rf-value)) (concrete e value-of)) (slots-list s)))))
      (else x v))))

"A constant's value in a model (another is any value)."
(define model-value (subr rf-st (model) (subr rf-st (rf-value) rf-value))
  (lambda (m)
    (lambda ((k rf-value))
      (letrec ((find (subr rf-st (model) rf-value)
                 (lambda (l) (cond ((null? l) (if (bool-term? k) rf-false (rf-int 0)))
                                   ((rf-eqv? (extract (car l) k) k) (extract (car l) v))
                                   (else (find (cdr l)))))))
        (find m)))))

"The branches on the model's path to ob, in order."
(define trace (subr rf-eff (obligation model) (listof trace-entry acyclic))
  (lambda (ob m)
    (let ((value-of (model-value m)))
      (letrec ((loop (subr rf-eff (branches (listof trace-entry acyclic)) (listof trace-entry acyclic))
                 (lambda (bs acc)
                   (cond ((null? bs) acc)
                         ((rf-true? (term-value (extract (car bs) pc) value-of (new-term-memo)))
                          (loop (cdr bs) (cons (product (source (extract (car bs) source)) (value (term-value (extract (car bs) condition) value-of (new-term-memo)))) acc)))
                         (else (loop (cdr bs) acc))))))
        (loop (extract ob branches) nil)))))

"The values a concrete run asks for, in order."
(define playback-values (subr rf-eff (rf-vals model) rf-vals)
  (lambda (constants m)
    (let ((value-of (model-value m)))
      (filter-map-vals (lambda ((k rf-value)) (if (rf-true? (term-value (constant-pc k) value-of (new-term-memo))) (sum some (value-of k)) (sum none #u)))
                       constants))))
(define filter-map-vals (subr rf-eff ((subr rf-eff (rf-value) (sumof (none unit) (some rf-value))) rf-vals) rf-vals)
  (lambda (f l) (if (null? l) nil (tagcase (f (car l)) (some v (cons v (filter-map-vals f (cdr l)))) (none u (filter-map-vals f (cdr l)))))))

(define status-name (subr rf-st (symbol) string)
  (lambda (s)
    (cond ((eq? s 'success) "SUCCESS") ((eq? s 'failure) "FAILURE") ((eq? s 'unreachable) "UNREACHABLE")
          ((eq? s 'undetermined) "UNDETERMINED") ((eq? s 'satisfied) "SATISFIED") (else "UNSATISFIABLE"))))
(define kind-prefix (subr rf-st (symbol) string)
  (lambda (k)
    (cond ((or (eq? k 'assert) (eq? k 'cover)) "") ((eq? k 'error) "error: ") ((eq? k 'unwind) "unwinding: ")
          ((eq? k 'loop) "loop: ") ((eq? k 'unsupported) "unsupported: ") (else "contract: "))))
(define show-value (subr rf-eff (rf-value) string)
  (lambda (v) (cond ((rf-true? v) "#t") ((rf-false? v) "#f") (else (datum->string v)))))

"A kind and label, as reports key checks."
(define-type check-key (productof (status symbol) (kind symbol) (label string)))
(define key-member? (subr rf-st (symbol symbol string (listof check-key acyclic)) bool)
  (lambda (st kind label l)
    (and (pair? l) (or (and (eq? (extract (car l) status) st) (eq? (extract (car l) kind) kind) (string=? (extract (car l) label) label))
                       (key-member? st kind label (cdr l))))))

"Where to play back failures: the directory, the program, the proof, why
a playback is not available (\"\" if it is), the libraries, the proof's
library."
(define-type playback-info
  (productof (dir string) (forms rf-vals) (proof symbol) (abstraction string)
             (libraries (listof loaded-library acyclic)) (library rf-value)))

"1 if the proof failed, else 0."
(define report-proof (subr rf-eff (string (listof result acyclic) bool (sumof (none unit) (some playback-info)) writer) int)
  (lambda (name results verbose? playback out)
    (begin
      (out (string-append "proof " name ":\n"))
      ;; Checks that passed are reported once for each kind and label. A
      ;; check is unreachable, and a cover unsatisfiable, only if each check
      ;; of its kind and label is.
      (let ((failed (the (ref int @rf) (new 0))) (quiet (the (ref int @rf) (new 0))) (played (the (ref int @rf) (new 0)))
            (shown (the (ref (listof check-key acyclic) @rf) (new nil)))
            (reached (filter (lambda ((r result)) (not (or (eq? (extract r status) 'unreachable) (eq? (extract r status) 'unsatisfiable)))) results)))
        (begin
          (for-each
           (lambda ((r result))
             (let* ((ob (extract r ob)) (status (extract r status)) (kind (extract ob kind)) (label (extract ob label))
                    (once? (or (eq? status 'success) (eq? status 'unreachable) (eq? status 'unsatisfiable))))
               (begin
                 (if (or (eq? status 'failure) (eq? status 'undetermined)) (set failed (+ 1 (get failed))) #u)
                 (if (and (or verbose? (eq? kind 'assert) (eq? kind 'cover) (eq? kind 'contract) (not (eq? status 'success)))
                          (not (and once? (key-member? status kind label (get shown))))
                          (not (and (or (eq? status 'unreachable) (eq? status 'unsatisfiable))
                                    (letrec ((any (subr rf-st ((listof result acyclic)) bool)
                                                (lambda (l) (and (pair? l) (or (and (eq? (extract (extract (car l) ob) kind) kind)
                                                                                    (string=? (extract (extract (car l) ob) label) label))
                                                                               (any (cdr l)))))))
                                      (any reached)))))
                     (begin
                       (if once? (set shown (cons (product (status status) (kind kind) (label label)) (get shown))) #u)
                       (out (string-append "  " (string-pad-right (status-name status) 14 #\space) (kind-prefix kind) label "\n"))
                       (let ((at (if (eq? status 'success) "" (source-location (extract ob source)))))
                         (if (string=? at "") #u (out (string-append "      at " at "\n"))))
                       ;; A proof's inputs, as they are; then what else the
                       ;; model says, of constants not made for them.
                       (for-each (lambda ((i input-text)) (out (string-append "      " (datum->string (extract i name)) " = " (extract i text) "\n")))
                                 (extract r inputs))
                       (for-each (lambda ((e model-entry))
                                   (out (string-append "      " (let ((d (constant-description (extract e k)))) (if (has-description? (extract e k)) d "?"))
                                                       "  ->  " (show-value (extract e v)) "\n")))
                                 (if (null? (extract r inputs)) (extract r model)
                                     (filter (lambda ((e model-entry)) (not (memq-val? (extract e k) (get input-constants)))) (extract r model))))
                       (if (extract r has-trace) (write-trace (extract r trace) out) #u)
                       (tagcase playback
                         (some pb (if (and (eq? status 'failure) (or (eq? kind 'assert) (eq? kind 'error) (eq? kind 'contract)))
                                      (begin (set played (+ 1 (get played)))
                                             (play-back pb (get played) ob (extract r model) (extract r values) out))
                                      #u))
                         (none u #u)))
                     (set quiet (+ 1 (get quiet)))))))
           results)
          (if (> (get quiet) 0)
              (out (string-append "  (" (int->string (get quiet)) (if (= (get quiet) 1) " other check" " other checks") " passed)\n"))
              #u)
          (out (if (= 0 (get failed)) "  VERIFICATION SUCCESSFUL\n"
                   (string-append "  VERIFICATION FAILED (" (int->string (get failed)) (if (= (get failed) 1) " check" " checks") " failed)\n")))
          (if (= 0 (get failed)) 0 1))))))

"The branches to a failure: the last few, if there are many."
(define max-trace int 12)
(define write-trace (subr rf-eff ((listof trace-entry acyclic) writer) unit)
  (lambda (branches out)
    (if (null? branches) #u
        (let ((n (list-length branches)))
          (begin
            (out "      path:\n")
            (if (> n max-trace) (out (string-append "        (" (int->string (- n max-trace)) " branches before)\n")) #u)
            (for-each (lambda ((b trace-entry)) (out (string-append "        " (datum->string (extract b source)) "  ->  " (show-value (extract b value)) "\n")))
                      (drop-trace branches (max 0 (- n max-trace)))))))))
(define drop-trace (subr rf-st ((listof trace-entry acyclic) int) (listof trace-entry acyclic))
  (lambda (l k) (if (or (null? l) (<= k 0)) l (drop-trace (cdr l) (- k 1)))))

"Write and run the playback program for the nth failure reported in a
proof, and report whether the failure happened."
(define play-back (subr rf-eff (playback-info int obligation model rf-vals writer) unit)
  (lambda (pb n ob m values out)
    (let ((path (string-append (extract pb dir) "/" (symbol->string (extract pb proof)) "-" (int->string n) ".scm")))
      (if (not (string=? (extract pb abstraction) ""))
          (out (string-append "      playback: not available: " (extract pb abstraction) "\n"))
          (begin
            (write-playback! path (extract pb forms) (extract pb libraries) (extract pb proof) (extract pb library)
                             (append (list (string-append "proof: " (symbol->string (extract pb proof)))
                                           (string-append "check: " (kind-prefix (extract ob kind)) (extract ob label))
                                           "counterexample:")
                                     (map (lambda ((e model-entry))
                                            (string-append "  " (if (has-description? (extract e k)) (constant-description (extract e k)) "?")
                                                           "  ->  " (show-value (extract e v))))
                                          m))
                             values)
            (let* ((line (run-playback path))
                   (expected (string-append "playback: FAILED " (extract ob label))))
              (out (string-append "      playback: " path ": "
                                  (cond ((string=? line "") "did not finish (see the program's output)")
                                        ((string=? line expected) "the failure happens")
                                        ((and (eq? (extract ob kind) 'error) (string-prefix? "playback: FAILED error: " line)) "the failure happens")
                                        (else (string-append "NOT REPRODUCED -- " line)))
                                  "\n"))))))))
(define string-prefix? (subr rf-st (string string) bool)
  (lambda (prefix s) (and (>= (string-length s) (string-length prefix)) (string=? (substring s 0 (string-length prefix)) prefix))))
