;;; playback.fx: concrete playback of counterexamples, as in Kani:
;;; shakedown's `(shakedown playback)`. (Being ported: for now it writes
;;; nothing, and runs nothing.)

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
                    (m-eval (load-moduleof "eval.fx" m-core m-term m-value m-print m-syntax m-numbers m-reader m-machine m-prims m-hashtables m-ports m-prelude m-library))))

"Write the playback program for a failure."
(define write-playback! (subr rf-eff (string rf-vals (listof loaded-library acyclic) symbol rf-value strings rf-vals) unit)
  (lambda (path forms libraries proof-name proof-library header values) #u))
"Run the playback program at path; its last line starting \"playback: \",
or \"\"."
(define run-playback (subr rf-eff (string) string) (lambda (path) ""))

"The Larceny that runs playback programs (bin/ratfink passes $LARCENY)."
(define larceny-command (ref string @rf) (new "larceny"))
(define set-larceny! (subr rf-st (string) unit) (lambda (c) (set larceny-command c)))
