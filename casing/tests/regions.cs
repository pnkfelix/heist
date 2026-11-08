;; Regions: a relation that changes may say the region it changes in, and
;; an event may write a region (every relation in it) as well as relations.
(sig Lamp (on Lamp #:lone #:var @lamp) (level Lamp #:set #:var @lamp))
(sig Door (open Door #:lone #:var @door))
(sig Guest #:var @door)                     ; who is in: changes with the door
(event (switch (l Lamp)) #:writes @lamp
  (and (= (join l (prime on)) l) (some (join l (prime level)))))
(event (enter) #:writes @door
  (some (diff (prime Guest) Guest)))
(event (prop (l Lamp) (d Door)) #:writes (@lamp open)   ; a region and a relation
  (and (= (join d (prime open)) d) (no (join l (prime on)))))
(fact (no on) (no level) (no open) (no Guest))
(fact (always (or (stutter) (enter) (some ((l Lamp)) (switch l))
                  (some ((l Lamp) (d Door)) (prop l d)))))
;; switching leaves the door's region as it was: no counterexample
(assert switch-alone (always (all ((l Lamp)) (implies (switch l) (unchanged @door)))))
(check switch-alone (Lamp 1) (Door 1) (Guest 2) (steps 1 3))
;; entering leaves the lamp's region as it was: no counterexample
(assert enter-alone (always (implies (enter) (unchanged @lamp))))
(check enter-alone (Lamp 1) (Door 1) (Guest 2) (steps 1 3))
;; propping a door open may change the lamp's level, though not the guests
(assert prop-dims (always (all ((l Lamp) (d Door)) (implies (prop l d) (unchanged level)))))
(check prop-dims (Lamp 1) (Door 1) (Guest 1) (steps 1 3))
(pred (party) (eventually (and (some on) (some Guest) (some open))))
(run party (Lamp 1) (Door 1) (Guest 1) (steps 1 4))
