-- casing/tests/light.cs in Alloy. casing's events leave unchanged every
-- relation that changes and that they do not write; here each says so.
sig Light { var on: lone Light }
one sig Switch { var pressed: set Light }
pred toggle[l: Light] {
  (some l.on implies no l.on' else l.on' = l)
  pressed' = pressed }
pred press[l: Light] {
  pressed' = pressed + Switch -> l
  on' = on }
pred stutter { on' = on and pressed' = pressed }
fact { no on }
fact { no pressed }
fact { always (stutter or some l: Light | toggle[l] or press[l]) }
assert staysOff { always no on }
--# 1
check staysOff for 3 but 1 Light, 1..4 steps
assert onOnce { all l: Light | eventually some l.on }
--# 2
check onOnce for 3 but 1 Light, 1..3 steps
pred blink { eventually some on and eventually no on and always eventually some on }
--# 3
run blink for 3 but 1 Light, 1..4 steps
