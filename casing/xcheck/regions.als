-- casing/tests/regions.cs in Alloy. Regions are casing's: here each
-- event says what it leaves unchanged. (open is Alloy's keyword: opened.)
sig Lamp { var on: lone Lamp, var level: set Lamp }
sig Door { var opened: lone Door }
var sig Guest {}
pred switch[l: Lamp] { l.on' = l and some l.level'
                       opened' = opened and Guest' = Guest }
pred enter { some Guest' - Guest           -- writes @door: Guest and opened
             on' = on and level' = level }
pred prop[l: Lamp, d: Door] { d.opened' = d and no l.on'
                              Guest' = Guest }
pred stutter { on' = on and level' = level and opened' = opened and Guest' = Guest }
fact { no on and no level and no opened and no Guest }
fact { always (stutter or enter or (some l: Lamp | switch[l])
               or (some l: Lamp, d: Door | prop[l, d])) }
assert switchAlone { always all l: Lamp | switch[l] implies (opened' = opened and Guest' = Guest) }
--# 1
check switchAlone for 3 but 1 Lamp, 1 Door, 2 Guest, 1..3 steps
assert enterAlone { always (enter implies (on' = on and level' = level)) }
--# 2
check enterAlone for 3 but 1 Lamp, 1 Door, 2 Guest, 1..3 steps
assert propDims { always all l: Lamp, d: Door | prop[l, d] implies level' = level }
--# 3
check propDims for 3 but 1 Lamp, 1 Door, 1 Guest, 1..3 steps
pred party { eventually (some on and some Guest and some opened) }
--# 4
run party for 3 but 1 Lamp, 1 Door, 1 Guest, 1..4 steps
