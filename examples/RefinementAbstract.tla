---- MODULE RefinementAbstract ----

EXTENDS Naturals

VARIABLES x, y

vars == <<x, y>>

Init ==
    /\ x = 0
    /\ y = 0

Next ==
    /\ x' = x + 1
    /\ y' = y + 1

Spec == Init /\ [][Next]_vars

===================================
