------------------------- MODULE CompositionTheorem -------------------------
EXTENDS CStruct
CONSTANTS L
VARIABLES learned1, prop1, from1, fromto, 
    learned2, prop2, to2
vars == <<learned1, prop1, from1, fromto, 
    learned2, prop2, to2>>
vars1 == <<learned1, prop1, from1, fromto>>
vars2 == <<learned2, prop2, fromto, to2>>
CGC1 == INSTANCE ComposableGC WITH
    learned <- learned1, prop <- prop1,
    from <- from1, to <- fromto
CGC2 == INSTANCE ComposableGC WITH
    learned <- learned2, prop <- prop2,
    from <- fromto, to <- to2
CGC == INSTANCE ComposableGC WITH
    learned <- [l \in L |-> learned1[l] \cup learned2[l]],
    prop <- prop1 \cup prop2, from <- from1, to <- to2
Init == CGC1!Init /\ CGC2!Init
Next == 
    \/ CGC1!Next /\ UNCHANGED <<vars2, fromto>>
    \/ CGC2!Next /\ UNCHANGED <<vars1, fromto>>
    \/ CGC1!Abort /\ CGC2!InitM
THEOREM Init /\ [][Next /\ from1' \subseteq {Bottom}]_vars => CGC!Spec
=============================================================================
\* Modification History
\* Last modified Sun Jan 10 22:34:46 EST 2016 by nano
\* Created Sun Jan 10 20:38:24 EST 2016 by nano
