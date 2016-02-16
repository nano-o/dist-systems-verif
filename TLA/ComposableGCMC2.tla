-------------------------- MODULE ComposableGCMC2 --------------------------

EXTENDS Diamond2

CONSTANTS Learner

VARIABLES learned1, propCmd1, fromPrev1, toNext1, 
    learned2, propCmd2, fromPrev2, toNext2

vars == <<learned1, propCmd1, fromPrev1, toNext1, 
    learned2, propCmd2, fromPrev2, toNext2>>
vars1 == <<learned1, propCmd1, fromPrev1, toNext1>>
vars2 == <<learned2, propCmd2, fromPrev2, toNext2>>


CGC1 == INSTANCE ComposableGC WITH
    learned <- learned1,
    propCmd <- propCmd1,
    fromPrev <- fromPrev1,
    toNext <- toNext1

CGC2 == INSTANCE ComposableGC WITH
    learned <- learned2,
    propCmd <- propCmd2,
    fromPrev <- fromPrev2,
    toNext <- toNext2

INSTANCE CStruct

NoneToBot(s) == IF s = none THEN Bottom ELSE s

GC == INSTANCE GeneralizedConsensus WITH
    propCmd <- propCmd1 \union propCmd2,
    learned <- [l \in Learner |-> NoneToBot(learned1[l]) \sqcup NoneToBot(learned2[l])]

Init == CGC1!Init /\ CGC2!Init

Next == 
    \/  CGC1!Next /\ UNCHANGED <<vars2, toNext1>>
    \/  CGC2!Next /\ UNCHANGED <<vars1, fromPrev2>>
    \/  /\  CGC1!ToNext 
        /\  CGC2!FromPrev
        /\  toNext1' = fromPrev2'

Spec == Init /\ [][Next /\ fromPrev1' \subseteq {Bottom}]_vars

=============================================================================
\* Modification History
\* Last modified Wed Nov 11 18:43:04 EST 2015 by nano
\* Created Wed Nov 11 18:22:38 EST 2015 by nano
