-------------------------- MODULE ComposableGCMC1 --------------------------

EXTENDS Diamond2

CONSTANTS Learner

VARIABLES learned, propCmd, fromPrev, toNext

CGC == INSTANCE ComposableGC

GC == INSTANCE GeneralizedConsensus WITH
    learned <- [l \in Learner |-> IF learned[l] = CGC!none THEN Bottom ELSE learned[l]]

Spec == CGC!Init /\ [][CGC!Next /\ fromPrev' \subseteq {Bottom}]_<<learned,propCmd,fromPrev,toNext>>
    


=============================================================================
\* Modification History
\* Last modified Wed Nov 11 18:22:15 EST 2015 by nano
\* Created Wed Nov 11 17:55:52 EST 2015 by nano
