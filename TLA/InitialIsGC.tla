---------------------------- MODULE InitialIsGC ----------------------------
EXTENDS CStruct
CONSTANTS L
VARIABLES prop, learned, cgcLearned, from, to
vars == <<prop, learned, cgcLearned, from, to>>
CGC == INSTANCE ComposableGC 
    WITH learned <- cgcLearned
GC == INSTANCE GeneralizedConsensus
Next == 
    \/ /\ CGC!InitM /\ from' \subseteq {Bottom} 
       /\ UNCHANGED cgcLearned
    \/ CGC!Propose /\ UNCHANGED cgcLearned
    \/ CGC!Abort /\ UNCHANGED cgcLearned
    \/ \E l \in L : CGC!Learn(l) /\ cgcLearned' = 
        [cgcLearned EXCEPT ![l] = @ \sqcup learned[l]']  
Spec == CGC!Init /\ [][CGC!Next]_vars
THEOREM Spec => GC!Spec
=============================================================================
\* Modification History
\* Last modified Sun Jan 10 22:49:31 EST 2016 by nano
\* Created Sun Jan 10 22:37:20 EST 2016 by nano
