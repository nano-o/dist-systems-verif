------------------------ MODULE GeneralizedConsensus ------------------------

EXTENDS CStruct

CONSTANT L

VARIABLES prop, learned

TypeInv ==
    /\  prop \subseteq Cmd
    /\  learned \in [L -> CStruct]

Init ==
    /\  prop = {}
    /\  learned = [l \in L |-> Bottom]

Propose ==
    \E c \in Cmd \ prop :
        /\  prop' = prop \union {c}
        /\  UNCHANGED learned

Learn(l) ==
    /\  \E s \in Str(prop) :
            /\  \A r \in L : Compat(s, learned[l])
            /\  learned[l] \preceq s
            /\  learned' = [learned EXCEPT ![l] = s]
    /\  UNCHANGED prop

Next == Propose \/ \E l \in L : Learn(l)

Spec == Init /\ [][Next]_<<prop, learned>>

NonTriviality == \A l \in L : [](learned[l] \in Str(prop))
Stability == \A l \in L, s \in CStruct :
    [](learned[l] = s => [](s \preceq learned[l]))
Consistency ==
    \A l1,l2 \in L :
        []Compat(learned[l1], learned[l2])

THEOREM Spec => ([]TypeInv) /\ NonTriviality /\ Stability /\ Consistency

=============================================================================
\* Modification History
\* Last modified Sun Jan 10 22:39:23 EST 2016 by nano
\* Created Wed Nov 11 14:43:37 EST 2015 by nano
