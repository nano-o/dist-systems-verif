---------------------------- MODULE ComposableGC ----------------------------
EXTENDS CStruct
CONSTANTS L
VARIABLES prop, learned, from, to
Init == prop = {} /\ from = {} /\ to = {}
    /\ learned = [l \in L |-> {}]
Propose == \E c \in Cmd : prop' = prop \union {c}
    /\ UNCHANGED <<learned, from, to>>
Valid == { t  \star  cs : cs \in Seq(prop), 
    t \in {GLB(T) : T \in SUBSET from }}
Learn(l) == \E s \in Valid : 
    /\ \A s2 \in to : s \preceq s2 /\ from # {} 
    /\ \A r \in L : \A s2 \in learned[r] : Compat(s, s2)
    /\ learned' = [learned EXCEPT ![l] = @ \cup {s}]
    /\ UNCHANGED <<prop, from, to>>
InitM == \E s \in CStruct : from' = from \union {s} 
    /\ UNCHANGED <<prop, learned, to>>
Abort == \E s \in Valid : to' = to \union {s}
    /\ \A l \in L : \A s2 \in learned[l] : s2 \preceq s
    /\ UNCHANGED <<from, prop, learned>>
Next == Propose \/ InitM \/ Abort\/ \E l \in L : Learn(l)
Spec == Init /\ [][Next]_<<from, prop, learned, to>>
=============================================================================
\* Modification History
\* Last modified Sun Jan 10 21:45:55 EST 2016 by nano
\* Created Wed Nov 11 16:11:13 EST 2015 by nano
