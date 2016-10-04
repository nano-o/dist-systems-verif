----------------------- MODULE MultiPaxosWithRecovery -----------------------

EXTENDS Integers, FiniteSets

CONSTANT Value, Acceptor, Quorum, Window

ASSUME 
    /\ \A Q \in Quorum : Q \subseteq Acceptor 
    /\ \A Q1, Q2 \in Quorum : Q1 \cap Q2 # {} 
                                                                   
Ballot ==  Nat
Instance == Nat

ASSUME
    ((Ballot \cup {-1}) \cap Acceptor) = {}

MajQuorums == {Q \in SUBSET Acceptor : Cardinality(Q) > Cardinality(Acceptor) \div 2}

(***************************************************************************)
(* We define None to be an unspecified value that is not in the set Value. *)
(***************************************************************************)
None == CHOOSE v : v \notin Value
 
(***********
--algorithm MP {

  variables ballot = [a \in Acceptor |-> 0],
            vote = [a \in Acceptor |-> [b \in Ballot |-> [i \in Instance |-> None]]],
            onebs = [a \in Acceptor |-> [b \in Ballot |-> <<>>]],
            twobs = [a \in Acceptor |-> [b \in Ballot |-> [i \in Instance |-> None]]],
            suggestion = [b \in Ballot |-> [i \in Instance |-> None]],
            twoas = [b \in Ballot |-> [i \in Instance |-> None]],
            instStatus = [b \in Ballot |-> IF b = 0 THEN [i \in Instance |-> None] ELSE <<>>],
            log = [a \in Acceptor |-> [i \in Instance |-> None]],
            lowestAcc = [a \in Acceptor |-> 0],
            lowestLeader = [l \in Ballot |-> 0] (* the lowest instance in which a leader can participate *)
            
    define {
  
    TypeInvariant ==
        /\ \A a \in Acceptor : 
            /\ ballot[a] \in Ballot
            /\ \A b \in Ballot, i \in Instance : vote[a][b][i] \in Value \cup {None}
            /\ \A b \in Ballot : 
                \/ onebs[a][b] = <<>> 
                \/ \A i \in Instance : onebs[a][b][i] \in (Ballot \times Value) \cup {None}
  
    ChosenIn(b, i, v) == \E q \in Quorum : \A a \in q : twobs[a][b][i] = v
    
    Chosen(i, v) == \E b \in Ballot : ChosenIn(b, i, v)

    ChosenVals == [b \in Ballot |-> [i \in Instance |-> {v \in Value : ChosenIn(b, i, v)}]]
    
    Max(xs, LessEq(_,_)) == CHOOSE x \in xs : \A y \in xs : LessEq(y,x)
    
    Joined(q, b, i) == \A a \in q : onebs[a][b] # <<>> /\ lowestAcc[a] \leq i
    
    MaxVote(vs) == IF vs # {} THEN Max(vs, LAMBDA x, y : x[2] <= y[2]) ELSE None
    
    Votes(a, i, b) == {v \in {<<vote[a][c][i], c>> : c \in 0..(b-1)} : v[1] # None}
    
    SafeVal(b, i, q) == 
        LET vs == {onebs[a][b][i] : a \in q} \ {None}
        IN  MaxVote(vs)
    
    LearnedByQuorum(i) == \E q \in Quorum : \A a \in q : log[a][i] # None
    
    MaxB(q) == Max({ballot[a] : a \in q}, <=)
    
    MaxI(q) ==
        LET is == {i \in Instance : \E a \in q : lowestAcc[a] = i \/ log[a][i] # None}
        IN IF is # {} THEN Max(is, <=) ELSE 0

        
    Safety == \A i \in Instance : \A v,w \in Value : Chosen(i,v) /\ Chosen(i,w) => v = w
    
    Inv1 == \A q \in Quorum : \A b \in Ballot : \A j \in Instance :
        j > MaxI(q)+Window+1 => suggestion[b][j] = None
        (***********************************************************************)
        (* We can be sure that instance MaxI(q)+Window+1 is the highest        *)
        (* possibly started instance.                                          *)
        (***********************************************************************)
    
   }
       
    macro joinBallot(a, b) {
        await b > ballot[a];
        with (vs = [i \in Instance |-> Votes(a, i, b)])
            ballot[a] := b || onebs[a][b] := [i \in Instance |-> MaxVote(vs[i])] 
    }
    
    macro vote(a, i) {
        with (b = ballot[a]) {
            await vote[a][b][i] = None /\ twoas[b][i] # None /\ i \geq lowestAcc[a];
            with (v = twoas[b][i])
                vote[a][b][i] := v || twobs[a][b][i] := twoas[b][i] 
        }
    }
    
    macro learn(a, i) {
        with (q \in Quorum, b \in Ballot) {
            await \A a2 \in q : vote[a2][b][i] # None;
            with (a2 \in q) log[a][i] := twobs[a2][b][i]
        }
    }
        
    macro resetAcc(a) {
        with (q \in Quorum, b = MaxB(q)) {
            ballot[a] := b || vote[a] := [c \in Ballot |-> [i \in Instance |-> None]]
            || lowestAcc[a] := MaxI(q)+Window+1
        }
    }
    
    macro acquire(b, q) {
        if (b # 0) {
            with(i = lowestLeader[b]) {
                await (q \in Quorum /\ Joined(q, b, i));
                instStatus[b] := [j \in Instance |-> IF j < i THEN None
                    ELSE SafeVal(b, j, q)];
                twoas[b] := instStatus[b] || suggestion[b] := instStatus[b] }
        }
    }
    
    macro suggest(b, i, v) {
        await
            /\  \A j \in Instance : (j < (i - Window)) => LearnedByQuorum(j)
            /\  instStatus[b] # <<>> 
            /\  instStatus[b][i] = None
            /\  lowestLeader[b] <= i
            /\  suggestion[b][i] = None; 
        suggestion[b][i] := v || twoas[b][i] := v
    }
    
    macro resetLeader(b) {
        with (q \in Quorum, c = MaxB(q), low = MaxI(q)+Window+1) {
            await low \in Instance;
            lowestLeader[b] := low || suggestion[b] := [i \in Instance |-> None]
        }
    }
   
  process (acc \in Acceptor) {
    acc: 
        while (TRUE) {
            either
        join:   with (b \in Ballot) joinBallot(self, b)
            or
        vote:   with (i \in Instance) vote(self, i)
            or 
        learn:  with (i \in Instance) learn(self, i)
            or 
        rese:   resetAcc(self)
        }
   }

  process (l \in Ballot) {
    acq:    with (q \in Quorum) acquire(self, q);
    loop:   while (TRUE) { 
                either
        sugg:       with (i \in Instance, v \in Value) suggest(self, i, v);
                or {
        reset:      resetLeader(self);
                    goto acq;
                }
            }
   }
}

**********)

\* BEGIN TRANSLATION
\* Label acc of process acc at line 143 col 9 changed to acc_
\* Label vote of process acc at line 147 col 22 changed to vote_
VARIABLES ballot, vote, onebs, twobs, suggestion, twoas, instStatus, log, 
          lowestAcc, lowestLeader, pc

(* define statement *)
TypeInvariant ==
    /\ \A a \in Acceptor :
        /\ ballot[a] \in Ballot
        /\ \A b \in Ballot, i \in Instance : vote[a][b][i] \in Value \cup {None}
        /\ \A b \in Ballot :
            \/ onebs[a][b] = <<>>
            \/ \A i \in Instance : onebs[a][b][i] \in (Ballot \times Value) \cup {None}

ChosenIn(b, i, v) == \E q \in Quorum : \A a \in q : twobs[a][b][i] = v

Chosen(i, v) == \E b \in Ballot : ChosenIn(b, i, v)

ChosenVals == [b \in Ballot |-> [i \in Instance |-> {v \in Value : ChosenIn(b, i, v)}]]

Max(xs, LessEq(_,_)) == CHOOSE x \in xs : \A y \in xs : LessEq(y,x)

Joined(q, b, i) == \A a \in q : onebs[a][b] # <<>> /\ lowestAcc[a] \leq i

MaxVote(vs) == IF vs # {} THEN Max(vs, LAMBDA x, y : x[2] <= y[2]) ELSE None

Votes(a, i, b) == {v \in {<<vote[a][c][i], c>> : c \in 0..(b-1)} : v[1] # None}

SafeVal(b, i, q) ==
    LET vs == {onebs[a][b][i] : a \in q} \ {None}
    IN  MaxVote(vs)

LearnedByQuorum(i) == \E q \in Quorum : \A a \in q : log[a][i] # None

MaxB(q) == Max({ballot[a] : a \in q}, <=)

MaxI(q) ==
    LET is == {i \in Instance : \E a \in q : lowestAcc[a] = i \/ log[a][i] # None}
    IN IF is # {} THEN Max(is, <=) ELSE 0


Safety == \A i \in Instance : \A v,w \in Value : Chosen(i,v) /\ Chosen(i,w) => v = w

Inv1 == \A q \in Quorum : \A b \in Ballot : \A j \in Instance :
    j > MaxI(q)+Window+1 => suggestion[b][j] = None


vars == << ballot, vote, onebs, twobs, suggestion, twoas, instStatus, log, 
           lowestAcc, lowestLeader, pc >>

ProcSet == (Acceptor) \cup (Ballot)

Init == (* Global variables *)
        /\ ballot = [a \in Acceptor |-> 0]
        /\ vote = [a \in Acceptor |-> [b \in Ballot |-> [i \in Instance |-> None]]]
        /\ onebs = [a \in Acceptor |-> [b \in Ballot |-> <<>>]]
        /\ twobs = [a \in Acceptor |-> [b \in Ballot |-> [i \in Instance |-> None]]]
        /\ suggestion = [b \in Ballot |-> [i \in Instance |-> None]]
        /\ twoas = [b \in Ballot |-> [i \in Instance |-> None]]
        /\ instStatus = [b \in Ballot |-> IF b = 0 THEN [i \in Instance |-> None] ELSE <<>>]
        /\ log = [a \in Acceptor |-> [i \in Instance |-> None]]
        /\ lowestAcc = [a \in Acceptor |-> 0]
        /\ lowestLeader = [l \in Ballot |-> 0]
        /\ pc = [self \in ProcSet |-> CASE self \in Acceptor -> "acc_"
                                        [] self \in Ballot -> "acq"]

acc_(self) == /\ pc[self] = "acc_"
              /\ \/ /\ pc' = [pc EXCEPT ![self] = "join"]
                 \/ /\ pc' = [pc EXCEPT ![self] = "vote_"]
                 \/ /\ pc' = [pc EXCEPT ![self] = "learn"]
                 \/ /\ pc' = [pc EXCEPT ![self] = "rese"]
              /\ UNCHANGED << ballot, vote, onebs, twobs, suggestion, twoas, 
                              instStatus, log, lowestAcc, lowestLeader >>

join(self) == /\ pc[self] = "join"
              /\ \E b \in Ballot:
                   /\ b > ballot[self]
                   /\ LET vs == [i \in Instance |-> Votes(self, i, b)] IN
                        /\ ballot' = [ballot EXCEPT ![self] = b]
                        /\ onebs' = [onebs EXCEPT ![self][b] = [i \in Instance |-> MaxVote(vs[i])]]
              /\ pc' = [pc EXCEPT ![self] = "acc_"]
              /\ UNCHANGED << vote, twobs, suggestion, twoas, instStatus, log, 
                              lowestAcc, lowestLeader >>

vote_(self) == /\ pc[self] = "vote_"
               /\ \E i \in Instance:
                    LET b == ballot[self] IN
                      /\ vote[self][b][i] = None /\ twoas[b][i] # None /\ i \geq lowestAcc[self]
                      /\ LET v == twoas[b][i] IN
                           /\ twobs' = [twobs EXCEPT ![self][b][i] = twoas[b][i]]
                           /\ vote' = [vote EXCEPT ![self][b][i] = v]
               /\ pc' = [pc EXCEPT ![self] = "acc_"]
               /\ UNCHANGED << ballot, onebs, suggestion, twoas, instStatus, 
                               log, lowestAcc, lowestLeader >>

learn(self) == /\ pc[self] = "learn"
               /\ \E i \in Instance:
                    \E q \in Quorum:
                      \E b \in Ballot:
                        /\ \A a2 \in q : vote[a2][b][i] # None
                        /\ \E a2 \in q:
                             log' = [log EXCEPT ![self][i] = twobs[a2][b][i]]
               /\ pc' = [pc EXCEPT ![self] = "acc_"]
               /\ UNCHANGED << ballot, vote, onebs, twobs, suggestion, twoas, 
                               instStatus, lowestAcc, lowestLeader >>

rese(self) == /\ pc[self] = "rese"
              /\ \E q \in Quorum:
                   LET b == MaxB(q) IN
                     /\ ballot' = [ballot EXCEPT ![self] = b]
                     /\ lowestAcc' = [lowestAcc EXCEPT ![self] = MaxI(q)+Window+1]
                     /\ vote' = [vote EXCEPT ![self] = [c \in Ballot |-> [i \in Instance |-> None]]]
              /\ pc' = [pc EXCEPT ![self] = "acc_"]
              /\ UNCHANGED << onebs, twobs, suggestion, twoas, instStatus, log, 
                              lowestLeader >>

acc(self) == acc_(self) \/ join(self) \/ vote_(self) \/ learn(self)
                \/ rese(self)

acq(self) == /\ pc[self] = "acq"
             /\ \E q \in Quorum:
                  IF self # 0
                     THEN /\ LET i == lowestLeader[self] IN
                               /\ (q \in Quorum /\ Joined(q, self, i))
                               /\ instStatus' = [instStatus EXCEPT ![self] =              [j \in Instance |-> IF j < i THEN None
                                                                             ELSE SafeVal(self, j, q)]]
                               /\ /\ suggestion' = [suggestion EXCEPT ![self] = instStatus'[self]]
                                  /\ twoas' = [twoas EXCEPT ![self] = instStatus'[self]]
                     ELSE /\ TRUE
                          /\ UNCHANGED << suggestion, twoas, instStatus >>
             /\ pc' = [pc EXCEPT ![self] = "loop"]
             /\ UNCHANGED << ballot, vote, onebs, twobs, log, lowestAcc, 
                             lowestLeader >>

loop(self) == /\ pc[self] = "loop"
              /\ \/ /\ pc' = [pc EXCEPT ![self] = "sugg"]
                 \/ /\ pc' = [pc EXCEPT ![self] = "reset"]
              /\ UNCHANGED << ballot, vote, onebs, twobs, suggestion, twoas, 
                              instStatus, log, lowestAcc, lowestLeader >>

sugg(self) == /\ pc[self] = "sugg"
              /\ \E i \in Instance:
                   \E v \in Value:
                     /\ /\  \A j \in Instance : (j < (i - Window)) => LearnedByQuorum(j)
                        /\  instStatus[self] # <<>>
                        /\  instStatus[self][i] = None
                        /\  lowestLeader[self] <= i
                        /\  suggestion[self][i] = None
                     /\ /\ suggestion' = [suggestion EXCEPT ![self][i] = v]
                        /\ twoas' = [twoas EXCEPT ![self][i] = v]
              /\ pc' = [pc EXCEPT ![self] = "loop"]
              /\ UNCHANGED << ballot, vote, onebs, twobs, instStatus, log, 
                              lowestAcc, lowestLeader >>

reset(self) == /\ pc[self] = "reset"
               /\ \E q \in Quorum:
                    LET c == MaxB(q) IN
                      LET low == MaxI(q)+Window+1 IN
                        /\ low \in Instance
                        /\ /\ lowestLeader' = [lowestLeader EXCEPT ![self] = low]
                           /\ suggestion' = [suggestion EXCEPT ![self] = [i \in Instance |-> None]]
               /\ pc' = [pc EXCEPT ![self] = "acq"]
               /\ UNCHANGED << ballot, vote, onebs, twobs, twoas, instStatus, 
                               log, lowestAcc >>

l(self) == acq(self) \/ loop(self) \/ sugg(self) \/ reset(self)

Next == (\E self \in Acceptor: acc(self))
           \/ (\E self \in Ballot: l(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Tue Oct 04 15:14:08 EDT 2016 by nano
\* Created Mon Oct 03 11:25:27 EDT 2016 by nano
