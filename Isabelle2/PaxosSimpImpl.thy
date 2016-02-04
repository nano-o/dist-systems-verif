theory PaxosSimpImpl
imports Main  "~~/src/HOL/Library/Monad_Syntax"
begin

datatype ('v,'a) msg =
  Phase1a (leader: 'a) (ballot:nat)
| Phase1b (last_vote:"('v \<times> nat) option") (new_ballot: nat) (acceptor:'a)
| Phase2a (for_ballot:nat) (suggestion:'v)
| Phase2b (ballot:nat) (acceptor: 'a)

datatype ('v,'a)  packet =
  Packet (sender: 'a) (dst: 'a) (msg: "('v,'a) msg") 

record ('v,'a) pimp_state =
  acceptors :: "'a set"
    -- {* The set of all acceptors *}
  ballot :: "'a \<Rightarrow> nat option"
    -- {* the highest ballot in which an acceptor participated *}
  vote :: "'a \<Rightarrow> 'v option"
    -- {* The last vote cast by an acceptor *}
  last_ballot :: "'a \<Rightarrow> nat option"
    -- {* For an acceptor a, this is the ballot in which "vote a" was cast *}
  highest_seen :: "'a \<Rightarrow> nat option"
    -- {* highest_seen is used by an acceptor to find a high enough ballot *}
  onebs :: "'a \<Rightarrow> nat \<Rightarrow> ('a \<times> ('v \<times> nat) option) list"
    -- {* For an acceptor a and a ballot b, 
      this is the list of all the 1b messages receive by a in b *}
  pending :: "'a \<Rightarrow> 'v option"
    -- {* For an acceptor a, is "Some v" when a has send_1ad v.
      An acceptor may have only one pending proposal. *}
  twobs :: "'a \<Rightarrow> nat \<Rightarrow> 'a list"
    -- {* For an acceptor a and a ballot b, 
      this is the list of all the 2b messages receive by a in b *}
  decided :: "'a \<Rightarrow> 'v option"
    -- {* For an acceptor a, this is Some v if a has decided v in some ballot *}

definition init_state :: "'a set \<Rightarrow> ('v,'a) pimp_state" where
  "init_state accs \<equiv> \<lparr>
    pimp_state.acceptors = accs,
    ballot = (\<lambda> a . None),
    vote = (\<lambda> a . None),
    last_ballot = (\<lambda> a . None),
    highest_seen = (\<lambda> a . None),
    onebs = (\<lambda> a . \<lambda> b . []),
    pending = (\<lambda> a . None),
    twobs = (\<lambda> a . \<lambda> b . []),
    decided = (\<lambda> a . None)\<rparr>"
  
definition quorum_received where
  "quorum_received a b s \<equiv> 2 * length (onebs s a b) > card (acceptors s)"

definition map_opt where
  "map_opt ao bo f \<equiv> ao \<bind> (\<lambda> a . bo \<bind> (\<lambda> b . Some (f a b)))"

definition f_opt where
  "f_opt ao bo f \<equiv> (case ao of None \<Rightarrow> (case bo of None \<Rightarrow> None | Some b \<Rightarrow> Some b) |
    Some a \<Rightarrow> (case bo of None \<Rightarrow> Some a | Some b \<Rightarrow> Some (f a b)))"

definition highest_voted where
  "highest_voted a b s \<equiv>
    let received = onebs s a b; 
        filtered = map snd received;
        max_pair = (\<lambda> x y . if (snd x > snd y) then x else y);
        max_pairo = (\<lambda> x y . f_opt x y max_pair)
    in case (fold max_pairo filtered (hd filtered)) of None \<Rightarrow> None | Some (v,b) \<Rightarrow> Some v"

value "let received = [(3,Some (1,5)),(10, Some (3,(40::nat)))];
        filtered = map snd received;
        max_pair = (\<lambda> x y . if (snd x > snd y) then x else y);
        max_pairo = (\<lambda> x y . map_opt x y max_pair)
    in case (fold max_pairo filtered (hd filtered)) of None \<Rightarrow> None | Some (v,b) \<Rightarrow> Some v"

definition next_ballot_nat
  where "next_ballot_nat a b N \<equiv> (b div N + 1) * N + a"

fun next_ballot where
  "next_ballot a None N = next_ballot_nat a 0 N"
| "next_ballot a (Some b) N = next_ballot_nat a b N"

fun send_1a where
  "send_1a a v s =
    (let msg_1a = Phase1a a (next_ballot a (highest_seen s a) (card (acceptors s))) in
      (s\<lparr>pending := (pending s)(a := Some v)\<rparr>, {Packet a b msg_1a | b . b \<in> (acceptors s)}))"

fun receive_1a where
  "receive_1a a (Phase1a l b) s = 
    (let bal = last_ballot s a in
      (if (bal = None \<or> ((the bal) < b)) 
       then 
          (let 
            to_send = (vote s a) \<bind> (\<lambda> v . bal \<bind> (\<lambda> b . Some (v, b)));
            msg_1b = Phase1b to_send b a;
            pack = Packet a l msg_1b in
          (s\<lparr>ballot := (ballot s)(a := Some b)\<rparr>, {pack}))
       else (s,{})))"
| "receive_1a a _ s = (s,{})"

text {* Let's assume that we are using TCP, and therefore have no duplicates *}
fun receive_1b where
 "receive_1b a (Phase1b last_v new_bal a2) s N = (
    if (new_bal = the (ballot s a)) 
    then (
      (let new_onebs = (a2, last_v) # (onebs s a)(the (ballot s a));
           suggestion = (case (highest_voted a new_bal s) of None \<Rightarrow> the (pending s a) | Some v \<Rightarrow> v);
           msgs = (if (2 * length new_onebs > N) then {Phase2a new_bal suggestion} else {});
           new_state = s\<lparr>
            onebs := (onebs s)(a := ((onebs s a)(the (ballot s a) := new_onebs))),
            pending := (pending s)(a := Some suggestion)\<rparr>
       in (new_state, msgs)))
    else (s,{}))"
| "receive_1b a _ s N = (s, {})"

fun receive_2a where 
  "receive_2a a (Phase2a b v) s = 
    (let bal = (ballot s a) in
      (if (bal = Some b)
      then (s\<lparr>vote := (vote s)(a := Some v)\<rparr>, {Phase2b b a})
      else (s, {})))"
| "receive_2a a _ s = (s, {})"

fun receive_2b where
  "receive_2b a (Phase2b b a2) (s::('v,'a) pimp_state) (N::nat) =
    (let s = 
      (if (decided s a = None)
      then 
        (let new_twobs = a2 # (twobs s a b)
        in
          (if (2 * length new_twobs > N) 
          then 
            s\<lparr>twobs := (twobs s)(a := (twobs s a)(b := new_twobs)),
              decided := (decided s)(a := (pending s a))\<rparr>
          else
            s\<lparr>twobs := (twobs s)(a := (twobs s a)(b := new_twobs))\<rparr>))
      else 
        s)
    in (s,{}))"
| "receive_2b a _ s N = (s, {})"
      
export_code send_1a receive_1a receive_1b receive_2a receive_2b in Scala file "simplePaxos.scala"

end