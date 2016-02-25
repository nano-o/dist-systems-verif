theory MultiPaxos
imports Main  "~~/src/HOL/Library/Monad_Syntax" "~~/src/HOL/Library/Code_Target_Nat"
begin

text {* We assume reliable channels (TCP) *}

datatype ('v,'a,'b) msg =
  Phase1a (leader: 'a) (ballot:'b)
| Phase1b (last_vote:"('v \<times> 'b) option list") (new_ballot: 'b) (acceptor:'a)
  -- {* last_vote contains the list of all instances in which the sender has participated, 
    along with what it voted and in which ballot. The intended meaning is also that the acceptor 
    did not participate in any instance numbered greater than the length of the list. *}
| Phase2a (inst: nat) (for_ballot:'b) (suggestion:'v) (leader: 'a)
| Phase2b (inst: nat) (ballot:'b) (acceptor: 'a)
| Vote (inst: nat) (val: 'v)
  -- {* Instructs a learner that a value has been decided *}
| Fwd (val: 'v)
  -- {* Forwards a proposal to another proposer (the leader) *}

datatype ('v,'a,'b)  packet =
  -- {* A message with sender/destination information *}
  Packet (sender: 'a) (dst: 'a) (msg: "('v,'a,'b) msg")

datatype 'v Safe = NoneSafe | Safe (the_safe: 'v) | All
  -- {* Describes which values are safe *}

record ('v, 'a, 'b) mp_state =
  acceptors :: "'a set"
    -- {* The set of all acceptors *}
  ballot :: "'a \<Rightarrow> 'b option"
    -- {* the highest ballot in which an acceptor participated *}
  vote :: "'a \<Rightarrow> nat \<Rightarrow> 'v option"
    -- {* The last vote cast by an acceptor *}
  last_ballot :: "'a \<Rightarrow> nat \<Rightarrow> 'b option"
    -- {* For an acceptor a, this is the ballot in which "vote a" was cast *}
  onebs :: "'a \<Rightarrow> ('b \<Rightarrow> ('a \<times> ('v \<times> 'b) option) list) list"
    -- {* For an acceptor a and a ballot b, 
      this is the list of all the 1b messages receive by a in b *}
  twobs :: "'a \<Rightarrow> ('b \<Rightarrow> 'a list) list"
    -- {* For an acceptor a and a ballot b, 
      this is the list of all the 2b messages receive by a in b *}
  decided :: "'a \<Rightarrow> nat \<Rightarrow> 'v option"
    -- {* For an acceptor a, this is Some v if a has decided v in some ballot *}
  highest_instance :: "'a \<Rightarrow> nat"
  lowest_instance :: "'a \<Rightarrow> nat"
    -- {* When a is a leader, the next instance to use. *}

definition init_state :: "'a set \<Rightarrow> ('v,'a,'b) mp_state" where
  "init_state accs \<equiv> \<lparr>
    mp_state.acceptors = accs,
    ballot = (\<lambda> a . None),
    vote = (\<lambda> a . \<lambda> i . None),
    last_ballot = (\<lambda> a . \<lambda> i . None),
    onebs = (\<lambda> a . []),
    twobs = (\<lambda> a .[]),
    decided = (\<lambda> a . \<lambda> i . None),
    highest_instance = (\<lambda> a . 0),
    lowest_instance = (\<lambda> a . 0)\<rparr>"

definition one_b_quorum where
  "one_b_quorum a i b s \<equiv> 2 * length (((onebs s a)!i) b) > card (acceptors s)"

definition map_opt where
  "map_opt ao bo f \<equiv> ao \<bind> (\<lambda> a . bo \<bind> (\<lambda> b . Some (f a b)))"

definition max_opt where
  -- {* Applies f only if ao and bo are both not None. Wraps the result in an option. 
    TODO: wouldn't it be better to extend the nat ordering on "nat option"? Using transfer or lifting? *}
  "max_opt ao bo f \<equiv> (case ao of None \<Rightarrow> (case bo of None \<Rightarrow> None | Some b \<Rightarrow> Some b) |
    Some a \<Rightarrow> (case bo of None \<Rightarrow> Some a | Some b \<Rightarrow> Some (f a b)))"

definition highest_voted where
  "highest_voted a i b s \<equiv>
    let received = ((onebs s a)!i) b; 
        filtered = map snd received;
        max_pair = (\<lambda> x y . if (snd x > snd y) then x else y);
        max_pairo = (\<lambda> x y . max_opt x y max_pair);
        init_val = (if filtered = [] then None else (hd filtered))
    in case (fold max_pairo filtered init_val) of None \<Rightarrow> None | Some (v,b) \<Rightarrow> Some v"

value "let received = [(3,Some (1::int,5)),(10, Some (3,(40::nat)))];
        filtered = map snd received;
        max_pair = (\<lambda> x y . if (snd x > snd y) then x else y);
        max_pairo = (\<lambda> x y . map_opt x y max_pair)
    in case (fold max_pairo filtered (hd filtered)) of None \<Rightarrow> None | Some (v,b) \<Rightarrow> Some v"

definition suc_bal :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat"
  where "suc_bal a b N \<equiv> (b div N + 1) * N + a"

fun nx_bal where
  "nx_bal a None N = suc_bal a 0 N"
| "nx_bal a (Some b) N = suc_bal a b N"

definition one_a_msgs where
  "one_a_msgs a s \<equiv> 
    let
      next_bal = nx_bal a (ballot s a) (card (acceptors s));
      msg_1a = Phase1a a next_bal 
    in {Packet a b msg_1a | b . b \<in> (acceptors s)}"

definition nr where
  "nr s \<equiv> card (acceptors s)"

definition leader where
  "leader s b \<equiv> case b of None \<Rightarrow> 0 | Some b \<Rightarrow> 
    (b mod (nr s))"

definition propose where 
  -- {* If leader, then go ahead with 2a, otherwise forward to the leader.
    TODO: how to choose an instance?
    Maintain a list of available instances? or maybe just a variable last_instance will suffice.
    How to record the pending command? *}
  "propose a v s \<equiv>
    (if (leader s (ballot s a) = a)
      then (s, {})
      else (s, {Packet a (leader s (ballot s a)) (Fwd v)}))"
 
fun send_1a where
  -- {* a tries to become the leader *}
  "send_1a a s =
    (let
        b = nx_bal a (ballot s a) (card (acceptors s));
        msg_1a = Phase1a a b in
      (s, {Packet a a2 msg_1a | a2 . a2 \<in> (acceptors s)}))"

fun receive_1a where
  -- {* Upon receiving a 1a message for a higher ballot, send a list containing the highest 
    vote cast in every instance the acceptor participated in. *}
  "receive_1a a (Phase1a l b) s =
    (let bal = ballot s a in
      (if (bal = None \<or> ((the bal) < b))
       then
          (let
            is = case bal of None \<Rightarrow> [] | Some b \<Rightarrow>  [0..(int b)];
            get_vote = (\<lambda> i . (vote s i a) \<bind> (\<lambda> v . (last_ballot s a i)  \<bind> (\<lambda> b . Some (v, b))));
            votes = [get_vote v . v \<leftarrow> map nat is];
            msg_1b = Phase1b votes b a;
            packet = Packet a l msg_1b;
            state = s\<lparr>ballot := (ballot s)(a := Some b)\<rparr>
          in
          (state, {packet}))
       else (s,{})))"                                                        
| "receive_1a a _ s = (s,{})"

definition update_onebs where 
  -- {* Update the list of highest voted values when receiving a onebs 
    message from a2 for ballot bal containing last_vs*}
  "update_onebs s a bal a2 last_vs \<equiv>
    let 
      is = if last_vs = [] then [] else [0..(int (length last_vs)-1)];
      update = \<lambda> i . \<lambda> b . 
        if (b = bal) 
        then (a2, (last_vs!i)) # (((onebs s a)!i) bal)
        else ((onebs s a)!i) b;
      onebs_a = [update (nat i) . i  \<leftarrow> is]  in
    s\<lparr>onebs := (onebs s)(a := onebs_a)\<rparr>"

fun max_inst where
  "max_inst [] = None"
| "max_inst x#xs = "

definition max_instance where
  "max_instance s a b \<equiv>
    "

fun receive_1b where
 "receive_1b a (Phase1b last_vs new_bal a2) s = (
    if (new_bal = the (ballot s a))
    then (
      (let msgs = {};
           new_state = update_onebs s a new_bal a2 last_vs
       in (new_state, msgs)))
    else (s,{}))"
| "receive_1b a _ s = (s, {})"

fun receive_1b where
  -- {* Upon receiving a quorum of 1b messages, update the "safe" variable, then complete all 
    pending instances. If the leader is restricted to start a new instance only when the previous 
    has finished, then there should be at most one pending instance to complete. *}
 "receive_1b a (Phase1b last_vs new_bal a2) s = (
    if (new_bal = the (ballot s a))
    then (
      (let new_onebs = (\<lambda> i . (a2, (last_vs!i)) # (onebs s a i (the (ballot s a))));
           suggestion = (case (highest_voted a i new_bal s) of None \<Rightarrow> the (pending s a i) | Some v \<Rightarrow> v);
           msgs =                              
           (if (2 * length new_onebs > N)
            then {Packet a a2 (Phase2a  new_bal suggestion a (highest_instance s a)) | a2 . a2 \<in> acceptors s}
            else {});
           new_state = s\<lparr>
            onebs := (onebs s)(a := ((onebs s a)(the (ballot s a) := new_onebs))),
            pending := (pending s)(a := (\<lambda>v. Some suggestion))\<rparr>
       in (new_state, msgs)))
    else (s,{}))"
| "receive_1b a _ s N = (s, {})"

fun receive_2a where
  "receive_2a a (Phase2a b v l) s =
    (let bal = (ballot s a) in
      (if (bal = Some b)
      then (s\<lparr>vote := (vote s)(a := Some v)(*, 
              last_ballot := (last_ballot s)(a := bal)*)\<rparr>, {Packet a l (Phase2b b a)})
      else (s, {})))"
| "receive_2a a _ s = (s, {})"

fun receive_2b where
  "receive_2b a (Phase2b b a2) (s::('v,'a) mp_state) (N::nat) =
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

inductive reachable :: "nat set \<Rightarrow> (nat,nat) mp_state \<times> (nat,nat)packet set \<Rightarrow> bool" for replicas where
  "reachable replicas ((init_state replicas),{})"
| "\<lbrakk>reachable replicas (s,n); (t,n') = (send_1a a v s)\<rbrakk> \<Longrightarrow> reachable replicas (t,n \<union> n')" 
| "\<lbrakk>reachable replicas (s,n); p \<in> n; dst p = l; (t,n') = receive_1a l (msg p) s\<rbrakk> \<Longrightarrow> reachable replicas (t,n \<union> n')" 
| "\<lbrakk>reachable replicas (s,n); p \<in> n; dst p = a; (t,n') = receive_1b a (msg p) s (card replicas)\<rbrakk> \<Longrightarrow> reachable replicas (t,n \<union> n')" 
| "\<lbrakk>reachable replicas (s,n); p \<in> n; dst p = a; (t,n') = receive_2a a (msg p) s\<rbrakk> \<Longrightarrow> reachable replicas (t,n \<union> n')" 
| "\<lbrakk>reachable replicas (s,n); p \<in> n; dst p = a; (t,n') = receive_2b a (msg p) s (card replicas)\<rbrakk> \<Longrightarrow> reachable replicas (t,n \<union> n')" 

(* definition decided where
  "decided s v \<equiv> \<exists> q . q \<subseteq> acceptors s \<and> card q \<ge> (card (acceptors s) div 2) \<and> \<exists> b . \<forall> a \<in> q . " *)

definition decided where
  "decided s v \<equiv> \<exists> a \<in> acceptors s . mp_state.decided s a = v"

lemma
  "reachable {0,1} (x,y) \<Longrightarrow> \<forall> v1 v2 . decided x v1 \<and> decided x v2 \<longrightarrow> v1 = v2" 
    nitpick[card nat=2, show_all, timeout=300, verbose,
      card "nat list" = 5, card "(nat \<times> nat) option list" = 25, card "(nat \<times> (nat \<times> nat) option) list" = 25, card "nat option" = 3, card "(nat \<times> nat) option" = 25,
    card "(nat, nat) mp_state \<times> (nat, nat) packet set" = 1000, card "(nat, nat) msg" = 100, card unit = 1, card "(nat, nat) packet" = 100, card "(nat, nat) mp_state" = 100, iter reachable = 1, 
    bits = 1]
oops

export_code send_1a receive_1a receive_1b receive_2a receive_2b init_state in Scala file "simplePaxos.scala"

end