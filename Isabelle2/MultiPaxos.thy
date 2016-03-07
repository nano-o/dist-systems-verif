theory MultiPaxos
imports Main  "~~/src/HOL/Library/Monad_Syntax" "~~/src/HOL/Library/Code_Target_Nat" Log
begin

text {* We assume reliable channels (TCP) *}

datatype 'v cmd = Cmd 'v | NoOp

datatype ('v,'a,'b) msg =
  Phase1a (leader: 'a) (ballot:'b)
| Phase1b (last_vote:"('v \<times> 'b) option list") (new_ballot: 'b) (acceptor:'a)
  -- {* last_vote contains the list of all instances in which the sender has participated, 
    along with the highest ballot in which it voted and the corresponding value.
    The intended meaning is also that the acceptor 
    did not participate in any instance numbered greater than the length of the list. *}
| Phase2a (inst: nat) (for_ballot:'b) (suggestion:'v) (leader: 'a)
| Phase2b (inst: nat) (ballot:'b) (acceptor: 'a)
| Vote (inst: nat) (val: 'v)
  -- {* Instructs a learner that a value has been decided. Not used for now... *}
| Fwd (val: 'v)
  -- {* Forwards a proposal to another proposer (the leader) *}

datatype ('v,'a,'b)  packet =
  -- {* A message with sender/destination information *}
  Packet (sender: 'a) (dst: 'a) (msg: "('v,'a,'b) msg")

record ('v, 'a, 'b) mp_state =
  acceptors :: "'a set"
    -- {* The set of all acceptors *}
  ballot :: "'a \<Rightarrow> 'b option"
    -- {* the highest ballot in which an acceptor participated *}
  vote :: "'a \<Rightarrow> nat \<Rightarrow> 'v cmd option"
    -- {* The last vote cast by an acceptor *}
  last_ballot :: "'a \<Rightarrow> nat \<Rightarrow> 'b option"
    -- {* For an acceptor a, this is the ballot in which "vote a" was cast *}
  onebs :: "'a \<Rightarrow> 'b \<Rightarrow> ('a \<times> ('v cmd \<times> 'b) option) list list"
    -- {* For an acceptor a and a ballot b,
      this is a list list option. Each element in the outer list describes all the 1b messages 
      receive by a in b in the instance corresponding to the position in the list *}
  twobs :: "'a \<Rightarrow> nat \<Rightarrow> 'b \<Rightarrow> 'a list"
    -- {* For an acceptor a, an instant i, and a ballot b, 
      this is the list describing all the 2b messages receive by a in i in b *}
  decided :: "'a \<Rightarrow> nat \<Rightarrow> 'v cmd option"
    -- {* For an acceptor a, this is Some v if a has decided v in some ballot.
      TODO: is this needed? Seems superseded by the log field. *}
  highest_instance :: "'a \<Rightarrow> nat"
  pending :: "'a \<Rightarrow> nat \<Rightarrow> 'v cmd option"
  (*lowest_instance :: "'a \<Rightarrow> nat"
    -- {* When a is a leader, the next instance to use. *}*)
  log :: "'a \<Rightarrow> (nat \<times> 'v cmd) list"
  leadership_acquired :: "'a \<Rightarrow> 'b \<Rightarrow> bool"

definition init_state :: "'a set \<Rightarrow> ('v,'a,'b) mp_state" where
  "init_state accs \<equiv> \<lparr>
    mp_state.acceptors = accs,
    ballot = (\<lambda> a . None),
    vote = (\<lambda> a . \<lambda> i . None),
    last_ballot = (\<lambda> a . \<lambda> i . None),
    onebs = (\<lambda> a . \<lambda> b . []),
    twobs = (\<lambda> a . \<lambda> i . \<lambda> b . []),
    decided = (\<lambda> a . \<lambda> i . None),
    highest_instance = (\<lambda> a . 0),
    pending = (\<lambda> a . \<lambda> i . None),
    log = ( \<lambda> a . []),
    leadership_acquired = (\<lambda> a . \<lambda> b . False)
    \<rparr>"

definition nr where
  "nr s \<equiv> card (acceptors s)"

definition one_b_quorum where
  "one_b_quorum a i b s \<equiv> 2 * length ((onebs s a b)!i) > nr s"

definition map_opt where
  "map_opt ao bo f \<equiv> ao \<bind> (\<lambda> a . bo \<bind> (\<lambda> b . Some (f a b)))"

definition max_opt where
  -- {* Applies f only if ao and bo are both not None. Wraps the result in an option. 
    TODO: wouldn't it be better to extend the nat ordering on "nat option"? Using transfer or lifting? *}
  "max_opt ao bo f \<equiv> (case ao of None \<Rightarrow> (case bo of None \<Rightarrow> None | Some b \<Rightarrow> Some b) |
    Some a \<Rightarrow> (case bo of None \<Rightarrow> Some a | Some b \<Rightarrow> Some (f a b)))"

definition highest_voted where
  -- {* Given a list describing the 1b messages received by an acceptor, is the highest voted value *}
  "highest_voted l \<equiv>
    let 
        filtered = map snd l;
        max_pair = (\<lambda> x y . if (snd x > snd y) then x else y);
        max_option = (\<lambda> x y . max_opt x y max_pair);
        init_val = (if filtered = [] then None else (hd filtered))
    in case (fold max_option filtered init_val) of None \<Rightarrow> None | Some (v,b) \<Rightarrow> Some v"

value "highest_voted [(1,Some (1,1))]"

definition suc_bal :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat"
  -- {* The smallest ballot belonging to replica a and greater than ballt b, when there are N replicas *}
  where "suc_bal a b N \<equiv> (b div N + 1) * N + a"

fun nx_bal where
  "nx_bal a None N = suc_bal a 0 N"
| "nx_bal a (Some b) N = suc_bal a b N"

definition one_a_msgs where
  -- {* The set of 1a messages to send to try to become the leader *}
  "one_a_msgs a s \<equiv> 
    let
      next_bal = nx_bal a (ballot s a) (card (acceptors s));
      msg_1a = Phase1a a next_bal
    in {Packet a b msg_1a | b . b \<in> (acceptors s)}"

definition leader where
  "leader s b \<equiv> case b of None \<Rightarrow> 0 | Some b \<Rightarrow>
    (b mod (nr s))"

definition send_all where "send_all s sendr m \<equiv> {Packet sendr a2 m | a2 . a2 \<in> acceptors s}"

definition do_2a where
  "do_2a s a v\<equiv> 
    let
      inst = highest_instance s a + 1;
      msg = Phase2a inst (the (ballot s a)) v a;
      new_state = s\<lparr>highest_instance := (highest_instance s)(a := inst),
        pending := (pending s)(a := (pending s a)(inst := Some v))\<rparr>
    in
      (new_state, send_all s a msg)"

definition propose where
  -- {* If leader, then go ahead with 2a, otherwise forward to the leader. *}
  "propose (a::nat) v s \<equiv>
    (if (leader s (ballot s a) = a)
      then do_2a s a v
      else (s, {Packet a (leader s (ballot s a)) (Fwd v)}))"
 
fun receive_fwd where
  "receive_fwd a (Fwd v) s = 
    (if (leader s (ballot s a) = a) then do_2a s a v else (s, ({})))"
| "receive_fwd a _ s = (s, ({}))"

fun send_1a where
  -- {* a tries to become the leader *}
  "send_1a a s =
    (let
        b = nx_bal a (ballot s a) (card (acceptors s));
        msg_1a = Phase1a a b in
      (s, {Packet a a2 msg_1a | a2 . a2 \<in> (acceptors s)}))"

fun receive_1a where
  -- {* Upon receiving a 1a message for a higher ballot than the current one, join this ballot and
    send a list containing the highest 
      vote cast in every instance the acceptor participated in. *}
  "receive_1a a (Phase1a l b) s =
    (let bal = ballot s a in
      (if (bal = None \<or> ((the bal) < b))
       then
          (let
            is = case bal of None \<Rightarrow> [] | Some b \<Rightarrow>  [0..<(Suc b)];
            get_vote = (\<lambda> i . (vote s i a) \<bind> (\<lambda> v . (last_ballot s a i) \<bind> (\<lambda> b . Some (v, b))));
            votes = [get_vote i . i \<leftarrow> is];
            msg_1b = Phase1b votes b a;
            packet = Packet a l msg_1b;
            state = s\<lparr>ballot := (ballot s)(a := Some b)\<rparr>
          in
          (state, {packet}))
       else (s,{})))"
| "receive_1a a _ s = (s,{})"

definition update_onebs where
  -- {* Update the list of highest voted values when receiving a 1b
    message from a2 for ballot bal containing last_vs *}
  "update_onebs s a bal a2 last_vs \<equiv>
    let 
      max_is = Max {length last_vs, length (onebs s a bal)};
      is = [1..<Suc max_is];
      curr_onebs = onebs s a bal;
      at_i = (\<lambda> i . 
        ( if (length curr_onebs \<ge> i) 
          then 
            ( if (length last_vs \<ge> i) 
              then (a2,last_vs!(i-1))#curr_onebs!(i-1)
              else (a2,None)#curr_onebs!(i-1) )
          else [(a2,last_vs!(i-1))] ) );
      new = (if max_is = 0 then [[(a2,None)]] else [at_i i . i \<leftarrow> is])
    in
      s\<lparr>onebs := (onebs s)(a := (onebs s a)(bal := new))\<rparr>"

value "
  let last_vs = [];
    curr_onebs = [[(a1,Some (1,1))]];
    max_is = Max {length last_vs, length curr_onebs};
    is = [1..<Suc max_is];
    at_i = (\<lambda> i . 
      ( if (length curr_onebs \<ge> i)
        then 
          ( if (length last_vs \<ge> i)
            then (a2,last_vs!(i-1))#curr_onebs!(i-1)
            else (a2,None)#curr_onebs!(i-1) )
        else [(a2,last_vs!(i-1))] ) )
  in (if max_is = 0 then [[(a2,None)]] else [at_i i . i \<leftarrow> is])"

definition fold_union where "fold_union l \<equiv> (fold (\<lambda> x y . x \<union> y) l {})"

text {* 
  When a quorum of 1b messages is received, we complete
  We complete all started instances by sending 2b messages containing a safe value.
  If an instance has not been started by a higher instance has been started, we complete
  it by sending a no-op message. *}
fun receive_1b where
 "receive_1b a (Phase1b last_vs new_bal a2) s = (
    if (new_bal = the (ballot s a))
    then (
      (let 
           new_state1 = update_onebs s a new_bal a2 last_vs;
           onebs' = onebs new_state1 a new_bal;
           quorum_received = 2 * length (onebs'!0) > nr s;
           new_state2 = if (quorum_received) 
            then new_state1\<lparr>leadership_acquired := (leadership_acquired new_state1)(a := (
              leadership_acquired new_state1 a)(new_bal := True))\<rparr>   
            else new_state1;
           msgs = 
            if (quorum_received)
            then 
              let
                received = onebs new_state2 a new_bal;
                highest = enumerate 1 [highest_voted l . l \<leftarrow> received]; (* of the form [(1,v_1),(2,v_2)...] where v_i is safe at i*)
                msg =
                  (\<lambda> (i,opt) . (case opt of None \<Rightarrow> Some (Phase2a i new_bal NoOp a) | Some v \<Rightarrow> Some (Phase2a i new_bal v a)));
                msgs =
                  [(case (msg x) of None \<Rightarrow> {} | Some m \<Rightarrow> send_all s a m) . x \<leftarrow> highest ]
              in fold_union msgs
            else {}
       in (new_state2, msgs)))
    else (s,{}))"
| "receive_1b a _ s = (s, {})"

fun receive_2a where
  "receive_2a a (Phase2a i b v l) s =
    (let bal = (ballot s a) in
      (if (bal = Some b)
      then (s\<lparr>vote := (vote s)(a := (vote s a)(i := Some v))\<rparr>, {Packet a l (Phase2b i b a)})
      else (s, {})))"
| "receive_2a a _ s = (s, {})"

fun receive_2b where
  "receive_2b (a::'a) (Phase2b i b a2) s =
    (let s = 
      (if (decided s a i = None)
      then
        (let new_twobs = a2 # (twobs s a i b)
        in
          (if (2 * length new_twobs > card (acceptors s)) 
          then
            s\<lparr>twobs := (twobs s)(a := (twobs s a)(i := (twobs s a i)(b := new_twobs))),
              decided := (decided s)(a := (decided s a)(i := pending s a i)),
              log := (log s)(a := distinct_Sorted_Insert (i, the (pending s a i)) (log s a)) \<rparr>
          else
            s\<lparr>twobs := (twobs s)(a := (twobs s a)(i := (twobs s a i)(b := new_twobs)))\<rparr>))
      else 
        s)
    in (s,{}))"
| "receive_2b a _ s = (s, ({}))"

value "largestprefix [(1,v1), (2,v2), (4,v4)]"

export_code send_1a receive_1a receive_1b init_state propose receive_2a receive_2b receive_fwd 
  largestprefix in Scala file "simplePaxos.scala"

end