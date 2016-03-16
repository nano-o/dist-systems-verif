theory MultiPaxos3
imports Main  "~~/src/HOL/Library/Monad_Syntax" "~~/src/HOL/Library/Code_Target_Nat"
  Log LinorderOption "~~/src/HOL/Library/FinFun_Syntax"
begin

text {* A version of MultiPaxos using FinFuns *}

subsection {* Ordering on pairs *}

fun less_eq_pair where
  "less_eq_pair (x,y) (u,v) = (y \<le> v)"

fun less_pair where 
  "less_pair (x,y) (u,v) = (y < v)"

instantiation prod :: (type,order) preorder
begin

definition less_eq_def: "less_eq x y = less_eq_pair x y"
definition less_def: "less x y = less_pair x y"

instance
apply(intro_classes)
apply (auto simp add:less_eq_def less_def)
done

end

subsection {* Actions, messages, and state. *}

datatype 'v cmd = Cmd 'v | NoOp

datatype ('v,'a) msg =
  Phase1a (leader: 'a) (ballot:nat)
| Phase1b (last_votes:"nat \<Rightarrow>f ('v cmd \<times> nat) option") (new_ballot: nat) (acceptor:'a)
| Phase2a (inst: nat) (for_ballot:nat) (suggestion:'v) (leader: 'a)
| Phase2b (inst: nat) (ballot:nat) (acceptor: 'a) (val: 'v)
| Vote (inst: nat) (val: 'v)
  -- {* Instructs a learner that a value has been decided. Not used for now... *}
| Fwd (val: 'v)
  -- {* Forwards a proposal to another proposer (the leader) *}

datatype ('v,'a)  packet =
  -- {* A message with sender/destination information *}
  Packet (sender: 'a) (dst: 'a) (msg: "('v,'a) msg")

type_synonym bal = nat
type_synonym inst = nat

record ('v, 'a) mp_state =
  acceptors :: "'a set"
    -- {* The set of all acceptors *}
  ballot :: "'a \<Rightarrow>f bal option"
    -- {* the highest ballot in which an acceptor participated *}
  vote :: "'a \<Rightarrow>f inst \<Rightarrow>f 'v cmd option"
    -- {* The last vote cast by an acceptor, for each instance *}
  last_ballot :: "'a \<Rightarrow>f nat \<Rightarrow>f bal option"
    -- {* For an acceptor a, this is the ballot in which "vote a" was cast, for each instance *}
  onebs :: "'a \<Rightarrow>f bal \<Rightarrow>f inst \<Rightarrow>f ('a \<times> ('v cmd \<times> bal) option) list"
    -- {* For an acceptor a and a ballot b, lists of 1b-message descriptions, indexed by ballot then instance. *}
  twobs :: "'a \<Rightarrow>f inst \<Rightarrow>f bal \<Rightarrow>f 'a list"
    -- {* For an acceptor a: lists describing the 2b messages, indexed by instance then ballot. *}
  decided :: "'a \<Rightarrow>f inst \<Rightarrow>f 'v cmd option"
  highest_instance :: "'a \<Rightarrow>f nat"
  pending :: "'a \<Rightarrow>f inst \<Rightarrow>f 'v cmd option"
  log :: "'a \<Rightarrow>f (nat \<times> 'v cmd) list"
  leadership_acquired :: "'a \<Rightarrow>f bal \<Rightarrow>f bool"

definition init_state :: "'a set \<Rightarrow> ('v,'a) mp_state" where
  "init_state accs \<equiv> \<lparr>
    mp_state.acceptors = accs,
    ballot = K$ None,
    vote = K$ K$ None,
    last_ballot = K$ K$ None,
    onebs = K$ K$ K$ [],
    twobs = K$ K$ K$ [],
    decided = K$ K$ None,
    highest_instance = K$ 0,
    pending = K$ K$ None,
    log = K$ [],
    leadership_acquired = K$ K$ False \<rparr>"

definition nr where
  -- {* The number of replicas *}
  "nr s \<equiv> card (acceptors s)"


subsection {* Event handlers *}

definition one_b_quorum_received where
  "one_b_quorum_received a i b s \<equiv> 
    let at_b = onebs s $ a $ b;
        at_b_i = at_b $ i
    in 2 * length at_b_i > nr s"

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
      next_bal = nx_bal a (ballot s $ a) (card (acceptors s));
      msg_1a = Phase1a a next_bal
    in {Packet a b msg_1a | b . b \<in> (acceptors s)}"

definition leader where
  "leader s b \<equiv> case b of None \<Rightarrow> 0 | Some b \<Rightarrow>
    (b mod (nr s))"

definition send_all where "send_all s sendr m \<equiv> {Packet sendr a2 m | a2 . a2 \<in> acceptors s}"

definition do_2a where
  "do_2a s a v \<equiv>
    let
      inst = highest_instance s $ a + 1;
      msg = Phase2a inst (the (ballot s $ a)) v a;
      new_state = s\<lparr>highest_instance := (highest_instance s)(a $:= inst),
        pending := (pending s)(a $:= (pending s $ a)(inst $:= (Some v)))\<rparr>
    in
      (new_state, send_all s a msg)"

definition propose where
  -- {* If leader, then go ahead with 2a, otherwise forward to the leader. *}
  "propose (a::nat) v s \<equiv>
    (if (leader s (ballot s $ a) = a)
      then do_2a s a v
      else (s, {Packet a (leader s (ballot s $ a)) (Fwd v)}))"
 
fun receive_fwd where
  "receive_fwd a (Fwd v) s = 
    (if (leader s (ballot s $ a) = a) then do_2a s a v else (s, ({})))"
| "receive_fwd a _ s = (s, ({}))"

fun send_1a where
  -- {* a tries to become the leader *}
  "send_1a a s =
    (let
        b = nx_bal a (ballot s $ a) (card (acceptors s));
        msg_1a = Phase1a a b in
      (s, {Packet a a2 msg_1a | a2 . a2 \<in> (acceptors s)}))"

fun receive_1a :: "'a \<Rightarrow> ('v,'a)msg \<Rightarrow> ('v, 'a)mp_state \<Rightarrow> (('v, 'a)mp_state \<times> ('v,'a)packet set)" where
  "receive_1a a (Phase1a l b) s =
    (let bal = ballot s $ a in
      (if (bal = None \<or> ((the bal) < b))
       then
          (let
            combiner = (\<lambda> (vo,bo) . vo \<bind> (\<lambda> v . bo \<bind> (\<lambda> b . Some (v,b))));
            last_votes = combiner o$ ($ vote s $ a, last_ballot s $ a $);
            msg_1b = Phase1b last_votes b a;
            packet = Packet a l msg_1b;
            state = s\<lparr>ballot := (ballot s)(a $:= Some b)\<rparr>
          in
          (state, {packet}))
       else (s,{})))"
| "receive_1a a _ s = (s,{})"

definition update_onebs :: 
  "('v, 'a)mp_state \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> (nat \<Rightarrow>f ('v cmd \<times> nat) option) \<Rightarrow> ('v, 'a)mp_state" where
  -- {* Update the list of highest voted values when receiving a 1b
    message from a2 for ballot bal containing last_vs *}
  "update_onebs s a bal a2 last_vs \<equiv>
    let
      combiner = \<lambda> (xs, y) . (case y of None \<Rightarrow> (a2, None)#xs | Some z \<Rightarrow> (a2, Some z)#xs);
      at_bal = combiner o$ ($ (onebs s $ a $ bal), last_vs $)
    in s\<lparr>onebs := (onebs s)(a $:= (onebs s $ a)(bal $:= at_bal))\<rparr>"

abbreviation s1 where 
  -- {* This is a state in which acceptor 1 is in ballot 2 and has received a ballot-2 1b message from
  acceptor 2 saying that acceptor 2 last voted in ballot 1 in instance 1 for value 1. *}
  "s1 \<equiv> \<lparr>
    mp_state.acceptors = {1,2,3::int},
    ballot = K$ Some 2,
    vote = K$ K$ None,
    last_ballot = K$ K$ None,
    onebs = (K$ K$ K$ [])(1 $:= (K$ K$ [])(2 $:= (K$ [(2, None)])(1 $:= [(2, Some (Cmd 1,1))]))),
    twobs = K$ K$ K$ [],
    decided = K$ K$ None,
    highest_instance = K$ 1,
    pending = K$ K$ None,
    log = K$ [],
    leadership_acquired = K$ K$ False \<rparr>"

value "onebs test_state_1 $ 1 $ 2 $ 1"

text {* State obtained after acceptor 1 receives a ballot-2 1b message from acceptor 3 saying that acceptor 3 never voted *}
abbreviation s2 where "s2 \<equiv> update_onebs s1 1 2 3 (K$ None)"
value "onebs s2 $ 1 $ 2 $ 1"

text {* State obtained after acceptor 1 receives a ballot-2 1b message from acceptor 3 saying that acceptor 3 last voted in instance 1 and ballot 1 for value 1 *}
abbreviation s3 where  "s3 \<equiv> update_onebs s1 1 2 3 ((K$ None)(1 $:= Some (Cmd 1,1)))"
value "onebs s3 $ 1 $ 2 $ 1"

definition highest_voted :: "(nat \<Rightarrow>f ('a \<times> ('v cmd \<times> nat) option) list) \<Rightarrow> (nat \<Rightarrow>f ('v cmd) option)" where
  -- {* Makes sense only if no list in the map is empty. *}
  "highest_voted m \<equiv>
    let
        votes = (map snd) o$ m;
        highest = (\<lambda> l . (fold max l (l!0)) \<bind> (\<lambda> vb . Some (fst vb)))
    in highest o$ votes"

text {* The highest n which has been updated (excluding updates to the default). 
  The tentative below does not work.
  Basically we would need to sort the domain and carry a sorted list in the result,
  so that when we encounter a duplicate update then we can revise the max. *}

abbreviation test :: "nat \<Rightarrow>f bool \<Rightarrow> (bool \<times> nat)"
  where "test \<equiv> finfun_rec (\<lambda> (d::bool) . (d, 0)) 
    (\<lambda> k v r . if (v \<noteq> fst r) 
      then (fst r, max k (snd r)) else r)"

interpretation finfun_rec_wf "(\<lambda> (d::bool) . (d, 0::nat))"
  "(\<lambda> k v r . if (v \<noteq> fst r) then (fst r, max k (snd r)) else r)"
apply(unfold_locales)
apply auto[2]
defer
apply(simp split:split_if_asm)
apply auto
oops

text {* Instead of trying to define the max as a recursive function, let's use finfun_to_list. *}

value "finfun_to_list (((K$ False)(5 $:= True)(4 $:= False)(2 $:= True))::(nat \<Rightarrow>f bool))"

text {* 
  When a quorum of 1b messages is received, we complete all started instances by sending 2b messages containing a safe value.
  If an instance has not been started but a higher instance has been started, we complete
  it by sending a no-op message.
  TODO: why do we need the no-ops? we could also reuse instances where everything is safe...
  It's because holes block the execution of higher commands while we have no new client commands to propose.
  But that's unlikely under high load...
*}
fun receive_1b :: "'a \<Rightarrow> ('v,'a)msg \<Rightarrow> ('v,'a)mp_state \<Rightarrow> (('v,'a)msg set \<times> ('v,'a)mp_state)" where
 "receive_1b a (Phase1b last_vs new_bal a2) s = (
    if (Some new_bal = ballot s $ a)
    then (
      (let 
           new_state1 = update_onebs s a new_bal a2 last_vs;
           onebs' = at new_bal (onebs new_state1 a);
           quorum_received = 2 * length (at 1 onebs') > nr s;
           new_state2 = if (quorum_received)
            then new_state1\<lparr>leadership_acquired := (leadership_acquired new_state1)(a := 
              updated_at new_bal True (leadership_acquired new_state1 a))\<rparr>
            else new_state1;
           msgs =
            if (quorum_received)
            then
              let
                received = at new_bal (onebs new_state2 a);
                highest = rev (enumerate 1 (rev [highest_voted l . l \<leftarrow> received])); (* of the form [(n,v_1),(n-1,v_2)...] where v_i is safe at i *)
                msg =
                  (\<lambda> (i,opt) . (case opt of None \<Rightarrow> Some (Phase2a i new_bal NoOp a)
                    | Some v \<Rightarrow> Some (Phase2a i new_bal v a)));
                msgs =
                  [(case (msg x) of None \<Rightarrow> {} | Some m \<Rightarrow> send_all s a m) . x \<leftarrow> highest]
              in fold (op \<union>) msgs {}
            else {}
       in (new_state2, msgs)))
    else (s,{}))"
| "receive_1b a _ s = (s, {})"

definition is_leader where 
  "is_leader s a \<equiv> 
    case ballot s a of None \<Rightarrow> False | Some b \<Rightarrow> at b (leadership_acquired s a)"

fun receive_2a where
  "receive_2a a (Phase2a i b v l) s =
    (let bal = (ballot s a) in
      (if (bal = Some b)
      then (s\<lparr>vote := (vote s)(a := updated_at i (Some v) (vote s a) None)\<rparr>, {send_all s a (Phase2b i b a v)})
      else (s, {})))"
| "receive_2a a _ s = (s, {})"

fun receive_2b where
  "receive_2b a (Phase2b i b a2 v) s =
    (let s =
      (if (at i (decided s a) = None)
      then
        (let new_twobs = a2 # (at b (at i (twobs s a)))
        in
          (if (2 * length new_twobs > card (acceptors s))
          then
            s\<lparr>twobs := (twobs s)(a := updated_at i (updated_at b new_twobs (at i (twobs s a)) []) (twobs s a) []) \<rparr>
          else
            s\<lparr>twobs := (twobs s)(a := updated_at i (updated_at b new_twobs (at i (twobs s a)) []) (twobs s a) [] )\<rparr>))
      else
        s)
    in (s,{}))"
| "receive_2b a _ s = (s, ({}))"

(*,
              decided := (decided s)(a := updated_at i (Some v) (decided s a) None),
              log := (log s)(a := distinct_Sorted_Insert (i, v) (log s a))
*)

(* TODO: does not work... *)

definition test_state_3 where 
  "test_state_3 \<equiv> \<lparr>
    mp_state.acceptors = {1,2,3::int},
    ballot = (\<lambda> a . Some 2),
    vote = (\<lambda> a . []),
    last_ballot = (\<lambda> a . []),
    onebs = (\<lambda> a . if a = 1 then [[[(2, Some (Cmd 1, 1))]], [[]]] else []),
    twobs = (\<lambda> a . []),
    decided = (\<lambda> a .[]),
    highest_instance = (\<lambda> a . 1),
    pending = (\<lambda> a . [Some (Cmd (43::int))]),
    log = ( \<lambda> a . []),
    leadership_acquired = (\<lambda> a . [])
    \<rparr>"

value "at 1 (pending test_state_3 1)"

value "let 
  val = (42::int);
  instance = (1::nat);
  ballot = (2::nat);
  receiver = (1::int);
  from1 = (2::int);
  (s1,msgs1) = receive_2b receiver (Phase2b instance 1 from1 (Cmd val)) test_state_3
in at 1 (pending s1 1)"

value "let 
  val = (42::int);
  instance = (1::nat);
  ballot = (2::nat);
  receiver = (1::int);
  from1 = (2::int);
  (s1,msgs1) = receive_2b receiver (Phase2b instance ballot from1 (Cmd val)) test_state_3
in at 1 (twobs s1 1)"

(* A test of receive_2b 
value "let 
  val = (42::int);
  instance = (1::nat);
  ballot = (2::nat);
  receiver = (1::int);
  from1 = (2::int);
  (s1,msgs1) = receive_2b receiver (Phase2b instance ballot from1 (Cmd val)) test_state_1;
  from2 = (3::int);
  (s2,msgs2) = receive_2b receiver (Phase2b instance ballot from2 (Cmd val)) s1;
  twobs = at instance (at ballot (twobs s2 receiver));
  n = card (acceptors s)
in (twobs, msgs2, at instance (pending s2 receiver), at instance (decided s2 receiver))" *)

value "largestprefix [(1,v1), (2,v2), (4,v4)]"

export_code send_1a receive_1a receive_1b init_state propose receive_2a receive_2b receive_fwd 
  largestprefix is_leader in Scala file "simplePaxos.scala"

end