theory MultiPaxos2
imports Main  "~~/src/HOL/Library/Monad_Syntax" "~~/src/HOL/Library/Code_Target_Nat"
  Log LinorderOption
begin

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

subsection {* Nat maps *}

text {* 
Maps from nat to 'a where only a finite subset of nat maps to a non-default value. 
Example: a map describing the value decided in each instance.

Constraint: good access speed to the highest non-default mappings.
For now this is not the case because of the length computation. 

Implemented with Lists indexed starting from the end, along with the default value.

Related to FinFuns.

TODO: reimplementing all the features of finfun is a bit too much.
Note that we only need the "fast access to tail" optimisation in 2a/2b, which don't need fancy
features. But, the log maintenance needs a fancy features: max.
*}

type_synonym 'a nat_map = "'a \<times> 'a list"

definition pos 
  -- {* the position of element i in the list *}
  where "pos i l \<equiv> length l - i"

definition at where "at i m \<equiv> 
  let l = snd m in (if (i \<le> length l) then l!(pos i l) else fst m)"

value "at 1 (43, [42,2,3,4,(5::int)])"

fun pad where
  -- {* pad with n copies of d *}
  "pad 0 l d = l"
| "pad (Suc n) l d = pad n (d#l) d"

value "pad 0 [1,2::int] 42"

definition pad_to where
  -- {* pad with copies of d to obtain a list of size n*}
  "pad_to n l d \<equiv> let len = length l in if (n > len) then pad (n-len) l d else l"

value "pad_to 4 [1::int] 42"

definition updated_at where
  "updated_at i x m \<equiv> let l = snd m in (fst m, (pad_to i l (fst m))[(pos i l) := x])"

value "updated_at 8 42 (43,[1,2,3,4,(5::int)])"

value "at 9 (updated_at 8 42 (43,[1,2,3,4,(5::int)]))"

fun combine_from_max :: "nat \<Rightarrow> 'a nat_map \<Rightarrow> 'b nat_map \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'c nat_map" where
  -- {* TODO: inefficient implementation. *}
  "combine_from_max 0 m1 m2 f = (f (fst m1) (fst m2), [])"
| "combine_from_max (Suc n) m1 m2 f = 
    updated_at (Suc n) (f (at (Suc n) m1) (at (Suc n) m2)) (combine_from_max n m1 m2 f)"

definition combine where
  "combine m1 m2 f \<equiv> 
    let max = max (length (snd m1)) (length (snd m2))
    in combine_from_max max m1 m2 f"

definition list_to_nm :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a nat_map" where 
  "list_to_nm l d \<equiv> (d,l)"

definition default_nm where "default_nm d \<equiv> (d,[])"

definition map_nm :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a nat_map \<Rightarrow> 'b nat_map" where
  "map_nm f m \<equiv> (f (fst m), map f (snd m))"

value "map_nm (\<lambda> x . x+1) (list_to_nm [3,4] (1::int))"

value "combine (0, [1,(2::int)]) (0, [42]) (\<lambda> x y . x + y)"

(* export_code updated_at combine in Scala *)

subsection {* Actions, messages, and state. *}

datatype 'v cmd = Cmd 'v | NoOp

datatype ('v,'a) msg =
  Phase1a (leader: 'a) (ballot:nat)
| Phase1b (last_votes:"('v cmd \<times> nat) option nat_map") (new_ballot: nat) (acceptor:'a)
  -- {* last_vote contains the list of all instances in which the sender has participated, 
    along with the highest ballot in which it voted and the corresponding value.
    The intended meaning is also that the acceptor 
    did not participate in any instance numbered greater than the length of the list. *}
| Phase2a (inst: nat) (for_ballot:nat) (suggestion:'v) (leader: 'a)
| Phase2b (inst: nat) (ballot:nat) (acceptor: 'a) (val: 'v)
| Vote (inst: nat) (val: 'v)
  -- {* Instructs a learner that a value has been decided. Not used for now... *}
| Fwd (val: 'v)
  -- {* Forwards a proposal to another proposer (the leader) *}

datatype ('v,'a)  packet =
  -- {* A message with sender/destination information *}
  Packet (sender: 'a) (dst: 'a) (msg: "('v,'a) msg")

text {* The state. Grows with time and is copied a lot, which means the generated code is slow. 
  Ideas to improve access and modification time to large structures: 
  1) Use a diff array where arrays are needed (see JinjaThreads/Diff_Array.html, which relies on an unverified implementation).
  2) Use SepRef.
  On might be a good quick hack to start with. 

  We have two types of growing data-structure: lists and functions (whose domain grow).
  We would like to access and modify those structures in constant time, or bound their size to a small value.
  First thing: convert the "nat => x" functions to lists (since we mostly access the front, that should make it faster).
  Then we need fast log maintenance (Ian's code).

  Problem: to promote head list access, we need to track the size of lists...
*}

type_synonym bal = nat

text {* Warning: ballots start at 1 in this formalization *}

record ('v, 'a) mp_state =
  acceptors :: "'a set"
    -- {* The set of all acceptors *}
  ballot :: "'a \<Rightarrow> bal option"
    -- {* the highest ballot in which an acceptor participated *}
  vote :: "'a \<Rightarrow> 'v cmd option nat_map"
    -- {* The last vote cast by an acceptor, for each instance *}
  last_ballot :: "'a \<Rightarrow> bal option nat_map"
    -- {* For an acceptor a, this is the ballot in which "vote a" was cast, for each instance *}
  onebs :: "'a \<Rightarrow> ('a \<times> ('v cmd \<times> bal) option) list nat_map nat_map"
    -- {* For an acceptor a and a ballot b, lists of 1b-message descriptions, indexed by ballot then instance. *}
  twobs :: "'a \<Rightarrow> 'a list nat_map nat_map"
    -- {* For an acceptor a: lists describing the 2b messages, indexed by instance then ballot. *}
  decided :: "'a \<Rightarrow> 'v cmd option nat_map"
  highest_instance :: "'a \<Rightarrow> nat"
  pending :: "'a \<Rightarrow> 'v cmd option nat_map" (* Useless now because we added the command to the 2b messages *)
  log :: "'a \<Rightarrow> (nat \<times> 'v cmd) list"
  leadership_acquired :: "'a \<Rightarrow> bool nat_map"

definition init_state :: "'a set \<Rightarrow> ('v,'a) mp_state" where
  "init_state accs \<equiv> \<lparr>
    mp_state.acceptors = accs,
    ballot = (\<lambda> a . None),
    vote = (\<lambda> a . default_nm None),
    last_ballot = (\<lambda> a . default_nm None),
    onebs = (\<lambda> a . default_nm (default_nm [])),
    twobs = (\<lambda> a . default_nm (default_nm [])),
    decided = (\<lambda> a . default_nm None),
    highest_instance = (\<lambda> a . 0),
    pending = (\<lambda> a . default_nm None),
    log = ( \<lambda> a . []),
    leadership_acquired = (\<lambda> a . default_nm False)
    \<rparr>"

definition nr where
  -- {* The number of replicas *}
  "nr s \<equiv> card (acceptors s)"


subsection {* Event handlers *}

definition one_b_quorum where
  "one_b_quorum a i b s \<equiv> 
    let at_b = at b (onebs s a);
        at_b_i = at i at_b 
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
      next_bal = nx_bal a (ballot s a) (card (acceptors s));
      msg_1a = Phase1a a next_bal
    in {Packet a b msg_1a | b . b \<in> (acceptors s)}"

definition leader where
  "leader s b \<equiv> case b of None \<Rightarrow> 0 | Some b \<Rightarrow>
    (b mod (nr s))"

definition send_all where "send_all s sendr m \<equiv> {Packet sendr a2 m | a2 . a2 \<in> acceptors s}"

definition do_2a where
  "do_2a s a v \<equiv>
    let
      inst = highest_instance s a + 1;
      msg = Phase2a inst (the (ballot s a)) v a;
      new_state = s\<lparr>highest_instance := (highest_instance s)(a := inst),
        pending := (pending s)(a := updated_at inst (Some v) (pending s a))\<rparr>
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
    send a list containing the highest vote cast in every instance the acceptor participated in. *}
  "receive_1a a (Phase1a l b) s =
    (let bal = ballot s a in
      (if (bal = None \<or> ((the bal) < b))
       then
          (let
            is = case bal of None \<Rightarrow> [] | Some b \<Rightarrow>  [0..<(Suc b)];
            get_vote = (\<lambda> i . (at i (vote s a)) \<bind> (\<lambda> v . (at i (last_ballot s a)) \<bind> (\<lambda> b . Some (v, b))));
            votes = list_to_nm [get_vote i . i \<leftarrow> is] None;
            msg_1b = Phase1b votes b a;
            packet = Packet a l msg_1b;
            state = s\<lparr>ballot := (ballot s)(a := Some b)\<rparr>
          in
          (state, {packet}))
       else (s,{})))"
| "receive_1a a _ s = (s,{})"

definition update_onebs :: "('v, 'a)mp_state \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> ('v cmd \<times> nat) option nat_map \<Rightarrow> ('v, 'a)mp_state" where
  -- {* Update the list of highest voted values when receiving a 1b
    message from a2 for ballot bal containing last_vs *}
  "update_onebs s a bal a2 last_vs \<equiv>
    let
      combiner = \<lambda> xs y . (case y of None \<Rightarrow> (a2, None)#xs | Some z \<Rightarrow> (a2, Some z)#xs);
      at_bal = combine (at bal (onebs s a)) last_vs combiner
    in
      s\<lparr>onebs := (onebs s)(a := updated_at bal at_bal (onebs s a))\<rparr>"

definition test_state_1 where 
  -- {* This is a state in which acceptor 1 is in ballot 2 and has received a ballot-2 1b message from
  acceptor 2 saying that acceptor 2 last voted in ballot 1 in instance 1 for value 1. *}
  "test_state_1 \<equiv> \<lparr>
    mp_state.acceptors = {1,2,3::int},
    ballot = (\<lambda> a . Some 2),
    vote = (\<lambda> a . default_nm None),
    last_ballot = (\<lambda> a . default_nm None),
    onebs = (\<lambda> a . if a = 1 then list_to_nm [list_to_nm [[],[(2, Some (Cmd 1, 1))]] [], default_nm []] (default_nm []) else default_nm (default_nm [])),
    twobs = (\<lambda> a . default_nm (default_nm [])),
    decided = (\<lambda> a .default_nm None),
    highest_instance = (\<lambda> a . 1),
    pending = (\<lambda> a . default_nm None),
    log = ( \<lambda> a . []),
    leadership_acquired = (\<lambda> a . default_nm False)
    \<rparr>"

value "onebs test_state_1 1"

value "at 1 (at 2 (onebs test_state_1 1))"

text {* State obtained after acceptor 1 receives a ballot-2 1b message from acceptor 3 saying that acceptor 3 never voted *}
value "update_onebs test_state_1 1 2 3 (default_nm None)"
value "at 1 (at 2 (onebs (update_onebs test_state_1 1 2 3 (default_nm None)) 1))"
text {* State obtained after acceptor 1 receives a ballot-2 1b message from acceptor 3 saying that acceptor 3 last voted in ballot 1 for value 1 *}
value "update_onebs test_state_1 1 2 3 (list_to_nm [Some (Cmd 1,1)] None)"
value "at 1 (at 2 (onebs (update_onebs test_state_1 1 2 3 (list_to_nm [Some (Cmd 1,1)] None)) 1))"
abbreviation test_state_2 where  "test_state_2 \<equiv> update_onebs test_state_1 1 2 3 (list_to_nm [Some (Cmd 1,1)] None)"

definition highest_voted :: "('a \<times> ('v cmd \<times> nat) option) list nat_map \<Rightarrow> 'v cmd" where
  -- {* Given a list describing the ballot-n 1b messages received by an acceptor, is the highest voted value. 
        Problem: highest needs to be a map_nm too, but here we need to access the internal representation
        because we don't have recursion or fold (finfun has). 
        TODO: since this is only for leadership acquisition, which is rare, we could just use finfun and 
        accept the performance drawback. *}
  "highest_voted m \<equiv> 
    let
        votes = map_nm (map snd) m;
        highest = (\<lambda> i . fold max (at i votes) ((at i votes)!0))
    in NoOp"

text {* 
  When a quorum of 1b messages is received, we complete all started instances by sending 2b messages containing a safe value.
  If an instance has not been started but a higher instance has been started, we complete
  it by sending a no-op message. 
  TODO: why do we need the no-ops? we could also reuse instances where everything is safe...
*}
fun receive_1b :: "'a \<Rightarrow> ('v,'a)msg \<Rightarrow> ('v,'a)mp_state \<Rightarrow> (('v,'a)msg set \<times> ('v,'a)mp_state)" where
 "receive_1b a (Phase1b last_vs new_bal a2) s = (
    if (new_bal = the (ballot s a))
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