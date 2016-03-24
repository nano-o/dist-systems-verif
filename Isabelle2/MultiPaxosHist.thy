theory MultiPaxosHist
imports 
  MultiPaxos3
begin

text {* A version of MultiPaxos with history variables added *}

text {* TODO: Prove that MultiPaxos refines it, preferrably automatically *}

record 'v mph_state =
  acceptors :: "acc fset"
    -- {* The set of all acceptors *}
  ballot :: "acc \<Rightarrow>f bal option"
    -- {* the highest ballot in which an acceptor participated *}
  vote :: "acc \<Rightarrow>f inst \<Rightarrow>f 'v cmd option"
    -- {* The last vote cast by an acceptor, for each instance *}
  vote_hist :: "inst \<Rightarrow>f acc \<Rightarrow>f bal \<Rightarrow>f 'v cmd option"
  last_ballot :: "acc \<Rightarrow>f nat \<Rightarrow>f bal option"
    -- {* For an acceptor a, this is the ballot in which "vote a" was cast, for each instance *}
  onebs :: "acc \<Rightarrow>f bal \<Rightarrow>f inst \<Rightarrow>f (acc \<times> ('v cmd \<times> bal) option) list"
    -- {* For an acceptor a and a ballot b, lists of 1b-message descriptions, indexed by ballot then instance. *}
  twobs :: "acc \<Rightarrow>f inst \<Rightarrow>f bal \<Rightarrow>f acc list"
    -- {* For an acceptor a: lists describing the 2b messages, indexed by instance then ballot. *}
  decided :: "acc \<Rightarrow>f inst \<Rightarrow>f 'v cmd option"
  next_inst :: "acc \<Rightarrow>f nat"
  pending :: "acc \<Rightarrow>f inst \<Rightarrow>f 'v cmd option"
  log :: "acc \<Rightarrow>f (nat \<times> 'v cmd) list"
  leader :: "acc \<Rightarrow>f bool" (* TODO: we don't need the ballot here, because it's only used for the current ballot. *)

definition init_state :: "acc fset \<Rightarrow> 'v mph_state" where
  "init_state accs \<equiv> \<lparr>
    mph_state.acceptors = accs,
    ballot = K$ None,
    vote = K$ K$ None,
    vote_hist = K$ K$ K$ None,
    last_ballot = K$ K$ None,
    onebs = K$ K$ K$ [],
    twobs = K$ K$ K$ [],
    decided = K$ K$ None,
    next_inst = K$ 1, (* instances start at 1 *)
    pending = K$ K$ None,
    log = K$ [],
    leader = K$ False \<rparr>"

definition nr where
  -- {* The number of replicas *}
  "nr s \<equiv> fcard (acceptors s)"

subsection {* Event handlers *}

text {* If we had finfun_Ex we could do this better.
  Here we use instance 0 by default, but that's arbitrary. *}
definition one_b_quorum_received where
  "one_b_quorum_received a b s \<equiv> 
    let at_b = onebs s $ a $ b;
        at_b_i = at_b $ 0
    in 2 * length at_b_i > nr s"

definition suc_bal :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat"
  -- {* The smallest ballot belonging to replica a and greater than ballot b, when there are N replicas *}
  where "suc_bal a b N \<equiv> (b div N + 1) * N + a"

fun nx_bal where
  "nx_bal a None N = suc_bal a 0 N"
| "nx_bal a (Some b) N = suc_bal a b N"

definition one_a_msgs where
  -- {* The set of 1a messages to send to try to become the leader *}
  "one_a_msgs a s \<equiv> 
    let
      next_bal = nx_bal a (ballot s $ a) (nr s);
      msg_1a = Phase1a a next_bal
    in {Packet a b msg_1a | b . b |\<in>| (acceptors s)}"

definition leader_of_bal where
  "leader_of_bal s b \<equiv> case b of None \<Rightarrow> 0 | Some b \<Rightarrow>
    (b mod (nr s))"

definition send_all where "send_all s sendr m \<equiv> fimage (\<lambda> a2 . Packet sendr a2 m)  (acceptors s)"

definition do_2a where
  "do_2a s a v \<equiv>
    let
      inst = (next_inst s $ a);
      msg = Phase2a inst (the (ballot s $ a)) v a;
      new_state = s\<lparr>next_inst := (next_inst s)(a $:= inst+1),
        pending := (pending s)(a $:= (pending s $ a)(inst $:= (Some v)))\<rparr>
    in
      (new_state, send_all s a msg)"

definition propose :: "acc \<Rightarrow> 'v \<Rightarrow> 'v mph_state \<Rightarrow> ('v mph_state \<times> 'v packet fset)" where
  -- {* If leader, then go ahead with 2a, otherwise forward to the leader. *}
  "propose a v s \<equiv>
    (if (leader_of_bal s (ballot s $ a) = a \<and> leader s $ a)
      then do_2a s a (Cmd v)
      else ( if (leader_of_bal s (ballot s $ a) = a)
        then (s,{||}) (* TODO: here we loose the proposal... *)
        else (s, {|Packet a (leader_of_bal s (ballot s $ a)) (Fwd (Cmd v))|})) )"
 
fun receive_fwd where
  "receive_fwd a (Fwd v) s = 
    (if (leader_of_bal s (ballot s $ a) = a) then do_2a s a v else (s, ({||})))"
| "receive_fwd a _ s = (s, ({||}))"

fun send_1a :: "acc \<Rightarrow> 'v mph_state \<Rightarrow> ('v mph_state \<times> 'v packet fset)" where
  -- {* a tries to become the leader *}
  "send_1a a s =
    (let
        b = nx_bal a (ballot s $ a) (nr s);
        msg_1a = Phase1a a b in
      (s\<lparr>ballot := (ballot s)(a $:= Some b)\<rparr>, fimage (\<lambda> a2 . Packet a a2 msg_1a) (acceptors s)))"

export_code send_1a in Scala

fun receive_1a :: "acc \<Rightarrow> 'v msg \<Rightarrow> 'v mph_state \<Rightarrow> ('v mph_state \<times> 'v packet fset)" where
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
          (state, {|packet|}))
       else (s, {||})))"
| "receive_1a a _ s = (s, {||})"

definition update_onebs :: 
  "'v mph_state \<Rightarrow> acc \<Rightarrow> bal \<Rightarrow> acc \<Rightarrow> (inst \<Rightarrow>f ('v cmd \<times> bal) option) \<Rightarrow> 'v mph_state" where
  -- {* Update the list of highest voted values when receiving a 1b
    message from a2 for ballot bal containing last_vs *}
  "update_onebs s a bal a2 last_vs \<equiv>
    let
      combiner = \<lambda> (xs, y) . (case y of None \<Rightarrow> (a2, None)#xs | Some z \<Rightarrow> (a2, Some z)#xs);
      pair_map = ($ (onebs s $ a $ bal), last_vs $);
      at_bal = combiner o$ pair_map
    in s\<lparr>onebs := (onebs s)(a $:= (onebs s $ a)(bal $:= at_bal))\<rparr>"

abbreviation s1 where 
  -- {* This is a state in which acceptor 1 is in ballot 2 and has received a ballot-2 1b message from
  acceptor 2 saying that acceptor 2 last voted in ballot 1 in instance 1 for value 1. *}
  "s1 \<equiv> \<lparr>
    mph_state.acceptors = {|1,2,3|},
    ballot = K$ Some 2,
    vote = K$ K$ None,
    vote_hist = K$ K$ K$ None,
    last_ballot = K$ K$ None,
    onebs = (K$ K$ K$ [])(1 $:= (K$ K$ [])(2 $:= (K$ [(2, None)])(1 $:= [(2, Some (Cmd 1,1))]))),
    twobs = K$ K$ K$ [],
    decided = K$ K$ None,
    next_inst = K$ 1,
    pending = K$ K$ None,
    log = K$ [],
    leader = K$ False \<rparr>"

value "onebs test_state_1 $ 1 $ 2 $ 1"

text {* State obtained after acceptor 1 receives a ballot-2 1b message from acceptor 3 saying that acceptor 3 never voted *}
abbreviation s2 where "s2 \<equiv> update_onebs s1 1 2 3 (K$ None)"
value "s2"
value "onebs s2 $ 1 $ 2 $ 1"

text {* State obtained after acceptor 1 receives a ballot-2 1b message from acceptor 3 saying that acceptor 3 last voted in instance 1 and ballot 1 for value 1 *}
abbreviation s3 where  "s3 \<equiv> update_onebs s1 1 2 3 ((K$ None)(1 $:= Some (Cmd 1,1)))"
value "onebs s3 $ 1 $ 2 $ 1"

definition highest_voted :: "(nat \<Rightarrow>f (acc \<times> ('v cmd \<times> nat) option) list) \<Rightarrow> (nat \<Rightarrow>f ('v cmd) option)" where
  -- {* Makes sense only if no list in the map is empty. *}
  "highest_voted m \<equiv>
    let
        votes = (map snd) o$ m;
        highest = (\<lambda> l . if (l = []) then None else (fold max l (l!0)) \<bind> (\<lambda> vb . Some (fst vb)))
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
value "((K$ False)(5 $:= True)(4 $:= False)(2 $:= True)) $ (2::int)"
value "finfun_to_list (((K$ False)(5 $:= True)(4 $:= False)(2 $:= True))::(nat \<Rightarrow>f bool))"

text {* 
  When a quorum of 1b messages is received, we complete all started instances by sending 2b messages containing a safe value.
  If an instance has not been started but a higher instance has been started, we complete
  it by sending a no-op message.
  TODO: why do we need the no-ops? we could also reuse instances where everything is safe...
  It's because holes block the execution of higher commands while we have no new client commands to propose.
  But that's unlikely under high load...

  For now we propose values to all the instances ever started.
*}
fun receive_1b :: "acc \<Rightarrow> 'v msg \<Rightarrow> 'v mph_state \<Rightarrow> ('v mph_state \<times> 'v packet fset)" where
 "receive_1b a (Phase1b last_vs bal a2) s = (
    if (Some bal = ballot s $ a)
    then
      (let s1 = update_onebs s a bal a2 last_vs
       in (if one_b_quorum_received a bal s1 
          then (let
              h = highest_voted (onebs s1 $ a $ bal);
              max_i = let l = (finfun_to_list (onebs s1 $ a $ bal)) in (if l = [] then 0 else hd (rev l));
              s2 = s1\<lparr>leader := (leader s1)(a $:= True)\<rparr>;
              s3 = s2\<lparr>next_inst := (next_inst s2)(a $:= max_i+1)\<rparr>;
              twoa_is = [1..<max_i+1];
              msgs = map (\<lambda> i . case h $ i of 
                  None \<Rightarrow> Phase2a i bal NoOp a
                | Some v \<Rightarrow> Phase2a i bal v a) twoa_is;
              pckts = map (\<lambda> m . send_all s a m) msgs
            in (s3, fold (op |\<union>|) pckts {||}) )
          else (s1, {||}) ) )
    else (s, {||}))"
| "receive_1b a _ s = (s, {||})"

fun receive_2a :: "acc \<Rightarrow> 'v msg \<Rightarrow> 'v mph_state \<Rightarrow> ('v mph_state \<times> 'v packet fset)" where
  "receive_2a a (Phase2a i b v l) s =
    (let bal = (ballot s $ a) in
      (if (bal = Some b)
        then (s\<lparr>vote := (vote s)(a $:= (vote s $ a)(i $:= Some v)),
          vote_hist := (vote_hist s)(i $:= (vote_hist s $ i)(a $:= (vote_hist s $ i $ a)(b $:= Some v)))\<rparr>, send_all s a (Phase2b i b a v))
        else (s, {||})))"
| "receive_2a a _ s = (s, {||})"

fun receive_2b :: "acc \<Rightarrow> 'v msg \<Rightarrow> 'v mph_state \<Rightarrow> ('v mph_state \<times> 'v packet fset)" where
  "receive_2b a (Phase2b i b a2 v) s =
    (if (decided s $ a $ i = None)
      then
        (let 
            new_twobs = a2 # (twobs s $ a $ i $ b);
            s2 = s\<lparr>twobs := (twobs s)(a $:= (twobs s $ a)(i $:= (twobs s $ a $ i)(b $:= new_twobs)))\<rparr>
        in
          (if (2 * length new_twobs > nr s)
            then let
                s3 = s2\<lparr>decided := (decided s2)(a $:= (decided s2 $ a)(i $:= Some v))\<rparr>;
                s4 = s3\<lparr>log := (log s2)(a $:= distinct_Sorted_Insert (i, v) (log s $ a))\<rparr>
              in
                (s4, {||})
            else
              (s2, {||}) ) )
      else
        (s, {||}) )"
| "receive_2b a _ s = (s, {||})"

end