theory MultiPaxos3
imports Main  "~~/src/HOL/Library/Monad_Syntax" "~~/src/HOL/Library/Code_Target_Nat"
  LinorderOption "~~/src/HOL/Library/FinFun_Syntax" "~~/src/HOL/Library/FSet"
  "../../IO-Automata/IOA"
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

type_synonym bal = nat
type_synonym inst = nat
type_synonym acc = nat

datatype 'v msg =
  Phase1a (from_leader: acc) (ballot:bal)
| Phase1b (last_votes:"inst \<Rightarrow>f ('v cmd \<times> bal) option") (new_ballot: bal) (acceptor:acc)
| Phase2a (inst: inst) (for_ballot:bal) (suggestion:"'v cmd") (leader: acc)
| Phase2b (inst: inst) (ballot:bal) (acceptor: acc) (cmd: "'v cmd")
| Vote (inst: inst) (cmd: "'v cmd")
  -- {* Instructs a learner that a value has been decided. Not used for now... *}
| Fwd (val: 'v)
  -- {* Forwards a proposal to another proposer (the leader) *}

datatype 'v  packet =
  -- {* A message with sender/destination information *}
  Packet (sender: acc) (dst: acc) (msg: "'v msg")

record 'v acc_state =
  id :: acc
  acceptors :: "acc fset"
    -- {* The set of all acceptors *}
  ballot :: "bal option"
    -- {* the highest ballot in which an acceptor participated *}
  vote :: "inst \<Rightarrow>f 'v cmd option"
    -- {* The last vote cast by an acceptor, for each instance *}
  last_ballot :: "nat \<Rightarrow>f bal option"
    -- {* For an acceptor a, this is the ballot in which "vote a" was cast, for each instance *}
  onebs :: "bal \<Rightarrow>f inst \<Rightarrow>f (acc \<times> ('v cmd \<times> bal) option) list"
    -- {* For an acceptor a and a ballot b, lists of 1b-message descriptions, indexed by ballot then instance. *}
  twobs :: "inst \<Rightarrow>f bal \<Rightarrow>f acc list"
    -- {* For an acceptor a: lists describing the 2b messages, indexed by instance then ballot. *}
  decided :: "inst \<Rightarrow>f 'v cmd option"
  next_inst :: "nat"
  pending :: "inst \<Rightarrow>f 'v cmd option"
  leader :: "bool"

fun accs where
  "accs (0::nat) = {||}"
| "accs (Suc n) = (accs n) |\<union>| {|Suc n|}"

definition init_acc_state :: "nat \<Rightarrow> acc \<Rightarrow> 'v acc_state" where
  "init_acc_state n a \<equiv> \<lparr>
    id = a,
    acc_state.acceptors = accs n,
    ballot = None,
    vote = K$ None,
    last_ballot = K$ None,
    onebs = K$ K$ [],
    twobs = K$ K$ [],
    decided = K$ None,
    next_inst = 1, (* instances start at 1 *)
    pending = K$ None,
    leader = False \<rparr>"

definition nr where
  -- {* The number of replicas *}
  "nr s \<equiv> fcard (acceptors s)"

subsection {* Event handlers *}

text {* If we had finfun_Ex we could do this better.
  Here we use instance 0 by default, but that's arbitrary. *}
definition one_b_quorum_received where
  "one_b_quorum_received b s \<equiv> 
    let at_b = onebs s $ b;
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
  "one_a_msgs s \<equiv> 
    let
      a = id s;
      next_bal = nx_bal a (ballot s) (nr s);
      msg_1a = Phase1a a next_bal
    in {Packet a b msg_1a | b . b |\<in>| (acceptors s)}"

definition leader_of_bal where
  "leader_of_bal s b \<equiv> case b of None \<Rightarrow> 0 | Some b \<Rightarrow>
    (b mod (nr s))"

definition send_all where "send_all s m \<equiv> fimage (\<lambda> a2 . Packet (id s) a2 m)  (acceptors s)"

definition do_2a where
  "do_2a s v \<equiv>
    let
      a = id s;
      inst = (next_inst s);
      msg = Phase2a inst (the (ballot s)) v a;
      new_state = s\<lparr>next_inst := (inst+1),
        pending := (pending s)(inst $:= (Some v))\<rparr>
    in
      (new_state, send_all s msg)"

definition propose :: "'v \<Rightarrow> 'v acc_state \<Rightarrow> ('v acc_state \<times> 'v packet fset)" where
  -- {* If leader, then go ahead with 2a, otherwise forward to the leader. *}
  "propose v s \<equiv> let a = id s in
    (if (leader_of_bal s (ballot s) = a \<and> leader s)
      then do_2a s (Cmd v)
      else ( if (leader_of_bal s (ballot s) = a)
        then (s,{||}) (* TODO: here we loose the proposal... *)
        else (s, {|Packet a (leader_of_bal s (ballot s)) (Fwd v)|})) )"
 
(* TODO: what if the target process is not the leader anymore *)
definition receive_fwd  :: "'v \<Rightarrow> 'v acc_state \<Rightarrow> ('v acc_state \<times> 'v packet fset)" where
  "receive_fwd v s \<equiv> let a = id s in 
    (if (leader_of_bal s (ballot s) = a) then do_2a s (Cmd v) else (s, ({||})))"

definition send_1a :: "'v acc_state \<Rightarrow> ('v acc_state \<times> 'v packet fset)" where
  -- {* a tries to become the leader *}
  "send_1a s \<equiv>
    (let
        a = id s;
        b = nx_bal a (ballot s) (nr s);
        msg_1a = Phase1a a b in
      (s\<lparr>ballot := Some b\<rparr>, fimage (\<lambda> a2 . Packet a a2 msg_1a) (acceptors s)))"

definition receive_1a :: "acc \<Rightarrow> bal \<Rightarrow> 'v acc_state \<Rightarrow> ('v acc_state \<times> 'v packet fset)" where
  "receive_1a l b s \<equiv>
    (let bal = ballot s; a = id s in
      (if (bal = None \<or> ((the bal) < b))
       then
          (let
            combiner = (\<lambda> (vo,bo) . vo \<bind> (\<lambda> v . bo \<bind> (\<lambda> b . Some (v,b))));
            last_votes = combiner o$ ($ vote s, last_ballot s $);
            msg_1b = Phase1b last_votes b a;
            packet = Packet a l msg_1b;
            state = s\<lparr>ballot := Some b\<rparr>
          in
          (state, {|packet|}))
       else (s, {||})))"

definition update_onebs :: 
  "'v acc_state \<Rightarrow> bal \<Rightarrow> acc \<Rightarrow> (inst \<Rightarrow>f ('v cmd \<times> bal) option) \<Rightarrow> 'v acc_state" where
  -- {* Update the list of highest voted values when receiving a 1b
    message from a2 for ballot bal containing last_vs *}
  "update_onebs s bal a2 last_vs \<equiv>
    let
      a = id s;
      combiner = \<lambda> (xs, y) . (case y of None \<Rightarrow> (a2, None)#xs | Some z \<Rightarrow> (a2, Some z)#xs);
      pair_map = ($ (onebs s $ bal), last_vs $);
      at_bal = combiner o$ pair_map
    in s\<lparr>onebs := (onebs s)(bal $:= at_bal)\<rparr>"

definition highest_voted :: "(nat \<Rightarrow>f (acc \<times> ('v cmd \<times> nat) option) list) \<Rightarrow> (nat \<Rightarrow>f ('v cmd) option)" where
  -- {* Makes sense only if no list in the map is empty. *}
  "highest_voted m \<equiv>
    let
        votes = (map snd) o$ m;
        highest = (\<lambda> l . if (l = []) then None else (fold max l (l!0)) \<bind> (\<lambda> vb . Some (fst vb)))
    in highest o$ votes"

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
definition receive_1b :: "(inst \<Rightarrow>f ('v cmd \<times> bal) option) \<Rightarrow> bal \<Rightarrow> acc \<Rightarrow> 'v acc_state \<Rightarrow> ('v acc_state \<times> 'v packet fset)" where
 "receive_1b last_vs bal a2 s \<equiv> (let a = id s in (
    if (Some bal = ballot s)
    then
      (let s1 = update_onebs s bal a2 last_vs
       in (if one_b_quorum_received bal s1 
          then (let
              h = highest_voted (onebs s1 $ bal);
              max_i = let l = (finfun_to_list (onebs s1 $ bal)) in (if l = [] then 0 else hd (rev l));
              s2 = s1\<lparr>leader := True\<rparr>;
              s3 = s2\<lparr>next_inst := max_i+1\<rparr>;
              twoa_is = [1..<max_i+1];
              msgs = map (\<lambda> i . case h $ i of 
                  None \<Rightarrow> Phase2a i bal NoOp a
                | Some v \<Rightarrow> Phase2a i bal v a) twoa_is;
              pckts = map (\<lambda> m . send_all s m) msgs
            in (s3, fold (op |\<union>|) pckts {||}) )
          else (s1, {||}) ) )
    else (s, {||})) )"

definition receive_2a :: "inst \<Rightarrow> bal \<Rightarrow> 'v cmd \<Rightarrow> acc \<Rightarrow> 'v acc_state \<Rightarrow> ('v acc_state \<times> 'v packet fset)" where
  "receive_2a i b v l s =
    (let a = id s; bal = (ballot s) in
      (if (bal = Some b)
        then (s\<lparr>vote := (vote s)(i $:= Some v)\<rparr>, send_all s (Phase2b i b a v))
        else (s, {||})))"

definition receive_2b :: "inst \<Rightarrow> bal \<Rightarrow> acc \<Rightarrow> 'v cmd  \<Rightarrow> 'v acc_state \<Rightarrow> ('v acc_state \<times> 'v packet fset)" where
  "receive_2b i b a2 v s \<equiv> let a = id s in 
    (if (decided s $ i = None)
      then
        (let 
            new_twobs = a2 # (twobs s $ i $ b);
            s2 = s\<lparr>twobs := (twobs s)(i $:= (twobs s $ i)(b $:= new_twobs))\<rparr>
        in
          (if (2 * length new_twobs > nr s)
            then (s2\<lparr>decided := (decided s2)(i $:= Some v)\<rparr>, {||})
            else (s2, {||}) ) )
      else
        (s, {||}) )"

value "largestprefix [(1,v1), (2,v2), (4,v4)]"

text {* output transition could return an option *}
definition learn :: "inst \<Rightarrow> 'v  \<Rightarrow> 'v acc_state \<Rightarrow> ('v acc_state \<times> 'v packet fset) option" where 
  "learn i v s \<equiv> 
    case (decided s $ i) of None \<Rightarrow> None |
      Some cm \<Rightarrow> (case cm of NoOp \<Rightarrow> None 
        | Cmd c \<Rightarrow> (if v = c then Some (s, {||}) else None))"

fun process_msg where
  "process_msg (Phase1a l b) s = receive_1a l b s"
| "process_msg (Phase1b lvs b a) s = receive_1b lvs b a s"
| "process_msg (Phase2a i b cm l) s = receive_2a i b cm l s"
| "process_msg (Phase2b i b a cm) s = receive_2b i b a cm s"
| "process_msg (Vote i cm) s = undefined"
| "process_msg (Fwd v) s = receive_fwd v s"

export_code learn process_msg in Scala file "simplePaxos.scala"

section {* The I/O-automata *}

record 'v mp_state = 
  node_states :: "nat \<Rightarrow>f 'v acc_state"
  network :: "'v packet fset"

datatype 'v mp_action =
  Receive_fwd acc acc 'v
| Propose acc 'v
| Send_1as acc
| Receive_1a_send_1b acc acc bal
| Receive_1b acc acc "inst \<Rightarrow>f ('v cmd \<times> bal) option" bal
| Receive_2a_send_2b acc acc inst bal "'v cmd"
| Receive_2b acc acc inst bal "'v cmd"
| Learn acc inst 'v

locale mp_ioa = IOA +
  fixes nas :: nat
    -- {* The number of acceptors *}
begin    

text {* TODO: get rid of this! *}
no_notation Append  (infixl "#" 65)
notation Cons (infixr "#" 65)
no_notation Concat  (infixl "@" 65)
notation append (infixr "@" 65)

definition mp_asig where
  "mp_asig \<equiv>
    \<lparr> inputs = { Propose a c | a c . a |\<in>| accs nas},
      outputs = { Learn l i v | i v l . l |\<in>| accs nas},
      internals = {Receive_fwd a1 a2 v | a1 a2 v . a1 |\<in>| accs nas \<and> a2 |\<in>| accs nas}
        \<union> {Send_1as a | a . a |\<in>| accs nas}
        \<union> {Receive_1a_send_1b a1 a2 b | a1 a2 b . a1 |\<in>| accs nas \<and> a2 |\<in>| accs nas}
        \<union> {Receive_1b a1 a2 f b | a1 a2 f b . a1 |\<in>| accs nas \<and> a2 |\<in>| accs nas}
        \<union> {Receive_2a_send_2b a1 a2 i b c | a1 a2 i b c . a1 |\<in>| accs nas \<and> a2 |\<in>| accs nas}
        \<union> {Receive_2b a1 a2 i b c | a1 a2 i b c. a1 |\<in>| accs nas \<and> a2 |\<in>| accs nas}
        \<union> {Learn a i c | a i c . a |\<in>| accs nas}\<rparr>"

fun init_nodes_state where
  "init_nodes_state (0::nat) n = undefined"
| "init_nodes_state (Suc i) n = (init_nodes_state i n)(Suc i $:= init_acc_state n (Suc i))"

lemma init_acc: 
assumes "a \<le> n" and "a > 0"
shows "(init_nodes_state a n) $ a = init_acc_state n a" using assms
by (induct a n arbitrary:n rule:init_nodes_state.induct, auto)

definition mp_start where
  "mp_start \<equiv> {\<lparr>node_states = (init_nodes_state nas nas), network = {||}\<rparr>}"

definition update_state where 
  "update_state a a_s packets s \<equiv>
    s\<lparr>node_states := (node_states s)(a $:= a_s),
      network := network s |\<union>| packets\<rparr>"

inductive mp_trans where
  "mp_trans (s, Propose a v, 
    let (new_s, ps) = propose v (node_states s $ a) in
      update_state a new_s ps s)"
| "Packet src dest (Fwd v) |\<in>| network s \<Longrightarrow>
      mp_trans (s, Receive_fwd src dest v, 
        let (new_s, ps) = receive_fwd v (node_states s $ dest) in 
          update_state a new_s ps s)"
| "\<lbrakk>Packet src dest (Phase1a l b) |\<in>| network s; l = src\<rbrakk> \<Longrightarrow> 
    mp_trans (s, Receive_1a_send_1b src dest b, 
      let (new_s, ps) = receive_1a l b (node_states s $ dest) in 
          update_state dest new_s ps s)"
| "mp_trans (s, Send_1as l,
    let (new_s, ps) = send_1a (node_states s $ l) in
      update_state l new_s ps s)"
| "\<lbrakk>Packet src l (Phase1b vs b a) |\<in>| network s; src = a\<rbrakk> \<Longrightarrow>
    mp_trans (s, Receive_1b src l vs b,
    let (new_s, ps) = receive_1b vs b l (node_states s $ l) in
      update_state l new_s ps s)"
| "\<lbrakk>Packet src l (Phase2b i b a cm) |\<in>| network s; src = a\<rbrakk> \<Longrightarrow>
    mp_trans (s, Receive_2b a l i b cm,
    let (new_s, ps) = receive_2b i b l cm (node_states s $ l) in
      update_state l new_s ps s)"
| "\<lbrakk>Packet src dest (Phase2a i b cm l) |\<in>| network s; src = l\<rbrakk> \<Longrightarrow>
    mp_trans (s, Receive_2a_send_2b l dest i b cm,
    let (new_s, ps) = receive_2a i b cm dest (node_states s $ dest) in
      update_state dest new_s ps s)"
| "learn i v (node_states s $ a) = Some (new_s, ps) \<Longrightarrow> 
    mp_trans (s, Learn a i v, update_state a new_s ps s)"

definition p_ioa where
  "p_ioa \<equiv> \<lparr>ioa.asig = mp_asig, start = mp_start, trans = {(s,a,t) . mp_trans (s, a, t)}\<rparr>"

end

end