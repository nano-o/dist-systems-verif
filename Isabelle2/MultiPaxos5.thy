theory MultiPaxos5
imports Main  "~~/src/HOL/Library/Monad_Syntax" "~~/src/HOL/Library/Code_Target_Numeral"
  LinorderOption "~~/src/HOL/Library/FinFun_Syntax" "~~/src/HOL/Library/FSet"
  "../../IO-Automata/IOA" 
begin

text {* A version of MultiPaxos using FinFuns *}

text {* TODO: implement checkpointing *}

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

datatype 'v cmd = Cmd (the_val: 'v) | NoOp

type_synonym bal = nat
type_synonym inst = nat
type_synonym acc = nat

datatype 'v msg =
  Phase1a (from_leader: acc) (ballot:bal)
| Phase1b (last_votes:"inst \<Rightarrow>f (bal \<times> ('v cmd option))") (new_ballot: bal) (acceptor:acc)
| Phase2a (inst: inst) (for_ballot:bal) (suggestion:"'v cmd") (leader: acc)
| Phase2b (inst: inst) (ballot:bal) (acceptor: acc) (cmd: "'v cmd")
| Fwd (val: 'v)
  -- {* Forwards a proposal to another proposer (the leader) *}

datatype 'v packet =
  -- {* A message with sender/destination information *}
  Packet (sender: acc) (dst: acc) (msg: "'v msg")

record 'v consensus = 
  view :: "bal"
  accepts :: "acc list"
  status :: "nat"
    -- {* 0: not started; 1: processing; 2: closed *}
  val :: "'v cmd option"
  
record 'v state =
  id :: "acc"

  leader :: "bool"
  acceptors :: "acc list"
  propCmds :: "'v cmd list"

  ballot :: "bal"
  firstUncommitted :: "inst"

  onebs :: "bal \<Rightarrow>f inst \<Rightarrow>f (acc \<times> bal \<times> ('v cmd option)) list"
    -- {* For an acceptor a and a ballot b, lists of 1b-message descriptions, indexed by ballot then instance. *}

  next_inst :: "inst"
  instances :: "inst \<Rightarrow>f 'v consensus"
 
subsection {* A few functions to export to Scala for use by the runtime. *}

definition replicaCount where "replicaCount s \<equiv> length (acceptors s)"

definition get_ballot where "get_ballot s \<equiv> ballot s"

definition is_leader where "is_leader s \<equiv> leader s"

definition get_leader where 
  "get_leader s \<equiv> case ballot s of 0 \<Rightarrow> None | b \<Rightarrow> Some (b mod (replicaCount s))"

definition get_next_instance where
  "get_next_instance s \<equiv> next_inst s"

definition get_firstUncommitted where
  "get_firstUncommitted s = firstUncommitted s"

definition get_request::"inst \<Rightarrow> 'v state \<Rightarrow> 'v cmd option" where
  "get_request i s \<equiv> val (instances s $ i)"

definition leader_of_bal::"nat \<Rightarrow> nat \<Rightarrow> nat" where
  "leader_of_bal b n \<equiv> case b of 0 \<Rightarrow> 0 | bs \<Rightarrow> (bs mod n)" 

definition is_decided where "is_decided i s \<equiv> i < firstUncommitted s"

definition get_vote_num where
  "get_vote_num i s \<equiv> length (accepts (instances s $ i))"

definition get_status :: "inst \<Rightarrow> 'v state \<Rightarrow> nat" where
  "get_status i s \<equiv> status (instances s $ i)"

subsection {* Some auxiliary functions. *}

fun accs where
  "accs (0::nat) = []"
| "accs (Suc n) = (accs n) @ [n]"

fun generateBallot where 
  "generateBallot a (Suc b) N = (if ((Suc b) mod N = a) then (Suc b)
    else (generateBallot a b N))"
| "generateBallot a 0 N = 0"

definition nextBallot :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat"
  -- {* The smallest ballot belonging to replica a and greater than ballot b, when there are N replicas *}
  where "nextBallot a b N \<equiv> generateBallot a (b + N) N"

definition send_all where "send_all acc mesg s \<equiv> image (\<lambda> a2 . Packet acc a2 mesg) (set (acceptors s) - {acc})"

definition update_decided where 
  "update_decided i v s  \<equiv> s\<lparr>
    instances := (instances s)(i $:= (instances s $ i)\<lparr>status := 2, val := Some v\<rparr>)
\<rparr>"

definition update_accepts where
  "update_accepts i as s \<equiv> s\<lparr>instances := (instances s)(i $:= (instances s $ i)\<lparr>accepts := as\<rparr>)\<rparr>"

text {* If we had finfun_Ex we could do this better.
  Here we use instance 0 by default, but that's arbitrary. *}
definition quorum_received where
  "quorum_received b s \<equiv> 
    let at_b_i = onebs s $ b $ 0
    in 2 * length at_b_i > (replicaCount s)"

subsection {* Initialization of the state. *}

definition init_state :: "nat \<Rightarrow> acc \<Rightarrow> 'v state" where
  "init_state n a \<equiv> \<lparr>
    id = a,
    leader = False,
    acceptors = accs n,
    propCmds = [],

    ballot = 0,
    firstUncommitted = 1,

    onebs = K$ K$ [],

    next_inst = 1, (* instances start at 1 *)
    instances = K$ \<lparr>view = 0, accepts = [], status = 0, val = None\<rparr>
   \<rparr>"

subsection {* Functions that handle internal and external messages. *} 

definition addRequest where
  "addRequest v s \<equiv> (let pCmds = propCmds s; 
    newCmds = (if List.member pCmds v then pCmds else (pCmds @ [v])) in
      s\<lparr>propCmds := newCmds\<rparr>)"

definition onRequest where "onRequest v s \<equiv> addRequest v s"

definition send_2a where
  "send_2a v s \<equiv>
    let
      a = id s;
      inst = (next_inst s);
      b = (ballot s);
      msg = Phase2a inst b v a;
      s1 = addRequest v s;
      new_state = s1\<lparr>next_inst := (inst + 1),
        instances := (instances s1)(inst $:= (instances s1 $ inst)\<lparr>view := b, accepts := [a], status := 1, val := (Some v)\<rparr>)
       \<rparr>
    in
      (new_state, send_all a msg s)"

definition propose :: "'v \<Rightarrow> 'v state \<Rightarrow> ('v state \<times> 'v packet set)" where
  -- {* If leader, then go ahead with 2a, otherwise forward to the leader. *}
  "propose v s \<equiv> (let a = id s in if (leader s) then (send_2a (Cmd v) s)
      else (s, {Packet a (leader_of_bal (ballot s) (replicaCount s)) (Fwd v)}))"
 
(* What if the target process is not the leader anymore? TODO: Then let's forward it again. *)
definition receive_fwd  :: "'v \<Rightarrow> 'v state \<Rightarrow> ('v state \<times> 'v packet set)" where
  "receive_fwd v s \<equiv> (let a = id s in
    (if (leader_of_bal (ballot s) (replicaCount s) = a \<and> leader s) then send_2a (Cmd v) s else (s, {})))"

definition send_1a :: "'v state \<Rightarrow> ('v state \<times> 'v packet set)" where
  -- {* a tries to become the leader *}
  "send_1a s \<equiv>
    (let a = id s;
        b = nextBallot a (ballot s) (replicaCount s);
        msg_1a = Phase1a a b in
      (s\<lparr>ballot := b\<rparr>, send_all a msg_1a s))"

definition receive_1a :: "acc \<Rightarrow> bal \<Rightarrow> 'v state \<Rightarrow> ('v state \<times> 'v packet set)" where
  "receive_1a l b s \<equiv>
    (let a = id s; bal = ballot s in
      (if (bal < b)
       then
          (let
            insts = instances s;
            last_vs = ($view o$ insts, val o$ insts$);
            msg_1b = Phase1b last_vs b a;
            packet = Packet a l msg_1b;
            state = s\<lparr>ballot := b, leader := False\<rparr>(*Modified*)
          in
          (state, {packet}))
       else (s, {})))"

definition update_onebs :: 
  "'v state \<Rightarrow> bal \<Rightarrow> acc \<Rightarrow> (inst \<Rightarrow>f (bal \<times> ('v cmd option))) \<Rightarrow> 'v state" where
  -- {* Update the list of highest voted values when receiving a 1b
    message from a2 for ballot bal containing last_vs *}
  "update_onebs s b a last_vs \<equiv>
    let
      combiner = \<lambda> (xs, y) . (if (List.member xs (a, y)) then xs else ((a, y) # xs));
      pair_map = ($ (onebs s $ b), last_vs $);
      at_bal = combiner o$ pair_map
    in s\<lparr>onebs := (onebs s)(b $:= at_bal)\<rparr>"

definition highest_voted :: "(inst \<Rightarrow>f (acc \<times> bal \<times> ('v cmd option)) list) \<Rightarrow> (inst \<Rightarrow> ('v cmd option))" where
  -- {* Makes sense only if no list in the map is empty. *}
  "highest_voted onebs_bal \<equiv>
    let
        onebs_i = (\<lambda>i. (map (\<lambda>s. snd s) (onebs_bal $ i)));
        (*votes = (map snd) o$ m;
        highest = (\<lambda> l . if (l = []) then None else (fold max l (l!0)) \<bind> (\<lambda> vb . Some (fst vb)))*)
        highest = (\<lambda>bcl. if (bcl = []) then None else snd (fold (\<lambda>bc bc0. if (fst bc0 < fst bc) then bc else bc0) bcl (bcl!0)))
    in highest o onebs_i"

text {* 
  When a quorum of 1b messages is received, we complete all started instances by sending 2b messages containing a safe value.
  If an instance has not been started but a higher instance has been started, we complete
  it by sending a no-op message.
  TODO: why do we need the no-ops? we could also reuse instances where everything is safe...
  It's because holes block the execution of higher commands while we have no new client commands to propose.
  But that's unlikely under high load...

  For now we propose values to all the instances ever started.
*}
definition receive_1b :: "(inst \<Rightarrow>f (bal \<times> ('v cmd option))) \<Rightarrow> bal \<Rightarrow> acc \<Rightarrow> 'v state \<Rightarrow> ('v state \<times> 'v packet set)" where
 "receive_1b last_vs bal a2 s \<equiv> (let a = id s in
    if (bal = ballot s)
    then
      (let s1 = update_onebs s bal a2 last_vs
       in (if quorum_received bal s1
          then (let
              onebs_bal = onebs s1 $ bal;
              highestVoted = highest_voted onebs_bal;
              max_i = let l = (finfun_to_list onebs_bal) in (if l = [] then 0 else Max (set l));
              maxInst = (next_inst s1);
              (*Modified*)
              s2 = s1\<lparr>leader := True, next_inst := (if max_i + 1 < maxInst then maxInst else max_i + 1)\<rparr>;
              twoa_is = [(firstUncommitted s2)..<max_i+1];
              (* TODO: the following might traverse all the finfun, which is a problem when there are many instances. *)
              s3 = fold (\<lambda> i s . s\<lparr>instances := (instances s)(i $:= (instances s $ i)\<lparr>view := bal, accepts := [a],
                status := 1\<rparr>)\<rparr>) twoa_is s2;
              msgs = map (\<lambda> i . case highestVoted i of 
                  None \<Rightarrow> Phase2a i bal NoOp a
                | Some v \<Rightarrow> Phase2a i bal v a) twoa_is;
              pckts = map (\<lambda> m . send_all a m s3) msgs
            in (s3, fold (op \<union>) pckts {}) )
          else (s1, {}) ) )
    else (s, {}))"


definition receive_2_first  :: "inst \<Rightarrow> bal \<Rightarrow> 'v cmd \<Rightarrow> acc \<Rightarrow> 'v state \<Rightarrow> 'v state" where
 "receive_2_first i b v l s \<equiv>
    (let bal = (ballot s) in (
      if (bal \<le> b) then 
        (let a = id s; nas = replicaCount s; nextInst = (next_inst s) in
            (s\<lparr>ballot := b, next_inst := (if (i + 1) < nextInst then nextInst else (i + 1)),
              instances := (instances s)(i $:= (instances s $ i)\<lparr>view := b, accepts := [a,l],
                status := 2, val := (Some v)\<rparr>)\<rparr>))
     else s))"

definition receive_2_addl  :: "inst \<Rightarrow> bal \<Rightarrow> 'v cmd \<Rightarrow> acc \<Rightarrow> 'v state \<Rightarrow> 'v state" where
 "receive_2_addl i b v a2 s \<equiv>
    (let a = id s; bal = ballot s; accs = (accepts (instances s $ i)); nas = (replicaCount s) in
    if (List.member accs a2) then s 
    else (let s2 = update_accepts i (a2 # accs) s; votes = (get_vote_num i s2) in (
      if (2 * votes \<le> nas) then s2
      else (update_decided i v s2)))
    )"    
            
definition receive_2 :: "inst \<Rightarrow> bal \<Rightarrow> 'v cmd \<Rightarrow> acc \<Rightarrow> 'v state \<Rightarrow> 'v state" where
  "receive_2 i b v l s \<equiv>
  (if ((get_status i s) > 0) (* This is not the first message from the instance *)
     then (receive_2_addl i b v l s) 
  else (* This is the first message, treat like a propose *)
     (receive_2_first i b v l s)
  )"

definition receive_2a :: "inst \<Rightarrow> bal \<Rightarrow> 'v cmd \<Rightarrow> acc \<Rightarrow> 'v state \<Rightarrow> ('v state \<times> 'v packet set)" where
  "receive_2a i b v l s \<equiv> 
  if (ballot s \<le> b) then (let a = id s in
    (receive_2 i b v l s, send_all a (Phase2b i b a v) s))
  else (s, {})"

definition receive_2b :: "inst \<Rightarrow> bal \<Rightarrow> acc \<Rightarrow> 'v cmd  \<Rightarrow> 'v state \<Rightarrow> ('v state \<times> 'v packet set)" where
  "receive_2b i b a2 v s \<equiv> (receive_2 i b v a2 s, {})"

text {* output transition could return an option *}
definition learn :: "inst \<Rightarrow> 'v  \<Rightarrow> 'v state \<Rightarrow> ('v state \<times> 'v packet set) option" where 
  "learn i v s \<equiv> 
    case (get_request i s) of None \<Rightarrow> None |
      Some cm \<Rightarrow> (case cm of NoOp \<Rightarrow> None 
        | Cmd c \<Rightarrow> (if v = c then Some (s, {}) else None))"

subsection {* The I/O-automata *}

record 'v mp_state = 
  node_states :: "nat \<Rightarrow>f 'v state"
  network :: "'v packet fset"

datatype 'v mp_action =
  Receive_fwd acc acc 'v
| Propose acc "'v cmd"
| Send_1as acc
| Receive_1a_send_1b acc acc bal
| Receive_1b acc acc "inst \<Rightarrow>f (bal \<times> ('v cmd option))" bal
| Receive_2a_send_2b acc acc inst bal "'v cmd"
| Receive_2b acc acc inst bal "'v cmd"
| Learn acc inst "'v cmd"

definition mp_acceptors where "mp_acceptors n \<equiv> (accs n)"

locale mp_ioa = IOA +
  fixes nas :: nat
    -- {* The number of acceptors *}
begin

definition mp_acceptors where
  "mp_acceptors \<equiv> set (accs nas)"

definition mp_asig where
  "mp_asig \<equiv>
    \<lparr> inputs = { Propose a c | a c . a \<in> mp_acceptors},
      outputs = { Learn l i v | i v l . l \<in> mp_acceptors},
      internals = {Receive_fwd a1 a2 v | a1 a2 v . a1 \<in> mp_acceptors \<and> a2 \<in> mp_acceptors}
        \<union> {Send_1as a | a . a \<in> mp_acceptors}
        \<union> {Receive_1a_send_1b a1 a2 b | a1 a2 b . a1 \<in> mp_acceptors \<and> a2 \<in> mp_acceptors}
        \<union> {Receive_1b a1 a2 f b | a1 a2 f b . a1 \<in> mp_acceptors \<and> a2 \<in> mp_acceptors}
        \<union> {Receive_2a_send_2b a1 a2 i b c | a1 a2 i b c . a1 \<in> mp_acceptors \<and> a2 \<in> mp_acceptors}
        \<union> {Receive_2b a1 a2 i b c | a1 a2 i b c. a1 \<in> mp_acceptors \<and> a2 \<in> mp_acceptors}
        \<union> {Learn a i c | a i c . a \<in> mp_acceptors}\<rparr>"

fun init_nodes_state::"nat \<Rightarrow> nat \<Rightarrow>f 'a state" where
  "init_nodes_state (0::nat) = (K$ (init_state nas 0))"
| "init_nodes_state (Suc i) = (init_nodes_state i)(i $:= (init_state nas i))"

lemma init_acc: 
assumes "a \<ge> 0"
shows "(init_nodes_state (Suc a)) $ a = (init_state nas a)" using assms
by (induct a rule:init_nodes_state.induct, auto)

definition mp_start where
  "mp_start \<equiv> \<lparr>node_states = (init_nodes_state nas), network = {||}\<rparr>"

definition update_state where 
  "update_state a a_s packets s \<equiv>
    s\<lparr>node_states := (node_states s)(a $:= a_s),
      network := network s |\<union>| packets\<rparr>"

(*fun mp_transit where
  "mp_transit s (Receive_fwd src dest v) = (if Packet src dest (Fwd v) \<in> network s 
    then (let (new_s, ps) = receive_fwd dest v (node_states s $ dest) nas mp_acceptors in 
      update_state dest new_s ps s)
    else s)"
|  "mp_transit s (Propose a (Cmd v)) = (let (new_s, ps) = propose a v (node_states s $ a) nas mp_acceptors in
    update_state a new_s ps s)" 
| "mp_transit s (Receive_1a_send_1b src dest b) = (if (Packet src dest (Phase1a src b) \<in> network s) 
    then let (new_s, ps) = receive_1a dest src b (node_states s $ dest) in
      update_state dest new_s ps s 
    else s)"
| "mp_transit s (Send_1as l) = (let (new_s, ps) = send_1a l (node_states s $ l) nas mp_acceptors in
    update_state l new_s ps s)"
| "mp_transit s (Receive_1b src l vs b) = (if (Packet src l (Phase1b vs b src) \<in> network s)
    then let (new_s, ps) = receive_1b l vs b src (node_states s $ l) nas mp_acceptors in
      update_state l new_s ps s 
    else s)"
| "mp_transit s (Receive_2b a l i b cm) = (if (Packet a l (Phase2b i b a cm) \<in> network s)
    then let (new_s, ps) = receive_2b l i b a cm (node_states s $ l) nas in
      update_state l new_s ps s 
    else s)"
| "mp_transit s (Receive_2a_send_2b l dest i b cm) = (if (Packet l dest (Phase2a i b cm l) \<in> network s)
    then (let (new_s, ps) = receive_2a dest i b cm l (node_states s $ dest) nas mp_acceptors in
        update_state dest new_s ps s)
    else s)"
| "mp_transit s (Learn a i (Cmd v)) = (case (learn i v (node_states s $ a)) of (Some st) \<Rightarrow> 
  (let (new_s, ps) = st in update_state a new_s ps s)| None \<Rightarrow> s)"*)

end

(*global_interpretation mp_ioa_3:mp_ioa "3"
defines mp_start = mp_ioa_3.mp_start and mp_transit = mp_ioa_3.mp_transit
done

primrec accset where
  "accset 0 = {}"
  |"accset (Suc n) = insert n (accset n)"

definition safe_at::"'v mp_state \<Rightarrow> inst \<Rightarrow> nat \<Rightarrow> bool" where
  "safe_at s i nas \<equiv> (let acceptors = (accset nas) in
    \<forall>acc\<^sub>1 \<in> acceptors. \<forall>acc\<^sub>2 \<in> acceptors. (acc\<^sub>1 \<noteq> acc\<^sub>2) \<longrightarrow>
    (case (decided ((node_states s) $ acc\<^sub>1) $ i) of None \<Rightarrow> True |
      Some cm \<Rightarrow> (
        case (decided ((node_states s) $ acc\<^sub>2) $ i) of None \<Rightarrow> True |
          Some cs \<Rightarrow> (cm = cs))))"

definition ballot_constraint where
  "ballot_constraint s bound \<equiv>
    let 
      n_s = node_states s;
      bals = (\<lambda> a_s . ballot a_s) o$ n_s;
      as = finfun_to_list bals;
      bal_list = map (\<lambda> a . bals $ a) as;
      bal_list_sorted = sort bal_list;
      max_bal = if bal_list_sorted = [] then 0 else bal_list_sorted ! (length bal_list_sorted - 1)
    in
    max_bal \<le> bound"

definition inst_constraint where
  "inst_constraint s bound \<equiv>
    let 
      n_s = node_states s;
      insts = (\<lambda> a_s . next_inst a_s) o$ n_s;
      as = finfun_to_list insts;
      inst_list = map (\<lambda> a . insts $ a) as;
      inst_list_sorted = sort inst_list;
      max_inst = if inst_list_sorted = [] then 1 else inst_list_sorted ! (length inst_list_sorted - 1)
    in
    max_inst \<le> bound"*)

subsection {* Code generation *}

text {* We need to rename a few modules to let the Scala compiler resolve circular dependencies. *}
code_identifier
  code_module Code_Numeral \<rightharpoonup> (Scala) MicroCheckerLib
| code_module Groups \<rightharpoonup> (Scala) MicroCheckerLib
| code_module Rings \<rightharpoonup> (Scala) MicroCheckerLib
| code_module Optiona \<rightharpoonup> (Scala) MicroCheckerLib
| code_module List \<rightharpoonup> (Scala) MicroCheckerLib
| code_module FinFun \<rightharpoonup> (Scala) MicroCheckerLib
| code_module FSet \<rightharpoonup> (Scala) MicroCheckerLib
| code_module Cardinality \<rightharpoonup> (Scala) MicroCheckerLib
| code_module Fun \<rightharpoonup> (Scala) MicroCheckerLib
| code_module HOL \<rightharpoonup> (Scala) MicroCheckerLib
| code_module Product_Type \<rightharpoonup> (Scala) MicroCheckerLib
| code_module Phantom_Type \<rightharpoonup> (Scala) MicroCheckerLib
| code_module String \<rightharpoonup> (Scala) MicroCheckerLib
| code_module Orderings \<rightharpoonup> (Scala) MicroCheckerLib
| code_module Num \<rightharpoonup> (Scala) MicroCheckerLib
| code_module Finite_Set \<rightharpoonup> (Scala) MicroCheckerLib
| code_module Set \<rightharpoonup> (Scala) MicroCheckerLib
| code_module Nat \<rightharpoonup> (Scala) MicroCheckerLib
| code_module LinorderOption \<rightharpoonup> (Scala) MicroCheckerLib
| code_module Divides \<rightharpoonup> (Scala) MicroCheckerLib
| code_module Serialization  \<rightharpoonup> (Scala) MicroCheckerLib
| code_module Conditionally_Complete_Lattices \<rightharpoonup> (Scala) MicroCheckerLib
| code_module Complete_Lattices \<rightharpoonup> (Scala) MicroCheckerLib
| code_module Complete_Partial_Order \<rightharpoonup> (Scala) MicroCheckerLib
| code_module Lattices \<rightharpoonup> (Scala) MicroCheckerLib

fun processExternalEvent where
  "processExternalEvent (Phase1a l b) s = receive_1a l b s"
| "processExternalEvent (Phase1b last_vote b a) s = receive_1b last_vote b a s "
| "processExternalEvent (Phase2a i b cm l) s = receive_2a i b cm l s"
| "processExternalEvent (Phase2b i b a cm) s = receive_2b i b a cm s"
| "processExternalEvent (Fwd v) s = receive_fwd v s"

export_code learn onRequest send_1a propose init_state get_ballot is_leader get_leader 
  get_request propose processExternalEvent in Scala file "MultiPaxos5.scala"

end