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

  onebs :: "inst \<Rightarrow>f (acc \<times> bal \<times> ('v cmd option)) list"
    -- {* For an acceptor a and a ballot b, lists of 1b-message descriptions, indexed by ballot then instance. *}

  next_inst :: "inst"
  instances :: "inst \<Rightarrow>f 'v consensus"

datatype 'v msg =
  Phase1a (from_leader: acc) (leader_ballot:bal) (firstUndecided: inst)
| Phase1b (last_votes:"'v consensus list") (new_ballot: bal) (ballot_acceptor:acc)
| Phase2a (vote_inst: inst) (for_ballot:bal) (suggestion:"'v cmd") (vote_leader: acc)
| Phase2b (decide_inst: inst) (decide_ballot:bal) (decide_acceptor: acc) (decide_cmd: "'v cmd")
| Fwd (decide_val: 'v)
  -- {* Forwards a proposal to another proposer (the leader) *}

datatype 'v packet =
  -- {* A message with sender/destination information *}
  Packet (sender: acc) (dst: acc) (msg: "'v msg")

 
subsection {* A few functions to export to Scala for use by the runtime. *}

definition def_replicaCount where "def_replicaCount s \<equiv> length (acceptors s)"

definition def_getBallot where "def_getBallot s \<equiv> ballot s"

definition def_isLeader where "def_isLeader s \<equiv> leader s"

definition def_getLeader where 
  "def_getLeader s \<equiv> case ballot s of 0 \<Rightarrow> None | b \<Rightarrow> Some (b mod (def_replicaCount s))"

definition def_getNextInstance where
  "def_getNextInstance s \<equiv> next_inst s"

definition def_getFirstUncommitted where
  "def_getFirstUncommitted s = firstUncommitted s"

definition def_getRequest::"inst \<Rightarrow> 'v state \<Rightarrow> 'v cmd option" where
  "def_getRequest i s \<equiv> val (instances s $ i)"

definition def_leaderOfBal::"nat \<Rightarrow> nat \<Rightarrow> nat" where
  "def_leaderOfBal b n \<equiv> case b of 0 \<Rightarrow> 0 | bs \<Rightarrow> (bs mod n)" 

definition def_isDecided where "def_isDecided i s \<equiv> (status (instances s $ i) = 2)"

definition def_getVoteNum where
  "def_getVoteNum i s \<equiv> length (accepts (instances s $ i))"

definition def_getInstances where
  "def_getInstances s \<equiv> instances s"

definition def_getInsts where
  "def_getInsts insts = finfun_to_list insts"

definition def_getView where "def_getView cs \<equiv> view cs"
definition def_getAccepts where"def_getAccepts cs \<equiv> accepts cs"
definition def_getStatus where "def_getStatus cs \<equiv> status cs"
definition def_getValue where "def_getValue cs \<equiv> val cs"

definition def_setView where "def_setView b cs \<equiv> cs\<lparr>view := b\<rparr>"
definition def_setAccepts where "def_setAccepts as cs \<equiv> cs\<lparr>accepts := as\<rparr>"
definition def_setStatus where "def_setStatus s cs \<equiv> cs\<lparr>status := s\<rparr>"
definition def_setValue where "def_setValue v cs \<equiv> cs\<lparr>val := v\<rparr>"

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

fun take_request :: "'v cmd list \<Rightarrow> 'v cmd option \<Rightarrow> ('v cmd \<times> 'v cmd list)" where
  "take_request [] None = (NoOp, [])"
  |"take_request (x#xs) None = (x, xs)"
  |"take_request vs (Some v) = (v, vs)"

fun construct_msg :: "'v cmd list \<Rightarrow> 'v cmd option list \<Rightarrow> ('v cmd list \<times> 'v cmd list)" where
  "construct_msg vs [] = ([], vs)"|
  "construct_msg [] (x#xs) = (let (newvs, newvcs) = (take_request [] x) in
    (newvs # (fst (construct_msg [] xs)), []))"|
  "construct_msg as (x#xs) = (let (newvs, newvcs) = (take_request as x); 
    (newvs1, newvcs1) = (construct_msg newvcs xs)
    in (newvs#newvs1, newvcs1))"

definition emptyOBS :: "inst \<Rightarrow>f (acc \<times> bal \<times> ('v cmd option)) list" where "emptyOBS = (K$ [])"
definition emptyInstances :: "inst \<Rightarrow>f 'v consensus" where "emptyInstances = (K$ \<lparr>view = 0, accepts = [], status = 0, val = None\<rparr>)"
definition addInstance :: "inst \<Rightarrow> 'v consensus \<Rightarrow> (inst \<Rightarrow>f 'v consensus) \<Rightarrow> (inst \<Rightarrow>f 'v consensus)" where 
  "addInstance i nConsensus insts = (insts(i $:= nConsensus))"

definition send_all where "send_all acc mesg s \<equiv> map (\<lambda> a2 . Packet acc a2 mesg) (remove1 acc (acceptors s))"

text {* If we had finfun_Ex we could do this better.
  Here we use instance 0 by default, but that's arbitrary. *}
definition quorum_received where
  "quorum_received i s \<equiv> 
    let at_b_i = onebs s $ i
    in 2 * length at_b_i > (def_replicaCount s)"

text {* Finfun Filter/Merge for snapshots / catch ups *}

definition finfun_filt:: "('a::linorder \<Rightarrow>f 'b) \<Rightarrow>('a \<Rightarrow> bool) \<Rightarrow> ('a::linorder \<Rightarrow>f 'b)" where
  "finfun_filt ff filt \<equiv> fold (\<lambda> k l . if (filt k) then (l) else ((l)(k $:= (ff $ k)))) (finfun_to_list ff) (K$ (finfun_default ff)) "
definition finfun_filt_le :: "'a::linorder \<Rightarrow>f 'b \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow>f 'b" where
  "finfun_filt_le ff truncloc\<equiv> finfun_filt ff (\<lambda> k . (k \<le> truncloc))"
definition finfun_filt_ge :: "'a::linorder \<Rightarrow>f 'b \<Rightarrow>  'a \<Rightarrow> 'a \<Rightarrow>f 'b" where
  "finfun_filt_ge ff truncloc\<equiv> finfun_filt ff (\<lambda> k . (k \<ge> truncloc))"
definition finfun_replace:: "('a::linorder \<Rightarrow>f 'b) \<Rightarrow> ('a::linorder \<Rightarrow>f 'b)  \<Rightarrow> ('a::linorder \<Rightarrow>f 'b)" where
  "finfun_replace from_ff to_ff \<equiv> fold (\<lambda> k l . (l)(k $:= (from_ff $ k)) ) (finfun_to_list from_ff) to_ff "
definition finfun_maxinst:: "(inst \<Rightarrow>f 'b) \<Rightarrow> inst" where
  "finfun_maxinst ff\<equiv> fold (\<lambda> k l . if (k > l) then k else l) (finfun_to_list ff) 0"
definition finfun_remove:: "('a::linorder \<Rightarrow>f 'b) \<Rightarrow> ('a \<Rightarrow>f 'b) \<Rightarrow> ('a \<Rightarrow>f 'b)" where
  "finfun_remove ff ff_remove \<equiv> fold (\<lambda> k l . (l)(k $:= (finfun_default l) )) (finfun_to_list ff_remove) ff"
definition finfun_deserialize where
 "finfun_deserialize l \<equiv> foldr (\<lambda> kv r . finfun_update_code r (fst kv) (snd kv)) l (K$ None)"
definition finfun_serialize where
 "finfun_serialize vs \<equiv> (let insts = finfun_to_list vs; ilength = length insts; iter = [0..<ilength] in
     map (\<lambda>i. vs $ (insts!i)) iter)"

subsection {* Initialization of the state. *}

definition init_state :: "nat \<Rightarrow> acc \<Rightarrow> 'v state" where
  "init_state n a \<equiv> \<lparr>
    id = a,
    leader = False,
    acceptors = accs n,
    propCmds = [],

    ballot = 0,
    firstUncommitted = 1,

    onebs = K$ [],

    next_inst = 1, (* instances start at 1 *)
    instances = K$ \<lparr>view = 0, accepts = [], status = 0, val = None\<rparr>
   \<rparr>"

subsection {* Functions that handle internal and external messages. *} 

definition def_onRequest where
  "def_onRequest v s \<equiv> (let pCmds = propCmds s; 
    newCmds = (if List.member pCmds v then pCmds else (pCmds @ [v])) in
      s\<lparr>propCmds := newCmds\<rparr>)"

definition def_send1a :: "'v state \<Rightarrow> ('v state \<times> 'v packet list)" where
  -- {* a tries to become the leader *}
  "def_send1a s \<equiv>
    (let a = id s;
        b = nextBallot a (ballot s) (def_replicaCount s);
        i = firstUncommitted s;
        msg_1a = Phase1a a b i in
      (s\<lparr>ballot := b, onebs := K$ []\<rparr>, send_all a msg_1a s))"

definition def_receive1a :: "acc \<Rightarrow> bal \<Rightarrow> inst \<Rightarrow> 'v state \<Rightarrow> ('v state \<times> 'v packet list)" where
  "def_receive1a l b i s \<equiv>
    (let bal = ballot s in
      (if (bal < b)
       then
          (let a = id s;
            insts = finfun_filt_le (instances s) i;
            msg_1b = Phase1b insts b a;
            packet = Packet a l msg_1b;
            state = s\<lparr>ballot := b, leader := False, onebs := K$ []\<rparr>
          in
          (state, [packet]))
       else (s, [])))"

definition update_onebs where
  -- {* Update the list of highest voted values when receiving a 1b
    message from a2 for ballot bal containing last_vs *}
  "update_onebs s a last_vs \<equiv>
    let
      combiner = \<lambda> (xs, y) . (if (List.member xs (a, y)) then xs else ((a, y) # xs));
      pair_map = ($ (onebs s), last_vs $);
      at_bal = combiner o$ pair_map
    in s\<lparr>onebs := at_bal\<rparr>"

definition highest_voted where
  -- {* Makes sense only if no list in the map is empty. *}
  "highest_voted onebs_bal \<equiv>
    let
      onebs_i = (\<lambda>i. map (\<lambda>obs. snd obs) (onebs_bal $ i));
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

definition def_receive1b :: "('v consensus list) \<Rightarrow> bal \<Rightarrow> acc \<Rightarrow> 'v state \<Rightarrow> ('v state \<times> 'v packet list)" where
 "def_receive1b last_vs bal a2 s \<equiv> (
    if (bal = ballot s)
    then (let a = id s; i = (firstUncommitted s); s1 = update_onebs s a2 last_vs in 
      (if quorum_received i s1
          then (let
              onebs_bal = onebs s1;
              max_i = (let l = (finfun_to_list onebs_bal) in (if l = [] then 0 else hd (rev l)));
              maxInst = (next_inst s1);
              s2 = s1\<lparr>leader := True, next_inst := (if max_i + 1 < maxInst then maxInst else max_i + 1)\<rparr>;
              insts = [i..<max_i+1];
              highestVoted = highest_voted onebs_bal;
              pCmds = (propCmds s2);
              cmdOptions = map (\<lambda> i . highestVoted i) insts;
              (newCmds, newPCmds) = construct_msg pCmds cmdOptions;
              msgs = map (\<lambda>v. Phase2a i bal v a) newCmds;
              s3 = fold (\<lambda> i s . s\<lparr>propCmds := newPCmds, instances := (instances s)(i $:= (instances s $ i)\<lparr>view := bal, 
                accepts := [a], status := 1, val := (highestVoted i)\<rparr>)\<rparr>) insts s2;
              pckts = map (\<lambda> m . send_all a m s3) msgs
            in (s3, fold (op @) pckts []))
      else (s1, []) ) )
    else (s, []))"

definition def_send2a where
  "def_send2a i v s \<equiv>
    let
      a = id s;
      inst = (next_inst s);
      b = (ballot s);
      msg = Phase2a inst b v a;
      new_state = s\<lparr>next_inst := (if i + 1 < inst then inst else i + 1),
        instances := (instances s)(i $:= (instances s $ i)\<lparr>view := b, accepts := [a], status := 1, val := (Some v)\<rparr>)
       \<rparr>
    in
      (new_state, send_all a msg s)"

definition def_propose :: "'v \<Rightarrow> 'v state \<Rightarrow> ('v state \<times> 'v packet list)" where
  -- {* If leader, then go ahead with 2a, otherwise forward to the leader. *}
  "def_propose v s \<equiv> (let a = id s in 
    if (leader s) then (def_send2a (next_inst s) (Cmd v) s)
    else (s, [Packet a (def_leaderOfBal (ballot s) (def_replicaCount s)) (Fwd v)]))"
 
(* What if the target process is not the leader anymore? TODO: Then let's forward it again. *)
definition def_receiveFwd :: "'v \<Rightarrow> 'v state \<Rightarrow> ('v state \<times> 'v packet list)" where
  "def_receiveFwd v s \<equiv> (let a = id s in
    (if (def_leaderOfBal (ballot s) (def_replicaCount s) = a \<and> leader s) then def_send2a (next_inst s) (Cmd v) s
    else (s, [])))"

definition def_receive2_first  :: "inst \<Rightarrow> bal \<Rightarrow> 'v cmd \<Rightarrow> acc \<Rightarrow> 'v state \<Rightarrow> 'v state" where
 "def_receive2_first i b v l s \<equiv>
    (let bal = (ballot s) in (
      if (bal \<le> b) then
        (let a = id s; nas = def_replicaCount s; nextInst = (next_inst s); 
            nInst = (if (i + 1) < nextInst then nextInst else (i + 1)); fUncommitted = (firstUncommitted s);
            fUndecide = (if (i + 1) < fUncommitted then fUncommitted else (i + 1)) in
          if (4 \<le> nas) 
            then s\<lparr>ballot := b, next_inst := nInst, instances := (instances s)(i $:= (instances s $ i)\<lparr>view := b, 
              accepts := [a,l], status := 1, val := (Some v)\<rparr>)\<rparr>
          else s\<lparr>ballot := b, next_inst := nInst, firstUncommitted := fUndecide, 
            instances := (instances s)(i $:= (instances s $ i)\<lparr>view := b, 
              accepts := [a,l], status := 2, val := (Some v)\<rparr>)\<rparr>)
     else s))"

definition def_receive2_addl  :: "inst \<Rightarrow> bal \<Rightarrow> acc \<Rightarrow> 'v state \<Rightarrow> 'v state" where
 "def_receive2_addl i b a2 s \<equiv>
    (let a = id s; accs = (accepts (instances s $ i)); nas = (def_replicaCount s) in
    if (List.member accs a2) then s
    else (let newaccs = (a2 # accs); votes = length newaccs in (
      if (2 * votes \<le> nas) 
        then s\<lparr>instances := (instances s)(i $:= (instances s $ i)\<lparr>accepts := newaccs\<rparr>)\<rparr>
      else (let fUncommitted = (firstUncommitted s) in 
        s\<lparr>firstUncommitted := (if (i + 1) < fUncommitted then fUncommitted else (i + 1)), 
          instances := (instances s)(i $:= (instances s $ i)\<lparr>accepts := newaccs, status := 2\<rparr>)\<rparr>
    ))))"
            
definition def_receive2 :: "inst \<Rightarrow> bal \<Rightarrow> 'v cmd \<Rightarrow> acc \<Rightarrow> 'v state \<Rightarrow> 'v state" where
  "def_receive2 i b v l s \<equiv> (let i_status = (def_getStatus (instances s $ i)) in
  (if (i_status > 0) (* This is not the first message from the instance *)
     then (def_receive2_addl i b l s)
  else (* This is the first message, treat like a propose *)
     (def_receive2_first i b v l s)
))"

definition def_receive2a :: "inst \<Rightarrow> bal \<Rightarrow> 'v cmd \<Rightarrow> acc \<Rightarrow> 'v state \<Rightarrow> ('v state \<times> 'v packet list)" where
  "def_receive2a i b v l s \<equiv> 
  if (ballot s \<le> b) then (let a = id s in
    (def_receive2 i b v l s, send_all a (Phase2b i b a v) s))
  else (s, [])"

definition def_receive2b :: "inst \<Rightarrow> bal \<Rightarrow> acc \<Rightarrow> 'v cmd  \<Rightarrow> 'v state \<Rightarrow> ('v state \<times> 'v packet list)" where
  "def_receive2b i b a2 v s \<equiv> (def_receive2 i b v a2 s, [])"

text {* output transition could return an option *}
definition def_learn :: "inst \<Rightarrow> 'v  \<Rightarrow> 'v state \<Rightarrow> ('v state \<times> 'v packet list) option" where 
  "def_learn i v s \<equiv> 
    case (def_getRequest i s) of None \<Rightarrow> None |
      Some cm \<Rightarrow> (case cm of NoOp \<Rightarrow> None 
        | Cmd c \<Rightarrow> (if v = c then Some (s, []) else None))"

subsection {* Code generation *}

text {* We need to rename a few modules to let the Scala compiler resolve circular dependencies. *}
code_identifier
  code_module Code_Numeral \<rightharpoonup> (Scala) MPLib
| code_module Groups \<rightharpoonup> (Scala) MPLib
| code_module Rings \<rightharpoonup> (Scala) MPLib
| code_module Optiona \<rightharpoonup> (Scala) MPLib
| code_module List \<rightharpoonup> (Scala) MPLib
| code_module FinFun \<rightharpoonup> (Scala) MPLib
| code_module FSet \<rightharpoonup> (Scala) MPLib
| code_module Cardinality \<rightharpoonup> (Scala) MPLib
| code_module Fun \<rightharpoonup> (Scala) MPLib
| code_module HOL \<rightharpoonup> (Scala) MPLib
| code_module Product_Type \<rightharpoonup> (Scala) MPLib
| code_module Phantom_Type \<rightharpoonup> (Scala) MPLib
| code_module String \<rightharpoonup> (Scala) MPLib
| code_module Orderings \<rightharpoonup> (Scala) MPLib
| code_module Num \<rightharpoonup> (Scala) MPLib
| code_module Finite_Set \<rightharpoonup> (Scala) MPLib
| code_module Set \<rightharpoonup> (Scala) MPLib
| code_module Nat \<rightharpoonup> (Scala) MPLib
| code_module LinorderOption \<rightharpoonup> (Scala) MPLib
| code_module Divides \<rightharpoonup> (Scala) MPLib
| code_module Serialization  \<rightharpoonup> (Scala) MPLib
| code_module Conditionally_Complete_Lattices \<rightharpoonup> (Scala) MPLib
| code_module Complete_Lattices \<rightharpoonup> (Scala) MPLib
| code_module Complete_Partial_Order \<rightharpoonup> (Scala) MPLib
| code_module Lattices \<rightharpoonup> (Scala) MPLib

fun processExternalEvent where
  "processExternalEvent (Phase1a l b i) s = def_receive1a l b i s"
| "processExternalEvent (Phase1b last_vote b a) s = def_receive1b last_vote b a s "
| "processExternalEvent (Phase2a i b cm l) s = def_receive2a i b cm l s"
| "processExternalEvent (Phase2b i b a cm) s = def_receive2b i b a cm s"
| "processExternalEvent (Fwd v) s = def_receiveFwd v s"

export_code def_learn def_onRequest def_send1a def_propose init_state def_getBallot def_isLeader def_getLeader def_getNextInstance 
  def_getFirstUncommitted def_getRequest def_leaderOfBal def_isDecided def_getStatus processExternalEvent
    finfun_deserialize def_getView def_getAccepts def_getStatus def_getValue def_getInstances def_getInsts
      def_setView def_setAccepts def_setStatus def_setValue emptyOBS emptyInstances addInstance 
        finfun_serialize in Scala file "MultiPaxos5.scala"

end