theory MultiPaxos4
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
| Phase1b (last_votes:"inst \<Rightarrow>f ('v cmd \<times> bal) option") (new_ballot: bal) (acceptor:acc)
| Phase2a (inst: inst) (for_ballot:bal) (suggestion:"'v cmd") (leader: acc)
| Phase2b (inst: inst) (ballot:bal) (acceptor: acc) (cmd: "'v cmd")
| Vote (inst: inst) (cmd: "'v cmd")
  -- {* Instructs a learner that a value has been decided. Not used for now... *}
| Fwd (val: 'v)
  -- {* Forwards a proposal to another proposer (the leader) *}
| CatchUpReq (inst_start: inst) (inst_end: inst) (acceptor: acc)
  -- {* Forwards a request for catch up to the leader. *}
| CatchUpRes (catchupdes:"inst \<Rightarrow>f 'v cmd option") 
  -- {* The instances required to catch up *}
datatype 'v  packet =
  -- {* A message with sender/destination information *}
  Packet (sender: acc) (dst: acc) (msg: "'v msg")

datatype 'v internal_event =
  NoEvent | Commit "'v cmd"
 
record 'v acc_state =
  id :: acc
  leader :: "bool"
  acceptors :: "acc fset"
    -- {* The set of all acceptors *}

  ballot :: "bal option"
  decided :: "inst \<Rightarrow>f 'v cmd option"
    -- {* the highest ballot in which an acceptor participated *}
  vote :: "inst \<Rightarrow>f 'v cmd option"
    -- {* The last vote cast by an acceptor, for each instance *}
  last_ballot :: "inst \<Rightarrow>f bal option"
    -- {* For an acceptor a, this is the ballot in which "vote a" was cast, for each instance *}
  onebs :: "bal \<Rightarrow>f inst \<Rightarrow>f (acc \<times> ('v cmd \<times> bal) option) list"
    -- {* For an acceptor a and a ballot b, lists of 1b-message descriptions, indexed by ballot then instance. *}
  twobs :: "inst \<Rightarrow>f bal \<Rightarrow>f acc list"
    -- {* For an acceptor a: lists describing the 2b messages, indexed by instance then ballot. *}

  next_inst :: "nat"
  last_decision :: "nat option"
  working_instances :: "inst \<Rightarrow>f bool" 

  commit_buffer :: "inst \<Rightarrow>f 'v cmd option"
  last_committed :: "inst"

  snapshot_reference :: "inst"
   -- {* The point strictly one less that the starting point for all the logs. The instance number at which the 
         database is caught up too. *}
  snapshot_proposal :: "inst list"
   -- {* A list that contains requested points to conduct snapshot. *}

  pending :: "inst \<Rightarrow>f 'v cmd option" (*Possibly useless *)
  
  catch_up_requested :: "nat"
   -- {* Zero if no catch up on going, else set to the leader that we are requesting a catch up from. *}

fun accs where
  "accs (0::nat) = {||}"
| "accs (Suc n) = (accs n) |\<union>| {|n|}"

subsection {* Utility functions. *}

definition send_all where "send_all s a m \<equiv> fimage (\<lambda> a2 . Packet (id s) a2 m)  (acceptors s |-| {|a|})"

definition def_GetReplicaCount where
  -- {* The number of replicas *}
  "def_GetReplicaCount s \<equiv> fcard (acceptors s)"
definition leader_of_bal where
  "leader_of_bal s b \<equiv> case b of None \<Rightarrow> 0 | Some b \<Rightarrow>
    (b mod (def_GetReplicaCount s))"

text {* A few functions to export to Scala for use by the runtime. *}

definition def_IntEvtHandler_GetLeader where "def_IntEvtHandler_GetLeader s \<equiv> ballot s"

definition def_IntEvtHander_IsLeader where "def_IntEvtHander_IsLeader s \<equiv> leader s"

definition def_IntEvtHander_GetLeader where 
  "def_IntEvtHander_GetLeader s \<equiv> case ballot s of Some (b::nat) \<Rightarrow> Some (b mod (def_GetReplicaCount s)) | _ \<Rightarrow> None"

datatype 'v inst_status = s_not_participated | s_pending "'v cmd" | s_decided (decision:"'v cmd")

definition get_instance_info where
  "get_instance_info s i \<equiv> 
    case decided s $ i of Some c \<Rightarrow> s_decided c | _ \<Rightarrow> (
      case pending s $ i of Some c \<Rightarrow> s_pending c | _ \<Rightarrow> s_not_participated )"
definition get_next_instance where
  "get_next_instance s \<equiv> next_inst s"

text {* Finfun Filter/Merge for snapshots / catch ups *}

definition finfun_filter_advanced:: "('a::linorder \<Rightarrow>f 'b) \<Rightarrow>('a \<Rightarrow> bool) \<Rightarrow> ('a::linorder \<Rightarrow>f 'b)" where
  "finfun_filter_advanced ff filt_test\<equiv> fold (\<lambda> k l . if (filt_test k) then (l) else ((l)( k $:= (ff $ k)))) (finfun_to_list ff) (K$ (finfun_default ff)) "
definition finfun_filter_lteq :: "'a::linorder \<Rightarrow>f 'b \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow>f 'b" where
  "finfun_filter_lteq ff  truncloc\<equiv> finfun_filter_advanced ff (\<lambda> k . (k \<le> truncloc))"
definition finfun_filter_gteq :: "'a::linorder \<Rightarrow>f 'b \<Rightarrow>  'a \<Rightarrow> 'a \<Rightarrow>f 'b" where
  "finfun_filter_gteq ff truncloc\<equiv> finfun_filter_advanced ff (\<lambda> k . (k \<ge> truncloc))"
definition finfun_merge:: "('a::linorder \<Rightarrow>f 'b) \<Rightarrow> ('a::linorder \<Rightarrow>f 'b)  \<Rightarrow> ('a::linorder \<Rightarrow>f 'b)" where
  "finfun_merge from_ff to_ff \<equiv> fold (\<lambda> k l . finfun_update_code l  k (from_ff $ k) ) (finfun_to_list from_ff) to_ff "
value "let ff = ((K$ 0) :: int \<Rightarrow>f int)(1 $:= 42)(42 $:= 0)(43 $:= 1); 
          ff2 = ((K$ 0) :: int \<Rightarrow>f int)(1 $:= 42)(42 $:= 0)(20 $:= 1)  in (finfun_default ff) "

subsection {* State Manipulating Utility Functions *}

definition def_ProposeInstance :: "'v \<Rightarrow> 'v acc_state \<Rightarrow> ('v acc_state \<times> 'v packet fset)" where
  -- {* If leader, then go ahead with 2a, otherwise forward to the leader. *}
  " def_ProposeInstance v s \<equiv> let a = id s in
    (if (leader_of_bal s (ballot s) = a \<and> leader s)
      then 
      let
      a = id s;
      inst = (next_inst s);
      b = the (ballot s);
      msg = Phase2a inst b (Cmd v) a;
      new_state = s\<lparr>next_inst := (inst+1),
        pending := finfun_update_code (pending s) inst (Some (Cmd v)),
        twobs := finfun_update_code (twobs s) inst ((K$ [])(b $:= [a])),
        working_instances := (working_instances s)(inst $:=True) (* Added by ian to track working instances *)
       \<rparr>
    in
      (new_state, send_all s a msg) 
      else ( if (leader_of_bal s (ballot s) = a)
        then (s,{||}) (* TODO: here we loose the proposal... *)
        else (s, {|Packet a (leader_of_bal s (ballot s)) (Fwd v)|})) )"

subsection {* External Event handlers *}


 
(* Depreciated version.
definition receive_fwd  :: "'v \<Rightarrow> 'v acc_state \<Rightarrow> ('v acc_state \<times> 'v packet fset)" where
  "receive_fwd v s \<equiv> let a = id s in 
    (if (leader_of_bal s (ballot s) = a) then do_2a s (Cmd v) else (s, ({||})))" 
*)

definition def_ExtEvtHandler_ReceiveFwd  :: "'v \<Rightarrow> 'v acc_state \<Rightarrow> ('v acc_state \<times> 'v packet fset)" where
  "def_ExtEvtHandler_ReceiveFwd v s \<equiv> def_ProposeInstance v s"

definition def_ExtEvtHandler_Receive1a :: "acc \<Rightarrow> bal \<Rightarrow> 'v acc_state \<Rightarrow> ('v acc_state \<times> 'v packet fset)" where
  "def_ExtEvtHandler_Receive1a l b s \<equiv>
    (let bal = ballot s; a = id s in
      (if (bal = None \<or> ((the bal) < b))
       then
          (let
            combiner = (\<lambda> (vo,bo) . vo \<bind> (\<lambda> v . bo \<bind> (\<lambda> b . Some (v,b))));
            x = ($ vote s, last_ballot s $);
            last_votes = combiner o$ x ;

            msg_1b = Phase1b last_votes b a;
            packet = Packet a l msg_1b;
            state = s\<lparr>ballot := Some b\<rparr>
          in
          (state, {|packet|}))
       else (s, {||})))"

definition def_Receive1b_UpdateOnebs :: 
  "'v acc_state \<Rightarrow> bal \<Rightarrow> acc \<Rightarrow> (inst \<Rightarrow>f ('v cmd \<times> bal) option) \<Rightarrow> 'v acc_state" where
  -- {* Update the list of highest voted values when receiving a 1b
    message from a2 for ballot bal containing last_vs *}
  "def_Receive1b_UpdateOnebs s bal a2 last_vs \<equiv>
    let
      a = id s;
      combiner = \<lambda> (xs, y) . (case y of None \<Rightarrow> (a2, None)#xs | Some z \<Rightarrow> (a2, Some z)#xs);
      pair_map = ($ (onebs s $ bal), last_vs $);
      at_bal = combiner o$ pair_map
    in s\<lparr>onebs := (onebs s)(bal $:= at_bal)\<rparr>"

definition def_Receive1b_HighestVoted :: "(nat \<Rightarrow>f (acc \<times> ('v cmd \<times> nat) option) list) \<Rightarrow> (nat \<Rightarrow>f ('v cmd) option)" where
  -- {* Makes sense only if no list in the map is empty. *}
  "def_Receive1b_HighestVoted m \<equiv>
    let
        votes = (map snd) o$ m;
        highest = (\<lambda> l . if (l = []) then None else (fold max l (l!0)) \<bind> (\<lambda> vb . Some (fst vb)))
    in highest o$ votes"

text {* If we had finfun_Ex we could do this better.
  Here we use instance 0 by default, but that's arbitrary. *}
definition def_ExtEvtHandler_Receive1b_QuorumReceived where
  "def_ExtEvtHandler_Receive1b_QuorumReceived b s \<equiv> 
    let at_b = onebs s $ b;
        at_b_i = at_b $ 0
    in 2 * length at_b_i > def_GetReplicaCount s"

text {* 
  When a quorum of 1b messages is received, we complete all started instances by sending 2b messages containing a safe value.
  If an instance has not been started but a higher instance has been started, we complete
  it by sending a no-op message.
  TODO: why do we need the no-ops? we could also reuse instances where everything is safe...
  It's because holes block the execution of higher commands while we have no new client commands to propose.
  But that's unlikely under high load...

  For now we propose values to all the instances ever started.
*}
definition def_ExtEvtHandler_Receive1b :: "(inst \<Rightarrow>f ('v cmd \<times> bal) option) \<Rightarrow> bal \<Rightarrow> acc \<Rightarrow> 'v acc_state \<Rightarrow> ('v acc_state \<times> 'v packet fset)" where
 "def_ExtEvtHandler_Receive1b last_vs bal a2 s \<equiv> (let a = id s in (
    if (Some bal = ballot s)
    then
      (let s1 = def_Receive1b_UpdateOnebs s bal a2 last_vs
       in (if def_ExtEvtHandler_Receive1b_QuorumReceived bal s1 
          then (let
              h = def_Receive1b_HighestVoted (onebs s1 $ bal);
              max_i = let l = (finfun_to_list (onebs s1 $ bal)) in (if l = [] then 0 else hd (rev l));
              s2 = s1\<lparr>leader := True\<rparr>;
              s3 = s2\<lparr>next_inst := max_i+1\<rparr>;
              twoa_is = [1..<max_i+1];
              (* TODO: the following might traverse all the finfun, which is a problem when there are many instances. *)
              s4 = fold (\<lambda> i s . s\<lparr>twobs := finfun_update_code (twobs s) i ((twobs s $ i)(bal $:= [a]))\<rparr>) twoa_is s3;
              msgs = map (\<lambda> i . case h $ i of 
                  None \<Rightarrow> Phase2a i bal NoOp a
                | Some v \<Rightarrow> Phase2a i bal v a) twoa_is;
              pckts = map (\<lambda> m . send_all s a m) msgs
            in (s4, fold (op |\<union>|) pckts {||}) )
          else (s1, {||}) ) )
    else (s, {||})) )"

text {*  Method def_Receive2_SetDecided
  Description:
   Stores the decided instance and it's command in the log and queue's it for commit.   
  Returns:
    New state with updates value.
  Performance Hazard: 
    Deciding an already decided instance would result in an extra record in the commit buffer indefinitely.
*}
definition def_Receive2_SetDecided where 
  "def_Receive2_SetDecided pvar_StartState pvar_Instance pvar_InstanceCommand \<equiv> pvar_StartState\<lparr>
        decided := finfun_update_code (decided pvar_StartState) pvar_Instance (Some pvar_InstanceCommand), 
        last_decision := Some pvar_Instance,
        commit_buffer := (commit_buffer pvar_StartState)(pvar_Instance $:= Some pvar_InstanceCommand)
\<rparr>"

definition def_Receive2_AddlMsg  :: "inst \<Rightarrow> bal \<Rightarrow> 'v cmd \<Rightarrow> acc \<Rightarrow> 'v acc_state \<Rightarrow> 'v acc_state" where
 "def_Receive2_AddlMsg pvar_Instance pvar_MsgBallotNum pvar_InstanceCommand pvar_FromReplica pvar_StartState \<equiv>  
    (let  lvar_BallotWithNewVote =  pvar_FromReplica # (twobs pvar_StartState $ pvar_Instance $ pvar_MsgBallotNum);
          lvar_IntermState1 =  
            pvar_StartState\<lparr>twobs := finfun_update_code (twobs pvar_StartState) 
                                                         pvar_Instance 
                                                         (twobs  pvar_StartState $ pvar_Instance)(pvar_MsgBallotNum $:= lvar_BallotWithNewVote)\<rparr>; 
          lvar_VoteCount = (length (twobs lvar_IntermState1 $ pvar_Instance $ pvar_MsgBallotNum));
          lvar_ReplicaCount = def_GetReplicaCount pvar_StartState
     in (
          if (2 * lvar_VoteCount \<le> lvar_ReplicaCount) (* Build the quorum *)
          then (
            (lvar_IntermState1)
          ) else ( 
            if ( ((lvar_ReplicaCount div 2)+1) = lvar_VoteCount) (* Decision Time *)
            then ( 
              (def_Receive2_SetDecided lvar_IntermState1 pvar_Instance pvar_InstanceCommand)
            ) else ( 
              if (lvar_ReplicaCount = lvar_VoteCount) (* Last Message *)
              then ( 
                let 
                   lvar_IntermState2 = lvar_IntermState1\<lparr> working_instances := (working_instances  lvar_IntermState1)(pvar_Instance $:= False)\<rparr>
                in 
                  ( lvar_IntermState2)
              ) else 
                (lvar_IntermState1) (*extra messages -- but not the last one*)
            )
          )             
     )
    )"     
definition def_Receive2_FirstMsg  :: "inst \<Rightarrow> bal \<Rightarrow> 'v cmd \<Rightarrow> acc \<Rightarrow> 'v acc_state \<Rightarrow> 'v acc_state" where
 "def_Receive2_FirstMsg i b v l s \<equiv>
    (let a = id s; bal = (ballot s); s2 = s\<lparr>vote := finfun_update_code (vote s) i (Some v),
                    twobs := finfun_update_code (twobs s) i ((K$ [])((the bal) $:= [a,l])),
                    next_inst := i+1,
                    pending := finfun_update_code (pending s) i (Some v),
                    working_instances := (working_instances s)(i $:= True)\<rparr>
     in (
          if (3 < def_GetReplicaCount s)
          then ( 
            (s2)
          ) else ( 
              if (3 = def_GetReplicaCount s)
              then ( 
                (def_Receive2_SetDecided s2 i v)
              ) else ( (*def_GetReplicaCount = 2 *) (*Decided and not working as no more message to receive*)
                   let s3= s2\<lparr> working_instances := (working_instances s)(i $:= False)\<rparr> (*This is still working as we have 1 more message to receive *)
                   in (def_Receive2_SetDecided s3 i v)
              )
          )             
        )
     )"     
definition def_Receive2_EntryPoint :: "inst \<Rightarrow> bal \<Rightarrow> 'v cmd \<Rightarrow> acc \<Rightarrow> 'v acc_state \<Rightarrow> 'v acc_state" where
  "def_Receive2_EntryPoint i b v l s \<equiv>
    (let bcurr=if ((ballot s) = None) then 0 else the (ballot s); s2 = (if (b > bcurr) then (s\<lparr> ballot := (Some b)\<rparr>) else s) 
        (* if there is no ballot or a newer ballot.. grab it from the message *)
     in (if ((working_instances s2) $ i) (* This is not the first message from the instance *)
        then (
          def_Receive2_AddlMsg i b v l s2  
      ) else (* This is the first message, treat like a propose *)
     (
          def_Receive2_FirstMsg i b v l s2  
     )
     
  ))
"
definition def_ExtEvtHandler_Receive2a :: "inst \<Rightarrow> bal \<Rightarrow> 'v cmd \<Rightarrow> acc \<Rightarrow> 'v acc_state \<Rightarrow> ('v acc_state \<times> 'v packet fset)" where
  "def_ExtEvtHandler_Receive2a i b v l s \<equiv> (def_Receive2_EntryPoint i b v l s, send_all s (id s) (Phase2b i b (id s) v)) "

definition def_ExtEvtHandler_Receive2b :: "inst \<Rightarrow> bal \<Rightarrow> acc \<Rightarrow> 'v cmd  \<Rightarrow> 'v acc_state \<Rightarrow> ('v acc_state \<times> 'v packet fset)" where
  "def_ExtEvtHandler_Receive2b i b a2 v s \<equiv> (def_Receive2_EntryPoint i b v a2 s, {||})"

text {* The leader receives this from a recovering replica *} 
definition def_ExtEvtHandler_ReceiveCatchUp :: "inst \<Rightarrow> inst \<Rightarrow> acc \<Rightarrow> 'v acc_state \<Rightarrow> ('v acc_state \<times>  'v packet fset)" where
  "def_ExtEvtHandler_ReceiveCatchUp i1 i2 from s \<equiv> let 
      a= (id s); 
      n1 = (finfun_filter_lteq (decided s) (i1-1));
      needed=(finfun_filter_gteq (decided s) (i2+1)) 
    in  
    (s, 
      ( {|Packet a from 
          (CatchUpRes needed)
        |}))"

text {* The replica receives this from the leader replica with catch decisions. Make sure to run the Commit internal handler after to finish the catch up.. TODO: Or should we force it here?*} 
definition def_ExtEvtHandler_ReceiveCatchUpResponse :: "(inst \<Rightarrow>f 'v cmd option) \<Rightarrow> 'v acc_state \<Rightarrow> ('v acc_state \<times>  'v packet fset)" where
  "def_ExtEvtHandler_ReceiveCatchUpResponse d s \<equiv>  let 
    a=(id s); s2 =  s\<lparr>decided := (finfun_merge d (decided s)), catch_up_requested := 0 \<rparr>
  in
    (s2, ({||}))"

subsection {* Internal Handlers *}

definition def_IntEvtHandler_InitializeReplicaState :: "nat \<Rightarrow> acc \<Rightarrow> 'v acc_state" where
  "def_IntEvtHandler_InitializeReplicaState n a \<equiv> \<lparr>
    id = a,
    leader = False,
    acc_state.acceptors = accs n,

    ballot = None,
    decided = K$ None,
    vote = K$ None, 
    last_ballot = K$ None,
    onebs = K$ K$ [],
    twobs = K$ K$ [],

    next_inst = 1, (* instances start at 1 *)
    last_decision = None,
    working_instances =  K$ False,

    commit_buffer =  K$ None,
    last_committed = 0,

    snapshot_reference=0,
    snapshot_proposal = [],
    
    pending = K$ None,
    catch_up_requested = 0
   \<rparr>" 


definition def_IntEvtHandler_ProposeInstance :: "'v \<Rightarrow> 'v acc_state \<Rightarrow> ('v acc_state \<times> 'v packet fset)" where
  -- {* If leader, then go ahead with 2a, otherwise forward to the leader. *}
  "def_IntEvtHandler_ProposeInstance v s \<equiv> def_ProposeInstance v s"

fun fun_StartLeaderElection_GetOwnedBallot where 
  "fun_StartLeaderElection_GetOwnedBallot a (Suc b) N = (if ((Suc b) mod N = a) then (Suc b)
    else (fun_StartLeaderElection_GetOwnedBallot a b N))"
| "fun_StartLeaderElection_GetOwnedBallot a 0 N = 0"

definition def_StartLeaderElection_suc_bal :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat"
  -- {* The smallest ballot belonging to replica a and greater than ballot b, when there are N replicas *}
  where "def_StartLeaderElection_suc_bal a b N \<equiv> fun_StartLeaderElection_GetOwnedBallot a (b + N) N"

fun  fun_StartLeaderElection_nx_bal where
  "fun_StartLeaderElection_nx_bal a None N = def_StartLeaderElection_suc_bal a 0 N"
| "fun_StartLeaderElection_nx_bal a (Some b) N = def_StartLeaderElection_suc_bal a b N"

definition def_IntEvtHandler_StartLeaderElection :: "'v acc_state \<Rightarrow> ('v acc_state \<times> 'v packet fset)" where
  -- {* a tries to become the leader *}
  "def_IntEvtHandler_StartLeaderElection s \<equiv>
    (let
        a = id s;
        b = fun_StartLeaderElection_nx_bal a (ballot s) (def_GetReplicaCount s);
        msg_1a = Phase1a a b in
      (s\<lparr>ballot := Some b\<rparr>, fimage (\<lambda> a2 . Packet a a2 msg_1a) (acceptors s)))"

fun fun_IntEvtHandler_ProcessExternalEvent where
  "fun_IntEvtHandler_ProcessExternalEvent (Phase1a l b) s = def_ExtEvtHandler_Receive1a l b s"
| "fun_IntEvtHandler_ProcessExternalEvent (Phase1b lvs b a) s = def_ExtEvtHandler_Receive1b lvs b a s"
| "fun_IntEvtHandler_ProcessExternalEvent (Phase2a i b cm l) s = def_ExtEvtHandler_Receive2a i b cm l s"
| "fun_IntEvtHandler_ProcessExternalEvent (Phase2b i b a cm) s = def_ExtEvtHandler_Receive2b i b a cm s"
| "fun_IntEvtHandler_ProcessExternalEvent (Vote i cm) s = undefined"
| "fun_IntEvtHandler_ProcessExternalEvent (Fwd v) s = def_ExtEvtHandler_ReceiveFwd v s"
| "fun_IntEvtHandler_ProcessExternalEvent (CatchUpReq i1 i2 a ) s = def_ExtEvtHandler_ReceiveCatchUp i1 i2 a s"
| "fun_IntEvtHandler_ProcessExternalEvent (CatchUpRes d ) s = def_ExtEvtHandler_ReceiveCatchUpResponse d s"
text {* Serializing finfuns to lists *}

definition def_IntEvtHandler_ProcessCommit :: "'v acc_state \<Rightarrow> ('v acc_state \<times> 'v internal_event) option" where
  "def_IntEvtHandler_ProcessCommit s \<equiv> if (((commit_buffer s) $ ((last_committed s)+1)) = None)
    then None
    else Some (s\<lparr>last_committed := ((last_committed s)+1), 
          commit_buffer := ((commit_buffer s)(((last_committed s)+1) $:= None)) \<rparr>, 
          Commit (the ((commit_buffer s) $ ((last_committed s)+1))))"

fun fun_ProcessSnapshot_Dequeue :: "'v list \<Rightarrow> (('v list \<times> 'v) option)" where
"fun_ProcessSnapshot_Dequeue (a#l) = Some (l, a)" |
"fun_ProcessSnapshot_Dequeue [] = None"
    
(* This handler performs a snapshot. Considering filtering on onebs as needed. *)
definition def_IntEvtHandler_ProcessSnapshot :: "'v acc_state \<Rightarrow> 'v acc_state option" where
  "def_IntEvtHandler_ProcessSnapshot s \<equiv> 
    let sp=(fun_ProcessSnapshot_Dequeue (snapshot_proposal s))
    in (
      if ( sp = None) 
      then None (* Nothing todo *)
      else (  
        if ((snd (the sp)) > (last_committed s))
        then
          None  (* we are trying to snapshot but haven't committed that far *)
        else
          Some (s\<lparr>snapshot_proposal := (fst (the sp)), snapshot_reference := (snd (the sp)),
                decided := (finfun_filter_lteq (decided s) (snd (the sp))), 
                vote := (finfun_filter_lteq (vote s) (snd (the sp))),
                last_ballot := (finfun_filter_lteq (last_ballot s) (snd (the sp))),
                pending := (finfun_filter_lteq (pending s) (snd (the sp))),
                twobs := (finfun_filter_lteq (twobs s) (snd (the sp)))
                \<rparr>)
      )
    )"

text {*  Method update_twobs
  Description:
   Do a periodic catch up if need be. Strictly run after a receve 2a/b message as the ballot # will be fixed
in the receive 2a/b. 
    
  Inputs:
    s: state 

  Returns:
    New state and catch up message as needed. 
*}
definition def_IntEvtHandler_ProcessPeriodicCatchUp  ::  "'v acc_state \<Rightarrow> ('v acc_state \<times> 'v packet fset) option" where 
 " def_IntEvtHandler_ProcessPeriodicCatchUp s \<equiv> 
 (let a = id s; 
      disparity=500; (* How far the last decision can go wrt last committed before a catch up is triggered *)
      ld=(if ((last_decision s) = None) then (0) else the (last_decision s));
      retry_needed = ((catch_up_requested s) \<noteq> 0) \<and> the (ballot s) \<noteq> (catch_up_requested s); (* Retry if the leader changes *)
      run = (((ld-(last_committed s)) >  disparity) \<and> ((catch_up_requested s) = 0))  \<or> (retry_needed) 
     in ( if run then
            Some (
                s\<lparr>catch_up_requested :=  the (ballot s)\<rparr>,  
                {|Packet a (leader_of_bal s (ballot s)) (CatchUpReq ((last_committed s)+1) ld a)|})
          else
            None 
        )
     )"

definition def_IntEvtHandler_RequestSnapshot :: "'v acc_state \<Rightarrow> inst \<Rightarrow> 'v acc_state option " where
  "def_IntEvtHandler_RequestSnapshot s instance \<equiv> 
    if (instance \<le> (snapshot_reference s)) then 
       None
    else ( 
      let 
        s2 = s\<lparr>snapshot_proposal := ((snapshot_proposal s) @ [instance]) \<rparr>
       in
        Some s2
    )"


subsection {* Code generation *}

text {* We need to rename a few modules to let the Scala compiler resolve circular dependencies. *}
code_identifier
  code_module Code_Numeral \<rightharpoonup> (Scala) Nat
| code_module List \<rightharpoonup> (Scala) Set

export_code 
  def_ExtEvtHandler_Receive1b_QuorumReceived 
    (* Ideally protocol later would figure this out from updated sate or a different particular internal event handler *)
  def_IntEvtHandler_InitializeReplicaState
  def_IntEvtHandler_ProposeInstance 
  def_IntEvtHandler_StartLeaderElection 
  fun_IntEvtHandler_ProcessExternalEvent  
  def_IntEvtHandler_ProcessCommit
  def_IntEvtHandler_RequestSnapshot
  def_IntEvtHandler_ProcessSnapshot
  def_IntEvtHandler_ProcessPeriodicCatchUp
  def_IntEvtHandler_GetLeader def_IntEvtHander_IsLeader def_IntEvtHander_GetLeader

in Scala file "simplePaxos.scala"

section {* The I/O-automata *}

record 'v mp_state = 
  node_states :: "nat \<Rightarrow>f 'v acc_state"
  network :: "'v packet fset"

datatype 'v mp_action =
  Receive_fwd acc acc 'v
| Propose acc "'v cmd"
| Send_1as acc
| Receive_1a_send_1b acc acc bal
| Receive_1b acc acc "inst \<Rightarrow>f ('v cmd \<times> bal) option" bal
| Receive_2a_send_2b acc acc inst bal "'v cmd"
| Receive_2b acc acc inst bal "'v cmd"
| Learn acc inst "'v cmd"

locale mp_ioa = IOA +
  fixes nas :: nat
    -- {* The number of acceptors *}
begin

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
| "init_nodes_state (Suc i) n = 
    (if Suc i > n then undefined else (init_nodes_state i n)(Suc i $:= def_IntEvtHandler_InitializeReplicaState n (Suc i)))"

lemma init_acc: 
assumes "a \<le> n" and "a > 0"
shows "(init_nodes_state a n) $ a = def_IntEvtHandler_InitializeReplicaState n a" using assms
by (induct a n arbitrary:n rule:init_nodes_state.induct, auto)


definition mp_start where
  "mp_start \<equiv> \<lparr>node_states = (init_nodes_state nas nas), network = {||}\<rparr>"

definition update_state where 
  "update_state a a_s packets s \<equiv>
    s\<lparr>node_states := (node_states s)(a $:= a_s),
      network := network s |\<union>| packets\<rparr>"

inductive mp_trans where
  "propose v (node_states s $ a) = (new_s, ps) \<Longrightarrow>
    mp_trans (s, Propose a (Cmd v), update_state a new_s ps s)"
| "\<lbrakk>receive_fwd v (node_states s $ dest) = (new_s, ps); 
    Packet src dest (Fwd v) |\<in>| network s\<rbrakk> \<Longrightarrow>
      mp_trans (s, Receive_fwd src dest v, update_state a new_s ps s)"
| "\<lbrakk>def_ExtEvtHandler_Receive1a l b (node_states s $ dest) = (new_s, ps);
    Packet src dest (Phase1a l b) |\<in>| network s; l = src\<rbrakk> \<Longrightarrow>
    mp_trans (s, Receive_1a_send_1b src dest b, update_state dest new_s ps s)"
| "send_1a (node_states s $ l) = (new_s, ps) \<Longrightarrow>
    mp_trans (s, Send_1as l, update_state l new_s ps s)"
| "\<lbrakk>def_ExtEvtHandler_Receive1b vs b l (node_states s $ l) = (new_s, ps); 
    Packet src l (Phase1b vs b a) |\<in>| network s; src = a\<rbrakk> \<Longrightarrow>
      mp_trans (s, Receive_1b src l vs b, update_state l new_s ps s)"
| "\<lbrakk>def_ExtEvtHandler_Receive2b i b l cm (node_states s $ l) = (new_s, ps);
    Packet src l (Phase2b i b a cm) |\<in>| network s; src = a\<rbrakk> \<Longrightarrow>
      mp_trans (s, Receive_2b a l i b cm, update_state l new_s ps s)"
| "\<lbrakk>def_ExtEvtHandler_Receive2a i b cm dest (node_states s $ dest) = (new_s, ps);
    Packet src dest (Phase2a i b cm l) |\<in>| network s; src = l\<rbrakk> \<Longrightarrow>
      mp_trans (s, Receive_2a_send_2b l dest i b cm, update_state dest new_s ps s)"
| "learn i v (node_states s $ a) = Some (new_s, ps) \<Longrightarrow>
    mp_trans (s, Learn a i (Cmd v), update_state a new_s ps s)"

definition mp_ioa where
  "mp_ioa \<equiv> \<lparr>ioa.asig = mp_asig, start = {mp_start}, trans = {(s,a,t) . mp_trans (s, a, t)}\<rparr>"

end

end