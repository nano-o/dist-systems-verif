theory MultiPaxosImpl
imports Main  "~~/src/HOL/Library/Monad_Syntax" "~~/src/HOL/Library/Code_Target_Numeral"
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
datatype 'v cmd = Cmd (the_val: 'v) | NoOp

type_synonym bal = nat
type_synonym inst = nat
type_synonym acc = nat
type_synonym ss_pointer = nat (* Notional snapshot pointer: from Upper Layer which is a db reference point. *)

datatype 'v msg =
  Phase1a (from_leader: acc) (ballot:bal) (inst: inst) 
| Phase1b (last_votes:"inst \<Rightarrow>f ('v cmd \<times> bal) option") (new_ballot: bal) (acceptor:acc)  (new_decided:"inst \<Rightarrow>f 'v cmd option") (new_wi:"inst \<Rightarrow>f 'v cmd option") (snapshotr:inst) (snapshotp:"ss_pointer option") 
| Phase2a (inst: inst) (for_ballot:bal) (suggestion:"'v cmd") (leader: acc)
| Phase2b (inst: inst) (ballot:bal) (acceptor: acc) (cmd: "'v cmd")
| Vote (inst: inst) (cmd: "'v cmd")
  -- {* Instructs a learner that a value has been decided. Not used for now... *}
| Fwd (val: 'v)
  -- {* Forwards a proposal to another proposer (the leader) *}
| CatchUpReq (inst_start: inst) (inst_end: inst) (acceptor: acc)
  -- {* Forwards a request for catch up to the leader. *}
| CatchUpRes (catchupdes:"inst \<Rightarrow>f 'v cmd option")  (snapshotr:inst)  (snapshotp:"ss_pointer option") 
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

  ballot :: "bal"
  decided :: "inst \<Rightarrow>f 'v cmd option"
    -- {* the highest ballot in which an acceptor participated *}
  vote :: "inst \<Rightarrow>f 'v cmd option"
    -- {* The last vote cast by an acceptor, for each instance *}
  last_ballot :: "inst \<Rightarrow>f bal"
    -- {* For an acceptor a, this is the ballot in which "vote a" was cast, for each instance *}
  onebs :: "bal \<Rightarrow>f inst \<Rightarrow>f (acc \<times> ('v cmd \<times> bal) option) list"
    -- {* For an acceptor a and a ballot b, lists of 1b-message descriptions, indexed by ballot then instance. *}
  twobs :: "inst \<Rightarrow>f bal \<Rightarrow>f acc list"
    -- {* For an acceptor a: lists describing the 2b messages, indexed by instance then ballot. *}

  next_inst :: "nat"
  highest_decided :: "inst option"
  working_instances :: "inst \<Rightarrow>f 'v cmd option" 

  commit_buffer :: "inst \<Rightarrow>f 'v cmd option"
  last_committed :: "inst"

  snapshot_reference :: "inst"
   -- {* The point strictly one less that the starting point for all the logs. The instance number at which the 
         database is caught up too. *}
  snapshot_pointer :: "ss_pointer option" 
   -- {* The point to the latest Snapshot from the upper layer. Is None if no Snapshot present. *}

  snapshot_proposal :: "(inst \<times> ss_pointer) list"
   -- {* A list that contains requests from upper layer for Snapshot. Each entry contains the instance point and the DB Snapshot reference . *}

  catch_up_requested :: "nat"
   -- {* Zero if no catch up on going, else set to the leader that we are requesting a catch up from. *}

  disparity :: "nat"
  -- {* How far the highest decided is allowed to grow before a catch up is triggered . *}

fun accs where
  "accs (0::nat) = {||}"
| "accs (Suc n) = (accs n) |\<union>| {|n|}"


definition initialize :: "nat \<Rightarrow> acc \<Rightarrow> nat \<Rightarrow> 'v acc_state" where
  "initialize n a d \<equiv> \<lparr>
    id = a,
    leader = False,
    acceptors = accs n,

    ballot = 0,
    decided = K$ None,
    vote = K$ None, 
    last_ballot = K$ 0,
    onebs = K$ K$ [],
    twobs = K$ K$ [],

    next_inst = 1, (* instances start at 1 *)
    highest_decided = None,
    working_instances =  K$ None,

    commit_buffer =  K$ None,
    last_committed = 0,

    snapshot_reference=0,
    snapshot_pointer = None,
    snapshot_proposal = [],
    
    catch_up_requested = 0,

    disparity = d
   \<rparr>" 


definition replicaCount where
  -- {* The number of replicas *}
  "replicaCount s \<equiv> fcard (acceptors s)"

definition leaderOfBallot where
  "leaderOfBallot s b \<equiv> case b of 0 \<Rightarrow> 0 | b \<Rightarrow> (b mod (replicaCount s))"

definition getBallot where "getBallot s \<equiv> ballot s"
definition getNextInstance where "getNextInstance s \<equiv> next_inst s"
definition isLeader where "isLeader s \<equiv> leader s"
definition getLeader where "getLeader s \<equiv> (ballot s) mod (replicaCount s)"

subsection {* Utility functions. *}

definition sendAll where "sendAll s a m \<equiv> fimage (\<lambda> a2 . Packet (id s) a2 m)  (acceptors s |-| {|a|})"

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

value "let ff = ((K$ 0) :: nat \<Rightarrow>f nat)(1 $:= 42)(42 $:= 0)(43 $:= 1) in (finfun_maxinst ff)"
value "let ff = ((K$ 0) :: int \<Rightarrow>f int)(1 $:= 42)(42 $:= 0)(43 $:= 1); 
          ff2 = ((K$ 0) :: int \<Rightarrow>f int)(1 $:= 42)(42 $:= 0)(20 $:= 1)  in (finfun_replace ff ff2)"

definition receive1a :: "acc \<Rightarrow> bal \<Rightarrow> inst \<Rightarrow> 'v acc_state \<Rightarrow> ('v acc_state \<times> 'v packet fset)" where
  "receive1a l b ins s \<equiv>
    (let bal = ballot s; a = id s in
      (if (bal = 0 \<or> (bal < b))
       then
          (let
            combiner = (\<lambda> (vo, bo) . vo \<bind> (\<lambda> v . Some (v,bo)));
            x = ($ vote s, last_ballot s $);
            last_votes = combiner o$ x ;

            new_decided = finfun_filt_le (decided s) ins; (* Send newer decided instances new leader *)                        
            new_wi = finfun_filt_le (working_instances s) ins; (* Send newer working instances to potentially new leader *)
            snapr = (if ((snapshot_reference s) > ins) 
              then (* We need to send the snapshot along *)
                (snapshot_reference s)
              else (0)
            );
            snapp = (if ((snapshot_reference s) > ins) 
              then (* We need to send the snapshot along *)
                (snapshot_pointer s)
              else 
                (None)
            ); 
            msg_1b = Phase1b last_votes b a new_decided new_wi snapr snapp;
            packet = Packet a l msg_1b;
            state = s\<lparr>ballot := b\<rparr>
          in
          (state, {|packet|}))
       else (s, {||})))"

subsection {* State Manipulating Utility Functions *}

definition propose :: "'v \<Rightarrow> 'v acc_state \<Rightarrow> ('v acc_state \<times> 'v packet fset)" where
  -- {* If leader, then go ahead with 2a, otherwise forward to the leader. *}
  " propose v s \<equiv> let a = id s in
    (if (leaderOfBallot s (ballot s) = a \<and> leader s) then 
       let
        a = id s;
        inst = (next_inst s);
        b = (ballot s);
        msg = Phase2a inst b (Cmd v) a;
        new_state = s\<lparr>next_inst := (inst+1),
          twobs := finfun_update_code (twobs s) inst ((K$ [])(b $:= [a])),
          working_instances := (working_instances s)(inst $:=(Some (Cmd v)))
          \<rparr>
       in (new_state, sendAll s a msg) 
      else ( 
        if (leaderOfBallot s (ballot s) = a) then 
          (s,{||}) (* Unreachable state *)
        else 
          (s,{|Packet a (leaderOfBallot s (ballot s)) (Fwd v)|})) )"

subsection {* External Event handlers *}

definition receiveFwd  :: "'v \<Rightarrow> 'v acc_state \<Rightarrow> ('v acc_state \<times> 'v packet fset)" where
  "receiveFwd v s \<equiv> propose v s"

definition updateObs :: 
  "'v acc_state \<Rightarrow> bal \<Rightarrow> acc \<Rightarrow> (inst \<Rightarrow>f ('v cmd \<times> bal) option) \<Rightarrow> 'v acc_state" where
  -- {* Update the list of highest voted values when receiving a 1b
    message from a2 for ballot bal containing last_vs *}
  "updateObs s bal a2 last_vs \<equiv>
    let
      a = id s;
      combiner = \<lambda> (xs, y) . (case y of None \<Rightarrow> (a2, None)#xs | Some z \<Rightarrow> (a2, Some z)#xs);
      pair_map = ($ (onebs s $ bal), last_vs $);
      at_bal = combiner o$ pair_map
    in s\<lparr>onebs := (onebs s)(bal $:= at_bal)\<rparr>"

definition updateInstances :: 
  "'v acc_state \<Rightarrow> (inst \<Rightarrow>f 'v cmd option) \<Rightarrow> (inst \<Rightarrow>f 'v cmd option) \<Rightarrow> inst \<Rightarrow> (ss_pointer option) \<Rightarrow> ((inst list) \<times> inst \<times> 'v acc_state )" where
  -- {* Update self, based on the decided and working instances from the 1b message send by others *}
  " updateInstances s nd nwi sr sp \<equiv>
    let
      a = id s;

      nd = finfun_filt_le nd (last_committed s); (* Get rid of anything that you might have committed between the initial 1a and receiving the 1b *)
      nwi = finfun_filt_le nwi (last_committed s); (* Get rid of anything that you might have committed between the initial 1a and receiving the 1b *)

      nwi = (finfun_replace nwi (working_instances s)); (* Merge the two working instance lists*)
      nwi =  finfun_remove nwi nd; (* Get rid of anything from the working instances that you can now decide *)
      ncb = finfun_replace nd (commit_buffer s); (* Add in new decisions to commit buffer. *)
      nd = finfun_replace nd (decided s); (* Add in new decisions to decision log. *)

      s1 = s\<lparr>working_instances := nwi, 
              decided := nd, 
              commit_buffer := ncb,
              highest_decided := Some (finfun_maxinst (commit_buffer s))
            \<rparr>;
      s2 = if (sr > 0) then 
              (s1\<lparr>snapshot_reference := sr, snapshot_pointer := sp, last_committed := sr\<rparr>) 
           else 
              (s1);

      max_value = (if the (highest_decided s2) \<le> finfun_maxinst (working_instances s2) 
                  then  finfun_maxinst (working_instances s2) else the (highest_decided s2));
      w = [((last_committed s2)+1)..<(max_value+1)];
      holes = fold (\<lambda> k l . if ((working_instances s2 $ k) = None \<and> (commit_buffer s2 $ k) = None ) then (k # l) else (l)) w []


    in (holes,max_value,s2)"

text {* If we had finfun_Ex we could do this better.
  Here we use instance 0 by default, but that's arbitrary. *}
definition quorumReceived where
  "quorumReceived b s \<equiv> 
    let at_b = onebs s $ b;
        at_b_i = at_b $ 0
    in 2 * length at_b_i > replicaCount s"

text {* 
  When a quorum of 1b messages is received, we complete all started instances by sending 2b messages containing a safe value.
  If an instance has not been started but a higher instance has been started, we complete
  it by sending a no-op message.
  TODO: why do we need the no-ops? we could also reuse instances where everything is safe...
  It's because holes block the execution of higher commands while we have no new client commands to propose.
  But that's unlikely under high load...

*}

definition receive1b :: "(inst \<Rightarrow>f ('v cmd \<times> bal) option) \<Rightarrow> bal \<Rightarrow> acc \<Rightarrow> (inst \<Rightarrow>f 'v cmd option) \<Rightarrow> (inst \<Rightarrow>f 'v cmd option) \<Rightarrow> inst \<Rightarrow> (ss_pointer option) \<Rightarrow>   'v acc_state \<Rightarrow> ('v acc_state \<times> 'v packet fset)" where
 "receive1b last_vs bal a2 nd nwi sr sp s \<equiv> (let a = id s in (
    if (bal = ballot s)
    then
      (let s1 = updateObs s bal a2 last_vs; 
           result = updateInstances s1 nd nwi sr sp;
           s2 = snd (snd result);
           holes = fst result;
           max_value = fst (snd result)
       in (if quorumReceived bal s2 
          then (let
                s3 = s2\<lparr>leader := (if (leaderOfBallot s bal = a) then (True) else (False)), next_inst := (max_value+1)\<rparr>; 
                working = finfun_to_list (working_instances s3);
                s4 = fold (\<lambda> i s_local . s_local\<lparr>twobs := finfun_update_code (twobs s) i ((twobs s $ i)(bal $:= [a]))\<rparr>) working s3; 
                s5 = fold (\<lambda> i s_local . s_local\<lparr>twobs := finfun_update_code (twobs s) i ((twobs s $ i)(bal $:= [a]))\<rparr>) holes s4; 
                msgsa = map (\<lambda> i . Phase2a i bal (the ((working_instances s5) $i)) a) working;
                msgsb = map (\<lambda> i . Phase2a i bal NoOp a) holes;
                msgs = msgsa @ msgsb;
                pckts = map (\<lambda> m . sendAll s a m) msgs
            in (s5, fold (op |\<union>|) pckts {||}) )
          else (s2, {||}) ) )
    else (s, {||})) )"

text {*  Method def_Receive2_SetDecided
  Description:
   Stores the decided instance and it's command in the log and queue's it for commit.   
  Returns:
    New state with updates value.
  Performance Hazard: 
    Deciding an already decided instance would result in an extra record in the commit buffer indefinitely.
*}
definition receive2_SetDecided where 
  "receive2_SetDecided s ins v \<equiv> 
        let highestd = (if (highest_decided s = None) 
        then (0) else (the (highest_decided s))) in 
        s\<lparr>decided := finfun_update_code (decided s) ins (Some v), 
          highest_decided := (if (ins > highestd) then (Some ins) else (Some highestd)),
          commit_buffer := (commit_buffer s)(ins $:= Some v)
\<rparr>"

definition receive2_AddlMsg  :: "inst \<Rightarrow> bal \<Rightarrow> 'v cmd \<Rightarrow> acc \<Rightarrow> 'v acc_state \<Rightarrow> 'v acc_state" where
 "receive2_AddlMsg ins ball v l s \<equiv>  
    (let  last_vote =  l # (twobs s $ ins $ ball);
          s1 = s\<lparr>twobs := finfun_update_code (twobs s) ins (twobs s $ ins)(ball $:= last_vote)\<rparr>; 
          lvar_VoteCount = (length (twobs s1 $ ins $ ball));
          accCount = replicaCount s
     in (
          if (2 * lvar_VoteCount \<le> accCount) (* Build the quorum *)
          then (
            (s1)
          ) else ( 
            if (((accCount div 2) + 1) = lvar_VoteCount) (* Decision Time *)
            then ( 
              (receive2_SetDecided s1 ins v)
            ) else ( 
              if (accCount = lvar_VoteCount) (* Last Message *)
              then ( 
                let 
                   s2 = s1\<lparr>working_instances := (working_instances s1)(ins $:= None)\<rparr>
                in 
                  (s2)
              ) else 
                (s1) (*extra messages -- but not the last one*)
            )
          )             
     )
    )"     
definition receive2_FirstMsg  :: "inst \<Rightarrow> bal \<Rightarrow> 'v cmd \<Rightarrow> acc \<Rightarrow> 'v acc_state \<Rightarrow> 'v acc_state" where
 "receive2_FirstMsg i b v l s \<equiv>
    (let a = id s; bal = (ballot s); s2 = s\<lparr>vote := finfun_update_code (vote s) i (Some v),
                    twobs := finfun_update_code (twobs s) i ((K$ [])(bal $:= [a,l])),
                    next_inst := i+1,
                    working_instances := (working_instances s)(i $:= (Some v))\<rparr>
     in (
          if (3 < replicaCount s)
          then ( 
            (s2)
          ) else ( 
              if (3 = replicaCount s)
              then ( 
                (receive2_SetDecided s2 i v)
              ) else ( (*def_GetReplicaCount = 2 *) (*Decided and not working as no more message to receive*)
                   let s3= s2\<lparr> working_instances := (working_instances s)(i $:= None)\<rparr> (*This is still working as we have 1 more message to receive *)
                   in (receive2_SetDecided s3 i v)
              )
          )             
        )
     )"     
definition receive2_EntryPoint :: "inst \<Rightarrow> bal \<Rightarrow> 'v cmd \<Rightarrow> acc \<Rightarrow> 'v acc_state \<Rightarrow> 'v acc_state" where
  "receive2_EntryPoint i b v l s \<equiv>
    (let bcurr= (ballot s); s2 = (if (b > bcurr) then (s\<lparr> ballot := b\<rparr>) else s) 
        (* if there is no ballot or a newer ballot.. grab it from the message *)
     in (if ((working_instances s2) $ i \<noteq> None) (* This is not the first message from the instance *)
        then (
          receive2_AddlMsg i b v l s2  
      ) else (* This is the first message, treat like a propose *)
     (
          receive2_FirstMsg i b v l s2  
     )
  ))
"
definition receive2a :: "inst \<Rightarrow> bal \<Rightarrow> 'v cmd \<Rightarrow> acc \<Rightarrow> 'v acc_state \<Rightarrow> ('v acc_state \<times> 'v packet fset)" where
  "receive2a i b v l s \<equiv> (receive2_EntryPoint i b v l s, sendAll s (id s) (Phase2b i b (id s) v)) "

definition receive2b :: "inst \<Rightarrow> bal \<Rightarrow> acc \<Rightarrow> 'v cmd  \<Rightarrow> 'v acc_state \<Rightarrow> ('v acc_state \<times> 'v packet fset)" where
  "receive2b i b a2 v s \<equiv> (receive2_EntryPoint i b v a2 s, {||})"

text {* The leader receives this from a recovering replica *} 
definition receiveCatchUp :: "inst \<Rightarrow> inst \<Rightarrow> acc \<Rightarrow> 'v acc_state \<Rightarrow> ('v acc_state \<times>  'v packet fset)" where
  "receiveCatchUp i1 i2 from s \<equiv> let 
      a= (id s); 
      n1 = (finfun_filt_le (decided s) (i1-1));
      needed=(finfun_filt_ge (n1) (i2+1));
      snapr = (if ((snapshot_reference s) > (i1-1)) 
              then (* We need to send the snapshot along *)
                (snapshot_reference s)
              else 
                (0)
            );
            snapp = (if ((snapshot_reference s) > (i1-1)) 
              then (* We need to send the snapshot along *)
                (snapshot_pointer s)
              else 
                (None)
            )
    in  
    (s, 
      ( {|Packet a from 
          (CatchUpRes needed snapr snapp)
        |}))"

text {* The replica receives this from the leader replica with catch decisions. 
Make sure to run the Commit internal handler after to finish the catch up.. TODO: Or should we force it here?*} 
definition receiveCatchUpResp :: "(inst \<Rightarrow>f 'v cmd option) \<Rightarrow> inst \<Rightarrow> (ss_pointer option) \<Rightarrow> 'v acc_state \<Rightarrow> ('v acc_state \<times>  'v packet fset)" where
  "receiveCatchUpResp d sr sp s \<equiv>  let 
    a=(id s); s1 =  s\<lparr>decided := (finfun_replace d (decided s)), 
            commit_buffer := (finfun_filt_le (finfun_replace d (commit_buffer s)) (last_committed s)), catch_up_requested := 0 \<rparr>;
    s2 = if (sr > 0) then 
              (s1 \<lparr>snapshot_reference:=sr, snapshot_pointer:=sp, last_committed:=sr\<rparr>) 
           else 
              (s1)
  in
    (s2, ({||}))"

subsection {* Internal Handlers *}

definition finfun_deserialize where
 "finfun_deserialize l \<equiv> foldr (\<lambda> kv r . finfun_update_code r (fst kv) (snd kv)) l (K$ None)"

definition proposeInstance :: "'v \<Rightarrow> 'v acc_state \<Rightarrow> ('v acc_state \<times> 'v packet fset)" where
  -- {* If leader, then go ahead with 2a, otherwise forward to the leader. *}
  "proposeInstance v s \<equiv> propose v s"

fun generateBallot where 
  "generateBallot a (Suc b) N = (if ((Suc b) mod N = a) then (Suc b)
    else (generateBallot a b N))"
| "generateBallot a 0 N = 0"

fun  nextBallot where
  -- {* The smallest ballot belonging to replica a and greater than ballot b, when there are N replicas *}
  "nextBallot a b N = generateBallot a (b + N) N"

definition send1a :: "'v acc_state \<Rightarrow> ('v acc_state \<times> 'v packet fset)" where
  -- {* a tries to become the leader *}
  "send1a s \<equiv>
    (let
        a = id s;
        b = nextBallot a (ballot s) (replicaCount s);
        c = (last_committed s);
        msg_1a = Phase1a a b c in
      (s\<lparr>ballot := b\<rparr>, fimage (\<lambda> a2 . Packet a a2 msg_1a) (acceptors s)))"

fun processExternalEvent where
  "processExternalEvent (Phase1a l b i) s = receive1a l b i s"
| "processExternalEvent (Phase1b lvs b a nd nwi sr sp ) s = receive1b lvs b a nd nwi sr sp s "
| "processExternalEvent (Phase2a i b cm l) s = receive2a i b cm l s"
| "processExternalEvent (Phase2b i b a cm) s = receive2b i b a cm s"
| "processExternalEvent (Vote i cm) s = undefined"
| "processExternalEvent (Fwd v) s = receiveFwd v s"
| "processExternalEvent (CatchUpReq i1 i2 a ) s = receiveCatchUp i1 i2 a s"
| "processExternalEvent (CatchUpRes d sr sp ) s = receiveCatchUpResp d sr sp s"
text {* Serializing finfuns to lists *}

definition processCommit :: "'v acc_state \<Rightarrow> ('v acc_state \<times> 'v internal_event) option" where
  "processCommit s \<equiv> if (((commit_buffer s) $ ((last_committed s)+1)) = None)
    then None
    else Some (s\<lparr>last_committed := ((last_committed s)+1), 
          commit_buffer := ((commit_buffer s)(((last_committed s)+1) $:= None)) \<rparr>, 
          Commit (the ((commit_buffer s) $ ((last_committed s)+1))))"

fun process_Dequeue :: "'v list \<Rightarrow> (('v list \<times> 'v) option)" where
"process_Dequeue (a#l) = Some (l, a)" |
"process_Dequeue [] = None"
    
(* This handler performs a snapshot. Considering filtering on onebs as needed. *)
definition processSnapshot :: "'v acc_state \<Rightarrow> 'v acc_state option" where
  "processSnapshot s \<equiv> 
    let sp=(process_Dequeue (snapshot_proposal s))
    in (
      if ( sp = None) 
      then None (* Nothing todo *)
      else (  
        if ((fst (snd (the sp))) > (last_committed s))
        then
          None  (* we are trying to snapshot but haven't committed that far *)
        else
          Some (s\<lparr>snapshot_proposal := (fst (the sp)), snapshot_pointer:= Some (snd (snd (the sp))),snapshot_reference := fst (snd (the sp)),
                decided := (finfun_filt_le (decided s) (fst (snd (the sp)))), 
                vote := (finfun_filt_le (vote s)  (fst (snd (the sp)))),
                last_ballot := (finfun_filt_le (last_ballot s)  (fst (snd (the sp)))),
                twobs := (finfun_filt_le (twobs s) (fst (snd (the sp))))
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

definition processPeriodicCatchUp  ::  "'v acc_state \<Rightarrow> ('v acc_state \<times> 'v packet fset) option" where 
 " processPeriodicCatchUp s \<equiv> 
 (let a = id s; 
      ld=(if ((highest_decided s) = None) then (0) else the (highest_decided s));
      retry_needed = ((catch_up_requested s) \<noteq> 0) \<and> (ballot s) \<noteq> (catch_up_requested s); (* Retry if the leader changes *)
      run = (((ld-(last_committed s)) >  (disparity s)) \<and> ((catch_up_requested s) = 0))  \<or> (retry_needed) 
     in ( if run then
            Some (
                s\<lparr>catch_up_requested := (ballot s)\<rparr>,  
                {|Packet a (leaderOfBallot s (ballot s)) (CatchUpReq ((last_committed s)+1) ld a)|})
          else
            None 
        )
     )"

definition requestSnapshot :: "'v acc_state \<Rightarrow> inst \<Rightarrow> ss_pointer \<Rightarrow> 'v acc_state option " where
  "requestSnapshot s instance ssp \<equiv> 
    if (instance \<le> (snapshot_reference s)) then 
       None
    else ( 
      let 
        s2 = s\<lparr> snapshot_proposal := ((snapshot_proposal s) @ [(instance,ssp)]) \<rparr>
       in
        Some s2
    )"


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

export_code 
  quorumReceived (* Ideally upper layer would not need to call this *)
  initialize
  propose 
  send1a 
  processExternalEvent  
  processCommit
  requestSnapshot
  processSnapshot
  processPeriodicCatchUp
  getBallot isLeader getLeader getNextInstance finfun_deserialize

in Scala file "MultiPaxosImpl.scala"

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
    (if Suc i > n then undefined else (init_nodes_state i n)(Suc i $:= initialize n (Suc i)))"

lemma init_acc: 
assumes "a \<le> n" and "a > 0"
shows "(init_nodes_state a n) $ a = initialize n a" using assms
by (induct a n arbitrary:n rule:init_nodes_state.induct, auto)

(*
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
*)

end

end