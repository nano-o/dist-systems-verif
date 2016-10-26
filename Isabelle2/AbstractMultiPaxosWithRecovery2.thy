theory AbstractMultiPaxosWithRecovery2
  imports Utils MaxByKey IOA Quorums Paxos_Sig "~~/src/HOL/Library/Monad_Syntax"
begin

text {* TODO: add rejoin; add log truncation *}

section {* Local state and transitions *}

subsection {* Data structures *}

record ('a, 'v) acc =
  -- {* The local state of an acceptor. *}
  id :: 'a
  acceptors :: "'a set"
  ballot :: bal
  log :: "inst \<rightharpoonup> 'v"
    -- {* Last ballot in which the acceptor voted. *}
  inst_status :: "bal \<rightharpoonup> (inst \<rightharpoonup> 'v)"
    -- {* After leadership is acquired in ballot b, this describes the result of the 
      safe-at computation *}
  votes :: "inst \<rightharpoonup> ('v \<times> bal)"
    -- {* The last vote in each instance. *}
  onebs :: "bal \<Rightarrow> ('a \<rightharpoonup> (inst \<times> (inst \<rightharpoonup> ('v\<times>bal))))"
    -- {* The oneb messages rcvd when the acceptor tries to acquire leadership.
    Note that we need the outermost option to signify that we did not rcv a oneb message
    from the acceptor, as opposed to receiving a oneb message from an acceptor that never voted. *}
  twobs :: "bal \<Rightarrow> inst \<Rightarrow> 'a set"
    -- {* the twob messages rcvd (they are broadcast). *}
  decisions :: "inst \<Rightarrow> 'a \<rightharpoonup> 'v"
    -- {* Decisions by other processes known to the current process. *}
  rejoin_resps :: "'a \<rightharpoonup> inst option"
  restarting :: "bool"
  lowest :: "inst"
  bound :: "inst"

datatype ('a,'v) msg =
  Phase1a bal
  | Phase1b 'a bal inst "inst \<rightharpoonup> ('v \<times> bal)" (* third param is lowest *)
  | Phase2a bal inst 'v
  | Phase2b 'a bal inst 'v
  | Fwd 'v
  | Decision 'a inst 'v
  | ReJoin 'a
  | ReJoinResp 'a "inst option"
  
datatype ('a,'v) packet =
  Packet 'a  "('a,'v) msg"

locale amp_r3 =
  fixes leader :: "bal \<Rightarrow> 'a::linorder"
  and next_bal :: "bal \<Rightarrow> 'a \<Rightarrow> bal"
  and as :: "'a set"
  and quorums :: "'a set set"
  and lookahead :: nat
begin

definition local_start where "local_start a \<equiv>
  \<lparr>id = a, acceptors = as, ballot = 0, log =\<lambda> i . None, inst_status = \<lambda> i . None,
  votes = \<lambda> i . None, onebs = \<lambda> b a . None,
  twobs = \<lambda> b i . {}, decisions = \<lambda> i a . None, rejoin_resps = \<lambda> a . None, 
  restarting = False, lowest = 0, bound = lookahead\<rparr>"
  
end

subsection {* The propose action *}

definition send_all where send_all_def[code del]:
  "send_all s m \<equiv> { Packet a m | a . a \<in> acceptors s \<and> a \<noteq> id s}"
  
context amp_r3
begin
  
definition next_inst where "next_inst s \<equiv>
  SOME i . inst_status s i = None"

definition do_2a where "do_2a s v \<equiv>
  let i = next_inst s in if (\<not> restarting s \<and> i \<le> bound s) then
    (let b = ballot s;
      s' = s\<lparr>inst_status := (inst_status s)(b := map_option (\<lambda> f . f(i := Some v)) (inst_status s b)),
        twobs := (twobs s)(b := (twobs s b)(i := {id s}))\<rparr>;
      msgs = send_all s (Phase2a b i v)
    in (s', msgs))
  else (s, {})"
 
definition propose where "propose s v \<equiv>
  let l = leader (ballot s) in
    if l = id s
    then (do_2a s v)
    else (s, {Packet l (Fwd v)})"

subsection {* The @{text rcv_fwd} action *}

definition rcv_fwd where "rcv_fwd s v \<equiv>
  let l = leader (ballot s) in
    if l = id s
    then do_2a s v
    else (s, {Packet l (Fwd v)})"

end

subsection {* The @{text try_acquire_leadership} action *}

context amp_r3 begin

definition try_acquire_leadership where "try_acquire_leadership s \<equiv>
  let
    a = id s;
    b = next_bal (ballot s) a;
    s' = s\<lparr>onebs := (onebs s)(b := ((onebs s b)(a := Some (lowest s, votes s)))), 
      ballot := b\<rparr>;
    msgs = send_all s (Phase1a b)
  in if \<not> restarting s then (s', msgs) else (s, {})"

subsection {* The @{text rcv_1a} action *}

definition rcv_1a where "rcv_1a s b \<equiv>
  if \<not> restarting s \<and> b > ballot s then let
      msgs = {Packet (leader b) (Phase1b (id s) b (lowest s) (votes s))};
      s' = s\<lparr>ballot := b\<rparr>
    in (s', msgs)
  else (s, {})"
  
end

subsection {* The @{text rcv_1b} action *}

context amp_r3 begin

definition status_from_1bs where 
  -- {* Here we use only vote information that is after an acceptor's lowest instance.
    TODO: this might not be needed as crashes reset the votes to None.  *}
  "status_from_1bs bs accs \<equiv> \<lambda> i .
    let votes = {x . \<exists> a \<in> accs . \<exists> f l . bs a = Some (l, f) \<and> f i = Some x \<and> l \<ge> i}
    in (if votes = {} then None else Some (fst (the_elem (max_by_key votes snd))))"

definition msgs_2a where "msgs_2a low bnd bs accs lg b \<equiv>
  let to_complete = (\<lambda> i . 
    if (low \<le> i \<and> i \<le> bnd) 
    then (case lg i of Some v \<Rightarrow> None | None \<Rightarrow> (status_from_1bs bs accs i))
    else None)
  in {Phase2a b i v | i v . to_complete i = Some v}"

definition rcv_1b where "rcv_1b s a b l vs \<equiv> if \<not> restarting s then (
  let s' = s\<lparr>onebs := (onebs s)(b := ((onebs s b)(a := Some (l, vs))))\<rparr>
  in (if (inst_status s b = None \<and> (\<forall> a \<in> acceptors s . onebs s' b a \<noteq> None))
    then let
        s'' = s'\<lparr>inst_status := (inst_status s)(b := Some (status_from_1bs (onebs s b) (acceptors s)))\<rparr>;
        msgs = msgs_2a (lowest s) (bound s) (onebs s b) (acceptors s) (log s) b;
        pcks = \<Union> {send_all s m | m . m \<in> msgs}
      in (s'', pcks)
    else (s', {}))) 
    else (s, {})"

subsection {* The @{text rcv_2a} action *}

abbreviation (input) decided where "decided s i \<equiv> 
  case (log s i) of Some _ \<Rightarrow> True | _ \<Rightarrow> False"
  
definition rcv_2a where "rcv_2a s b i v \<equiv>
  if \<not> restarting s \<and> b \<ge> ballot s \<and> i \<ge> lowest s then
    let s' = s\<lparr>votes := (votes s)(i := Some (v, b)),
      twobs := (twobs s)(b := (twobs s b)(i := insert (id s) (twobs s b i))),
      ballot := b\<rparr>;
      msgs = send_all s (Phase2b (id s) b i v)
    in (s', msgs)
  else (s, {})"
  
subsection {* The @{text rcv_2b} action *}

definition rcv_2b where "rcv_2b s i b a v \<equiv>
  if \<not> restarting s \<and> (~ decided s i) \<and> i \<ge> lowest s
  then let
      s' = s\<lparr>twobs := (twobs s)(i := (twobs s i)(b := insert a (twobs s i b)))\<rparr>
    in (
      if (twobs s' i b = (acceptors s))
      then let s'' = s'\<lparr>log := (log s)(i := Some v)\<rparr>
        in (s'', send_all s (Decision (id s) i v))
      else (s', {}) )
  else (s, {})"
   
subsection {* The @{text rcv_decision} action *}
 
definition rcv_decision where "rcv_decision s a i v \<equiv>
  let s' = s\<lparr>log := (log s)(i := Some v), decisions := (decisions s)(i := (
    decisions s i)(a := Some v))\<rparr>;
    s'' = if (\<forall> a \<in> acceptors s . decisions s i a \<noteq> None \<and> i < bound s) then s'\<lparr>bound := i\<rparr> else s'
  in (s', {})"

subsection {* The @{text restart} action *}

definition restart where "restart s \<equiv>
  (local_start (id s)\<lparr>restarting := True\<rparr>, send_all s (ReJoin (id s)))"
  
subsection {* The @{text rcv_rejoin} action *}

definition rcv_rejoin where "rcv_rejoin s src \<equiv>
    let 
      ds = {i . log s i \<noteq> None};
      resp = if ds = {} then None else Some (Max ds)
    in
  (s, {Packet src (ReJoinResp (id s) resp)})"

subsection {* The @{text rcv_rejoin_resp} action *}
  
definition rcv_rejoin_resp where "rcv_rejoin_resp s a io \<equiv> if restarting s then (
  let s' = s\<lparr>rejoin_resps := (rejoin_resps s)(a := Some io)\<rparr>
  in if \<forall> a . rejoin_resps s a \<noteq> None
    then let 
        rs = {i . \<exists> a . rejoin_resps s a = Some (Some i)};
        l = if rs = {} then lookahead+1 else (Max rs)+lookahead+2
      in (s'\<lparr>lowest := l, restarting := False\<rparr>, {})
    else (s', {}) )
  else (s, {})"

subsection {* The @{text process_msg} action *}

fun process_msg where
  "process_msg s (Phase1a b) = rcv_1a s b"
  | "process_msg s (Phase2a b i v) = rcv_2a s b i v"
  | "process_msg s (Phase1b a b i vs) = rcv_1b s a b i vs"
  | "process_msg s (Phase2b a i b v) = rcv_2b s i b a v"
  | "process_msg s (Fwd v) = rcv_fwd s v"
  | "process_msg s (Decision a i v) = rcv_decision s a i v"
  | "process_msg s (ReJoin a) = rcv_rejoin s a"
  | "process_msg s (ReJoinResp a io) = rcv_rejoin_resp s a io"

end

subsection {* Global system IOA. *} 

record ('a,'v) global_state =
  lstate :: "'a \<Rightarrow> ('a, 'v)acc"
  network :: "('a, 'v) packet set"

context amp_r3 begin

definition global_start where "global_start \<equiv>
  \<lparr>lstate = (\<lambda> a . local_start a), network = {}\<rparr>"

inductive trans_rel :: "(('a,'v) global_state \<times> ('a,'v) paxos_action \<times> ('a,'v) global_state) \<Rightarrow> bool" where
  "\<lbrakk>(Packet a m) \<in> network s; process_msg ((lstate s) a) m = (sa', ms); m = Phase2b a i b v;
    log ((lstate s) a) \<noteq> log sa'\<rbrakk>
    \<Longrightarrow> trans_rel (s, Learn a i [v],
      s\<lparr>lstate := (lstate s)(a := sa'), network := network s \<union> ms\<rparr>)"
| "\<lbrakk>(Packet a m) \<in> network s; process_msg ((lstate s) a) m = (sa', ms)\<rbrakk>
    \<Longrightarrow> trans_rel (s, Internal, 
      s\<lparr>lstate := (lstate s)(a := sa'), network := network s \<union> ms\<rparr>)" 
| "\<lbrakk>propose ((lstate s) a) v = (sa', ms)\<rbrakk>
    \<Longrightarrow> trans_rel (s, Propose v, 
      s\<lparr>lstate := (lstate s)(a := sa'), network := network s \<union> ms\<rparr>)"
| "\<lbrakk>try_acquire_leadership ((lstate s) a) = (sa', ms)\<rbrakk>
    \<Longrightarrow> trans_rel (s, Internal, 
      s\<lparr>lstate := (lstate s)(a := sa'), network := network s \<union> ms\<rparr>)"
| "\<lbrakk>restart ((lstate s) a) = (sa', ms)\<rbrakk>
    \<Longrightarrow> trans_rel (s, Internal, 
      s\<lparr>lstate := (lstate s)(a := sa'), network := network s \<union> ms\<rparr>)"
  
inductive_cases trans_rel_cases:"trans_rel (s,a,s')"

abbreviation (input) local_step where "local_step a p r r' \<equiv> 
  r' = r\<lparr>lstate := (lstate r)(a := fst p), network := network r \<union> snd p\<rparr>"
  
lemma trans_cases:
  assumes "trans_rel (r, act, r')"
  obtains
    (propose) a v where "act = Propose v" and "local_step a (propose (lstate r a) v) r r'"
  | (learn) a i b v m p where "act = Learn a i [v]" and "m = Phase2b a i b v"
    and "p = rcv_2b (lstate r a) i b a v"
    and "local_step a p r r'"
    and "Packet a m \<in> network r" 
    and "log (lstate r a) \<noteq> log (fst p)"
  | (acquire_leadership) a where "act = Internal" and "local_step a (try_acquire_leadership (lstate r a)) r r'"
  | (rcv_1a) a b m p where "act = Internal" and "m = Phase1a b"
    and "p = rcv_1a (lstate r a) b"
    and "local_step a p r r'"
    and "Packet a m \<in> network r" 
  | (rcv_2a) a b i v m p where "act = Internal" and "m = Phase2a b i v"
    and "p = rcv_2a (lstate r a) b i v"
    and "local_step a p r r'"
    and "Packet a m \<in> network r" 
  | (rcv_2b) a a2 i b v m p where "act = Internal" and "m = Phase2b a2 i b v"
    and "p = rcv_2b (lstate r a) i b a2 v"
    and "local_step a p r r'"
    and "Packet a m \<in> network r" 
  | (rcv_1b) a b i vs m p a2 where "act = Internal" and "m = Phase1b a2 b i vs"
    and "p = rcv_1b (lstate r a) a2 b i vs"
    and "local_step a p r r'"
    and "Packet a m \<in> network r" 
  | (fwd) a v m p where "act = Internal" and "m = Fwd v"
    and "p = rcv_fwd (lstate r a) v"
    and "local_step a p r r'"
    and "Packet a m \<in> network r"
  | (rcv_decision) a a2 i v p m where "act = Internal" and "m = Decision a2 i v"
    and "p = rcv_decision (lstate r a) a2 i v"
    and "local_step a p r r'"
    and "Packet a m \<in> network r"
  | (rcv_rejoin) a a2 p m where "act = Internal" and "m = ReJoin a2"
    and "p = rcv_rejoin (lstate r a) a2"
    and "local_step a p r r'"
  | (rcv_rejoin_resp) a a2 io p m where "act = Internal" and "m = ReJoinResp a2 io"
    and "p = rcv_rejoin_resp (lstate r a) a2 io"
    and "local_step a p r r'"
  | (restart) a p m where "act = Internal"
    and "p = restart (lstate r a)"
    and "local_step a p r r'"
proof -
  show ?thesis using assms
    apply (rule trans_rel_cases)
    subgoal premises prems using learn prems by (metis fst_conv snd_conv)
       defer
    subgoal premises prems using propose prems by (metis fst_conv snd_conv)
    subgoal premises prems using acquire_leadership prems by (metis fst_conv snd_conv) 
    subgoal premises prems using restart prems by (metis fst_conv snd_conv)
    subgoal premises prems for a m s' msgs using prems
      apply (induct rule:process_msg.induct; simp)
      subgoal premises prems using rcv_1a prems by (metis fst_conv snd_conv)
      subgoal premises prems using rcv_2a prems by (metis fst_conv snd_conv)
      subgoal premises prems using rcv_1b prems  by (metis fst_conv snd_conv) 
      subgoal premises prems using rcv_2b prems by (metis fst_conv snd_conv)
      subgoal premises prems using fwd prems by (metis fst_conv snd_conv) 
      subgoal premises prems using rcv_decision prems  by (metis fst_conv snd_conv) 
      subgoal premises prems using rcv_rejoin prems by (metis fst_conv snd_conv)
      subgoal premises prems using rcv_rejoin_resp prems by (metis fst_conv snd_conv)
      done
    done
qed 

definition ioa where
  "ioa \<equiv> \<lparr>ioa.asig = paxos_asig, ioa.start = {global_start}, ioa.trans = Collect trans_rel\<rparr>"

end

end