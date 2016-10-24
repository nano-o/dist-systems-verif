theory AbstractMultiPaxosWithRecovery2
  imports Utils MaxByKey IOA Quorums Paxos_Sig "~~/src/HOL/Library/Monad_Syntax"
begin

section {* Local state and transitions *}

subsection {* Data structures *}

record ('a, 'v) acc =
  -- {* The local state of an acceptor. *}
  id :: 'a
  acceptors :: "'a set"
  ballot :: bal
  decision :: "inst \<rightharpoonup> 'v"
    -- {* Last ballot in which the acceptor voted. *}
  inst_status :: "bal \<rightharpoonup> (inst \<rightharpoonup> 'v)"
    -- {* After leadership is acquired in ballot b, this describes the result of the 
      safe-at computation *}
  votes :: "inst \<rightharpoonup> ('v \<times> bal)"
    -- {* The last vote in each instance. *}
  onebs :: "bal \<Rightarrow> ('a \<rightharpoonup> (inst \<times> (inst \<rightharpoonup> ('v\<times>bal))))"
    -- {* The oneb messages received when the acceptor tries to acquire leadership.
    Note that we need the outermost option to signify that we did not receive a oneb message
    from the acceptor, as opposed to receiving a oneb message from an acceptor that never voted. *}
  twobs :: "bal \<Rightarrow> inst \<Rightarrow> 'a set"
    -- {* the twob messages received (they are broadcast). *}
  decisions :: "inst \<Rightarrow> 'a \<rightharpoonup> 'v"
    -- {* Decisions by other processes known to the current process. *}
  lowest :: "inst"
  bound :: "inst"

datatype ('a,'v) msg =
  Phase1a bal
  | Phase1b 'a bal inst "inst \<rightharpoonup> ('v \<times> bal)" (* third param is lowest *)
  | Phase2a bal inst 'v
  | Phase2b 'a bal inst 'v
  | Fwd 'v
  | Decision 'a inst 'v
  
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
  \<lparr>id = a, acceptors = as, ballot = 0, decision =\<lambda> i . None, inst_status = \<lambda> i . None,
  votes = \<lambda> i . None, onebs = \<lambda> b a . None,
  twobs = \<lambda> b i . {}, decisions = \<lambda> i a . None, lowest = 0, bound = lookahead\<rparr>"
  
end

subsection {* The propose action *}

definition send_all where send_all_def[code del]:
  "send_all s m \<equiv> { Packet a m | a . a \<in> acceptors s \<and> a \<noteq> id s}"
  
context amp_r3
begin
  
definition next_inst where "next_inst s \<equiv>
  SOME i . inst_status s i = None"

definition do_2a where "do_2a s v \<equiv>
  let i = next_inst s in if (i \<le> bound s) then
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

subsection {* The @{text receive_fwd} action *}

definition receive_fwd where "receive_fwd s v \<equiv>
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
  in (s', msgs)"

subsection {* The @{text receive_1a} action *}

definition receive_1a where "receive_1a s b \<equiv>
  if b > ballot s then let
      msgs = {Packet (leader b) (Phase1b (id s) b (lowest s) (votes s))};
      s' = s\<lparr>ballot := b\<rparr>
    in (s', msgs)
  else (s, {})"
  
end

subsection {* The @{text receive_1b} action *}

context amp_r3 begin

definition status_from_1bs where 
  -- {* Here we use only vote information that is after an acceptor's lowest instance.
    TODO: this might not be needed as crashes reset the votes to None.  *}
  "status_from_1bs bs accs \<equiv> \<lambda> i .
    let votes = {x . \<exists> a \<in> accs . \<exists> f l . bs a = Some (l, f) \<and> f i = Some x \<and> l \<ge> i}
    in (if votes = {} then None else Some (fst (the_elem (max_by_key votes snd))))"

definition msgs_2a where "msgs_2a l bnd bs accs log b \<equiv>
  let to_complete = (\<lambda> i . 
    if (l \<le> i \<and> i \<le> bnd) 
    then (case log i of Some v \<Rightarrow> None | None \<Rightarrow> (status_from_1bs bs accs i))
    else None)
  in {Phase2a b i v | i v . to_complete i = Some v}"

definition receive_1b where "receive_1b s a b l vs \<equiv>
  let s' = s\<lparr>onebs := (onebs s)(b := ((onebs s b)(a := Some (l, vs))))\<rparr>
  in (if (inst_status s b = None \<and> (\<forall> a \<in> acceptors s . onebs s' b a \<noteq> None))
    then let
        s'' = s'\<lparr>inst_status := (inst_status s)(b := Some (status_from_1bs (onebs s b) (acceptors s)))\<rparr>;
        msgs = msgs_2a (lowest s) (bound s) (onebs s b) (acceptors s) (decision s) b;
        pcks = \<Union> {send_all s m | m . m \<in> msgs}
      in (s'', pcks)
    else (s', {}))"

subsection {* The @{text receive_2a} action *}

abbreviation (input) decided where "decided s i \<equiv> 
  case (decision s i) of Some _ \<Rightarrow> True | _ \<Rightarrow> False"
  
definition receive_2a where "receive_2a s i b v \<equiv>
  if b \<ge> ballot s \<and> i \<ge> lowest s then
    let s' = s\<lparr>votes := (votes s)(i := Some (v, b)),
      twobs := (twobs s)(b := (twobs s b)(i := insert (id s) (twobs s b i))),
      ballot := b\<rparr>;
      msgs = send_all s (Phase2b (id s) b i v)
    in (s', msgs)
  else (s, {})"
  
subsection {* The @{text receive_2b} action *}

definition receive_2b where "receive_2b s i b a v \<equiv>
  if (~ decided s i) \<and> i \<ge> lowest s
  then let
      s' = s\<lparr>twobs := (twobs s)(i := (twobs s i)(b := insert a (twobs s i b)))\<rparr>
    in (
      if (twobs s' i b = (acceptors s))
      then let s'' = s'\<lparr>decision := (decision s)(i := Some v)\<rparr>
        in (s'', send_all s (Decision (id s) i v))
      else (s', {}) )
  else (s, {})"
  
definition receive_decision where "receive_decision s a i v \<equiv>
  let s' = s\<lparr>decision := (decision s)(i := Some v), decisions := (decisions s)(i := (
    decisions s i)(a := Some v))\<rparr>;
    s'' = if (\<forall> a \<in> acceptors s . decisions s i a \<noteq> None \<and> i < bound s) then s'\<lparr>bound := i\<rparr> else s'
  in (s', {})"

subsection {* The @{text process_msg} action *}

fun process_msg where
  "process_msg s (Phase1a b) = receive_1a s b"
  | "process_msg s (Phase2a b i v) = receive_2a s i b v"
  | "process_msg s (Phase1b a b i vs) = receive_1b s a b i vs"
  | "process_msg s (Phase2b a i b v) = receive_2b s i b a v"
  | "process_msg s (Fwd v) = receive_fwd s v"
  | "process_msg s (Decision a i v) = receive_fwd s v"

end

subsection {* Global system IOA. *} 

record ('a,'v) global_state =
  lstate :: "'a \<Rightarrow> ('a, 'v)acc"
  network :: "('a, 'v) packet set"

context amp_r3 begin

definition global_start where "global_start \<equiv>
  \<lparr>lstate = (\<lambda> a . local_start a), network = {}\<rparr>"

inductive trans_rel :: "(('a,'v) global_state \<times> 'v paxos_action \<times> ('a,'v) global_state) \<Rightarrow> bool" where
  "\<lbrakk>(Packet a m) \<in> network s; process_msg ((lstate s) a) m = (sa', ms); m = Phase2b a i b v;
    decision ((lstate s) a) \<noteq> decision sa'\<rbrakk>
    \<Longrightarrow> trans_rel (s, Learn i v, 
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
  
inductive_cases trans_rel_cases:"trans_rel (s,a,s')"

abbreviation(input) local_step where "local_step a p r r' \<equiv> 
  r' = r\<lparr>lstate := (lstate r)(a := fst p), network := network r \<union> snd p\<rparr>"
  
lemma trans_cases:
  assumes "trans_rel (r, act, r')"
  obtains
    (propose) a v where "act = Propose v" and "local_step a (propose (lstate r a) v) r r'"
  | (learn) a i b v m p where "act = Learn i v" and "m = Phase2b a i b v"
    and "p = receive_2b (lstate r a) i b a v"
    and "local_step a p r r'"
    and "Packet a m \<in> network r" 
    and "decision (lstate r a) \<noteq> decision (fst p)"
  | (acquire_leadership) a where "act = Internal" and "local_step a (try_acquire_leadership (lstate r a)) r r'"
  | (receive_1a) a b m p where "act = Internal" and "m = Phase1a b"
    and "p = receive_1a (lstate r a) b"
    and "local_step a p r r'"
    and "Packet a m \<in> network r"
  | (receive_2a) a i b v m p where "act = Internal" and "m = Phase2a i b v"
    and "p = receive_2a (lstate r a) i b v"
    and "local_step a p r r'"
    and "Packet a m \<in> network r"
  | (receive_2b) a a2 i b v m p where "act = Internal" and "m = Phase2b a2 i b v"
    and "p = receive_2b (lstate r a) i b a2 v"
    and "local_step a p r r'"
    and "Packet a m \<in> network r"
  | (receive_1b) a b vs m p a2 where "act = Internal" and "m = Phase1b a2 b vs"
    and "p = receive_1b (lstate r a) a2 b vs"
    and "local_step a p r r'"
    and "Packet a m \<in> network r"
  | (fwd) a v m p where "act = Internal" and "m = Fwd v"
    and "p = receive_fwd (lstate r a) v"
    and "local_step a p r r'"
    and "Packet a m \<in> network r"
proof -
  show ?thesis using assms
    apply (rule trans_rel_cases)
       apply (metis fst_conv learn snd_conv)
      defer
      apply (metis fst_conv propose snd_conv)
     apply (metis acquire_leadership fst_conv snd_conv)
    subgoal premises prems for a m (* TODO: how to apply induct here without subgoal? *)
      using prems
      apply (induct rule:process_msg.induct)
          apply (metis fst_conv process_msg.simps(1) receive_1a snd_conv)
         apply (metis fst_conv process_msg.simps(2) receive_2a snd_conv)
        defer
        apply (metis fst_conv process_msg.simps(4) receive_1b snd_conv)
       apply (metis amp_r3.process_msg.simps(5) fst_conv fwd snd_conv)
      by (metis fst_conv process_msg.simps(3) receive_2b snd_conv)
    done
qed

definition ioa where
  "ioa \<equiv> \<lparr>ioa.asig = paxos_asig, ioa.start = {global_start}, ioa.trans = Collect trans_rel\<rparr>"

end

end