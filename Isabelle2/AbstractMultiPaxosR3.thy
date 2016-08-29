chapter {* Distributed and executable algorithm *}

theory AbstractMultiPaxosR3 
  imports Utils "~~/src/HOL/Library/FinFun" MaxByKey IOA Quorums Paxos_Sig
begin

unbundle finfun_syntax

type_synonym bal = nat
type_synonym inst = nat

section {* Local state and transitions *}

subsection {* Data structures *}

locale amp_r3 =
  fixes leader :: "bal \<Rightarrow> 'a::linorder"
  and next_bal :: "bal \<Rightarrow> 'a \<Rightarrow> bal"
  and as :: "'a set"
  and quorums :: "'a set set"
begin

datatype 'v inst_status =
  Decided 'v | Proposed 'v | Free
  -- {* An instance is in status @{term Free} locally when the acceptor has not itself proposed 
    or seen a decision in that instance, or seen a proposal. *}

end

record ('a, 'v) local_state =
  -- {* The local state of an acceptor. *}
  id :: 'a
  acceptors :: "'a set"
  ballot :: bal
  log :: "inst \<Rightarrow>f 'v amp_r3.inst_status"
    -- {* Last ballot in which the acceptor voted. *}
  votes :: "inst \<Rightarrow>f ('v \<times> bal) option"
  onebs :: "bal \<Rightarrow>f ('a \<Rightarrow>f inst \<Rightarrow>f ('v\<times>bal) option) option"
    -- {* The oneb messages received when the acceptor tries to acquire leadership. *}
  twobs :: "inst \<Rightarrow>f bal \<Rightarrow>f 'a set"
    -- {* the twob messages received (they are broadcast). *}

context amp_r3
begin

datatype ('aa,'vv) msg =
  Phase1a bal
  | Phase1b bal "inst \<Rightarrow>f ('vv \<times> bal) option"
  | Phase2a inst bal 'vv
  | Phase2b 'aa inst bal 'vv
  (* | Decision inst 'v *)
  | Fwd 'vv

datatype ('aa,'vv) packet =
  Packet 'aa  "('aa,'vv) msg"

definition local_start where "local_start a \<equiv>
  \<lparr>id = a, acceptors = as, ballot = 0, log = K$ Free,
    votes = K$ None, onebs = K$ None, twobs = K$ K$ {}\<rparr>"

subsection {* The propose action *} 

fun last_contiguous :: "nat list \<Rightarrow> nat" where 
  "last_contiguous [x] = x"
| "last_contiguous (x#y#xs) = (if y = Suc x then last_contiguous (y#xs) else x)"

definition send_all where
  "send_all s m \<equiv> { Packet a m | a . a \<in> acceptors s \<and> a \<noteq> id s}"
  (* "send_all s m \<equiv> (\<lambda> a . Packet a m) ` (acceptors s - {id s})" *)

definition next_inst where "next_inst s \<equiv>
  last_contiguous (finfun_to_list (log s))"
  -- {* TODO: optimize using a definition with finfun_rec. *}
  
definition do_2a where "do_2a s v \<equiv>
  let
    i = next_inst s;
    b = ballot s;
    s' = s\<lparr>log := (log s)(i $:= Proposed v),
      twobs := (twobs s)(i $:= (twobs s $ i)(b $:= {id s}))\<rparr>;
    msgs = send_all s (Phase2a i b v)
  in (s', msgs)"
  
definition propose where "propose s v \<equiv> 
  let l = leader (ballot s) in
    if l = id s 
    then do_2a s v
    else (s, {Packet l (Fwd v)})"
  -- {* TODO: Here we loose the proposal if it happens during an unsuccessful
  leadership acquisition attempt. *}

subsection {* The @{text receive_fwd} action *}

definition receive_fwd where "receive_fwd s v \<equiv>
  let l = leader (ballot s) in
    if l = id s
    then do_2a s v
    else (s, {Packet l (Fwd v)})"
  -- {* TODO: Here we loose the proposal if it happens during an unsuccessful
  leadership acquisition attempt. *}
  
end

subsection {* The @{text try_acquire_leadership} action *}

locale update_onebs =
  fixes onebs :: "bal \<Rightarrow>f ('a \<Rightarrow>f inst \<Rightarrow>f ('v\<times>bal) option) option"
  and votes :: "inst \<Rightarrow>f ('v \<times> bal) option"
  and  b :: bal and a :: 'a
begin 
  abbreviation(input) at_b where "at_b \<equiv> onebs $ b"
  abbreviation(input) from_none where "from_none \<equiv> (K$ K$ None)(a $:= votes)"
  abbreviation(input) from_existing where "from_existing \<equiv> \<lambda> ff . ff(a $:= votes)"
  definition new_onebs where "new_onebs \<equiv>
    case at_b of None \<Rightarrow> onebs(b $:= Some from_none)
    | Some ff \<Rightarrow> onebs(b $:= Some (from_existing ff))"
end

global_interpretation uonebs:update_onebs onebs votes b a for onebs votes b a 
  defines new_onebs = update_onebs.new_onebs .

context amp_r3 begin

definition try_acquire_leadership where "try_acquire_leadership s \<equiv>
  let
    b = next_bal (ballot s) (id s);
    s' = s\<lparr>onebs := new_onebs (onebs s) (votes s) b (id s), ballot := b\<rparr>;
    msgs = send_all s (Phase1a b)
  in (s, msgs)"

subsection {* The @{text receive_1a} action *}

definition receive_1a where "receive_1a s b \<equiv> if b > ballot s then
      let 
        msgs = {Packet (leader b) (Phase1b b (votes s))};
        s' = s\<lparr>ballot := b\<rparr>
      in (s', msgs)
    else (s, {})"

end 

subsection {* The @{text receive_1b} action *}

locale receive_1b =
  fixes votes :: "'a \<Rightarrow>f inst \<Rightarrow>f ('v\<times>bal) option"
  fixes as :: "'a set"
  fixes log :: "inst \<Rightarrow>f 'v amp_r3.inst_status"
begin

definition per_inst where "per_inst \<equiv> op$ votes ` as"
definition votes_per_inst where "votes_per_inst \<equiv> \<lambda> s . Finite_Set.fold
  (\<lambda> ff1 ff2 . (\<lambda> (vo, vs) . option_as_set vo \<union> vs) o$ ($ ff1, ff2 $) ) (K$ {}) s"
lemma votes_per_inst_code[code]:
  "votes_per_inst (set (x#xs)) = 
    (\<lambda> (vo, vs) . option_as_set vo \<union> vs) o$ ($ x, votes_per_inst (set xs) $)"
proof -
  define f :: "'b \<Rightarrow>f 'c option \<Rightarrow> 'b \<Rightarrow>f 'c set \<Rightarrow> 'b \<Rightarrow>f 'c set"
    where "f \<equiv> \<lambda> ff1 ff2 . (\<lambda> (vo, vs) . option_as_set vo \<union> vs) o$ ($ ff1, ff2 $)"
  interpret folding_idem f "K$ {}" 
    apply (unfold_locales)
     apply (auto simp add:f_def option_as_set_def fun_eq_iff expand_finfun_eq split!:option.splits)
    done
  let ?fold_expr = "\<lambda> s . Finite_Set.fold f (K$ {}) s"
  from insert_idem[of "set xs" x] have "?fold_expr (set (x#xs)) = f x (?fold_expr (set xs))"
    by (simp add:votes_per_inst_def option_as_set_def eq_fold split!:option.splits)
  thus ?thesis by (auto simp add:votes_per_inst_def f_def)
qed
  
definition max_per_inst where "max_per_inst \<equiv> (flip max_by_key snd) o$ (votes_per_inst per_inst)"
  
definition new_log where "new_log \<equiv> (\<lambda> (is, m) .
    case is of amp_r3.Decided _ \<Rightarrow> is | _ \<Rightarrow> (
      if m = {} then amp_r3.Free else amp_r3.Proposed ((fst o the_elem) m)) )
  o$ ($ log, max_per_inst $)"
  
definition msgs where "msgs \<equiv> 
  let 
    is = finfun_to_list new_log;
    to_propose = map (\<lambda> i . (i, the_elem (max_per_inst $ i))) is;
    msg_list = map (\<lambda> (i,v,b) . (amp_r3.Phase2a i b v)) to_propose
  in set msg_list"

end

global_interpretation r1:receive_1b votes as log for votes as log
  defines new_log = "receive_1b.new_log"
    and msgs = "receive_1b.msgs"
  .

context amp_r3 begin

definition receive_1b where "receive_1b s b vs \<equiv>
  let s' = s\<lparr>onebs := new_onebs (onebs s) vs b (id s)\<rparr>
  in (if (set (finfun_to_list (the (onebs s' $ b))) = acceptors s) 
    then let
        s'' = s'\<lparr>log := new_log (the (onebs s $ b)) (acceptors s) (log s)\<rparr>;
        msgs = msgs (the (onebs s $ b)) (acceptors s) (log s)
      in (s'', Set.bind msgs (send_all s)) 
    else (s', {}))"

subsection {* The @{text receive_2a} action *}

abbreviation(input) decided where "decided s i \<equiv> 
  case (log s $ i) of Decided _ \<Rightarrow> True | _ \<Rightarrow> False"
  
definition receive_2a where "receive_2a s i b v \<equiv>
  if b \<ge> ballot s then
    let s' = s\<lparr>votes := (votes s)(i $:= Some (v, b)),
      twobs := (twobs s)(i $:= (twobs s $ i)(b $:= insert (id s) (twobs s $ i $ b))),
      ballot := b\<rparr>;
      msgs = send_all s (Phase2b (id s) i b v)
    in (s', msgs)
  else (s, {})"
  
subsection {* The @{text receive_1b} action *}

definition receive_2b where "receive_2b s i b a v \<equiv>
  if (~ decided s i)
  then let
      s' = s\<lparr>twobs := (twobs s)(i $:= (twobs s $ i)(b $:= insert a (twobs s $ i $ b)))\<rparr>
    in (
      if (twobs s' $ i $ b = (acceptors s))
      then let s'' = s'\<lparr>log := (log s)(i $:= Decided v)\<rparr>
        in (s'', {})
      else (s', {}) )
  else (s, {})"

subsection {* The @{text proces_msg} action *}

fun process_msg where
  "process_msg s (Phase1a b) = receive_1a s b"
  | "process_msg s (Phase2a i b v) = receive_2a s i b v"
  | "process_msg s (Phase2b a i b v) = receive_2b s i b a v"
  | "process_msg s (Phase1b b vs) = receive_1b s b vs"
  | "process_msg s (Fwd v) = receive_fwd s v"

end

subsection {* Global system IOA. *} 

record ('a,'v) global_state =
  local_states :: "'a \<Rightarrow> ('a, 'v)local_state"
  network :: "('a, 'v) amp_r3.packet set"

context amp_r3 begin

definition global_start where "global_start \<equiv>
  \<lparr>local_states = (\<lambda> a . local_start a), network = {}\<rparr>"

inductive trans_rel :: "(('a,'v) global_state \<times> 'v paxos_action \<times> ('a,'v) global_state) \<Rightarrow> bool" where
  "\<lbrakk>(Packet a m) \<in> network s; process_msg ((local_states s) a) m = (sa', ms); m = Phase2b a i b v;
    log ((local_states s) a) \<noteq> log sa'\<rbrakk>
    \<Longrightarrow> trans_rel (s, Learn i v, 
      s\<lparr>local_states := (local_states s)(a := sa'), network := network s \<union> ms\<rparr>)"
| "\<lbrakk>(Packet a m) \<in> network s; process_msg ((local_states s) a) m = (sa', ms)\<rbrakk>
    \<Longrightarrow> trans_rel (s, Internal, 
      s\<lparr>local_states := (local_states s)(a := sa'), network := network s \<union> ms\<rparr>)"
| "\<lbrakk>propose ((local_states s) a) v = (sa', ms)\<rbrakk>
    \<Longrightarrow> trans_rel (s, Propose v, 
      s\<lparr>local_states := (local_states s)(a := sa'), network := network s \<union> ms\<rparr>)"
| "\<lbrakk>try_acquire_leadership ((local_states s) a) = (sa', ms)\<rbrakk>
    \<Longrightarrow> trans_rel (s, Internal, 
      s\<lparr>local_states := (local_states s)(a := sa'), network := network s \<union> ms\<rparr>)"
  
inductive_cases trans_rel_cases:"trans_rel (s,a,s')"

abbreviation(input) local_step where "local_step a p r r' \<equiv> 
  r' = r\<lparr>local_states := (local_states r)(a := fst p), network := network r \<union> snd p\<rparr>"
  
lemma trans_cases:
  assumes "trans_rel (r, act, r')"
  obtains
    (propose) a v where "act = Propose v" and "local_step a (propose (local_states r a) v) r r'"
  | (learn) a i b v m p where "act = Learn i v" and "m = Phase2b a i b v"
    and "p = receive_2b (local_states r a) i b a v"
    and "local_step a p r r'"
    and "Packet a m \<in> network r" 
    and "log (local_states r a) \<noteq> log (fst p)"
  | (acquire_leadership) a where "act = Internal" and "local_step a (try_acquire_leadership (local_states r a)) r r'"
  | (receive_1a) a b m p where "act = Internal" and "m = Phase1a b"
    and "p = receive_1a (local_states r a) b"
    and "local_step a p r r'"
    and "Packet a m \<in> network r"
  | (receive_2a) a i b v m p where "act = Internal" and "m = Phase2a i b v"
    and "p = receive_2a (local_states r a) i b v"
    and "local_step a p r r'"
    and "Packet a m \<in> network r"
  | (receive_2b) a a2 i b v m p where "act = Internal" and "m = Phase2b a2 i b v"
    and "p = receive_2b (local_states r a) i b a2 v"
    and "local_step a p r r'"
    and "Packet a m \<in> network r"
  | (receive_1b) a b vs m p where "act = Internal" and "m = Phase1b b vs"
    and "p = receive_1b (local_states r a) b vs"
    and "local_step a p r r'"
    and "Packet a m \<in> network r"
  | (fwd) a v m p where "act = Internal" and "m = Fwd v"
    and "p = receive_fwd (local_states r a) v"
    and "local_step a p r r'"
    and "Packet a m \<in> network r"
proof -
  show ?thesis using assms
    apply (rule trans_rel_cases)
       apply (metis fst_conv learn snd_conv)
      defer
      apply (metis fst_conv propose snd_conv)
     apply (metis acquire_leadership fst_conv snd_conv)
    subgoal premises prems for a m (* TODO: how to apply induct here, without subgoal...*)
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