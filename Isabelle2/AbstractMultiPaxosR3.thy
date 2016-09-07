chapter {* Distributed and executable algorithm *}

theory AbstractMultiPaxosR3 
  imports Utils FinFun_Supplemental MaxByKey IOA Quorums Paxos_Sig
begin

unbundle finfun_syntax

type_synonym bal = nat
type_synonym inst = nat

section {* Local state and transitions *}

subsection {* Data structures *}

datatype 'v inst_status =
  Decided 'v | Active | Free
  -- {* An instance is in status @{term Free} locally when the acceptor has not itself proposed 
    or seen a decision in that instance, or seen a proposal. *}

record ('a, 'v) acc =
  -- {* The local state of an acceptor. *}
  id :: 'a
  acceptors :: "'a set"
  ballot :: bal
  log :: "inst \<Rightarrow>f 'v inst_status"
    -- {* Last ballot in which the acceptor voted. *}
  votes :: "inst \<Rightarrow>f ('v \<times> bal) option"
  onebs :: "bal \<Rightarrow>f ('a \<Rightarrow>f inst \<Rightarrow>f ('v\<times>bal) option)"
    -- {* The oneb messages received when the acceptor tries to acquire leadership. *}
  twobs :: "inst \<Rightarrow>f bal \<Rightarrow>f 'a set"
    -- {* the twob messages received (they are broadcast). *}

datatype ('aa,'vv) msg =
  Phase1a bal
  | Phase1b 'aa bal "inst \<Rightarrow>f ('vv \<times> bal) option"
  | Phase2a inst bal 'vv
  | Phase2b 'aa inst bal 'vv
  (* | Decision inst 'v *)
| Fwd 'vv
  
datatype ('aa,'vv) packet =
  Packet 'aa  "('aa,'vv) msg"

locale amp_r3 =
  fixes leader :: "bal \<Rightarrow> 'a::linorder"
  and next_bal :: "bal \<Rightarrow> 'a \<Rightarrow> bal"
  and as :: "'a set"
  and quorums :: "'a set set"
begin

definition local_start where "local_start a \<equiv>
  \<lparr>id = a, acceptors = as, ballot = 0, log = K$ Free,
    votes = K$ None, onebs = K$ K$ K$ None, twobs = K$ K$ {}\<rparr>"
  
end

subsection {* The propose action *} 

definition send_all where send_all_def[code del]:
  "send_all s m \<equiv> { Packet a m | a . a \<in> acceptors s \<and> a \<noteq> id s}"
  -- {* TODO: This definition does not always work for code generation. Why? *}
  
lemma send_all_code[code]:
  "send_all s m = (flip Packet m) ` (acceptors s - {id s})"
  by (auto simp add:send_all_def)

fun first_hole :: "nat list \<Rightarrow> nat" where 
  "first_hole [] = 0"
| "first_hole [x] = Suc x"
| "first_hole (x#y#xs) = (if y = Suc x then first_hole (y#xs) else Suc x)"

lemma first_hole_lemma:
  assumes "sorted l" and "distinct l"
    shows "first_hole l \<notin> set l" and "l \<noteq> [] \<Longrightarrow> first_hole l > hd l"
proof -
  have "first_hole l \<notin> set l \<and> (l \<noteq> [] \<longrightarrow> first_hole l > hd l)"
    using assms
  proof (induct l rule:first_hole.induct)
    case 1
    then show ?case
      by simp 
  next
    case (2 x)
    then show ?case
      by simp
  next
    case (3 x y xs)
    from "3.prems" have 4:"sorted (y#xs)" and 5:"distinct (y#xs)" using sorted_Cons by auto
    show ?case proof (cases "y = Suc x")
      case True
      hence 6:"first_hole (x#y#xs) = first_hole (y#xs)" by auto
      have 7:"y < first_hole (y#xs)" using 4 5 3 True by auto
      show ?thesis using 3 4 5 6 7 True by auto
    next
      case False
      with \<open>sorted (x#y#xs)\<close> and \<open>distinct (x#y#xs)\<close> have "\<And> z . z \<in> set (y#xs) \<Longrightarrow> z > Suc x"
        apply auto by (metis Suc_lessI le_imp_less_or_eq le_less_Suc_eq le_trans sorted_Cons)
      then show ?thesis apply simp using not_less by blast
    qed
  qed
  thus "first_hole l \<notin> set l" and "l \<noteq> [] \<Longrightarrow> first_hole l > hd l"
    by auto
qed
  
context amp_r3
begin

definition next_inst where "next_inst s \<equiv>
  first_hole (finfun_to_list (log s))"
  -- {* TODO: optimize using a definition with finfun_rec. *}
  
lemma next_inst_lemma:
  fixes s 
  assumes "finfun_default (log s) = Free"
  shows "(log s) $ (next_inst s) = Free"
proof -
    let ?l="finfun_to_list (log s)" 
    have 2:"distinct ?l" and 3:"sorted ?l" apply (simp add: distinct_finfun_to_list) by (simp add: sorted_finfun_to_list)
    show "(log s) $ (next_inst s) = Free" using assms(1) first_hole_lemma[OF 3 2] apply simp apply (auto simp add:next_inst_def)
    by (simp add: finfun_dom_conv)
qed
  
definition do_2a where "do_2a s v \<equiv>
  let
    i = next_inst s;
    b = ballot s;
    s' = s\<lparr>log := (log s)(i $:= Active),
      twobs := (twobs s)(i $:= (twobs s $ i)(b $:= {id s}))\<rparr>;
    msgs = send_all s (Phase2a i b v)
  in (s', msgs)"
 
definition propose where "propose s v \<equiv> 
  let l = leader (ballot s) in
    if l = id s
    then (do_2a s v)
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
  fixes onebs :: "bal \<Rightarrow>f ('a \<Rightarrow>f inst \<Rightarrow>f ('v\<times>bal) option)"
  and votes :: "inst \<Rightarrow>f ('v \<times> bal) option"
  and  b :: bal and a :: 'a
begin 
definition new_onebs where "new_onebs \<equiv> onebs(b $:= (onebs $ b)(a $:= votes))"

end
global_interpretation uonebs:update_onebs onebs votes b a for onebs votes b a 
  defines new_onebs = update_onebs.new_onebs .

context amp_r3 begin

definition try_acquire_leadership where "try_acquire_leadership s \<equiv>
  let
    b = next_bal (ballot s) (id s);
    s'' = s\<lparr>onebs := (onebs s)(b $:= ((onebs s)$ b)((id s) $:= votes s)), ballot := b\<rparr>;
    msgs = send_all s (Phase1a b)
  in (s, msgs)"

subsection {* The @{text receive_1a} action *}

definition receive_1a where "receive_1a s b \<equiv> if b > ballot s then
      let 
        msgs = {Packet (leader b) (Phase1b (id s) b (votes s))};
        s' = s\<lparr>ballot := b\<rparr>
      in (s', msgs)
    else (s, {})"

end 

subsection {* The @{text receive_1b} action *}

locale receive_1b =
  fixes onebs :: "'a \<Rightarrow>f inst \<Rightarrow>f ('v\<times>bal) option"
  fixes as :: "'a set"
  fixes log :: "inst \<Rightarrow>f 'v inst_status"
begin

definition c where 
  "c a vs \<equiv> (\<lambda> (vo, vs) . option_as_set vo \<union> vs) o$ ($ (onebs $ a), vs $)"
  
definition pre_votes_per_inst where
  "pre_votes_per_inst S \<equiv> Finite_Set.fold c (K$ {}) S"

definition votes_per_inst where
  "votes_per_inst \<equiv> pre_votes_per_inst as"
  
sublocale folding_idem c "K$ {}"
  apply (unfold_locales)
   apply (auto simp add:c_def option_as_set_def fun_eq_iff expand_finfun_eq split!:option.splits)
  done

lemma votes_per_inst_code[code]:
  "pre_votes_per_inst (set (x#xs)) = c x (pre_votes_per_inst (set xs))" 
  using insert_idem[of "set xs" x]
  by (simp add: eq_fold pre_votes_per_inst_def) 

definition max_per_inst where "max_per_inst \<equiv> (flip max_by_key snd) o$ votes_per_inst"
  
definition new_log where "new_log \<equiv> (\<lambda> (s, m) .
    case s of Decided _ \<Rightarrow> s | _ \<Rightarrow> (if m = {} then Free else Active))
  o$ ($ log, max_per_inst $)"
  
definition msgs_2 where "msgs_2 \<equiv> let
    is = ((\<lambda> s . case s of Decided _ \<Rightarrow> False | _ \<Rightarrow> True) o$ log);
    to_propose = my_comp (\<lambda> i (b,m) . if m = {} \<or> \<not> b then {} else ((case_prod (flip (Phase2a i))) ` m))
      ($is, max_per_inst$)
    in True"
  
definition msgs where "msgs \<equiv>
  let 
    is = finfun_to_list ((op= Active) o$ new_log);
    to_propose = map (\<lambda> i . (i, the_elem (max_per_inst $ i))) is;
    msg_list = map (\<lambda> (i,v,b) . (Phase2a i b v)) to_propose
  in set msg_list"

lemma msgs_lemma:
  "\<And> m . m \<in> msgs \<Longrightarrow> case m of (Phase2a _ _ _) \<Rightarrow> True |_ \<Rightarrow> False"
  by (auto simp add:local.msgs_def) 

end

global_interpretation r1:receive_1b onebs as log for onebs as log
  defines new_log = "receive_1b.new_log"
    and msgs = "receive_1b.msgs"
  .

context amp_r3 begin

definition receive_1b where "receive_1b s a b vs \<equiv>
  let s' = s\<lparr>onebs := new_onebs (onebs s) vs b a\<rparr>
  in (if (set (finfun_to_list (onebs s' $ b)) = acceptors s)
    then let
        s'' = s'\<lparr>log := new_log (onebs s $ b) (acceptors s) (log s)\<rparr>;
        msgs = msgs (onebs s $ b) (acceptors s) (log s)
      in (s'', \<Union> {send_all s m | m . m \<in> msgs})
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
  
subsection {* The @{text receive_2b} action *}

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
  | "process_msg s (Phase1b a b vs) = receive_1b s a b vs"
  | "process_msg s (Fwd v) = receive_fwd s v"

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
    log ((lstate s) a) \<noteq> log sa'\<rbrakk>
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
    and "log (lstate r a) \<noteq> log (fst p)"
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