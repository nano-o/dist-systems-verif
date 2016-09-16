chapter {* Distributed and executable algorithm *}

theory AbstractMultiPaxosR3
  imports Utils FinFun_Supplemental MaxByKey IOA Quorums Paxos_Sig
begin

unbundle finfun_syntax

type_synonym bal = nat
type_synonym inst = nat

section {* Local state and transitions *}

subsection {* Data structures *}

record ('a, 'v) acc =
  -- {* The local state of an acceptor. *}
  id :: 'a
  acceptors :: "'a set"
  ballot :: bal
  decision :: "inst \<Rightarrow>f 'v option"
    -- {* Last ballot in which the acceptor voted. *}
  inst_status :: "bal \<Rightarrow>f (inst \<Rightarrow>f 'v option) option"
    -- {* Mirrors the member of the same name in R1 *}
  proposal :: "inst \<Rightarrow>f bal \<Rightarrow>f 'v option"
  votes :: "inst \<Rightarrow>f ('v \<times> bal) option"
  onebs :: "bal \<Rightarrow>f ('a \<Rightarrow>f (inst \<Rightarrow>f ('v\<times>bal) option) option)"
    -- {* The oneb messages received when the acceptor tries to acquire leadership. 
    Note that we need the outermost option to signify that we did not receive a oneb message
    from the acceptor, as opposed to receiving a oneb message from an acceptor that never voted.  *}
  twobs :: "inst \<Rightarrow>f bal \<Rightarrow>f 'a set"
    -- {* the twob messages received (they are broadcast). *}

datatype ('aa,'vv) msg =
  Phase1a bal
  | Phase1b 'aa bal "inst \<Rightarrow>f ('vv \<times> bal) option"
  | Phase2a inst bal 'vv
  | Phase2b 'aa inst bal 'vv
  | Fwd 'vv
  (* | Decision inst 'v *)
  
datatype ('aa,'vv) packet =
  Packet 'aa  "('aa,'vv) msg"

locale amp_r3 =
  fixes leader :: "bal \<Rightarrow> 'a::linorder"
  and next_bal :: "bal \<Rightarrow> 'a \<Rightarrow> bal"
  and as :: "'a set"
  and quorums :: "'a set set"
begin

definition local_start where "local_start a \<equiv>
  \<lparr>id = a, acceptors = as, ballot = 0, decision = K$ None, inst_status = K$ None,
  proposal = K$ K$ None, votes = K$ None, onebs = K$ K$ None, twobs = K$ K$ {}\<rparr>"
  
end

subsection {* The propose action *}

definition send_all where send_all_def[code del]:
  "send_all s m \<equiv> { Packet a m | a . a \<in> acceptors s \<and> a \<noteq> id s}"
  -- {* TODO: This definition does not always work for code generation. Why? 
  That's why there is a code equation below. *}
  
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

definition next_inst where "next_inst s \<equiv> let b = ballot s in 
  first_hole (finfun_to_list (the (inst_status s $ b)))"
  
lemma next_inst_lemma:
  fixes s 
  assumes "inst_status s $ (ballot s) = Some f" and "finfun_default f = None"
  shows "f $ (next_inst s) = None"
proof -
  let ?b="ballot s"
  let ?l="finfun_to_list (the (inst_status s $ ?b))" 
  have 2:"distinct ?l" and 3:"sorted ?l" by (simp_all add: distinct_finfun_to_list sorted_finfun_to_list)
  moreover have "next_inst s = first_hole (finfun_to_list f)" using assms(1) unfolding next_inst_def  by auto
  ultimately show "f $ (next_inst s) = None" using assms first_hole_lemma[OF 3 2] by (auto simp add:next_inst_def finfun_dom_conv)
qed
  
definition do_2a where "do_2a s v \<equiv>
  let
    i = next_inst s;
    b = ballot s;
    s' = s\<lparr>proposal := (proposal s)(i $:= (proposal s $ i)(b $:= Some v)),
      twobs := (twobs s)(i $:= (twobs s $ i)(b $:= {id s}))\<rparr>;
    msgs = send_all s (Phase2a i b v)
  in (s', msgs)"
 
definition propose where "propose s v \<equiv> 
  let l = leader (ballot s) in
    if l = id s
    then (do_2a s v)
    else (s, {Packet l (Fwd v)})"
  -- {* TODO: Here we loose the proposal if it happens during an unsuccessful leadership acquisition attempt. *} 

subsection {* The @{text receive_fwd} action *}

definition receive_fwd where "receive_fwd s v \<equiv>
  let l = leader (ballot s) in
    if l = id s
    then do_2a s v
    else (s, {Packet l (Fwd v)})"
  -- {* TODO: Here we loose the proposal if it happens during an unsuccessful leadership acquisition attempt. *}
  
end

subsection {* The @{text try_acquire_leadership} action *}

context amp_r3 begin

definition try_acquire_leadership where "try_acquire_leadership s \<equiv>
  let
    a = id s;
    b = next_bal (ballot s) a;
    s' = s\<lparr>onebs := (onebs s)(b $:= ((onebs s) $ b)(a $:= Some (votes s))), 
      ballot := b\<rparr>;
    msgs = send_all s (Phase1a b)
  in (s', msgs)"

subsection {* The @{text receive_1a} action *}

definition receive_1a where "receive_1a s b \<equiv> 
  if b > ballot s then let
      msgs = {Packet (leader b) (Phase1b (id s) b (votes s))};
      s' = s\<lparr>ballot := b\<rparr>
    in (s', msgs)
  else (s, {})"
  
end 

subsection {* The @{text receive_1b} action *}

locale receive_1b =
  fixes onebs :: "'a \<Rightarrow>f (inst \<Rightarrow>f ('v\<times>bal) option) option"
  fixes q :: "'a set"
  fixes decision :: "inst \<Rightarrow>f 'v option"
  fixes b :: bal
begin

text {* Why not do things with @{term finfun_rec}? *}

text {* Intended to be used when a oneb message has been received from each member of q. *}

definition c where 
  "c a vs \<equiv> (\<lambda> (vo, vs) . option_as_set vo \<union> vs) o$ ($ the (onebs $ a), vs $)"
  
definition pre_votes_per_inst where
  "pre_votes_per_inst S \<equiv> Finite_Set.fold c (K$ {}) S"

definition votes_per_inst where
  "votes_per_inst \<equiv> pre_votes_per_inst q"
  
sublocale folding_idem c "K$ {}"
  apply (unfold_locales)
   apply (auto simp add:c_def option_as_set_def fun_eq_iff expand_finfun_eq split!:option.splits)
  done

lemma votes_per_inst_code[code]:
  "pre_votes_per_inst (set (x#xs)) = c x (pre_votes_per_inst (set xs))" 
  using insert_idem[of "set xs" x]
  by (simp add: eq_fold pre_votes_per_inst_def) 

definition max_per_inst where "max_per_inst \<equiv> (flip max_by_key snd) o$ votes_per_inst"
  
definition new_status where "new_status \<equiv>
  (map_option fst) o$ (\<lambda> m . if m = {} then None else Some (the_elem m)) o$ max_per_inst"
  
definition to_propose where "to_propose \<equiv>
  (\<lambda> (d,s) . case d of Some _ \<Rightarrow> {} | None \<Rightarrow> fst ` s) o$ ($ decision, max_per_inst $)"

  (*
definition msgs_2 where "msgs_2 \<equiv> let
    is = ((\<lambda> s . case s of Decided _ \<Rightarrow> False | _ \<Rightarrow> True) o$ decision);
    to_propose = my_comp (\<lambda> i (b,m) . if m = {} \<or> \<not> b then {} else ((case_prod (flip (Phase2a i))) ` m))
      ($is, max_per_inst$)
    in \<Union> {the (to_propose $ i) | i . i \<in> set (finfun_to_list to_propose)}" *)
  
definition msgs where "msgs \<equiv>
  let 
    is = finfun_to_list to_propose;
    to_propose = map (\<lambda> i . (i, to_propose $ i)) is;
    msg_list = map (\<lambda> (i,vs) . (Phase2a i b) ` vs) to_propose
  in \<Union> (set msg_list)"

lemma msgs_lemma:
  "\<And> m . m \<in> msgs \<Longrightarrow> case m of (Phase2a _ _ _) \<Rightarrow> True | _ \<Rightarrow> False"
  by (auto simp add:local.msgs_def) 

end

global_interpretation r1:receive_1b onebs as decision b for onebs as decision b
  defines new_status = "r1.new_status" and msgs = "r1.msgs"
  .

context amp_r3 begin

definition receive_1b where "receive_1b s a b vs \<equiv>
  let s' = s\<lparr>onebs := (onebs s)(b $:= ((onebs s) $ b)(a $:= Some vs))\<rparr>
  in (if (set (finfun_to_list (onebs s' $ b)) = acceptors s)
      \<and> inst_status s $ b = None
    then let
        s'' = s'\<lparr>inst_status := (inst_status s)(b $:= Some (new_status (onebs s $ b) (acceptors s)))\<rparr>;
        msgs = msgs (onebs s $ b) (acceptors s) (decision s) (ballot s)
      in (s'', \<Union> {send_all s m | m . m \<in> msgs})
    else (s', {}))"

subsection {* The @{text receive_2a} action *}

abbreviation(input) decided where "decided s i \<equiv> 
  case (decision s $ i) of Some _ \<Rightarrow> True | _ \<Rightarrow> False"
  
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
      then let s'' = s'\<lparr>decision := (decision s)(i $:= Some v)\<rparr>
        in (s'', {})
      else (s', {}) )
  else (s, {})"

subsection {* The @{text process_msg} action *}

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