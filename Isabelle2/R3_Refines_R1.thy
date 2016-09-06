section {* R3 refines R1 *} 

theory R3_Refines_R1   
imports AbstractMultiPaxosR3 AbstractMultiPaxosR1 Simulations Hist_Supplemental IOA_Automation
begin

section {* A few lemmas *}

lemma comprehension_to_fold:
  fixes Y P c
  assumes "finite Y" 
  defines "c \<equiv> \<lambda> y xs . xs \<union> {x . P x y}"
  shows "{x . \<exists> y \<in> Y . P x y} = Finite_Set.fold c {} Y" using assms
proof -
  interpret c_folding:folding_idem c "{}"
    apply (unfold_locales)
     apply (auto simp add:c_def)
    done
  show ?thesis using assms(1)
  proof (induct Y)
    case empty
    then show ?case by simp
  next
    case (insert x F)
    have "Finite_Set.fold c {} (insert x F) = c x {x . \<exists> y \<in> F . P x y}"
      using c_folding.eq_fold c_folding.insert insert.hyps(1) insert.hyps(2) insert.hyps(3) by auto
    also have "... =  {z . \<exists> y \<in> (insert x F) . P z y}" 
      by (fastforce simp add:c_def)
    finally show ?case by simp
  qed
qed

locale receive_1b_lemmas = receive_1b onebs as log for onebs as log +
  assumes votes_default:"\<And> a . finfun_default (onebs $ a) = None"
    and log_default:"finfun_default log = inst_status.Free" and fin:"finite as"
  and conservative:"\<And> a a' i b v v' . \<lbrakk>onebs $ a $ i = Some (v,b); onebs $a' $ i = Some (v',b)\<rbrakk>
        \<Longrightarrow> v = v'"
begin

lemma per_inst_lemma:
  "\<And> ff . ff \<in> per_inst \<Longrightarrow> finfun_default ff = None"
  using receive_1b_lemmas_axioms receive_1b_lemmas_def
  using per_inst_def
  by (metis (no_types, hide_lams) image_iff) 

lemma votes_per_inst_default:
  fixes s assumes "finite s" and "\<And> ff . ff \<in> s \<Longrightarrow> finfun_default ff = None"
  shows "finfun_default (votes_per_inst s) = {}"
proof (simp add:votes_per_inst_def)
  show "finfun_default (Finite_Set.fold combine (K$ {}) s) = {}" using assms
  proof (induct s)
    case empty
    then show ?case by (simp add:combine_def finfun_default_const)
  next
    case (insert x F)
    have 1:"Finite_Set.fold combine (K$ {}) (insert x F)
      = combine x (Finite_Set.fold combine (K$ {}) F)" using insert_idem
      by (metis eq_fold insert.hyps(1))
    have "finfun_default (Finite_Set.fold combine (K$ {}) F) = {}"
      by (simp add: insert.hyps(3) insert.prems)
    moreover have "finfun_default x = None"
      by (simp add: insert.prems) 
    ultimately have "finfun_default ($ x, Finite_Set.fold combine (K$ {}) F $) = (None, {})"
      by (simp add: diag_default)
    hence "finfun_default ( (\<lambda>(vo, vs). option_as_set vo \<union> vs) \<circ>$
                 ($x, Finite_Set.fold combine (K$ {}) F$)) = {}"
      by (simp add:comp_default option_as_set_def)
    thus ?case apply (simp add:1) by (auto simp add:combine_def) 
  qed
qed

lemma max_per_inst_default:
  "finfun_default (max_per_inst) = {}"
proof -
  have "finfun_default (votes_per_inst per_inst) = {}"
  proof -
    have "finite per_inst" using fin by (simp add:per_inst_def)
    thus ?thesis by (simp add:per_inst_lemma votes_per_inst_default)
  qed
  thus ?thesis by (simp add:max_per_inst_def max_by_key_def comp_default)
qed

lemma new_log_default:
  "finfun_default new_log = inst_status.Free" using log_default
  by (auto simp add:new_log_def max_per_inst_default comp_default diag_default)


lemma votes_per_inst_decl: 
  "votes_per_inst per_inst $ i = {(v,b) . \<exists> a \<in> as . onebs $ a $ i = Some (v,b)}"
  sorry

lemma conservative_per_inst:
  fixes v v' b i
    assumes "(v,b) \<in> votes_per_inst per_inst $ i"
    and "(v',b) \<in> votes_per_inst per_inst $ i"
  shows "v = v'" using conservative assms votes_per_inst_decl by auto

lemma test:
  assumes "max_by_key ps snd \<noteq> {}"
  obtains p where "max_by_key ps snd = {p}"
    using max_by_key_ordered 
  oops

lemma max_per_inst_lemma:
  "\<forall> i . max_per_inst $ i = max_by_key {(v,b) . (\<exists> a \<in> as . onebs $ a $ i = Some (v,b))} snd"
  oops
  
lemma max_per_inst_lemma_2:
  "\<forall> i . let m = max_by_key {(v,b) . (\<exists> a \<in> as . onebs $ a $ i = Some (v,b))} snd in
     case log $ i of Decided _ \<Rightarrow> new_log $ i = log $ i
     | _ \<Rightarrow> if m = {} then new_log $ i = Free 
        else new_log $ i = Active"
  oops
  
lemma test:
  "new_log $ i = Active \<longleftrightarrow> (\<exists> b . Phase2a i b v \<in> msgs)"
  apply (simp add:msgs_def) 
  oops
  
end
  
section {* Refinement proof using a refinement mapping *}
  
locale ref_proof_4 = quorums quorums + amp_r3 leader next_bal as quorums
  + r1:ampr1_ioa quorums leader
  for quorums :: "('a::linorder) set set" and leader :: "bal \<Rightarrow> ('a::linorder)" and next_bal as + 
  fixes ampr3_ioa :: "(('a, 'v) global_state, 'v paxos_action) ioa" 
    and ampr1_ioa :: "(('v, 'a, 'l) ampr1_state, 'v paxos_action) ioa" 
  defines "ampr3_ioa \<equiv> ioa" and "ampr1_ioa \<equiv> r1.ioa"
  fixes a1 a2 a3
  assumes at_least_3:"a1 \<in> as \<and> a2 \<in> as \<and> a3 \<in> as \<and> a1 \<noteq> a2 \<and> a3 \<noteq> a2 \<and> a3 \<noteq> a1"
  assumes fin:"finite as" and infin:"infinite (UNIV::'a set)"
    -- {* @{term "UNIV::'a set"} must be infinite for @{term finfun_default} to make sense. *}
begin

interpretation IOA .

lemmas action_defs = propose_def do_2a_def receive_2b_def
      try_acquire_leadership_def receive_1a_def receive_2a_def receive_1b_def receive_fwd_def
  send_all_def Let_def

lemmas init_defs = ampr3_ioa_def ioa_def global_start_def local_start_def
  ampr1_ioa_def r1.ioa_def r1.start_def r1.start_s_def 

method trans_cases =
  (simp add:is_trans_def ampr3_ioa_def ioa_def, elim trans_cases)

definition inv1 where inv1_def[inv_proofs_defs]:
  "inv1 s \<equiv> \<forall> a . acceptors (lstate s a) = as \<and> id (lstate s a) = a"
lemma inv1:"invariant ampr3_ioa inv1"
  apply (rule invariantI)
   apply (simp add:inv1_def init_defs)
  apply (rm_reachable)
  apply trans_cases
         apply (auto simp add:inv1_def action_defs)
  done
declare inv1[invs]

declare finfun_upd_apply[simp]

definition inv6 where inv6_def:
  "inv6 s \<equiv> \<forall> a i b v . (Packet a (Phase2a i b v) \<in> network s \<longrightarrow> log (lstate s (leader b)) $ i \<noteq> Free)"
lemma inv6: "invariant ampr3_ioa inv6"
  apply (rule invariantI)
   apply (simp add:inv6_def init_defs)
  apply (insert invs)
  apply (instantiate_invs)
  apply (rm_reachable)
  apply (trans_cases)
        apply (fastforce simp add:inv1_def inv6_def action_defs)
        apply (fastforce simp add:inv1_def inv6_def action_defs)
       apply (simp add:inv1_def inv6_def action_defs split!:if_splits)
      apply (fastforce simp add:inv1_def inv6_def action_defs split!:if_splits)
     apply (fastforce simp add:inv1_def inv6_def action_defs split!:if_splits)
    apply (fastforce simp add:inv1_def inv6_def action_defs split!:if_splits) defer
   apply (fastforce simp add:inv1_def inv6_def action_defs split!:if_splits)
   (* TODO: The hard one is left. *) oops
  
definition inv2 where inv2_def:
  "inv2 s \<equiv> \<forall> i b v1 v2 a1 a2 .
    (Packet a1 (Phase2a i b v1) \<in> network s
      \<and> Packet a2 (Phase2a i b v2) \<in> network s \<longrightarrow> v1 = v2)"
lemma inv2:"invariant ampr3_ioa inv2"
  apply (rule invariantI)
   apply (simp add:inv2_def init_defs)
  apply (insert invs)
  apply (instantiate_invs)
  apply (rm_reachable)
  apply (trans_cases;
    (simp add:inv1_def inv2_def action_defs finfun_default_update_const split!:packet.splits msg.splits; fail)?)
  subgoal premises prems for s t act a v
  proof -
    thm prems
    show ?thesis using prems(1,2,4) oops
      nitpick[no_assms, card 'v =2, card 'a = 1, show_types]
  
definition inv3 where 
  "inv3 s \<equiv> \<forall> i a1 a2 b d1 v1 d2 v2 .
    Packet d1 (Phase2b a1 i b v1) \<in> network s \<and> Packet d2 (Phase2b a2 i b v2) \<in> network s
    \<longrightarrow> v1 = v2"
lemma inv2:"invariant ampr3_ioa inv2"
  apply (rule invariantI)
   apply (simp add:inv2_def init_defs)
  apply (insert invs)
  apply (instantiate_invs)
  apply (rm_reachable)
  apply trans_cases
  oops

definition inv5 :: "('a,'v)global_state \<Rightarrow> bool" where inv5_def[inv_proofs_defs]:
  "inv5 s \<equiv> \<forall> a b a2 p . 
    finfun_default ((acc.onebs (lstate s a)) $ b $ a2) = None
    \<and> (finfun_default (acc.votes (lstate s a)) = None)
    \<and> (p \<in> network s \<longrightarrow> 
        (case p of Packet _ (Phase1b _ _ vs) \<Rightarrow> finfun_default vs = None
        | Packet _ _ \<Rightarrow> True))"
lemma inv5:"invariant ampr3_ioa inv5"
  apply (rule invariantI)
   apply (simp add:inv5_def init_defs finfun_default_const)
  apply (insert invs)
  apply (instantiate_invs)
  apply (rm_reachable)
  apply (trans_cases;
    (simp add:inv1_def inv5_def action_defs finfun_default_update_const split!:packet.splits msg.splits; fail)?)
  subgoal premises prems for s t act a b vs m p a2 (* receive_1b*)
  proof -
    have 1:"acc.onebs (lstate t a) = new_onebs (acc.onebs (lstate s a)) vs b a2"
      using prems(2,5,6) by (auto simp add:inv1_def action_defs)
    show ?thesis
    proof (auto simp add:inv5_def)
      fix a' b' a2'
      show "finfun_default (acc.onebs (lstate t a') $ b' $ a2') = None" 
      proof (cases "a' = a")
        case True
        have 2:"acc.onebs (lstate t a') = new_onebs (acc.onebs (lstate s a')) vs b a2"
          using 1 True by auto
        have 3:"finfun_default (acc.onebs (lstate s a') $ b' $ a2') = None"
          using prems(1) by (auto simp add:inv5_def)
        show ?thesis using 2 3 prems(1,4,7)
          apply (auto simp add: inv5_def new_onebs_def update_onebs.new_onebs_def)
          apply (case_tac "b' = b", case_tac "a2' = a2")
            apply fastforce
          apply blast
          by fastforce
      next
        case False
        then show ?thesis using prems(1,6) by (simp add:inv5_def) 
      qed
    next
      fix a
      show "finfun_default (votes (lstate t a)) = None" using prems 
        by (simp add:inv1_def inv5_def action_defs finfun_default_update_const split!:packet.splits msg.splits)
    next 
      fix p
      let ?sa = "lstate s a"
      have 1:"let msgs = msgs (acc.onebs ?sa $ b) (acc.acceptors ?sa) (log ?sa)
        in snd (receive_1b ?sa a2 b vs) \<subseteq> \<Union> {send_all ?sa m | m . m \<in> msgs} "
        by (auto simp add:inv1_def action_defs)
      have 2:"\<And> m . let msgs = msgs (acc.onebs ?sa $ b) (acc.acceptors ?sa) (log ?sa) in 
        m \<in> \<Union> {send_all ?sa m | m . m \<in> msgs} \<Longrightarrow> case m of Packet _ (Phase2a _ _ _) \<Rightarrow> True | _ \<Rightarrow> False"
        using r1.msgs_lemma by (fastforce simp add:send_all_def)
      from 1 2 have "\<And> p . p \<in> snd (receive_1b ?sa a2 b vs) \<Longrightarrow> 
        case p of Packet _ (Phase2a _ _ _) \<Rightarrow> True | _ \<Rightarrow> False" by auto
      moreover have "network t = snd (receive_1b ?sa a2 b vs) \<union> network s" using prems(5,6) by auto
      ultimately show "p \<in> network t \<Longrightarrow> case p of Packet _ (Phase1b _ _ vs) \<Rightarrow> finfun_default vs = None | Packet _ _ \<Rightarrow> True"  
        using prems(1) by (force simp add:inv5_def inv1_def split!:packet.splits msg.splits)
    qed
  qed
  done
declare inv5[invs]

definition inv4 where "inv4 s \<equiv>
  (\<forall> a . finfun_default (log (lstate s a)) = Free)"
  
lemma inv4:"invariant ampr3_ioa inv4"
  apply (rule invariantI)
   apply (simp add:inv4_def init_defs)
   apply (simp add: finfun_default_const)
  apply (insert invs)
  apply (instantiate_invs)
  apply (rm_reachable)
  apply trans_cases
         apply (auto simp add:inv4_def inv1_def action_defs finfun_default_update_const finfun_upd_apply
          amp_r3.next_inst_lemma
          split!:if_splits msg.splits packet.splits inst_status.splits) oops

fun extract_vs where 
  "extract_vs (Fwd v) = {v}"
| "extract_vs (Phase2a _ _ v) = {v}"
| "extract_vs (Phase2b _ _ _ v) = {v}"
| "extract_vs (Phase1b _ _ ff) = {v . \<exists> i b . ff $ i = Some (v,b)}"
  -- {* Could be @{term "{ff $ i \<bind> (Some o fst) | i . True} \<bind> option_as_set" } *}
| "extract_vs _ = {}"
  
definition propCmd where "propCmd s \<equiv> \<Union> ((\<lambda> p . case p of Packet _ m \<Rightarrow> extract_vs m) ` network s)"

definition ref_map where "ref_map s \<equiv> \<lparr>
  ampr1_state.propCmd = propCmd s,
  ballot = \<lambda> a . acc.ballot (lstate s a),
  vote = \<lambda> i a b . if (\<exists> a2 v . Packet a2 (Phase2b a i b v) \<in> network s) 
    then Some (the_elem {v . \<exists> a2 . Packet a2 (Phase2b a i b v) \<in> network s}) else None,
  suggestion = \<lambda> i b . if (\<exists> a v. Packet a (Phase2a i b v) \<in> network s) 
    then Some (the_elem {v . \<exists> a . Packet a (Phase2a i b v) \<in> network s}) else None,
  onebs = \<lambda> a b . if (\<exists> ff . Packet (leader b) (Phase1b a b ff) \<in> network s) 
    then Some (the_elem {op$ ff | ff . Packet (leader b) (Phase1b a b ff) \<in> network s}) else None\<rparr>"
  
lemmas ref_defs = ref_map_def propCmd_def 

lemma "is_ref_map ref_map ampr3_ioa ampr1_ioa"
  apply (auto simp add:is_ref_map_def)
   apply (simp add:init_defs ref_defs)
  apply (insert invs)
  apply (instantiate_invs)
  apply (rm_reachable)
  apply trans_cases
  subgoal premises prems for s t act a v (* Propose *)
  proof (intro exI[where ?x="ref_map s"] exI[where ?x="[(act, ref_map t)]"])
    thm prems
    have "ref_map t = (ref_map s)\<lparr>propCmd := insert v (ampr1_state.propCmd (ref_map s))\<rparr>"
    proof (cases "leader (acc.ballot (lstate s a)) = a") oops
    
end

section {* Testing interpretation. *}


definition n :: nat where "n \<equiv> 3"
  -- {* The number of processes *}

definition accs where "accs \<equiv> {1..n}"
  -- {* The set of acceptors *}

definition leader where "leader (b::nat) \<equiv> (b mod n) + 1"
  
definition next_bal :: "nat \<Rightarrow> nat \<Rightarrow> nat" where "next_bal b a \<equiv> 
  (b div n + 1) * n + a"

global_interpretation cq:card_quorums accs
  defines qs = "cq.quorums" and nas = "cq.nas"
  apply (unfold_locales)
   apply (simp add: accs_def n_def)
  apply (simp add: accs_def)
  done
                
definition r3_ioa :: "((nat, nat) global_state, nat paxos_action) ioa"
  where r3_ioa_def:"r3_ioa \<equiv> amp_r3.ioa leader next_bal accs"

definition r1_ioa  :: "((nat, nat, nat) ampr1_state, nat paxos_action) ioa"
  where "r1_ioa \<equiv> ampr1_ioa.ioa qs leader"
  
global_interpretation ref_proof_4 qs leader next_bal accs 
  r3_ioa r1_ioa 1 2 3
    apply (unfold_locales)
      apply (auto simp add:accs_def n_def r3_ioa_def r1_ioa_def) .

term ioa
thm ioa_def
interpretation IOA .
thm init_defs
(* declare [[show_types, show_consts]] *)
lemma "invariant r3_ioa inv2"
  apply (rule invariantI)
   apply (simp add:inv2_def init_defs accs_def leader_def next_bal_def amp_r3.ioa_def
      amp_r3.global_start_def)
  apply (insert invs)
  apply (instantiate_invs)
  apply (rm_reachable)
  apply (trans_cases;
    (simp add:inv1_def inv2_def action_defs finfun_default_update_const split!:packet.splits msg.splits; fail)?)
apply (simp add:inv2_def inv1_def inv5_def propose_def do_2a_def send_all_def) oops
  
section {* Old attempts. *}

subsection {* Proof using a history variable (simple sketch) *}

locale ref_proof_1 = quorums quorums + amp_r3 leader next_bal as quorums 
  + r1:ampr1_ioa quorums leader
  for quorums :: "('a::linorder) set set" and leader :: "bal \<Rightarrow> ('a::linorder)" and next_bal as + 
  fixes ampr3_ioa :: "(('a, 'v) global_state, 'v paxos_action) ioa" 
    and ampr1_ioa :: "(('v, 'a, 'l) ampr1_state, 'v paxos_action) ioa" 
  defines "ampr3_ioa \<equiv> ioa" and "ampr1_ioa \<equiv> r1.ioa"
begin

interpretation IOA .

definition ghost_ioa where 
  -- {* We add a history variable that tracks the set of proposed commands. *}
  "ghost_ioa \<equiv>
      let update = \<lambda> s h a s' . case a of Propose v \<Rightarrow> insert v h | _ \<Rightarrow> h;
        init = \<lambda> s . {}
      in
    add_history ampr3_ioa update init"

lemmas ioa_defs =
   IOA.actions_def
   IOA.externals_def IOA.add_history_def

lemmas amp_defs = ioa_defs ampr1_ioa_def ampr3_ioa_def ghost_ioa_def
  ioa_def global_start_def

definition inv1 where "inv1 s \<equiv> let r3_s = fst s; h = snd s in
  \<forall> a v . (Packet a (Fwd v)) \<in> network r3_s \<longrightarrow> v \<in> h"
declare inv1_def[inv_proofs_defs]

lemma inv1:"invariant ghost_ioa inv1"
  apply (rule invariantI)
   apply (simp add:inv1_def amp_defs)
  apply (rm_reachable)
  apply (simp add:ghost_ioa_def)
  apply (simp only: split_paired_all)
  apply (frule IOA.add_hist_trans(1), drule IOA.add_hist_trans(2))
  apply (simp add:is_trans_def ampr3_ioa_def ioa_def)
  apply (drule trans_cases)
          apply (auto simp add:inv1_def)
         defer 
         apply(simp add:receive_2b_def Let_def split:if_splits option.splits)
        apply(simp add:try_acquire_leadership_def Let_def send_all_def split:if_splits option.splits)
       apply (metis amp_r3.msg.distinct(13) amp_r3.packet.inject empty_iff receive_1a_def singletonD snd_conv)
      apply(simp add:receive_2a_def Let_def send_all_def split:if_splits option.splits)
     apply(simp add:receive_2b_def Let_def send_all_def split:if_splits option.splits)
    apply(simp add:receive_1b_def receive_1b.msgs_def msgs_def Let_def send_all_def split:if_splits option.splits)
  subgoal proof - oops
    fix a :: "('a, 'v) global_state" and b :: "'v set" and ac :: 'a and bb :: nat and vs :: "nat \<Rightarrow>f ('v \<times> nat) option" and ad :: "('a, 'v) acc" and bc :: "('a, 'v) packet set" and ae :: 'a and v :: 'v
    assume a1: "(\<exists>x. finfun_dom (receive_1b.new_log (the (acc.onebs (lstate a ac) $ bb)) (acceptors (lstate a ac)) (log (lstate a ac))) $ x \<and> (Fwd v::('a, 'v) msg) = (case the_elem (receive_1b.max_per_inst (the (acc.onebs (lstate a ac) $ bb)) (acceptors (lstate a ac)) $ x) of (v, b) \<Rightarrow> Phase2a x b v)) \<and> ae \<in> acceptors (lstate a ac) \<and> ae \<noteq> acc.id (lstate a ac)"
    have "\<And>n p v. (case p of (v, na) \<Rightarrow> Phase2a n na v) \<noteq> (Fwd v::('a, 'v) msg)"
      by (metis amp_r3.msg.distinct(17) case_prod_conv surj_pair)
    then show "v \<in> b"
      using a1 by metis
  qed
   apply(simp add: do_2a_def receive_fwd_def Let_def send_all_def split:if_splits option.splits)
  apply(simp add: do_2a_def propose_def Let_def send_all_def split:if_splits option.splits)
  done

end

subsection {* Proof using a more involved history state. *}
  
locale ref_proof = quorums quorums + amp_r3 leader next_bal as quorums 
  + r1:ampr1_ioa quorums leader
  for quorums :: "('a::linorder) set set" and leader :: "bal \<Rightarrow> ('a::linorder)" and next_bal as + 
  fixes ampr3_ioa :: "(('a, 'v) global_state, 'v paxos_action) ioa" 
    and ampr1_ioa :: "(('v, 'a, 'l) ampr1_state, 'v paxos_action) ioa" 
  defines "ampr3_ioa \<equiv> ioa" and "ampr1_ioa \<equiv> r1.ioa"
begin

interpretation IOA .

lemmas ioa_defs =
   IOA.actions_def
   IOA.externals_def IOA.add_history_def

definition update_hist where "update_hist s h a s' \<equiv> case a of 
  Propose v \<Rightarrow> h\<lparr>propCmd := insert v (propCmd h)\<rparr>
  | Internal \<Rightarrow> 
      h\<lparr>vote := \<lambda> i a b . case (votes (lstate s' a) $ i) of Some (v,b2) \<Rightarrow> 
          (if b = b2 then Some v else (vote h i a b)) | None \<Rightarrow> None,
        ampr1_state.ballot := \<lambda> a . acc.ballot (lstate s' a),
        suggestion := \<lambda> i b . case (log (lstate s' (leader b)) $ i) of Proposed v \<Rightarrow> (
              case (log (lstate s (leader b)) $ i) of Free \<Rightarrow> Some v | _ \<Rightarrow> suggestion h i b)
          | Decided v \<Rightarrow> suggestion h i b
          | Free \<Rightarrow> None,
        onebs := \<lambda> a b . if acc.ballot (lstate s' a) = b \<and> acc.ballot (lstate s' a) \<noteq> b
          then Some (op$ (votes (lstate s a))) else None\<rparr>
  | _ \<Rightarrow> h"

definition ghost_ioa where 
  -- {* This gets a little tricky. Why not define a history IOA without @{term add_hist} and 
  prove trace inclusion with a forward simulation? *}
  "ghost_ioa \<equiv> add_history ampr3_ioa update_hist (\<lambda> s . r1.start_s)"

lemmas amp_defs = ioa_defs ampr1_ioa_def ampr3_ioa_def ghost_ioa_def
  ioa_def global_start_def

definition inv1 where "inv1 s \<equiv> let r3_s = fst s; h = snd s in
  \<forall> a v . (Packet a (Fwd v)) \<in> network r3_s \<longrightarrow> v \<in> propCmd h"
declare inv1_def[inv_proofs_defs]

lemma inv1:"invariant ghost_ioa inv1"
  apply (rule invariantI)
   apply (simp add:inv1_def amp_defs)
  apply (rm_reachable)
  apply (simp add:ghost_ioa_def)
  apply (simp only: split_paired_all)
  apply (frule IOA.add_hist_trans(1), drule IOA.add_hist_trans(2))
  apply (simp add:is_trans_def ampr3_ioa_def ioa_def)
  apply (elim trans_cases)
         apply (auto simp add:inv1_def update_hist_def)
         apply (simp add:propose_def do_2a_def Let_def send_all_def split:if_splits)
        apply (simp add:receive_2b_def Let_def send_all_def split:if_splits)
       apply (simp add:try_acquire_leadership_def Let_def send_all_def split:if_splits)
      apply (simp add:receive_1a_def Let_def send_all_def split:if_splits)
     apply (simp add:receive_2a_def Let_def send_all_def split:if_splits)
    apply (simp add:receive_2b_def Let_def send_all_def split:if_splits)
   apply (simp add:receive_1b_def Let_def send_all_def msgs_def receive_1b.msgs_def split:if_splits)
  subgoal proof -
    fix a :: "('a, 'v) global_state" and b :: "('v, 'a, ?'l) ampr1_state" and ac :: 'a and bb :: nat and vs :: "nat \<Rightarrow>f ('v \<times> nat) option" and ad :: "('a, 'v) acc" and bc :: "('a, 'v) packet set" and ae :: 'a and v :: 'v
    assume a1: "(\<exists>x. finfun_dom (receive_1b.new_log (the (acc.onebs (lstate a ac) $ bb)) (acceptors (lstate a ac)) (log (lstate a ac))) $ x \<and> (Fwd v::('a, 'v) msg) = (case the_elem (receive_1b.max_per_inst (the (acc.onebs (lstate a ac) $ bb)) (acceptors (lstate a ac)) $ x) of (v, b) \<Rightarrow> Phase2a x b v)) \<and> ae \<in> acceptors (lstate a ac) \<and> ae \<noteq> acc.id (lstate a ac)"
    have "\<And>n p v. (case p of (v, na) \<Rightarrow> Phase2a n na v) \<noteq> (Fwd v::('a, 'v) msg)"
      by (metis amp_r3.msg.distinct(17) case_prod_conv surj_pair)
    then show "v \<in> propCmd b" oops
      using a1 by metis
  qed
  apply (simp add:receive_fwd_def do_2a_def Let_def send_all_def split:if_splits)
  done
declare inv1[invs]

definition ref_map where "ref_map s \<equiv> snd s"
  
method apply_exI_hist =
  (match conclusion in "\<exists> e\<^sub>0 ef . refines (e\<^sub>0,ef) (?s,h) a (?s',h') ?ioa ?f" for h h' a 
    \<Rightarrow> \<open>intro exI[where ?x=h] exI[where ?x="[(a,h')]"]\<close>)

lemma "is_ref_map ref_map ghost_ioa ampr1_ioa"
  apply (auto simp add:is_ref_map_def)
   apply (simp add:ghost_ioa_def add_history_def ampr3_ioa_def r1.start_s_def ampr1_ioa_def r1.ioa_def r1.start_def
      ref_map_def)
  apply (insert invs)
  apply (instantiate_invs)
  apply (rm_reachable)
  apply (simp add:ghost_ioa_def)
  apply (frule IOA.add_hist_trans(1), drule IOA.add_hist_trans(2))
  apply (simp add:is_trans_def ampr3_ioa_def ioa_def)
  apply (elim trans_cases)
  (* Propose. *)
         apply apply_exI_hist
         apply (force simp add:ampr1_ioa_def ref_map_def refines_def update_hist_def is_trans_def r1.ioa_def
      r1.trans_def trace_match_def paxos_asig_def Let_def inv1_def r1.propose_def externals_def
      trace_def schedule_def filter_act_def propose_def do_2a_def split!:if_splits)
        prefer 7
  subgoal premises prems for s h s' h' act a v m p
    apply apply_exI_hist
    apply (simp add:refines_def)
    apply (intro conjI)
       apply (simp add:ref_map_def)
      apply (simp add:ref_map_def)
     prefer 2
     apply (simp add:trace_match_def trace_def schedule_def externals_def
        filter_act_def ampr1_ioa_def r1.ioa_def paxos_asig_def Let_def split!:if_splits)
  subgoal proof (cases "id (lstate s a) = leader (acc.ballot (lstate s a))")
    case False
    with prems(3,5,6) have "update_hist s h act s' = h" apply (simp add:update_hist_def receive_fwd_def)
    thm prems
    oops
    
end

subsection {* implementation proof using a forward simulation *}
  
locale ref_proof_3 = quorums quorums + amp_r3 leader next_bal as quorums
  + r1:ampr1_ioa quorums leader
  for quorums :: "('a::linorder) set set" and leader :: "bal \<Rightarrow> ('a::linorder)" and next_bal as + 
  fixes ampr3_ioa :: "(('a, 'v) global_state, 'v paxos_action) ioa" 
    and ampr1_ioa :: "(('v, 'a, 'l) ampr1_state, 'v paxos_action) ioa" 
  defines "ampr3_ioa \<equiv> ioa" and "ampr1_ioa \<equiv> r1.ioa"
  fixes a1 a2 a3
  assumes "a1 \<in> as" and "a2 \<in> as" and "a3 \<in> as" and "a1 \<noteq> a2" and "a3 \<noteq> a2" and "a3 \<noteq> a1"
begin

interpretation IOA .

lemmas action_defs = propose_def do_2a_def receive_2b_def
      try_acquire_leadership_def receive_1a_def receive_2a_def receive_1b_def receive_fwd_def
lemmas init_defs = ampr3_ioa_def ioa_def global_start_def local_start_def
  ampr1_ioa_def r1.ioa_def r1.start_def r1.start_s_def 

method trans_cases =
  (simp add:is_trans_def ampr3_ioa_def ioa_def, elim trans_cases)

definition inv1 where inv1_def[inv_proofs_defs]:"inv1 s \<equiv> \<forall> a . acceptors (lstate s a) = as \<and> id (lstate s a) = a"
lemma inv1:"invariant ampr3_ioa inv1"
  apply (rule invariantI)
   apply (simp add:inv1_def init_defs)
  apply (rm_reachable)
  apply trans_cases
         apply (auto simp add:Let_def inv1_def action_defs)
  done
declare inv1[invs]

fun extract_vs where 
  "extract_vs (Fwd v) = {v}"
| "extract_vs (Phase2a _ _ v) = {v}"
| "extract_vs (Phase2b _ _ _ v) = {v}"
| "extract_vs (Phase1b _ _ ff) = {v . \<exists> i b . ff $ i = Some (v,b)}"
  -- {* Could be @{term "{ff $ i \<bind> (Some o fst) | i . True} \<bind> option_as_set" }*}
| "extract_vs _ = {}"
  
definition propCmd where "propCmd s \<equiv> \<Union> ((\<lambda> p . case p of Packet _ m \<Rightarrow> extract_vs m) ` network s)"

definition propCmd2 where "propCmd2 s \<equiv> {v . \<exists> a \<in> as . 
  Packet a (Fwd v) \<in> network s 
  \<or> (\<exists> i b . Packet a (Phase2a i b v) \<in> network s)
  \<or> (\<exists> a2 \<in> as . \<exists> i b v . Packet a (Phase2b a2 i b v) \<in> network s)
  \<or> (\<exists> a2 \<in> as . \<exists> b ff i b2 . Packet a (Phase1b a2 b ff) \<in> network s \<and> ff $ i = Some (v,b2))}"

definition fwd_sim where "fwd_sim s \<equiv> {t . 
  ampr1_state.propCmd t = propCmd s
  \<and> ballot t = (\<lambda> a . acc.ballot (lstate s a))
  \<and> (\<forall> i b v . suggestion t i b = None \<longleftrightarrow> (\<forall> a . Packet a (Phase2a i b v) \<notin> network s))
  \<and> (\<forall> i b v . suggestion t i b = Some v \<longleftrightarrow> (\<forall> a . a \<noteq> leader b \<longrightarrow> Packet a (Phase2a i b v) \<in> network s))
  \<and> (\<forall> i b v a . vote t i a b = None \<longleftrightarrow> (\<forall> a2 . Packet a2 (Phase2b a i b v) \<notin> network s))
  \<and> (\<forall> i b v a . vote t i a b = Some v \<longleftrightarrow> (\<forall> a2 . a2 \<noteq> a \<longrightarrow> Packet a2 (Phase2b a i b v) \<in> network s))
  \<and> (\<forall> a b ff . onebs t a b = None \<longleftrightarrow> (Packet (leader b) (Phase1b a b ff) \<notin> network s))
  \<and> (\<forall> a b f . onebs t a b = Some f \<longleftrightarrow> (Packet (leader b) (Phase1b a b (Abs_finfun f)) \<in> network s))}"
  
lemmas sim_defs = fwd_sim_def propCmd_def 

lemma "is_forward_sim fwd_sim ampr3_ioa ampr1_ioa"
  apply (auto simp add:is_forward_sim_def)
   apply (simp add:init_defs sim_defs)
   apply (metis ref_proof_3.axioms(2) ref_proof_3_axioms ref_proof_3_axioms_def)
  apply (insert invs)
  apply (instantiate_invs)
  apply (rm_reachable)
  apply trans_cases
  subgoal premises prems for s s' t act a v (* Propose *)
  proof -
    let ?ef = "[(act, s'\<lparr>ampr1_state.propCmd := insert v (ampr1_state.propCmd s')\<rparr>)]"
    show ?thesis
      apply (intro exI[where ?x="?ef"])
      apply (intro conjI)
        prefer 3
        apply (force simp add:trace_match_def trace_def schedule_def externals_def
          filter_act_def ampr1_ioa_def r1.ioa_def paxos_asig_def Let_def is_trans_def 
          r1.trans_def split!:if_splits)
       apply simp
      subgoal proof (cases "leader (acc.ballot (lstate s a)) = acc.id (lstate s a)")
        case False
        with prems(1,4) show ?thesis by (simp add:propose_def send_all_def fwd_sim_def propCmd_def)
      next
        case True thm prems
        have 1:"\<And> a . acc.ballot (lstate t a) = ballot s' a" using prems(1,4) True 
          by (simp add:do_2a_def propose_def send_all_def fwd_sim_def Let_def propCmd_def)
        have 2:"network t = network s \<union> {Packet a2 (Phase2a (next_inst (lstate s a)) (acc.ballot (lstate s a)) v) 
            | a2 . a2 \<noteq> a \<and> a2 \<in> acceptors (lstate s a)}"
          using prems(4,2) True
          by (fastforce simp add:do_2a_def propose_def send_all_def fwd_sim_def propCmd_def Let_def inv1_def) oops
        show ?thesis using 1 2 prems(1,2) apply (auto simp add:sim_defs inv1_def split!:msg.splits packet.splits)
              apply (metis ref_proof_3.axioms(2) ref_proof_3_axioms ref_proof_3_axioms_def)
             apply meson defer
          apply meson oops
end

end