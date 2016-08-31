section {* R3 refines R1 *} 

theory R3_Refines_R1   
imports AbstractMultiPaxosR3 AbstractMultiPaxosR1 Simulations Hist_Supplemental IOA_Automation
begin

section {* A first attempt. *}

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
  subgoal proof -
    fix a :: "('a, 'v) global_state" and b :: "'v set" and ac :: 'a and bb :: nat and vs :: "nat \<Rightarrow>f ('v \<times> nat) option" and ad :: "('a, 'v) local_state" and bc :: "('a, 'v) packet set" and ae :: 'a and v :: 'v
    assume a1: "(\<exists>x. finfun_dom (receive_1b.new_log (the (local_state.onebs (lstate a ac) $ bb)) (acceptors (lstate a ac)) (log (lstate a ac))) $ x \<and> (Fwd v::('a, 'v) msg) = (case the_elem (receive_1b.max_per_inst (the (local_state.onebs (lstate a ac) $ bb)) (acceptors (lstate a ac)) $ x) of (v, b) \<Rightarrow> Phase2a x b v)) \<and> ae \<in> acceptors (lstate a ac) \<and> ae \<noteq> local_state.id (lstate a ac)"
    have "\<And>n p v. (case p of (v, na) \<Rightarrow> Phase2a n na v) \<noteq> (Fwd v::('a, 'v) msg)"
      by (metis amp_r3.msg.distinct(17) case_prod_conv surj_pair)
    then show "v \<in> b"
      using a1 by metis
  qed
   apply(simp add: do_2a_def receive_fwd_def Let_def send_all_def split:if_splits option.splits)
  apply(simp add: do_2a_def propose_def Let_def send_all_def split:if_splits option.splits)
  done

end

section {* A second attempt *}
  
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
        ampr1_state.ballot := \<lambda> a . local_state.ballot (lstate s' a),
        suggestion := \<lambda> i b . case (log (lstate s' (leader b)) $ i) of Proposed v \<Rightarrow> (
              case (log (lstate s (leader b)) $ i) of Free \<Rightarrow> Some v | _ \<Rightarrow> suggestion h i b)
          | Decided v \<Rightarrow> suggestion h i b
          | Free \<Rightarrow> None,
        onebs := \<lambda> a b . if local_state.ballot (lstate s' a) = b \<and> local_state.ballot (lstate s' a) \<noteq> b
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
    fix a :: "('a, 'v) global_state" and b :: "('v, 'a, ?'l) ampr1_state" and ac :: 'a and bb :: nat and vs :: "nat \<Rightarrow>f ('v \<times> nat) option" and ad :: "('a, 'v) local_state" and bc :: "('a, 'v) packet set" and ae :: 'a and v :: 'v
    assume a1: "(\<exists>x. finfun_dom (receive_1b.new_log (the (local_state.onebs (lstate a ac) $ bb)) (acceptors (lstate a ac)) (log (lstate a ac))) $ x \<and> (Fwd v::('a, 'v) msg) = (case the_elem (receive_1b.max_per_inst (the (local_state.onebs (lstate a ac) $ bb)) (acceptors (lstate a ac)) $ x) of (v, b) \<Rightarrow> Phase2a x b v)) \<and> ae \<in> acceptors (lstate a ac) \<and> ae \<noteq> local_state.id (lstate a ac)"
    have "\<And>n p v. (case p of (v, na) \<Rightarrow> Phase2a n na v) \<noteq> (Fwd v::('a, 'v) msg)"
      by (metis amp_r3.msg.distinct(17) case_prod_conv surj_pair)
    then show "v \<in> propCmd b"
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
  subgoal proof (cases "id (lstate s a) = leader (local_state.ballot (lstate s a))")
    case False
    with prems(3,5,6) have "update_hist s h act s' = h" apply (simp add:update_hist_def receive_fwd_def)
    thm prems
    oops
    
end

section {* A third attempt *}
  
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
  \<and> ballot t = (\<lambda> a . local_state.ballot (lstate s a))
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
      subgoal proof (cases "leader (local_state.ballot (lstate s a)) = local_state.id (lstate s a)")
        case False
        with prems(1,4) show ?thesis by (simp add:propose_def send_all_def fwd_sim_def propCmd_def)
      next
        case True thm prems
        have 1:"\<And> a . local_state.ballot (lstate t a) = ballot s' a" using prems(1,4) True 
          by (simp add:do_2a_def propose_def send_all_def fwd_sim_def Let_def propCmd_def)
        have 2:"network t = network s \<union> {Packet a2 (Phase2a (next_inst (lstate s a)) (local_state.ballot (lstate s a)) v) 
            | a2 . a2 \<noteq> a \<and> a2 \<in> acceptors (lstate s a)}"
          using prems(4,2) True
          by (fastforce simp add:do_2a_def propose_def send_all_def fwd_sim_def propCmd_def Let_def inv1_def)
        show ?thesis using 1 2 prems(1,2) apply (auto simp add:sim_defs inv1_def split!:msg.splits packet.splits)
              apply (metis ref_proof_3.axioms(2) ref_proof_3_axioms ref_proof_3_axioms_def)
             apply meson defer
          apply meson oops
end

section {* A fourth attempt *}
  
locale ref_proof_4 = quorums quorums + amp_r3 leader next_bal as quorums
  + r1:ampr1_ioa quorums leader
  for quorums :: "('a::linorder) set set" and leader :: "bal \<Rightarrow> ('a::linorder)" and next_bal as + 
  fixes ampr3_ioa :: "(('a, 'v) global_state, 'v paxos_action) ioa" 
    and ampr1_ioa :: "(('v, 'a, 'l) ampr1_state, 'v paxos_action) ioa" 
  defines "ampr3_ioa \<equiv> ioa" and "ampr1_ioa \<equiv> r1.ioa"
  fixes a1 a2 a3
  assumes "a1 \<in> as" and "a2 \<in> as" and "a3 \<in> as" and "a1 \<noteq> a2" and "a3 \<noteq> a2" and "a3 \<noteq> a1"
  (* assumes a_inf:"\<not> finite (UNIV::'a set)" *)
begin

interpretation IOA .

lemmas action_defs = propose_def do_2a_def receive_2b_def
      try_acquire_leadership_def receive_1a_def receive_2a_def receive_1b_def receive_fwd_def
  send_all_def Let_def

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

definition inv2 where inv2_def:
  "inv2 s \<equiv> \<forall> i b v a . Packet a (Phase2a i b v) \<in> network s 
    \<longrightarrow> log (lstate s (leader b)) $ i = Free"
lemma inv2:"invariant ampr3_ioa inv2"
  apply (rule invariantI)
   apply (simp add:inv2_def init_defs)
  apply (insert invs)
  apply (instantiate_invs)
  apply (rm_reachable)
  apply trans_cases
         apply (simp_all add:inv2_def inv1_def action_defs split!:if_splits) 
  oops
  
definition inv3 where 
  "inv3 s \<equiv> \<forall> i a b d1 v1 d2 v2 . 
    Packet d1 (Phase2b a i b v1) \<in> network s \<and> Packet d2 (Phase2b a i b v2) \<in> network s
    \<longrightarrow> v1 = v2 \<and> d1 = d2"
lemma inv2:"invariant ampr3_ioa inv2"
  apply (rule invariantI)
   apply (simp add:inv2_def init_defs)
  apply (insert invs)
  apply (instantiate_invs)
  apply (rm_reachable)
  apply trans_cases
  oops

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
  -- {* Could be @{term "{ff $ i \<bind> (Some o fst) | i . True} \<bind> option_as_set" }*}
| "extract_vs _ = {}"
  
definition propCmd where "propCmd s \<equiv> \<Union> ((\<lambda> p . case p of Packet _ m \<Rightarrow> extract_vs m) ` network s)"

definition ref_map where "ref_map s \<equiv> \<lparr>
  ampr1_state.propCmd = propCmd s,
  ballot = \<lambda> a . local_state.ballot (lstate s a),
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
      subgoal proof (cases "leader (local_state.ballot (lstate s a)) = local_state.id (lstate s a)")
        case False
        with prems(1,4) show ?thesis by (simp add:propose_def send_all_def fwd_sim_def propCmd_def)
      next
        case True thm prems
        have 1:"\<And> a . local_state.ballot (lstate t a) = ballot s' a" using prems(1,4) True 
          by (simp add:do_2a_def propose_def send_all_def fwd_sim_def Let_def propCmd_def)
        have 2:"network t = network s \<union> {Packet a2 (Phase2a (next_inst (lstate s a)) (local_state.ballot (lstate s a)) v) 
            | a2 . a2 \<noteq> a \<and> a2 \<in> acceptors (lstate s a)}"
          using prems(4,2) True
          by (fastforce simp add:do_2a_def propose_def send_all_def fwd_sim_def propCmd_def Let_def inv1_def)
        show ?thesis using 1 2 prems(1,2) apply (auto simp add:sim_defs inv1_def split!:msg.splits packet.splits)
              apply (metis ref_proof_3.axioms(2) ref_proof_3_axioms ref_proof_3_axioms_def)
             apply meson defer
          apply meson oops
end

end