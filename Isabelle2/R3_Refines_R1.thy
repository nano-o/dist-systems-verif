theory R3_Refines_R1   
imports AbstractMultiPaxosR3 AbstractMultiPaxosR1 Simulations Hist_Supplemental IOA_Automation
begin

locale ref_proof = quorums quorums + amp_r3 leader next_bal as quorums 
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
    assume a1: "(\<exists>x. finfun_dom (receive_1b.new_log (the (local_state.onebs (local_states a ac) $ bb)) (acceptors (local_states a ac)) (log (local_states a ac))) $ x \<and> (Fwd v::('a, 'v) msg) = (case the_elem (receive_1b.max_per_inst (the (local_state.onebs (local_states a ac) $ bb)) (acceptors (local_states a ac)) $ x) of (v, b) \<Rightarrow> Phase2a x b v)) \<and> ae \<in> acceptors (local_states a ac) \<and> ae \<noteq> local_state.id (local_states a ac)"
    have "\<And>n p v. (case p of (v, na) \<Rightarrow> Phase2a n na v) \<noteq> (Fwd v::('a, 'v) msg)"
      by (metis amp_r3.msg.distinct(17) case_prod_conv surj_pair)
    then show "v \<in> b"
      using a1 by metis
  qed
   apply(simp add: do_2a_def receive_fwd_def Let_def send_all_def split:if_splits option.splits)
  apply(simp add: do_2a_def propose_def Let_def send_all_def split:if_splits option.splits)
  done

text {*
TODO: what about letting the ghost state be exactly the state of r1?
That would give a very simple refinement map, but we will need to prove invariants
relating the normal state to the ghost state.
*}

definition ref_map where "ref_map s \<equiv> let r3_s = fst s; ghost_s = snd s in \<lparr>
  ampr1_state.propCmd = ghost_s,
  ampr1_state.ballot = (\<lambda> a . local_state.ballot (local_states r3_s a)),
  ampr1_state.vote = undefined,
  ampr1_state.suggestion = undefined,
  ampr1_state.onebs = undefined,
  ampr1_state.leader = undefined\<rparr>"
  
lemma "is_ref_map ref_map ghost_ioa ampr1_ioa" 
oops
  
end

end