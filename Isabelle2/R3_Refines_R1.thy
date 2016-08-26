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
  apply (simp add:ghost_ioa_def)
  apply(simp only: split_paired_all)
  apply (rule IOA.add_hist_trans)
  

definition ref_map where "ref_map s \<equiv> \<lparr>
  ampr1_state.propCmd = propCmd s,
  ampr1_state.ballot = ballot s,
  ampr1_state.vote = (\<lambda> i a . vote s $ a $ i),
  ampr1_state.suggestion = suggestion s,
  ampr1_state.onebs = onebs s,
  ampr1_state.leader = ampr2_state.leader s\<rparr>"

end