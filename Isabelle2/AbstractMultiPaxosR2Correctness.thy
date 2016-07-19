theory AbstractMultiPaxosR2Correctness
imports AbstractMultiPaxosR1 AbstractMultiPaxosR2 Simulations
begin

print_locale ampr2_ioa

locale ampr2_proof = IOA + quorums quorums + ampr2_ioa quorums for
     quorums :: "'a set set" +
  fixes ampr2_ioa :: "(('v,'a,'l)ampr2_state, ('v,'a,'l)ampr1.action) ioa"
  and ampr1_ioa :: "(('v,'a,'l)ampr1_state, ('v,'a,'l)ampr1.action) ioa"
  defines "ampr2_ioa \<equiv> ioa" and "ampr1_ioa \<equiv> ampr1.ioa"
begin

definition ref_map where "ref_map s \<equiv> \<lparr>
  ampr1_state.propCmd = propCmd s,
  ampr1_state.ballot = ballot s,
  ampr1_state.vote = (\<lambda> i a . vote s a i),
  ampr1_state.suggestion = suggestion s,
  ampr1_state.onebs = onebs s,
  ampr1_state.learned = learned s,
  ampr1_state.leader = ampr2_state.leader s\<rparr>"

term "ampr1_ioa"
term "ampr2_ioa"

lemma "is_ref_map ref_map ampr2_ioa ampr1_ioa"
proof (auto simp add:is_ref_map_def simp del:split_paired_Ex)
  fix s
  assume "s \<in> ioa.start ampr2_ioa"
  thus "ref_map s \<in> ioa.start ampr1_ioa" 
    by (simp add:ref_map_def ampr1.simps ampr2_ioa_def ampr1_ioa_def ioa_def start_def)
next
  fix s t a
  assume a1:"reachable ampr2_ioa s" and a2:"s \<midarrow>a\<midarrow>ampr2_ioa\<longrightarrow> t"
  let ?e = "(ref_map s, [(a, ref_map t)])"
  have "refines ?e s a t ampr1_ioa ref_map"
  proof (auto simp add:refines_def ioa_simps trace_match_def trace_def schedule_def filter_act_def)
    show "(ref_map s, a, ref_map t) \<in> ioa.trans ampr1_ioa" using a2
    apply (simp add:ampr2_ioa_def ioa_def is_trans_def trans_def)
    apply (simp add:ampr1_ioa_def ampr1.ioa_def ampr1.trans_def)
    apply (induct rule:trans_cases_2)
    apply (simp_all add:simps ampr1.simps ref_map_def)[2]
    (* join_ballot *)
    apply (induct a) apply auto[2]
    apply (auto simp add:ref_map_def ampr1.simps simps)[1]
    (* do_vote *)
    apply (induct a) apply auto[2] 
    subgoal premises prems for a i v
    proof -
      have "ampr1.do_vote a i v (ref_map s) (ref_map t)" using prems
        by (auto simp add:ref_map_def simps Let_def ampr1.simps fun_eq_iff)
      thus ?thesis by auto
    qed
    (* suggest *)
    apply (induct a) apply auto[2] 
    subgoal premises prems for a i b v
    proof -
      have "ampr1.suggest a i b v (ref_map s) (ref_map t)" using prems
        by (auto simp add:ref_map_def simps Let_def ampr1.simps fun_eq_iff)
      thus ?thesis by auto
    qed
    (* catch_up *)
    apply (induct a) apply auto[2] 
    subgoal premises prems for l1 l2 i v
    proof -
      have "ampr1.catch_up l1 l2 i v (ref_map s) (ref_map t)" using prems
        by (auto simp add:ref_map_def simps Let_def ampr1.simps fun_eq_iff)
      thus ?thesis by auto
    qed
    (* acquire_leadership *)
    apply (induct a) apply auto[2] 
    subgoal premises prems for aa q
    proof -
      have "ampr1.acquire_leadership aa q (ref_map s) (ref_map t)" using prems
        by (auto simp add:ref_map_def simps Let_def ampr1.simps fun_eq_iff)
      thus ?thesis by auto
    qed
    done 
    qed
  thus "\<exists> e . refines e s a t ampr1_ioa ref_map" by blast
qed

end