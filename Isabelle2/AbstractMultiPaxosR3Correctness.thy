theory AbstractMultiPaxosR3Correctness
imports AbstractMultiPaxosR1 AbstractMultiPaxosR3 "../../IO-Automata/Simulations"
begin

locale ampr2_proof = IOA + quorums quorums + ampr2_ioa quorums for
     quorums :: "'a set set" +
  fixes ampr2_ioa :: "(('v,'a,'l)ampr2_state, ('v,'a,'l)ampr1.amp_action) ioa"
  and ampr1_ioa :: "(('v,'a,'l)amp_state, ('v,'a,'l)ampr1.amp_action) ioa"
  defines "ampr2_ioa \<equiv> ioa" and "ampr1_ioa \<equiv> ampr1.amp_ioa"
begin

definition ref_map :: "('v,'a,'l)ampr2_state \<Rightarrow> ('v,'a,'l)amp_state" where 
  "ref_map s \<equiv> \<lparr> amp_state.propCmd = (propCmd s),
  ballot = (\<lambda>a. ((ballot s) $ a)),
  vote = (\<lambda>a i b. (vote s $ a $ i $ b)),
  suggestion = (\<lambda>i b. ((suggestion s i) $ b)),
  onebs = (\<lambda>a b. if (onebs s $ a $ b) = None then None else (Some (\<lambda>i. (the (onebs s $ a $ b)) $ i))),
  learned = (\<lambda>l i. (learned s $ l $ i)),
  leader = (\<lambda>a. (ampr2_state.leader s $ a)) \<rparr>"

term "ampr1_ioa"
term "ampr2_ioa"

lemma aux_proof:"(op $ (K$ False)(leading b $:= True)) = (\<lambda> a . leading b = a)"
proof
  fix a
  have "(K$  False)(leading b $:= True) $ a = (leading b = a)"
  proof(cases "leading b = a")
    case True
      thus ?thesis by (simp add: finfun_upd_apply_same)
  next
    case False
      thus ?thesis by (simp add: finfun_upd_apply)
  qed
  thus "\<And>a. (K$  False)(leading b $:= True) $ a = (leading b = a)" by (simp add: finfun_upd_apply)
qed

lemma aux_proof1:"\<And>l i v b q. \<lbrakk>q \<in> quorums; \<forall>a \<in> q. ampr2_state.vote s $ a $ i $ b = Some v\<rbrakk> \<Longrightarrow>
    (\<lambda>la. op $ ((ampr2_state.learned s)(l $:= (ampr2_state.learned s $ l)(i $:= Some v)) $ la)) = 
      (\<lambda>l. op $ (ampr2_state.learned s $ l))(l := op $ (ampr2_state.learned s $ l) (i \<mapsto> v))"
proof
  fix l i v b q la
  assume 0:"q \<in> quorums" and 1:"\<forall>a \<in> q. ampr2_state.vote s $ a $ i $ b = Some v"
  let ?t = "op $ ((ampr2_state.learned s)(l $:= (ampr2_state.learned  s $ l)(i $:= Some v)) $ la) =
    ((\<lambda>l. op $ (ampr2_state.learned s $ l)) (l := op $ (ampr2_state.learned s $ l) (i \<mapsto> v))) la"
  have ?t
  proof(cases ?t)
    case True
      thus ?thesis by metis
  next
    case False
      thus ?thesis by (metis (no_types, lifting) finfun_update.rep_eq fun_upd_def)
  qed
  thus ?t by blast
qed

lemma aux_proof2:"\<lbrakk>b = ampr2_state.ballot s $ a; ampr2_state.suggestion s i $ b = None\<rbrakk> \<Longrightarrow>
  (\<lambda>ia. op $ (if ia = i then (ampr2_state.suggestion s i)(b $:= Some v) else ampr2_state.suggestion s ia)) =
    (\<lambda>i. op $ (ampr2_state.suggestion s i))(i := op $ (ampr2_state.suggestion s i) (b \<mapsto> v))"
proof
  fix ia
  assume "b = ampr2_state.ballot s $ a" and "ampr2_state.suggestion s i $ b = None"
  let ?t = "op $ (if ia = i then (ampr2_state.suggestion s i)(b $:= Some v) else ampr2_state.suggestion s ia) =
    ((\<lambda>i. op $ (ampr2_state.suggestion s i))(i := op $ (ampr2_state.suggestion s i)(b \<mapsto> v))) ia"
  have ?t
  proof(cases ?t)
    case True
      thus ?thesis by metis
  next
    case False
      thus ?thesis by (smt finfun_update.rep_eq fun_upd_apply)
  qed
  thus ?t by blast
qed

lemma aux_proof3:"(\<lambda>l. op $ ((ampr2_state.learned s)(l1 $:= (ampr2_state.learned s $ l1)(i $:= Some v)) $ l)) =
  (\<lambda>l. op $ (ampr2_state.learned s $ l))(l1 := op $ (ampr2_state.learned s $ l1)(i \<mapsto> v))"
proof
  fix l
  let ?t = "op $ ((ampr2_state.learned s)(l1 $:= (ampr2_state.learned s $ l1)(i $:= Some v)) $ l) =
    ((\<lambda>l. op $ (ampr2_state.learned s $ l))(l1 := op $ (ampr2_state.learned s $ l1)(i \<mapsto> v))) l"
  have ?t
  proof(cases ?t)
    case True
      thus ?thesis by blast
  next
    case False
      thus ?thesis by auto
  qed
  thus "\<And>l. ?t" by blast
qed
  
lemma aux_proof4:"\<And>c. (\<lambda>a b. if ampr2_state.onebs s $ a $ b = None then None
  else Some (op $ (the (ampr2_state.onebs (s\<lparr>ampr2_state.propCmd := insert c (ampr2_state.propCmd s)\<rparr>) $ a $ b)))) = 
    (\<lambda>a b. if ampr2_state.onebs s $ a $ b = None then None else Some (op $  (the (ampr2_state.onebs s $ a $  b))))"
sorry

lemma "is_ref_map ref_map ampr2_ioa ampr1_ioa"
proof (auto simp add:is_ref_map_def simp del:split_paired_Ex)
  fix s
  assume "s \<in> ioa.start ampr2_ioa"
  thus "ref_map s \<in> ioa.start ampr1_ioa" 
    by (simp add:ref_map_def ampr2_ioa_def ampr1_ioa_def ioa_def start_def ampr1.simps aux_proof)
next
  fix s t a
  assume a1:"reachable ampr2_ioa s" and a2:"s \<midarrow>a\<midarrow>ampr2_ioa\<longrightarrow> t"
  let ?e = "(ref_map s, [(a, ref_map t)])"
  have "refines ?e s a t ampr1_ioa ref_map"
  proof (auto simp add:refines_def ioa_simps trace_match_def trace_def schedule_def filter_act_def)
    show "(ref_map s, a, ref_map t) \<in> ioa.trans ampr1_ioa" using a2
    apply (simp add:ampr2_ioa_def ioa_def is_trans_def trans_def)
    apply (simp add:ampr1_ioa_def ampr1.amp_ioa_def ampr1.amp_trans_def)
    apply (induct rule:trans_cases_2)
    (* propose *)
    apply (simp add:simps ampr1.simps ref_map_def aux_proof4)
    (* learn *)
    apply (simp add:simps ampr1.simps ref_map_def ballot_array.chosen_def ballot_array.chosen_at_def)
    
    (* join_ballot *)
    apply (induct a) apply auto[2]
    subgoal premises prems for a b
    proof -
      have "ampr1.join_ballot a b (ref_map s) (ref_map t)" using prems
        by (auto simp add:ref_map_def simps Let_def ampr1.simps fun_eq_iff)
      thus ?thesis by auto
    qed
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
      have "ampr1.suggest a i b v (ref_map s) (ref_map t)" using prems(1)
        by (auto simp add:suggest_def ampr1.suggest_def ref_map_def aux_proof2)
      thus ?thesis by auto
    qed
    (* catch_up *)
    apply (induct a) apply auto[2] 
    subgoal premises prems for l1 l2 i v
    proof -
      have "ampr1.catch_up l1 l2 i v (ref_map s) (ref_map t)" using prems
        by (auto simp add:catch_up_def ampr1.catch_up_def ref_map_def aux_proof3)
      thus ?thesis by auto
    qed
    (* acquire_leadership *)
    apply (induct a) apply auto[2] 
    subgoal premises prems for aa q
    proof -
      have "ampr1.acquire_leadership aa q (ref_map s) (ref_map t)" using prems
        apply (auto simp add:acquire_leadership_def ampr1.acquire_leadership_def ref_map_def)
        by (auto simp add:simps Let_def ampr1.simps fun_eq_iff)
      thus ?thesis by auto
    qed
    done 
    qed
  thus "\<exists> e . refines e s a t ampr1_ioa ref_map" by blast
qed

end