theory AbstractMultiPaxosR3Correctness
imports AbstractMultiPaxosR1 AbstractMultiPaxosR3 Simulations
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
  suggestion = (\<lambda>i b. ((suggestion s $ i) $ b)),
  onebs = (\<lambda>a b. if (onebs s $ a $ b) = None then None else (Some (\<lambda>i. (the (onebs s $ a $ b)) $ i))),
  learned = (\<lambda>l i. (learned s $ l $ i)),
  leader = (\<lambda>a. (ampr2_state.leader s $ a)) \<rparr>"

term "ampr1_ioa"
term "ampr2_ioa"

lemma aux_proof:"(op $ (K$ False)(leading b $:= True)) = (\<lambda> a . leading b = a)"
proof
  fix a
  let ?t = "(K$ False)(leading b $:= True) $ a = (leading b = a)"
  have ?t
  proof(cases "leading b = a")
    case True
      thus ?thesis by (simp add: finfun_upd_apply_same)
  next
    case False
      thus ?thesis by (simp add: finfun_upd_apply)
  qed
  thus "\<And>a. ?t" by (simp add: finfun_upd_apply)
qed
 
subsection {* auxiliary lemmas for propose definition. *} 
lemma aux_proof_propose:"\<And>c. (\<lambda>a b. if ampr2_state.onebs s $ a $ b = None then None
  else Some (op $ (the (ampr2_state.onebs (s\<lparr>ampr2_state.propCmd := insert c (ampr2_state.propCmd s)\<rparr>) $ a $ b)))) = 
    (\<lambda>a b. if ampr2_state.onebs s $ a $ b = None then None else Some (op $ (the (ampr2_state.onebs s $ a $ b))))"
proof
  fix c a
  let ?t = "(\<lambda>b. if ampr2_state.onebs s $ a $ b = None then None
    else Some (op $ (the (ampr2_state.onebs (s\<lparr>ampr2_state.propCmd := insert c (ampr2_state.propCmd s)\<rparr>) $ a $  b)))) =
      (\<lambda>b. if ampr2_state.onebs s $ a $ b = None then None else Some (op $ (the (ampr2_state.onebs s $ a $ b))))"
  have ?t
  proof-
    {
      assume 0:"\<not>?t"
      hence "False" by auto
    }
    thus ?t by blast
  qed
  thus "\<And>c a. ?t" by blast
qed

subsection {* auxiliary lemmas for learn definition. *}

lemma aux_proof_learn:"\<And>l i v. (\<lambda>a b. if ampr2_state.onebs s $ a $ b = None then None 
  else Some (op $ (the (ampr2_state.onebs (s\<lparr>ampr2_state.learned := (ampr2_state.learned s)(l $:= (ampr2_state.learned s $ l)(i $:= Some v))\<rparr>) $ a $ b)))) 
   = (\<lambda>a b.  if ampr2_state.onebs s $ a $ b = None then None else Some (op $ (the (ampr2_state.onebs s $ a $ b)))) 
  \<and> (\<lambda>la. op $ ((ampr2_state.learned s)(l $:= (ampr2_state.learned s $ l)(i $:= Some v)) $ la)) =
    (\<lambda>l. op $ (ampr2_state.learned s $ l))(l := op $ (ampr2_state.learned s $ l) (i \<mapsto> v))"
proof-
  fix l i v
  let ?t1 = "(\<lambda>a b. if ampr2_state.onebs s $ a $ b = None then None 
    else Some (op $ (the (ampr2_state.onebs (s\<lparr>ampr2_state.learned := (ampr2_state.learned s)(l $:= (ampr2_state.learned s $ l)(i $:= Some v))\<rparr>) $ a $ b)))) 
    = (\<lambda>a b.  if ampr2_state.onebs s $ a $ b = None then None else Some (op $ (the (ampr2_state.onebs s $ a $ b))))"
  let ?t2 = "(\<lambda>la. op $ ((ampr2_state.learned s)(l $:= (ampr2_state.learned s $ l)(i $:= Some v)) $ la)) =
    (\<lambda>l. op $ (ampr2_state.learned s $ l))(l := op $ (ampr2_state.learned s $ l) (i \<mapsto> v))"
  have 1:?t1
  proof-
    {
      assume 0:"\<not>?t1"
      hence "False" by force
    }
    thus ?t1 by blast
  qed
  have ?t2
  proof-
    {
      assume 0:"\<not>?t2"
      hence "False" by force
    }
    thus ?t2 by blast
  qed
  thus "\<And>l i v. ?t1 \<and> ?t2" using 1 by blast
qed

lemma aux_proof_learn1:"\<And>l i v. [b\<leftarrow>finfun_to_list (ampr2_state.suggestion s $ i) .
  Set.filter (\<lambda>q. Set.filter (\<lambda>a. ampr2_state.vote s $ a $ i $ b = Some v) q = q) quorums \<noteq> {}] \<noteq> [] \<Longrightarrow>
  \<exists>b q. q \<in> quorums \<and> (\<forall>a\<in>q. ampr2_state.vote s $ a $ i $ b = Some v)"
proof-
  fix l i v
  let ?prems = "[b\<leftarrow>finfun_to_list (ampr2_state.suggestion s $ i) .
    Set.filter (\<lambda>q. Set.filter (\<lambda>a. ampr2_state.vote s $ a $ i $ b = Some v) q = q) quorums \<noteq> {}] \<noteq> []"
  let ?conc = "\<exists>b q. q \<in> quorums \<and> (\<forall>a\<in>q. ampr2_state.vote s $ a $ i $ b = Some v)"
  assume 0:"[b\<leftarrow>finfun_to_list (ampr2_state.suggestion s $ i) .
    Set.filter (\<lambda>q. Set.filter (\<lambda>a. ampr2_state.vote s $ a $ i $ b = Some v) q = q) quorums \<noteq> {}] \<noteq> []"
  with this obtain b where 1:"Set.filter (\<lambda>q. Set.filter (\<lambda>a. ampr2_state.vote s $ a $ i $ b = Some v) q = q) quorums \<noteq> {}"
    by (meson filter_False)
  with this obtain q where 2:"q \<in> quorums" and 3:"Set.filter (\<lambda>a. ampr2_state.vote s $ a $ i $ b = Some v) q = q"
    using Collect_empty_eq Set.filter_def by fastforce
  hence "\<forall>a\<in>q. ampr2_state.vote s $ a $ i $ b = Some v" using member_filter by auto
  thus "\<And>l i v. ?prems \<Longrightarrow> ?conc" using 0 2 by blast
qed

subsection {* auxiliary lemmas for join_ballot definition. *}
lemma "acc_max voteimpl a b = distributed_safe_at.acc_max voteimpl a b"
unfolding acc_max_def distributed_safe_at.acc_max_def sorry

lemma aux_proof_join:"\<And>y xa. insts = (finfun_to_list (ampr2_state.vote s $ a)) \<Longrightarrow> 
  fold (\<lambda>i ob. ob(i $:= acc_max (\<lambda>a. op $ (ampr2_state.vote s $ a $ i)) a b)) insts y $ xa =
    distributed_safe_at.acc_max (\<lambda>a. op $ (ampr2_state.vote s $ a $ xa)) a b"
proof-
  fix y xa
  assume 0:"insts = (finfun_to_list (ampr2_state.vote s $ a))"
  let ?t = "fold (\<lambda>i ob. ob(i $:= acc_max (\<lambda>a. op $ (ampr2_state.vote s $ a $ i)) a b)) insts y $ xa =
    distributed_safe_at.acc_max (\<lambda>a. op $ (ampr2_state.vote s $ a $ xa)) a b"
  let ?t1 = "fold (\<lambda>i ob. ob(i $:= acc_max (\<lambda>a. op $ (ampr2_state.vote s $ a $ i)) a b)) insts y"
  have "\<forall>i \<in> set insts. ?t1 $ i = acc_max (\<lambda>a. op $ (ampr2_state.vote s $ a $ i)) a b" sorry
  have ?t
  proof(cases "xa \<in> set insts")
    case True
      thus ?thesis sorry
  next
    case False
      hence "ampr2_state.vote s $ a $ xa = (K$ None)" using 0 sorry
      thus ?thesis sorry
  qed
  thus "\<And>y xa. insts = (finfun_to_list (ampr2_state.vote s $ a)) \<Longrightarrow> ?t" by blast
qed

subsection {* auxiliary lemmas for catch_up definition. *}
lemma aux_proof_catchup:"(\<lambda>l. op $ ((ampr2_state.learned s)(l1 $:= (ampr2_state.learned s $ l1)(i $:= Some v)) $ l)) =
  (\<lambda>l. op $ (ampr2_state.learned s $ l))(l1 := op $ (ampr2_state.learned s $ l1)(i \<mapsto> v))"
proof
  fix l
  let ?t = "op $ ((ampr2_state.learned s)(l1 $:= (ampr2_state.learned s $ l1)(i $:= Some v)) $ l) =
    ((\<lambda>l. op $ (ampr2_state.learned s $ l))(l1 := op $ (ampr2_state.learned s $ l1)(i \<mapsto> v))) l"
  have ?t
  proof-
    {
      assume 0:"\<not>?t"
      hence "False" by auto
    }
    thus ?t by blast
  qed
  thus "\<And>l. ?t" by blast
qed

lemma aux_proof_catchup1:"(\<lambda>a b. if ampr2_state.onebs s $ a $ b = None then None else 
    Some (op $ (the (ampr2_state.onebs (s\<lparr>ampr2_state.learned := (ampr2_state.learned s)(l1 $:= (ampr2_state.learned s $ l1)(i $:= Some v))\<rparr>) $ a $ b)))) =
    (\<lambda>a b. if ampr2_state.onebs s $ a $ b = None then None else Some (op $ (the (ampr2_state.onebs s $ a $ b))))"
by (simp add: aux_proof_learn)

subsection {* auxiliary lemmas for leadership definition. *}
lemma aux_proof_leadership:"\<And>x. \<lbrakk>b = ampr2_state.ballot s $ aa; leading b = aa;
  q \<in> quorums; \<not> ampr2_state.leader s $ aa;  \<forall>a\<in>q. \<exists>y. ampr2_state.onebs s $ a $ b = Some y\<rbrakk> \<Longrightarrow>
  fold (\<lambda>i ss. ss(i $:= (ss $ i)(b $:= map_option fst (max_pair q (\<lambda>a. the (ampr2_state.onebs s $ a $ b) $ i)))))
    (finfun_to_list (the (ampr2_state.onebs s $ aa $ b))) (ampr2_state.suggestion s) $ x $ b =
  map_option fst (distributed_safe_at.max_pair q (\<lambda>a. the (if ampr2_state.onebs s $ a $ b = None
    then None else Some (op $ (the (ampr2_state.onebs s $ a $ b)))) x))" sorry

lemma aux_proof_leadership1:"\<And>x xa. \<lbrakk>b = ampr2_state.ballot s $ aa; leading b = aa; q \<in> quorums;
  \<not> ampr2_state.leader s $ aa; \<forall>a\<in>q. \<exists>y. ampr2_state.onebs s $ a $ b = Some y; xa \<noteq> b\<rbrakk> \<Longrightarrow>
  fold (\<lambda>i ss.  ss(i $:= (ss $ i)(b $:= map_option fst (max_pair q (\<lambda>a. the (ampr2_state.onebs s $ a $ b) $ i)))))
    (finfun_to_list (the (ampr2_state.onebs s $ aa $ b))) (ampr2_state.suggestion s) $ x $ xa =
  ampr2_state.suggestion s $ x $ xa" sorry

subsection {* lemma for refinement relationship between ampr1_ioa and ampr2_ioa. *}
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
    apply (simp add:simps ampr1.simps ref_map_def aux_proof_propose)
    (* learn *)
    apply (simp add:simps ampr1.simps ref_map_def ballot_array.chosen_def ballot_array.chosen_at_def)
    apply (simp add:aux_proof_learn aux_proof_learn1)
    (* join_ballot *)
    apply (induct a) apply auto[2]
    subgoal premises prems for a b
    proof -
      have "ampr1.join_ballot a b (ref_map s) (ref_map t)" using prems
        apply (auto simp add:join_ballot_def ampr1.join_ballot_def ref_map_def)
        by (auto simp add:ref_map_def simps Let_def ampr1.simps fun_eq_iff aux_proof_join)
      thus ?thesis by auto
    qed
    (* do_vote *)
    apply (induct a) apply auto[2] 
    subgoal premises prems for a i v
    proof -
      have "ampr1.do_vote a i v (ref_map s) (ref_map t)" using prems
        by (auto simp add:ref_map_def simps Let_def ampr1.simps fun_eq_iff )
      thus ?thesis by auto
    qed
    (* suggest *)
    apply (induct a) apply auto[2] 
    subgoal premises prems for a i b v
    proof -
      have "ampr1.suggest a i b v (ref_map s) (ref_map t)" using prems(1)
        apply (auto simp add:suggest_def ampr1.suggest_def ref_map_def) 
        by (auto simp add:simps Let_def ampr1.simps fun_eq_iff)
      thus ?thesis by auto
    qed
    (* catch_up *)
    apply (induct a) apply auto[2] 
    subgoal premises prems for l1 l2 i v
    proof -
      have "ampr1.catch_up l1 l2 i v (ref_map s) (ref_map t)" using prems
        by (auto simp add:catch_up_def ampr1.catch_up_def ref_map_def aux_proof_catchup aux_proof_catchup1)
      thus ?thesis by auto
    qed
    (* acquire_leadership *)
    apply (induct a) apply auto[2] 
    subgoal premises prems for aa q
    proof -
      have "ampr1.acquire_leadership aa q (ref_map s) (ref_map t)" using prems
        apply (auto simp add:acquire_leadership_def ampr1.acquire_leadership_def ref_map_def)
        apply (auto simp add:simps Let_def ampr1.simps fun_eq_iff)
        apply (simp add:aux_proof_leadership)
        using aux_proof_leadership1 by blast
      thus ?thesis by auto
    qed
    done 
    qed
  thus "\<exists> e . refines e s a t ampr1_ioa ref_map" by blast
qed

end