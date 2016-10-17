section {* Proof of the agreement property of AbstractMultiPaxosWithRecovery. *}

theory AbstractMultiPaxosWithRecoveryCorrectness
imports AbstractMultiPaxosWithRecovery "~~/src/HOL/Eisbach/Eisbach_Tools" BallotArrayProperties 
begin

text {* Guidelines:
  If a state function depends on only part of the state, make this clear by passing it only that part.
  To maintain reactivity, set a number of threads greater than the number of background tools that can be started.
  *}

text {* Ideas: 
  In the abstract ballot-array model, the asynchronous combination of immutable state (or binary monotonic, acting on the last value) can be done atomically.
  What examples like the monotonicity of choosable? *}

nitpick_params [verbose, timeout = 60, finitize nat, dont_box]

locale amp_proof = quorums quorums + ampr_ioa quorums for quorums :: "'a set set" +
  fixes the_ioa :: "(('v, 'a) ampr_state, ('a, 'v) paxos_action) ioa"
  defines "the_ioa \<equiv> ioa"
  -- {* Here we have to fix the constant @{term the_ioa} in order to fix all type variables.
  Otherwise, there are problems in Eisbach when matching the same polymorphic constant appearing in several terms. *}
begin

interpretation IOA .

subsection {* Automation setup *}

lemmas ioa_defs =
   is_trans_def actions_def trans_def start_def
   externals_def ioa_def the_ioa_def paxos_asig_def

named_theorems inv_defs

named_theorems invs
  -- "named theorem for use by the tactics below"

declare propose_def[simp] join_ballot_def[simp] do_vote_def[simp] crash_def[simp]
  learn_def[simp] Let_def[simp] if_split[split] if_split_asm[split]

method rm_trans_rel_assm = 
  (match premises in P[thin]:"trans_rel ?x ?y ?z" \<Rightarrow> \<open>-\<close>)

lemma is_trans_simp[simp]:
  "s \<midarrow>a\<midarrow>the_ioa\<longrightarrow> t = trans_rel s a t"
  by (simp add:is_trans_def the_ioa_def ioa_def trans_def)
  
method my_fail for msg::"char list" = (print_term msg; fail)

method rm_reachable = (match premises in R[thin]:"reachable ?ioa ?s" \<Rightarrow> \<open>-\<close>)

lemma reach_and_inv_imp_p:"\<lbrakk>reachable the_ioa s; invariant the_ioa i\<rbrakk> \<Longrightarrow> i s"
  by (auto simp add:invariant_def)

method instantiate_invs declares invs =
  (match premises in I[thin]:"invariant ?ioa ?inv" and R:"reachable ?ioa ?s" \<Rightarrow> \<open>
    print_fact I, insert reach_and_inv_imp_p[OF R I]\<close>)+

method instantiate_invs_2 declares invs = (
  (* Deduce that all invariants hold in s *)
  ( insert invs,
    instantiate_invs )?,
  (* Deduce that all invariants hold in t (first deduce that t is reachable) *)
  match premises in R[thin]:"reachable ?ioa ?s" and T:"?s \<midarrow>?a\<midarrow>?ioa\<longrightarrow> ?t" \<Rightarrow> 
    \<open>insert reachable_n[OF R T]\<close>,
  ( insert invs,
    instantiate_invs )?,
  (* Get rid of the reachability assumption *)
  rm_reachable )

text {* If any of m1, m2, or m3 fail, then the whole method fails. *}
method inv_cases methods m1 m2 m3 uses invs declares inv_defs =
  (rule invariantI; (
      ((match premises in "?s \<in> ioa.start ?ioa" \<Rightarrow> \<open>-\<close>); m1 )
    | ((instantiate_invs_2 invs:invs | my_fail "''instantiation failed''");
        (m2 | my_fail "''method 2 failed''"); simp only:is_trans_simp;
          ((induct_tac rule:trans_cases | my_fail "''case analysis failed''"), simp?); rm_trans_rel_assm; m3)
        ) )

method force_inv uses invs declares inv_defs =
  inv_cases \<open>(force simp add:inv_defs ioa_defs)?\<close> \<open>-\<close> \<open>(force simp add:inv_defs split:option.splits)?\<close>
  invs:invs inv_defs:inv_defs

method simp_inv uses invs declares inv_defs =
  inv_cases \<open>simp add:inv_defs ioa_defs\<close> \<open>-\<close> \<open>(simp add:inv_defs split:option.splits; fail)?\<close>
  invs:invs inv_defs:inv_defs

method auto_inv uses invs declares inv_defs =
  inv_cases \<open>auto simp add:inv_defs ioa_defs\<close> \<open>-\<close> \<open>(auto simp add:inv_defs split:option.splits; fail)?\<close>
  invs:invs inv_defs:inv_defs
  
subsection {* finiteness lemmas. *}

context begin

definition learned_instances where 
  "learned_instances l \<equiv> {i . \<exists> a . l a i \<noteq> None}"
  
definition learned_instances_finite where learned_instances_finite_def[inv_defs]:
  "learned_instances_finite s \<equiv> finite (learned_instances (log s))"

lemma learned_instances_finite:"invariant the_ioa learned_instances_finite"
  apply (simp_inv inv_defs:learned_instances_def)
  subgoal premises prems for s t _ a i vs 
  proof -
    from prems(1) obtain j where "log s a k = None" if "k > j" for a k
      unfolding learned_instances_def learned_instances_finite_def using that
      by (metis (mono_tags, lifting) finite_nat_set_iff_bounded mem_Collect_eq not_less_iff_gr_or_eq)
    hence "\<And> k a . \<lbrakk>k > max (i + length vs) j\<rbrakk> \<Longrightarrow>  log t a k = None" using \<open>learn a i vs s t\<close>
      by (cases s, cases t, auto)
    thus ?thesis unfolding learned_instances_def learned_instances_finite_def
    proof -
      assume a1: "\<And>k a. max (i + length vs) j < k \<Longrightarrow> log t a k = None"
      obtain nn :: "nat set \<Rightarrow> nat \<Rightarrow> nat" where
        f2: "\<And>N n. (finite N \<or> nn N n \<in> N) \<and> (\<not> nn N n \<le> n \<or> finite N)"
        by (metis (full_types, lifting) finite_nat_set_iff_bounded_le)
      moreover
      { assume "\<exists>n. \<forall>a. log t a (nn {n. \<exists>a. log t a n \<noteq> None} n) = None"
        then have "\<exists>n. nn {n. \<exists>a. log t a n \<noteq> None} n \<notin> {n. \<exists>a. log t a n \<noteq> None}"
          by simp
        then have "finite {n. \<exists>a. log t a n \<noteq> None}"
          using f2 by blast }
      ultimately show "finite {n. \<exists>a. log t a n \<noteq> None}"
        using a1 by (meson not_le)
    qed 
  qed
  subgoal premises prems for s t _ a
  proof -
    from prems(1) obtain j where "log s a k = None" if "k > j" for a k
      unfolding learned_instances_def learned_instances_finite_def using that
      by (metis (mono_tags, lifting) finite_nat_set_iff_bounded mem_Collect_eq not_less_iff_gr_or_eq)
    moreover
    from \<open>crash a s t\<close> have "\<exists> a . log s a i = Some v" if "log t a i = Some v" for a i v
      using that by (cases s, cases t, auto)
    ultimately have  "i \<le> j" if "log t a i = Some v" for a i v
      by (metis leI option.distinct(1) that)
    thus ?thesis unfolding learned_instances_def learned_instances_finite_def
      using finite_nat_set_iff_bounded_le by auto 
  qed
  done

private definition instance_bound_bound where "instance_bound_bound l \<equiv> 
  if learned_instances l \<noteq> {} then Max (learned_instances l) + lookahead + 1 else lookahead"
  
private lemma l1: "learned_by_one (log s) q \<subseteq> learned_instances (log s)"
  by (auto simp add:learned_by_one_def learned_instances_def)
  
private  lemma l2:
  "learned_by_quorum_consec (log s) \<subseteq> learned_instances (log s)"
  apply (auto simp add:learned_by_quorum_consec_def learned_instances_def is_learned_by_set_def)
  by (meson Int_emptyI order_refl quorums_axioms quorums_def)

private lemma l3:
  assumes "finite (learned_instances (log s))" and "finite (learned_by_quorum_consec (log s))"
  shows "instance_bound_bound (log s) \<ge> instance_bound (log s)"
  using assms l1 l2 unfolding instance_bound_bound_def instance_bound_def
  apply simp
proof -
  assume a1: "finite (learned_instances (log s))"
  { fix nn :: nat
    have "\<And>a. learned_by_quorum_consec (log (a::('b, 'a, 'c) ampr_state_scheme)) \<subseteq> learned_instances (log a)"
      by (metis (no_types) all_not_in_conv l1 l2 order_trans quorums_axioms quorums_def)
    then have "learned_by_quorum_consec (log s) = {} \<or> (learned_instances (log s) = {} \<or> nn \<notin> learned_by_quorum_consec (log s) \<or> nn \<le> Max (learned_instances (log s))) \<and> learned_instances (log s) \<noteq> {}"
      using a1 by (metis (no_types) Max.boundedE Max_mono assms(2) empty_subsetI inf.absorb_iff1 inf.absorb_iff2) }
  then have "learned_by_quorum_consec (log s) = {} \<or> (learned_instances (log s) = {} \<or> (\<forall>n. n \<notin> learned_by_quorum_consec (log s) \<or> n \<le> Max (learned_instances (log s)))) \<and> learned_instances (log s) \<noteq> {}"
    by blast
  then show "learned_by_quorum_consec (log s) \<noteq> {} \<longrightarrow> (learned_instances (log s) \<noteq> {} \<longrightarrow> (\<forall>n\<in>learned_by_quorum_consec (log s). n \<le> Max (learned_instances (log s)))) \<and> learned_instances (log s) \<noteq> {}"
    by blast
qed

definition learned_by_one_finite where learned_by_one_finite_def[inv_defs]:
  "learned_by_one_finite s \<equiv> \<forall> q . finite (learned_by_one (log s) q)"
  
definition learned_by_quorum_consec_finite where learned_by_quorum_consec_finite_def[inv_defs]:
  "learned_by_quorum_consec_finite s \<equiv> finite (learned_by_quorum_consec (log s))"
    
lemma learned_by_one_finite: "invariant the_ioa learned_by_one_finite"
  using learned_instances_finite l1
  by (metis IOA.invariant_def infinite_super learned_by_one_finite_def learned_instances_finite_def) 

lemma learned_by_quorum_consec_finite:"invariant the_ioa learned_by_quorum_consec_finite"
  using learned_instances_finite l2
  by (metis IOA.invariant_def finite_subset learned_by_quorum_consec_finite_def learned_instances_finite_def)

lemmas finiteness = learned_by_quorum_consec_finite  learned_instances_finite
  learned_by_one_finite

subsection {* Properties of the instance bound. *}

private  definition aux_inv1 where aux_inv1_def[inv_defs]:
  "aux_inv1 s \<equiv> \<forall> i a b . (i > lookahead \<and> vote s a b i \<noteq> None)
    \<longrightarrow> (i-(lookahead+1)) \<in> learned_by_quorum_consec (log s)"

definition inv1 where inv1_def[inv_defs]:
  "inv1 s \<equiv> \<forall> i > instance_bound (log s) . \<forall> a b . vote s a b i = None"
  
private lemma learn_mono:
  assumes "learn a i vs (s::('v, 'a) ampr_state) t"
    and "log s a2 j \<noteq> None"
  shows "log t a2 j \<noteq> None" using assms by (cases s, cases t, auto simp add:fun_eq_iff)

private lemma learn_increases_learned_by_quorum_consec:
  assumes "learn a i vs (s::('v, 'a) ampr_state) t" and "finite (learned_by_quorum_consec (log s))"
    and "finite (learned_by_quorum_consec (log t))"
  shows "learned_by_quorum_consec (log s) \<subseteq> learned_by_quorum_consec (log t)"
proof -
  have "log s a j \<noteq> None \<Longrightarrow> log t a j \<noteq> None" for j a using learn_mono[OF assms(1)] by auto
  thus "learned_by_quorum_consec (log s) \<subseteq> learned_by_quorum_consec (log t)"
  proof (auto simp add:learned_by_quorum_consec_def is_learned_by_set_def)
    fix j k
    assume 1:"\<And> a l . \<exists>y. log s a l = Some y \<Longrightarrow> \<exists>y. log t a l = Some y"
      and 2:"\<forall>l\<le>j. \<exists>q\<in>quorums. \<forall>a\<in>q. \<exists>y. log s a l = Some y" and 3:"k \<le> j" 
    show "\<exists>q\<in>quorums. \<forall>a\<in>q. \<exists>y. log t a k = Some y"
    proof -
      from 2 and 3 obtain q where "q \<in> quorums" and "\<And> a . a \<in> q \<Longrightarrow> \<exists> y . log s a k = Some y" by auto
      with 1 show ?thesis by meson 
    qed
  qed
qed

private lemma aux_inv1: "invariant the_ioa aux_inv1"
  apply (simp_inv invs:learned_by_quorum_consec_finite inv_defs:inv_defs learned_by_quorum_consec_def is_learned_by_set_def)
  subgoal premises prems for s t 
  proof -
    from prems(2,3) learn_increases_learned_by_quorum_consec[OF prems(4)]
    have "learned_by_quorum_consec (log s) \<subseteq> learned_by_quorum_consec (log t)" by (auto simp add:inv_defs)
    moreover have "vote t = vote s" using prems(4) by (cases s, cases t, auto)
    ultimately show ?thesis using prems(1) by (force simp add:inv_defs)
  qed
  subgoal premises prems for s t using prems(1,4)
    by (cases s, cases t, force simp add:inv_defs learned_by_quorum_consec_def)
  subgoal premises prems for s t _ a i q v
  proof -
    from prems(4) have "vote t = (vote s)(a := (vote s a)(ballot s a := (vote s a (ballot s a))(i := Some v)))"
      and "bounded t" and "log t = log s" by auto
    thus ?thesis using prems(1) by (simp add:inv_defs bounded_def, metis)
  qed
  done

lemma inv1:"invariant the_ioa inv1"
proof -
  have "inv1 (s::('v, 'a) ampr_state)" if "aux_inv1 s" and "learned_by_quorum_consec_finite s" for s
  proof (rule ccontr, auto simp add:inv_defs)
    fix i a b v
    assume 1:"instance_bound (log s) < i" and 2:"vote s a b i = Some v"
    from 1 have "i > lookahead" by (auto simp add:instance_bound_def)
    with 2 \<open>aux_inv1 s\<close> have "(i-lookahead-1) \<in> learned_by_quorum_consec (log s)"
      by (auto simp add:inv_defs)
    with 1 \<open>learned_by_quorum_consec_finite s\<close> show False apply (simp add: instance_bound_def inv_defs)
      by (metis Max_ge Suc_eq_plus1 diff_Suc_eq_diff_pred leD le_diff_conv)
  qed
  thus ?thesis by (metis IOA.invariant_def aux_inv1 learned_by_quorum_consec_finite)
qed  
  
definition inv2 where inv2_def[inv_defs]:
  "inv2 s \<equiv> \<forall> i > instance_bound (log s) . \<forall> a . log s a i = None"
  
lemma learn_increases_instance_bound:
  assumes "learn a i vs (s::('v, 'a) ampr_state) t" and "finite (learned_by_quorum_consec (log s))"
    and "finite (learned_by_quorum_consec (log t))"
  shows "instance_bound (log t) \<ge> instance_bound (log s)"  
  using learn_increases_learned_by_quorum_consec
  by (metis (no_types, lifting) Max.antimono One_nat_def add.right_neutral add_Suc_right add_mono_thms_linordered_semiring(3) assms(1-3) instance_bound_def le_imp_less_Suc linear not_add_less2 subset_empty)
 
lemma inv2:"invariant the_ioa inv2"
  apply (auto_inv invs:inv1 learned_by_quorum_consec_finite inv_defs:inv_defs)
  subgoal premises prems for s t _ a i vs
  proof (auto simp add:inv2_def)
    fix a2 j
    assume 1:"instance_bound (log t) < j"
    show "log t a2 j = None" 
    proof (cases "log s a2 j = None")
      case True
      show ?thesis 
      proof (rule ccontr)
        assume 2:"log t a2 j \<noteq> None"
        with \<open>learn a i vs s t\<close> True have 3:"a2 = a"
          by (cases s, cases t, auto)
        have "chosen s j (the (log t a2 j))"
        proof -
          from \<open>learn a i vs s t\<close> 3 have "\<forall>j\<in>{0..<i} \<union> {i + length vs..} . log s a2 j = log t a2 j"
            by (cases s, cases t, auto)
          hence 4:"j \<in> {i..<i+length vs}" using 2 True
            by (metis UnI1 UnI2 atLeastLessThan_iff atLeast_iff leI not_less_zero)
          hence "chosen s j (vs ! (j-i))" using \<open>learn a i vs s t\<close> apply auto
            using le_Suc_ex by fastforce
          moreover have "log t a j = Some (vs ! (j-i))" using \<open>learn a i vs s t\<close> 4
            by (cases s, cases t, auto)
          ultimately show ?thesis using 3 by simp
        qed
        with \<open>inv1 s\<close> have "j \<le> instance_bound (log s)" 
          apply (auto simp add:inv_defs ballot_array.chosen_def ballot_array.chosen_at_def quorums_def)
          by (metis (full_types) not_less option.distinct(1) quorum_inter_witness)
        then show False using learn_mono  prems(3,5) learn_increases_instance_bound 1
          by (meson dual_order.strict_trans1 learned_by_quorum_consec_finite_def not_le prems(6))
      qed
    next
      case False
      then show ?thesis using learn_mono \<open>inv2 s\<close> \<open>learn a i vs s t\<close> prems(3,5)(* finiteness *) 1 
          learn_increases_instance_bound
        apply (auto simp add:inv_defs simp del:learn_def) by (meson False le_less_trans)
    qed
  qed
  done

definition inv4 where inv4_def[inv_defs]:
  "inv4 s \<equiv> \<forall> a i b . (ghost_vote s a b i \<noteq> None \<or> vote s a b i \<noteq> None) \<longrightarrow> i \<le> instance_bound (log s)"
  
lemma inv4: "invariant the_ioa inv4"                                                                                
  apply (auto_inv invs:inv1 inv2 finiteness inv_defs:)
  subgoal premises prems for s t _ a i vs 
  proof -
    from prems(12) have "ghost_vote t = ghost_vote s" and "vote t = vote s"  by (cases s, cases t, auto)+
    moreover
    have "instance_bound (log t) \<ge> instance_bound (log s)"
      using learn_increases_instance_bound learned_by_quorum_consec_finite_def prems(12) prems(4) prems(9) by blast 
    ultimately show ?thesis
      by (metis (no_types, lifting) dual_order.trans inv4_def prems(1))
  qed
  subgoal by (auto simp add:inv4_def; blast)
  done

lemmas instance_bound_lemmas = inv1 inv2 inv4

end

subsection {* Relation between the ghost state and the normal state. *}

context begin

definition safe_instance_gt_instance_bound where safe_instance_gt_instance_bound_def[inv_defs]:
  "safe_instance_gt_instance_bound s \<equiv> \<forall> q \<in> quorums . safe_instance (log s) q > instance_bound (log s)"

lemma safe_instance_gt_instance_bound: 
  assumes "\<And> q . finite (learned_by_one (log s) q)"
  shows "safe_instance_gt_instance_bound s"
  unfolding safe_instance_gt_instance_bound_def
proof 
  fix q
  assume "q \<in> quorums"
  have "learned_by_quorum_consec (log s) \<subseteq> learned_by_one (log s) q" by (simp add: \<open>q \<in> quorums\<close> l1) 
  thus "instance_bound (log s) < safe_instance (log s) q" 
    apply (simp add:instance_bound_def safe_instance_def) using Max_mono assms(1) le_imp_less_Suc by blast
qed

private definition inv5 where inv5_def[inv_defs]:
  "inv5 s \<equiv> \<forall> a i b . (i \<ge> lowest s a \<and> vote s a b i = None) \<longrightarrow> ghost_vote s a b i = None"
  
private lemma inv5: "invariant the_ioa inv5"                                                                                
  apply (simp_inv invs:  inv4 learned_by_one_finite)
    subgoal premises prems for s t using prems
      by (cases s, cases t, auto simp add:inv_defs)
  subgoal premises prems using prems safe_instance_gt_instance_bound
    apply (auto simp add:inv_defs)
    apply (meson inv4_def leD less_le_trans prems(2) safe_instance_gt_instance_bound safe_instance_gt_instance_bound_def)
    done
  done

definition inv6 where inv6_def[inv_defs]:
  "inv6 s \<equiv> \<forall> a i . i \<ge> lowest s a  \<longrightarrow> (\<forall> b . ghost_vote s a b i = vote s a b i)" 
  
lemma inv6: "invariant the_ioa inv6"  
  apply (auto_inv invs:inv5)
  subgoal premises prems for s t using prems
    by (cases s, cases t, auto simp add:inv_defs)
  done
  
definition inv7 where inv7_def[inv_defs]:
  "inv7 s \<equiv> \<forall> a b i . vote s a b i \<noteq> None \<longrightarrow> ghost_vote s a b i = vote s a b i"

lemma inv7: "invariant the_ioa inv7"
  apply (auto_inv invs: inv6) 
  subgoal premises prems for s t using prems
    by (cases s, cases t, auto simp add:inv_defs)
  done

definition inv13 where inv13_def[inv_defs]:
  "inv13 s \<equiv> \<forall> i \<le> instance_bound (log s) . \<forall> a . i \<ge> lowest s a \<longrightarrow> ghost_ballot s a i = ballot s a"
lemma inv13: "invariant the_ioa inv13"                                                                                
  apply (simp_inv invs: inv6 inv7 instance_bound_lemmas)
  subgoal premises prems using prems amp_proof_axioms apply -
    nitpick[no_assms, card 'v = 2, card 'a = 3,  card nat = 4, card "'v option" = 3, card "nat option" = 5, expect=none,
        card "nat \<times> nat" = 9, card "('v, 'a) ampr_state" = 2, card "'v list" = 2]
    sorry
  subgoal premises prems using prems amp_proof_axioms apply -
    nitpick[no_assms, card 'v = 2, card 'a = 3,  card nat = 4, card "'v option" = 3, card "nat option" = 5, expect=none,
        card "nat \<times> nat" = 9, card "('v, 'a) ampr_state" = 2, card "'v list" = 2]
    sorry
  sorry

lemmas ghost_rel = inv6 inv7 inv13

end

subsection {* Other invariants *}

definition inv12 where inv12_def[inv_defs]:
  "inv12 s \<equiv> \<forall> i > instance_bound (log s) . \<forall> a . ghost_ballot s a i = 0"
  
lemma inv12: "invariant the_ioa inv12"
  apply (simp_inv invs: instance_bound_lemmas ghost_rel inv_defs:inv_defs)
  subgoal premises prems using prems amp_proof_axioms apply -
    nitpick[no_assms, card 'v = 2, card 'a = 3,  card nat = 4, card "'v option" = 3, card "nat option" = 5, expect=none,
        card "nat \<times> nat" = 9, card "('v, 'a) ampr_state" = 2, card "'v list" = 2]
    sorry
  subgoal premises prems for s t using prems amp_proof_axioms apply -
    nitpick[no_assms, card 'v = 2, card 'a = 3,  card nat = 4, card "'v option" = 3, card "nat option" = 5, expect=none,
        card "nat \<times> nat" = 9, card "('v, 'a) ampr_state" = 2, card "'v list" = 2, eval="(instance_bound (log s), instance_bound (log t))"]
    sorry
  sorry

definition inv8 where inv8_def[inv_defs]:
  "inv8 s \<equiv> \<forall> a b i . ghost_vote s a b i \<noteq> None
    \<longrightarrow> (\<exists> q \<in> quorums . ballot_array.joined (flip (ghost_ballot s) i) b q)"

lemma inv8: "invariant the_ioa inv8"
  apply (simp_inv invs: instance_bound_lemmas ghost_rel inv_defs:inv_defs ballot_array.chosen_def)
  subgoal premises prems using prems amp_proof_axioms apply -
  nitpick[no_assms, card 'v = 2, card 'a = 3,  card nat = 4, card "'v option" = 3, card "nat option" = 5, expect=none,
      card "nat \<times> nat" = 9, card "('v, 'a) ampr_state" = 2, card "'v list" = 2]
  sorry
  subgoal premises prems using prems amp_proof_axioms apply -
  nitpick[no_assms, card 'v = 2, card 'a = 3,  card nat = 4, card "'v option" = 3, card "nat option" = 5, expect=none,
      card "nat \<times> nat" = 9, card "('v, 'a) ampr_state" = 2]
  sorry
  subgoal premises prems using prems amp_proof_axioms apply -
  nitpick[no_assms, card 'v = 2, card 'a = 3,  card nat = 4, card "'v option" = 3, card "nat option" = 5, expect=none,
      card "nat \<times> nat" = 9, card "('v, 'a) ampr_state" = 2]
  sorry
  subgoal premises prems using prems amp_proof_axioms apply -
  nitpick[no_assms, card 'v = 2, card 'a = 3,  card nat = 4, card "'v option" = 3, card "nat option" = 5, expect=none,
      card "nat \<times> nat" = 9, card "('v, 'a) ampr_state" = 2]
  sorry
  done

definition inv9 where inv9_def[inv_defs]:
  "inv9 s \<equiv> \<forall> a i v . log s a i = Some v \<longrightarrow> ghost_chosen s i v"
  
lemma inv9: "invariant the_ioa inv9"
  apply (simp_inv invs: instance_bound_lemmas ghost_rel inv_defs:inv_defs ballot_array.chosen_def)
  subgoal premises prems using prems amp_proof_axioms apply -
  nitpick[no_assms, card 'v = 2, card 'a = 3,  card nat = 4, card "'v option" = 3, card "nat option" = 5, expect=none,
      card "nat \<times> nat" = 9, card "('v, 'a) ampr_state" = 2, card "'v list" = 2]
  sorry
  subgoal premises prems using prems amp_proof_axioms apply -
  nitpick[no_assms, card 'v = 2, card 'a = 3,  card nat = 4, card "'v option" = 3, card "nat option" = 5, expect=none,
      card "nat \<times> nat" = 9, card "('v, 'a) ampr_state" = 2]
  sorry
  subgoal premises prems using prems amp_proof_axioms apply -
  nitpick[no_assms, card 'v = 2, card 'a = 3,  card nat = 4, card "'v option" = 3, card "nat option" = 5, expect=none,
      card "nat \<times> nat" = 9, card "('v, 'a) ampr_state" = 2]
  sorry
done
  
definition inv10 where inv10_def[inv_defs]:
  "inv10 s \<equiv> \<forall> a i b . ghost_vote s a b i \<noteq> None 
    \<longrightarrow> (\<exists> q \<in> quorums . ballot_array.joined (ballot s) b q)"

lemma inv10: "invariant the_ioa inv10"
  apply (simp_inv invs: instance_bound_lemmas ghost_rel)
  subgoal premises prems using prems amp_proof_axioms apply -
  nitpick[no_assms, card 'v = 2, card 'a = 3,  card nat = 4, card "'v option" = 3, card "nat option" = 5, expect=none,
      card "nat \<times> nat" = 9, card "('v, 'a) ampr_state" = 2, card "'v list" = 2]
  sorry
  subgoal premises prems using prems amp_proof_axioms apply -
  nitpick[no_assms, card 'v = 2, card 'a = 3,  card nat = 4, card "'v option" = 3, card "nat option" = 5, expect=none,
      card "nat \<times> nat" = 9, card "('v, 'a) ampr_state" = 2]
  sorry
  subgoal premises prems using prems amp_proof_axioms apply -
  nitpick[no_assms, card 'v = 2, card 'a = 3,  card nat = 4, card "'v option" = 3, card "nat option" = 5, expect=none,
      card "nat \<times> nat" = 9, card "('v, 'a) ampr_state" = 2]
  sorry
  subgoal premises prems using prems amp_proof_axioms apply -
  nitpick[no_assms, card 'v = 2, card 'a = 3,  card nat = 4, card "'v option" = 3, card "nat option" = 5, expect=none,
      card "nat \<times> nat" = 9, card "('v, 'a) ampr_state" = 2]
  sorry
done

definition inv11 where inv11_def[inv_defs]:
  "inv11 s \<equiv> \<forall> a . let l = lowest s a; j = (l-lookahead-2) in l > lookahead+1 \<longrightarrow>
    (\<exists> q \<in> quorums . \<exists> a \<in> q . log s a j \<noteq> None)"
  -- {* Superseded?. Probably better to prove that lowest is always below @{term instance_bound}*}

lemma inv11: "invariant the_ioa inv11"
  apply (simp_inv invs: instance_bound_lemmas)
  subgoal premises prems using prems amp_proof_axioms apply -
  nitpick[no_assms, card 'v = 2, card 'a = 3,  card nat = 4, card "'v option" = 3, card "nat option" = 5, expect=none,
      card "nat \<times> nat" = 9, card "('v, 'a) ampr_state" = 2, card "'v list" = 2]
  sorry
  subgoal premises prems using prems amp_proof_axioms apply -
  nitpick[no_assms, card 'v = 2, card 'a = 3,  card nat = 4, card "'v option" = 3, card "nat option" = 5, expect=none,
      card "nat \<times> nat" = 9, card "('v, 'a) ampr_state" = 2]
  sorry
done
  
subsection {* the ghost ballot-array is conservative *}

interpretation ba:ballot_array quorums ballot vote for ballot vote .
interpretation bap:ballot_array_props ballot vote quorums for ballot vote 
  by (unfold_locales)

definition conservative_array where conservative_array_def[inv_defs]:
  "conservative_array s \<equiv>  \<forall> i . 
    ballot_array.conservative_array (ghost_ba_vote s i)
    \<and> ballot_array.conservative_array (ba_vote s i)"
  
text {* For this we need explicit suggestions. As it is now, if we don't use the ghost vars in the transitions,
  then an acceptor can vote for a value, crash and forget it, and then another acceptor can vote for a different value,
  making the ghost array not conservative. *}

lemma conservative_inductive:
  "invariant the_ioa conservative_array"
  apply (simp_inv invs:ghost_rel instance_bound_lemmas inv_defs:conservative_array_def ballot_array.conservative_array_def ballot_array.conservative_def)
    apply (case_tac s, case_tac t, auto simp add: conservative_array_def ballot_array.conservative_array_def ballot_array.conservative_def split:option.splits)[1]
  subgoal premises prems for s t using prems amp_proof_axioms apply -
    nitpick[no_assms, card 'v = 2, card 'a = 3,  card nat = 4, card "'v option" = 3, card "nat option" = 5, expect=none,
        card "nat \<times> nat" = 9, card "('v, 'a) ampr_state" = 2, eval="inv6 s"]
    sorry
  subgoal premises prems for s t using prems amp_proof_axioms apply -
    nitpick[no_assms, card 'v = 2, card 'a = 3,  card nat = 4, card "'v option" = 3, card "nat option" = 5, expect=none,
        card "nat \<times> nat" = 9, card "('v, 'a) ampr_state" = 2, eval="inv6 s"]
    sorry
  done

subsection {* the ghost ballot-array is safe } *}

abbreviation safe where "safe s \<equiv> \<forall> i . ballot_array.safe quorums (ballot s) (ba_vote s i)"

abbreviation safe_at where "safe_at s i \<equiv> ba.safe_at (ballot s) (ba_vote s i)"
  
abbreviation ghost_safe where "ghost_safe s \<equiv> 
  \<forall> i . ballot_array.safe quorums (flip (ghost_ballot s) i) (ghost_ba_vote s i)"

abbreviation ghost_safe_at where "ghost_safe_at s i \<equiv> 
  ba.safe_at (flip (ghost_ballot s) i) (ghost_ba_vote s i)"
    
lemma quorum_ballots_finite_ne:
  assumes "q \<in> quorums"
  shows "finite {ballot s a | a . a \<in> q}" and "{ballot s a | a . a \<in> q} \<noteq> {}"
  using quorums_axioms assms by (auto simp add:quorums_def)

lemma quorum_ghost_ballots_finite_ne:
  assumes "q \<in> quorums"
  shows "finite {ghost_ballot s a | a . a \<in> q}" and "{ghost_ballot s a | a . a \<in> q} \<noteq> {}"
  using quorums_axioms assms by (auto simp add:quorums_def)

(* 
lemma trans_imp_prefix_order:
  assumes "s \<midarrow>a\<midarrow>the_ioa\<longrightarrow> t"
  shows "is_prefix_2 quorums (ballot s) (ballot t) (ba_vote s i) (ba_vote t i)" using assms[simplified]
  apply (cases rule:trans_cases)
      apply (auto simp add:is_prefix_2_def split:option.split_asm)[1]
     apply (case_tac s, case_tac t, auto simp add:is_prefix_2_def split:option.split_asm)[1]
    apply (auto simp add:is_prefix_2_def split:option.split_asm)[1] defer defer
  subgoal premises prems for acc
  proof (simp add:is_prefix_2_def, rule allI)
    fix a
    have "(ballot s a \<le> ballot t a) 
      \<and> (\<forall> b . (b < ballot s a \<or> (b = ballot s a \<and> vote s a b i \<noteq> None)) \<longrightarrow> vote s a b i = vote t a b i)" (is "?P")
      if "a \<noteq> acc" using prems that by auto
    moreover
    { assume "a = acc"
      have 1:"\<forall>b. vote t a b i = None" using \<open>a = acc\<close> prems by auto
      have 2:"\<exists> q\<in>quorums . \<forall>a2\<in>q. ballot s a2 \<le> ballot t a"
      proof -
        from prems \<open>a = acc\<close> obtain q b where "q \<in> quorums" and "b = Max {ballot s a | a . a \<in> q}"
          and "ballot t a = b" by (cases s, cases t, auto)
        moreover have "ballot s a \<le> Max {ballot s a | a . a \<in> q}" (is "ballot s a \<le> Max ?S") if "a \<in> q" for a
          using quorum_ballots_finite_ne[of q s, OF \<open>q \<in> quorums\<close>] that by (metis (mono_tags, lifting) Max.coboundedI mem_Collect_eq)
        ultimately show ?thesis by auto
      qed
      note 1 2 }
    ultimately show "ballot s a \<le> ballot t a \<and> (\<forall>b. (b < ballot s a \<longrightarrow> vote s a b i = vote t a b i) \<and> (b = ballot s a \<and> (\<exists>y. vote s a b i = Some y) \<longrightarrow> vote s a (ballot s a) i = vote t a (ballot s a) i)) \<or> (\<exists>q\<in>quorums. \<forall>a2\<in>q. ballot s a2 \<le> ballot t a) \<and> (\<forall>b. vote t a b i = None)"
      by force 
  qed
  apply (auto simp add:is_prefix_2_def split:option.split_asm)[1]
  done *)

definition all_invs where all_invs_def[inv_defs]:"all_invs s \<equiv> inv1 s \<and> inv2 s \<and> inv4 s
  \<and> inv6 s \<and> inv7 s \<and> inv13 s \<and> inv12 s \<and> inv8 s \<and> inv9 s \<and> inv10 s \<and> inv11 s"

lemma trans_imp_prefix_order:
  assumes "(s::('v, 'a) ampr_state) \<midarrow>a\<midarrow>the_ioa\<longrightarrow> t" (* and "is_prefix (ballot s) (ballot t) (ba_vote s i) (ba_vote t i)" *)
    and "all_invs s"
  shows "is_prefix (flip (ghost_ballot s) i) (flip (ghost_ballot t) i) (ghost_ba_vote s i) (ghost_ba_vote t i)" 
  using assms[simplified]
  apply (cases rule:trans_cases)
      (* apply (auto simp add:is_prefix_2_def split:option.split_asm)[2] *)
  subgoal premises prems using prems amp_proof_axioms apply -
  nitpick[no_assms, card 'v = 2, card 'a = 3,  card nat = 4, card "'v option" = 3, card "nat option" = 5, expect=none,
      card "nat \<times> nat" = 9, card "('v, 'a) ampr_state" = 2]
  sorry
  subgoal premises prems using prems amp_proof_axioms apply -
  nitpick[no_assms, card 'v = 2, card 'a = 3,  card nat = 4, card "'v option" = 3, card "nat option" = 5, expect=none,
      card "nat \<times> nat" = 9, card "('v, 'a) ampr_state" = 2, card "'v list"=2]
  sorry
  subgoal premises prems using prems amp_proof_axioms apply -
  nitpick[no_assms, card 'v = 2, card 'a = 3,  card nat = 4, card "'v option" = 3, card "nat option" = 5, expect=none,
      card "nat \<times> nat" = 9, card "('v, 'a) ampr_state" = 2]
  sorry
  subgoal premises prems using prems amp_proof_axioms apply -
  nitpick[no_assms, card 'v = 2, card 'a = 3,  card nat = 4, card "'v option" = 3, card "nat option" = 5, expect=none,
      card "nat \<times> nat" = 9, card "('v, 'a) ampr_state" = 2]
  sorry
  subgoal premises prems using prems amp_proof_axioms apply -
  nitpick[no_assms, card 'v = 2, card 'a = 3,  card nat = 4, card "'v option" = 3, card "nat option" = 5, expect=none,
      card "nat \<times> nat" = 9, card "('v, 'a) ampr_state" = 2]
  sorry
done

lemma safe_mono:
  -- {* @{term safe_at} is monotonic. *}
  assumes "(s::('v, 'a) ampr_state) \<midarrow>a\<midarrow>the_ioa\<longrightarrow> t" and "ghost_safe_at s i v b" and "all_invs s"
    and "ba.joined (ballot s) b q" and "q \<in> quorums"
  shows "ghost_safe_at t i v b" 
proof -
  have "is_prefix (flip (ghost_ballot s) i) (flip (ghost_ballot t) i) (ghost_ba_vote s i) (ghost_ba_vote t i)" 
    using assms(1,3) trans_imp_prefix_order by auto
  with ballot_array_prefix.safe_at_mono quorums_axioms assms(2,4,5) 
  show ?thesis by (fastforce simp add:ballot_array_prefix_def ballot_array_prefix_axioms_def)
qed

text {* To fix from there. *}

lemma safe_votes: 
  fixes s :: "('v, 'a) ampr_state" and t a i v q
  assumes "do_vote a i q v s t" and "conservative_array s" and "safe s"
  shows "safe_at t i v (ballot s a)"
proof -
  let ?b = "ballot s a"
  from \<open>do_vote a i q v s t\<close> have 1:"proved_safe_at s ?b i q v" and 2:"q \<in> quorums" by simp_all
  from 1 \<open>conservative_array s\<close> \<open>safe s\<close> bap.proved_safe_at_abs_imp_safe_at[of ?b "ba_vote s i" "ballot s"]
  have 4:"safe_at s i v ?b"  by (auto simp add:ballot_array.safe_def conservative_array_def split:option.splits)
  have 5:"ba.joined (ballot s) ?b q" using \<open>do_vote a i q v s t\<close>
    by (auto simp add:ballot_array.proved_safe_at_abs_def ballot_array.joined_def)
  have 6:"s \<midarrow>Internal\<midarrow>the_ioa\<longrightarrow> t" using \<open>do_vote a i q v s t\<close> by (metis (full_types) is_trans_simp trans_rel.simps(2))
  from 5 2 safe_mono[of s "Internal" t i v ?b, OF 6 4] show ?thesis by auto
qed

abbreviation ghost_proved_safe_at where 
  -- {* v is proved safe in instance i at ballot b by quorum q *}
  "ghost_proved_safe_at s b i q v \<equiv> 
    ba.proved_safe_at_abs ((flip (ghost_ballot s)) i) (ghost_ba_vote s i) q b v
    \<and> (\<forall> a \<in> q . i \<ge> lowest s a)"
  
lemma safe_votes_ghost: 
  fixes s :: "('v, 'a) ampr_state" and t a i v q
  assumes "do_vote a i q v s t" and "conservative_array s" and "ghost_safe s" and "reachable the_ioa s"
  shows "ghost_safe_at t i v (flip (ghost_ballot s) i a)"
proof -
  let ?b = "ghost_ballot s a i"
  from \<open>do_vote a i q v s t\<close> have 2:"q \<in> quorums" by simp
  from \<open>do_vote a i q v s t\<close> have 1:"ghost_proved_safe_at s ?b i q v"
    using \<open>reachable the_ioa s\<close> apply -
    apply ( insert all_invs, instantiate_invs )
    subgoal premises prems using prems(1) prems(3-) amp_proof_axioms apply -
      nitpick[no_assms, card 'v = 2, card 'a = 3,  card nat = 4, card "'v option" = 3, card "nat option" = 5, expect=none,
          card "nat \<times> nat" = 9, card "('v, 'a) ampr_state" = 2]
      sorry
    done
  from 1 \<open>conservative_array s\<close> \<open>ghost_safe s\<close> 
    bap.proved_safe_at_abs_imp_safe_at[of ?b "ghost_ba_vote s i" "flip (ghost_ballot s) i"]
  have 4:"ghost_safe_at s i v ?b"  by (auto simp add:ballot_array.safe_def conservative_array_def split:option.splits)
  have 5:"ba.joined (flip (ghost_ballot s) i) ?b q" using \<open>do_vote a i q v s t\<close> 
    using \<open>reachable the_ioa s\<close> apply -
    apply ( insert all_invs, instantiate_invs )
    subgoal premises prems using prems(1) prems(3-) amp_proof_axioms apply -
      nitpick[no_assms, card 'v = 2, card 'a = 3,  card nat = 4, card "'v option" = 3, card "nat option" = 5, expect=none,
          card "nat \<times> nat" = 9, card "('v, 'a) ampr_state" = 2]
      sorry (*
    by (auto simp add:ballot_array.proved_safe_at_abs_def ballot_array.joined_def) *)
    done
  have 6:"s \<midarrow>Internal\<midarrow>the_ioa\<longrightarrow> t" using \<open>do_vote a i q v s t\<close> by (metis (full_types) is_trans_simp trans_rel.simps(2))
  from 5 2 safe_mono_ghost[of s "Internal" t i v ?b, OF 6 4] \<open>reachable the_ioa s\<close> show ?thesis by auto
qed

lemma safe_inv:
  "invariant the_ioa ghost_safe"
  apply (simp_inv inv_defs:inv_defs ballot_array.safe_def invs:all_invs)
  sorry
declare safe_inv[invs]

subsection {* Finally, the proof that agreement holds (trivial, follows immediately from safe).*}

definition agreement where 
  "agreement s \<equiv> \<forall> v w i . chosen s i v \<and> chosen s i w \<longrightarrow> v = w"

lemma agreement:"invariant the_ioa agreement"
apply(rule invariantI)
    apply(auto simp add: inv_proofs_defs agreement_def ballot_array.chosen_def ballot_array.chosen_at_def)[1]
  apply (metis (mono_tags, lifting) IOA.invariant_def IOA.reachable_n agreement_def proof.safe_inv proof_axioms ballot_array_props.intro ballot_array_props.safe_imp_agreement quorums_axioms the_ioa_def)
done

end

end