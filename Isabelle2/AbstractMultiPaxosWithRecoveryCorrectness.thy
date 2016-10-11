section {* Proof of the agreement property of AbstractMultiPaxosWithRecovery. *}

theory AbstractMultiPaxosWithRecoveryCorrectness
imports AbstractMultiPaxosWithRecovery "~~/src/HOL/Eisbach/Eisbach_Tools" BallotArrayProperties 
begin

text {* Guidlines:
  If a state function depends on only part of the state, make this clear by passing it only that part.
  To maintain reactivity, set a number of threads greater than the number of background tools that can be started.
  *}

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

subsection {* The instance bound. *}

definition instance_bound where "instance_bound l \<equiv> 
  if learned_by_quorum_consec l \<noteq> {} 
  then Max (learned_by_quorum_consec l) + lookahead + 1 
  else lookahead"
  -- {* No instance greater than that can have any vote. *}
  
subsection {* finiteness lemmas. *}

context begin

definition learned_by_one_in_quorum where 
  "learned_by_one_in_quorum l \<equiv> \<Union> q \<in> quorums . learned_by_one l q"
  
private definition instance_bound_bound where "instance_bound_bound l \<equiv> 
  if learned_by_one_in_quorum l \<noteq> {} then Max (learned_by_one_in_quorum l) + lookahead + 1 else lookahead"
  
lemma l1:
  assumes "q \<in> quorums"
  shows "learned_by_quorum_consec (log s) \<subseteq> learned_by_one (log s) q" using assms
  apply (auto simp add:learned_by_quorum_consec_def learned_by_one_def is_learned_by_set_def)
  by (meson order_refl quorum_inter_witness)

private lemma l2:
  assumes "\<And> q . q \<in> quorums \<Longrightarrow> finite (learned_by_one (log s) q)" and "finite (learned_by_quorum_consec (log s))"
  shows "instance_bound_bound (log s) \<ge> instance_bound (log s)" 
proof -
  have "finite (learned_by_one_in_quorum (log s))" using assms(1) quorums_axioms by (simp add:quorums_def
        learned_by_one_in_quorum_def) 
  thus ?thesis using l1 assms(2) apply (auto simp add:instance_bound_bound_def 
        instance_bound_def learned_by_one_in_quorum_def) using Max_ge 
     apply blast
    apply (metis all_not_in_conv empty_subsetI inf.absorb_iff1 inf.absorb_iff2 quorums_axioms quorums_def)
    done
qed

private lemma l3:
  assumes "learn a i vs (s::('v, 'a) ampr_state) t" 
    and "finite (learned_by_one (log s) q)" (is "finite ?S")
  shows "finite (learned_by_one (log t) q)" (is "finite ?T") 
proof -
  from \<open>finite ?S\<close> consider "?S = {}" | j where "j = Max ?S" and "?S \<noteq> {}" by blast
  then obtain k where "\<And> j . j \<in> learned_by_one (log t) q \<Longrightarrow> j \<le> k"
  proof (cases)
    case 1
    hence "\<And> k a . \<lbrakk>k > i + length vs; a \<in> q\<rbrakk> \<Longrightarrow> log t a k = None" using assms(1)
      by (cases s, cases t, auto simp add:learned_by_one_def) 
    hence "\<And> k . k \<in> learned_by_one (log t) q \<Longrightarrow> k \<le> i + length vs"
      apply (auto simp add:learned_by_one_def) by (metis (full_types) not_None_eq not_le)
    thus ?thesis using that by auto
  next
    case 2
    hence "\<And> k a . \<lbrakk>k > j; a \<in> q\<rbrakk> \<Longrightarrow> log s a k = None" using assms(2)
      unfolding learned_by_one_def using Max_gr_iff by blast 
    hence "\<And> k a . \<lbrakk>k > max (i + length vs) j; a \<in> q\<rbrakk> \<Longrightarrow>  log t a k = None" using assms(1)
      by (auto simp add:learned_by_one_def) 
    hence "\<And> k . k \<in> learned_by_one (log t) q \<Longrightarrow> k \<le> max (i + length vs) j"
      apply (auto simp add:learned_by_one_def is_learned_by_set_def) using not_less by force
    thus ?thesis using that by auto
  qed
  thus ?thesis
    using finite_nat_set_iff_bounded_le by blast
qed
  
definition learned_by_one_finite where learned_by_one_finite_def[inv_defs]:
  "learned_by_one_finite s \<equiv> \<forall> q . finite (learned_by_one (log s) q)"
  
definition learned_by_one_in_quorum_finite where
  "learned_by_one_in_quorum_finite s \<equiv> finite (learned_by_one_in_quorum (log s))"
  
definition learned_by_quorum_consec_finite where learned_by_quorum_consec_finite_def[inv_defs]:
  "learned_by_quorum_consec_finite s \<equiv> finite (learned_by_quorum_consec (log s))"
    
lemma learned_by_one_finite: "invariant the_ioa learned_by_one_finite"
  apply (auto_inv invs: inv_defs:inv_defs learned_by_one_def is_learned_by_set_def)
  subgoal premises prems using l3 prems unfolding learned_by_one_finite_def by blast
  done

lemma learned_by_one_in_quorum_finite:"invariant the_ioa learned_by_one_in_quorum_finite"
proof -
  have "learned_by_one_in_quorum_finite s" if "learned_by_one_finite s" for s using that quorums_axioms
    by (auto simp add:learned_by_one_in_quorum_finite_def learned_by_one_finite_def quorums_def
        learned_by_one_in_quorum_def) 
  thus ?thesis
    using IOA.invariant_def learned_by_one_finite by blast  
qed

lemma learned_by_quorum_consec_finite:"invariant the_ioa learned_by_quorum_consec_finite"
proof -
  have "learned_by_one_finite s \<Longrightarrow> learned_by_quorum_consec_finite s" for s using l1
    by (metis all_not_in_conv learned_by_one_finite_def infinite_super learned_by_quorum_consec_finite_def quorums_axioms quorums_def) 
  show ?thesis using learned_by_one_finite by (simp add: \<open>\<And>s. learned_by_one_finite s \<Longrightarrow> learned_by_quorum_consec_finite s\<close> IOA.invariant_def)
qed

lemmas finiteness = learned_by_quorum_consec_finite  learned_by_one_in_quorum_finite
  learned_by_one_finite

subsection {* Properties of the instance bound. *}

private 
definition aux_inv1 where aux_inv1_def[inv_defs]:
  "aux_inv1 s \<equiv> \<forall> i a b . (i > lookahead \<and> vote s a b i \<noteq> None)
    \<longrightarrow> (i-(lookahead+1)) \<in> learned_by_quorum_consec (log s)"

definition inv1 where inv1_def[inv_defs]:
  "inv1 s \<equiv> \<forall> i > instance_bound (log s) . \<forall> a b . vote s a b i = None"
  
private lemma learn_mono:
  assumes "learn a i vs (s::('v, 'a) ampr_state) t"
    and "log s a2 j \<noteq> None"
  shows "log t a2 j \<noteq> None" using assms 
  by (auto, metis UnI1 UnI2 add_le_cancel_left atLeastLessThan_iff atLeast_iff nat_le_iff_add not_le zero_le)

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

private
lemma aux_inv1: "invariant the_ioa aux_inv1"
  apply (simp_inv invs:learned_by_quorum_consec_finite inv_defs:inv_defs learned_by_quorum_consec_def is_learned_by_set_def)
  subgoal premises prems for s t 
  proof -
    from prems(2,3) learn_increases_learned_by_quorum_consec[OF prems(4)]
    have "learned_by_quorum_consec (log s) \<subseteq> learned_by_quorum_consec (log t)" by (auto simp add:inv_defs)
    moreover have "vote t = vote s" using prems(4) by auto
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
      by (auto simp add:inv_defs )
    with 1 \<open>learned_by_quorum_consec_finite s\<close> show False apply (simp add: instance_bound_def inv_defs)
      by (metis Max_ge Suc_eq_plus1 diff_Suc_eq_diff_pred leD le_diff_conv)
  qed
  thus ?thesis by (metis IOA.invariant_def aux_inv1 learned_by_quorum_consec_finite) 
qed  
  
definition inv2 where inv2_def[inv_defs]:
  -- {* Is this needed? YES *}
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
    fix a i
    assume 1:"instance_bound (log t) < i"
    show "log t a i = None" 
    proof (cases "log s a i = None")
      case True
      then show ?thesis sorry
    next
      case False
      then show ?thesis using learn_mono prems 1 learn_increases_instance_bound
        apply (auto simp add:inv_defs simp del:learn_def) by (meson False le_less_trans)
    qed
  qed
  done
  
end

subsection {* Relation between the ghost state and the normal state. *}

definition inv3 where inv3_def[inv_defs]:
  "inv3 s \<equiv> \<forall> a i . i \<ge> lowest s a  \<longrightarrow> ghost_ballot s a i = ballot s a"

lemma inv3: "invariant the_ioa inv3" by (force_inv)
  
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
   
definition inv4 where inv4_def[inv_defs]:
  "inv4 s \<equiv> \<forall> a i b . (ghost_vote s a b i \<noteq> None \<or> vote s a b i \<noteq> None) \<longrightarrow> i \<le> instance_bound (log s)"
  
lemma inv4: "invariant the_ioa inv4"                                                                                
  apply (auto_inv invs:inv1 inv2 finiteness inv_defs:)
  subgoal premises prems for s t _ a i vs 
  proof -
    from prems(12) have "ghost_vote t = ghost_vote s" and "vote t = vote s" by auto
    moreover
    have "instance_bound (log t) \<ge> instance_bound (log s)"
      using learn_increases_instance_bound learned_by_quorum_consec_finite_def prems(12) prems(4) prems(9) by blast 
    ultimately show ?thesis
      by (metis (no_types, lifting) dual_order.trans inv4_def prems(1))
  qed
  subgoal by (auto simp add:inv4_def; blast)
  done
  
definition inv5 where inv5_def[inv_defs]:
  "inv5 s \<equiv> \<forall> a i b . (i \<ge> lowest s a \<and> vote s a b i = None) \<longrightarrow> ghost_vote s a b i = None"
  
lemma inv5: "invariant the_ioa inv5"                                                                                
  apply (simp_inv invs:  inv4 learned_by_one_finite)
   apply (force simp add:inv_defs)
  subgoal premises prems using prems safe_instance_gt_instance_bound
    apply (auto simp add:inv_defs)
    apply (meson inv4_def leD less_le_trans prems(2) safe_instance_gt_instance_bound safe_instance_gt_instance_bound_def)
    done
  done

definition inv6 where inv6_def[inv_defs]:
  "inv6 s \<equiv> \<forall> a i . i \<ge> lowest s a  \<longrightarrow> (\<forall> b . ghost_vote s a b i = vote s a b i)" 
  
lemma inv6: "invariant the_ioa inv6"  by (auto_inv invs:inv5)
  
definition inv7 where inv7_def[inv_defs]:
  "inv7 s \<equiv> \<forall> a b i . vote s a b i \<noteq> None \<longrightarrow> ghost_vote s a b i = vote s a b i"

lemma inv7: "invariant the_ioa inv7"
  by (auto_inv invs: inv6 inv3) 

lemmas ghost_rel = inv3 inv6 inv7

subsection {* Other invariants *}
  subgoal premises prems using prems amp_proof_axioms apply -
  nitpick[no_assms, card 'v = 2, card 'a = 3,  card nat = 4, card "'v option" = 3, card "nat option" = 5, expect=none,
      card "nat \<times> nat" = 9, card "('v, 'a) ampr_state" = 2]
  sorry
done

definition inv30 where inv30_def[inv_defs]:
  "inv30 s \<equiv> \<forall> a b i . ghost_vote s a b i \<noteq> None
    \<longrightarrow> (\<exists> q \<in> quorums . ballot_array.joined (flip (ghost_ballot s) i) b q)"

lemma inv30: "invariant the_ioa inv30"
  apply (simp_inv invs: inv3 old_inv2 old_inv3 safe_instance_gt_instance_bound old_inv5 old_inv6 old_inv7 old_inv8  inv_defs:inv_defs ballot_array.chosen_def)
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
  subgoal premises prems using prems amp_proof_axioms apply -
  nitpick[no_assms, card 'v = 2, card 'a = 3,  card nat = 4, card "'v option" = 3, card "nat option" = 5, expect=none,
      card "nat \<times> nat" = 9, card "('v, 'a) ampr_state" = 2]
  sorry
  done


definition old_inv9 where old_inv9_def[inv_defs]:
  "old_inv9 s \<equiv> \<forall> a i v . log s a i = Some v \<longrightarrow> ghost_chosen s i v"
  
lemma old_inv9: "invariant the_ioa old_inv9"
  apply (simp_inv invs: inv3 old_inv2 old_inv3 safe_instance_gt_instance_bound old_inv5 old_inv6 old_inv7 old_inv8 inv30 inv31 inv_defs:inv_defs ballot_array.chosen_def)
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
  
definition inv32 where inv32_def[inv_defs]:
  "inv32 s \<equiv> \<forall> a i b . ghost_vote s a b i \<noteq> None 
    \<longrightarrow> (\<exists> q \<in> quorums . ballot_array.joined (ballot s) b q)"

lemma inv32: "invariant the_ioa inv32"
  apply (simp_inv invs: inv3 old_inv2 old_inv3 safe_instance_gt_instance_bound old_inv5 old_inv6 old_inv7 old_inv8 old_inv9 inv30 inv31) 
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
  subgoal premises prems using prems amp_proof_axioms apply -
  nitpick[no_assms, card 'v = 2, card 'a = 3,  card nat = 4, card "'v option" = 3, card "nat option" = 5, expect=none,
      card "nat \<times> nat" = 9, card "('v, 'a) ampr_state" = 2]
  sorry
done

definition inv33 where inv33_def[inv_defs]:
  "inv33 s \<equiv> \<forall> a . let l = lowest s a; j = l-lookahead-1 in l > lookahead+1 \<longrightarrow>
    (\<exists> q \<in> quorums . \<exists> a \<in> q . log s a j \<noteq> None)"

lemma inv33: "invariant the_ioa inv33"
  apply (simp_inv invs: inv3 old_inv2 old_inv3 safe_instance_gt_instance_bound old_inv5 old_inv6 old_inv7 old_inv8 old_inv9 inv30 inv31 inv32)
  subgoal premises prems using prems amp_proof_axioms apply -
  nitpick[no_assms, card 'v = 2, card 'a = 3,  card nat = 4, card "'v option" = 3, card "nat option" = 5, expect=none,
      card "nat \<times> nat" = 9, card "('v, 'a) ampr_state" = 2]
  sorry
  subgoal premises prems using prems amp_proof_axioms apply -
  nitpick[no_assms, card 'v = 2, card 'a = 3,  card nat = 4, card "'v option" = 3, card "nat option" = 5, expect=none,
      card "nat \<times> nat" = 9, card "('v, 'a) ampr_state" = 2]
  sorry
done
  
definition ghost_rel_normal_inv where "ghost_rel_normal_inv s \<equiv> inv3 s \<and> safe_instance_gt_instance_bound s \<and> old_inv5 s \<and> old_inv8 s \<and> inv31 s"

definition all_invs where "all_invs s \<equiv> inv3 s \<and> old_inv2 s \<and> old_inv3 s \<and> safe_instance_gt_instance_bound s \<and> old_inv5 s \<and> old_inv6 s 
  \<and> old_inv7 s \<and> old_inv8 s \<and> old_inv9 s \<and> inv30 s \<and> inv31 s \<and> inv32 s \<and> inv33 s"
  
subsection {* the ghost ballot-array is conservative *}

interpretation ba:ballot_array quorums ballot vote for ballot vote .
interpretation bap:ballot_array_props ballot vote quorums for ballot vote 
  by (unfold_locales)

definition conservative_array where conservative_array_def[inv_defs]:
  "conservative_array s \<equiv>  \<forall> i . 
    ballot_array.conservative_array (ghost_ba_vote s i) 
    \<and> ballot_array.conservative_array (ba_vote s i)"

lemmas ghost_rel_normal = old_inv8 inv3 inv31 old_inv5 safe_instance_gt_instance_bound
  
lemma conservative_inductive:
  "invariant the_ioa conservative_array"
  apply (simp_inv invs:ghost_rel_normal inv_defs:conservative_array_def ballot_array.conservative_array_def ballot_array.conservative_def)
   apply (auto simp add: conservative_array_def ballot_array.conservative_array_def ballot_array.conservative_def split:option.splits)[1]
  subgoal premises prems using prems amp_proof_axioms apply -
  nitpick[no_assms, card 'v = 2, card 'a = 3,  card nat = 4, card "'v option" = 3, card "nat option" = 5, expect=none,
      card "nat \<times> nat" = 9, card "('v, 'a) ampr_state" = 2]
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
  
lemma trans_imp_prefix_order:
  assumes "s \<midarrow>a\<midarrow>the_ioa\<longrightarrow> t"
  shows "is_prefix_2 quorums (ballot s) (ballot t) (ba_vote s i) (ba_vote t i)" using assms[simplified]
  apply (cases rule:trans_cases)
      apply (auto simp add:is_prefix_2_def split:option.split_asm)[3] defer
   apply (auto simp add:is_prefix_2_def split:option.split_asm)[1]
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
  done

lemma test:
  assumes "is_prefix_2 quorums (ballot s) (ballot t) (ba_vote s i) (ba_vote t i)"
    and "all_invs s" and "all_invs t"
  shows "is_prefix_2 quorums (flip (ghost_ballot s) i) (flip (ghost_ballot t) i) (ghost_ba_vote s i) (ghost_ba_vote t i)"
  using assms amp_proof_axioms apply -
  nitpick[no_assms, card 'v = 2, card 'a = 3,  card nat = 4, card "'v option" = 3, card "nat option" = 5, expect=none,
      card "nat \<times> nat" = 9, card "('v, 'a) ampr_state" = 2]
  oops

lemma trans_imp_prefix_order_ghost:
  assumes "s \<midarrow>a\<midarrow>the_ioa\<longrightarrow> t" and "is_prefix_2 quorums (ballot s) (ballot t) (ba_vote s i) (ba_vote t i)"
    and "all_invs s" and "all_invs t"
  shows "is_prefix_2 quorums (flip (ghost_ballot s) i) (flip (ghost_ballot t) i) (ghost_ba_vote s i) (ghost_ba_vote t i)" 
  using assms[simplified]
  apply (cases rule:trans_cases)
      apply (auto simp add:is_prefix_2_def split:option.split_asm)[2] 
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
  assumes "s \<midarrow>a\<midarrow>the_ioa\<longrightarrow> t" and "safe_at s i v b" and "ba.joined (ballot s) b q" and "q \<in> quorums"
  shows "safe_at t i v b" 
proof -
  have "is_prefix_2 quorums (ballot s) (ballot t) (ba_vote s i) (ba_vote t i)" 
    using assms(1) trans_imp_prefix_order by auto
  with ballot_array_prefix_2.safe_at_mono quorums_axioms assms(2-4) 
  show ?thesis
    by (auto simp add:ballot_array_prefix_2_def ballot_array_prefix_2_axioms_def, fast)
qed

lemmas all_invs = inv3 old_inv2 old_inv3 safe_instance_gt_instance_bound old_inv5 old_inv6 old_inv7 old_inv8 old_inv9 inv30 inv31 inv32 inv33

lemma safe_mono_ghost:
  -- {* @{term safe_at} is monotonic. *}
  assumes "s \<midarrow>a\<midarrow>the_ioa\<longrightarrow> t" and "ghost_safe_at s i v b" 
    and "ba.joined (flip (ghost_ballot s) i) b q" and "q \<in> quorums"
    and "reachable the_ioa s"
  shows "ghost_safe_at t i v b" 
proof -
  have "is_prefix_2 quorums (ballot s) (ballot t) (ba_vote s i) (ba_vote t i)" 
    using assms(1) trans_imp_prefix_order by auto
  hence "is_prefix_2 quorums (flip (ghost_ballot s) i) (flip (ghost_ballot t) i) (ghost_ba_vote s i) (ghost_ba_vote t i)"
    using \<open>reachable the_ioa s\<close> trans_imp_prefix_order_ghost \<open>s \<midarrow>a\<midarrow>the_ioa\<longrightarrow> t\<close>
    apply - apply (instantiate_invs_2 invs:all_invs) by (auto simp add:all_invs_def)
  with ballot_array_prefix_2.safe_at_mono[of quorums "flip (ghost_ballot s) i"
      "ghost_ba_vote s i" "flip (ghost_ballot t) i" "ghost_ba_vote t i"]
    quorums_axioms assms(2-4) 
  show ?thesis
    by (auto simp add:ballot_array_prefix_2_def ballot_array_prefix_2_axioms_def)
qed

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