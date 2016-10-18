section {* Proof of the agreement property of AbstractMultiPaxosWithRecovery. *}

theory AbstractMultiPaxosWithRecoveryCorrectness
imports AbstractMultiPaxosWithRecovery "~~/src/HOL/Eisbach/Eisbach_Tools" BallotArrayProperties 
begin

text {* Guidelines:
  If a state function depends on only part of the state, make this clear by passing it only that part.
  To maintain reactivity, set a number of threads greater than the number of background tools that can be started.
  For easier maintenance, do not use automatically generated fact references (i.e. prems(4)) *}

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

declare propose_def[simp] join_ballot_def[simp] do_vote_def[simp] crash_def[simp] suggest_def[simp]
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
method inv_cases methods m1 m2 m3 uses invs =
  (rule invariantI; (
      ((match premises in "?s \<in> ioa.start ?ioa" \<Rightarrow> \<open>-\<close>); m1 )
    | ((instantiate_invs_2 invs:invs | my_fail "''instantiation failed''");
        simp only:is_trans_simp; (m2 | my_fail "''method 2 failed''"); 
          ((induct_tac rule:trans_cases | my_fail "''case analysis failed''"), simp?); rm_trans_rel_assm; m3)
        ) )

method force_inv uses invs declares inv_defs =
  inv_cases \<open>(force simp add:inv_defs ioa_defs)?\<close> \<open>-\<close> \<open>(force simp add:inv_defs split:option.splits)?\<close>
  invs:invs

method simp_inv uses invs declares inv_defs =
  inv_cases \<open>simp add:inv_defs ioa_defs\<close> \<open>-\<close> \<open>(simp add:inv_defs split:option.splits; fail)?\<close>
  invs:invs

method simp_inv_2 methods m uses invs declares inv_defs =
  inv_cases \<open>simp add:inv_defs ioa_defs\<close> m \<open>(simp add:inv_defs split:option.splits; fail)?\<close>
  invs:invs

method auto_inv uses invs declares inv_defs =
  inv_cases \<open>auto simp add:inv_defs ioa_defs\<close> \<open>-\<close> \<open>(auto simp add:inv_defs split:option.splits; fail)?\<close>
  invs:invs

method auto_inv_cases uses invs declares inv_defs =
  inv_cases \<open>auto simp add:inv_defs ioa_defs\<close> \<open>-\<close> \<open>(case_tac s, case_tac t, auto simp add:inv_defs split:option.splits; fail)?\<close>
  invs:invs

method auto_inv_cases_2 methods m uses invs declares inv_defs =
  inv_cases \<open>auto simp add:inv_defs ioa_defs\<close> m \<open>(case_tac s, case_tac t, auto simp add:inv_defs split:option.splits; fail)?\<close>
  invs:invs
  
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
  subgoal premises prems for s t _ a q
  proof -
    from prems(1) obtain j where "log s a k = None" if "k > j" for a k
      unfolding learned_instances_def learned_instances_finite_def using that
      by (metis (mono_tags, lifting) finite_nat_set_iff_bounded mem_Collect_eq not_less_iff_gr_or_eq)
    moreover
    from \<open>crash a q s t\<close> have "\<exists> a . log s a i = Some v" if "log t a i = Some v" for a i v
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
  "aux_inv1 s \<equiv> \<forall> i a b . (i > lookahead \<and> (vote s a b i \<noteq> None \<or> suggestion s b i \<noteq> None))
    \<longrightarrow> (i-(lookahead+1)) \<in> learned_by_quorum_consec (log s)"

definition inv1 where inv1_def[inv_defs]:
  "inv1 s \<equiv> \<forall> i > instance_bound (log s) . \<forall> a b . suggestion s b i = None \<and> vote s a b i = None"
  
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

private lemma crash_increases_learned_by_quorum_consec:
  assumes "crash a q s t"
  shows "learned_by_quorum_consec (log s) \<subseteq> learned_by_quorum_consec (log t)"
  using assms
  apply (cases s, cases t, auto simp add:learned_by_quorum_consec_def is_learned_by_set_def)
  by (meson quorum_inter_witness)

private lemma aux_inv1: "invariant the_ioa aux_inv1"
  apply (simp_inv invs:learned_by_quorum_consec_finite inv_defs:inv_defs learned_by_quorum_consec_def is_learned_by_set_def)
  subgoal premises prems for s t _ a i vs (* learn *)
  proof - thm prems
    from \<open>learned_by_quorum_consec_finite t\<close> \<open>learned_by_quorum_consec_finite s\<close> learn_increases_learned_by_quorum_consec[OF prems(4)]
    have "learned_by_quorum_consec (log s) \<subseteq> learned_by_quorum_consec (log t)" by (auto simp add:inv_defs)
    moreover have "vote t = vote s" and "suggestion t = suggestion s" using \<open>learn a i vs s t\<close> by (cases s, cases t, auto)+
    ultimately show ?thesis using prems(1) by (force simp add:inv_defs)
  qed
  subgoal premises prems for s t _ a q (* crash *)
    using \<open>aux_inv1 s\<close> \<open>crash a q s t\<close> crash_increases_learned_by_quorum_consec[OF prems(4)]
    by (cases s, cases t, force simp add:inv_defs)
  subgoal premises prems for s t _ a i v (* do_vote *)
  proof -
    from \<open>do_vote a i v s t\<close> and \<open>aux_inv1 s\<close> have "vote t = (vote s)(a := (vote s a)(ballot s a := (vote s a (ballot s a))(i := Some v)))"
      and "log t = log s" and "suggestion t = suggestion s" and "i > lookahead \<Longrightarrow> (i-(lookahead+1)) \<in> learned_by_quorum_consec (log s)" by (force simp add:aux_inv1_def)+
    thus ?thesis using \<open>aux_inv1 s\<close> by (simp add:inv_defs) blast
  qed
  subgoal premises prems for s t _ b i q v (* suggest *)
    using prems by (fastforce simp add:inv_defs)
  done

lemma inv1:"invariant the_ioa inv1"
proof -
  have "inv1 (s::('v, 'a) ampr_state)" if "aux_inv1 s" and "learned_by_quorum_consec_finite s" for s
  proof - (* by contradiction *)
    { fix i a b v
      assume 1:"instance_bound (log s) < i" and 2:"vote s a b i = Some v \<or> suggestion s b i = Some v"
      from 1 have "i > lookahead" by (auto simp add:instance_bound_def)
      with 2 \<open>aux_inv1 s\<close> have "(i-lookahead-1) \<in> learned_by_quorum_consec (log s)"
        by (fastforce simp add:inv_defs)
      with 1 \<open>learned_by_quorum_consec_finite s\<close> have False apply (simp add: instance_bound_def inv_defs)
        by (metis Max_ge Suc_eq_plus1 diff_Suc_eq_diff_pred leD le_diff_conv) }
    thus ?thesis apply (simp add:inv_defs)
      by (meson not_Some_eq)
  qed
  thus ?thesis
    using IOA.invariant_def aux_inv1 learned_by_quorum_consec_finite by blast 
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
  subgoal premises prems for s t _ a i vs (* learn *)
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
  subgoal premises prems for s t _ a q (* crash *)
  proof -
    have "instance_bound (log t) \<ge> instance_bound (log s)"
    proof -
      have "learned_by_quorum_consec (log s) \<subseteq> learned_by_quorum_consec (log t)"
        using \<open>crash a q s t\<close>
        apply (cases s, cases t, auto simp add:learned_by_quorum_consec_def is_learned_by_set_def)
        by (meson quorum_inter_witness)
      thus ?thesis
        by (smt Max_mono Suc_eq_plus1 add.commute add_le_cancel_left eq_iff instance_bound_def learned_by_quorum_consec_finite_def less_add_Suc2 less_imp_le prems(5) subset_empty)
    qed
    moreover have "log t a2 i \<noteq> log s a2 i \<Longrightarrow> i \<le> instance_bound (log s)" for i a2
      using \<open>crash a q s t\<close> \<open>inv2 s\<close> by (cases s, cases t, auto simp add:inv_defs)
    ultimately show ?thesis using \<open>inv2 s\<close> apply (auto simp add:inv_defs)
      by (metis le_less_trans not_le)
  qed
  done
thm ampr_state.iffs

definition inv4 where inv4_def[inv_defs]:
  "inv4 s \<equiv> \<forall> a i b . (ghost_vote s a b i \<noteq> None \<or> vote s a b i \<noteq> None) \<longrightarrow> i \<le> instance_bound (log s)"
  
lemma crash_instance_bound:
  assumes "crash a q s t" and "learned_by_quorum_consec_finite s"
    and "learned_by_quorum_consec_finite t"
  shows "instance_bound (log t) \<ge> instance_bound (log s)"
proof -
  from crash_increases_learned_by_quorum_consec[OF \<open>crash a q s t\<close>]
  show ?thesis using \<open>learned_by_quorum_consec_finite s\<close> \<open>learned_by_quorum_consec_finite t\<close>
    apply (simp add:instance_bound_def learned_by_quorum_consec_finite_def)
    using Max_ge by blast
qed

lemma inv4: "invariant the_ioa inv4"
  apply (auto_inv invs:inv1 inv2 finiteness inv_defs:)
  subgoal premises prems for s t _ a i vs
  proof -
    from \<open>learn a i vs s t\<close> have "ghost_vote t = ghost_vote s" and "vote t = vote s"  by (cases s, cases t, auto)+
    moreover
    have "instance_bound (log t) \<ge> instance_bound (log s)"
      using learn_increases_instance_bound learned_by_quorum_consec_finite_def \<open>learn a i vs s t\<close> \<open>learned_by_quorum_consec_finite s\<close> \<open>learned_by_quorum_consec_finite t\<close> by blast 
    ultimately show ?thesis
      by (metis (no_types, lifting) dual_order.trans inv4_def \<open>inv4 s\<close>)
  qed
  subgoal premises prems for s t _ a q
    using \<open> crash a q s t\<close> crash_instance_bound [OF \<open>crash a q s t\<close> \<open>learned_by_quorum_consec_finite s\<close> \<open>learned_by_quorum_consec_finite t\<close>]
    apply (cases s, cases t, auto simp add:inv_defs)
     apply (metis (no_types, lifting) ampr_state.select_convs(6) ampr_state.select_convs(8) dual_order.trans inv4_def option.distinct(1) \<open>inv4 s\<close>)
    by (metis (no_types, lifting) ampr_state.select_convs(3) ampr_state.select_convs(6) dual_order.trans inv4_def option.distinct(1) \<open>inv4 s\<close>)
  done

lemmas instance_bound_lemmas = inv1 inv2 inv4

end

subsection {* Relation between the ghost state and the normal state. *}

context begin

definition inv0 where inv0_def[inv_defs]:
  "inv0 s \<equiv> \<forall> a b i v . (ghost_vote s a b i = Some v \<or> vote s a b i = Some v) \<longrightarrow> suggestion s b i = Some v"

lemma inv0: "invariant the_ioa inv0"
  by (auto_inv_cases)
  
lemma safe_instance_gt_instance_bound: 
  assumes "\<And> q . finite (learned_by_one (log s) q)"
  shows "\<forall> q \<in> quorums . safe_instance (log s) q > instance_bound (log s)"
proof 
  fix q
  assume "q \<in> quorums"
  hence "learned_by_quorum_consec (log s) \<subseteq> learned_by_one (log s) q" 
    apply (auto simp add:learned_by_quorum_consec_def learned_by_one_def)
    by (metis ampr_ioa.is_learned_by_set_def not_None_eq order_refl quorum_inter_witness)
  thus "instance_bound (log s) < safe_instance (log s) q" 
    apply (simp add:instance_bound_def safe_instance_def) using Max_mono assms(1) le_imp_less_Suc by blast
qed

private definition inv5 where inv5_def[inv_defs]:
  "inv5 s \<equiv> \<forall> a i b . (i \<ge> lowest s a \<and> vote s a b i = None) \<longrightarrow> ghost_vote s a b i = None"
  
private lemma inv5: "invariant the_ioa inv5"                                                                                
  apply (auto_inv_cases invs:  inv4 learned_by_one_finite)
  subgoal premises prems for s t _ a q (* crash *)
    using prems
    apply (cases s, cases t, auto simp add:inv_defs)
    by (metis (no_types, lifting) ampr_state.select_convs(6) ampr_state.select_convs(8) dual_order.trans inv4_def leD \<open>inv4 s\<close> safe_instance_gt_instance_bound)
  done

definition inv6 where inv6_def[inv_defs]:
  "inv6 s \<equiv> \<forall> a i . i \<ge> lowest s a  \<longrightarrow> (\<forall> b . ghost_vote s a b i = vote s a b i)" 
  
lemma inv6: "invariant the_ioa inv6"
  by (auto_inv_cases invs:inv5)
  
definition inv7 where inv7_def[inv_defs]:
  "inv7 s \<equiv> \<forall> a b i . vote s a b i \<noteq> None \<longrightarrow> ghost_vote s a b i = vote s a b i"

lemma inv7: "invariant the_ioa inv7"
  by (auto_inv_cases)

definition inv13 where inv13_def[inv_defs]:
  "inv13 s \<equiv> \<forall> i \<le> instance_bound (log s) . \<forall> a . i \<ge> lowest s a \<longrightarrow> ghost_ballot s a i = ballot s a"
  
lemma inv13: "invariant the_ioa inv13"
  -- {* TODO: an understandable proof. *}
  apply (simp_inv invs: finiteness)
  subgoal premises prems for s t _ a i vs (* learn *)
  proof -
    have "instance_bound (log t) \<ge> instance_bound (log s)"
      using learn_increases_instance_bound learned_by_quorum_consec_finite_def 
        \<open>learned_by_quorum_consec_finite t\<close> \<open>learned_by_quorum_consec_finite s\<close> \<open>learn a i vs s t \<close> by blast
    thus ?thesis using \<open>inv13 s\<close> \<open>learn a i vs s t\<close> by (cases s, cases t, auto simp add:inv_defs)
  qed
  subgoal premises prems for s t _ a2 q (* crash *)
  proof -
    have "instance_bound (log t) \<ge> instance_bound (log s)" using crash_instance_bound
        \<open>crash a2 q s t\<close> \<open>learned_by_quorum_consec_finite s\<close> \<open>learned_by_quorum_consec_finite t\<close> by blast
    moreover have "safe_instance (log s) q > instance_bound (log s)" 
      using safe_instance_gt_instance_bound \<open>learned_by_one_finite s\<close> \<open>crash a2 q s t\<close>
      by (metis crash_def learned_by_one_finite_def)
    ultimately
    show ?thesis using \<open>inv13 s\<close> \<open>crash a2 q s t\<close>
      apply (cases s, cases t, auto simp add:inv_defs)
       apply (metis (no_types, lifting) ampr_state.select_convs(2) dual_order.strict_trans1 fun_upd_same)
    proof -
      fix propCmd :: "'v set" and ballota :: "'a \<Rightarrow> nat" and vote :: "'a \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'v option" and suggestion :: "nat \<Rightarrow> nat \<Rightarrow> 'v option" and lowest :: "'a \<Rightarrow> nat" and log :: "'a \<Rightarrow> nat \<Rightarrow> 'v option" and ghost_ballota :: "'a \<Rightarrow> nat \<Rightarrow> nat" and ghost_vote :: "'a \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'v option" and ghost_ballotaa :: "'a \<Rightarrow> nat \<Rightarrow> nat" and i :: nat and new_log :: "nat \<Rightarrow> 'v option" and aa :: 'a
      assume a1: "aa \<noteq> a2"
      assume a2: "lowest aa \<le> i"
      assume a3: "i \<le> instance_bound (log(a2 := new_log))"
      assume "s = \<lparr>propCmd = propCmd, ballot = ballota, vote = vote, suggestion = suggestion, lowest = lowest, log = log, ghost_ballot = ghost_ballota, ghost_vote = ghost_vote\<rparr>"
      assume a4: "\<forall>i\<le>instance_bound log. \<forall>a. lowest a \<le> i \<longrightarrow> ghost_ballota a i = ballota a"
      assume a5: "ghost_ballotaa = (\<lambda>a i. if instance_bound log < i \<and> i \<le> instance_bound (log(a2 := new_log)) then ballot \<lparr>propCmd = propCmd, ballot = ballota(a2 := Max {ballota a |a. a \<in> q}), vote = vote(a2 := \<lambda>b. Map.empty), suggestion = suggestion, lowest = lowest(a2 := safe_instance log q), log = log(a2 := new_log), ghost_ballot = ghost_ballotaa, ghost_vote = ghost_vote\<rparr> a else ghost_ballot \<lparr>propCmd = propCmd, ballot = ballota, vote = vote, suggestion = suggestion, lowest = lowest, log = log, ghost_ballot = ghost_ballota, ghost_vote = ghost_vote\<rparr> a i)"
      assume "t = \<lparr>propCmd = propCmd, ballot = ballota(a2 := Max {ballota a |a. a \<in> q}), vote = vote(a2 := \<lambda>b. Map.empty), suggestion = suggestion, lowest = lowest(a2 := safe_instance log q), log = log(a2 := new_log), ghost_ballot = ghost_ballotaa, ghost_vote = ghost_vote\<rparr>"
      have "\<And>f n. (f(a2 := n::nat)) aa = f aa"
        using a1 by (metis (lifting) fun_upd_apply)
      then show "ghost_ballotaa aa i = ballota aa"
        using a5 a4 a3 a2 by (metis (lifting) ampr_state.select_convs(2) ampr_state.select_convs(7) not_le)
    qed
  qed
  done

lemmas ghost_rel = inv6 inv7 inv13

end

subsection {* Other invariants *}

definition inv12 where inv12_def[inv_defs]:
  "inv12 s \<equiv> \<forall> i > instance_bound (log s) . \<forall> a . ghost_ballot s a i = 0"
  
lemma inv12: "invariant the_ioa inv12"
  apply (simp_inv invs: finiteness inv_defs:inv_defs)
  subgoal premises prems for s t _ a i vs (* learn *)
  proof -
    have "instance_bound (log t) \<ge> instance_bound (log s)"
      using learn_increases_instance_bound learned_by_quorum_consec_finite_def \<open>learn a i vs s t\<close> \<open>learned_by_quorum_consec_finite t\<close> \<open>learned_by_quorum_consec_finite s\<close> by blast
    thus ?thesis using \<open>learn a i vs s t\<close>  \<open>inv12 s\<close> by (cases s, cases t, auto simp add:inv_defs)
  qed
  subgoal premises prems for s t _ a q
  proof -
    have "instance_bound (log t) \<ge> instance_bound (log s)" thm prems(2) prems(5) prems(8)
      using crash_instance_bound \<open>crash a q s t\<close> \<open>learned_by_quorum_consec_finite s\<close> \<open>learned_by_quorum_consec_finite t\<close> by blast
    thus ?thesis using \<open>crash a q s t\<close>  \<open>inv12 s\<close> apply (cases s, cases t, auto simp add:inv_defs)
      by (metis (no_types, lifting) ampr_state.select_convs(7) leD le_less_trans)
  qed
  done

lemma ghost_ballot_mono:
  assumes "trans_rel s a t" and "inv12 s"
    shows "\<forall> a2 j . ghost_ballot t a2 j \<ge> ghost_ballot s a2 j" using assms
  by (induct rule:trans_cases; (auto; fail)?; (cases s, cases t, simp add:inv_defs))
    (metis ampr_state.select_convs(7) le0 less_or_eq_imp_le)

definition inv8 where inv8_def[inv_defs]:
  "inv8 s \<equiv> \<forall> a b i . (suggestion s b i \<noteq> None \<or> ghost_vote s a b i \<noteq> None)
    \<longrightarrow> (\<exists> q \<in> quorums . ballot_array.joined (flip (ghost_ballot s) i) b q)"

lemma inv8: "invariant the_ioa inv8"
  apply (simp_inv_2 \<open>frule ghost_ballot_mono\<close> invs: inv12 inv13 finiteness inv_defs:inv_defs ballot_array.joined_def)
  subgoal premises prems for s t _ a i vs (* learn *)
  proof -
    from \<open>learn a i vs s t\<close> have "suggestion t = suggestion s" and "ghost_vote t = ghost_vote s"
      by (cases s, cases t, auto)+ 
    thus ?thesis using \<open>\<forall>a2 j. ghost_ballot s a2 j \<le> ghost_ballot t a2 j\<close> \<open>inv8 s\<close> 
      apply (simp add:inv_defs ballot_array.joined_def) by (meson dual_order.trans)
  qed
  subgoal premises prems for s t  _ a b
  proof -
    have "suggestion t = suggestion s" and "ghost_vote t = ghost_vote s" using \<open>join_ballot a b s t\<close>
      by auto
    with \<open>inv8 s\<close> \<open>\<forall>a2 j. ghost_ballot s a2 j \<le> ghost_ballot t a2 j\<close> 
    show ?thesis apply (simp add:inv8_def ballot_array.joined_def)
      by (meson dual_order.trans)
  qed
  subgoal premises prems for s t _ a q
  proof -
    have "suggestion t = suggestion s" and "ghost_vote t = ghost_vote s" using \<open>crash a q s t\<close>
      by (cases s, cases t, force)+
    with \<open>inv8 s\<close> \<open>\<forall>a2 j. ghost_ballot s a2 j \<le> ghost_ballot t a2 j\<close> 
    show ?thesis apply (simp add:inv8_def ballot_array.joined_def)
      by (meson dual_order.trans)
  qed
  subgoal premises prems for s t _ b i q v thm prems
  proof -
    obtain q2 where "q2 \<in> quorums" and 1:"\<And> a2 . a2 \<in> q2 \<Longrightarrow> i \<ge> lowest s a2 \<and> ballot s a2 \<ge> b"
       using \<open>suggest b i q v s t\<close> by (auto simp add:ballot_array.proved_safe_at_abs_def)
    have "i \<le> instance_bound (log s)" using \<open>suggest b i q v s t\<close>
      apply (auto simp add:instance_bound_def)
      by (metis Max_ge Suc_eq_plus1_left add.left_commute le_diff_conv learned_by_quorum_consec_finite_def \<open>learned_by_quorum_consec_finite s\<close>)
    have 2:"ghost_ballot s a2 i \<ge> b" if "a2 \<in> q2" for a2 using \<open>inv13 s\<close> \<open>i \<le> instance_bound (log s)\<close>
      1 that by (auto simp add:inv_defs)
    show ?thesis using 2 \<open>q2 \<in> quorums\<close> \<open>suggest b i q v s t\<close> \<open>inv8 s\<close>
      by (auto simp add:inv_defs ballot_array.joined_def)
  qed
  done
    
definition inv9 where inv9_def[inv_defs]:
  "inv9 s \<equiv> \<forall> a i v . log s a i = Some v \<longrightarrow> ghost_chosen s i v"
  
lemma inv9: "invariant the_ioa inv9"
  apply (auto_inv_cases invs: ghost_rel inv_defs:inv_defs ballot_array.chosen_def)
  subgoal premises prems using prems amp_proof_axioms apply -
  nitpick[no_assms, card 'v = 2, card 'a = 3,  card nat = 4, card "'v option" = 3, card "nat option" = 5, expect=none,
      card "('v, 'a) ampr_state" = 2]
  sorry
  subgoal premises prems using prems amp_proof_axioms apply -
  nitpick[no_assms, card 'v = 2, card 'a = 3,  card nat = 4, card "'v option" = 3, card "nat option" = 5, expect=none,
      card "('v, 'a) ampr_state" = 2]
  sorry
done
  
definition inv10 where inv10_def[inv_defs]:
  "inv10 s \<equiv> \<forall> a i b . (suggestion s b i \<noteq> None \<or> ghost_vote s a b i \<noteq> None)
    \<longrightarrow> (\<exists> q \<in> quorums . ballot_array.joined (ballot s) b q)"
    -- {* TODO: Needed? *}

lemma inv10: "invariant the_ioa inv10"
  apply (simp_inv invs: instance_bound_lemmas ghost_rel)
  subgoal premises prems using prems amp_proof_axioms apply -
  nitpick[no_assms, card 'v = 2, card 'a = 3,  card nat = 4, card "'v option" = 3, card "nat option" = 5, expect=none,
      card "('v, 'a) ampr_state" = 2, card "'v list" = 2]
  sorry
  subgoal premises prems using prems amp_proof_axioms apply -
  nitpick[no_assms, card 'v = 2, card 'a = 3,  card nat = 4, card "'v option" = 3, card "nat option" = 5, expect=none,
      card "('v, 'a) ampr_state" = 2]
  sorry
  subgoal premises prems using prems amp_proof_axioms apply -
  nitpick[no_assms, card 'v = 2, card 'a = 3,  card nat = 4, card "'v option" = 3, card "nat option" = 5, expect=none,
      card "('v, 'a) ampr_state" = 2]
  sorry
  subgoal premises prems using prems amp_proof_axioms apply -
  nitpick[no_assms, card 'v = 2, card 'a = 3,  card nat = 4, card "'v option" = 3, card "nat option" = 5, expect=none,
      card "('v, 'a) ampr_state" = 2]
  sorry
  subgoal premises prems using prems amp_proof_axioms apply -
  nitpick[no_assms, card 'v = 2, card 'a = 3,  card nat = 4, card "'v option" = 3, card "nat option" = 5, expect=none,
      card "('v, 'a) ampr_state" = 2]
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

lemma conservative_inductive:
  "invariant the_ioa conservative_array"
  by (auto_inv_cases invs:inv0 inv_defs:conservative_array_def ballot_array.conservative_array_def ballot_array.conservative_def)

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

definition all_invs where all_invs_def[inv_defs]:"all_invs s \<equiv> inv0 s \<and> inv1 s \<and> inv2 s \<and> inv4 s
  \<and> inv6 s \<and> inv7 s \<and> inv13 s \<and> inv12 s \<and> inv8 s \<and> inv9 s \<and> inv10 s"
  
thm ghost_rel

lemma trans_imp_prefix_order:
  assumes "trans_rel (s::('v, 'a) ampr_state) a t" 
    and "\<forall> a2 j . ghost_ballot t a2 j \<ge> ghost_ballot s a2 j"
    and "inv6 s" and "inv7 s" and "inv13 s" and "inv1 s"
  shows "is_prefix (flip (ghost_ballot s) i) (flip (ghost_ballot t) i) (ghost_ba_vote s i) (ghost_ba_vote t i)" 
  using assms
  apply ((cases rule:trans_cases);
      (cases s, cases t, force simp add:is_prefix_def)?)
  apply (cases s, cases t, auto simp add:is_prefix_def inv_defs)
  apply (metis le_less_linear neq_iff option.distinct(1))
  done

lemma safe_mono:
  -- {* @{term safe_at} is monotonic. *}
  assumes "trans_rel (s::('v, 'a) ampr_state) a t" and "ghost_safe_at s i v b" and "all_invs s"
    and True (* and "ba.joined (flip (ghost_ballot s) i) b q"*) and "q \<in> quorums"
  shows "ghost_safe_at t i v b" 
proof -
  have "is_prefix (flip (ghost_ballot s) i) (flip (ghost_ballot t) i) (ghost_ba_vote s i) (ghost_ba_vote t i)" 
    using assms(1,3) trans_imp_prefix_order by auto
  with ballot_array_prefix.safe_at_mono quorums_axioms assms(2,5) 
  show ?thesis by (fastforce simp add:ballot_array_prefix_def ballot_array_prefix_axioms_def)
qed

definition inv15 where inv15_def[inv_defs]:
  "inv15 (s::('v,'a)ampr_state) \<equiv> \<forall> b i v . suggestion s b i = Some v 
    \<longrightarrow> (\<exists> q . ballot_array.proved_safe_at_abs quorums (flip (ghost_ballot s) i) (ghost_ba_vote s i) q b v)"
  
lemma inv15: "invariant the_ioa inv15"
  apply (simp_inv_2 \<open>frule ghost_ballot_mono\<close> invs: inv12 inv13 finiteness inv_defs:inv_defs ballot_array.joined_def)
  subgoal premises prems for s t _ a i vs (* learn *)

text {* To fix from there. *}

lemma safe_votes: 
  fixes s :: "('v, 'a) ampr_state" and t a i v
  assumes "do_vote a i v s t" and "conservative_array s" and "safe s"
  shows "safe_at t i v (ballot s a)"
proof -
  let ?b = "ballot s a"
  from \<open>do_vote a i v s t\<close> have 1:"proved_safe_at s ?b i q v" and 2:"q \<in> quorums" by simp_all
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
          card "('v, 'a) ampr_state" = 2]
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
          card "('v, 'a) ampr_state" = 2]
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