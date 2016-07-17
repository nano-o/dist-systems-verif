theory BallotArrays2
imports Main Quorums LinorderOption "~~/src/HOL/Library/FinFun_Syntax"
  FinFun_Supplemental
begin

locale ballot_array =
  fixes ballot :: "'a \<Rightarrow>f nat option"
  and vote :: "'a \<Rightarrow>f nat \<Rightarrow>f 'v option"
  and quorums :: "'a fset fset"
  and acceptors :: "'a fset"
begin

definition conservative where
  "conservative b \<equiv> \<forall> a1 . \<forall> a2 . a1 |\<in>| acceptors \<and> a2 |\<in>| acceptors \<longrightarrow> (
    let v1 = vote $ a1 $ b; v2 = vote $ a2 $ b in 
      (v1 \<noteq> None \<and> v2 \<noteq> None) \<longrightarrow> v1 = v2)"

definition conservative_array where
  "conservative_array \<equiv> \<forall> b . conservative b"

text {* Here the max is the one from Lattices_Big *}

(* TODO: this is not used... *)
definition max_voted_round where
  "max_voted_round a bound \<equiv> Max {b . vote $ a $ b \<noteq> None \<and> b \<le> bound}"

definition max_voted_round_2 where
  "max_voted_round_2 a bound \<equiv> Max {b \<in> fset (finfun_fset_dom (vote $ a)) . b \<le> bound}"

definition max_voted_round_q where
  "max_voted_round_q q bound \<equiv> 
    if \<exists> b a . a |\<in>| q \<and> b \<le> bound \<and> vote $ a $ b \<noteq> None
    then Some (Max {b . \<exists> a . a |\<in>| q \<and> b \<le> bound \<and> vote $ a $ b \<noteq> None})
    else None"

definition max_voted_round_q_2 where
  "max_voted_round_q_2 q bound \<equiv> let
    max_acc = (\<lambda> ff . {b \<in> fset (finfun_fset_dom ff) . b \<le> bound}) o$ vote;
    max_acc_q = id o$ max_acc (* TODO: here we would need the ` operator *)
  in max_acc"

lemma finite_voted_bals:"finite {b::nat . \<exists> a . a |\<in>| q \<and> b \<le> bound \<and> vote $ a $ b \<noteq> None}"
proof -
  have "{b . \<exists> a . a |\<in>| q \<and> b \<le> bound \<and> vote $ a $ b \<noteq> None} \<subseteq> {b . b \<le> bound}"
    by auto
  moreover have "finite {b::nat . b \<le> bound}" by simp
  ultimately show ?thesis
  by (metis (no_types, lifting) finite_subset)
qed

lemma max_voted_round_none:
  assumes "a |\<in>| q" and "(b::nat) \<le> bound" 
  and "max_voted_round_q q bound = None \<or> b > the (max_voted_round_q q bound)"
  shows "vote $ a $ b = None"
proof (cases "max_voted_round_q q bound")
case None 
  thus ?thesis using assms(1,2)
  by (auto simp add:max_voted_round_q_def split:split_if_asm)
next
  case (Some b\<^sub>m\<^sub>a\<^sub>x)
  with this obtain a2 b2 v where "a2 |\<in>| q \<and> b2 \<le> bound \<and> vote $ a2 $ b2 = Some v"
  by (auto simp add:max_voted_round_q_def split:split_if_asm)
  hence "{b . \<exists> a . a |\<in>| q \<and> b \<le> bound \<and> vote $ a $ b \<noteq> None} \<noteq> {}" by auto
  with this obtain b2 a2 where "a2 |\<in>| q \<and> b2 \<le> bound \<and> vote $ a2 $ b2 \<noteq> None"
    by auto
  moreover note finite_voted_bals
  moreover have "b > Max {b . \<exists> a . a |\<in>| q \<and> b \<le> bound \<and> vote $ a $ b \<noteq> None}" using Some assms(3)
    by (auto simp add:max_voted_round_q_def split:split_if_asm)
  ultimately
  show ?thesis by (metis (mono_tags, lifting) Max.coboundedI assms(1,2) leD mem_Collect_eq) 
qed

lemma max_voted_round_some :
  assumes "max_voted_round_q q (bound::nat) = Some (b::nat)"
  obtains a where "a |\<in>| q" and "vote $ a $ b \<noteq> None" and "b \<le> bound"
proof -
  from assms have "b = Max {b . \<exists> a . a |\<in>| q \<and> b \<le> bound \<and> vote $ a $ b \<noteq> None}"
    by (auto simp add:max_voted_round_q_def split:split_if_asm)
  moreover note finite_voted_bals
  moreover obtain a2 b2 where "a2 |\<in>| q \<and> b2 \<le> bound \<and> vote $ a2 $ b2 \<noteq> None"
    using assms by (auto simp add:max_voted_round_q_def) (metis option.distinct(1))
  ultimately show ?thesis using that
  by (smt Max_in empty_iff finite_nat_set_iff_bounded_le mem_Collect_eq) 
qed
 
definition max_vote where
  "max_vote q bound \<equiv>
    case max_voted_round_q q bound of
      None \<Rightarrow> None
    | Some b \<Rightarrow> 
        let max_voter = (SOME a . a |\<in>| q \<and> vote $ a $ b \<noteq> None)
        in (vote) $ max_voter $ b"

lemma max_vote_some_prop:
  assumes "max_vote q (bound::nat) = Some v"
  obtains a b\<^sub>m\<^sub>a\<^sub>x where "vote $ a $ b\<^sub>m\<^sub>a\<^sub>x = max_vote q bound" and "a |\<in>| q"
  and "\<And> a2 b2 . \<lbrakk>a2 |\<in>| q; b2 > b\<^sub>m\<^sub>a\<^sub>x; b2 \<le> bound\<rbrakk> \<Longrightarrow> vote $ a2 $ b2 = None"
  and "b\<^sub>m\<^sub>a\<^sub>x \<le> bound"
proof -
  from assms obtain b\<^sub>m\<^sub>a\<^sub>x where 0:"max_voted_round_q q bound = Some (b\<^sub>m\<^sub>a\<^sub>x::nat)"
    by (auto simp add:max_vote_def) (metis (lifting) not_None_eq option.simps(4)) 
  with max_voted_round_some obtain a where
    "a |\<in>| q" and "vote $ a $ b\<^sub>m\<^sub>a\<^sub>x \<noteq> None" and 1:"b\<^sub>m\<^sub>a\<^sub>x \<le> bound" by metis
  hence 
    "let a2 = SOME a . a |\<in>| q \<and> vote $ a $ b\<^sub>m\<^sub>a\<^sub>x \<noteq> None in a2 |\<in>| q \<and> vote $ a2 $ b\<^sub>m\<^sub>a\<^sub>x \<noteq> None"
      by (metis (mono_tags, lifting) someI_ex)
  moreover have "\<And> a2 b2 . \<lbrakk>a2 |\<in>| q; b2 \<le> bound; b2 > b\<^sub>m\<^sub>a\<^sub>x\<rbrakk> \<Longrightarrow> vote $ a2 $ b2 = None" 
    using max_voted_round_none by (metis "0" option.sel)  
  moreover have "max_vote q bound = vote $ (SOME a . a |\<in>| q \<and> vote $ a $ b\<^sub>m\<^sub>a\<^sub>x \<noteq> None) $ b\<^sub>m\<^sub>a\<^sub>x"
    using 0 by (auto simp add:max_vote_def)
  ultimately show ?thesis using that 1
    by (metis (no_types, lifting))
qed

lemma max_vote_none_prop:
  assumes "max_vote q (bound::nat) = None"
  shows "\<And> a b . \<lbrakk>a |\<in>| q; b \<le> bound\<rbrakk> \<Longrightarrow> vote $ a $ b = None"
using assms
apply (simp add:max_vote_def split add:option.split_asm)
    apply (smt max_voted_round_none)
  apply (smt max_voted_round_some not_None_eq option.simps(3) someI_ex)
done
  
definition proved_safe_at where
  "proved_safe_at Q b v \<equiv>
    case b of 0 \<Rightarrow> True
  | Suc c \<Rightarrow> (case (max_vote Q c) of (* note that here c is b-1 *)
      None \<Rightarrow> True
    | Some v' \<Rightarrow> v = v')"

definition chosen_at where
  "chosen_at v b \<equiv> \<exists> q . q |\<in>| quorums \<and> (\<forall> a . a |\<in>| q \<longrightarrow> vote $ a $ b = (Some v))"

definition chosen where
  "chosen v \<equiv> \<exists> b . chosen_at v b"
  
definition choosable where
  "choosable v b \<equiv>
    \<exists> q . q |\<in>| quorums \<and> (\<forall> a . a |\<in>| q \<longrightarrow> (
      ballot $ a > Some b \<longrightarrow> vote $ a $ b = Some v))"

definition safe_at where
  "safe_at v b \<equiv>
    (\<forall> b2 . \<forall> v2 .
      ((b2 < b \<and> choosable v2 b2) \<longrightarrow> (v = v2)))"

definition safe where
  "safe \<equiv> \<forall> b . \<forall> a . a |\<in>| acceptors \<longrightarrow> 
    (let vote = vote $ a $ b in (case vote of None \<Rightarrow> True | Some v \<Rightarrow> safe_at v b))"
  
definition well_formed where
  "well_formed \<equiv> \<forall> a b . a |\<in>| acceptors \<and> ballot $ a < b  
    \<longrightarrow> vote $ a $ (the b) = None"

end

locale ballot_array_props = ballot_array + quorums
begin

lemma "safe_at v (bot::nat)"
by (auto simp add:safe_at_def)

lemma chosen_at_is_choosable:
  assumes "chosen_at v b"
  shows "choosable v b" using assms
  by (auto simp add:chosen_at_def choosable_def)

lemma safe_at_prec:
  assumes "safe_at v b" and "b2 < b"
  shows "safe_at v b2"
  using assms by (meson order.strict_trans safe_at_def)

lemma chosen_at_same:
  assumes "chosen_at v1 b1" and "chosen_at v2 b1"
  shows "v1 = v2" 
by (metis assms chosen_at_def option.inject quorum_inter_witness)

lemma all_choosable_no_safe:
  assumes "\<And> (v::'b) . choosable v b"
  and "safe_at v (Suc b)" and "(v1::'b) \<noteq> v2"
  shows False
  by (metis assms(1) assms(2) assms(3) lessI safe_at_def) 
term vote
lemma safe_is_safe:
  assumes "safe" and "chosen v\<^sub>1" and "chosen v\<^sub>2"
  shows "v\<^sub>1 = v\<^sub>2"
  -- {* This follows the proof of Proposition 1 from "Generalized Consensus and paxos" *}
proof -
  text {* The main argument as a lemma to avoid repetitions*}
  { fix b\<^sub>1 b\<^sub>2 v\<^sub>1 v\<^sub>2
    assume 1:"chosen_at v\<^sub>1 b\<^sub>1" and 2:"chosen_at v\<^sub>2 b\<^sub>2"
    with this obtain q\<^sub>1 and q\<^sub>2 where 3:"\<And> a . a |\<in>| q\<^sub>1 \<Longrightarrow> (vote $ a $ b\<^sub>1) = (Some v\<^sub>1)" 
    and 4:"\<And> a . a |\<in>| q\<^sub>2 \<Longrightarrow> (vote) $ a  $ b\<^sub>2 = (Some v\<^sub>2)" and 5:"q\<^sub>1 |\<in>| quorums" and 6:"q\<^sub>2 |\<in>| quorums"
    by (auto simp add:chosen_at_def)
    have "v\<^sub>1 = v\<^sub>2" if "b\<^sub>1 < b\<^sub>2"
    proof -
      have 9:"choosable v\<^sub>1 b\<^sub>1" using 1 chosen_at_is_choosable by fast
      have 10:"safe_at v\<^sub>2 b\<^sub>2"
      proof -
        obtain a where "a |\<in>| q\<^sub>2" using 6 by (metis quorum_inter_witness)
        with this assms(1) 4 6 have "safe_at (the (vote $ a $ b\<^sub>2)) b\<^sub>2"
          by (metis fset_rev_mp option.case_eq_if option.distinct(1) quorums_axioms quorums_def safe_def)
        moreover have "the (vote $ a $ b\<^sub>2) = v\<^sub>2" using `a |\<in>| q\<^sub>2` 4 by force
        ultimately show ?thesis by auto
      qed
      thus ?thesis using 9 10 assms(1) that by (metis safe_at_def)
    qed }
  note main = this
  obtain b\<^sub>1 and b\<^sub>2 where 1:"chosen_at v\<^sub>1 b\<^sub>1" and 2:"chosen_at v\<^sub>2 b\<^sub>2" using assms(2,3)
  by (auto simp add:chosen_def)
  have ?thesis if "b\<^sub>1 = b\<^sub>2" by (metis "1" "2" chosen_at_same that)
  moreover
  have ?thesis if "b\<^sub>1 < b\<^sub>2" using main 1 2 that by blast
  moreover 
  have ?thesis if "b\<^sub>2 < b\<^sub>1" using main 1 2 that by blast
  ultimately show ?thesis by fastforce
qed

text {* The main lemma *}

lemma proved_safe_is_safe:
  assumes "safe" and "q |\<in>| quorums"
  and "\<And> a . a |\<in>| q \<Longrightarrow> ballot $ a \<ge> Some i"
  and "proved_safe_at q i v" and "conservative_array"
  shows "safe_at v (i::nat)"
proof (cases "i = 0")
  case True thus ?thesis
    by (metis not_less0 safe_at_def) 
next
  case False
  consider 
    (a) k a
      where "a |\<in>| q" and "vote $ a $ k = Some v" and "k < i"
      and "\<And> a\<^sub>2 l . \<lbrakk>a\<^sub>2 |\<in>| q; k < l; l < i\<rbrakk> \<Longrightarrow> vote $ a\<^sub>2 $ l = None"
  | (b) "\<And> a k . \<lbrakk>a |\<in>| q; k < i\<rbrakk>  \<Longrightarrow> vote $ a $ k = None"
  proof (cases "max_vote q (i-1)")
    case None 
    hence "\<And> a k . \<lbrakk>a |\<in>| q; k < i\<rbrakk>  \<Longrightarrow> vote $ a $ k = None" 
      using False by (metis Suc_diff_eq_diff_pred Suc_leI diff_is_0_eq gr0I max_vote_none_prop)
    thus ?thesis using that by auto
  next
    case (Some v') 
    with this obtain k a where "a |\<in>| q" and "vote $ a $ k = Some v" and "k < i"  
      and "\<And> a\<^sub>2 l . \<lbrakk>a\<^sub>2 |\<in>| q; k < l; l < i\<rbrakk> \<Longrightarrow> vote $ a\<^sub>2 $ l = None"
      using False assms(4)
      by (simp add:proved_safe_at_def)
      (smt False Nitpick.case_nat_unfold Some Suc_pred less_Suc_eq_le max_vote_some_prop option.case_eq_if option.sel option.simps(3)) 
    thus ?thesis using that by auto
  qed
  thus ?thesis
  proof (cases)
    case b
    { fix j v
      assume 1:"j < i"  and 2:"choosable v j"
      from 2 obtain q2 where 3:"q2 |\<in>| quorums" and 4:"\<And> a . a |\<in>| q2 \<Longrightarrow>
        (ballot $ a) > Some j \<Longrightarrow> vote $ a $ j = Some v"
        by (auto simp add:choosable_def)
      from 3 assms(2) obtain a where 5:"a |\<in>| q" and 6:"a |\<in>| q2"
        using quorum_inter_witness by metis
      have 9:"vote $ a $ j = Some v"
        by (metis (no_types, hide_lams) "1" "4" "5" "6" assms(3) less_def less_o.simps(4) not_le order_trans) 
      from b have False by (metis "1" "5" "9" option.distinct(1)) }
    thus ?thesis by (auto simp add:safe_at_def)
  next
    case a
    have "v' = v" if "choosable v' j" and "j < i" for j v'
    proof -
      consider (aa) "j < k" | (bb) "j = k" | (cc) "k < j" by fastforce
      hence ?thesis
      proof cases
        case aa
        have "a |\<in>| acceptors"
          by (meson a(1) assms(2) fset_rev_mp quorums_axioms quorums_def)
        hence "safe_at v k" using  assms(1)
          by (metis a(2) option.case_eq_if option.distinct(1) option.sel safe_def)
        with aa show ?thesis using that by (metis safe_at_def) 
      next
        case cc
        from that obtain q2 where 3:"q2 |\<in>| quorums" and 4:"\<And> a . a |\<in>| q2 \<Longrightarrow>
          (ballot $ a) > Some j \<Longrightarrow> vote $ a $ j = Some v'"
          by (auto simp add:choosable_def)
        from 3 assms(2) obtain a2 where 5:"a2 |\<in>| q" and 6:"a2 |\<in>| q2" 
          using quorum_inter_witness by metis
        have 8:"vote $ a2 $ j = Some v'" using 4 5 6 assms(3) that(2) 
          by (metis dual_order.strict_trans1 less_def less_o.simps(4))
        thus ?thesis by (metis "5" a(4) cc option.distinct(1) that(2)) 
      next
        case bb (* Here we need the fact that the array is conservative: *)
        have 1:"vote $ a $ k = Some v" if "a |\<in>| acceptors" and " vote $ a $ k \<noteq> None"  for a using that assms(5) 
          by (auto simp add:conservative_array_def conservative_def)
            (metis a(1) a(2) assms(2) fset_rev_mp option.inject quorums_axioms quorums_def)  
        from that obtain q2 where 3:"q2 |\<in>| quorums" and 4:"\<And> a . a |\<in>| q2 \<Longrightarrow>
          (ballot $ a) > Some j \<Longrightarrow> vote $ a $ j = Some v'"
          by (auto simp add:choosable_def)
        from 3 assms(2) obtain a2 where 5:"a2 |\<in>| q" and 6:"a2 |\<in>| q2" 
          using quorum_inter_witness by metis
        have 7:"ballot $ a2 \<ge> Some k"
          by (metis "5" a(3) assms(3) less_eq_def less_eq_o.simps(3) less_imp_le order_trans)
        have 8:"a2 |\<in>| acceptors"
          by (metis (full_types) "3" "6" fset_rev_mp quorums_axioms quorums_def)  
        have 9:"vote $ a2 $ k = Some v"
          by (metis "1" "4" "5" "6" "7" "8" assms(3) bb leD less_eq_def less_eq_o.simps(3) option.discI order.not_eq_order_implies_strict that(2))
        show ?thesis
          by (metis "4" "5" "6" "7" "9" antisym_conv2 assms(3) bb leD less_eq_def less_eq_o.simps(3) option.sel that(2)) 
      qed
      thus ?thesis by (auto simp add:safe_at_def)
    qed
    thus ?thesis
      by (metis safe_at_def) 
  qed 
qed

end

end