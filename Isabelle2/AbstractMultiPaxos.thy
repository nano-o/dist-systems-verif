theory AbstractMultiPaxos
imports Main LinorderOption "~~/src/HOL/Library/FSet"
begin

text {* 
The use of statespaces and FinFuns hampers Sledgehammer... 
Which feature does the most?
Why not interpret the locale to get rid of the statespace before the proofs?
Why not have two versions, one with normal functions and the other with FinFuns, then prove a refinement mapping? *}

datatype ('v,'a,'l) p_action =
  Propose 'v
| Learn 'v 'l
| Vote 'a
| JoinBallot nat 'a
| StartBallot nat

record ('v,'a,'b) abs_multi_paxos_state =
  propCmd :: "'v set"
  ballot :: "'a \<Rightarrow> nat \<Rightarrow> 'b option"
  vote :: "'a \<Rightarrow> nat \<Rightarrow> 'b \<Rightarrow> 'v option"


text {* We give all the parameters in order to fix their type. Also fixed ballots to be nat. *}
locale abs_multi_paxos = 
  fixes acceptors::"'a fset" and learners::"'l fset" and quorums::"'a fset fset"
  assumes "acceptors \<noteq> {||}"
    and "learners \<noteq> {||}"
    and "\<And> q1 q2 . \<lbrakk>q1 |\<in>| quorums; q2 |\<in>| quorums\<rbrakk> \<Longrightarrow> q1 |\<inter>| q2 \<noteq> {||}"
    and "\<And> q . q |\<in>| quorums \<Longrightarrow> q |\<subseteq>| acceptors"
    and "quorums \<noteq> {||}"
begin

definition conservative where
  "conservative s b \<equiv> \<forall> a1 . \<forall> a2 . \<forall> i . a1 |\<in>| acceptors \<and> a2 |\<in>| acceptors \<longrightarrow> (
    let v1 = vote s a1 i b; v2 = vote s a2 i b in
      (v1 \<noteq> None \<and> v2 \<noteq> None) \<longrightarrow> v1 = v2)"

definition conservative_array where
  "conservative_array r \<equiv> \<forall> b . conservative r b"

text {* Here the max is the one from Lattices_Big *}

definition max_voted_round where
  "max_voted_round s a i bound \<equiv> Max {b . vote s i a b \<noteq> None \<and> b \<le> bound}"
  
definition max_voted_round_q where
  "max_voted_round_q s i q bound \<equiv> 
    if \<exists> b a . a |\<in>| q \<and> b \<le> bound \<and> vote s a i b \<noteq> None
    then Some (Max {b . \<exists> a . a |\<in>| q \<and> b \<le> bound \<and> vote s a i b \<noteq> None})
    else None"

lemma finite_voted_bals:"finite {b::nat . \<exists> a . a |\<in>| q \<and> b \<le> bound \<and> vote s i a b \<noteq> None}"
  (is "finite ?S")
proof -
  have "?S \<subseteq> {b . b \<le> bound}"
    by auto
  moreover have "finite {b . b \<le> bound}" by simp
  ultimately show ?thesis
  by (metis (no_types, lifting) finite_subset) 
qed

lemma max_voted_round_none:
  assumes "a |\<in>| q" and "(b::nat) \<le> bound" 
  and "max_voted_round_q r i q bound = None \<or> b > the (max_voted_round_q r i q bound)"
  shows "vote r a i b = None"
proof (cases "max_voted_round_q r i q bound")
case None 
  thus ?thesis using assms(1,2)
  by (auto simp add:max_voted_round_q_def split:split_if_asm)
next
  case (Some b\<^sub>m\<^sub>a\<^sub>x)
  with this obtain a2 b2 v where "a2 |\<in>| q \<and> b2 \<le> bound \<and> vote r a2 i b2 = Some v"
  by (auto simp add:max_voted_round_q_def split:split_if_asm)
  hence "{b . \<exists> a . a |\<in>| q \<and> b \<le> bound \<and>  vote r a i b \<noteq> None} \<noteq> {}" by auto
  with this obtain b2 a2 where "a2 |\<in>| q \<and> b2 \<le> bound \<and>  vote r a2 i b2 \<noteq> None"
    by auto
  moreover note finite_voted_bals
  moreover have "b > Max {b . \<exists> a . a |\<in>| q \<and> b \<le> bound \<and>  vote r a i b \<noteq> None}" using Some assms(3)
    by (auto simp add:max_voted_round_q_def split:split_if_asm)
  ultimately
  show ?thesis
    by (smt Max_ge assms(1) assms(2) finite_nat_set_iff_bounded_le leD mem_Collect_eq) 
qed

lemma max_voted_round_some :
  assumes "max_voted_round_q s i q (bound::nat) = Some (b::nat)"
  obtains a where "a |\<in>| q" and "vote s a i b \<noteq> None" and "b \<le> bound"
proof -
  from assms have "b = Max {b . \<exists> a . a |\<in>| q \<and> b \<le> bound \<and> vote s a i b \<noteq> None}"
    by (auto simp add:max_voted_round_q_def split:split_if_asm)
  moreover note finite_voted_bals
  moreover obtain a2 b2 where "a2 |\<in>| q \<and> b2 \<le> bound \<and> vote s a2 i b2 \<noteq> None"
    using assms apply (auto simp add:max_voted_round_q_def)
      by (metis (no_types, hide_lams) option.simps(3)) 
  ultimately show ?thesis using that
  by (smt Max_in empty_iff finite_nat_set_iff_bounded_le mem_Collect_eq) 
qed
 
definition max_vote where
  "max_vote s i q bound \<equiv>
    case max_voted_round_q s i q bound of
      None \<Rightarrow> None
    | Some b \<Rightarrow> 
        let max_voter = (SOME a . a |\<in>| q \<and> vote s a i b \<noteq> None)
        in vote s max_voter i b"

lemma max_vote_some_prop:
  assumes "max_vote s i q (bound::nat) = Some v"
  obtains a b\<^sub>m\<^sub>a\<^sub>x where "vote s a i b\<^sub>m\<^sub>a\<^sub>x = max_vote s i q bound" and "a |\<in>| q"
  and "\<And> a2 b2 . \<lbrakk>a2 |\<in>| q; b2 > b\<^sub>m\<^sub>a\<^sub>x; b2 \<le> bound\<rbrakk> \<Longrightarrow> vote s a2 i b2 = None"
  and "b\<^sub>m\<^sub>a\<^sub>x \<le> bound"
proof -
  from assms obtain b\<^sub>m\<^sub>a\<^sub>x where 0:"max_voted_round_q s i q bound = Some (b\<^sub>m\<^sub>a\<^sub>x::nat)"
    by (auto simp add:max_vote_def) (metis (lifting) not_None_eq option.simps(4)) 
  with max_voted_round_some obtain a where
    "a |\<in>| q" and "vote s a i  b\<^sub>m\<^sub>a\<^sub>x \<noteq> None" (is "?bmax \<noteq> None") and 1:"b\<^sub>m\<^sub>a\<^sub>x \<le> bound" by metis
  hence 
    "let a2 = SOME a . a |\<in>| q \<and> ?bmax \<noteq> None in a2 |\<in>| q \<and> ?bmax \<noteq> None"
      by (metis (mono_tags, lifting) someI_ex)
  moreover have "\<And> a2 b2 . \<lbrakk>a2 |\<in>| q; b2 \<le> bound; b2 > b\<^sub>m\<^sub>a\<^sub>x\<rbrakk> \<Longrightarrow> vote s a2 i b2 = None" 
    using max_voted_round_none by (metis "0" option.sel)  
  moreover have "max_vote s i q bound = vote s (SOME a . a |\<in>| q \<and> vote s a i b\<^sub>m\<^sub>a\<^sub>x \<noteq> None) i b\<^sub>m\<^sub>a\<^sub>x"
    using 0 by (auto simp add:max_vote_def)
  ultimately show ?thesis using that 1
    by (smt \<open>a |\<in>| q\<close> someI_ex)
qed

lemma max_vote_none_prop:
  assumes "max_vote s i q bound = None"
  shows "\<And> a (b::nat) . \<lbrakk>a |\<in>| q; b \<le> bound\<rbrakk> \<Longrightarrow> vote s a i b = None"
using assms
apply (simp add:max_vote_def split add:option.split_asm)
    apply (metis max_voted_round_none)
  apply (smt max_voted_round_some not_None_eq someI_ex)
done
  
definition proved_safe_at where
  "proved_safe_at r i Q b v \<equiv>
    case b of 0 \<Rightarrow> True
  | Suc c \<Rightarrow> (case (max_vote r i Q c) of (* note that here c is b-1 *)
      None \<Rightarrow> True
    | Some v' \<Rightarrow> v = v')"

definition chosen_at where
  "chosen_at r i v b \<equiv> \<exists> q . q |\<in>| quorums \<and> (\<forall> a . a |\<in>| q \<longrightarrow> (vote r) a i b = (Some v))"

definition chosen where
  "chosen r i v \<equiv> \<exists> b . chosen_at r i v b"
  
definition choosable where
  "choosable r i v b \<equiv>
    \<exists> q . q |\<in>| quorums \<and> (\<forall> a . a |\<in>| q \<longrightarrow> (
      (ballot r a i) > Some b \<longrightarrow> (vote r) a i b = Some v))"

definition safe_at where
  "safe_at r i v b \<equiv>
    (\<forall> b2 . \<forall> v2 .
      ((b2 < b \<and> choosable r i v2 b2) \<longrightarrow> (v = v2)))"

definition safe where
  "safe r \<equiv> \<forall> i . \<forall> b . \<forall> a . a |\<in>| acceptors \<longrightarrow> 
    (let vote = (vote r) a i b in (vote \<noteq> None \<longrightarrow> safe_at r i (the vote) b))"
  
definition well_formed where
  "well_formed r  \<equiv> \<forall> i a b . a |\<in>| acceptors \<and> (ballot r) a i < b  
    \<longrightarrow> (vote r) a i (the b) = None"

lemma "safe_at r i v (bot::nat)"
by (auto simp add:safe_at_def)

lemma chosen_at_is_choosable:
  assumes "chosen_at r i v b"
  shows "choosable r i v b" using assms
  by (auto simp add:chosen_at_def choosable_def)

lemma safe_at_prec:
  assumes "safe_at r i v (b::nat)" and "b2 < b"
  shows "safe_at r i v b2"
  using assms by (meson order.strict_trans safe_at_def)

lemma quorum_inter_witness:
  assumes "q1 |\<in>| quorums" and "q2 |\<in>| quorums"
  obtains a where "a |\<in>| q1" and "a |\<in>| q2"
  using assms abs_multi_paxos_axioms abs_multi_paxos_def
  by (metis all_not_fin_conv finter_iff)

lemma quorum_vote:
  assumes "q1 |\<in>| quorums" and "q2 |\<in>| quorums"
  and "\<And> a . a |\<in>| q1 \<Longrightarrow> vote r a i b = Some v1"
  and "\<And> a . a |\<in>| q2 \<Longrightarrow> vote r a i b = Some v2"
  shows "v1 = v2"
proof -
  obtain a where "a |\<in>| q1" and "a |\<in>| q2"
  proof -
    have "q1 |\<inter>| q2 \<noteq> {||}" using assms(1,2)
      by (metis abs_multi_paxos_axioms abs_multi_paxos_def)
    hence "\<exists> a . a |\<in>| q1 \<and> a |\<in>| q2"
      by (metis assms(1) assms(2) quorum_inter_witness) 
    with that show ?thesis by auto
  qed
  thus ?thesis using assms(3,4) by force
qed

lemma chosen_at_same:
  assumes "chosen_at r i v1 b1" and "chosen_at r i v2 b1"
  shows "v1 = v2" using quorum_vote assms
  by (auto simp add:chosen_at_def) fast

lemma all_choosable_no_safe:
  assumes "\<And> (v::'v) . choosable r i v b"
  and "safe_at r i v (Suc b)" and "(v1::'v) \<noteq> v2"
  shows False using assms 
  by (auto simp add:safe_at_def)(metis lessI)

lemma safe_is_safe:
  assumes "safe r" and "chosen r i v\<^sub>1" and "chosen r i v\<^sub>2"
  shows "v\<^sub>1 = v\<^sub>2"
  -- {* This follows the proof of Proposition 1 from "Generalized Consensus and Paxos" *}
proof -
  text {* The main argument as a lemma to avoid repetitions*}
  { fix b\<^sub>1 b\<^sub>2 v\<^sub>1 v\<^sub>2
    assume 1:"chosen_at r i v\<^sub>1 b\<^sub>1" and 2:"chosen_at r i v\<^sub>2 b\<^sub>2"
    with this obtain q\<^sub>1 and q\<^sub>2 where 3:"\<And> a . a |\<in>| q\<^sub>1 \<Longrightarrow> vote r a i b\<^sub>1 = (Some v\<^sub>1)" 
    and 4:"\<And> a . a |\<in>| q\<^sub>2 \<Longrightarrow> (vote r) a i b\<^sub>2 = (Some v\<^sub>2)" and 5:"q\<^sub>1 |\<in>| quorums" and 6:"q\<^sub>2 |\<in>| quorums"
    by (auto simp add:chosen_at_def)
    have "v\<^sub>1 = v\<^sub>2" if "b\<^sub>1 < b\<^sub>2"
    proof -
      have 9:"choosable r i v\<^sub>1 b\<^sub>1" using 1 chosen_at_is_choosable by fast
      have 10:"safe_at r i v\<^sub>2 b\<^sub>2"
      proof -
        obtain a where "a |\<in>| q\<^sub>2" using 6 by (metis quorum_inter_witness)
        with this assms(1) 4 6 have "safe_at r i (the (vote r a i b\<^sub>2)) b\<^sub>2" 
          using abs_multi_paxos_axioms abs_multi_paxos_def apply auto (* Prood reconstruction fails without calling auto first *)
            by (metis abs_multi_paxos_def fset_rev_mp option.discI option.sel safe_def)
        moreover have "the (vote r a i b\<^sub>2) = v\<^sub>2" using `a |\<in>| q\<^sub>2` 4 by force
        ultimately show ?thesis by auto
      qed
      thus ?thesis using 9 10 assms(1) that by (metis safe_at_def)
    qed }
  note main = this
  obtain b\<^sub>1 and b\<^sub>2 where 1:"chosen_at r i v\<^sub>1 b\<^sub>1" and 2:"chosen_at r i v\<^sub>2 b\<^sub>2" using assms(2,3)
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
  assumes "safe s" and "q |\<in>| quorums"
  and "\<And> a . a |\<in>| q \<Longrightarrow> ballot s a n \<ge> Some i"
  and "proved_safe_at s n q i v" and "conservative_array s"
  shows "safe_at s n v (i::nat)"
proof (cases "i = 0")
  case True thus ?thesis
    by (metis not_less0 safe_at_def) 
next
  case False
  consider 
    (a) k a
      where "a |\<in>| q" and "vote s a n k = Some v" and "k < i"
      and "\<And> a\<^sub>2 l . \<lbrakk>a\<^sub>2 |\<in>| q; k < l; l < i\<rbrakk> \<Longrightarrow> vote s a\<^sub>2 n l = None"
  | (b) "\<And> a k . \<lbrakk>a |\<in>| q; k < i\<rbrakk>  \<Longrightarrow> vote s a n k = None"
  proof (cases "max_vote s n q (i-1)")
    case None 
    hence "\<And> a k . \<lbrakk>a |\<in>| q; k < i\<rbrakk>  \<Longrightarrow> vote s a n k = None" 
      using False by (metis Suc_diff_eq_diff_pred Suc_leI diff_is_0_eq gr0I max_vote_none_prop)
    thus ?thesis using that by auto
  next
    case (Some v') 
    with this obtain k a where "a |\<in>| q" and "vote s a n k = Some v" and "k < i"  
      and "\<And> a\<^sub>2 l . \<lbrakk>a\<^sub>2 |\<in>| q; k < l; l < i\<rbrakk> \<Longrightarrow> vote s a\<^sub>2 n l = None"
      using False assms(4)
      by (simp add:proved_safe_at_def)
      (smt False Nitpick.case_nat_unfold Some Suc_pred less_Suc_eq_le max_vote_some_prop option.case_eq_if option.sel option.simps(3)) 
    thus ?thesis using that by auto
  qed
  thus ?thesis
  proof (cases)
    case b
    { fix j v
      assume 1:"j < i"  and 2:"choosable s n v j"
      from 2 obtain q2 where 3:"q2 |\<in>| quorums" and 4:"\<And> a . a |\<in>| q2 \<Longrightarrow>
        (ballot s a n) > Some j \<Longrightarrow> (vote s) a n j = Some v"
        by (auto simp add:choosable_def)
      from 3 assms(2) obtain a where 5:"a |\<in>| q" and 6:"a |\<in>| q2"
        using quorum_inter_witness by metis
      have 9:"vote s a n j = Some v"
        by (metis (no_types, hide_lams) "1" "4" "5" "6" assms(3) less_def less_o.simps(4) not_le order_trans) 
      from b have False by (metis "1" "5" "9" option.distinct(1)) }
    thus ?thesis by (auto simp add:safe_at_def)
  next
    case a
    have "v' = v" if "choosable s n v' j" and "j < i" for j v'
    proof -
      consider (aa) "j < k" | (bb) "j = k" | (cc) "k < j" by fastforce
      hence ?thesis
      proof cases
        case aa
        have "a |\<in>| acceptors"
          by (metis abs_multi_paxos_axioms abs_multi_paxos_def a(1) assms(2) fset_mp) 
        hence "safe_at s n v k" using  assms(1)
          by (metis a(2) option.discI option.sel safe_def)
        with aa show ?thesis using that by (metis safe_at_def) 
      next
        case cc
        from that obtain q2 where 3:"q2 |\<in>| quorums" and 4:"\<And> a . a |\<in>| q2 \<Longrightarrow>
          (ballot s a n) > Some j \<Longrightarrow> (vote s) a n j = Some v'"
          by (auto simp add:choosable_def)
        from 3 assms(2) obtain a2 where 5:"a2 |\<in>| q" and 6:"a2 |\<in>| q2" 
          using quorum_inter_witness by metis
        have 8:"vote s a2 n j = Some v'"
          by (metis (mono_tags, lifting) "4" "5" "6" assms(3) leD leI less_eq_def less_eq_o.simps(3) order_trans that(2)) 
        show ?thesis using a(4) 5 that(2) 8 cc by (metis option.distinct(1))
      next
        case bb (* Here we probably need the fact that the array is conservative: *)
        have 1:"vote s a n k = Some v" if "a |\<in>| acceptors" and " vote s a n k \<noteq> None"  for a using that assms(5) 
          by (auto simp add:conservative_array_def conservative_def)
            (metis (no_types, hide_lams) abs_multi_paxos_axioms abs_multi_paxos_def a(1) a(2) assms(2) option.inject order.not_eq_order_implies_strict pfsubsetD)  
        from that obtain q2 where 3:"q2 |\<in>| quorums" and 4:"\<And> a . a |\<in>| q2 \<Longrightarrow>
          (ballot s a n) > Some j \<Longrightarrow> (vote s) a n j = Some v'"
          by (auto simp add:choosable_def)
        from 3 assms(2) obtain a2 where 5:"a2 |\<in>| q" and 6:"a2 |\<in>| q2" 
          using quorum_inter_witness by metis
        have 7:"ballot s a2 n \<ge> Some k"
          by (metis "5" a(3) assms(3) less_eq_def less_eq_o.simps(3) less_imp_le order_trans)
        have 8:"a2 |\<in>| acceptors"
          by (metis "5" abs_multi_paxos_axioms abs_multi_paxos_def assms(2) order.not_eq_order_implies_strict pfsubsetD) 
        have 9:"vote s a2 n k = Some v"
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

section {* The I/O-automaton *}

end

end