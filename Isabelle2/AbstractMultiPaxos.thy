theory AbstractMultiPaxos4
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

section {* The I/O-automaton *}

end

end