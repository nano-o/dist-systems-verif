theory AbstractMultiPaxos2
imports Main LinorderOption "~~/src/HOL/Statespace/StateSpaceSyntax" "~~/src/HOL/Library/FSet"
begin

datatype ('v,'a,'l) p_action =
  Propose 'v
| Learn 'v 'l
| Vote 'a
| JoinBallot nat 'a
| StartBallot nat

statespace ('v,'a,'b) abs_multi_paxos_state =
  propCmd :: "'v set"
  ballot :: "'a \<Rightarrow> nat \<Rightarrow> 'b option"
  vote :: "'a \<Rightarrow> nat \<Rightarrow> 'b \<Rightarrow> 'v option"

print_locale abs_multi_paxos_state

text {* We give all the parameters in order to fix their type. Also fixed ballots to be nat. *}
locale abs_multi_paxos = abs_multi_paxos_state propCmd ballot vote project_'v_Option_option_'b_fun_Nat_nat_fun_'a_fun inject_'v_Option_option_'b_fun_Nat_nat_fun_'a_fun
            project_'b_Option_option_Nat_nat_fun_'a_fun inject_'b_Option_option_Nat_nat_fun_'a_fun project_'v_Set_set inject_'v_Set_set
            for propCmd ballot vote project_'v_Option_option_'b_fun_Nat_nat_fun_'a_fun inject_'v_Option_option_'b_fun_Nat_nat_fun_'a_fun and 
            project_'b_Option_option_Nat_nat_fun_'a_fun :: "'c \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> nat option"  and inject_'b_Option_option_Nat_nat_fun_'a_fun 
            and project_'v_Set_set::"'c \<Rightarrow> 'v set" and inject_'v_Set_set +
  fixes acceptors::"'a fset" and learners::"'l fset" and quorums::"'a fset fset"
  assumes "acceptors \<noteq> {||}"
    and "learners \<noteq> {||}"
    and "\<And> q1 q2 . \<lbrakk>q1 |\<in>| quorums; q2 |\<in>| quorums\<rbrakk> \<Longrightarrow> q1 |\<inter>| q2 \<noteq> {||}"
    and "\<And> q . q |\<in>| quorums \<Longrightarrow> q |\<subseteq>| acceptors"
    and "quorums \<noteq> {||}"
begin

definition conservative where
  "conservative s b \<equiv> \<forall> a1 . \<forall> a2 . \<forall> i . a1 |\<in>| acceptors \<and> a2 |\<in>| acceptors \<longrightarrow> (
    let v1 = (s\<cdot>vote) a1 i b; v2 = (s\<cdot>vote) a2 i b in
      (v1 \<noteq> None \<and> v2 \<noteq> None) \<longrightarrow> v1 = v2)"

definition conservative_array where
  "conservative_array r \<equiv> \<forall> b . conservative r b"

text {* Here the max is the one from Lattices_Big *}

definition max_voted_round where
  "max_voted_round s a i bound \<equiv> Max {b . (s\<cdot>vote) i a b \<noteq> None \<and> b \<le> bound}"
  
definition max_voted_round_q where
  "max_voted_round_q s i q bound \<equiv> 
    if \<exists> b a . a |\<in>| q \<and> b \<le> bound \<and> (s\<cdot>vote) a i b \<noteq> None
    then Some (Max {b . \<exists> a . a |\<in>| q \<and> b \<le> bound \<and> (s\<cdot>vote) a i b \<noteq> None})
    else None"

lemma finite_voted_bals:"finite {b . \<exists> a . a |\<in>| q \<and> b \<le> bound \<and> (s\<cdot>vote) i a b \<noteq> None}"
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
  shows "(r\<cdot>vote) a i b = None"
proof (cases "max_voted_round_q r i q bound")
case None 
  thus ?thesis using assms(1,2)
  by (auto simp add:max_voted_round_q_def split:split_if_asm)
next
  case (Some b\<^sub>m\<^sub>a\<^sub>x)
  with this obtain a2 b2 v where "a2 |\<in>| q \<and> b2 \<le> bound \<and> (r\<cdot>vote) a2 i b2 = Some v"
  by (auto simp add:max_voted_round_q_def split:split_if_asm)
  hence "{b . \<exists> a . a |\<in>| q \<and> b \<le> bound \<and>  (r\<cdot>vote) a i b \<noteq> None} \<noteq> {}" by auto
  with this obtain b2 a2 where "a2 |\<in>| q \<and> b2 \<le> bound \<and>  (r\<cdot>vote) a2 i b2 \<noteq> None"
    by auto
  moreover note finite_voted_bals
  moreover have "b > Max {b . \<exists> a . a |\<in>| q \<and> b \<le> bound \<and>  (r\<cdot>vote) a i b \<noteq> None}" using Some assms(3)
    by (auto simp add:max_voted_round_q_def split:split_if_asm)
  ultimately
  show ?thesis
    by (smt Max_ge assms(1) assms(2) finite_nat_set_iff_bounded_le leD mem_Collect_eq) 
qed

end 

end

end