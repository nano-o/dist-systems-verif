theory AbstractMultiPaxos
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

text {* We give all the parameters in order to fix their type. *}
locale abs_multi_paxos = abs_multi_paxos_state propCmd ballot vote project_'v_Option_option_'b_fun_Nat_nat_fun_'a_fun inject_'v_Option_option_'b_fun_Nat_nat_fun_'a_fun
            project_'b_Option_option_Nat_nat_fun_'a_fun inject_'b_Option_option_Nat_nat_fun_'a_fun project_'v_Set_set inject_'v_Set_set 
for propCmd and ballot and vote and project_'v_Option_option_'b_fun_Nat_nat_fun_'a_fun :: "'b \<Rightarrow> 'c \<Rightarrow> nat \<Rightarrow> 'd \<Rightarrow> 'e option" and inject_'v_Option_option_'b_fun_Nat_nat_fun_'a_fun
            and project_'b_Option_option_Nat_nat_fun_'a_fun and inject_'b_Option_option_Nat_nat_fun_'a_fun and project_'v_Set_set and inject_'v_Set_set::"'e set \<Rightarrow> 'b" +
  fixes acceptors::"'c fset" and learners::"'l fset" and quorums::"'c fset fset"
  assumes "acceptors \<noteq> {||}"
    and "learners \<noteq> {||}"
    and "\<And> q1 q2 . \<lbrakk>q1 |\<in>| quorums; q2 |\<in>| quorums\<rbrakk> \<Longrightarrow> q1 |\<inter>| q2 \<noteq> {||}"
    and "\<And> q . q |\<in>| quorums \<Longrightarrow> q |\<subseteq>| acceptors"
    and "quorums \<noteq> {||}"
begin

term "s\<cdot>vote"

definition conservative where
  "conservative s b \<equiv> \<forall> a1 . \<forall> a2 . \<forall> i . a1 |\<in>| acceptors \<and> a2 |\<in>| acceptors \<longrightarrow> (
    let v1 = (s\<cdot>vote) a1 i b; v2 = (s\<cdot>vote) a2 i b in 
      (v1 \<noteq> None \<and> v2 \<noteq> None) \<longrightarrow> v1 = v2)"

end

end