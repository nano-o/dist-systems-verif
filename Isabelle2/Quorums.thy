theory Quorums
imports Main 
  "~~/src/HOL/Library/FSet"
begin

locale quorums =
  fixes acceptors::"'a fset" and quorums::"'a fset fset"
  assumes "acceptors \<noteq> {||}"
    and "\<And> q1 q2 . \<lbrakk>q1 |\<in>| quorums; q2 |\<in>| quorums\<rbrakk> \<Longrightarrow> q1 |\<inter>| q2 \<noteq> {||}"
    and "\<And> q . q |\<in>| quorums \<Longrightarrow> q |\<subseteq>| acceptors"
    and "quorums \<noteq> {||}"
begin

lemma quorum_inter_witness:
  assumes "q1 |\<in>| quorums" and "q2 |\<in>| quorums"
  obtains a where "a |\<in>| q1" and "a |\<in>| q2"
  using assms quorums_axioms
    by (meson all_not_fin_conv finter_iff quorums_def)

lemma quorums_value_same:
  assumes "q1 |\<in>| quorums" and "q2 |\<in>| quorums"
  and "\<And> a . a |\<in>| q1 \<Longrightarrow> f a = x"
  and "\<And> a . a |\<in>| q2 \<Longrightarrow> f a = y"
  shows "x = y" using assms
by (metis quorum_inter_witness) 

end

end