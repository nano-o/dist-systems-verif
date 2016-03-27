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

definition nas where "nas \<equiv> fcard acceptors"

definition mp_quorums where
  "mp_quorums \<equiv> ffilter (\<lambda> s . 2 * fcard s > nas) (fPow acceptors)"

lemma assumes "q1 |\<in>| mp_quorums" "q2 |\<in>| mp_quorums"
shows "q1 |\<inter>| q2 \<noteq> {||}"
proof -
  have 1:"2 * fcard q1 > nas" and 2:"q1 |\<subseteq>| acceptors" using assms(1) 
  by (simp_all add:mp_quorums_def)
  moreover
  have 4:"2 * fcard q2 > nas" and 3:"q2 |\<subseteq>| acceptors" using assms(2) 
  by (simp_all add:mp_quorums_def)
  have "fcard q1 + fcard q2 > nas"
  by (smt 1 4 add_le_imp_le_right add_left_mono add_lessD1 leD less_imp_add_positive less_le linorder_neqE_nat mult_2) 
  with 2 3 show "q1 |\<inter>| q2 \<noteq> {||}"
  by (metis fcard_funion_disjoint fcard_mono leD le_sup_iff nas_def) 
qed

end

end