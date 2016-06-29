theory Quorums
imports Main 
  "~~/src/HOL/Library/FSet"
begin

locale quorums =
  fixes quorums::"'a set set"
  assumes "\<And> q1 q2 . \<lbrakk>q1 \<in> quorums; q2 \<in> quorums\<rbrakk> \<Longrightarrow> q1 \<inter> q2 \<noteq> {}"
    and "quorums \<noteq> {}"
begin

lemma quorum_inter_witness:
  assumes "q1 \<in> quorums" and "q2 \<in> quorums"
  obtains a where "a \<in> q1" and "a \<in> q2"
  using assms quorums_axioms
by (metis disjoint_iff_not_equal quorums_def) 

lemma quorums_value_same:
  assumes "q1 \<in> quorums" and "q2 \<in> quorums"
  and "\<And> a . a \<in> q1 \<Longrightarrow> f a = x"
  and "\<And> a . a \<in> q2 \<Longrightarrow> f a = y"
  shows "x = y" using assms
by (metis quorum_inter_witness) 

end 

locale card_quorums = 
  fixes acceptors
  assumes "acceptors \<noteq> {}" and "finite acceptors"
begin

definition nas where "nas \<equiv> card acceptors"

definition quorums where
  "quorums \<equiv> Set.filter (\<lambda> s . 2 * card s > nas) (Pow acceptors)"

lemma not_e:"quorums \<noteq> {}" 
proof -
  have "acceptors \<in> quorums" using card_quorums_axioms
    by (auto simp add:quorums_def nas_def card_quorums_def)
  thus ?thesis by auto
qed

lemma subset:"\<And> q . q \<in> quorums \<Longrightarrow> q \<subseteq> acceptors"
by (auto simp add:quorums_def)

lemma inter: assumes "q1 \<in> quorums" "q2 \<in> quorums"
shows "q1 \<inter> q2 \<noteq> {}"
proof -
  have 1:"2 * card q1 > nas" and 2:"q1 \<subseteq> acceptors" using assms(1) 
  by (simp_all add:quorums_def)
  moreover
  have 4:"2 * card q2 > nas" and 3:"q2 \<subseteq> acceptors" using assms(2) 
  by (simp_all add:quorums_def)
  have "card q1 + card q2 > nas"
  by (smt 1 4 add_le_imp_le_right add_left_mono add_lessD1 leD less_imp_add_positive less_le linorder_neqE_nat mult_2) 
  with 2 3 show "q1 \<inter> q2 \<noteq> {}"
  by (metis Int_Un_distrib2 card_Un_disjoint card_mono card_quorums_axioms card_quorums_def finite_subset inf.orderE inf.orderI leD nas_def) 
qed

print_locale quorums

sublocale quorums quorums
apply(unfold_locales)
  apply (metis inter)
apply (metis not_e)
done

end

end