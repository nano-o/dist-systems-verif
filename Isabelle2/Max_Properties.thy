section {* A few lemmas about Max *}

theory Max_Properties 
imports Main LinorderOption
begin

lemma Max_Max:
  assumes "finite Xs" and "Union Xs \<noteq> {}" and "\<And> X . X \<in> Xs \<Longrightarrow> X \<noteq> {} \<and> finite X"
  shows "Max (Max ` Xs) = Max (Union Xs)" (is "?A = ?B")
nitpick[verbose, card 'a = 2, card "'a option" = 3, expect=none]
proof -
  have 0:"finite (Union Xs)" using assms(1,3) by auto
  hence 1:"?B \<in> Union Xs"
    by (metis Max_in assms(2))
  have "finite (Max ` Xs)" by (metis assms(1) finite_imageI)
  moreover have "Max ` Xs \<noteq> {}" using assms(2) by (metis Sup_empty image_is_empty) 
  ultimately have 3:"?A \<in> (Max ` Xs)" and "\<And> x . x \<in> Max ` Xs \<Longrightarrow> x \<le> ?A"
    by (metis Max_in, metis Max_ge \<open>finite (Max ` Xs)\<close>)
  show ?thesis by (smt 1 3 Max_ge Max_mono Sup_upper UnionE 0 antisym assms(1,3) finite_imageI image_iff) 
qed

lemma Max_bot:"\<lbrakk>finite (S::'b::{linorder,order_bot} set); S \<noteq> {}; s \<in> S; Max S = bot\<rbrakk> \<Longrightarrow> s = bot"
by (metis Max.coboundedI bot.extremum_uniqueI)

lemma max_insert_none:
  fixes S :: "'b::linorder option set"
  assumes "S \<noteq> {}" and "finite S"
  shows "Max (insert None S) = Max S"
using bot_def Max_insert assms bot.extremum max_def by metis

lemma Some_Max_commute:
  fixes S::"'b::linorder set" assumes "S \<noteq> {}" and "finite S"
  shows "Max (Some ` S) = Some (Max S)"
proof -
  have "mono (Some::('b::linorder \<Rightarrow> 'b option))" 
  proof (auto simp add:mono_def)
    fix x y :: "'b::linorder"
    assume "x \<le> y"
    thus "Some x \<le> Some y"
      by (metis less_eq_def less_eq_o.simps(3)) 
  qed
  thus ?thesis
  by (metis assms(1) assms(2) mono_Max_commute) 
qed

end