section {* A few lemmas about Max *}

theory Max_Properties 
imports Main LinorderOption
begin

lemma Max_Max:
  assumes "finite Xs" and "Union Xs \<noteq> {}" and "\<And> X . X \<in> Xs \<Longrightarrow> X \<noteq> {} \<and> finite X"
  shows "Max (Max ` Xs) = Max (Union Xs)" (is "?A = ?B")
  -- {* Is this of any use? Note that all subsets are required to be non-empty. *}
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

subsection {* Max by key *}

definition max_by_key where
  "max_by_key S f \<equiv>
    let max_key = Max {f x | x . x \<in> S}
    in SOME x . x \<in> S \<and> f x = max_key"

lemma max_by_key_in_and_ge: fixes S::"'b set" and x::'b assumes "finite S" and "x \<in> S"
  shows "f x \<le> f (max_by_key S f)" and "max_by_key S f \<in> S"
nitpick[verbose, card 'b = 3, card "'b option" = 4, card 'c = 3, card "'c option" = 4, expect=none]
proof -
  from `finite S` have "finite {f x | x . x \<in> S}" (is "finite ?keys") by simp
  from `x \<in> S` have "?keys \<noteq> {}" by auto
  let ?some = "SOME x . x \<in> S \<and> f x = Max {f x | x . x \<in> S}"
  from `?keys \<noteq> {}` have "?some \<in> S" and "f ?some = Max {f x | x . x \<in> S}"
    apply (smt Max_in \<open>finite {f x |x. x \<in> S}\<close> mem_Collect_eq someI_ex)
    by (smt Max_in \<open>finite {f x |x. x \<in> S}\<close> \<open>{f x |x. x \<in> S} \<noteq> {}\<close> mem_Collect_eq someI_ex) 
  have "\<And> k . k \<in> ?keys \<Longrightarrow> k \<le> Max ?keys" and "Max ?keys \<in> ?keys" using `finite ?keys` and `?keys \<noteq> {}`
    apply auto using Max_in by auto
  show "f x \<le> f (max_by_key S f)" and "max_by_key S f \<in> S" 
    apply (auto simp add:max_by_key_def)
    using Max.coboundedI \<open>f (SOME x. x \<in> S \<and> f x = Max {f x |x. x \<in> S}) = Max {f x |x. x \<in> S}\<close> \<open>finite {f x |x. x \<in> S}\<close> assms(2) apply auto[1]
    using \<open>(SOME x. x \<in> S \<and> f x = Max {f x |x. x \<in> S}) \<in> S\<close> by blast 
qed

lemma in_and_ge_is_max_by_key: fixes S :: "'a set" and f :: "'a \<Rightarrow> ('b::linorder)"
  assumes "\<And> x . x \<in> S \<Longrightarrow> f x \<le> f m" and "m \<in> S" and "finite S" and "\<And> x y . \<lbrakk>x \<in> S; y \<in> S; x \<noteq> y\<rbrakk> \<Longrightarrow> f x \<noteq> f y"
  shows "m = max_by_key S f" 
nitpick[verbose,  card 'a = 4, card 'b =6, card "'b option" = 30, expect = none]
proof (rule ccontr) 
  assume "m \<noteq> max_by_key S f" (is "m \<noteq> ?m'")
  have "\<And> x . x \<in> S \<Longrightarrow> f x \<le> f ?m'" and "?m' \<in> S"
    apply (metis assms(3) max_by_key_in_and_ge(1)) by (metis assms(2) assms(3) max_by_key_in_and_ge(2)) 
  hence "f m = f ?m'" by (metis assms(1) assms(2) dual_order.antisym) 
  thus False by (metis \<open>m \<noteq> max_by_key S f\<close> \<open>max_by_key S f \<in> S\<close> assms(2) assms(4)) 
qed

lemma max_by_key_subsets:
  fixes Ss :: "'a set set" and f :: "'a \<Rightarrow> ('b::linorder)" and S
  assumes "\<And> S . S \<in> Ss \<Longrightarrow> finite S" and "finite Ss" and "S \<in> Ss" and "S \<noteq> {}"
  and "\<And> x y . \<lbrakk>x \<in> Union Ss; y \<in> Union Ss; f x = f y\<rbrakk> \<Longrightarrow> x = y"
  shows "max_by_key {max_by_key S f | S . S \<in> Ss \<and> S \<noteq> {}} f = max_by_key (Union Ss) f" 
nitpick[ card 'a = 3, card 'b = 3, card "'b option" = 4, expect=none] 
proof -
  let ?maxs = "{max_by_key S f | S . S \<in> Ss \<and> S \<noteq> {}}"
  have "finite ?maxs" using \<open>finite Ss\<close> by auto
  have "?maxs \<noteq> {}" using \<open>S \<in> Ss\<close> and \<open>S \<noteq> {}\<close> by blast
  have "finite (Union Ss)" using \<open>finite Ss\<close> and \<open>\<And> S . S \<in> Ss \<Longrightarrow> finite S\<close> by blast
  { fix S
    assume "S \<in> Ss" and "S \<noteq> {}"
    have 1:"max_by_key S f \<in> S" by (metis \<open>S \<in> Ss\<close> \<open>S \<noteq> {}\<close> assms(1) ex_in_conv max_by_key_in_and_ge(2))
    have 2:"\<And> x . x \<in> S \<Longrightarrow> f x \<le> f (max_by_key S f)" by (metis \<open>S \<in> Ss\<close> assms(1) max_by_key_in_and_ge(1))
    note 1 2 }
  note 1 = this
  { { fix x assume "x \<in> ?maxs"
        obtain S where "S \<in> Ss" and "S \<noteq> {}" and "x = max_by_key S f" using \<open>x \<in> {max_by_key S f |S. S \<in> Ss \<and> S \<noteq> {}}\<close> by blast 
        with 1 have "x \<in> S" by (meson all_not_in_conv assms(1) max_by_key_in_and_ge(2))
        hence "x \<in> Union Ss" using \<open>S \<in> Ss\<close> by blast }
      note 4 = this
      have 2:"max_by_key ?maxs f \<in> ?maxs" and 3:"\<And> m . m \<in> ?maxs \<Longrightarrow> f m \<le> f (max_by_key ?maxs f)"
        apply (metis (no_types, lifting) \<open>finite {max_by_key S f |S. S \<in> Ss \<and> S \<noteq> {}}\<close> \<open>{max_by_key S f |S. S \<in> Ss \<and> S \<noteq> {}} \<noteq> {}\<close> ex_in_conv max_by_key_in_and_ge(2))
        by (metis (no_types, lifting) \<open>finite {max_by_key S f |S. S \<in> Ss \<and> S \<noteq> {}}\<close> max_by_key_in_and_ge(1))
    note 2 3 }
  note 2 = this
  { have 3:"max_by_key ?maxs f \<in> Union Ss" by (smt "1"(1) "2"(1) CollectD UnionI) 
    have 4:"\<And> x . x \<in> Union Ss \<Longrightarrow> f x \<le> f (max_by_key ?maxs f)"  using "1"(2) "2"(2) apply auto by (metis (no_types, lifting) empty_iff order_trans) 
    note 3 4 }
  thus ?thesis using in_and_ge_is_max_by_key[where ?S="Union Ss" and ?f=f] by (metis (mono_tags, lifting) \<open>finite (\<Union>Ss)\<close> assms(5)) 
qed

end