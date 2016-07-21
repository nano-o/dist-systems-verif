section {* A few lemmas about Max *}

theory Max_Properties
imports Main
begin

subsection {* Max by key *}

definition max_by_key where
  "max_by_key S f \<equiv> let max_key = Max {f x | x . x \<in> S} in SOME x . x \<in> S \<and> f x = max_key"

definition max_by_key_2 where
  -- {* Executable version *} 
  "max_by_key_2 S f \<equiv> {x \<in> S . f x = Max (f ` S)}"

lemma max_by_key_ne:assumes "S \<noteq> {}" and "finite S" shows "max_by_key_2 S f \<noteq> {}" using assms
by (simp add:max_by_key_2_def) (metis (mono_tags, hide_lams) Max_in finite_imageI image_iff image_is_empty)

export_code max_by_key_2 in SML
value "max_by_key_2 {(1::nat,1),(0,3)} fst"

lemma max_by_key_2_in_and_ge:
  fixes S::"'b set" and x::'b 
  assumes "finite S" and "x \<in> S" and "m \<in> max_by_key_2 S f"
  shows "f x \<le> f m" and  "m \<in> S"
proof -
  from `finite S` have "finite (f ` S)" (is "finite ?keys") by simp
  from `x \<in> S` have "?keys \<noteq> {}" by auto
  have "f m = Max (f ` S)" by (metis (mono_tags, lifting) assms(3) max_by_key_2_def mem_Collect_eq) 
  have "m \<in> S" by (metis (no_types, lifting) assms(3) max_by_key_2_def mem_Collect_eq) 
  show "f x \<le> f m" and  "m \<in> S" by (simp add: \<open>f m = Max (f ` S)\<close> \<open>finite (f ` S)\<close> assms(2), simp add: \<open>m \<in> S\<close>)
qed

lemma in_and_ge_is_max_by_key_2: fixes S :: "'a set" and f :: "'a \<Rightarrow> ('b::linorder)"
assumes "\<And> x . x \<in> S \<Longrightarrow> f x \<le> f m" and "m \<in> S" and "finite S"
shows "m \<in> max_by_key_2 S f" using assms apply (simp add:max_by_key_2_def)
proof -
  assume a1: "\<And>x. x \<in> S \<Longrightarrow> f x \<le> f m"
  assume a2: "m \<in> S"
  assume a3: "finite S"
  obtain aa :: "'b \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a set \<Rightarrow> 'a" where
    f4: "\<forall>b. (\<forall>f A. b \<notin> f ` A \<or> aa b f A \<in> A \<and> b = f (aa b f A)) \<and> (\<forall>f A. (\<forall>a. (a::'a) \<notin> A \<or> b \<noteq> f a) \<or> b \<in> f ` A)"
    by moura
  have "finite (f ` S)"
    using a3 by simp
  then show "f m = Max (f ` S)"
    using f4 a2 a1 by (metis (no_types) Max_ge Max_in equals0D order_class.order.antisym)
qed 


lemma max_by_key_2_subsets:
  fixes Ss :: "'a set set" and f :: "'a \<Rightarrow> ('b::linorder)" and S
  assumes "\<And> S . S \<in> Ss \<Longrightarrow> finite S" and "finite Ss" and "S \<in> Ss" and "S \<noteq> {}"
  and "\<And> x y . \<lbrakk>x \<in> Union Ss; y \<in> Union Ss; f x = f y\<rbrakk> \<Longrightarrow> x = y"
  shows "max_by_key_2 (Union {max_by_key_2 S f | S . S \<in> Ss \<and> S \<noteq> {}}) f = max_by_key_2 (Union Ss) f"
proof -
  def maxs \<equiv> "Union {max_by_key_2 S f | S . S \<in> Ss \<and> S \<noteq> {}}"
  have 1:"finite maxs" 
  proof -
    have 1:"finite {max_by_key_2 S f | S . S \<in> Ss \<and> S \<noteq> {}}" using \<open>finite Ss\<close> by auto
    have 2:"\<And> S . S \<in> Ss \<Longrightarrow> finite (max_by_key_2 S f)" using \<open>\<And> S . S \<in> Ss \<Longrightarrow> finite S\<close>  by (auto simp add:max_by_key_2_def)
    show ?thesis using finite_Union[of "{max_by_key_2 S f | S . S \<in> Ss \<and> S \<noteq> {}}", OF 1] using 2 using CollectD maxs_def by blast
  qed 
  have 2:"maxs \<noteq> {}" 
  proof -
    have "max_by_key_2 S f \<noteq> {}" if "S \<in> Ss" and "S \<noteq> {}" for S using that 
      by (simp add:max_by_key_2_def) (metis (mono_tags, lifting) Max_in assms(1) finite_imageI imageE image_is_empty)
    thus ?thesis using assms(3) assms(4) using Sup_bot_conv(1) maxs_def mem_Collect_eq by auto 
  qed
  have 3:"finite (Union Ss)" using \<open>finite Ss\<close> and \<open>\<And> S . S \<in> Ss \<Longrightarrow> finite S\<close> by blast
  { fix x assume a1:"x \<in> max_by_key_2 maxs f"
    have a2:"x \<in> Union Ss" using a1 apply (simp add:max_by_key_2_def maxs_def) by (metis (no_types, lifting) mem_Collect_eq) 
    have a3:"f x \<ge> f y" if "y \<in> Union Ss" for y
    proof -
      from that obtain S where "S \<in> Ss" and "y \<in> S" by auto
      def M_S \<equiv> "max_by_key_2 S f"
      have "M_S \<noteq> {}" using \<open>y \<in> S\<close> max_by_key_ne by (metis M_S_def \<open>S \<in> Ss\<close> assms(1) equals0D) 
      have "f m_S \<ge> f y" if "m_S \<in> M_S" for m_S using \<open>S \<in> Ss\<close> \<open>y \<in> S\<close> assms(1) max_by_key_2_in_and_ge(1) that by (metis M_S_def) 
      have "M_S \<subseteq> maxs" using \<open>S \<in> Ss\<close> \<open>y \<in> S\<close> by (auto simp add:M_S_def maxs_def)
      have "f x \<ge> f m_S" if "m_S \<in> M_S" for m_S using a1 \<open>S \<in> Ss\<close> that by (metis "1" \<open>M_S \<subseteq> maxs\<close> max_by_key_2_in_and_ge(1) rev_subsetD) 
      show ?thesis by (metis \<open>M_S \<noteq> {}\<close> \<open>\<And>m_S. m_S \<in> M_S \<Longrightarrow> f m_S \<le> f x\<close> \<open>\<And>m_S. m_S \<in> M_S \<Longrightarrow> f y \<le> f m_S\<close> ex_in_conv order_trans)
    qed
    note a2 a3 }
  hence 4:"max_by_key_2 maxs f \<subseteq> max_by_key_2 (Union Ss) f" by (metis "3" in_and_ge_is_max_by_key_2 subsetI)
  { fix x assume a1:"x \<in> max_by_key_2 (Union Ss) f"
    obtain S where "S \<in> Ss" and "x \<in> S" by (metis "3" Union_iff a1 assms(3) assms(4) ex_in_conv max_by_key_2_in_and_ge(2))
    have "f x \<ge> f y" if "y \<in> S'" and "S' \<in> Ss" for y S' by (metis "3" UnionI a1 max_by_key_2_in_and_ge(1) that(1) that(2)) 
    have "x \<in> max_by_key_2 S f" by (metis \<open>S \<in> Ss\<close> \<open>\<And>y S'. \<lbrakk>y \<in> S'; S' \<in> Ss\<rbrakk> \<Longrightarrow> f y \<le> f x\<close> \<open>x \<in> S\<close> assms(1) in_and_ge_is_max_by_key_2)
    have a2:"x \<in> maxs" apply (simp add:maxs_def) by (metis \<open>S \<in> Ss\<close> \<open>x \<in> S\<close> \<open>x \<in> max_by_key_2 S f\<close> equals0D)
    have a3:"f x \<ge> f y" if "y \<in> maxs" for y using that apply (simp add:maxs_def) by (metis "3" Union_iff a1 assms(1) bot.extremum_uniqueI max_by_key_2_in_and_ge(1) max_by_key_2_in_and_ge(2) subset_emptyI) 
    note a2 a3 }
  hence 5:"max_by_key_2 (Union Ss) f \<subseteq> max_by_key_2 maxs f" by (metis "1" in_and_ge_is_max_by_key_2 subsetI) 
  from 4 5 show ?thesis using maxs_def set_eq_subset by blast
qed

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
  { have 2:"max_by_key ?maxs f \<in> ?maxs" and 3:"\<And> m . m \<in> ?maxs \<Longrightarrow> f m \<le> f (max_by_key ?maxs f)"
        apply (metis (no_types, lifting) \<open>finite {max_by_key S f |S. S \<in> Ss \<and> S \<noteq> {}}\<close> \<open>{max_by_key S f |S. S \<in> Ss \<and> S \<noteq> {}} \<noteq> {}\<close> ex_in_conv max_by_key_in_and_ge(2))
        by (metis (no_types, lifting) \<open>finite {max_by_key S f |S. S \<in> Ss \<and> S \<noteq> {}}\<close> max_by_key_in_and_ge(1))
    note 2 3 }
  note 2 = this
  { have 3:"max_by_key ?maxs f \<in> Union Ss" by (smt "1"(1) "2"(1) CollectD UnionI) 
    have 4:"\<And> x . x \<in> Union Ss \<Longrightarrow> f x \<le> f (max_by_key ?maxs f)"  using "1"(2) "2"(2) apply auto by (metis (no_types, lifting) empty_iff order_trans) 
    note 3 4 }
  thus ?thesis using in_and_ge_is_max_by_key[where ?S="Union Ss" and ?f=f] by (metis (mono_tags, lifting) \<open>finite (\<Union>Ss)\<close> assms(5)) 
qed

subsection {* Other properties *}
text {* Used anywhere? *}

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

end