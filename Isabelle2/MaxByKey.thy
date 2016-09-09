chapter {* Maximals elements over a set. *}

text {* Maximal elements over a set of elements whose position in a linear order is given by 
an auxiliary function. *}

theory MaxByKey
imports Main
begin

context begin

definition max_by_key :: "'a set \<Rightarrow> ('a \<Rightarrow> 'b::linorder) \<Rightarrow> 'a set" where
  -- {* @{term max_by_key} is executable *}
  "max_by_key S f \<equiv> {x \<in> S . f x = Max (f ` S)}"
  
lemma max_by_key:
  assumes "finite S" 
  shows "max_by_key S f = {x \<in> S . \<forall> y \<in> S  . f y \<le> f x}"
  apply (auto simp add:max_by_key_def)
   apply (metis Max.coboundedI assms finite_imageI rev_image_eqI)
  by (metis (mono_tags, hide_lams) Max_eqI assms finite_imageI image_iff)
  
lemma max_by_key_ordered:
  fixes S::"'a set" and f::"'a \<Rightarrow> 'b::linorder"
  assumes "\<And> x y . \<lbrakk>x \<in> S; y \<in> S; x \<noteq> y\<rbrakk> \<Longrightarrow> f x \<noteq> f y" and "finite S" and "S \<noteq> {}"
  obtains z where "max_by_key S f = {z}"
proof -
  have "Max (f ` S) \<in> f ` S"
    by (metis Max_in assms(2,3) finite_imageI image_is_empty)
  with this obtain z where "f z = Max (f ` S)" and "z \<in> S"
    by (metis imageE)
  have "{x \<in> S . f x = Max (f ` S)} = {z}" 
  proof 
    show "{z} \<subseteq> {x \<in> S. f x = Max (f ` S)}" using \<open>f z = Max (f ` S)\<close> \<open>z \<in> S\<close> by auto
  next
    show "{x \<in> S. f x = Max (f ` S)} \<subseteq> {z}"
      by (metis (mono_tags, lifting) \<open>f z = Max (f ` S)\<close> \<open>z \<in> S\<close> assms(1) mem_Collect_eq singleton_iff subsetI)
  qed
  thus ?thesis using that by (simp add:max_by_key_def)
qed

lemma max_by_key_ne:
  assumes "S \<noteq> {}" and "finite S" 
  shows "max_by_key S f \<noteq> {}" using assms
by (simp add:max_by_key_def) (metis (mono_tags, hide_lams) Max_in finite_imageI image_iff image_is_empty)

export_code max_by_key in SML
value "max_by_key {(1::nat,1),(0,3)} fst"

private
lemma max_by_key_in_and_ge:
  fixes S::"'b set" and x::'b 
  assumes "finite S" and "x \<in> S" and "m \<in> max_by_key S f"
  shows "f x \<le> f m" and  "m \<in> S"
   apply (metis (no_types, lifting) assms(1) assms(2) assms(3) max_by_key mem_Collect_eq)
  by (metis (no_types, lifting) CollectD assms(3) max_by_key_def) 

private
lemma in_and_ge_is_max_by_key: fixes S :: "'a set" and f :: "'a \<Rightarrow> ('b::linorder)"
assumes "\<And> x . x \<in> S \<Longrightarrow> f x \<le> f m" and "m \<in> S" and "finite S"
shows "m \<in> max_by_key S f" by (smt assms max_by_key mem_Collect_eq) 

lemma max_by_key_finite: 
  assumes "finite S"
  shows "finite (max_by_key S f)" using assms 
  by (simp add:max_by_key[OF assms])
    
private
lemma max_by_key_lemma: 
  assumes "finite S1" and "finite S2"
  shows "max_by_key (max_by_key S1 f \<union> max_by_key S2 f) f = max_by_key (S1 \<union> S2) f" 
    (is "?m (?m S1 \<union> ?m S2) = ?m (S1 \<union> S2)")
proof 
  have "finite (S1 \<union> S2)" and "finite (max_by_key S1 f \<union> max_by_key S2 f)"
     by (simp add: assms, simp add: assms max_by_key_finite) 
  show "?m (?m S1 \<union> ?m S2) \<subseteq> ?m (S1 \<union> S2)"
  proof -
    define lhs where "lhs \<equiv> ?m (?m S1 \<union> ?m S2)"
    have "lhs \<subseteq> (S1 \<union> S2)" by (auto simp add:max_by_key_def lhs_def)
    moreover
    have "f y \<le> f x" if 1:"x \<in> lhs" and "y \<in> S1 \<union> S2" for x y
    proof -
      have 1:"f z \<le> f x" if "z \<in> ?m S1 \<union> ?m S2" for z
        by (metis (no_types, lifting) CollectD 1 assms(1) assms(2) finite_UnI max_by_key max_by_key_finite that lhs_def)
      have 2:"f z \<le> f a" if "z \<in> S1" and "a \<in> ?m S1" for z a
        using assms(1) max_by_key that(1) that(2) by auto 
      have 3:"f z \<le> f a" if "z \<in> S2" and "a \<in> ?m S2" for z a
        using assms(2) max_by_key that(1) that(2) by auto
      show ?thesis using that 1 2 3
        by (metis Un_iff all_not_in_conv assms(1) assms(2) max_by_key_ne order_trans)
    qed
    ultimately
    have "lhs \<subseteq> ?m (S1 \<union> S2)" by (auto simp add: max_by_key[OF \<open>finite (S1 \<union> S2)\<close>])
    thus ?thesis by (simp add:lhs_def)
  qed
  show "?m (S1 \<union> S2) \<subseteq> ?m (?m S1 \<union> ?m S2)"
    by (smt Un_iff assms(1) assms(2) finite_UnI max_by_key max_by_key_finite mem_Collect_eq subsetI)
qed
    
private
lemma f_Union_f_is_f_Union:
  assumes "\<And> S1 S2 . \<lbrakk>finite S1; finite S2\<rbrakk> \<Longrightarrow> f (f S1 \<union> f S2) = f (S1 \<union> S2)"
  and "\<And> S . S \<in> Ss \<Longrightarrow> finite S" and "finite Ss"
  and "\<And> S . finite S \<Longrightarrow> finite (f S)"
shows "f (Union (f ` Ss)) = f (Union Ss)"
proof (cases "Ss = {}")
  case False
  show ?thesis using \<open>finite Ss\<close> and False assms(2-4)
  proof (induct "Ss" rule:finite_ne_induct)
    case (singleton x)
    have "finite x"
      by (metis singleton.prems(1) singletonI)
    show ?case using \<open>finite x\<close> assms(1) by fastforce 
  next
    case (insert x F)
    have 1:"f (\<Union>a\<in>F. f a) = f (\<Union>F)"
      by (simp add: insert.hyps(1) insert.hyps(4) insert.prems(1) insert.prems(3)) 
    have 4:"f (f x \<union> f (\<Union>F)) = f (x \<union> \<Union>F)"
      using assms(1) insert.prems(1) insert.prems(2) by auto
    have "f (\<Union>a\<in>insert x F. f a) = f (f x \<union> (\<Union>a\<in>F . f a))"
      by (metis Union_image_insert)
    also have "... = f (f x \<union> f (\<Union> F))"
      by (metis (no_types, lifting) "1" Un_absorb assms(1) finite_UN_I insert.hyps(1) insert.prems(1) insert.prems(3) insert_iff)
    also have "... = f (\<Union> (insert x F))"
      by (metis "4" Union_insert) 
    finally show ?case by assumption
  qed
next
  case True thus ?thesis by simp
qed 

lemma max_by_key_subsets:
  assumes "\<And> S . S \<in> Ss \<Longrightarrow> finite S" and "finite Ss"
  shows "max_by_key (\<Union>S\<in>Ss. max_by_key S f) f = max_by_key (Union Ss) f"
  by (metis (no_types, lifting) assms f_Union_f_is_f_Union max_by_key_finite max_by_key_lemma) 

end 

subsection {* Other properties *}

experiment begin

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

end