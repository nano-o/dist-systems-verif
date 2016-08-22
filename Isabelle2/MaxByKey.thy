chapter {* Maximals elements over a set. *}

text {* Maximal elements over a set of elements whose position in a linear order is given by 
an auxiliary function *}

theory MaxByKey
imports Main
begin

context begin

definition max_by_key :: "'a set \<Rightarrow> ('a \<Rightarrow> 'b::linorder) \<Rightarrow> 'a set" where
  -- {* @{term max_by_key} is executable *}
  "max_by_key S f \<equiv> {x \<in> S . f x = Max (f ` S)}"

lemma fixes X::"nat set" assumes "finite X" and "X \<noteq> {}"
  obtains a where "a \<in> X" and "\<And> x . \<lbrakk>x \<in> X; x \<noteq> a\<rbrakk> \<Longrightarrow> x < a"
  by (metis Max_ge Max_in assms(1) assms(2) le_neq_implies_less) 
  
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

lemma max_by_key_ne:assumes "S \<noteq> {}" and "finite S" shows "max_by_key S f \<noteq> {}" using assms
by (simp add:max_by_key_def) (metis (mono_tags, hide_lams) Max_in finite_imageI image_iff image_is_empty)

export_code max_by_key in SML
value "max_by_key {(1::nat,1),(0,3)} fst"

lemma max_by_key_in_and_ge:
  fixes S::"'b set" and x::'b 
  assumes "finite S" and "x \<in> S" and "m \<in> max_by_key S f"
  shows "f x \<le> f m" and  "m \<in> S"
proof -
  from `finite S` have "finite (f ` S)" (is "finite ?keys") by simp
  from `x \<in> S` have "?keys \<noteq> {}" by auto
  have "f m = Max (f ` S)" by (metis (mono_tags, lifting) assms(3) max_by_key_def mem_Collect_eq) 
  have "m \<in> S" by (metis (no_types, lifting) assms(3) max_by_key_def mem_Collect_eq) 
  show "f x \<le> f m" and  "m \<in> S" by (simp add: \<open>f m = Max (f ` S)\<close> \<open>finite (f ` S)\<close> assms(2), simp add: \<open>m \<in> S\<close>)
qed

lemma in_and_ge_is_max_by_key: fixes S :: "'a set" and f :: "'a \<Rightarrow> ('b::linorder)"
assumes "\<And> x . x \<in> S \<Longrightarrow> f x \<le> f m" and "m \<in> S" and "finite S"
shows "m \<in> max_by_key S f" using assms apply (simp add:max_by_key_def)
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

lemma max_by_key_finite: 
  assumes "finite S" and "S \<noteq> {}"
  shows "finite (max_by_key S f)"
   by (metis all_not_in_conv assms(1) assms(2) infinite_super max_by_key_in_and_ge(2) subsetI)
    
lemma max_by_key_lemma: 
  assumes "finite S1" and "finite S2"  and "S1 \<noteq> {}" and "S2 \<noteq> {}"
  shows "max_by_key (max_by_key S1 f \<union> max_by_key S2 f) f = max_by_key (S1 \<union> S2) f" 
    (is "?m (?m S1 f \<union> ?m S2 f) f = ?m (S1 \<union> S2) f")
proof 
  show "?m (?m S1 f \<union> ?m S2 f) f \<subseteq> ?m (S1 \<union> S2) f"
  proof -
    have "?m (?m S1 f \<union> ?m S2 f) f \<subseteq> (S1 \<union> S2)"
      by (smt Un_iff max_by_key_def mem_Collect_eq subsetI)
    have "f y \<le> f x" if "x \<in> ?m (?m S1 f \<union> ?m S2 f) f" and "y \<in> S1 \<union> S2" for x y
    proof -
      have 1:"f z \<le> f x" if "z \<in> ?m S1 f \<union> ?m S2 f" for z
        by (metis \<open>x \<in> max_by_key (max_by_key S1 f \<union> max_by_key S2 f) f\<close> assms(1) assms(2) assms(3) assms(4) finite_UnI max_by_key_finite max_by_key_in_and_ge(1) that) 
      have 2:"f z \<le> f a" if "z \<in> S1" and "a \<in> ?m S1 f" for z a
        by (metis assms(1) max_by_key_in_and_ge(1) that(1) that(2)) 
      have 3:"f z \<le> f a" if "z \<in> S2" and "a \<in> ?m S2 f" for z a
        by (metis assms(2) max_by_key_in_and_ge(1) that(1) that(2))
      show ?thesis using that 1 2 3
        by (metis Un_iff all_not_in_conv assms(1) assms(2) max_by_key_ne order_trans)
    qed
    show ?thesis
      by (smt \<open>\<And>y x. \<lbrakk>x \<in> max_by_key (max_by_key S1 f \<union> max_by_key S2 f) f; y \<in> S1 \<union> S2\<rbrakk> \<Longrightarrow> f y \<le> f x\<close> \<open>max_by_key (max_by_key S1 f \<union> max_by_key S2 f) f \<subseteq> S1 \<union> S2\<close> assms(1) assms(2) contra_subsetD finite_UnI in_and_ge_is_max_by_key subsetI)        
  qed
  show "?m (S1 \<union> S2) f \<subseteq> ?m (?m S1 f \<union> ?m S2 f) f"
    by (smt Collect_empty_eq Un_iff assms(1) assms(2) assms(3) assms(4) finite_UnI max_by_key_def max_by_key_finite max_by_key_in_and_ge(1) max_by_key_ne mem_Collect_eq order_class.order.antisym subsetI) 
qed    
    
private
lemma f_Union_f_is_f_Union:
  assumes "\<And> S1 S2 . \<lbrakk>finite S1; finite S2; S1 \<noteq> {}; S2 \<noteq> {}\<rbrakk> \<Longrightarrow> f (f S1 \<union> f S2) = f (S1 \<union> S2)"
  and "\<And> S . S \<in> Ss \<Longrightarrow> finite S" and "{} \<notin> Ss" and "finite Ss" and "Ss \<noteq> {}"
  and "\<And> S . \<lbrakk>finite S; S \<noteq> {}\<rbrakk> \<Longrightarrow> finite (f S) \<and> f S \<noteq> {}"
shows "f (Union (f ` Ss)) = f (Union Ss)"
proof -
  show ?thesis using \<open>finite Ss\<close> and \<open>Ss \<noteq> {}\<close> assms(2-5)
  proof (induct "Ss" rule:finite_ne_induct)
    case (singleton x)
    have "finite x"
      by (metis singleton.prems(1) singletonI)
    have "x \<noteq> {}"
      by (metis Pow_bottom Pow_empty singleton.prems(2)) 
    show ?case using \<open>x \<noteq> {}\<close> \<open>finite x\<close> apply simp
      by (metis Un_absorb assms(1)) 
  next
    case (insert x F)
    have 1:"f (\<Union>a\<in>F. f a) = f (\<Union>F)"
      by (metis insert.hyps(1) insert.hyps(2) insert.hyps(4) insert.prems(1) insert.prems(2) insertI2) 
    have 4:"f (f x \<union> f (\<Union>F)) = f (x \<union> \<Union>F)"
      by (metis Sup_insert assms(1) finite.cases finite_Union insert.hyps(1) insert.hyps(2) insert.prems(1) insert.prems(2) insertCI sup_eq_bot_iff)  
    have "f (\<Union>a\<in>insert x F. f a) = f (f x \<union> (\<Union>a\<in>F . f a))"
      by (metis Union_image_insert)
    also have "... = f (f x \<union> f (\<Union> F))" using assms(1)[of "f x" "f (\<Union> F)"]
      by (smt "1" "4" SUP_bot_conv(1) Sup_bot_conv(2) Un_absorb assms(1) assms(6) finite_UN_I insert.hyps(1) insert.prems(1) insert.prems(2) insertI1 insertI2 sup_bot.right_neutral)
    also have "... = f (\<Union> (insert x F))"
      by (metis "4" Union_insert) 
    finally show ?case by assumption
  qed
qed
  
lemma max_by_key_subsets:
  assumes "\<And> S . S \<in> Ss \<Longrightarrow> finite S" and "{} \<notin> Ss" and "finite Ss" and "Ss \<noteq> {}"
  shows "max_by_key (\<Union>S\<in>Ss. max_by_key S f) f = max_by_key (Union Ss) f"
  using f_Union_f_is_f_Union[where ?f="\<lambda> S . max_by_key S f" and ?Ss=Ss]
  by (metis (mono_tags, lifting) assms max_by_key_finite max_by_key_lemma max_by_key_ne) 

end 

subsection {* Other properties *}

context begin

text {* Used anywhere? *}

private
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

private
lemma Max_bot:"\<lbrakk>finite (S::'b::{linorder,order_bot} set); S \<noteq> {}; s \<in> S; Max S = bot\<rbrakk> \<Longrightarrow> s = bot"
by (metis Max.coboundedI bot.extremum_uniqueI)

end 

end