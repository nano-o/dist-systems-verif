theory FinFun_Supplemental
imports "~~/src/HOL/Library/FinFun"
begin

unbundle finfun_syntax

context includes lifting_syntax
begin

lemma finfun_Diag_transfer[transfer_rule]:
  "((pcr_finfun A B) ===> (pcr_finfun A C) ===> (pcr_finfun A (rel_prod B C))) 
    (\<lambda> f g  x . (f x, g x)) (\<lambda> ff gg . ($ ff, gg $))" 
  unfolding  OO_def pcr_finfun_def cr_finfun_def rel_prod_conv rel_fun_def
  by auto

lemma finfun_comp_transfer[transfer_rule]:
  shows "((B ===> C) ===> (pcr_finfun A B) ===> (pcr_finfun A C))
    (\<lambda> f1 g . f1 o g) (\<lambda> f2 gg . f2 o$ gg)"
  unfolding  OO_def pcr_finfun_def cr_finfun_def rel_prod_conv rel_fun_def by auto

end

lemma finfun_default_determined:
  fixes f::"'c \<Rightarrow> 'd" and  b B
  defines "B \<equiv> {a. f a \<noteq> b}"
  assumes infin: "\<not> finite (UNIV :: 'c set)" and fin:"finite B"
  shows "(THE b. finite {a. f a \<noteq> b}) = b"
proof -
  from fin show ?thesis unfolding B_def
  proof(elim the_equality)
    fix b'
    assume "finite {a. f a \<noteq> b'}" (is "finite ?B'")
    with infin fin have "UNIV - (?B' \<union> B) \<noteq> {}" using finite_subset by auto
    then obtain a where a: "a \<notin> ?B' \<union> B" by auto
    thus "b' = b" by (auto simp add:B_def)
  qed
qed

lemma comp_default:
  fixes ff :: "'c \<Rightarrow>f 'd" and f
  assumes infin:"infinite (UNIV::'c set)"
  shows "finfun_default (f o$ ff) = f (finfun_default ff)"
  apply transfer apply (simp add:finfun_default_aux_def finfun_def)
  subgoal premises prems for f ff
  proof - 
    from \<open>\<exists>b. finite {a. ff a \<noteq> b}\<close> obtain b where "finite {a. ff a \<noteq> b}"
      by auto
    hence 1:"(THE b. finite {a. ff a \<noteq> b}) = b" using infin by (auto simp add: finfun_default_determined)
    let ?b' = "f b"
    have "finite {a. f (ff a) \<noteq> ?b'}" using \<open>finite {a. ff a \<noteq> b}\<close>
      by (metis (mono_tags, lifting) Collect_mono finite_subset)
    hence 2:"(THE b. finite {a. f (ff a) \<noteq> b}) = ?b'" using infin by (auto simp add: finfun_default_determined)
    from 1 2 infin show ?thesis by blast
  qed
  done

lemma diag_default:
  assumes "finfun_default (ff1::'c \<Rightarrow>f 'd) = d1" 
  and "finfun_default (ff2::'c \<Rightarrow>f 'e) = d2"
  and infin:"infinite (UNIV::'c set)"
  shows "finfun_default ($ ff1, ff2 $) = (d1,d2)" using assms 
  apply (transfer)
  apply (auto simp add:finfun_default_aux_def finfun_def)
  subgoal premises prems for f1 f2 b1 b2
  proof -
    thm prems
    from \<open>finite {a. f1 a \<noteq> b1}\<close> and \<open>finite {a. f2 a \<noteq> b2}\<close>
    have 1:"(THE b . finite {a. f1 a \<noteq> b}) = b1" and 2:"(THE b . finite {a. f2 a \<noteq> b}) = b2"
      using infin
      by (auto simp add: finfun_default_determined)
    let ?b = "(b1,b2)"
    have "finite {a. (f1 a, f2 a) \<noteq> ?b}" (is "finite ?S")
    proof -
      have "?S = {a. f1 a \<noteq> b1} \<union> {a. f2 a \<noteq> b2}" by blast
      thus ?thesis using \<open>finite {a. f1 a \<noteq> b1}\<close> and \<open>finite {a. f2 a \<noteq> b2}\<close> by simp
    qed
    thus ?thesis using 1 2 infin by (auto simp add:finfun_default_determined)
  qed
  done
    
text {* Why not do this with @{term finfun_rec}? *}
lift_definition my_comp :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> ('a \<Rightarrow>f 'b) \<Rightarrow> ('a \<Rightarrow>f 'c option)"
  is "\<lambda> f ff . \<lambda> x . if finfun_dom ff $ x then Some (f x (ff $ x)) else None"
  apply (auto simp add:finfun_def)
  by (smt Abs_finfun_inverse Collect_cong finfun_dom_def finfun_dom_finfunI finite_finfun_default option.distinct(1)) 

lemma my_comp_default[simp]:
  assumes "\<not> finite (UNIV::'c set)"
  fixes f::"'c \<Rightarrow> 'd \<Rightarrow> 'b" and ff::"'c \<Rightarrow>f 'd"
  shows "finfun_default (my_comp f ff) = None"
proof (transfer)
  fix f::"'c \<Rightarrow> 'd \<Rightarrow> 'b" and ff :: "'c \<Rightarrow>f 'd"
  let ?comp = "\<lambda>x. if finfun_dom ff $ x then Some (f x (ff $ x)) else None"
  have "finite {x . ?comp x \<noteq> None}"
    using finite_finfun_dom by fastforce
  hence "(THE b . finite {x . ?comp x \<noteq> b}) = None" using finfun_default_determined[OF assms, 
        where ?b=None and ?f="?comp"] by auto
  thus "finfun_default_aux (\<lambda>x. if finfun_dom ff $ x then Some (f x (ff $ x)) else None) = None" 
    using assms by (simp add:finfun_default_aux_def)
qed

lemma my_comp_dom[simp]:
  assumes "\<not> finite (UNIV::'c set)"
  fixes f::"'c \<Rightarrow> 'd \<Rightarrow> 'b" and ff::"'c \<Rightarrow>f 'd"
  shows "finfun_dom (my_comp f ff) = finfun_dom ff" using my_comp_default[OF assms, of f ff]
  apply (auto simp add:finfun_dom_def my_comp_def)
proof -
  { fix cc :: 'c and bb :: 'b
    { assume "\<exists>f. my_comp f ff $ cc \<noteq> (None::'b option)"
      then have "\<exists>fa c fb. ff $ cc \<noteq> finfun_default ff \<and> fa $ (c::'c) \<noteq> (finfun_default fa::'d) \<and> my_comp f ff $ cc = my_comp fb fa $ c"
        by (metis finfun_dom_conv my_comp.rep_eq) }
    then have "Abs_finfun (\<lambda>c. \<exists>b. Abs_finfun (\<lambda>c. if Abs_finfun (\<lambda>c. ff $ c \<noteq> finfun_default ff) $ c then Some (id f c (id ff $ c)) else None) $ c = Some b) = Abs_finfun (\<lambda>c. ff $ c \<noteq> finfun_default ff) \<or> (\<exists>b. Abs_finfun (\<lambda>c. if Abs_finfun (\<lambda>c. ff $ c \<noteq> finfun_default ff) $ c then Some (id f c (id ff $ c)) else None) $ cc = Some b) \<and> ff $ cc \<noteq> finfun_default ff \<or> ff $ cc = finfun_default ff \<and> Abs_finfun (\<lambda>c. if Abs_finfun (\<lambda>c. ff $ c \<noteq> finfun_default ff) $ c then Some (id f c (id ff $ c)) else None) $ cc \<noteq> Some bb"
      by (metis (no_types) finfun_dom_conv finfun_dom_def id_apply my_comp.abs_eq my_comp.rep_eq option.distinct(1)) }
  then show "Abs_finfun (\<lambda>c. \<exists>b. Abs_finfun (\<lambda>c. if Abs_finfun (\<lambda>c. ff $ c \<noteq> finfun_default ff) $ c then Some (id f c (id ff $ c)) else None) $ c = Some b) = Abs_finfun (\<lambda>c. ff $ c \<noteq> finfun_default ff)"
    by meson
qed

lift_definition finfun_dom_2 :: "('a \<Rightarrow>f 'b) \<Rightarrow> ('a \<Rightarrow>f bool)"
  is "\<lambda> ff . \<lambda> a . ff $ a \<noteq> finfun_default ff" 
  using FinFun.finfun_dom_finfunI by assumption
  
declare finfun_default_const_code[simp]

end