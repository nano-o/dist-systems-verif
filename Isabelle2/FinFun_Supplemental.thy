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
    
declare finfun_default_const_code[simp]

end