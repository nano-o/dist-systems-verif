section {* A C-Struct for one-shot consensu *}

theory Consensus
imports CStruct
begin

text {* This theory provides a model for the C-Struct locale, thus showing 
  that the assumption of the C-Struct locale are consistent. *}

locale Consensus
begin

fun \<delta>::"'v option \<Rightarrow> 'v \<Rightarrow> 'v option" (infix "\<bullet>" 65) where
  "\<delta> None r = Some r"
| "\<delta> (Some v) r = Some v"

interpretation pre_CStruct \<delta> None .
notation exec (infix "\<star>" 65)
notation less_eq (infix "\<preceq>" 50 )
notation None ("\<bottom>")

lemma single_use:
  fixes r rs
  shows  "\<bottom> \<star> ([r]@rs) = Some r" 
proof (induct rs)
  case Nil
  thus ?case by simp
next
  case (Cons r rs)
  thus ?case by auto
qed

lemma bot: "\<exists> rs . s = \<bottom> \<star> rs"
proof (cases s)
  case None thus ?thesis 
    by (metis exec.simps(1))
next
  case (Some v) thus ?thesis 
    by (metis Consensus.single_use)
qed

lemma prec_eq_None_or_equal:
fixes s1 s2
assumes "s1 \<preceq> s2"
shows "s1 = None \<or> s1 = s2" using assms single_use
  by (metis less_eq_def not_None_eq pre_CStruct.exec.simps(1) pre_CStruct.exec_append)

lemma compat2_bot:
assumes "compat2 s1 s2"
shows "s1 = \<bottom> \<or> s2 = \<bottom> \<or> s1 = s2"
  using assms 
by (auto simp add: compat2_def less_eq_def)
(metis Consensus.prec_eq_None_or_equal assms(1) compat2_def option.distinct(1))

lemma compat_bot1:
assumes "compat {s1,s2,s3}" and "s1 \<noteq> \<bottom>"
shows "s1 \<noteq> \<bottom> \<Longrightarrow> (\<And> s . s \<in> {s2,s3} \<Longrightarrow> s = \<bottom> \<or> s = s1)"
using compat2_bot assms
   by (metis insertCI local.compat_def)

lemma compat_bot2:
assumes "compat {s1,s2,s3}" and "s1 \<noteq> \<bottom>"
shows "s1 = \<bottom> \<Longrightarrow> s2 = \<bottom> \<or> s3 = \<bottom> \<or> s2 = s3"
using compat2_bot assms by metis

lemma sup_bot_bot:"sup \<bottom> \<bottom> = \<bottom>"
apply(simp add:sup_def is_lub_def is_ub_def)
apply(rule the_equality[where a="\<bottom>"])
  subgoal by (smt pre_CStruct.exec.simps(1) pre_CStruct.less_eq_def)
  subgoal by (smt Consensus.prec_eq_None_or_equal pre_CStruct.exec.simps(1) pre_CStruct.less_eq_def)
done

lemma sup_bot1:
assumes "s1 = \<bottom>"
shows "sup s1 s2 = s2" using assms
apply(simp add:sup_def is_lub_def is_ub_def)
apply(rule the_equality[where a="s2"])
  subgoal by (metis Consensus.bot pre_CStruct.exec.simps(1) pre_CStruct.less_eq_def)
  subgoal by (metis Consensus.prec_eq_None_or_equal exec.simps(1) pre_CStruct.less_eq_def)
done

lemma sup_bot2:
assumes "s2 = \<bottom>"
shows "sup s1 s2 = s1" using assms 
apply(simp add:sup_def is_lub_def is_ub_def)
apply(rule the_equality[where a="s1"])
  subgoal by (metis Consensus.bot pre_CStruct.exec.simps(1) pre_CStruct.less_eq_def)
  subgoal by (metis Consensus.prec_eq_None_or_equal exec.simps(1) pre_CStruct.less_eq_def)
done

lemma sup_not_bot:
assumes "s1 \<noteq> \<bottom>" and "s2 \<noteq> \<bottom>" and "compat2 s1 s2"
shows "sup s1 s2 = s1"
proof -
  from assms have "s1 = s2"
    by (metis Consensus.compat2_bot) 
  thus ?thesis
    apply(simp add:sup_def is_lub_def is_ub_def)
    apply(rule the_equality[where a="s2"])
      subgoal by (metis Consensus.prec_eq_None_or_equal assms(1) less_bullet)
      subgoal by (metis Consensus.prec_eq_None_or_equal assms(2))
    done
qed  

lemma sup_cons:
assumes "compat2 s1 s2"
shows "(s1 = s2 \<and> sup s1 s2 = s1) \<or> (s1 = \<bottom> \<and> sup s1 s2 = s2) \<or> (s2 = \<bottom> \<and> sup s1 s2 = s1)"
by (metis Consensus.compat2_bot Consensus.sup_bot1 Consensus.sup_bot2 Consensus.sup_not_bot assms)

interpretation CStruct \<delta> \<bottom>
apply (unfold_locales)
  subgoal using Consensus.prec_eq_None_or_equal by auto
  subgoal 
    apply (simp add:is_glb_def is_lb_def) 
    apply (metis Consensus.bot Consensus.prec_eq_None_or_equal pre_CStruct.less_eq_def)
    done
  subgoal
    by (metis Consensus.prec_eq_None_or_equal bot.extremum empty_set is_glb_def pre_CStruct.exec.simps(1) pre_CStruct.is_lb_def sup.cobounded2) 
  subgoal
    by (metis Consensus.bot pre_CStruct.less_eq_def) 
  subgoal 
    apply (simp add:compat2_def is_lub_def is_ub_def)
    by (metis Consensus.prec_eq_None_or_equal \<open>\<And>s. \<bottom> \<preceq> s\<close>)
  subgoal
    by (metis (no_types, lifting) Consensus.sup_cons insertCI insert_absorb2 local.compat_def)
done

end

end