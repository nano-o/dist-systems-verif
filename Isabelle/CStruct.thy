theory CStruct
imports Main
begin

locale Sequences 
begin

text {* We reverse the order of application of @{term "op #"} and 
  @{term "op @"} because it we think that it is easier to think of sequences as growing 
  to the right. *}
no_notation Cons (infixr "#" 65)
abbreviation Append  (infixl "#" 65)
  where "Append xs x \<equiv> Cons x xs"
no_notation append (infixr "@" 65)
abbreviation Concat  (infixl "@" 65)
  where "Concat xs ys \<equiv> append ys xs"

end

subsection {* The pre-CStruct locale *}

locale pre_CStruct = Sequences +
  fixes \<delta>::"'a \<Rightarrow> 'c \<Rightarrow> 'a" (infix "\<bullet>" 65)
  and bot::'a ("\<bottom>")
begin

fun exec::"'a \<Rightarrow> 'c list \<Rightarrow> 'a" (infix "\<star>" 65) where 
  "exec s Nil = s"
| "exec s (rs#r) = (exec s rs) \<bullet> r"

definition less_eq (infix "\<preceq>" 50) where
  "less_eq s s' \<equiv> \<exists> rs . s' = (s\<star>rs)"

definition less (infix "\<prec>" 50) where
  "less s s' \<equiv> less_eq s s' \<and> s \<noteq> s'"

definition is_lb where
  "is_lb s s1 s2 \<equiv> s \<preceq> s2 \<and> s \<preceq> s1"

definition is_ub where
  "is_ub s s1 s2 \<equiv> s2 \<preceq> s \<and> s1 \<preceq> s"

definition is_glb where
  "is_glb s s1 s2 \<equiv> is_lb s s1 s2 \<and> (\<forall> s' . is_lb s' s1 s2 \<longrightarrow> s' \<preceq> s)"
  
definition is_lub where
  "is_lub s s1 s2 \<equiv> is_ub s s1 s2 \<and> (\<forall> s' . is_ub s' s1 s2 \<longrightarrow> s \<preceq> s')"

definition contains where
  "contains s r \<equiv> \<exists> rs . r \<in> set rs \<and> s = (\<bottom> \<star> rs)"

definition inf  (infix "\<sqinter>" 65) where
  "inf s1 s2 \<equiv> THE s . is_glb s s1 s2"

definition sup  (infix "\<squnion>" 65) where
  "sup s1 s2 \<equiv> THE s . is_lub s s1 s2"

definition compat where
  "compat s1 s2 \<equiv> \<exists> s3 . s1 \<preceq> s3 \<and> s2 \<preceq> s3"

subsection {* Useful Lemmas in the pre-CStruct locale *}

lemma exec_cons: 
  "s \<star> (rs # r)= (s \<star> rs) \<bullet> r" by simp

lemma exec_append: 
  "(s \<star> rs) \<star> rs'  = s \<star> (rs@rs')"
by (induct rs') (simp, metis append_Cons exec_cons)

lemma trans:
  assumes "s1 \<preceq> s2" and "s2 \<preceq> s3"
  shows "s1 \<preceq> s3" using assms
    by (auto simp add:less_eq_def, metis exec_append)

lemma contains_star:
  fixes s r rs
  assumes "contains s r"
  shows "contains (s \<star> rs) r"
proof (induct rs)
  case Nil thus ?case using assms by auto
next
  case (Cons r' rs)
  with this obtain rs' where 1:"s \<star> rs = \<bottom> \<star> rs'" and 2:"r \<in> set rs'" 
    by (auto simp add:contains_def)
  have 3:"s \<star> (rs#r') = \<bottom>\<star>(rs'#r')" using 1 by fastforce
  show "contains (s \<star> (rs#r')) r" using 2 3 
    by (auto simp add:contains_def) (metis exec_cons set_rev_mp set_subset_Cons)
qed

lemma preceq_star: "s \<star> (rs#r) \<preceq> s' \<Longrightarrow> s \<star> rs \<preceq> s'"
by (metis pre_CStruct.exec.simps(1) pre_CStruct.exec.simps(2) pre_CStruct.less_eq_def trans)

end

subsection {* The CStruct locale *}

text {* Properties of CStructs. Since we are only concerned about safety we may be able
  to reduce the number of properties *}

locale CStruct = pre_CStruct +
  assumes antisym:"\<And> s1 s2 . s1 \<preceq> s2 \<and> s2 \<preceq> s1 \<Longrightarrow> s1 = s2"
    -- {* antisym implies that @{term "op \<preceq>"} is a partial order*}
  and glb_exists:"\<And> s1 s2 . \<exists> s . is_glb s s1 s2"
  and bot:"\<And> s . \<bottom> \<preceq> s"

begin

lemma inf_glb:"is_glb (s1 \<sqinter> s2) s1 s2"
proof -
  { fix s s'
    assume "is_glb s s1 s2" and "is_glb s' s1 s2"
    hence "s = s'" using antisym by (auto simp add:is_glb_def is_lb_def) }
    from this and glb_exists show ?thesis
      by (auto simp add:inf_def, metis (lifting) theI')
qed

text {* CStructs form a partial order *}

sublocale ordering less_eq less
proof
  fix s
  show "s \<preceq> s"
  by (metis exec.simps(1) less_eq_def)
next
  fix s s'
  show "s \<prec> s' = (s \<preceq> s' \<and> s \<noteq> s')" 
  by (auto simp add:less_def)
next
  fix s s'
  assume "s \<preceq> s'" and "s' \<preceq> s"
  thus "s = s'"
  using antisym by auto
next
  fix s1 s2 s3
  assume "s1 \<preceq> s2" and "s2 \<preceq> s3"
  thus "s1 \<preceq> s3"
  using trans by blast
qed

sublocale semilattice_set inf
proof
  fix s
  show "s \<sqinter> s = s" 
    using inf_glb
    by (metis antisym is_glb_def is_lb_def refl) 
next
  fix s1 s2
  show "s1 \<sqinter> s2 = (s2 \<sqinter> s1)"
    using inf_glb 
    by (smt antisym is_glb_def pre_CStruct.is_lb_def)
next
  fix s1 s2 s3
  show "(s1 \<sqinter> s2) \<sqinter> s3 = (s1 \<sqinter> (s2 \<sqinter> s3))"
    using inf_glb 
    by(auto simp add:is_glb_def is_lb_def, smt antisym trans)
qed

sublocale semilattice_order_set inf less_eq less
proof 
  fix s s'
  show "s \<preceq> s' = (s = s \<sqinter> s')"
  by (metis antisym idem inf_glb pre_CStruct.is_glb_def pre_CStruct.is_lb_def)
next
  fix s s'
  show "s \<prec> s' = (s = s \<sqinter> s' \<and> s \<noteq> s')"
  by (metis inf_glb local.antisym local.refl pre_CStruct.is_glb_def pre_CStruct.is_lb_def pre_CStruct.less_def)
qed

notation F ("\<Sqinter> _" [99])

end

end