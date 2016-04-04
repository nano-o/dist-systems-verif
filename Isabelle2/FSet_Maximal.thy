theory FSet_Maximal
imports Main "~~/src/HOL/Library/FSet"
begin

subsubsection {* Executable max *}

definition max_acc where "max_acc (f::'a \<Rightarrow> ('b::linorder)) x xs \<equiv>
  if fBex xs ((op <) (f x) o f) then xs 
  else finsert x (ffilter (\<lambda> b2 . \<not> f b2 < f x) xs)"

interpretation max_acc_commute:comp_fun_commute "max_acc f" for f
proof (unfold_locales, simp only: fun_eq_iff, rule allI)
  fix x y zs
  show "(max_acc f y \<circ> max_acc f x) zs = (max_acc f x \<circ> max_acc f y) zs"
  proof (induct zs)
    case empty thus ?case by (auto simp add: comp_def max_acc_def)
  next
    case (insert z zs) thus ?case by (auto simp add: comp_def max_acc_def)
  qed
qed

interpretation max_acc_folding:folding "max_acc f" "{||}" for f
apply unfold_locales
by (metis max_acc_commute.comp_fun_commute)

interpretation max_acc_folding_idem:folding_idem "max_acc f" "{||}" for f
proof(unfold_locales, simp only:comp_def fun_eq_iff, rule allI)
  fix x xs
  show "max_acc f x (max_acc f x xs) = max_acc f x xs"
  proof (induct xs)
    case empty thus ?case by (auto simp add:max_acc_def)
  next
    case (insert y xs) thus ?case by (auto simp add:max_acc_def)
  qed
qed       

definition max_es where 
  "max_es f xs \<equiv> Finite_Set.fold (max_acc (f::'a \<Rightarrow> ('b::linorder))) {||} xs"

lemma [code]:"max_es f (set xs) = fold (max_acc f) xs {||}"
proof -
  have "finite (set xs)" by auto
  thus ?thesis
  proof (induct xs)
    case Nil thus ?case by (simp add:max_es_def max_acc_folding.eq_fold)
  next
    case (Cons x xs) thus ?case by (simp add:max_es_def)
      (metis List.finite_set fold_commute_apply max_acc_commute.comp_fun_commute max_acc_folding.eq_fold max_acc_folding_idem.insert_idem)
  qed
qed

value "max_es snd {(1::int,1::int), (2,3::int)}"

lemma max_in_set_aux: "finite es \<Longrightarrow> x |\<in>| max_es f es \<Longrightarrow> x \<in> es"
proof (induct es arbitrary: x rule:finite_induct)
  case empty thus ?case by (simp add:max_es_def)
next
  case (insert e es) thus ?case apply (simp add:max_es_def)
  by (metis ffmember_filter finsertE max_acc_def) 
qed

lemma max_es_in_set:"x |\<in>| max_es f es \<Longrightarrow> x \<in> es"
by (metis fempty_iff max_acc_folding.eq_fold max_acc_folding.infinite max_es_def max_in_set_aux)

lemma max_acc_maxs:
  fixes xs x f 
  assumes  "finite xs" and "fBex (max_es f xs) ((op <) (f y) o f)" 
  shows "\<not> (y |\<in>| (max_es f xs))" using assms
proof (induct xs arbitrary:y rule:finite_induct)
  case (empty y) thus ?case by (simp add:max_es_def)
next
  case (insert x xs y) thus ?case
  by (smt comp_eq_dest_lhs fBexE fBexI ffmember_filter finsertE max_acc_def max_acc_folding.eq_fold max_acc_folding_idem.insert_idem max_es_def not_le order_refl)  
qed

lemma max_es_1_aux:
  fixes xs y f 
  assumes "y |\<in>| (max_es f xs)"
  shows "\<not> fBex (max_es f xs) ((op <) (f y) o f)"
by (metis assms fempty_iff max_acc_folding.eq_fold max_acc_folding.infinite max_acc_maxs max_es_def)

lemma max_es_2_aux:
fixes xs x f
assumes "finite xs" and "x \<in> xs" and "\<not> fBex (max_es f xs) ((op <) (f x) o f)"
shows "x |\<in>| (max_es f xs)" using assms
proof (induct xs arbitrary:x rule:finite_induct)
  case empty thus ?case by auto
next
  case (insert x xs) thus ?case
  by (metis finite.insertI finsert_iff insert_Diff insert_absorb2 max_acc_def max_acc_folding.eq_fold max_acc_folding_idem.insert_idem max_es_def) 
qed

lemma max_es_1:
fixes xs y f x
assumes "y |\<in>| (max_es f xs)" and "x \<in> xs" and "x \<noteq> y" 
shows "\<not> f y < f x" using assms
by (smt dual_order.strict_implies_order fBexE fBexI fempty_iff less_le_trans max_acc_folding.eq_fold max_acc_folding.infinite max_es_1_aux max_es_2_aux max_es_def o_apply)

lemma max_es_2:
fixes xs x f
assumes "finite xs" and "x \<in> xs" and "\<And> y . \<lbrakk>y \<in> xs; y \<noteq> x\<rbrakk> \<Longrightarrow> \<not> f x < f y"
shows "x |\<in>| (max_es f xs)" using assms
by (metis (mono_tags, hide_lams) comp_apply fBexE max_es_2_aux max_es_in_set)

end