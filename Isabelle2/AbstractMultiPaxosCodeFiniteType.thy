theory AbstractMultiPaxosCode
imports AbstractMultiPaxosR1
begin

text {* A attempt at using a finite type of acceptors. 
  But code-generation setup is a bit tedious... *}

print_locale amp_ioa

definition n :: nat where "n \<equiv> 3"
  -- {* The number of processes *}

typedef accs = "{1..n}" by (auto simp add:n_def)

setup_lifting type_definition_accs

lemma finite_Univ_accs:"finite (UNIV::accs set)"
apply transfer
back
back
by auto

instantiation accs :: finite
begin
instance proof
  show "finite (UNIV::accs set)" using finite_Univ_accs by simp
qed

end

instantiation accs :: equal
begin
definition equal_def:"HOL.equal (x::accs) y \<equiv> x = y"
instance 
apply (intro_classes) apply(unfold equal_def) by simp

end

lemma test[code]: "HOL.equal (x::accs) y = (Rep_accs x = Rep_accs y)" 
apply (simp add:equal_def)
by (simp add: Rep_accs_inject)

definition acc1 where "acc1 \<equiv> Abs_accs 1"
lemma acc1_code[simp, code abstract]: "Rep_accs acc1 = 1" 
apply (simp add:acc1_def)
by (simp add: Abs_accs_inverse n_def) 

definition acc2 where "acc2 \<equiv> Abs_accs 2"
lemma acc2_code[simp, code abstract]: "Rep_accs acc2 = 2" 
apply (simp add:acc2_def)
by (simp add: Abs_accs_inverse n_def)
 
definition acc3 where "acc3 \<equiv> Abs_accs 3"
lemma acc3_code[simp, code abstract]: "Rep_accs acc3 = 3" 
apply (simp add:acc3_def)
by (simp add: Abs_accs_inverse n_def) 

lemma [code_unfold]:"(UNIV::accs set) = {acc1, acc2, acc3}" 
using acc1_def acc2_def acc3_def
proof -
  have f1: "Abs_accs ` {1..n} = UNIV"
    by (meson type_definition.Abs_image type_definition_accs)
  have "{1..n} = {3, Suc (Suc 0), Suc 0}"
    by (metis (no_types) One_nat_def atLeastAtMostSuc_conv atLeastAtMost_singleton eq_numeral_Suc n_def numeral_2_eq_2 one_le_numeral pred_numeral_simps(3))
  then show ?thesis
    using f1 by (simp add: acc1_def acc2_def acc3_def insert_commute numeral_2_eq_2)
qed

definition leader where "leader b \<equiv> acc1"

definition quorums where 
  "quorums \<equiv> Set.filter (\<lambda> x . 2 * card x > card (UNIV::accs set)) (Pow (UNIV::accs set))"

print_locale amp_ioa

global_interpretation amp_ioa quorums leader 
  defines test = "amp_start" .

(* Here we would need to implement the enum type class, the equal type class for some tuples, etc. *)
export_code test in SML

end