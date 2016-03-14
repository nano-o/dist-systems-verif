theory LinorderOption
imports Main
begin
section {* nat option as a linear order *}

fun less_eq_o where 
  "less_eq_o None _ = True"
| "less_eq_o (Some x) None = False"
| "less_eq_o (Some x) (Some y) = (x \<le> y)"

fun less_o where
  "less_o None None = False" 
| "less_o None _ = True"
| "less_o (Some x) None = False"
| "less_o (Some x) (Some y) = (x < y)"

instantiation option :: (linorder) linorder
begin

definition less_eq_def:"o1 \<le> o2 = less_eq_o o1 o2"
definition less_def:"o1 < o2 = less_o o1 o2"

instance 
apply(intro_classes)
apply (auto simp add:less_eq_def less_def)
apply (metis le_cases less_eq_o.elims(3) less_o.elims(2) less_o.simps(1) less_o.simps(2) not_le option.inject)
apply (metis less_eq_o.elims(2) less_o.elims(2) less_o.simps(1) less_o.simps(2) not_le option.inject)
apply (metis less_eq_o.elims(3) less_o.simps(2) less_o.simps(4) not_le)
apply (metis less_eq_o.elims(3) less_eq_o.simps(1) option.sel order_refl)
apply (smt less_eq_o.elims(2) less_eq_o.elims(3) less_o.simps(1) less_o.simps(2) option.inject order_trans)
apply (metis dual_order.antisym less_eq_o.elims(2) less_eq_o.simps(2) option.inject)
by (metis le_cases less_eq_o.elims(3) option.discI option.inject)

end

lemma gt_not_none:
  "b\<^sub>1 < (b\<^sub>2::'e::linorder option) \<Longrightarrow> b\<^sub>2 \<noteq> None"
by (metis less_def less_o.elims(2) option.discI)

end