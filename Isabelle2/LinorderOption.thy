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

instantiation option :: (preorder) "{preorder,bot}"
begin

definition less_eq_def:"o1 \<le> o2 = less_eq_o o1 o2"
definition less_def:"o1 < o2 = less_o o1 o2"
definition bot_def:"bot = None"

instance
apply(intro_classes)
apply (auto simp add:less_eq_def less_def)
apply (metis less_eq_o.simps(1) less_eq_o.simps(3) less_le_not_le less_o.elims(2))
apply (metis less_eq_o.elims(2) less_le_not_le less_o.elims(2) option.distinct(1) option.sel)
apply (metis (no_types, lifting) less_eq_o.elims(2) less_eq_o.elims(3) less_le_not_le less_o.elims(3) less_o.simps(1) less_o.simps(2) option.inject)
apply (metis less_eq_o.elims(3) less_eq_o.simps(1) option.sel order_refl)
apply (smt less_eq_o.elims(2) less_eq_o.elims(3) less_o.simps(1) less_o.simps(2) option.inject order_trans)
done

end

instantiation option :: (linorder) linorder
begin

instance 
apply(intro_classes)
apply (auto simp add:less_eq_def less_def)
apply (metis less_eq_o.elims(2) option.inject option.simps(3) order_class.order.antisym)
apply (metis le_cases less_eq_o.elims(3) less_eq_o.simps(3))
done

end

lemma gt_not_none:
  "b\<^sub>1 < (b\<^sub>2::'e::order option) \<Longrightarrow> b\<^sub>2 \<noteq> None"
by (metis less_def less_o.elims(2) option.discI)

end