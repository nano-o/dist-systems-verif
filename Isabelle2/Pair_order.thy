theory Pair_order
imports Main
begin

section {* Ordering on pairs *}

fun less_eq_pair_2 where
  "less_eq_pair_2 (x,y) (u,v) = (y \<le> v)"

fun less_pair_2 where 
  "less_pair_2 (x,y) (u,v) = (y < v)"

fun less_eq_pair_1 where
  "less_eq_pair_1 (x,y) (u,v) = (x \<le> u)"

fun less_pair_1 where 
  "less_pair_1 (x,y) (u,v) = (x < u)"

instantiation prod :: (type,order_bot) "{preorder,bot}"
begin

definition less_eq_def: "less_eq x y = less_eq_pair_2 x y"
definition less_def: "less x y = less_pair_2 x y"

instance
apply(intro_classes)
apply (auto simp add:less_eq_def less_def)
done

end

end