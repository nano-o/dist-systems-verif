theory Utils
imports Main
begin

definition option_as_set where "option_as_set x \<equiv> case x of None \<Rightarrow> {} | Some y \<Rightarrow> {y}"
  
abbreviation(input) flip where "flip f \<equiv> \<lambda> x y . f y x"
  
type_synonym bal = nat
type_synonym inst = nat

end