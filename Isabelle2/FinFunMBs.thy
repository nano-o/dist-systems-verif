(* Author: Ian Roessle  *)
theory FinFunMBs
imports Main  "~~/src/HOL/Library/Monad_Syntax" "~~/src/HOL/Library/Code_Target_Nat"
  Log LinorderOption "~~/src/HOL/Library/FinFun_Syntax"
begin

primrec bl_asc :: "nat \<Rightarrow> (nat \<Rightarrow>f nat) \<Rightarrow> (nat \<Rightarrow>f nat)" where
"bl_asc 0 a = a " |
"bl_asc (Suc n) a = (let z = (bl_asc n a)((Suc n) $:= Suc n::nat) in z)"

primrec bl_dsc :: "nat \<Rightarrow> (nat \<Rightarrow>f nat) \<Rightarrow> (nat \<Rightarrow>f nat)" where
"bl_dsc 0 a = a " |
"bl_dsc (Suc n) a = (let z = (a)((Suc n) $:= Suc n::nat);z=(bl_dsc n z) in z)"

definition ff_test_asc :: "nat \<Rightarrow> (nat list)" where
  "ff_test_asc a \<equiv>
          finfun_to_list (bl_asc a (K$ 0))"
definition ff_test_dsc :: "nat \<Rightarrow> (nat list)" where
  "ff_test_dsc a \<equiv>
          finfun_to_list (bl_dsc a (K$ 0))"


definition exp_asc_hi :: "nat \<Rightarrow> (nat \<Rightarrow>f nat)" where
  "exp_asc_hi a \<equiv>
      let
          list1 = bl_asc a (K$ 0)
      in 
        (list1)"


value "bl_asc 3 (K$ 0)"
value "bl_dsc 3 (K$ 0)"
value "finfun_to_list (bl_asc 3 (K$ 0))"
value "finfun_to_list (bl_dsc 3 (K$ 0))"

export_code ff_test_dsc ff_test_asc in Scala file ""


end