(* Author: Ian Roessle  *)
theory FinFunMBs
imports Main  "~~/src/HOL/Library/Monad_Syntax" "~~/src/HOL/Library/Code_Target_Nat"  "~~/src/HOL/Library/Nat"
 "~~/src/HOL/Library/FinFun_Syntax"
begin

(* Builds a finfun in ascending order 
  inputs:
    i1: size::nat The number of elements in insert
  outputs: 
    o1: thefinfun::(nat \<Rightarrow>f nat) The resultant finfun
*)
primrec bl_asc :: "nat \<Rightarrow> (nat \<Rightarrow>f nat)" where
"bl_asc 0  = (K$ 0) " |
"bl_asc (Suc n) = (let z = (bl_asc n)((Suc n) $:= Suc n::nat) in z)"


(* Builds a finfun in descending order 
  inputs:
    i1: size::nat The number of elements in insert
  outputs: 
    o1: thefinfun::(nat \<Rightarrow>f nat) The resultant finfun
*)
primrec bl_dsc_sub :: "nat \<Rightarrow> (nat \<Rightarrow>f nat) \<Rightarrow> (nat \<Rightarrow>f nat)" where
"bl_dsc_sub  0 a = a " |
"bl_dsc_sub (Suc n) a = (let z = (a)((Suc n) $:= Suc n::nat);z=(bl_dsc_sub n z) in z)"
definition bl_dsc :: "nat \<Rightarrow> (nat \<Rightarrow>f nat)" where
    "bl_dsc n \<equiv>  bl_dsc_sub n (K$ 0)"


(*Access a key in a finfun repeatedly
  inputs:
    i1: finfun::(nat \<Rightarrow>f nat) The input finfun
    i2: key::nat The key
    i3: repeat::nat The repeat count
*)
primrec access_x :: " (nat \<Rightarrow>f nat) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
"access_x a i 0  = a $ i" |
"access_x a i (Suc n) = (let z = a $ i; z=(access_x a i n) in z)"

(*Access a range of keys in a finfun repeatedly
  inputs:
    i1: finfun::(nat \<Rightarrow>f nat) The input finfun
    i2: end::nat The last element index to access 
    i3: count::nat The range of elements to access (scans in descending order, does count+1 elements)
    i4: repeat::nat The number of times to repeatedly access the same element.
 *)
primrec access_range_x :: "(nat \<Rightarrow>f nat) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow>f nat)" where 
   "access_range_x a end 0 repeat =   
      (let
          z = access_x a end repeat
      in 
        a)"  |
   "access_range_x a end (Suc n) repeat =   
      (let
          z = access_x a end repeat;
          x = end-1;
          p = access_range_x a x n repeat 
      in 
        a)"

(* Micro benchmark #1
  Functions to build a finfun of inputted size in ascending and descending orders. These functions 
need to be timed with increasing input size and plotted

*)
definition ff_test_asc :: "nat \<Rightarrow> (nat list)" where
  "ff_test_asc a \<equiv>
          finfun_to_list (bl_asc a )"
definition ff_test_dsc :: "nat \<Rightarrow> (nat list)" where
  "ff_test_dsc a \<equiv>
          finfun_to_list (bl_dsc a )"

(* Micro benchmark #2
 Builds an assending finfun of input size. 
Accesses either the front 10 or end 10 elements, of inputted repeat count.

*)
definition mb2_frontaccess :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow>f nat)" where
  "mb2_frontaccess sz repeat \<equiv>
        (let
            array = bl_asc sz;
            array=access_range_x array 10 9 repeat
          in 
          array)"           

definition mb2_endaccess :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow>f nat)" where
  "mb2_endaccess sz repeat \<equiv>
        (let
            array = bl_asc sz;
            array=access_range_x array sz 9 repeat
          in 
          array)"           


value "bl_asc 3"
value "bl_dsc 3"
value "finfun_to_list (bl_asc 3)"
value "finfun_to_list (bl_dsc 3)"

export_code access_x access_range_x mb2_endaccess mb2_frontaccess ff_test_dsc ff_test_asc in Scala file ""


end