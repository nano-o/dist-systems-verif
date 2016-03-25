(* Author: Ian Roessle  *)
theory FinFunMBs
imports "~~/src/HOL/Main"  "~~/src/HOL/Library/Monad_Syntax" "~~/src/HOL/Nat"
"~~/src/HOL/Library/FinFun_Syntax" "~~/src/HOL/Library/Code_Target_Numeral"
begin

(*
fun is_in_list where
  "is_in_list x [] = False"
| "is_in_list x (y#xs) = (if x = y then True else is_in_list x xs)"

definition (in linorder) insort_insert_key2 :: "('b \<Rightarrow> 'a) \<Rightarrow> 'b \<Rightarrow> 'b list \<Rightarrow> 'b list" where
"insort_insert_key2 f x xs =
  (if is_in_list (f x) (map f xs) then xs else insort_key f x xs)"

hide_const insort_insert

abbreviation "insort_insert \<equiv> insort_insert_key2 (\<lambda>x. x)"
*)

(* Builds a finfun in ascending order 
  inputs:
    i1: size::nat The number of elements in insert
  outputs: 
    o1: thefinfun::(nat \<Rightarrow>f nat) The resultant finfun
*)
primrec bl_asc :: "nat \<Rightarrow> (nat \<Rightarrow>f nat)" where
"bl_asc 0  = (K$ 0) " |
"bl_asc (Suc n) = (let z = (bl_asc n)((Suc n) $:= Suc n::nat) in z)"

definition bl_asc_2 :: "nat \<Rightarrow> (nat \<Rightarrow>f nat)" where
  "bl_asc_2 n \<equiv> fold (\<lambda> i ff . ff(i $:= i)) [1..<(n+1)] (K$ 0)"

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

definition bl_dsc_2 :: "nat \<Rightarrow> (nat \<Rightarrow>f nat)" where
  "bl_dsc_2 n \<equiv> foldr (\<lambda> i ff . ff(i $:= i)) [1..<(n+1)] (K$ 0)"

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
definition mb1a :: "nat \<Rightarrow> (nat list)" where
  "mb1a a \<equiv>
          finfun_to_list (bl_asc a )"
definition mb1b :: "nat \<Rightarrow> (nat list)" where
  "mb1b a \<equiv>
          finfun_to_list (bl_dsc a )"

(* Micro benchmark #2
 Builds an assending finfun of input size and repeat_count. 

Accesses either the front 10 or end 10 elements, of inputted repeat count.
*)
(* Front access *)
definition mb2a :: "(nat \<Rightarrow>f nat) \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow>f nat)" where
  "mb2a ary repeat \<equiv>
        (let
            array=access_range_x ary 10 9 repeat
          in 
          array)"           
(* Tail access*) 

definition mb2b :: " (nat \<Rightarrow>f nat) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow>f nat)" where
  "mb2b ary sz repeat \<equiv>
        (let
            array=access_range_x ary sz 9 repeat
          in 
          array)"           

(* runs experiment 1a on increasing array sizes.
This function is copied and timer code added on the scala side 

For now it's important that (end-start)%step == 0. This ensures that the first element is the start element.
Expected behavior for when this isn't true is that the last element wouldn't match the end element. 
This performs correctly but instead the first element doesn't match.

list_asc:
  Input 1: start element
  Input 2: end element
  Input 3: step size
*)

fun list_asc_offset :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat list" where
"list_asc_offset n 0 offset = [] " |
"list_asc_offset 0 (Suc s) offset  = [] " |
"list_asc_offset (Suc n) (Suc s) offset  = (list_asc_offset (n-s) (Suc s) offset)@[(Suc n)+offset]"
definition list_asc :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat list" where
  "list_asc start end step \<equiv> list_asc_offset (end-start+1) step (start-1)" 

definition exp_stub :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat list" where
  "exp_stub start stop step \<equiv> 
   (let
            array = list_asc 100 1500 100
          in 
          array)"     


abbreviation test :: "nat \<Rightarrow>f nat \<Rightarrow> (nat)"
  where "test \<equiv> finfun_rec(\<lambda> (d::nat) . (0))  
    (\<lambda> k v r . if (v \<noteq> 1) 
      then (r+1) else r)"

definition t2 :: " (nat \<Rightarrow>f nat) \<Rightarrow>  (nat)" where
  "t2 f \<equiv>
   (let
            ary = (K$ 0);
            ary = finfun_update ary 1 1;
            ary = finfun_update ary 2 0;
            ary = test ary
          in 
          ary)"     

value "t2 f"

definition build_ff_filter :: " (nat \<Rightarrow>f nat) \<Rightarrow>  nat \<Rightarrow> (nat \<Rightarrow>f nat)" where
  "build_ff_filter ff_in filterval \<equiv>
   (let
            ary = (K$ 0);
            ary = finfun_update_code ary 1 1;
            ary = finfun_update_code ary 2 2;
            ary = finfun_update_code ary 3 3

            
          in 
          ary)"     



value "bl_asc 2"
value "bl_dsc 3"
value "build_ff_filter a b"
value "finfun_to_list (bl_asc 3)"
value "finfun_to_list (bl_dsc 3)"


text {* Serializing finfuns to lists *}

abbreviation serialize_c where
  "serialize_c d \<equiv> ({}, d)"
abbreviation serialize_u_2 where
  "serialize_u_2 a b r \<equiv>  if b = snd r then r else (
    let x = {(a,b)} \<union> (fst r) - {(a,x) | x . True} in (
      if {fst p | p . p \<in> x} = UNIV
      then ({}, b) 
      else (x, snd r) ) )"
abbreviation serialize_u where
  "serialize_u a b r \<equiv>  if b = snd r then r else (
    let x = {(a,b)} \<union> (fst r) - {(a,x) | x . True} in  (x, snd r) )"

definition serialize_finfun_2 where
  "serialize_finfun_2 \<equiv> finfun_rec serialize_c serialize_u"

interpretation finfun_rec_wf_aux serialize_c serialize_u
apply (unfold_locales)
apply simp
apply force
apply force
done

definition test_c where "test_c d \<equiv> (d,{})" (* d is the default element as a passthrough *)
definition test_u where "test_u k v r \<equiv>
  if v = fst r
  then (if (k \<in> snd r) then (fst r, snd r - {k}) else r)
  else (
    if (k \<in> snd r)
      then r
      else (fst r, {k} \<union> snd r) )"
definition test where "test \<equiv> finfun_rec test_c test_u"
interpretation test:finfun_rec_wf_aux test_c test_u 
apply (unfold_locales)
apply (simp_all add:test_c_def test_u_def)
apply (smt Diff_insert_absorb fst_conv insertCI insert_Diff insert_Diff_if insert_is_Un singletonD snd_conv)
done

thm test.finfun_rec_upd 

print_codeproc
code_thms test

lemma finfun_rec_upd2 [simp,code]:
  "finfun_rec test_c test_u (finfun_update_code f a' b') = finfun_rec test_c test_u (f(a' $:= b'))"
  
apply auto
done


(*  "finfun_rec cnst upd (f(a' $:= b')) = upd a' b' (finfun_rec cnst upd f)" *)

lemma finfun_rec_upd3 [code]:
  "finfun_rec test_c test_u (finfun_update_code f a' b') = test_u a' b' (finfun_rec test_c test_u f)"
apply(simp only:finfun_rec_upd2) using test.finfun_rec_upd
apply (simp only:test.finfun_rec_upd)
done


value "test ((K$ (0::nat))::nat \<Rightarrow>f nat)( 0 $:=42)"

definition serialize_finfun  where
  "serialize_finfun ff = fold (\<lambda> k l . (k, ff $ k)#l) (finfun_to_list ff) []"

value "serialize_finfun (((K$ (1::nat))(2$:=3)):: nat \<Rightarrow>f nat)"

value "serialize_finfun ((K$ (1::nat)):: nat \<Rightarrow>f nat)"

definition deserialize_finfun where
  "deserialize_finfun l \<equiv> foldr (\<lambda> kv r . finfun_update_code r (fst kv) (snd kv)) l (K$ None)"


export_code access_x access_range_x mb1a mb1b mb2a mb2b list_asc_offset list_asc exp_stub in Scala file "bench.scala"


end