theory FinFun_Supplemental
imports "~~/src/HOL/Library/FinFun_Syntax" "~~/src/HOL/Library/FSet"
begin

subsection {* The domain of a finfun as an fset, using finfun_rec *}

text {* Note that CARD is executable in card_UNIV *}

definition finfun_fset_dom_c :: "'b \<Rightarrow> 'b \<times> ('a :: card_UNIV) fset"
  where "finfun_fset_dom_c d \<equiv> if CARD('a) = 0 then (d,{||}) else undefined"
definition finfun_fset_dom_u :: "('a :: card_UNIV) \<Rightarrow> 'b \<Rightarrow>'b \<times> 'a fset \<Rightarrow> 'b \<times> 'a fset" where 
  "finfun_fset_dom_u k v r \<equiv> if CARD('a) = 0 then (
    if v = fst r
    then (if (k |\<in>| snd r) then (fst r, snd r |-|  {|k|}) else r)
    else (
      if (k |\<in>| snd r)
        then r
        else let s = {|k|} |\<union>| snd r in (fst r, s)))
  else undefined"

interpretation finfun_fset_dom_wf_aux:finfun_rec_wf_aux finfun_fset_dom_c finfun_fset_dom_u
apply (unfold_locales)
apply (simp add:finfun_fset_dom_c_def finfun_fset_dom_u_def)
apply (simp add:finfun_fset_dom_c_def finfun_fset_dom_u_def Let_def)
apply (metis fdoubleton_eq_iff finsert_absorb finsert_absorb2 finsert_fminus_if fminus_finsert2)
apply (simp add:finfun_fset_dom_c_def finfun_fset_dom_u_def Let_def)
done

interpretation finfun_fset_dom_wf:finfun_rec_wf finfun_fset_dom_c "finfun_fset_dom_u::('a :: card_UNIV) \<Rightarrow> 'b \<Rightarrow>'b \<times> 'a fset \<Rightarrow> 'b \<times> 'a fset"
proof (unfold_locales)
  assume finite:"finite (UNIV::'a set)"
  hence "CARD('a) \<noteq> 0" by simp
  fix b b' :: 'b
  interpret comp_fun_commute "\<lambda>a. finfun_fset_dom_u a b'" 
    by (unfold_locales) (auto simp add:finfun_fset_dom_u_def finfun_fset_dom_c_def)
  show "Finite_Set.fold (\<lambda> (a::'a). finfun_fset_dom_u a b')
          (finfun_fset_dom_c b) UNIV = finfun_fset_dom_c b'" using finite
  by (auto simp add:finfun_fset_dom_u_def finfun_fset_dom_c_def)
   (metis UNIV_not_empty \<open>CARD('a) \<noteq> 0\<close> finfun_fset_dom_u_def finite.cases fold_insert_remove)
qed

definition finfun_fset_dom_aux where [code del]: 
  "finfun_fset_dom_aux \<equiv> finfun_rec finfun_fset_dom_c finfun_fset_dom_u"

lemma finfun_fset_dom_aux:
  shows "CARD('a) = 0 \<Longrightarrow> let r = finfun_fset_dom_aux ff in 
  ((a::'a::card_UNIV) |\<in>| snd r = (ff $ a \<noteq> finfun_default ff)) \<and> fst r = finfun_default ff"
apply (induct arbitrary:a rule:finfun_weak_induct) 
    apply (simp add:finfun_fset_dom_aux_def Let_def finfun_fset_dom_c_def)
  apply (metis finfun_default_const_code)
  apply (simp add:finfun_fset_dom_aux_def Let_def finfun_fset_dom_u_def finfun_fset_dom_c_def)
  apply (metis finfun_default_update_const finfun_upd_apply)
done

definition finfun_fset_dom where "finfun_fset_dom \<equiv> snd o finfun_fset_dom_aux"

lemma  finfun_fset_dom:
  shows "CARD('a) = 0 \<Longrightarrow> (a::'a::card_UNIV) |\<in>| finfun_fset_dom ff = (ff $ a \<noteq> finfun_default ff)"
  by (simp add: comp_def finfun_fset_dom_def) (metis finfun_fset_dom_aux)

lemma finfun_fset_dom_aux_upd [code]:
  "finfun_fset_dom_aux (finfun_update_code f (a::'a::card_UNIV) b) = finfun_fset_dom_u a b (finfun_fset_dom_aux f)"
by (metis finfun_fset_dom_aux_def finfun_fset_dom_wf_aux.finfun_rec_upd finfun_update_code_def)
  
lemma finfun_fset_dom_aux_const [code]:
  shows "finfun_fset_dom_aux ((K$ b)::('a::card_UNIV) \<Rightarrow>f 'b) = finfun_fset_dom_c b"
by (metis finfun_fset_dom_aux_def finfun_fset_dom_wf.finfun_rec_const)
  
text {* Testing code generation *}

value "let ff = ((K$ 0) :: int \<Rightarrow>f int)(1 $:= 42)(42 $:= 0)(43 $:= 1) in finfun_fset_dom ff"

subsection {* The image of a finfun as an fset *}

definition finfun_fset_image where 
  "finfun_fset_image ff \<equiv> (\<lambda> x . ff $ x) |`| finfun_fset_dom ff"

end