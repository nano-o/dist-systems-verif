section {* Definition of ballot arrays *}

theory BallotArrays3
imports Main "~~/src/HOL/Library/Monad_Syntax" LinorderOption Quorums2 Max_Properties
begin

subsection {* The definitions *}

locale ballot_array =
  fixes quorums :: "'a set set"
  and ballot :: "'a \<Rightarrow> nat"
  and vote :: "'a \<Rightarrow> nat \<rightharpoonup> 'v"
begin

definition conservative where
  "conservative b \<equiv> \<forall> a1 . \<forall> a2 .
    let v1 = vote a1 b; v2 = vote a2 b in
      case v1 of Some x \<Rightarrow> (case v2 of Some y \<Rightarrow> x = y | None \<Rightarrow> True) | None \<Rightarrow> True"

definition conservative_array where
  "conservative_array \<equiv> \<forall> b . conservative b"

text {* Here the @{term Max} is the one from @{text Lattices_Big} *}

definition proved_safe_at_2 where
  "proved_safe_at_2 q b v \<equiv>
    q \<in> quorums \<and> (\<forall> a \<in> q . ballot a \<ge> b) \<and>
    (if \<exists> a b\<^sub>2 . a \<in> q \<and> b\<^sub>2 < b \<and> vote a b\<^sub>2 \<noteq> None
    then \<exists> a b\<^sub>2 . a \<in> q \<and> b\<^sub>2 < b \<and> vote a b\<^sub>2 = Some v
      \<and> (\<forall> a\<^sub>2 b\<^sub>3 . a\<^sub>2 \<in> q \<and> b\<^sub>3 > b\<^sub>2 \<and> b\<^sub>3 < b \<longrightarrow> vote a\<^sub>2 b\<^sub>3 = None)
    else True)" (* TODO: why not Max ...? *)

definition proved_safe_at_2_a where
  "proved_safe_at_2_a q b v \<equiv>
    q \<in> quorums \<and> (\<forall> a \<in> q . ballot a \<ge> b) \<and>
    (if \<exists> a \<in> q . \<exists> b\<^sub>2 . b\<^sub>2 < b \<and> vote a b\<^sub>2 \<noteq> None
    then \<exists> a \<in> q . vote a (Max {b\<^sub>2 . \<exists> a \<in> q . b\<^sub>2 < b \<and> vote a b\<^sub>2 \<noteq> None}) = Some v
    else True)"

lemma "proved_safe_at_2_a q b v = proved_safe_at_2 q b v"
nitpick[verbose, card 'v = 2, card 'a = 3, card nat = 2, card "'v option" = 3,
card "nat option" = 3, card "nat option option" = 4, expect=none]
oops

definition voted_bal where
  "voted_bal a v_bal b \<equiv> v_bal < b \<and> vote a v_bal \<noteq> None"

lemma finite_voted_bal:"finite {b\<^sub>a. voted_bal a b\<^sub>a b}"
by (simp add: voted_bal_def)

definition chosen_at where
  "chosen_at v b \<equiv> \<exists> q . q \<in> quorums \<and> (\<forall> a \<in> q . vote a b = (Some v))"

definition chosen where
  "chosen v \<equiv> \<exists> b . chosen_at v b"
  
definition choosable where
  "choosable v b \<equiv>
    \<exists> q . q \<in> quorums \<and> (\<forall> a \<in> q . ballot a > b \<longrightarrow> vote a b = Some v)"

definition safe_at where
  "safe_at v b \<equiv>
    \<forall> b2 . \<forall> v2 . ((b2 < b \<and> choosable v2 b2) \<longrightarrow> (v = v2))"

definition safe where
  "safe \<equiv> \<forall> b . \<forall> a . case vote a b of None \<Rightarrow> True | Some v \<Rightarrow> safe_at v b"
  
definition well_formed where
  "well_formed \<equiv> \<forall> a b . ballot a < b \<longrightarrow> vote a b = None"

end

subsection {* Computing safe values in a distributed implementation *}

locale safe_val_lemmas = ballot_array quorums + quorums quorums for quorums
begin

definition acc_max where
  -- {* @{term acc_max} can be computed locally by an acceptor. *}
  "acc_max a bound \<equiv> 
    if (\<exists> b < bound . vote a b \<noteq> None)
    then Some (max_by_key {(v,b) . b < bound \<and> vote a b = Some v} snd)
    else None"

definition proved_safe_at where
  -- {* @{term proved_safe_at} can be computed locally by a leader *}
  "proved_safe_at q b v \<equiv> q \<in> quorums \<and> (\<forall> a \<in> q . ballot a \<ge> b) \<and>
    (let acc_maxs = Union ((\<lambda> a . case acc_max a b of None \<Rightarrow> {} | Some (v,b) \<Rightarrow> {(v,b)}) ` q)
    in 
      if acc_maxs = {} then True
      else fst (max_by_key acc_maxs snd) = v)"
                                                            
lemma assumes "proved_safe_at q b v" and "conservative_array" shows "proved_safe_at_2_a q b v"
nitpick[verbose, card 'a = 3, card nat = 2, card 'b = 3, card "nat option" = 3, card "'b option" = 4, card "('b \<times> nat) option" = 7,
  card "'b \<times> nat" = 6, expect=none]
proof -
  text {* First a few immediate facts. *}
  from assms have "q \<in> quorums" and bals:"\<And> a . a \<in> q \<Longrightarrow> ballot a \<ge> b" using proved_safe_at_def by auto
  from \<open>q \<in> quorums\<close> have "finite q" and "q \<noteq> {}"
    apply (metis quorums_axioms quorums_def) by (metis \<open>q \<in> quorums\<close> empty_iff quorum_inter_witness)

  text {* Re-stating the main goal. *}
  have "if \<exists> a \<in> q . \<exists> b\<^sub>2 . b\<^sub>2 < b \<and> vote a b\<^sub>2 \<noteq> None
    then \<exists> a \<in> q . vote a (Max {b\<^sub>2 . \<exists> a \<in> q . b\<^sub>2 < b \<and> vote a b\<^sub>2 \<noteq> None}) = Some v
    else True" (is "if ?cond then ?true else ?false")
  proof (cases "?cond")
    case True    
    from True obtain a b\<^sub>a where "a \<in> q" and "vote a b\<^sub>a \<noteq> None" and "b\<^sub>a < b" by (auto simp add:acc_max_def)
    hence "acc_max a b \<noteq> None" by (auto simp add:acc_max_def)

    text {* Using lemma @{thm max_by_key_subsets} *}
    let ?Ss = "{{(v,b\<^sub>a) . b\<^sub>a < b \<and> vote a b\<^sub>a = Some v} | a . a \<in> q}"
    let ?S = "{(v,b\<^sub>a) . b\<^sub>a < b \<and> vote a b\<^sub>a = Some v}"
    have 8:"finite ?Ss" using \<open>finite q\<close> by simp
    have 9:"\<And> S . S \<in> ?Ss \<Longrightarrow> finite S"
    proof -
      { fix S f g
        assume "finite (f ` S)" and "\<And> x . x \<in> S \<Longrightarrow> x = (g o f) x"
        hence "finite S" by (metis finite_imageI finite_subset image_comp image_eqI subsetI) }
      note 1 = this
      fix S assume "S \<in> ?Ss"
      obtain a where 2:"S = {(v,b\<^sub>a) . b\<^sub>a < b \<and> vote a b\<^sub>a = Some v}" by (smt \<open>S \<in> ?Ss\<close> mem_Collect_eq)
      moreover with this have "\<And> x . x \<in> S \<Longrightarrow> x = (the (vote a (snd x)), snd x)" by (metis (mono_tags, lifting) Product_Type.Collect_case_prodD option.sel prod.collapse) 
      moreover have "finite (snd ` S)" using 2 by (auto simp add:image_def)
      ultimately show "finite S" using 1[of snd S "\<lambda> b . (the (vote a b), b)"] by (metis comp_def)
    qed
    have 5:"?S \<in> ?Ss" using \<open>a \<in> q\<close> by blast
    have 6:"?S \<noteq> {}" using \<open>b\<^sub>a < b\<close> \<open>vote a b\<^sub>a \<noteq> None\<close> by blast
    have v_max_max:"v = fst (max_by_key {max_by_key S snd | S . S \<in> ?Ss \<and> S \<noteq> {}} snd)" 
    proof -
      let ?acc_maxs_set = "(\<lambda> a . case acc_max a b of None \<Rightarrow> {} | Some (v,b) \<Rightarrow> {(v,b)}) ` q"
      let ?acc_maxs = "Union ?acc_maxs_set"
      have 1:"?acc_maxs \<noteq> {}" using \<open>acc_max a b \<noteq> None\<close> apply (auto split add:option.splits) by (metis \<open>a \<in> q\<close>)
      hence 2:"fst (max_by_key ?acc_maxs snd) = v" by (metis (no_types, lifting) assms(1) proved_safe_at_def)
      moreover
      have 7:"?acc_maxs = {max_by_key S snd | S . S \<in> ?Ss \<and> S \<noteq> {}}"
        apply (auto simp add: acc_max_def split add:option.splits split_if_asm)
        apply (smt Collect_empty_eq case_prodI) by (metis (mono_tags) option.simps(3))
      ultimately show ?thesis by auto 
    qed
    hence v_max_Union:"v = fst (max_by_key (Union ?Ss) snd)"
    proof -
      have 10:"\<And> x y . \<lbrakk>x \<in> Union ?Ss; y \<in> Union ?Ss; snd x = snd y\<rbrakk> \<Longrightarrow> x = y"
        using assms(2) by (auto simp add:conservative_array_def conservative_def split add:option.splits)
      show ?thesis using max_by_key_subsets[of ?Ss ?S snd]
        by (metis (no_types, lifting) "10" "5" "6" "8" "9" v_max_max) 
    qed

    text {* now we prove that this is the same as Max... *}
    let ?m = "max_by_key (Union ?Ss) snd"  let ?b\<^sub>m = "snd ?m"
    have 13:"v = fst ?m" by (metis v_max_Union)
    let ?bals = "{b\<^sub>2 . b\<^sub>2 < b \<and> (\<exists> a \<in> q . vote a b\<^sub>2 \<noteq> None)}"
    have bm_max:"?b\<^sub>m = Max ?bals"
    proof -
      have "?b\<^sub>m \<in> ?bals" and "\<And> b . b \<in> ?bals \<Longrightarrow> b \<le> ?b\<^sub>m"
      proof -
        have 14:"(v,?b\<^sub>m) \<in> Union ?Ss" and 15:"\<And> x . x \<in> Union ?Ss \<Longrightarrow> snd x \<le> ?b\<^sub>m" 
        proof -
          have 11:"finite (Union ?Ss)" by (metis (no_types, lifting) "8" "9" finite_Union)
          have 12:"Union ?Ss \<noteq> {}" by (metis (no_types, lifting) "5" "6" Sup_bot_conv(1))
          show "(v,?b\<^sub>m) \<in> Union ?Ss" and 15:"\<And> x . x \<in> Union ?Ss \<Longrightarrow> snd x \<le> ?b\<^sub>m"
            apply (metis (mono_tags, lifting) "11" "12" ex_in_conv max_by_key_in_and_ge(2) surjective_pairing v_max_Union)
            by (metis (no_types, lifting) "11" max_by_key_in_and_ge(1))
        qed
        have 18:"?b\<^sub>m < b" using 14 by auto 
        have 16:"Union ?Ss = {(v\<^sub>2,b\<^sub>2) . b\<^sub>2 < b \<and> (\<exists> a \<in> q . vote a b\<^sub>2 = Some v\<^sub>2)}" by auto
        have 17:"\<exists> a \<in> q . vote a ?b\<^sub>m = Some v" and 19:"\<And> b\<^sub>2 v\<^sub>2. b\<^sub>2 < b \<and> (\<exists> a \<in> q . vote a b\<^sub>2 = Some v\<^sub>2) \<Longrightarrow> b\<^sub>2 \<le> ?b\<^sub>m"
          apply (smt "14" "16" Product_Type.Collect_case_prodD prod.collapse v_max_Union)
          by (metis (mono_tags, lifting) "15" "16" case_prod_conv mem_Collect_eq snd_conv)
        show "?b\<^sub>m \<in> ?bals" and "\<And> b . b \<in> ?bals \<Longrightarrow> b \<le> ?b\<^sub>m"
          apply (metis (mono_tags, lifting) "17" "18" mem_Collect_eq option.simps(3))
          apply auto apply (insert 19) by (metis (no_types, lifting)) 
      qed
      moreover have "finite ?bals" by fastforce
      moreover have "?bals \<noteq> {}"
        by (metis (mono_tags, lifting) Collect_empty_eq \<open>a \<in> q\<close> \<open>b\<^sub>a < b\<close> \<open>vote a b\<^sub>a \<noteq> None\<close>) 
      ultimately show "?b\<^sub>m = Max ?bals" by (metis (no_types, lifting) Max_eqI)
    qed
    have m_in_union:"?m \<in> Union ?Ss" 
    proof -
      have "finite (Union ?Ss)" by (metis (no_types, lifting) "8" "9" finite_Union) 
      moreover have "Union ?Ss \<noteq> {}"
        by (metis (mono_tags, lifting) "5" "6" empty_Union_conv)
      ultimately show ?thesis by (metis (no_types, lifting) ex_in_conv max_by_key_in_and_ge(2)) 
    qed
    obtain a2 where "a2 \<in> q" and max_vote:"vote a2 ?b\<^sub>m = Some v"
      by (smt Product_Type.Collect_case_prodD UnionE m_in_union mem_Collect_eq v_max_Union) 
    show ?thesis using bexI[where ?x=a2 and ?A=q] max_vote True \<open>a2 \<in> q\<close> bm_max by auto
  next
    case False
    thus ?thesis by auto
  qed
  thus ?thesis using \<open>q \<in> quorums\<close> bals by (auto simp add:proved_safe_at_2_a_def)
qed

end

end