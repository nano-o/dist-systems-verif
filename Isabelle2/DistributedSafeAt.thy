theory DistributedSafeAt
imports BallotArrays BallotArrayProperties
begin

subsection {* Computing safe values in a distributed implementation *}

locale distributed_safe_at = ballot_array 
begin

definition acc_max where
  -- {* @{term acc_max} can be computed locally by an acceptor. *}
  "acc_max a bound \<equiv> 
    if (\<exists> b < bound . vote a b \<noteq> None)
    then Some (max_by_key_2 {(v,b) . b < bound \<and> vote a b = Some v} snd)
    else None"

definition max_pair where
  "max_pair q a_max \<equiv> 
    let acc_maxs = Union ((\<lambda> a . case a_max a of None \<Rightarrow> {} | Some S \<Rightarrow> S) ` q)
    in
      if acc_maxs = {} then None
      else Some (max_by_key_2 acc_maxs snd)"

definition proved_safe_at where
  -- {* @{term proved_safe_at} can be computed locally by a leader *}
  "proved_safe_at q b v \<equiv> q \<in> quorums \<and> (\<forall> a \<in> q . ballot a \<ge> b) \<and>
    (case max_pair q (\<lambda> a . acc_max a b) of None \<Rightarrow> True
    | Some S \<Rightarrow> v \<in> (fst ` S))"
          
end

print_locale distributed_safe_at
print_locale quorums

locale dsa_properties = quorums quorums + distributed_safe_at quorums for quorums
begin

context begin
                                                         
private                                                  
lemma l1: assumes "proved_safe_at q b v" and "conservative_array"
  shows "proved_safe_at_2_a q b v"
proof -
  text {* First a few immediate facts. *}
  from assms have "q \<in> quorums" and bals:"\<And> a . a \<in> q \<Longrightarrow> ballot a \<ge> b" using proved_safe_at_def
    apply force by (meson assms(1) proved_safe_at_def)
  from \<open>q \<in> quorums\<close> have "finite q" and "q \<noteq> {}"
    apply (metis quorums_axioms quorums_def) by (metis \<open>q \<in> quorums\<close> empty_iff quorum_inter_witness)

  text {* Re-stating the main goal. *}
  have "if \<exists> a \<in> q . \<exists> b\<^sub>2 . b\<^sub>2 < b \<and> vote a b\<^sub>2 \<noteq> None
    then \<exists> a \<in> q . vote a (Max {b\<^sub>2 . \<exists> a \<in> q . b\<^sub>2 < b \<and> vote a b\<^sub>2 \<noteq> None}) = Some v
    else True" (is "if ?cond then ?true else ?false")
  proof (cases "?cond")
    case True    
    from True obtain a b\<^sub>a where t0:"a \<in> q" and t1:"vote a b\<^sub>a \<noteq> None" and t2:"b\<^sub>a < b" by (auto simp add:acc_max_def)
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
    have v_max_max:"v \<in> fst ` (max_by_key_2 (Union {max_by_key_2 S snd | S . S \<in> ?Ss \<and> S \<noteq> {}}) snd)" 
    proof -
      let ?acc_maxs_set = "(\<lambda> a . case acc_max a b of None \<Rightarrow> {} | Some S \<Rightarrow> S) ` q"
      let ?acc_maxs = "Union ?acc_maxs_set"
      obtain B where b0:"B = the (acc_max a b)" using \<open>acc_max a b \<noteq> None\<close> by simp
      hence b1:"B \<noteq> {}" using \<open>acc_max a b \<noteq> None\<close> \<open>b\<^sub>a < b\<close> \<open>vote a b\<^sub>a \<noteq> None\<close> unfolding acc_max_def
        by (smt "5" "6" "9" max_by_key_ne option.sel)
      have "B \<in> ?acc_maxs_set" using b0 \<open>a \<in> q\<close> \<open>acc_max a b \<noteq> None\<close> image_iff option.case_eq_if by fastforce
      hence 1:"?acc_maxs \<noteq> {}" using \<open>acc_max a b \<noteq> None\<close> \<open>a \<in> q\<close> apply (auto split add:option.splits)
        using b1 by auto
      hence 2:"v \<in> fst ` (max_by_key_2 ?acc_maxs snd)" using assms(1) proved_safe_at_def 
        apply (auto simp add:max_pair_def split add:option.splits)
        apply (metis empty_iff option.simps(3))
        proof -
          fix x2 :: "('b \<times> nat) set" and ba :: nat and aaa :: 'a and y :: "('b \<times> nat) set" and aa :: 'b and bb :: nat
          assume a1: "(if \<forall>a\<in>q. \<forall>x2. acc_max a b = Some x2 \<longrightarrow> x2 = {} then None else Some (max_by_key_2 (\<Union>a\<in>q. case acc_max a b of None \<Rightarrow> {} | Some S \<Rightarrow> S) snd)) = Some x2"
          assume a2: "(v, ba) \<in> x2"
          assume a3: "aaa \<in> q"
          assume a4: "acc_max aaa b = Some y"
          assume a5: "v \<notin> fst ` max_by_key_2 (\<Union>a\<in>q. case acc_max a b of None \<Rightarrow> {} | Some S \<Rightarrow> S) snd"
          assume a6: "(aa, bb) \<in> y"
          have "v \<in> fst ` x2"
            using a2 by (metis (no_types) fst_eqD image_iff)
          then show False
            using a6 a5 a4 a3 a1 by (metis equals0D option.sel)
        qed
      moreover
      have 7:"?acc_maxs = Union {max_by_key_2 S snd | S . S \<in> ?Ss \<and> S \<noteq> {}}"
        apply (auto simp add: acc_max_def split add:option.splits split_if_asm)
        apply (smt Collect_empty_eq case_prodI) by (metis (mono_tags) option.simps(3))
      ultimately show ?thesis by auto 
    qed
    hence v_max_Union:"v \<in> fst ` (max_by_key_2 (Union ?Ss) snd)"
    proof -
      have 10:"\<And> x y . \<lbrakk>x \<in> Union ?Ss; y \<in> Union ?Ss; snd x = snd y\<rbrakk> \<Longrightarrow> x = y"
        using assms(2) by (auto simp add:conservative_array_def conservative_def split add:option.splits)
      show ?thesis using max_by_key_2_subsets[of ?Ss ?S snd]
        by (metis (no_types, lifting) "10" "5" "6" "8" "9" v_max_max) 
    qed

    text {* now we prove that this is the same as Max... *}
    let ?m = "(max_by_key_2 (Union ?Ss) snd)"  let ?b\<^sub>m = "(snd ` ?m)"
    have 13:"v \<in> fst ` ?m" by (metis v_max_Union)
    let ?bals = "{b\<^sub>2 . b\<^sub>2 < b \<and> (\<exists> a \<in> q . vote a b\<^sub>2 \<noteq> None)}"
    have bm_max:"Max ?bals \<in> ?b\<^sub>m"
    proof -
      have "card (snd ` ?m) = 1"  using \<open>b\<^sub>a < b\<close> \<open>vote a b\<^sub>a \<noteq> None\<close> unfolding max_by_key_2_def 
      have "?b\<^sub>m \<in> ?bals" and "\<And> b . b \<in> ?bals \<Longrightarrow> b \<le> ?b\<^sub>m"
      proof -
        have 14:"(v,?b\<^sub>m) \<in> Union ?Ss" and 15:"\<And> x . x \<in> Union ?Ss \<Longrightarrow> snd x \<le> ?b\<^sub>m" 
        proof -
          have 11:"finite (Union ?Ss)" by (metis (no_types, lifting) "8" "9" finite_Union)
          have 12:"Union ?Ss \<noteq> {}" by (metis (no_types, lifting) "5" "6" Sup_bot_conv(1))
          show "(v,?b\<^sub>m) \<in> Union ?Ss" and 15:"\<And> x . x \<in> Union ?Ss \<Longrightarrow> snd x \<le> ?b\<^sub>m"
            
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

lemma proved_safe_at_imp_safe_at:
  assumes "\<And> a j w . \<lbrakk>j < i; vote a j = Some w\<rbrakk> \<Longrightarrow> safe_at w j"
  and "proved_safe_at q i v" and "conservative_array"
  shows "safe_at v (i::nat)" using l1 ballot_array_props.proved_safe_at_2_a_imp_safe_at
by (metis assms(1) assms(2) assms(3) ballot_array_props.intro quorums_axioms) 

end

end 

end