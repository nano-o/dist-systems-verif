theory DistributedSafeAt
imports BallotArrays BallotArrayProperties MaxByKey
begin

subsection {* Computing safe values in a distributed implementation *}

locale distributed_safe_at = ballot_array 
begin
  
definition acc_max where
  -- {* @{term acc_max} can be computed locally by an acceptor. *}
  "acc_max a bound \<equiv> 
    if (\<exists> b < bound . vote a b \<noteq> None)
    then Some (max_by_key {(v,b) . b < bound \<and> vote a b = Some v} snd)
    else None"
  
term "the ` ((\<lambda> b . vote a b \<bind> (\<lambda> v . Some (v,b))) ` {0::nat..<bound} - {None})"

lemma acc_max_code[code]:"acc_max a bound = 
  (if (\<exists> b < bound . vote a b \<noteq> None)
  then 
    let 
      f = \<lambda> x . case x of None \<Rightarrow> {} | Some y \<Rightarrow> {y};
      g = \<lambda> b . vote a b \<bind> (\<lambda> v . Some (v,b));
      votes = (g ` {0..<bound}) \<bind> f
    in Some (max_by_key votes snd)
  else None)" 
proof (cases "\<exists> b < bound . vote a b \<noteq> None")
  case True
  then show ?thesis 
  proof -              
    have "(((\<lambda> b . vote a b \<bind> (\<lambda> v . Some (v,b))) ` {0..<bound}) \<bind> 
        (\<lambda> x . case x of None \<Rightarrow> {} | Some y \<Rightarrow> {y}))
        = {(v,b) . b < bound \<and> vote a b = Some v}" apply (auto split!:option.split_asm)
        apply (simp add: bind_eq_Some_conv)
       apply (smt bind_eq_Some_conv option.sel prod.inject)
      by force
    thus ?thesis
      using acc_max_def by auto
  qed
next
  case False
  then show ?thesis
    using acc_max_def by auto 
qed

lemma acc_max_singleton: 
  assumes "acc_max a bound = Some xs"
  obtains val bal where "xs = {(val,bal)}" 
proof -  
  define votes where "votes = {(v,b) . b < bound \<and> vote a b = Some v}"
  have 4:"acc_max a bound = Some (max_by_key votes snd)"
    by (metis (no_types, lifting) votes_def acc_max_def assms option.distinct(1))
  obtain x where "max_by_key votes snd = {x}"
  proof -
    have 1:"votes \<noteq> {}" (is "?votes \<noteq> {}") using assms
      by (auto simp add:acc_max_def votes_def split!: if_split_asm)
    have 2:"finite votes" 
    proof -
      have 1:"finite (S \<bind> f)" if "finite S" and "\<And> x . x \<in> S \<Longrightarrow> finite (f x)" for S f
        by (simp add: bind_UNION that)
      have 2:"?votes = {b . b < bound} \<bind> (\<lambda> b . case vote a b of Some v \<Rightarrow> {(v,b)} | None  \<Rightarrow> {})"
        (is "?votes = Set.bind ?bals ?f")
        by (auto simp add: Set.bind_def votes_def split!:option.split)
      have 3:"finite ?bals"
        by simp 
      have 4:"finite (?f b)" for b by (simp split!:option.split)
      show ?thesis
        by (metis (no_types, lifting) 2 3 1 4)
    qed
    have 3:"snd x \<noteq> snd y" if "x \<in> ?votes" and "y \<in> ?votes" and "x \<noteq> y" for x y
      by (metis (mono_tags, lifting) votes_def BNF_Def.Collect_case_prodD option.simps(1) prod_eq_iff that)
    show ?thesis using that max_by_key_ordered 1 2 3
      by (metis (full_types))
  qed
  thus ?thesis using that
    by (metis "4" assms old.prod.exhaust option.simps(1))
qed

definition acc_max_2 where
  "acc_max_2 a bound \<equiv>
    if (\<exists> b < bound . vote a b \<noteq> None)
    then let 
        mbk2 = max_by_key {(v,b) . b < bound \<and> vote a b = Some v} snd
      in Some (the_elem mbk2)
    else None"

definition max_pair where
  "max_pair q a_max \<equiv> 
    let acc_maxs = Union ((\<lambda> a . case a_max a of None \<Rightarrow> {} | Some S \<Rightarrow> S) ` q)
    in
      if acc_maxs = {} then None
      else Some (max_by_key acc_maxs snd)"

definition proved_safe_at where
  -- {* @{term proved_safe_at} can be computed locally by a leader *}
  "proved_safe_at q b v \<equiv> q \<in> quorums \<and> (\<forall> a \<in> q . ballot a \<ge> b) \<and>
    (case max_pair q (\<lambda> a . acc_max a b) of None \<Rightarrow> True
    | Some S \<Rightarrow> v \<in> (fst ` S))"
          
end

locale dsa_properties = quorums quorums + distributed_safe_at quorums for quorums
begin

context begin

private lemma l1:
  assumes "proved_safe_at q b v"
  shows "proved_safe_at_abs q b v"
proof -
  have "v \<in> fst ` (max_by_key {} snd)" if "\<exists> a \<in> q . \<exists> b' < b . vote a b' \<noteq> None"

private
lemma l1: assumes "proved_safe_at q b v" and "conservative_array" shows "proved_safe_at_abs q b v" sorry
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
    have v_max_max:"v \<in> fst ` (max_by_key (Union {max_by_key S snd | S . S \<in> ?Ss \<and> S \<noteq> {}}) snd)" 
    proof -
      let ?acc_maxs_set = "(\<lambda> a . case acc_max a b of None \<Rightarrow> {} | Some (v,b) \<Rightarrow> {(v,b)}) ` q"
      let ?acc_maxs = "Union ?acc_maxs_set"
      have 1:"?acc_maxs \<noteq> {}" using \<open>acc_max a b \<noteq> None\<close> apply (auto split add:option.splits) by (metis \<open>a \<in> q\<close>)
      hence 2:"fst (max_by_key ?acc_maxs snd) = v" using assms(1) proved_safe_at_def 
        apply (auto simp add:max_pair_def split add:option.splits) apply (metis option.simps(3)) by (metis (no_types, lifting) fst_conv option.inject) 
      moreover
      have 7:"?acc_maxs = {max_by_key S snd | S . S \<in> ?Ss \<and> S \<noteq> {}}"
        apply (auto simp add: acc_max_def split add:option.splits split_if_asm)
        apply (smt Collect_empty_eq case_prodI) by (metis (mono_tags) option.simps(3))
      ultimately show ?thesis by auto 
    qed
    hence v_max_Union:"v = fst (max_by_key (Union ?Ss) snd)"
    proof -
      have 10:"\<And> x y . \<lbrakk>x \<in> Union ?Ss; y \<in> Union ?Ss; snd x = snd y\<rbrakk> \<Longrightarrow> x = y"
        using assms(2) by (auto simp add:conservative_array_def conservative_def split:option.splits)
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
  thus ?thesis using \<open>q \<in> quorums\<close> bals by (auto simp add:proved_safe_at_abs_def)
qed

lemma proved_safe_at_imp_safe_at:
  assumes "\<And> a j w . \<lbrakk>j < i; vote a j = Some w\<rbrakk> \<Longrightarrow> safe_at w j"
  and "proved_safe_at q i v" and "conservative_array"
  shows "safe_at v (i::nat)" using l1 ballot_array_props.proved_safe_at_abs_imp_safe_at
by (metis assms(1) assms(2) assms(3) ballot_array_props.intro quorums_axioms) 

end

end

end