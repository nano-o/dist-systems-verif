theory DistributedSafeAt
imports BallotArrays BallotArrayProperties "~~/src/HOL/Library/Monad_Syntax" Utils
begin

subsection {* Computing safe values in a distributed implementation *}
  
locale distributed_safe_at = ballot_array
begin

definition acc_max where
  -- {* @{term acc_max} can be computed locally by an acceptor. *}
  "acc_max a bound \<equiv> 
    if (\<exists> b < bound . vote a b \<noteq> None)
    then Some (the_elem (max_by_key {(v,b) . b < bound \<and> vote a b = Some v} snd))
    else None"

definition max_quorum_votes where
  "max_quorum_votes q a_max \<equiv> 
    let acc_maxs = Union ((\<lambda> a . option_as_set (a_max a)) ` q)
    in max_by_key acc_maxs snd"

definition proved_safe_at where
  -- {* @{term proved_safe_at} can be computed locally by a leader when it knows acc_max over q *}
  "proved_safe_at q b v \<equiv> q \<in> quorums \<and> (\<forall> a \<in> q . ballot a \<ge> b) \<and>
    v \<in> (fst ` max_quorum_votes q (\<lambda> a . acc_max a b))"

lemma acc_max_code[code]:
  fixes get_vote
  defines "get_vote a b \<equiv> vote a b \<bind> (\<lambda> v . Some (v,b))"
  shows "acc_max a bound = 
  (if (\<exists> b < bound . vote a b \<noteq> None)
  then let votes = (get_vote a ` {0..<bound}) \<bind> option_as_set
    in Some (the_elem (max_by_key votes snd))
  else None)"
proof (cases "\<exists> b < bound . vote a b \<noteq> None")
  case True
  then show ?thesis 
  proof -              
    have "(get_vote a ` {0..<bound}) \<bind> option_as_set = {(v,b) . b < bound \<and> vote a b = Some v}" 
      apply (auto simp add:option_as_set_def get_vote_def split!:option.split_asm)
        apply (simp add: bind_eq_Some_conv)
       apply (smt bind_eq_Some_conv option.sel prod.inject)
      by force
    thus ?thesis
      by (simp add: distributed_safe_at.acc_max_def) 
  qed
next
  case False
  then show ?thesis
    using acc_max_def by auto 
qed

lemma acc_max_singleton: 
  assumes "b < bound" and "vote a b \<noteq> None"
  fixes votes 
  defines "votes \<equiv> {(v,b) . b < bound \<and> vote a b = Some v}"
  obtains val bal where "max_by_key votes snd = {(val,bal)}"
proof -
  obtain x where "max_by_key votes snd = {x}"
  proof -
    have 1:"votes \<noteq> {}" (is "?votes \<noteq> {}") using assms
      by (auto simp add:acc_max_def votes_def split!: if_split_asm)
    have 2:"finite votes" using votes_finite by (auto simp add:votes_def)
    have 3:"snd x \<noteq> snd y" if "x \<in> ?votes" and "y \<in> ?votes" and "x \<noteq> y" for x y
      by (metis (mono_tags, lifting) votes_def BNF_Def.Collect_case_prodD option.simps(1) prod_eq_iff that)
    show ?thesis using that max_by_key_ordered 1 2 3
      by (metis (full_types))
  qed
  thus ?thesis using that
    by fastforce 
qed

lemma acc_max_is_max_by_key:
  fixes votes a bound v b
  defines "votes \<equiv> {(v,b) . b < bound \<and> vote a b = Some v}"
  assumes "acc_max a bound = Some (v,b)"
  shows "max_by_key votes snd = {(v,b)}"
proof -
  obtain b' where 1:"b' < bound" and 2:"vote a b' \<noteq> None" using assms
    by (metis acc_max_code option.simps(3))
  from acc_max_singleton[OF 1 2] obtain val bal where 4:"max_by_key votes snd = {(val,bal)}"
    using votes_def by blast
  thus ?thesis using assms(2) apply (simp add:acc_max_def votes_def)
    by (metis option.inject option.simps(3) prod.inject the_elem_eq)
qed

lemma acc_max_is_a_vote:
  assumes "acc_max a bound = Some (v,b)"
  shows "vote a b = Some v" 
proof -
  have "max_by_key {(v,b) . b < bound \<and> vote a b = Some v} snd = {(v,b)}"
    by (simp add: acc_max_is_max_by_key assms)
  moreover have "{(v,b) . b < bound \<and> vote a b = Some v} \<noteq> {}" using assms 
    by (auto simp add:acc_max_def split!:if_splits)
  ultimately show ?thesis using votes_finite max_by_key_in_and_ge(2)[of "{(v, b). b < bound \<and> vote a b = Some v}"] by blast
qed

end

locale dsa_properties = quorums quorums + distributed_safe_at quorums ballot vote 
  for quorums ballot vote
begin

lemma max_vote_unique:
  assumes "b' < b" and "a \<in> q" and "vote a b' = Some w" and "conservative_array" and "q \<in> quorums"
  obtains x where "max_quorum_votes q (\<lambda> a . acc_max a b) = {x}"
proof -
  let ?votes = "Union ((\<lambda> a . option_as_set ((\<lambda> a . acc_max a b) a)) ` q)"
  have "finite ?votes" using quorums_axioms apply (simp add:option_as_set_def quorums_def)
    by (simp add: \<open>q \<in> quorums\<close> option.case_eq_if)
  have "finite q" using \<open>q \<in> quorums\<close> quorums_axioms
     by (simp add: quorums_def)
  have "?votes \<noteq> {}" using assms(1-3) \<open>finite q\<close> acc_max_singleton 
    apply (auto simp add:option_as_set_def split!:option.splits)
    using acc_max_def by auto 
  have "vote a b' = Some v" if "(v,b') \<in> option_as_set (acc_max a b)" for a v b' using that acc_max_is_a_vote
    by (auto simp add:option_as_set_def split!:option.splits)
  hence "\<exists> a . vote a b' = Some v" if "(v,b') \<in> ?votes" for v b' using that by blast
  hence "snd x \<noteq> snd y" if "x \<in> ?votes" and "y \<in> ?votes" and "x \<noteq> y" for x y using \<open>conservative_array\<close> that
    apply (simp add:conservative_array_def conservative_def split!:option.splits)
    by (metis old.prod.exhaust snd_conv) 
  thus ?thesis using that using max_by_key_ordered[where ?f="snd" and ?S="?votes"] \<open>finite ?votes\<close> \<open>?votes \<noteq> {}\<close> 
    apply (simp add:max_quorum_votes_def) by blast
qed

context begin

private lemma l1:
  assumes "proved_safe_at q b v"
  shows "proved_safe_at_abs q b v"
proof -
  have "v \<in> fst ` (max_by_key {} snd)" if "\<exists> a \<in> q . \<exists> b' < b . vote a b' \<noteq> None" oops

private
lemma l1: assumes "proved_safe_at q b v" and "conservative_array" shows "proved_safe_at_abs q b v" oops
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
        apply (auto simp add:max_quorum_votes_def split add:option.splits) apply (metis option.simps(3)) by (metis (no_types, lifting) fst_conv option.inject) 
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