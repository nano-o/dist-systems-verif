theory DistributedSafeAt
imports BallotArrays BallotArrayProperties "~~/src/HOL/Library/Monad_Syntax" Utils
begin

section {* Computing safe values in a distributed implementation *}
  
locale distributed_safe_at = ballot_array
begin

definition acc_max where
  -- {* @{term acc_max} can be computed locally by an acceptor. *}
  "acc_max a bound \<equiv> max_by_key (a_votes a bound) snd"
  
definition max_quorum_votes where
  "max_quorum_votes q b \<equiv> max_by_key (\<Union> a \<in> q . acc_max a b) snd"

definition proved_safe_at where
  -- {* @{term proved_safe_at} can be computed locally by a leader when it knows acc_max over q *}
  "proved_safe_at q b v \<equiv> q \<in> quorums \<and> (\<forall> a \<in> q . ballot a \<ge> b) \<and>
    (v \<in> (fst ` max_quorum_votes q b) \<or> max_quorum_votes q b = {})"

end 

subsection {* Properties of @{term distributed_safe_at.proved_safe_at} *}

locale dsa_properties = quorums quorums + distributed_safe_at quorums ballot vote 
  for quorums ballot vote
begin

sublocale ballot_array_props 
  by (unfold_locales)

context begin

private
lemma max_quorum_votes:
  assumes "q \<in> quorums"
  shows "max_quorum_votes q b =
  max_by_key (q_votes q b) snd"
  (is "?lhs = max_by_key ?vs snd")
proof -
  define Ss where "Ss \<equiv> {a_votes a b | a . a \<in> q}"
  have "finite S" if "S \<in> Ss" for S using that using Ss_def a_votes_finite by blast 
  moreover
  have "finite Ss" using \<open>q \<in> quorums\<close> using  quorums_axioms unfolding Ss_def quorums_def  by auto
  moreover have "{(v, b'). b' < b \<and> (\<exists>a\<in>q. vote a b' = Some v)} = \<Union> Ss"
    unfolding Ss_def a_votes_def by auto
  moreover have "(\<Union>a\<in>q. acc_max a b) = (\<Union>S\<in>Ss . max_by_key S snd)" unfolding Ss_def acc_max_def by auto
  ultimately show ?thesis using max_by_key_subsets[of Ss snd] unfolding max_quorum_votes_def q_votes_def by auto
qed 
 
lemma max_vote_e_or_singleton:
  assumes "conservative_array" and "q \<in> quorums"
  obtains x where "max_quorum_votes q b = {x}"
  | "max_quorum_votes q b = {}"
proof (cases "\<exists> a \<in> q . \<exists> b' < b . vote a b' \<noteq> None")
  case True
  define vs where "vs \<equiv> q_votes q b"
  have "vs \<noteq> {}" using True unfolding vs_def q_votes_def by auto
  moreover have "finite vs" unfolding vs_def
    by (simp add: assms(2) q_votes_finite) 
  moreover have "snd x \<noteq> snd y" if "x \<in> vs" and "y \<in> vs" and "x \<noteq> y" for x y 
    using assms(1) that unfolding vs_def conservative_array_def conservative_def q_votes_def
    by (auto split!:option.splits) 
  moreover have "max_quorum_votes q b = max_by_key vs snd" unfolding vs_def q_votes_def
    by (simp add:max_quorum_votes[OF assms(2)] q_votes_def)
  ultimately
  obtain x where "max_quorum_votes q b = {x}" using max_by_key_ordered by metis
  thus ?thesis using that by auto
next
  case False
  then show ?thesis using that max_quorum_votes[OF assms(2)] unfolding max_by_key_def q_votes_def by fastforce
qed

private lemma safe_at_imp_safe_at_abs:
  assumes "proved_safe_at q b v" and "q \<in> quorums"
  shows "proved_safe_at_abs q b v"
proof (cases "max_quorum_votes q b = {}")
  case True
  hence "max_by_key (q_votes q b) snd = {}"  by (simp add:max_quorum_votes[OF \<open>q\<in>quorums\<close>])
  moreover have "finite (q_votes q b)" by (simp add: assms(2) q_votes_finite) 
  ultimately have "q_votes q b = {}" by (meson max_by_key_ne) 
  hence "\<not> (\<exists> a \<in> q . \<exists> b' . b' < b \<and> vote a b' \<noteq> None)" 
    apply (auto simp add:q_votes_def) by (meson option.exhaust)
  then show ?thesis using assms by (auto simp add:proved_safe_at_abs_def proved_safe_at_def)
next
  case False
  then show ?thesis 
    using  assms unfolding proved_safe_at_def
    by (auto simp add:max_quorum_votes[OF assms(2)] proved_safe_at_abs_def q_votes_def)
qed

private
lemma proved_safe_at_imp_safe_at_aux:
  assumes "\<And> a j w . \<lbrakk>j < i; vote a j = Some w\<rbrakk> \<Longrightarrow> safe_at w j"
    and "proved_safe_at q i v" and "conservative_array" and "q \<in> quorums"
  shows "safe_at v (i::nat)" using safe_at_imp_safe_at_abs assms proved_safe_at_abs_imp_safe_at
  by blast

lemma proved_safe_at_imp_safe_at:
  -- {* A weaker version of the above, but which is easier to use in proofs. *}
  assumes "safe"
    and "proved_safe_at q i v" and "conservative_array" and "q \<in> quorums"
  shows "safe_at v (i::nat)" using assms proved_safe_at_imp_safe_at_aux
  by (metis option.simps(5) safe_def)
  
end

end

end