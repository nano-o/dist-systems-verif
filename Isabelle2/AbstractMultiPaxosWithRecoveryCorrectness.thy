section {* Proof of the agreement property of AbstractMultiPaxosWithRecovery. *}

theory AbstractMultiPaxosWithRecoveryCorrectness
imports AbstractMultiPaxosWithRecovery "~~/src/HOL/Eisbach/Eisbach_Tools" BallotArrayProperties 
begin

locale amp_proof = quorums quorums + ampr_ioa quorums for quorums :: "'a set set" +
  fixes the_ioa :: "(('v, 'a) ampr_state, ('a, 'v) paxos_action) ioa"
  defines "the_ioa \<equiv> ioa"
  -- {* Here we have to fix the constant @{term the_ioa} in order to fix all type variables.
  Otherwise, there are problems in Eisbach when matching the same polymorphic constant appearing in several terms. *}
begin

interpretation IOA .

subsection {* Automation setup *}

lemmas ioa_defs =
   is_trans_def actions_def trans_def start_def
   externals_def ioa_def the_ioa_def paxos_asig_def

named_theorems inv_defs

named_theorems invs
  -- "named theorem for use by the tactics below"
named_theorems inv_proofs_defs
  -- "definitions to unfold"

declare propose_def[simp] join_ballot_def[simp] do_vote_def[simp] crash_def[simp]
  learn_def[simp] Let_def[simp] if_split[split] if_split_asm[split]

method rm_trans_rel_assm = 
  (match premises in P[thin]:"trans_rel ?x ?y ?z" \<Rightarrow> \<open>-\<close>)

lemma is_trans_simp[simp]:
  "s \<midarrow>a\<midarrow>the_ioa\<longrightarrow> t = trans_rel s a t"
  by (simp add:is_trans_def the_ioa_def ioa_def trans_def)
  
method my_fail for msg::"char list" = (print_term msg; fail)

method rm_reachable = (match premises in R[thin]:"reachable ?ioa ?s" \<Rightarrow> \<open>-\<close>)

lemma reach_and_inv_imp_p:"\<lbrakk>reachable the_ioa s; invariant the_ioa i\<rbrakk> \<Longrightarrow> i s"
  by (auto simp add:invariant_def)

method instantiate_invs declares invs =
  (match premises in I[thin]:"invariant ?ioa ?inv" and R:"reachable ?ioa ?s" \<Rightarrow> \<open>
    print_fact I, insert reach_and_inv_imp_p[OF R I]\<close>)+

method instantiate_invs_2 declares invs = (
  (* Deduce that all invariants hold in s *)
  ( insert invs,
    instantiate_invs )?,
  (* Deduce that all invariants hold in t (first deduce that t is reachable) *)
  match premises in R[thin]:"reachable ?ioa ?s" and T:"?s \<midarrow>?a\<midarrow>?ioa\<longrightarrow> ?t" \<Rightarrow> 
    \<open>insert reachable_n[OF R T]\<close>,
  ( insert invs,
    instantiate_invs )?,
  (* Get rid of the reachability assumption *)
  rm_reachable )

text {* If any of m1, m2, or m3 fail, then the whole method fails. *}
method inv_cases methods m1 m2 m3 uses invs declares inv_defs =
  (rule invariantI; (
      ((match premises in "?s \<in> ioa.start ?ioa" \<Rightarrow> \<open>-\<close>); m1 )
    | ((instantiate_invs_2 invs:invs | my_fail "''instantiation failed''");
        (m2 | my_fail "''method 2 failed''"); simp only:is_trans_simp;
          ((induct_tac rule:trans_cases | my_fail "''case analysis failed''"), simp?); rm_trans_rel_assm; m3)
        ) )

method force_inv uses invs declares inv_defs =
  inv_cases \<open>(force simp add:inv_defs ioa_defs)?\<close> \<open>-\<close> \<open>(force simp add:inv_defs split:option.splits)?\<close>
  invs:invs inv_defs:inv_defs

method simp_inv uses invs declares inv_defs =
  inv_cases \<open>simp add:inv_defs ioa_defs\<close> \<open>-\<close> \<open>(simp add:inv_defs split:option.splits; fail)?\<close>
  invs:invs inv_defs:inv_defs

method auto_inv uses invs declares inv_defs =
  inv_cases \<open>auto simp add:inv_defs ioa_defs\<close> \<open>-\<close> \<open>(auto simp add:inv_defs split:option.splits; fail)?\<close>
  invs:invs inv_defs:inv_defs

subsection {* @{term conservative_array}  is an inductive invariant *}

interpretation ba:ballot_array quorums ballot vote for ballot vote .
interpretation bap:ballot_array_props ballot vote quorums for ballot vote 
  by (unfold_locales)

definition conservative_array where conservative_array_def[inv_defs]:
  "conservative_array s \<equiv>  \<forall> i . conservative_at s i"

lemma conservative_inductive:
  "invariant the_ioa conservative_array"
  by (force_inv invs: inv_defs:ballot_array.conservative_array_def ballot_array.conservative_def)

abbreviation safe where "safe s \<equiv> \<forall> i . ballot_array.safe quorums (ballot s) (ba_vote s i)"

subsection {* @{term safe} is invariant } *}

abbreviation safe_at where "safe_at s i \<equiv> ba.safe_at (ballot s) (ba_vote s i)"
    
lemma quorum_ballots_finite_ne:
  assumes "q \<in> quorums"
  shows "finite {ballot s a | a . a \<in> q}" and "{ballot s a | a . a \<in> q} \<noteq> {}"
    using quorums_axioms assms by (auto simp add:quorums_def)
  
lemma trans_imp_prefix_order:
  assumes "s \<midarrow>a\<midarrow>the_ioa\<longrightarrow> t"
  shows "is_prefix_2 quorums (ballot s) (ballot t) (ba_vote s i) (ba_vote t i)" using assms[simplified]
  apply (cases rule:trans_cases)
      apply (auto simp add:is_prefix_2_def inv_proofs_defs split:option.split_asm)[3] defer
   apply (auto simp add:is_prefix_2_def inv_proofs_defs split:option.split_asm)[1]
  subgoal premises prems for acc
  proof (simp add:is_prefix_2_def, rule allI)
    fix a
    have "(ballot s a \<le> ballot t a) 
      \<and> (\<forall> b . (b < ballot s a \<or> (b = ballot s a \<and> vote s a b i \<noteq> None)) \<longrightarrow> vote s a b i = vote t a b i)" (is "?P")
      if "a \<noteq> acc" using prems that by auto
    moreover
    { assume "a = acc"
      have 1:"\<forall>b. vote t a b i = None" using \<open>a = acc\<close> prems by auto
      have 2:"\<exists> q\<in>quorums . \<forall>a2\<in>q. ballot s a2 \<le> ballot t a"
      proof -
        from prems \<open>a = acc\<close> obtain q b where "q \<in> quorums" and "b = Max {ballot s a | a . a \<in> q}"
            and "ballot t a = b" by (cases s, cases t, auto)
        moreover have "ballot s a \<le> Max {ballot s a | a . a \<in> q}" (is "ballot s a \<le> Max ?S") if "a \<in> q" for a
          using quorum_ballots_finite_ne[of q s, OF \<open>q \<in> quorums\<close>] that by (metis (mono_tags, lifting) Max.coboundedI mem_Collect_eq)
        ultimately show ?thesis by auto
      qed
      note 1 2 }
    ultimately show "ballot s a \<le> ballot t a \<and> (\<forall>b. (b < ballot s a \<longrightarrow> vote s a b i = vote t a b i) \<and> (b = ballot s a \<and> (\<exists>y. vote s a b i = Some y) \<longrightarrow> vote s a (ballot s a) i = vote t a (ballot s a) i)) \<or> (\<exists>q\<in>quorums. \<forall>a2\<in>q. ballot s a2 \<le> ballot t a) \<and> (\<forall>b. vote t a b i = None)"
      by force 
  qed
  done

lemma safe_mono:
  -- {* @{term safe_at} is monotonic. *}
  assumes "s \<midarrow>a\<midarrow>the_ioa\<longrightarrow> t" and "safe_at s i v b" and "ba.joined (ballot s) b q" and "q \<in> quorums"
  shows "safe_at t i v b" 
proof -
  have "is_prefix_2 quorums (ballot s) (ballot t) (ba_vote s i) (ba_vote t i)" 
    using assms(1) trans_imp_prefix_order by auto
  with ballot_array_prefix_2.safe_at_mono quorums_axioms assms(2-4) 
  show ?thesis
    by (auto simp add:ballot_array_prefix_2_def ballot_array_prefix_2_axioms_def, fast)
qed

definition inv1 where inv1_def[inv_defs]:
  "inv1 s \<equiv> \<forall> a i . i \<ge> lowest s a \<longrightarrow> ghost_ballot s a i = ballot s a"

lemma inv1: "invariant the_ioa inv1" by (force_inv)
(* nitpick[verbose, card 'v = 2, card 'a = 3, verbose,  card nat = 2, card "'v option" = 3, card "nat option" = 3, expect=none] *)

definition inv2 where inv2_def[inv_defs]:
  "inv2 s \<equiv> \<forall> a b i j . vote s a b i \<noteq> None \<and> j < i-window 
    \<longrightarrow> (\<exists> q \<in> quorums . \<forall> a \<in> q . log s a j \<noteq> None)"
  
lemma inv2: "invariant the_ioa inv2"
  apply (simp_inv invs:inv1 inv_defs:inv_defs) prefer 3 
  nitpick[verbose, card 'v = 2, card 'a = 3, verbose,  card nat = 3, card "'v option" = 3, card "nat option" = 4, expect=none,
      card "nat \<times> nat" = 9, card "('v, 'a) ampr_state" = 2]
  sorry

definition inv3 where inv3_def[inv_defs]:
  "inv3 s \<equiv> \<forall> i . (\<forall> q \<in> quorums . \<exists> a \<in> q . log s a i = None) 
    \<longrightarrow> (\<forall> j . j \<ge> i + window \<longrightarrow> (\<forall> a b . vote s a b j = None))"
  
lemma inv3: "invariant the_ioa inv3"
  apply (simp_inv invs:inv1 inv2 inv_defs:inv_defs) prefer 3
  nitpick[verbose, card 'v = 2, card 'a = 3, verbose,  card nat = 3, card "'v option" = 3, card "nat option" = 4, expect=none,
      card "nat \<times> nat" = 9, card "('v, 'a) ampr_state" = 2]
  sorry
  
definition inv4 where inv4_def[inv_defs]:
  "inv4 s \<equiv> \<forall> a b i . vote s a b i \<noteq> None 
    \<longrightarrow> (\<exists> q \<in> quorums . \<forall> a \<in> q . ghost_ballot s a i \<ge> b)"
  
lemma inv4: "invariant the_ioa inv4"
  apply (simp_inv invs:inv1 inv2 inv3 inv_defs:inv_defs) prefer 3
  nitpick[verbose, card 'v = 2, card 'a = 3, verbose,  card nat = 3, card "'v option" = 3, card "nat option" = 4, expect=none,
      card "nat \<times> nat" = 9, card "('v, 'a) ampr_state" = 2]
  oops
  
definition inv5 where inv5_def[inv_defs]:
  "inv5 s \<equiv> \<forall> a b i . vote s a b i \<noteq> None \<and> i \<ge> lowest s a
    \<longrightarrow> (\<exists> q \<in> quorums . ba.joined (flip (ghost_ballot s) i) b q)"

lemma inv5: "invariant the_ioa inv5"
  apply (simp_inv invs:inv1 inv_defs:inv_defs ballot_array.joined_def)
     apply (auto simp add:inv5_def ballot_array.joined_def split:option.splits, blast)[1]
  prefer 2
  nitpick[verbose, card 'v = 2, card 'a = 3, verbose,  card nat = 3, card "'v option" = 3, card "nat option" = 4, expect=none,
      card "nat \<times> nat" = 9, card "('v, 'a) ampr_state" = 2]
  oops
  
lemma safe_votes: 
  fixes s :: "('v, 'a) ampr_state" and t a i v q
  assumes "do_vote a i q v s t" and "conservative_array s" and "safe s"
  shows "safe_at t i v (ballot s a)"
proof -
  let ?b = "ballot s a"
  from \<open>do_vote a i q v s t\<close> have 1:"proved_safe_at s ?b i q v" and 2:"q \<in> quorums" and 3:"\<And> a . a \<in> q \<Longrightarrow> lowest s a \<ge> i" by simp_all
  from 1 \<open>conservative_array s\<close> \<open>safe s\<close> bap.proved_safe_at_abs_imp_safe_at[of ?b "ba_vote s i" "ballot s"]
  have 4:"safe_at s i v ?b"  by (auto simp add:ballot_array.safe_def conservative_array_def split:option.splits)
  have 5:"ba.joined (ballot s) ?b q" using \<open>do_vote a i q v s t\<close> 
    by (auto simp add:ballot_array.proved_safe_at_abs_def ballot_array.joined_def)
  have 6:"s \<midarrow>Internal\<midarrow>the_ioa\<longrightarrow> t" using \<open>do_vote a i q v s t\<close> by (metis (full_types) is_trans_simp trans_rel.simps(2))
  from 5 2 safe_mono[of s "Internal" t i v ?b, OF 6 4] show ?thesis by auto
qed

lemma safe_inv:
  "invariant the_ioa safe"
apply (try_solve_inv2 case_thm:trans_cases inv_proofs_defs:inv_proofs_defs ballot_array.safe_def invs:invs)
subgoal premises prems for s t act
proof (auto simp add:ballot_array.safe_def split:option.splits)
  fix i b a v
  assume "vote t i a b = Some v"
  show "safe_at t i v b"
  proof (cases "vote s i a b = vote t i a b")
    case True
    hence "safe_at s i v b" using prems(1) by (metis \<open>vote t i a b = Some v\<close> ballot_array.safe_def option.simps(5))
    thus ?thesis using prems(2) safe_mono
      by fastforce 
  next
    case False thus ?thesis using safe_votes
      using \<open>vote t i a b = Some v\<close> prems(1-3) by blast  
  qed
qed
done
declare safe_inv[invs]

subsection {* Finally, the proof that agreement holds (trivial, follows immediately from safe).*}

definition agreement where 
  "agreement s \<equiv> \<forall> v w i . chosen s i v \<and> chosen s i w \<longrightarrow> v = w"

lemma agreement:"invariant the_ioa agreement"
apply(rule invariantI)
    apply(auto simp add: inv_proofs_defs agreement_def ballot_array.chosen_def ballot_array.chosen_at_def)[1]
  apply (metis (mono_tags, lifting) IOA.invariant_def IOA.reachable_n agreement_def proof.safe_inv proof_axioms ballot_array_props.intro ballot_array_props.safe_imp_agreement quorums_axioms the_ioa_def)
done

end

end