section {* Proof of the agreement property of AbstractMultiPaxos. *}

theory AbstractMultiPaxosCorrectness
imports AbstractMultiPaxos IOA_Automation BallotArrayProperties 
begin

locale amp_proof = quorums quorums + amp_ioa quorums for quorums +
  fixes the_ioa
  defines "the_ioa \<equiv> amp_ioa"
  -- {* Here we have to fix the constant @{term the_ioa} in order to fix all type variables.
  Otherwise, there are problems in Eisbach when matching the same polymorphic constant appearing in several terms. *}
begin

interpretation IOA .

subsection {* Automation setup and a few lemmas *}

lemmas amp_ioa_defs =
   is_trans_def actions_def amp_trans_def amp_start_def
   externals_def amp_ioa_def the_ioa_def paxos_asig_def

declare amp_ioa_defs[inv_proofs_defs]
declare amp_ioa_def[inv_proofs_defs]

declare propose_def[simp] join_ballot_def[simp] do_vote_def[simp]
  learn_def[simp] Let_def[simp] if_split[split] if_split_asm[split]

subsection {* @{term conservative_array}  is an inductive invariant *}

declare ballot_array.conservative_array_def[inv_proofs_defs]

abbreviation conservative_array where
"conservative_array s \<equiv>  \<forall> i . conservative_at s i"

lemma conservative_inductive:
  "invariant the_ioa conservative_array"
  apply (try_solve_inv2 case_thm:trans_cases inv_proofs_defs:inv_proofs_defs ballot_array.conservative_def invs:invs)
  apply (case_tac a)
    apply (auto simp add:inv_proofs_defs split:option.split_asm)
done
declare conservative_inductive[invs]

subsection {* @{term safe} is inductive relative to @{term conservative_array}} *}

text {* 
We first prove that when the algorithm takes a step, the old state is a prefix
of the new state. With this fact, we obtain that (1) a safe value remains safe after a step using the lemma @{thm ballot_array_prefix.safe_at_mono }.
Then we prove that (2) when a vote is cast at a ballot b from a safe state, then the voted value is safe at b.
Given those two facts, the inductiveness of safe follows.  *}

abbreviation safe_at where "safe_at s i \<equiv> ballot_array.safe_at  quorums (ballot s) (vote s i)"

lemma trans_imp_prefix_order:
  assumes "s \<midarrow>a\<midarrow>the_ioa\<longrightarrow> t"
  shows "is_prefix (ballot s) (ballot t) (vote s i) (vote t i)" using assms
by (cases a) (auto simp add:is_prefix_def inv_proofs_defs split:option.split_asm)

lemma safe_mono:
  -- {* @{term safe_at} is monotonic. *}
  assumes "s \<midarrow>a\<midarrow>the_ioa\<longrightarrow> t" and "safe_at s i v b"
  shows "safe_at t i v b" using assms ballot_array_prefix.safe_at_mono
by (metis ballot_array_prefix_axioms.intro ballot_array_prefix_def quorums_axioms trans_imp_prefix_order)

abbreviation safe where "safe s \<equiv> \<forall> i . ballot_array.safe  quorums (ballot s) (vote s i)"

lemma safe_votes:
  assumes "s \<midarrow>aa\<midarrow>the_ioa\<longrightarrow> t" and "vote s i a b  \<noteq> vote t i a b" and "vote t i a b = Some v"
    and "conservative_array s" and "safe s"
  shows "safe_at t i v b" 
  using assms
  apply (cases aa)
    apply (auto simp add:inv_proofs_defs)
  subgoal premises prems
  proof -
    have "safe_at s i v (ballot s a)" by (smt assms(4) ballot_array.safe_def ballot_array_props.intro ballot_array_props.proved_safe_at_abs_imp_safe_at option.case_eq_if option.distinct(1) option.sel prems(2) prems(6) quorums_axioms) 
    thus ?thesis by (metis amp_state.select_convs(2) amp_state.select_convs(3) amp_state.surjective amp_state.update_convs(3) assms(1) fun_upd_apply prems(9) safe_mono) 
  qed
  done

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
  apply (metis (mono_tags, lifting) IOA.invariant_def IOA.reachable_n agreement_def amp_proof.safe_inv amp_proof_axioms ballot_array_props.intro ballot_array_props.safe_imp_agreement quorums_axioms the_ioa_def)
done

end

end