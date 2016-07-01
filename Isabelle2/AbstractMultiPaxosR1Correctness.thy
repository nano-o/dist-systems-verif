section {* Proof of the agreement property of AbstractMultiPaxos. *}

theory AbstractMultiPaxosR1Correctness
imports AbstractMultiPaxosR1 "../../IO-Automata/IOA_Automation"
  BallotArrayProperties
begin

locale amp_proof = IOA + quorums quorums + amp_ioa quorums learners for
     quorums :: "'a set set" and learners :: "'l set" +
  fixes the_ioa :: "(('v,'a)amp_state, ('v,'a,'l)amp_action) ioa"
  defines "the_ioa \<equiv> amp_ioa"
begin

subsection {* Automation setup and a few lemmas *}

lemmas amp_ioa_defs =
   is_trans_def actions_def amp_trans_def amp_start_def
   externals_def amp_ioa_def amp_asig_def

declare amp_ioa_defs[inv_proofs_defs]
declare the_ioa_def[inv_proofs_defs]

declare propose_def[simp] join_ballot_def[simp] do_vote_def[simp] suggest_def[simp]
  learn_def[simp] Let_def[simp] split_if[split] split_if_asm[split]

(*  Nitpick config:
nitpick[no_assms, show_consts, verbose, card 'a = 3, card 'v = 2, card nat = 2, card "'v option" = 3, card "nat option" = 3,
    card "('v \<times> nat) option" = 5, card "'v \<times> nat" = 4, card unit = 1, card "('v, 'a) amp_state" = 32]
*)
method rm_trans_rel_assm = 
  (match premises in P[thin]:"amp_trans_rel ?x ?y ?z" \<Rightarrow> \<open>-\<close>)
method unfold_to_trans_rel = 
  (simp add:is_trans_def the_ioa_def amp_ioa_def amp_trans_def)

definition inv1 where
  -- {* acceptors only vote for the suggestion. *}
  inv1_def[inv_proofs_defs]:"inv1 s \<equiv> \<forall> i a b . let v = vote s i a b in
    v \<noteq> None \<longrightarrow> v = suggestion s i b"

lemma inv1:
  "invariant the_ioa inv1"
apply (rule invariantI)
apply (force simp add:inv_proofs_defs invs)
apply (unfold_to_trans_rel)
apply (rm_reachable)
apply ((induct_tac rule:trans_cases, simp); rm_trans_rel_assm)
apply (simp_all add:inv1_def)
by (metis option.simps(3))
declare inv1[invs]

abbreviation safe_at where "safe_at s i \<equiv> ballot_array.safe_at quorums (ballot s) (vote s i)"

declare 
  ballot_array.conservative_array_def[inv_proofs_defs]
  ballot_array.conservative_def[inv_proofs_defs]

abbreviation conservative_array where
"conservative_array s \<equiv>  \<forall> i . conservative_at s i"

lemma conservative:
  "invariant the_ioa conservative_array"
apply (rule invariantI)
apply (force simp add:inv_proofs_defs)
apply instantiate_invs_2
apply (unfold_to_trans_rel)
apply (induct_tac rule:trans_cases, simp)
apply (auto simp add:ballot_array.conservative_def)[3]
defer
apply (auto simp add:ballot_array.conservative_def)[1]
subgoal premises prems using prems(1,3,5)  apply (simp add:inv_proofs_defs split add:option.splits) by metis
done
declare conservative[invs]

lemma trans_imp_prefix_order:
  assumes "s \<midarrow>a\<midarrow>the_ioa\<longrightarrow> t"
  shows "is_prefix (ballot s) (ballot t) (vote s i) (vote t i)" using assms
  apply (simp add:inv_proofs_defs)
  apply (induct rule:trans_cases)
  apply (auto simp add:is_prefix_def inv_proofs_defs split add:option.split_asm)
done

lemma safe_mono:
  -- {* @{term safe_at} is monotonic. *}
  assumes "s \<midarrow>a\<midarrow>the_ioa\<longrightarrow> t" and "safe_at s i v b"
  shows "safe_at t i v b" using assms ballot_array_prefix.safe_at_mono
by (metis ballot_array_prefix_axioms.intro ballot_array_prefix_def quorums_axioms trans_imp_prefix_order)

definition inv2 where
  -- {* a suggestion is safe. *}
  inv2_def[inv_proofs_defs]:"inv2 s \<equiv> \<forall> i b . case suggestion s i b of Some v \<Rightarrow> safe_at s i v b | None \<Rightarrow> True"

abbreviation safe where "safe s \<equiv> \<forall> i . ballot_array.safe  quorums (ballot s) (vote s i)"
declare ballot_array.safe_def[inv_proofs_defs]

lemma inv2_and_safe:
  "invariant the_ioa (\<lambda> s . inv2 s \<and> safe s)"
apply (rule invariantI)
    apply (force simp add:inv_proofs_defs invs)
  apply instantiate_invs_2
  subgoal premises prems for s t a
  proof -
    from prems and safe_mono have 1:"\<And> i v b . safe_at s i v b \<Longrightarrow> safe_at t i v b"
      by (simp add:inv2_def)
    with prems show ?thesis
    apply (unfold_to_trans_rel)
    apply ((induct_tac rule:trans_cases, simp); rm_trans_rel_assm)
              apply (auto simp add:inv_proofs_defs split add:option.splits)[3]
        apply (fastforce simp add:inv_proofs_defs split add:option.splits)
      apply auto
      subgoal premises prems for i b v q
      proof -
        from prems(5,8,2) have "safe_at s i v b"
          by (smt ballot_array.safe_def distributed_safe_at.intro distributed_safe_at.proved_safe_at_imp_safe_at option.case_eq_if option.distinct(1) option.sel quorums_axioms) 
        thus ?thesis using prems(4,9) 1 by (simp add:inv2_def split add:option.splits)
      qed
    done
  qed
done

subsection {* Finally, the proof that agreement holds (trivial, follows immediately from safe). *}

definition agreement where 
  "agreement s \<equiv> \<forall> v w i . chosen s i v \<and> chosen s i w \<longrightarrow> v = w"

lemma agreement:"invariant the_ioa agreement" 
apply(rule invariantI)
apply(auto simp add: inv_proofs_defs agreement_def ballot_array.chosen_def ballot_array.chosen_at_def)[1]
by (metis (mono_tags, lifting) IOA.reach_and_inv_imp_p IOA.reachable_n agreement_def ballot_array_props.intro ballot_array_props.safe_imp_agreement inv2_and_safe quorums_axioms)

end

end