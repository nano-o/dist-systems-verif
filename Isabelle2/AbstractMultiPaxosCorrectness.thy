section {* Proof of the agreement property of AbstractMultiPaxos. *}

theory AbstractMultiPaxosCorrectness
imports AbstractMultiPaxos7 "../../IO-Automata/Simulations" "../../IO-Automata/IOA_Automation" 
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

declare propose_def[simp] join_ballot_def[simp] do_vote_def[simp]
  learn_def[simp] Let_def[simp] split_if[split] split_if_asm[split]

lemma vote_one_inst_only:
  assumes "do_vote a i q v s s'" and "i \<noteq> j"
  shows "vote s j a = vote s' j a "
using assms by auto

lemma vote_ballot_unch:
  assumes "do_vote a i q v s s'"
  shows "ballot s = ballot s'"
using assms by (auto split add:option.split_asm)

subsection {* @{term conservative_array}  is an inductive invariant *}

declare ballot_array.conservative_array_def[inv_proofs_defs]

abbreviation conservative_array where
"conservative_array s \<equiv>  \<forall> i . conservative_at s i"

lemma conservative_inductive:
  "invariant the_ioa conservative_array"
apply (try_solve_inv2 inv_proofs_defs:inv_proofs_defs invs:invs)
    apply (force simp add:ballot_array.conservative_def)
  apply (case_tac a) 
  apply (auto simp add:inv_proofs_defs split add:option.split_asm)
done
declare conservative_inductive[invs]

subsection {* @{term safe}  is an inductive invariant *}

abbreviation safe_at where "safe_at s i \<equiv> ballot_array.safe_at  quorums (ballot s) (vote s i)"

lemma trans_imp_prefix_order:
  assumes "s \<midarrow>a\<midarrow>the_ioa\<longrightarrow> t"
  shows "is_prefix (ballot s) (ballot t) (vote s i) (vote t i)" using assms
by (cases a) (auto simp add:is_prefix_def inv_proofs_defs split add:option.split_asm)
    
lemma safe_mono:
  -- {* @{term safe_at} is monotonic. *}
  assumes "s \<midarrow>a\<midarrow>the_ioa\<longrightarrow> t" and "safe_at s i v b"
  shows "safe_at t i v b" using assms 
  by (drule_tac trans_imp_prefix_order)
    (meson assms(1) ballot_array_prefix.safe_at_mono ballot_array_prefix_axioms_def ballot_array_prefix_def quorums_axioms trans_imp_prefix_order)

abbreviation safe where "safe s \<equiv> \<forall> i . ballot_array.safe  quorums (ballot s) (vote s i)"

text {* TODO: make this proof generic to all algorithms in which the ballot array grows with safe_at values *}
lemma safe_inv:
  "invariant the_ioa safe"
apply (try_solve_inv2 inv_proofs_defs:inv_proofs_defs ballot_array.safe_def invs:invs)
subgoal premises prems for s t act
proof (auto simp add:ballot_array.safe_def split add:option.splits)
  fix i b a v
  assume "vote t i a b = Some v"
  show "safe_at t i v b"
  proof (cases "vote s i a b = Some v")
    case True
    hence "safe_at s i v b" using prems(1) by (metis ballot_array.safe_def option.simps(5))
    thus "safe_at t i v b" using prems(2) safe_mono by simp
  next
    case False
    with prems(2) \<open>vote t i a b = Some v\<close> obtain q where "do_vote a i q v s t" and "ballot s a = b"
      apply(simp add:is_trans_def the_ioa_def amp_ioa_def amp_trans_def del:do_vote_def)
      apply(elim amp_trans_rel.elims)
      apply simp apply simp defer apply simp
      apply (smt amp_ioa.do_vote_def amp_state.iffs amp_state.surjective amp_state.update_convs(3) fun_upd_apply option.sel)
      done
    hence "proved_safe_at s i q (ballot s a) v" and "q \<in> quorums" and "\<forall> a2 \<in> q . ballot s a \<le> ballot s a2" 
      by (auto simp add:ballot_array.proved_safe_at_2_def split add:nat.splits)
    hence "safe_at s i v b" using quorums_axioms prems(1) prems(3) `ballot s a = b`
      ballot_array_props.proved_safe_at_2_imp_safe_at[of quorums "ballot s a" "vote s i" "ballot s" q v]
      by (auto simp add:ballot_array.safe_def ballot_array_props_def split add:option.splits)
    thus "safe_at t i v b" using prems(2) safe_mono by simp
  qed
qed
done
declare safe_inv[invs]

subsection {* Finally, the proof that agreement holds. *}

definition agreement where 
  "agreement s \<equiv> \<forall> v w i . chosen s i v \<and> chosen s i w \<longrightarrow> v = w"

lemma agreement:"invariant the_ioa agreement"
apply(rule invariantI)
    apply(auto simp add: inv_proofs_defs agreement_def ballot_array.chosen_def ballot_array.chosen_at_def)[1]
  apply (metis (mono_tags, lifting) IOA.invariant_def IOA.reachable_n agreement_def amp_proof.safe_inv amp_proof_axioms ballot_array_props.intro ballot_array_props.safe_imp_agreement quorums_axioms the_ioa_def)
done

end

end