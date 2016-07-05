section {* Proof of the agreement property of AbstractMultiPaxos. *}

theory AbstractMultiPaxosR1Correctness
imports AbstractMultiPaxosR1 "../../IO-Automata/IOA_Automation"
  BallotArrayProperties
begin

locale amp_proof = IOA + quorums quorums + amp_ioa quorums for
     quorums :: "'a set set" +
  fixes the_ioa :: "(('v,'a,'l)amp_state, ('v,'a,'l)amp_action) ioa"
  defines "the_ioa \<equiv> amp_ioa"
begin

subsection {* Automation setup *}

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

subsection {* Auxiliary invariants *}

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

declare
  ballot_array.conservative_array_def[inv_proofs_defs]
  ballot_array.conservative_def[inv_proofs_defs]

abbreviation conservative_array where
  "conservative_array s \<equiv>  \<forall> i . ballot_array.conservative_array (vote s i)"

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

abbreviation safe_at where "safe_at s i \<equiv> ballot_array.safe_at quorums (ballot s) (vote s i)"

lemma safe_mono:
  -- {* @{term safe_at} is monotonic. *}
  assumes "s \<midarrow>a\<midarrow>the_ioa\<longrightarrow> t" and "safe_at s i v b"
  shows "safe_at t i v b" using assms ballot_array_prefix.safe_at_mono
by (metis ballot_array_prefix_axioms_def ballot_array_prefix_def quorums_axioms trans_imp_prefix_order) 

definition inv3 where 
  inv3_def[inv_proofs_defs]:"inv3 s \<equiv> \<forall> a b . case onebs s a b of None \<Rightarrow> True
    | Some maxs \<Rightarrow> 
      (\<forall> i . maxs i = distributed_safe_at.acc_max (vote s i) a b)
      \<and> (ballot s a \<ge> b)"

lemma inv3:
  "invariant the_ioa inv3"
apply (rule invariantI)
apply (force simp add:inv_proofs_defs)
apply instantiate_invs_2
apply (unfold_to_trans_rel)
apply ((induct_tac rule:trans_cases, simp); rm_trans_rel_assm)
          apply (auto simp add:inv_proofs_defs  split add:option.splits)[2]
      defer defer apply (auto simp add:inv_proofs_defs  split add:option.splits)[2]
      apply (metis dual_order.trans nat_less_le)
  subgoal premises prems for s t act a i v
  proof -
    { fix a2 b maxs
      assume a1:"onebs s a2 b = Some maxs"
      from a1 prems(1) have 1:"\<And> j . maxs j = distributed_safe_at.acc_max (vote s j) a2 b" 
        by (simp add:inv3_def split add:option.splits split_if split_if_asm)
      from a1 prems(1,6) have 2:"ballot t a2 \<ge> b" by (simp add:inv3_def split add:option.splits)
      { fix j assume "j \<noteq> i \<or> a \<noteq> a2"
        hence "maxs j = distributed_safe_at.acc_max (vote t j) a2 b" using 1 prems(6) by (auto simp add:distributed_safe_at.acc_max_def) }
      note 3 = this
      { fix j assume "j = i \<and> a = a2"
        hence "maxs j = distributed_safe_at.acc_max (vote t j) a2 b" using 1 prems(6) a1 2 apply (simp add:distributed_safe_at.acc_max_def)
          by (smt Collect_cong amp_state.select_convs(2) amp_state.surjective amp_state.update_convs(3) dual_order.strict_trans1 neq_iff split_cong) }
      note this 2 3 }
    thus ?thesis apply (simp add:inv3_def split add:option.splits)
      by (metis (no_types, lifting) amp_ioa.do_vote_def amp_state.select_convs(5) amp_state.surjective amp_state.update_convs(3) prems(6))
  qed
done
declare inv3[invs]
      
(* nitpick[no_assms, show_consts, verbose, card 'a = 3, card 'v = 2, card nat = 2, card "'v option" = 3, card "nat option" = 3,
    card "('v \<times> nat) option" = 5, card "'v \<times> nat" = 4, card unit = 1, card "('v, 'a) amp_state" = 32, card 'l = 1, expect=none]  *)
          

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
    from prems and safe_mono have 1:"\<And> i v b . safe_at s i v b \<Longrightarrow> safe_at t i v b" by (simp add:inv2_def)
    with prems show ?thesis
    apply (unfold_to_trans_rel)
    apply ((induct_tac rule:trans_cases, simp); rm_trans_rel_assm)
              apply (auto simp add:inv_proofs_defs split add:option.splits)[3]
        apply (fastforce simp add:inv_proofs_defs split add:option.splits)
        apply clarify
      subgoal premises prems for i b v q
      proof -
        from \<open>safe s\<close> \<open>suggest i b v q s t\<close> have "safe t" by (metis amp_state.select_convs(2) amp_state.select_convs(3) amp_state.surjective amp_state.update_convs(4) suggest_def) 
        moreover have "inv2 t"
        proof (auto simp add: inv2_def split add:option.split)
          fix j b2 w
          assume "suggestion t j b2 = Some w"
          show "safe_at t j w b2"
          proof (cases "i \<noteq> j \<or> b2 \<noteq> b")
            case True
            thus "safe_at t j w b2" using \<open>inv2 s\<close> \<open>suggest i b v q s t\<close>  apply (simp add:inv2_def split add:option.splits)
              apply (smt \<open>suggestion t j b2 = Some w\<close> amp_state.ext_inject amp_state.surjective amp_state.update_convs(4) fun_upd_def)
              by (smt \<open>suggestion t j b2 = Some w\<close> amp_state.ext_inject amp_state.surjective amp_state.update_convs(4) fun_upd_def)
          next
            case False
            hence "v = w" using \<open>suggest i b v q s t\<close>  \<open>suggestion t j b2 = Some w\<close> by simp
            have 2:"\<And> a . a \<in> q \<Longrightarrow> b \<le> ballot s a" using  \<open>suggest i b v q s t\<close> \<open>inv3 s\<close> by (auto simp add:inv3_def split add:option.splits)
            have 1:"\<And> a . a \<in> q \<Longrightarrow> case onebs s a b of Some f \<Rightarrow> f i = distributed_safe_at.acc_max (vote s i) a b | None \<Rightarrow> False" 
              using \<open> suggest i b v q s t\<close> \<open>inv3 s\<close> by (simp add:inv3_def split add:option.splits)
            hence 3:"distributed_safe_at.max_pair q (\<lambda> a . the (onebs s a b) i) = distributed_safe_at.max_pair q (\<lambda> a . distributed_safe_at.acc_max (vote s i) a b)"
              apply (simp add:distributed_safe_at.max_pair_def split add:option.splits) by (smt SUP_def image_cong option.case_eq_if)
            have "distributed_safe_at.proved_safe_at quorums (ballot s) (vote s i) q b v" using 1 2 3 \<open>suggest i b v q s t\<close> \<open>v = w\<close> 
              by (auto simp add:distributed_safe_at.proved_safe_at_def split add:option.splits)
            interpret p:dsa_properties "ballot s" "vote s i" quorums by unfold_locales
            show ?thesis by (metis False \<open>p.proved_safe_at q b v\<close> \<open>v = w\<close> option.simps(5) p.proved_safe_at_imp_safe_at p.safe_def prems(10) prems(2) prems(7)) 
          qed
        qed
        ultimately show ?thesis by auto
      qed
    done
  qed
done
declare inv2_and_safe[invs]

definition inv5 where
  inv5_def[inv_proofs_defs]:"inv5 s \<equiv> \<forall> i a b . ballot s a < b \<longrightarrow> vote s i a b = None"

lemma  inv5:"invariant the_ioa inv5"
apply (rule invariantI)
apply (force simp add:inv_proofs_defs)
apply instantiate_invs_2
apply (unfold_to_trans_rel)
apply (induct_tac rule:trans_cases, simp)
apply (auto simp add:inv_proofs_defs split add:option.splits)
done
declare inv5[invs]

lemma chosen_mono: assumes "chosen s i v" and "s \<midarrow>a\<midarrow>the_ioa\<longrightarrow> t" and "inv5 s"
  shows "chosen t i v" using assms
apply (unfold_to_trans_rel)
apply ((induct_tac rule:trans_cases, simp); rm_trans_rel_assm)
apply (auto simp add:inv_proofs_defs split add:option.splits)[3] defer
apply (auto simp add:inv_proofs_defs split add:option.splits)[1]
apply (cases s, cases t, auto simp add:inv_proofs_defs ballot_array.chosen_def ballot_array.chosen_at_def split add:option.splits)
by (metis option.distinct(1))
(* nitpick[no_assms, show_consts, verbose,expect=none unknown, card 'a = 3, card 'v = 2, card 'l = 1, card 'v option = 3, card nat = 2, card nat option = 3,
  card "(nat \<Rightarrow> ('v \<times> nat) option) option" = 10, card "('v \<times> nat) option" = 5] *)

definition inv4 where 
  inv4_def[inv_proofs_defs]:"inv4 s \<equiv> \<forall> i l . case learned s l i of Some v \<Rightarrow> chosen s i v | None \<Rightarrow> True"

lemma  inv4:"invariant the_ioa inv4"
apply (rule invariantI)
apply (force simp add:inv_proofs_defs)
apply instantiate_invs_2
apply (unfold_to_trans_rel)
apply (induct_tac rule:trans_cases, simp)
apply (auto simp add:inv_proofs_defs split add:option.splits)[3] defer
apply (auto simp add:inv_proofs_defs split add:option.splits)[1]
apply (insert chosen_mono[simplified inv_proofs_defs])
apply (auto simp add:inv4_def inv5_def  split add:option.splits)
by (metis (mono_tags) amp_state.select_convs(3) amp_state.surjective amp_state.update_convs(3) fun_upd_same)
declare inv4[invs]

subsection {* Finally, the proof of agreement. *}

definition agreement where 
  "agreement s \<equiv> \<forall> i l1 l2 . let v = learned s l1 i; w = learned s l2 i 
    in v \<noteq> None \<and> w \<noteq> None \<longrightarrow> v = w"

lemma agreement:"invariant the_ioa agreement"
apply(rule invariantI)
    apply(auto simp add: inv_proofs_defs agreement_def ballot_array.chosen_def ballot_array.chosen_at_def)[1]
  apply instantiate_invs_2 
  apply (auto simp add:inv4_def agreement_def split add:option.splits)
  by (metis ballot_array_props.intro ballot_array_props.safe_imp_agreement quorums_axioms)

end

end