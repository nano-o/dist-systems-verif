section {* Proof of the agreement property of AbstractMultiPaxos. *}

theory AbstractMultiPaxosR1Correctness
imports AbstractMultiPaxosR1 IOA_Automation
  BallotArrayProperties
begin

locale ampr1_proof = IOA + quorums quorums + ampr1_ioa quorums for
     quorums :: "'a set set" +
  fixes the_ioa 
  defines "the_ioa \<equiv> ioa"
begin

interpretation dsa:distributed_safe_at quorums ballot vote for ballot vote .

subsection {* Automation setup *}

lemmas ioa_defs =
   is_trans_def actions_def trans_def start_def start_s_def
   externals_def ioa_def asig_def

declare ioa_defs[inv_proofs_defs]
declare the_ioa_def[inv_proofs_defs]

declare propose_def[simp] join_ballot_def[simp] do_vote_def[simp] suggest_def[simp]
  learn_def[simp] Let_def[simp] if_split[split] if_split_asm[split]
  acquire_leadership_def[simp]

(*  Nitpick config:
nitpick[no_assms, show_consts, verbose, card 'a = 3, card 'v = 2, card nat = 2, card "'v option" = 3, card "nat option" = 3,
    card "('v \<times> nat) option" = 5, card "'v \<times> nat" = 4, card unit = 1, card "('v, 'a) ampr1_state" = 32]
*)
method rm_trans_rel_assm = 
  (match premises in P[thin]:"trans_rel ?x ?y ?z" \<Rightarrow> \<open>-\<close>)
method unfold_to_trans_rel = 
  (simp add:is_trans_def the_ioa_def ioa_def trans_def)


subsection {* Auxiliary invariants *}

definition inv7 where inv7_def[inv_proofs_defs]:
  "inv7 s \<equiv> \<forall> a . ampr1_state.leader s a \<longrightarrow> leader (ballot s a) = a"

lemma inv7: "invariant the_ioa inv7"
apply (rule invariantI)
apply (force simp add:inv_proofs_defs)
apply (unfold_to_trans_rel)
apply (rm_reachable)
apply ((induct_tac rule:trans_cases, simp); rm_trans_rel_assm)
apply (auto simp add:inv_proofs_defs)
done
declare inv7[invs]

definition inv6 where inv6_def[inv_proofs_defs]:
  "inv6 s \<equiv> \<forall> a b i . leader b = a \<and> (ballot s a < b \<or> (ballot s a = b \<and> \<not> ampr1_state.leader s a))
    \<longrightarrow> suggestion s i b = None"

lemma inv6: "invariant the_ioa inv6"
apply (rule invariantI)
apply (force simp add:inv_proofs_defs)
apply instantiate_invs_2
apply (unfold_to_trans_rel)
apply ((induct_tac rule:trans_cases, simp); rm_trans_rel_assm)
apply (auto simp add:inv_proofs_defs)
done
declare inv6[invs]

definition inv1 where inv1_def[inv_proofs_defs]:
  -- {* acceptors only vote for the suggestion. *}
  "inv1 s \<equiv> \<forall> i a b . let v = vote s i a b in v \<noteq> None \<longrightarrow> v = suggestion s i b"

lemma inv1:
  "invariant the_ioa inv1"
apply (rule invariantI)
apply (force simp add:inv_proofs_defs invs)
apply instantiate_invs_2
apply (unfold_to_trans_rel)
apply ((induct_tac rule:trans_cases, simp); rm_trans_rel_assm)
              apply (simp_all add:inv1_def)
    apply (metis option.simps(3))
  apply (simp add:inv7_def inv6_def)
  apply force
done
declare inv1[invs]

declare
  ballot_array.conservative_array_def[inv_proofs_defs]
  ballot_array.conservative_def[inv_proofs_defs]

abbreviation conservative_array where
  "conservative_array s \<equiv>  \<forall> i . ballot_array.conservative_array (vote s i)"

lemma conservative: "invariant the_ioa conservative_array"
proof -
  have "\<And> s . inv1 s \<Longrightarrow> conservative_array s"
    by (auto simp add:inv_proofs_defs split:option.splits) (metis option.sel)
  with inv1 show ?thesis  using IOA.invariant_def by blast
qed
declare conservative[invs]

lemma trans_imp_prefix_order:
    -- {* This is used to show that safe_at is monotonic *}
  assumes "s \<midarrow>a\<midarrow>the_ioa\<longrightarrow> t"
  shows "is_prefix (ballot s) (ballot t) (vote s i) (vote t i)" using assms
  apply (simp add:inv_proofs_defs)
  apply (induct rule:trans_cases)
  apply (auto simp add:is_prefix_def inv_proofs_defs split:option.split_asm)
done

abbreviation safe_at where "safe_at s i \<equiv> ballot_array.safe_at quorums (ballot s) (vote s i)"

lemma safe_mono:
  -- {* @{term safe_at} is monotonic. *}
  assumes "s \<midarrow>a\<midarrow>the_ioa\<longrightarrow> t" and "safe_at s i v b"
  shows "safe_at t i v b" using assms ballot_array_prefix.safe_at_mono
by (metis ballot_array_prefix_axioms_def ballot_array_prefix_def quorums_axioms trans_imp_prefix_order) 

definition inv3 where inv3_def[inv_proofs_defs]:
  "inv3 s \<equiv> \<forall> a b maxs i . onebs s a b = Some maxs \<longrightarrow>
  maxs i = acc_max (vote s i) a b \<and> ballot s a \<ge> b"
  
lemma inv3: "invariant the_ioa inv3"
  apply (rule invariantI)
   apply (force simp add:inv_proofs_defs)
  apply instantiate_invs_2
  apply (unfold_to_trans_rel)
  apply ((induct_tac rule:trans_cases, simp); rm_trans_rel_assm;
      (simp add:inv_proofs_defs  split:option.splits; fail)?)
   apply (auto simp add:inv_proofs_defs  split:option.splits)[1]
   apply (meson nat_less_le order_trans)
  apply (auto simp add:inv_proofs_defs acc_max_def dsa.acc_max_def dsa.a_votes_def 
      distributed_safe_at.acc_max_def  split:option.splits)
   apply (smt Collect_cong not_less prod.case_eq_if)
  by (smt Collect_cong not_less prod.case_eq_if)
declare inv3[invs]

(* nitpick[no_assms, show_consts, verbose, card 'a = 3, card 'v = 2, card nat = 2, card "'v option" = 3, card "nat option" = 3,
    card "('v \<times> nat) option" = 5, card "'v \<times> nat" = 4, card unit = 1, card "('v, 'a) ampr1_state" = 32, card 'l = 1, expect=none]  *)

definition inv5 where inv5_def[inv_proofs_defs]:
  "inv5 s \<equiv> \<forall> a b f i v b' . onebs s a b = Some f \<and> f i = {(v,b')}
    \<longrightarrow> (vote s i a b' = Some v)"
lemma inv5:"invariant the_ioa inv5"
  apply (rule invariantI)
   apply (force simp add:inv_proofs_defs)
  apply instantiate_invs_2
  apply (unfold_to_trans_rel)
  apply ((induct_tac rule:trans_cases, simp); rm_trans_rel_assm) oops
(* declare inv5[invs] *)

bundle trace_simp = [[simp_trace_new interactive mode=full]]

method instantiate_inv uses inv = (
  (* Deduce that all invariants hold in s *)
  ( insert inv,
    instantiate_invs )?,
  (* Deduce that all invariants hold in t (first deduce that t is reachable) *)
  match premises in R[thin]:"reachable ?ioa ?s" and T:"?s \<midarrow>?a\<midarrow>?ioa\<longrightarrow> ?t" \<Rightarrow> 
    \<open>insert reachable_n[OF R T]\<close>,
  ( insert inv,
    instantiate_invs )?,
  (* Get rid of the reachability assumption *)
  rm_reachable )

definition inv11 where inv11_def[inv_proofs_defs]:
  "inv11 s \<equiv> \<forall> a b f i . onebs s a b = Some f \<longrightarrow> f i = acc_max (vote s i) a b"
lemma inv11:"invariant the_ioa inv11"
  apply (rule invariantI)
   apply (simp add:inv_proofs_defs dsa.q_votes_def max_by_key_def)
  apply (instantiate_inv inv:inv3)
  apply (unfold_to_trans_rel)
  apply ((induct_tac rule:trans_cases, simp; rm_trans_rel_assm))
       apply ((simp_all add:inv_proofs_defs))[2] defer
     apply ((simp_all add:inv_proofs_defs))[3]
  apply (simp (no_asm_use) add:inv_proofs_defs)
  by blast
declare inv11[invs]
  
definition inv4 where inv4_def[inv_proofs_defs]:
  "inv4 s \<equiv> \<forall> i b q . q \<in> quorums \<and> (\<forall> a \<in> q . onebs s a b \<noteq> None) \<longrightarrow>
  ( max_by_key (\<Union> a \<in> q . the (onebs s a b) i) snd = (max_by_key (dsa.q_votes (vote s i) q b) snd))"
lemma inv4:"invariant the_ioa inv4"
proof -
  have "inv4 s" if "inv11 s" for s
  proof -
    show ?thesis 
    proof (simp add:inv4_def, clarify)
      fix i b ::nat and q :: "'a set"
      assume "q \<in> quorums" and 1:"\<forall>a\<in>q. \<exists>y. onebs s a b = Some y"
      interpret dsa_properties quorums "ballot s" "vote s i" by (unfold_locales)
      show "max_by_key (\<Union>a\<in>q. the (onebs s a b) i) snd = max_by_key (dsa.q_votes (vote s i) q b) snd"
      proof -
        have 1:"the (onebs s a b) i = acc_max (vote s i) a b" if "a \<in> q" for a
          using that \<open>inv11 s\<close> 1 by (auto simp add:inv11_def)
        interpret dsa_properties quorums "ballot s" "vote s i" by (unfold_locales)
        show ?thesis using 1 max_quorum_votes[OF \<open>q\<in> quorums\<close>]
          by (simp add:dsa.q_votes_def acc_max_def distributed_safe_at.max_quorum_votes_def)
      qed
    qed
  qed
  thus ?thesis
    using IOA.invariant_def inv11 by blast 
qed

abbreviation safe where "safe s \<equiv> \<forall> i . ballot_array.safe  quorums (ballot s) (vote s i)"
declare ballot_array.safe_def[inv_proofs_defs]

lemma aqcuire_leadership_ok:
  fixes a q s t i v safe_at 
  defines "safe_at w \<equiv> ballot_array.safe_at quorums (ballot t) (vote t i) w (ballot t a)"
  assumes "acquire_leadership a q s t" and "inv3 s" and "safe s" and "conservative_array t"
  shows "case suggestion t i (ballot t a) of Some v \<Rightarrow> safe_at v | None \<Rightarrow> safe_at v"
    -- {* Note that all values are safe when the suggestion in None. *}
proof -
  let ?b = "ballot s a"
  have 2:"?b = ballot t a" using \<open>acquire_leadership a q s t\<close> by (auto simp add:inv_proofs_defs safe_at_def) 
  define proved_safe_at where "proved_safe_at = dsa.proved_safe_at (ballot t) (vote t i) q ?b"
  have 5:"case suggestion t i (ballot t a) of Some v \<Rightarrow>  proved_safe_at v | None \<Rightarrow> proved_safe_at  v"
  proof -  
    have "q \<in> quorums" by (metis acquire_leadership_def \<open>acquire_leadership a q s t\<close>) 
    moreover
    have "\<And> a2 . a2 \<in> q \<Longrightarrow> ?b \<le> ballot t a2" using \<open>acquire_leadership a q s t\<close> \<open>inv3 s\<close> 
      apply (auto simp add:inv_proofs_defs) by (metis (no_types, lifting) option.simps(5))
    moreover
    have "dsa.max_quorum_votes q (\<lambda> a2 . the (onebs t a2 ?b) i) = 
      dsa.max_quorum_votes q (\<lambda> a2 . dsa.acc_max (vote t i) a2 ?b)"
    proof -
      have "dsa.max_quorum_votes q (\<lambda> a2 . the (onebs s a2 ?b) i) = 
        dsa.max_quorum_votes q (\<lambda> a2 . dsa.acc_max (vote s i) a2 ?b)"
      proof -
        have "case onebs s a2 ?b of Some f \<Rightarrow> f i = dsa.acc_max (vote s i) a2 ?b 
              | None \<Rightarrow> False" if "a2 \<in> q" for a2 using \<open>acquire_leadership a q s t\<close> \<open>inv3 s\<close> that
          by (auto simp add:inv_proofs_defs split:option.splits)
        hence "the (onebs s a2 ?b) i = dsa.acc_max (vote s i) a2 ?b" if "a2 \<in> q" for a2 using that
          by (smt option.case_eq_if)
        thus ?thesis by (auto simp add:dsa.max_quorum_votes_def split!:option.splits)
      qed
      thus ?thesis using \<open>acquire_leadership a q s t\<close> by (auto simp add:inv_proofs_defs)
    qed                                         
    ultimately show ?thesis using \<open>acquire_leadership a q s t\<close> 
      apply (auto simp add:dsa.proved_safe_at_def proved_safe_at_def split:option.splits)
  qed
  have 6:"safe t" using \<open>acquire_leadership a q s t\<close> \<open>safe s\<close> by (auto simp add:inv_proofs_defs)
  interpret p:dsa_properties "ballot t" "vote t i" quorums by unfold_locales
  show ?thesis using 2 5 6 p.proved_safe_at_imp_safe_at assms(4) by (metis option.case_eq_if option.distinct(1) option.sel p.safe_def)
qed

definition inv8 where inv8_def[inv_proofs_defs]:
  "inv8 s \<equiv> \<forall> a i v . let b = ballot s a in
    ampr1_state.leader s a \<and> suggestion s i b = None \<longrightarrow> safe_at s i v b"

definition inv2 where
  -- {* a suggestion is safe. *}
  inv2_def[inv_proofs_defs]:
  "inv2 s \<equiv> \<forall> i b . case suggestion s i b of Some v \<Rightarrow> safe_at s i v b | None \<Rightarrow> True"

lemma inv8_inv2_safe:"invariant the_ioa (\<lambda> s . inv8 s \<and> inv2 s \<and> safe s)" oops
apply (rule invariantI)
    apply (force simp add:inv_proofs_defs ballot_array.safe_at_def)
  apply instantiate_invs_2
  subgoal premises prems for s t act
  proof - thm prems
    note safe_mono[OF prems(2)]
    thus ?thesis using prems 
    apply (unfold_to_trans_rel)
    apply ((induct_tac rule:trans_cases, simp); rm_trans_rel_assm)
                  apply (auto simp add:inv_proofs_defs split:option.splits)[3]
            defer
            apply (auto simp add:inv_proofs_defs split:option.splits)[2]
            apply (elim conjE)
        subgoal premises prems for a q
        proof (rule conjI; (rule conjI)?) thm prems
          show "safe t" using \<open>safe s\<close> \<open>acquire_leadership a q s t\<close> by (auto simp add:inv_proofs_defs)
        next
          show "inv8 t"  proof (auto simp add:inv8_def)
            fix a2 i v
            assume a1:"ampr1_state.leader t a2" and a2:"suggestion t i (ballot t a2) = None"
            show "safe_at t i v (ballot t a2)"
            proof (cases "a2 = a")
              case False thus ?thesis using \<open>acquire_leadership a q s t\<close> \<open>inv8 s\<close> \<open>inv7 s\<close> prems(1) a1 a2
                by (fastforce simp add:inv_proofs_defs)
            next
              case True thus ?thesis using aqcuire_leadership_ok \<open>inv3 s\<close> \<open>safe s\<close> \<open>\<forall>i. ballot_array.conservative_array (vote t i)\<close> 
                \<open>acquire_leadership a q s t\<close> a2 by (metis (mono_tags, lifting) option.case_eq_if)
            qed
          qed
        next
          show "inv2 t" proof (auto simp add:inv2_def split:option.splits)
            fix i b v
            assume a1:"suggestion t i b = Some v"
            show "safe_at t i v b"
            proof (cases "b = ballot s a")
              case False thus ?thesis using \<open>acquire_leadership a q s t\<close> \<open>inv2 s\<close> prems(1) a1 \<open>inv7 s\<close> 
                by (auto simp add:inv_proofs_defs split:option.splits)
            next
              case True 
              have 1:"ballot t = ballot s" using \<open>acquire_leadership a q s t\<close> by simp
              show ?thesis using 1 True aqcuire_leadership_ok[OF \<open>acquire_leadership a q s t\<close> \<open>inv3 s\<close> \<open>safe s\<close> \<open>\<forall>i. ballot_array.conservative_array (vote t i)\<close>, of i]  
                a1 \<open>inv7 s\<close> by (fastforce simp only:inv7_def Let_def split:option.splits)
            qed
          qed
        qed
        
      apply (elim conjE)
      subgoal premises prems for a i v
      proof (rule conjI; (rule conjI)?) thm prems(12,14,9)
        show "inv8 t" by (smt ampr1_ioa.do_vote_def ampr1_state.ext_inject ampr1_state.surjective ampr1_state.update_convs(3) inv8_def prems(1) \<open>inv8 s\<close> \<open>do_vote a i v s t\<close>)
      next
        show "inv2 t" by (smt prems(1) ampr1_ioa.do_vote_def ampr1_state.ext_inject ampr1_state.surjective ampr1_state.update_convs(3) inv2_def option.case_eq_if \<open>inv2 s\<close>  \<open>do_vote a i v s t\<close>) 
      next
        show "safe t" by (smt ampr1_ioa.do_vote_def ampr1_state.ext_inject ampr1_state.surjective ampr1_state.update_convs(3) ballot_array.safe_def inv1_def inv2_def option.case_eq_if prems(1) \<open>do_vote a i v s t\<close> \<open>inv2 s\<close> \<open>inv1 t\<close>) 
      qed
    done
  qed
done
declare inv8_inv2_safe[invs]

definition inv9 where
  inv9_def[inv_proofs_defs]:"inv9 s \<equiv> \<forall> i a b . ballot s a < b \<longrightarrow> vote s i a b = None"

lemma  inv9:"invariant the_ioa inv9"
apply (rule invariantI)
apply (force simp add:inv_proofs_defs)
  apply (unfold_to_trans_rel)
  apply ((induct_tac rule:trans_cases, simp); rm_reachable; rm_trans_rel_assm;
      (simp add:inv_proofs_defs; fail)?)
done
declare inv9[invs]

lemma chosen_mono: assumes "chosen s i v" and "s \<midarrow>a\<midarrow>the_ioa\<longrightarrow> t"
  shows "chosen t i v" using assms
apply (unfold_to_trans_rel)
apply ((induct_tac rule:trans_cases, simp); rm_trans_rel_assm)
apply (auto simp add:inv_proofs_defs split:option.splits)[3] defer
apply (auto simp add:inv_proofs_defs split:option.splits)[1]
apply (cases s, cases t, auto simp add:inv_proofs_defs ballot_array.chosen_def ballot_array.chosen_at_def split:option.splits)
  by (metis option.distinct(1))

definition inv10 where inv4_def[inv_proofs_defs]:
  "inv10 s \<equiv> \<forall> i l . case learned s l i of Some v \<Rightarrow> chosen s i v | None \<Rightarrow> True"

lemma  inv10:"invariant the_ioa inv4"
apply (rule invariantI)
apply (force simp add:inv_proofs_defs)
apply instantiate_invs_2
apply (unfold_to_trans_rel)
apply (induct_tac rule:trans_cases, simp)
apply (auto simp add:inv_proofs_defs split:option.splits)[3] defer
apply (auto simp add:inv_proofs_defs split:option.splits)[1]
apply (insert chosen_mono[simplified inv_proofs_defs])
apply (auto simp add:inv4_def inv5_def  split:option.splits) oops
by (metis (mono_tags) ampr1_state.select_convs(3) ampr1_state.surjective ampr1_state.update_convs(3) fun_upd_same)
declare inv4[invs]

subsection {* Finally, the proof of agreement. *}

definition agreement where agreement_def[inv_proofs_defs]:
  "agreement s \<equiv> \<forall> i l1 l2 . let v = learned s l1 i; w = learned s l2 i 
    in v \<noteq> None \<and> w \<noteq> None \<longrightarrow> v = w"

lemma agreement:"invariant the_ioa agreement"
proof -
  text {* We prove that @{term inv4} and @{term  safe} imply @{term agreement}. 
    Therefore, since they are invariant, @{term agreement} is invariant} *}
  have "agreement s" if "inv4 s" and "safe s" for s
  proof (auto simp add:inv_proofs_defs)
    fix i l1 l2 v w
    assume a1:"learned s l1 i = Some v" and a2:"learned s l2 i = Some w"
    with \<open>inv4 s\<close> have "chosen s i v" and "chosen s i w" by (auto simp add:inv_proofs_defs split:option.splits)
    with \<open>safe s\<close> show "v = w" by (metis ballot_array_props.intro ballot_array_props.safe_imp_agreement quorums_axioms)
  qed
  thus ?thesis using inv4 inv8_inv2_safe oops by (metis (mono_tags, lifting) IOA.invariant_def)
qed
    
end

end