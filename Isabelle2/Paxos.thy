theory Paxos
imports "/home/nano/Documents/IO-Automata/IOA_Automation"  "~~/src/HOL/Eisbach/Eisbach_Tools"
  "/home/nano/Documents/IO-Automata/Simulations" "~~/src/HOL/Library/Monad_Syntax"
  "~~/src/HOL/Library/FSet"
   Quorums BallotArrays
begin

section {* paxos IOA *}

datatype ('v,'a,'l) p_action =
  Propose 'v
| Learn 'v 'l
| Vote 'a
| JoinBallot nat 'a
| StartBallot nat

record ('v, 'a) p_state =
  propCmd :: "'v fset"
  ballot :: "'a \<Rightarrow> nat option"
  vote :: "'a \<Rightarrow> nat \<Rightarrow> 'v option"
  suggestion :: "nat \<Rightarrow> 'v option"
    -- {* The suggestion of the leader of round b *}

locale paxos = IOA + quorums +
  fixes learners::"'l fset" 
  assumes "learners \<noteq> {||}"
begin

text {* If Nitpick can find a model then the assumptions are not contradictory *}
lemma False nitpick oops

definition p_asig where
  "p_asig \<equiv>
    \<lparr> inputs = { a . \<exists> c . a = Propose c  },
      outputs = { a . \<exists> v . \<exists> l . l |\<in>| learners \<and> a = Learn v l },
      internals = {a . \<exists> acc . acc |\<in>| acceptors \<and> a = Vote acc}
        \<union> {a . \<exists> b . \<exists> acc . acc |\<in>| acceptors \<and> a = JoinBallot b acc}\<rparr>"

definition p_start where
  "p_start \<equiv> {\<lparr>propCmd = {||}, ballot = (\<lambda> a . None), vote = (\<lambda> a b . None), 
    suggestion = (\<lambda> b . None) \<rparr>}"

definition propose where
  "propose c r r' \<equiv> (r' = r\<lparr>propCmd := (propCmd r) |\<union>| {|c|}\<rparr>)"

definition join_ballot where
  "join_ballot a b s s' \<equiv> Some b > (ballot s a) \<and> s' = s\<lparr>ballot := (ballot s)(a := Some b)\<rparr>"

definition start_ballot where
  "start_ballot b s s' \<equiv> suggestion s b = None \<and>
    (\<exists> q v . q |\<in>| quorums \<and> ballot_array.proved_safe_at (vote s) q b v \<and> (\<forall> a . a |\<in>| q \<longrightarrow> ballot s a \<ge> Some b)
      \<and> v |\<in>| propCmd s \<and> s' = s\<lparr>suggestion := (suggestion s)(b := Some v)\<rparr>)"

definition do_vote where
  "do_vote a s s' \<equiv> case ballot s a of None \<Rightarrow> False | Some b \<Rightarrow>
    vote s a b = None \<and> s' = s\<lparr>vote := (vote s)(a := (vote s a)(b := suggestion s b))\<rparr>"

definition learn where
  "learn l v s s' \<equiv> ((ballot_array.chosen (vote s) quorums) v) \<and> s = s'"

fun p_trans_fun  where
  "p_trans_fun r (Propose c) r' = propose c r r'"
| "p_trans_fun r (JoinBallot b a) r' = join_ballot a b r r'"
| "p_trans_fun r (Vote a) r' = do_vote a r r'"
| "p_trans_fun r (Learn v l) r' = learn l v r r'"
| "p_trans_fun r (StartBallot b) r' = start_ballot b r r'"

definition p_trans where
  "p_trans \<equiv> { (r,a,r') . p_trans_fun r a r'}"

definition p_ioa where
  "p_ioa \<equiv> \<lparr>ioa.asig = p_asig, start = p_start, trans = p_trans\<rparr>"

end

section {* Correctness proof *}

text {* We create a locale for the proof in order to fix the type variables appearing in p_ioa_def
  Otherwise we run into problem with polymorphism and Eisbach *}

print_locale paxos

locale paxos_proof = IOA + paxos acceptors quorums learners for acceptors :: "'a fset" 
  and quorums and learners :: "'l fset" +
  fixes the_ioa :: "(('v,'a)p_state, ('v,'a,'l)p_action) ioa"
  defines "the_ioa \<equiv> p_ioa"
begin

(* TODO: is this necessary?
interpretation ba?:ballot_array quorums acceptors "p_state.ballot r" "p_state.vote r" for r::"('v,'a)p_state"
by (unfold_locales) *)

lemmas p_ioa_defs =  
   is_trans_def actions_def p_trans_def p_start_def
   externals_def p_ioa_def p_asig_def

declare p_ioa_defs[inv_proofs_defs]

declare propose_def[simp] join_ballot_def[simp] do_vote_def[simp]
  learn_def[simp] start_ballot_def[simp]

definition inv1 where
  "inv1 s \<equiv> \<forall> a b . a |\<in>| acceptors \<and> vote s a b \<noteq> None 
    \<longrightarrow> vote s a b = suggestion s b"
declare inv1_def[inv_proofs_defs]

declare the_ioa_def[inv_proofs_defs]

lemma inv1:"invariant the_ioa inv1"
apply try_solve_inv2
    apply (smt fun_upd_apply option.case_eq_if p_state.ext_inject p_state.surjective p_state.update_convs(3))
  apply (metis fun_upd_other option.discI p_state.ext_inject p_state.surjective p_state.update_convs(4))
done

(* Does not seem needed. Is it? *)
declare ballot_array.well_formed_def[inv_proofs_defs]
lemma well_formed_inductive:
  "invariant the_ioa (\<lambda> s . ballot_array.well_formed (ballot s) (vote s) acceptors)"
apply try_solve_inv2
apply auto
apply (smt fun_upd_apply gt_not_none neq_iff option.case_eq_if option.expand p_state.ext_inject p_state.surjective p_state.update_convs(3))
done 
declare well_formed_inductive[invs]

declare ballot_array.conservative_array_def[inv_proofs_defs]
abbreviation conservative_array where 
"conservative_array \<equiv> (\<lambda> s . ballot_array.conservative_array (vote s) acceptors)"
lemma conservative_inductive:
  "invariant the_ioa conservative_array"
apply (try_solve_inv2 inv_proofs_defs:inv_proofs_defs ballot_array.conservative_def invs:invs inv1)
    apply metis
  apply force
done
declare conservative_inductive[invs]

abbreviation safe_at where "safe_at \<equiv> \<lambda> s . ballot_array.safe_at (ballot s) (vote s) quorums"
lemma safe_mono:
  assumes "safe_at s v b" and "s \<midarrow>a\<midarrow>the_ioa\<longrightarrow> t"
  shows "safe_at t v b" using assms
apply (cases a)
        apply (auto simp add:inv_proofs_defs ballot_array.safe_at_def ballot_array.choosable_def)[2] (* propose, learn *)
    defer (* join_ballot *)
    apply (simp add:inv_proofs_defs ballot_array.safe_at_def ballot_array.choosable_def)[1]
    apply (metis less_def order.strict_trans) 
  defer (* vote *)
  apply (simp add:inv_proofs_defs ballot_array.safe_at_def ballot_array.choosable_def, case_tac "ballot s x3", simp_all)
  apply (metis neq_iff)
apply (simp add:inv_proofs_defs ballot_array.safe_at_def ballot_array.choosable_def) (* start_ballot *)
apply (metis p_state.ext_inject p_state.surjective p_state.update_convs(4))
done

abbreviation safe where "safe \<equiv> \<lambda> s . ballot_array.safe (ballot s) (vote s) quorums acceptors"
definition inv2 where
  "inv2 s \<equiv> safe s \<and> (\<forall> b . case suggestion s b of None \<Rightarrow> True | Some v \<Rightarrow> safe_at s v b)"
declare inv2_def[inv_proofs_defs]

lemma inv2:
  "invariant the_ioa inv2"
apply(rule invariantI)
    apply (force simp add:inv_proofs_defs ballot_array.safe_def)
  apply instantiate_invs_2
  apply (case_tac a)
          subgoal premises prems for s t a v
          proof -
            from prems(2,7) have 1:"propose v s t"
              by (auto simp add:inv_proofs_defs) 
            hence 2:"\<And> b . suggestion s b = suggestion t b" 
              by(auto simp add:inv_proofs_defs)
            have 3:"safe t" using 1 prems(1) 
              by (auto simp add:inv_proofs_defs ballot_array.safe_def ballot_array.safe_at_def ballot_array.choosable_def) 
            from 1 2 3 safe_mono show ?thesis 
              by (auto simp add:inv2_def)
                (metis inv2_def option.case_eq_if prems(1) prems(2))
          qed
        subgoal by (auto simp add:inv_proofs_defs) (* learn *)
      subgoal premises prems for s t act a (* vote *)
      proof - 
        from prems(2,7) have 1:"do_vote a s t"
          by(auto simp add:inv_proofs_defs)
        hence 2:"\<And> b . suggestion s b = suggestion t b" 
          by (auto simp add:inv_proofs_defs)
            (smt option.case_eq_if p_state.select_convs(4) p_state.surjective p_state.update_convs(3)) 
        have 3:"safe t" using prems(1) 1 apply(auto simp add:inv2_def ballot_array.safe_def, case_tac "vote t aa b", simp_all)
          by (smt case_optionE fun_upd_def option.simps(5) p_state.ext_inject p_state.surjective p_state.update_convs(3) prems(2) safe_mono)
        from 1 2 3 safe_mono prems(1,2) show ?thesis
          by (metis inv2_def option.case_eq_if)
      qed
    subgoal premises prems for s t act b a
    proof -
      from prems(2,7) have 1:"join_ballot a b s t"
        by (auto simp add:inv_proofs_defs)
      hence 2:"\<And> b . suggestion s b = suggestion t b" 
        by (auto simp add:inv_proofs_defs)
      have 3:"safe t" using 1 safe_mono prems(1,2)
        by (smt ballot_array.safe_def inv2_def option.case_eq_if p_state.ext_inject p_state.surjective p_state.update_convs(2) paxos.join_ballot_def paxos_axioms)
      from 1 2 3 safe_mono prems(1,2) show ?thesis
        by (metis inv2_def option.case_eq_if) 
    qed
  subgoal premises prems for s t act b
  proof -
    from prems(2,7) have 1:"start_ballot b s t"
      by(auto simp add:inv_proofs_defs)
    have 3:"safe t" using prems(1) 1 by (auto simp add:inv2_def ballot_array.safe_def, case_tac "vote s a ba", auto, metis option.simps(5))
    from 1 obtain q v where 2:"q |\<in>| quorums" and 4:"(ballot_array.proved_safe_at (vote s)) q b v" 
      and 5:"t = s\<lparr>suggestion := suggestion s(b \<mapsto> v)\<rparr>" and 6:"\<And> a . a |\<in>| q \<Longrightarrow> ballot s a \<ge> Some b"
      by auto
    interpret ba_props:ballot_array_props "ballot s" "vote s" by unfold_locales
    have 2:"\<And> b . case suggestion t b of None \<Rightarrow> True | Some v \<Rightarrow> safe_at t v b"
      using 1 2 4 5 6 prems(1,2,3)
        by (simp add:inv2_def)
          (simp add: ba_props.proved_safe_is_safe option.case_eq_if prems(4))
    from 2 3 show ?thesis by (auto simp add:inv2_def)
  qed
done
declare inv2[invs]

lemma safe_inv:
  "invariant the_ioa safe"
apply(rule invariantI)
    apply (force simp add:ballot_array.safe_def inv_proofs_defs)
  apply instantiate_invs_2
  apply (case_tac a)
          apply (force simp add:ballot_array.safe_def inv_proofs_defs ballot_array.safe_at_def ballot_array.choosable_def)
        apply (force simp add:ballot_array.safe_def inv_proofs_defs ballot_array.safe_at_def ballot_array.choosable_def)
      apply (auto simp add:is_trans_def the_ioa_def p_ioa_def p_trans_def inv2_def)
done
declare safe_inv[invs]

definition agreement where 
  "agreement s \<equiv> \<forall> v w . (ballot_array.chosen (vote s) quorums v) 
    \<and> ballot_array.chosen (vote s) quorums w \<longrightarrow> v = w"
lemma agreement:"invariant the_ioa agreement"
apply(rule invariantI)
    apply(auto simp add: inv_proofs_defs agreement_def ballot_array.chosen_def ballot_array.chosen_at_def)[1]
    apply (metis fempty_iff quorum_inter_witness)
  apply instantiate_invs_2
  apply (insert ballot_array_props.safe_is_safe)
  apply (auto simp add:agreement_def)
  using ballot_array_props.intro quorums_axioms by fastforce

end

end