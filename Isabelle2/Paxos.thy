theory Paxos
imports "/home/nano/Documents/IO-Automata/IOA_Automation"  "~~/src/HOL/Eisbach/Eisbach_Tools"
  "/home/nano/Documents/IO-Automata/Simulations" "~~/src/HOL/Library/Monad_Syntax"
  "~~/src/HOL/Library/FSet"
   Quorums BallotArrays
begin

section {* paxos IOA *}

subsection {* State and actions of the paxos algorithm *}

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

print_locale ballot_array

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
  "do_vote a s s' \<equiv> let bo = ballot s a; b = the bo in
    bo \<noteq> None \<and> vote s a b = None \<and> s' = s\<lparr>vote := (vote s)(a := (vote s a)(b := suggestion s b))\<rparr>"

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

lemma gt_not_none:
  "b\<^sub>1 < (b\<^sub>2::'e::linorder option) \<Longrightarrow> b\<^sub>2 \<noteq> None"
by (metis less_def less_o.elims(2) option.discI)

declare propose_def[simp] join_ballot_def[simp] do_vote_def[simp]
  learn_def[simp] start_ballot_def[simp]

definition inv1 where
  "inv1 s \<equiv> \<forall> a b . a |\<in>| acceptors \<and> vote s a b \<noteq> None 
    \<longrightarrow> vote s a b = suggestion s b"
declare inv1_def[inv_proofs_defs]

declare the_ioa_def[inv_proofs_defs]

lemma inv1:"invariant the_ioa inv1"
apply try_solve_inv2
apply (smt fun_upd_apply p_state.ext_inject p_state.surjective p_state.update_convs(3))
apply (metis (no_types, lifting) map_upd_Some_unfold option.discI p_state.ext_inject p_state.surjective p_state.update_convs(4))
done

(* Does not seem needed. Is it? *)
declare ballot_array.well_formed_def[inv_proofs_defs]
lemma well_formed_inductive:
  "invariant the_ioa (\<lambda> s . ballot_array.well_formed (ballot s) (vote s) acceptors)"
apply try_solve_inv2
apply auto
apply (smt fun_upd_apply gt_not_none neq_iff option.collapse option.sel p_state.ext_inject p_state.surjective p_state.update_convs(3))
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
  apply (simp add:inv_proofs_defs ballot_array.safe_at_def ballot_array.choosable_def)
  apply (smt fun_upd_apply neq_iff option.sel p_state.select_convs(2) p_state.select_convs(3) p_state.surjective p_state.update_convs(3))
  (* That was amazing, Sledgehammer found it before I had time to think about why it would be true... *)
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
      subgoal premises prems for s t act a
      proof - 
        from prems(2,7) have 1:"do_vote a s t"
          by(auto simp add:inv_proofs_defs)
        hence 2:"\<And> b . suggestion s b = suggestion t b" 
          by (auto simp add:inv_proofs_defs)
            (metis p_state.ext_inject p_state.surjective p_state.update_convs(3))
        have 3:"safe t" using prems(1) 1 apply(auto simp add:inv2_def ballot_array.safe_def)
          proof - (* Auto-generated by Sledgehammer *)
            fix b :: nat and aa :: 'a
            assume a1: "aa |\<in>| acceptors"
            assume a2: "let bo = ballot s a; b = the bo in (\<exists>y. bo = Some y) \<and> vote s a b = None \<and> t = s \<lparr>vote := (vote s)(a := (vote s a)(b := suggestion s b))\<rparr>"
            assume a3: "\<forall>b. case suggestion s b of None \<Rightarrow> True | Some v \<Rightarrow> safe_at s v b"
            assume a4: "\<forall>b a. a |\<in>| acceptors \<longrightarrow> (let vote = vote s a b in (\<exists>y. vote = Some y) \<longrightarrow> safe_at s (the vote) b)"
            { fix vv :: 'v
              have ff1: "\<And>n. suggestion s n = None \<or> safe_at s (the (suggestion s n)) n"
                using a3 by (metis option.case_eq_if)
              obtain nn :: nat where
                ff2: "s\<lparr>vote := (vote s) (a := (vote s a) (the (ballot s a) := suggestion s (the (ballot s a))))\<rparr> = t \<and> ballot s a = Some nn \<and> vote s a (the (ballot s a)) = None"
                using a2 by metis
              have "\<forall>p. \<exists>f fa fb fc u. \<lparr>propCmd = f::'v fset, ballot = fa::'a \<Rightarrow> nat option, vote = fb, suggestion = fc, \<dots> = u::unit\<rparr> = p"
                by (metis p_state.cases_scheme)
              then obtain ff :: "('v, 'a) p_state \<Rightarrow> 'v fset" and zz :: "('v, 'a) p_state \<Rightarrow> 'a \<Rightarrow> nat option" and zza :: "('v, 'a) p_state \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> 'v option" and zzb :: "('v, 'a) p_state \<Rightarrow> nat \<Rightarrow> 'v option" and uu :: "('v, 'a) p_state \<Rightarrow> unit" where
                ff3: "\<And>p. \<lparr>propCmd = ff p, ballot = zz p, vote = zza p, suggestion = zzb p, \<dots> = uu p\<rparr> = p"
                by moura
              then have ff4: "\<And>p. vote p = zza p"
                by (metis p_state.select_convs(3))
              have "(zza s)(a := (zza s a)(the (Some nn) := suggestion s (the (Some nn)))) = zza t"
                using ff3 ff2 by (metis p_state.select_convs(3) p_state.update_convs(3))
              then have "zza t aa b = Some vv \<longrightarrow> ballot_array.safe_at (ballot s) (zza s) quorums (the (Some vv)) b"
                using ff4 ff2 ff1 a4 a1 by (metis fun_upd_apply)
              then have "vote t aa b \<noteq> Some vv \<or> safe_at t (the (vote t aa b)) b"
                using ff4 by (metis prems(2) safe_mono) }
            then show "let z = vote t aa b in (\<exists>v. z = Some v) \<longrightarrow> safe_at t (the z) b"
              by metis
          qed
        from 1 2 3 safe_mono show ?thesis 
          by (auto simp add:inv2_def)
            (metis inv2_def option.case_eq_if prems(1) prems(2))
      qed
    subgoal premises prems for s t act b a
    proof -
      from prems(2,7) have 1:"join_ballot a b s t"
        by (auto simp add:inv_proofs_defs)
      hence 2:"\<And> b . suggestion s b = suggestion t b" 
        by (auto simp add:inv_proofs_defs)
      have 3:"safe t" using prems(1) 1 apply (auto simp add:inv2_def ballot_array.safe_def)
        by (metis p_state.ext_inject p_state.surjective p_state.update_convs(2) prems(2) safe_mono) 
      from 1 2 3 safe_mono show ?thesis 
        by (auto simp add:inv2_def)
          (metis inv2_def option.case_eq_if prems(1) prems(2))
    qed
  subgoal premises prems for s t act b
  proof -
    from prems(2,7) have 1:"start_ballot b s t"
      by(auto simp add:inv_proofs_defs)
    have 3:"safe t" using prems(1) 1 by (auto simp add:inv2_def ballot_array.safe_def)
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