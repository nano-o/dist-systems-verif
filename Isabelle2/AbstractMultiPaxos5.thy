theory AbstractMultiPaxos5
imports Main LinorderOption "~~/src/HOL/Library/FSet" Quorums
  "/home/nano/Documents/IO-Automata/IOA_Automation"  "~~/src/HOL/Eisbach/Eisbach_Tools"
  "/home/nano/Documents/IO-Automata/Simulations" BallotArrays
begin

datatype ('v,'a,'l) amp_action =
  Propose 'v
| Learn nat 'v 'l
| Vote 
| JoinBallot

record ('v,'a) amp_state =
  propCmd :: "'v fset"
  ballot :: "'a \<Rightarrow> nat option"
  vote :: "'a \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'v option"

text {* We give all the parameters in order to fix their type. Also fixed ballots to be nat. *}
locale abs_multi_paxos = IOA + quorums +
  fixes learners::"'l fset"
  assumes "learners \<noteq> {||}"
begin

definition amp_asig where
  "amp_asig \<equiv>
    \<lparr> inputs = { a . \<exists> c . a = Propose c  },
      outputs = { a . \<exists> v l i . l |\<in>| learners \<and> a = Learn i v l },
      internals = {Vote} \<union> {JoinBallot}\<rparr>"

definition amp_start where
  "amp_start \<equiv> {\<lparr>propCmd = {||}, ballot = (\<lambda> a . None), vote = (\<lambda> a i b . None) \<rparr>}"

definition propose where
  "propose c r r' \<equiv> (r' = r\<lparr>propCmd := (propCmd r) |\<union>| {|c|}\<rparr>)"

definition join_ballot where
  "join_ballot s s' \<equiv> 
    \<exists> a b . a |\<in>| acceptors \<and> Some b > (ballot s a) \<and> s' = s\<lparr>ballot := (ballot s)(a := Some b)\<rparr>"

definition do_vote where
  "do_vote s s' \<equiv> \<exists> a i . a |\<in>| acceptors \<and> (let bo = ballot s a; b = the bo in
        bo \<noteq> None \<and> (\<exists> v . ballot_array.proved_safe_at  (\<lambda> a . vote s a i) acceptors b v 
        \<and> ballot_array.conservative_array  (\<lambda> a . vote s' a i) acceptors
        \<and> vote s a i b = None \<and> s' = s\<lparr>vote := (vote s)(a := (vote s a)(i := 
            (vote s a i)(b := Some v)))\<rparr>))"

definition learn where
  "learn l i v s s' \<equiv> ((ballot_array.chosen (\<lambda> a . vote s a i) quorums) v) \<and> s = s'"

fun amp_trans_fun  where
  "amp_trans_fun r (Propose c) r' = propose c r r'"
| "amp_trans_fun r JoinBallot r' = join_ballot r r'"
| "amp_trans_fun r Vote r' = do_vote r r'"
| "amp_trans_fun r (Learn i v l) r' = learn l i v r r'"

definition amp_trans where
  "amp_trans \<equiv> { (r,a,r') . amp_trans_fun r a r'}"

definition amp_ioa where
  "amp_ioa \<equiv> \<lparr>ioa.asig = amp_asig, start = amp_start, trans = amp_trans\<rparr>"

end

locale amp_proof = IOA + abs_multi_paxos acceptors quorums learners for acceptors :: "'a fset" 
  and quorums and learners :: "'l fset" +
  fixes the_ioa :: "(('v,'a)amp_state, ('v,'a,'l)amp_action) ioa"
  defines "the_ioa \<equiv> amp_ioa"
begin

lemmas amp_ioa_defs =  
   is_trans_def actions_def amp_trans_def amp_start_def
   externals_def amp_ioa_def amp_asig_def

declare amp_ioa_defs[inv_proofs_defs]
declare the_ioa_def[inv_proofs_defs]

declare propose_def[simp] join_ballot_def[simp] do_vote_def[simp]
  learn_def[simp]

declare ballot_array.conservative_array_def[inv_proofs_defs]
abbreviation conservative_array where 
"conservative_array s \<equiv>  \<forall> i . ballot_array.conservative_array (\<lambda> a . vote s a i) acceptors"
lemma conservative_inductive:
  "invariant the_ioa conservative_array"
apply (try_solve_inv2 inv_proofs_defs:inv_proofs_defs invs:invs)
    apply (force simp add:ballot_array.conservative_def)
  apply (case_tac a)
        apply (force simp add:inv_proofs_defs)
      apply (force simp add:inv_proofs_defs)
    defer
    apply (force simp add:inv_proofs_defs)
  apply (match premises in R[thin]:"reachable ?ioa ?s" \<Rightarrow> \<open>-\<close>)
  subgoal premises prems for s t a using prems
  proof -
    from prems(2,3) 
    obtain a i where 1:"a |\<in>| acceptors \<and> (let bo = ballot s a; b = the bo in
        bo \<noteq> None \<and> (\<exists> v . ballot_array.proved_safe_at  (\<lambda> a . vote s a i) acceptors b v 
        \<and> ballot_array.conservative_array  (\<lambda> a . vote t a i) acceptors
        \<and> vote s a i b = None \<and> t = s\<lparr>vote := (vote s)(a := (vote s a)(i := 
            (vote s a i)(b := Some v)))\<rparr>))"
    by (auto simp add:inv_proofs_defs)
    show "conservative_array t"
    proof (auto simp add: ballot_array.conservative_array_def)
      fix j b
      have "ballot_array.conservative (\<lambda>a. vote t a j) acceptors b" if "i \<noteq> j" 
      proof -
        have "ballot_array.conservative (\<lambda>a. vote s a j) acceptors b" using prems(1)
          by (auto simp add: ballot_array.conservative_array_def ballot_array.conservative_def)
        moreover from 1 obtain v where "t = s\<lparr>vote := (vote s)(a := (vote s a)(i :=
            (vote s a i)((the (ballot s a)) := Some v)))\<rparr>" by meson
        ultimately show ?thesis using that by (auto simp add:ballot_array.conservative_def)
      qed
      moreover
      have "ballot_array.conservative (\<lambda>a. vote t a j) acceptors b" if "i = j"
        using 1 that by auto (metis ballot_array.conservative_array_def) 
      ultimately show "ballot_array.conservative (\<lambda>a. vote t a j) acceptors b" by auto
    qed
  qed 
done
declare conservative_inductive[invs]

(*
abbreviation safe_at where "safe_at \<equiv> \<lambda> s . ballot_array.safe_at (ballot s) (vote s) quorums"
lemma safe_mono:
  assumes "safe_at s v b" and "s \<midarrow>a\<midarrow>the_ioa\<longrightarrow> t"
  shows "safe_at t v b" using assms oops
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
*)

end