section {* Proof of the agreement property of AbstractMultiPaxos. *}

theory AbstractMultiPaxosR1Correctness
imports AbstractMultiPaxosR1 IOA_Automation
  BallotArrayProperties
begin

locale ampr1_proof = IOA + quorums quorums + ampr1_ioa quorums for
     quorums :: "'a set set" +
  fixes the_ioa :: "(('v, 'a, 'l) ampr1_state, 'v paxos_action) ioa"
  defines "the_ioa \<equiv> ioa"
begin

interpretation dsa_p:dsa_properties quorums ballot vote for ballot :: "'a \<Rightarrow> bal" 
  and vote :: "'a \<Rightarrow> nat \<Rightarrow> 'v option"
  by (unfold_locales)

subsection {* Automation setup *}

lemmas ioa_defs =
   is_trans_def actions_def trans_def start_def start_s_def
   externals_def ioa_def asig_def the_ioa_def

declare propose_def[simp] join_ballot_def[simp] do_vote_def[simp] suggest_def[simp]
  learn_def[simp] Let_def[simp] if_splits[split] acquire_leadership_def[simp]
  join_started_ballot_def[simp]

named_theorems inv_defs

(*  Nitpick config:
nitpick[no_assms, show_consts, verbose, card 'a = 3, card 'v = 2, card nat = 2, card "'v option" = 3, card "nat option" = 3,
    card "('v \<times> nat) option" = 5, card "'v \<times> nat" = 4, card unit = 1, card "('v, 'a) ampr1_state" = 32]
*)

method rm_trans_rel_assm = 
  (match premises in P[thin]:"trans_rel ?x ?y ?z" \<Rightarrow> \<open>-\<close>)

lemma is_trans_simp[simp]:
  "s \<midarrow>a\<midarrow>the_ioa\<longrightarrow> t = trans_rel s a t"
  by (simp add:is_trans_def the_ioa_def ioa_def trans_def)
  
method my_fail for msg::"char list" = (print_term msg; fail)

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

subsection {* Invariants *}

definition inv3 where inv3_def[inv_defs]:
  -- {* acceptors only vote for the suggestion. *}
  "inv3 s \<equiv> \<forall> i a b . let v = vote s a i b in v \<noteq> None \<longrightarrow> v = suggestion s i b"
  
context begin
  -- {* Proof of @{term inv3} *}

private definition inv1 where inv1_def[inv_defs]:
  "inv1 s \<equiv> \<forall> b . inst_status s b \<noteq> None \<longrightarrow> ballot s (leader b) \<ge> b"
  
private lemma inv1: "invariant the_ioa inv1" by (force_inv)

private definition inv2 where inv2_def[inv_defs]:
  "inv2 s \<equiv> \<forall> a b i . leader b = a \<and> (ballot s a < b \<or> (ballot s a = b \<and> inst_status s b = None))
    \<longrightarrow> suggestion s i b = None"

private lemma inv2: "invariant the_ioa inv2"
  apply (simp_inv invs:inv1)
   apply (simp add:ioa_defs inv_defs; case_tac s; case_tac t; force split:option.splits)
  apply (simp add:ioa_defs inv_defs; case_tac s; case_tac t; simp) by (metis fun_upd_apply)

lemma inv3: "invariant the_ioa inv3" 
  apply (simp_inv invs:inv2)
   apply (simp add:ioa_defs inv_defs; case_tac s; case_tac t; force)
  apply (simp add:ioa_defs inv_defs; case_tac s; case_tac t; auto split:option.splits)
  by (metis fun_upd_apply option.distinct(1))

end

definition conservative where
  "conservative s \<equiv>  \<forall> i . ballot_array.conservative_array (flip (vote s) i)"

lemma conservative: "invariant the_ioa conservative"
proof -
  have "\<And> s . inv3 s \<Longrightarrow> conservative s"
    apply (simp add:inv_defs ballot_array.conservative_def ballot_array.conservative_array_def
       conservative_def split:option.splits) by (metis option.inject)
  with inv3 show ?thesis  using IOA.invariant_def by blast
qed

definition safe_at where "safe_at s i \<equiv> dsa.safe_at (ballot s) (flip (vote s) i)"

lemma safe_mono:
  -- {* @{term safe_at} is monotonic. A key lemma to simplify invariant proofs. *}
  assumes "s \<midarrow>a\<midarrow>the_ioa\<longrightarrow> t" and "safe_at s i v b"
  shows "safe_at t i v b"
proof -
  have "is_prefix (ballot s) (ballot t) (flip (vote s) i) (flip (vote t) i)" using \<open>s \<midarrow>a\<midarrow>the_ioa\<longrightarrow> t\<close>
    by (simp add:inv_defs ioa_defs; induct_tac rule:trans_cases, auto simp add:is_prefix_def inv_defs split:option.split_asm)
  thus ?thesis
  using assms ballot_array_prefix.safe_at_mono unfolding safe_at_def
  by (metis ballot_array_prefix_axioms_def ballot_array_prefix_def quorums_axioms) 
qed

method insert_safe_mono =
  match premises in P:"?s \<midarrow>?a\<midarrow>the_ioa\<longrightarrow> ?t" \<Rightarrow> \<open>insert safe_mono[OF P]\<close>
method inv_cases_3 uses invs declares inv_defs =
  inv_cases \<open>-\<close> \<open>insert_safe_mono\<close> \<open>-\<close> invs:invs inv_defs:inv_defs

definition safe where "safe s \<equiv> \<forall> a i b . case vote s a i b of Some v \<Rightarrow> safe_at s i v b | _ \<Rightarrow> True"

definition inv4 where inv4_def[inv_defs]:"inv4 s \<equiv> \<forall> i b . 
  case suggestion s i b of Some v \<Rightarrow> 
    (case inst_status s b of Some f \<Rightarrow>
      (case f i of None \<Rightarrow> True | Some w \<Rightarrow> v = w)
    | None \<Rightarrow> False)
  | None \<Rightarrow> True"
  
lemma inv4:"invariant the_ioa inv4"
  apply (simp_inv; (simp add:ioa_defs inv_defs; case_tac s; case_tac t; clarify; simp split:option.splits))
      apply (metis option.collapse option.distinct(1))
     apply (metis option.collapse option.distinct(1)) 
    apply (metis option.collapse option.distinct(1)) 
   apply auto
      apply fastforce
     apply (metis option.collapse option.distinct(1))
    apply (metis fun_upd_apply option.distinct(1) option.inject)
    apply (metis fun_upd_apply option.distinct(1))
   apply (metis fun_upd_apply)
  by (metis option.collapse option.distinct(1))

definition inst_status_inv where inst_status_inv_def[inv_defs]:
  "inst_status_inv s \<equiv> (\<forall> b . case inst_status s b of Some f \<Rightarrow> 
    (\<forall> i . case f i of Some v \<Rightarrow> safe_at s i v b | None \<Rightarrow> (\<forall> v . safe_at s i v b))
    | None \<Rightarrow> True)"

definition the_inv where the_inv_def[inv_defs]: "the_inv s \<equiv> 
  safe s  \<and> inst_status_inv s"
  
context begin
  --{* Proof of @{term the_inv} *}

private
definition inv5 where inv5_def[inv_defs]:"inv5 s \<equiv> \<forall> a b f i . onebs s a b = Some f 
      \<longrightarrow> f i = dsa.acc_max (flip (vote s) i) a b \<and> ballot s a \<ge> b"

private
lemma inv5:"invariant the_ioa inv5"
  -- {* The @{term do_vote} case necessitates to show that the value of @{term dsa.acc_max} dose not change as a result of the vote.  *}
  apply (force_inv inv_defs:inv5_def)
  subgoal premises prems for s t _ a2 i2 v unfolding inv5_def
      -- {* the @{term do_vote} case *}
  proof (clarify, rule conjI)
    fix a b f i
    assume "onebs t a b = Some f"
    hence "onebs s a b = Some f" using \<open>do_vote a2 i2 v s t\<close> unfolding do_vote_def by auto
    hence "f i = dsa.acc_max (flip (vote s) i) a b" and "b \<le> ballot s a" using \<open>inv5 s\<close> unfolding inv5_def by auto
    have "dsa.acc_max (flip (vote t) i) a b = dsa.acc_max (flip (vote s) i) a b"
    proof -
      from \<open>b \<le> ballot s a\<close> have "\<And> b' . b' < b \<Longrightarrow> flip (vote s) i a b' = flip (vote t) i a b'" using  \<open>do_vote a2 i2 v s t\<close>
        unfolding do_vote_def by auto
      hence "{(v, ba). ba < b \<and> flip (vote s) i a ba = Some v} = {(v, ba). ba < b \<and> flip (vote t) i a ba = Some v}" by metis
      thus ?thesis unfolding dsa.acc_max_def dsa.a_votes_def by auto
    qed
    with \<open>f i = dsa.acc_max (flip (vote s) i) a b\<close> show "f i = dsa.acc_max (flip (vote t) i) a b" by auto
    from \<open>b \<le> ballot s a\<close> and \<open>do_vote a2 i2 v s t\<close> show "b \<le> ballot t a" unfolding do_vote_def by auto
  qed
  done

  
lemma the_inv:"invariant the_ioa the_inv"
  apply (inv_cases_3 invs:inv4 conservative inv5)
        apply (simp add:ioa_defs inv_defs safe_def ballot_array.safe_def safe_at_def dsa_p.safe_at_0)
       apply (simp add:ioa_defs inv_defs safe_def split:option.splits)
       apply (metis option.distinct(1))
      apply (simp add:inv_defs split:option.splits)
  subgoal premises prems for s t _ a b (* join_ballot *)
  proof (auto simp add:the_inv_def)
    from \<open>join_ballot a b s t\<close> have 1:"inst_status t = inst_status s" and 2:"vote t = vote s" by auto
    note mono = \<open>(\<And>i v b. safe_at s i v b \<Longrightarrow> safe_at t i v b)\<close>
    show "safe t" using \<open>the_inv s\<close>  2 mono
      by (auto simp add:safe_def ballot_array.safe_def safe_at_def inv_defs split:option.splits)
    show "inst_status_inv t" using 1 2 mono \<open>the_inv s\<close>
      by (force simp add:inv_defs split:option.splits)
  qed
  subgoal premises prems for s t _ a i v (* do_vote *)
  proof (auto simp add:the_inv_def)
    note mono = \<open>(\<And>i v b. safe_at s i v b \<Longrightarrow> safe_at t i v b)\<close>
    have 1:"\<And> i b v . suggestion s i b = Some v \<Longrightarrow> safe_at s i v b" using \<open>the_inv s\<close> \<open>inv4 s\<close>
      by (fastforce simp add:safe_def inv_defs split:option.splits)
    show "safe t" using \<open>the_inv s\<close> mono \<open>do_vote a i v s t \<close> 1
      by (auto simp add:safe_def inv_defs split:option.splits)
    show "inst_status_inv t" using \<open>the_inv s\<close> mono \<open>do_vote a i v s t \<close>
      apply (cases s, cases t, auto simp add: inv_defs safe_def split!:option.splits)
      by (metis option.distinct(1))
  qed
  subgoal for s t _ _ _ _ _ (* suggest *)
    apply (cases s, cases t, auto simp add: inv_defs safe_def split:option.splits)[1]
    apply (metis option.distinct(1))
    done
  subgoal premises prems for s t _ a q (* acquire_leadership *)
  proof (auto simp add:the_inv_def)
    note mono = \<open>(\<And>i v b. safe_at s i v b \<Longrightarrow> safe_at t i v b)\<close>
    show "safe t" using \<open>acquire_leadership a q s t\<close> \<open>the_inv s\<close> mono
      by (auto simp add:safe_def inv_defs split:option.splits)
    show "inst_status_inv t"
    proof -
      let ?b = "ballot s a"
      from \<open>acquire_leadership a q s t\<close> have "joined s q ?b" and \<open>q\<in> quorums\<close> by (auto simp add:safe_def inv_defs split:option.splits)
      from \<open>the_inv s\<close> have "safe s" by (simp add: the_inv_def) 
      
      text {* First we show that @{term max_vote} is the max over @{term dsa.acc_max} 
        (i.e. @{term dsa.max_quorum_votes} *}
      have 1:"max_vote s i ?b q = dsa.max_quorum_votes (flip (vote s) i) q ?b" for i 
      proof -
        have "(the (onebs s a ?b)) i = dsa.acc_max (flip (vote s) i) a ?b" if "a \<in> q" for a i
          using \<open>inv5 s\<close> \<open>joined s q ?b\<close> that by (simp add: ampr1_ioa.joined_def inv5_def)
        thus ?thesis by (auto simp add:max_vote_def dsa.max_quorum_votes_def)
      qed
      have 2:"ballot s a \<ge> ?b" if "a \<in> q" for a using \<open>joined s q ?b\<close> \<open>inv5 s\<close> that by (auto simp add:inv5_def joined_def)
      
      text {* Then we show that a suggestion is @{term dsa.proved_safe_at}, and that everything is 
        safe if there is no suggestion *}
      let ?proved="\<lambda> i . dsa.proved_safe_at (ballot s) (flip (vote s) i) q ?b"
      have 3:"case sugg s i ?b q of Some v \<Rightarrow> ?proved i v | None \<Rightarrow> (\<forall> v . ?proved i v)" for i
      proof (cases "sugg s i ?b q")
        case None
        hence "dsa.max_quorum_votes (flip (vote s) i) q ?b = {}" unfolding sugg_def
            \<open>max_vote s i ?b q = dsa.max_quorum_votes (flip (vote s) i) q ?b\<close> by auto
        thus ?thesis using 2 \<open>q \<in> quorums\<close> None unfolding dsa.proved_safe_at_def joined_def by auto 
      next
        case (Some v)
          -- {* Here the difficulty lies in the use of @{term the_elem} in @{thm sugg_def} *}
        obtain x where "dsa.max_quorum_votes (flip (vote s) i) q ?b = {x}"
        proof -
          from Some have "max_vote s i ?b q \<noteq> {}" unfolding sugg_def by auto
          moreover
          note \<open>max_vote s i ?b q = dsa.max_quorum_votes (flip (vote s) i) q ?b\<close>  and \<open>conservative s\<close> 
          moreover note dsa_p.max_vote_e_or_singleton
          ultimately show ?thesis using that unfolding conservative_def by (metis \<open>q \<in> quorums\<close>) 
        qed
        moreover 
        have "v = (the_elem (fst ` (dsa.max_quorum_votes (flip (vote s) i) q ?b)))" using Some \<open>joined s q ?b\<close> 1
          by (auto simp add: sugg_def)
        ultimately show ?thesis using \<open>q\<in>quorums\<close> \<open>joined s q ?b\<close> 1 2 Some
          unfolding dsa.proved_safe_at_def by auto
      qed
      
      text {* Finally we conclude using lemma @{thm dsa_p.proved_safe_at_imp_safe_at} *}
      
      obtain f where 6:"f = (\<lambda> i . sugg s i ?b q)" and 7:"inst_status t (ballot s a) = Some f" using \<open>acquire_leadership a q s t\<close> 
        using \<open>acquire_leadership a q s t\<close> by simp
      have 8:"case f i of Some v \<Rightarrow> safe_at s i v ?b | None \<Rightarrow> safe_at s i v ?b" for i v
      proof (cases "f i")
        case None
        with \<open>acquire_leadership a q s t\<close> 6 have "sugg s i ?b q = None" by auto
        with 3 have "dsa.proved_safe_at (ballot s) (flip (vote s) i) q ?b v" by (metis (mono_tags) option.simps(4)) 
        thus ?thesis using \<open>conservative s\<close> \<open>q\<in>quorums\<close> dsa_p.proved_safe_at_imp_safe_at None
          apply (auto simp add:safe_def safe_at_def conservative_def split:option.splits)
          apply (metis (full_types) ampr1_proof.safe_at_def ampr1_proof.safe_def ampr1_proof_axioms dsa.safe_def \<open>safe s\<close>)
          done
      next
        case (Some w)
        from Some 6 have 7:"sugg s i ?b q = Some w" by auto
        hence "dsa.proved_safe_at (ballot s) (flip (vote s) i) q ?b w" using "3" by (metis option.simps(5)) 
        with \<open>safe s\<close> and \<open>conservative s\<close> show ?thesis using Some \<open>q\<in>quorums\<close> dsa_p.proved_safe_at_imp_safe_at
          by (auto simp add:safe_def safe_at_def conservative_def ballot_array.safe_def inv_defs split!:option.splits)
      qed
      from 7 8 show ?thesis using \<open>the_inv s\<close> \<open>acquire_leadership a q s t\<close> mono
        apply (simp add: inv_defs split:option.splits)
        by (smt option.case_eq_if option.distinct(1) option.sel)
    qed
  qed
  apply (simp add:ioa_defs inv_defs safe_def split:option.splits; metis option.distinct(1))
  done
  
end

definition inv7 where inv7_def[inv_defs]:
  "inv7 s \<equiv> \<forall> i . ballot_array.safe quorums (ballot s) (flip (vote s) i)"
  
lemma inv7:"invariant the_ioa inv7"
proof -
  { fix s
    assume "the_inv s" and "inv3 s" and "inv4 s"
    hence "flip (vote s) i a b = Some v \<longrightarrow> safe_at s i v b" for a i b v  apply (simp add:inv_defs) by (metis (no_types) option.simps(5) safe_def)
    hence "inv7 s"   by (simp add:ballot_array.safe_def safe_at_def inv7_def split:option.splits) }
  thus ?thesis by (smt IOA.invariant_def inv4 inv3 the_inv) 
qed

context begin
-- {* Is this stuff needed? *}

private
definition inv6 where
  inv6_def[inv_defs]:"inv6 s \<equiv> \<forall> i a b . ballot s a < b \<longrightarrow> flip (vote s) i a b = None"
  
private
lemma  inv6:"invariant the_ioa inv6"
by (force_inv)

end

end

end