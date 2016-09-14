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

sublocale dsa_p:dsa_properties quorums ballot vote for ballot vote 
  by (unfold_locales)

subsection {* Automation setup *}

lemmas ioa_defs =
   is_trans_def actions_def trans_def start_def start_s_def
   externals_def ioa_def asig_def the_ioa_def

declare propose_def[simp] join_ballot_def[simp] do_vote_def[simp] suggest_def[simp]
  learn_def[simp] Let_def[simp] if_splits[split] acquire_leadership_def[simp]

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
  
method try_ind_step =
  -- {* performs case analysis and tries to solve each case with force, leaving unsolved cases untouched. *}
  (simp only:is_trans_simp, ((induct_tac rule:trans_cases | print_term "''case analysis failed''"), simp?);
    (rm_trans_rel_assm; (force simp add:inv_defs split:option.splits)?))

method try_inv uses invs declares inv_defs =
  (rule invariantI;
    (match premises in
      P:"?s \<in> ioa.start ?ioa" \<Rightarrow> \<open>(insert P; force simp add:inv_defs ioa_defs) | print_term "''base case failed''"\<close> 
      \<bar> R:"reachable ?ioa ?x" and P:"_"(multi) \<Rightarrow> 
        \<open>(insert P, instantiate_invs_2 invs:invs, try_ind_step) | print_term "''ind case failed''"\<close> )
    )
  
subsection {* Invariants *}

definition inv7 where inv7_def[inv_defs]:
  "inv7 s \<equiv> \<forall> a . ampr1_state.leader s a \<longrightarrow> leader (ballot s a) = a"

lemma inv7: "invariant the_ioa inv7" by (try_inv)

definition inv6 where inv6_def[inv_defs]:
  "inv6 s \<equiv> \<forall> a b i . leader b = a \<and> (ballot s a < b \<or> (ballot s a = b \<and> \<not> ampr1_state.leader s a))
    \<longrightarrow> suggestion s i b = None"

lemma inv6: "invariant the_ioa inv6"  by (try_inv invs:inv7)

definition inv1 where inv1_def[inv_defs]:
  -- {* acceptors only vote for the suggestion. *}
  "inv1 s \<equiv> \<forall> i a b . let v = vote s i a b in v \<noteq> None \<longrightarrow> v = suggestion s i b"

lemma inv1: "invariant the_ioa inv1"  by (try_inv invs:inv7 inv6)

abbreviation conservative_array where
  "conservative_array s \<equiv>  \<forall> i . ballot_array.conservative_array (vote s i)"

lemma conservative: "invariant the_ioa conservative_array"
proof -
  have "\<And> s . inv1 s \<Longrightarrow> conservative_array s"
    apply (simp add:inv_defs ballot_array.conservative_def ballot_array.conservative_array_def
        split:option.splits) by (metis option.inject) 
  with inv1 show ?thesis  using IOA.invariant_def by blast
qed

abbreviation safe_at where "safe_at s i \<equiv> ballot_array.safe_at quorums (ballot s) (vote s i)"

lemma safe_mono:
  -- {* @{term safe_at} is monotonic. A key lemma to simplify invariant proofs. *}
  assumes "s \<midarrow>a\<midarrow>the_ioa\<longrightarrow> t" and "safe_at s i v b"
  shows "safe_at t i v b"
proof -
  have "is_prefix (ballot s) (ballot t) (vote s i) (vote t i)" using \<open>s \<midarrow>a\<midarrow>the_ioa\<longrightarrow> t\<close>
    by (simp add:inv_defs ioa_defs; induct_tac rule:trans_cases, auto simp add:is_prefix_def inv_defs split:option.split_asm)
  thus ?thesis
  using assms ballot_array_prefix.safe_at_mono
  by (metis ballot_array_prefix_axioms_def ballot_array_prefix_def quorums_axioms) 
qed

definition inv3 where inv3_def[inv_defs]:
  "inv3 s \<equiv> \<forall> a b f i . onebs s a b = Some f \<longrightarrow> f i = dsa.acc_max (vote s i) a b \<and> ballot s a \<ge> b"
  
lemma inv3: "invariant the_ioa inv3"
  -- {* @{term inv3} is inductive on its own. The @{term do_vote} case necessitates  to show 
  that the value of @{term dsa.acc_max} dose not change as a result of the vote. 
  TODO: superseded by inv4. *}
  apply try_inv
  subgoal premises prems for s t _ a2 i2 v unfolding inv3_def
      -- {* the @{term do_vote} case *}
  proof (clarify, rule conjI)
    fix a b f i
    assume "onebs t a b = Some f"
    hence "onebs s a b = Some f" using \<open>do_vote a2 i2 v s t\<close> unfolding do_vote_def by auto
    hence "f i = dsa.acc_max (vote s i) a b" and "b \<le> ballot s a" using \<open>inv3 s\<close> unfolding inv3_def by auto
    have "dsa.acc_max (vote t i) a b = dsa.acc_max (vote s i) a b"
    proof -
      from \<open>b \<le> ballot s a\<close> have "\<And> b' . b' < b \<Longrightarrow> vote s i a b' = vote t i a b'" using  \<open>do_vote a2 i2 v s t\<close>
        unfolding do_vote_def by auto
      hence "{(v, ba). ba < b \<and> vote s i a ba = Some v} = {(v, ba). ba < b \<and> vote t i a ba = Some v}" by metis
      thus ?thesis unfolding dsa.acc_max_def dsa.a_votes_def by auto
    qed
    with \<open>f i = dsa.acc_max (vote s i) a b\<close> show "f i = dsa.acc_max (vote t i) a b" by auto
    from \<open>b \<le> ballot s a\<close> and \<open>do_vote a2 i2 v s t\<close> show "b \<le> ballot t a" unfolding do_vote_def by auto
  qed
  done

(* 
method instantiate_inv uses inv = (
  ( insert inv,
    instantiate_invs )?,
  match premises in R[thin]:"reachable ?ioa ?s" and T:"?s \<midarrow>?a\<midarrow>?ioa\<longrightarrow> ?t" \<Rightarrow> 
    \<open>insert reachable_n[OF R T]\<close>,
  ( insert inv,
    instantiate_invs )?,
  rm_reachable )
*)

definition inv4 where inv4_def[inv_defs]:
  "inv4 s \<equiv> \<forall> i b q . joined s q b \<longrightarrow> 
    (max_vote s i b q = dsa.max_quorum_votes (vote s i) q b) \<and> (\<forall> a \<in> q . ballot s a \<ge> b)"
lemma inv4:"invariant the_ioa inv4"
  -- {* This is a trivial consequence of @{thm inv3}. *}
proof - 
  have "inv4 s" if "inv3 s" for s unfolding inv4_def
  proof (clarsimp, rule conjI)
    fix i b q
    assume "joined s q b"
    hence "(the (onebs s a b)) i = dsa.acc_max (vote s i) a b" if "a \<in> q" for a
      using \<open>inv3 s\<close> inv3_def joined_def that by fastforce
    thus "max_vote s i b q = dsa.max_quorum_votes (vote s i) q b" 
      unfolding max_vote_def dsa.max_quorum_votes_def by auto
    show "\<forall>a\<in>q. b \<le> ballot s a" using \<open>inv3 s\<close> \<open>joined s q b\<close> unfolding joined_def inv3_def by auto
  qed
  thus ?thesis using IOA.invariant_def inv3 by blast 
qed

definition inv15 where inv15_def[inv_defs]:
  "inv15 s \<equiv> \<forall> b i q . joined s q b \<and> q \<in> quorums \<longrightarrow> 
  (case sugg s i b q of  Some v \<Rightarrow> dsa.proved_safe_at (ballot s) (vote s i) q b v
  | None \<Rightarrow> (\<forall> v . dsa.proved_safe_at (ballot s) (vote s i) q b v))"
lemma inv15:"invariant the_ioa inv15"
  -- {* Here the difficulty lies in the use of @{term the_elem} in @{thm sugg_def} *}
proof -
  have "inv15 s" if "inv4 s" and "conservative_array s" for s unfolding inv15_def
  proof (clarify)
    fix b i q
    assume  "joined s q b" and "q \<in> quorums"
    let ?proved="dsa.proved_safe_at (ballot s) (vote s i) q b"
    show "case sugg s i b q of  Some v \<Rightarrow> ?proved v | None \<Rightarrow> (\<forall> v . ?proved v)"
    proof (cases "sugg s i b q")
      case None
      then show ?thesis 
          --  {* TODO*}
        sorry
    next
      case (Some v)
      obtain x where "dsa.max_quorum_votes (vote s i) q b = {x}"
      proof -
        from Some have "max_vote s i b q \<noteq> {}" unfolding sugg_def by auto
        moreover
        have "max_vote s i b q = dsa.max_quorum_votes (vote s i) q b" by (metis \<open>joined s q b\<close>  \<open>inv4 s\<close> inv4_def)
        moreover 
        have "ballot_array.conservative_array (vote s i)" using \<open>conservative_array s\<close> by auto
        moreover note dsa_p.max_vote_e_or_singleton
        ultimately show ?thesis using that  by (metis \<open>q \<in> quorums\<close>) 
      qed
      moreover 
      have "v = (the_elem (fst ` (dsa.max_quorum_votes (vote s i) q b)))" using Some \<open>joined s q b\<close> \<open>inv4 s\<close>
        by (auto simp add:inv4_def sugg_def)
      ultimately show ?thesis using \<open>q\<in>quorums\<close> \<open>joined s q b\<close> \<open>inv4 s\<close> Some
        unfolding dsa.proved_safe_at_def inv3_def inv4_def by auto
    qed
  qed
  thus ?thesis by (metis (mono_tags, lifting) IOA.invariant_def conservative inv3 inv4)
qed

definition inv12 where inv12_def[inv_defs]:
  "inv12 s \<equiv> \<forall> b i q v . sugg s i b q = Some v \<and> joined s q b \<and> q \<in> quorums
    \<longrightarrow> dsa.proved_safe_at (ballot s) (vote s i) q b v"
lemma inv12:"invariant the_ioa inv12"
  -- {* Here the difficulty lies in the use of @{term the_elem} in @{thm sugg_def} *}
proof -
  have "inv12 s" if "inv4 s" and "inv3 s" and "conservative_array s" for s unfolding inv12_def
  proof  (clarify)
    fix b i q v 
    assume 1:"sugg s i b q = Some v" and 2:"joined s q b" and "q\<in>quorums"
    obtain x where "dsa.max_quorum_votes (vote s i) q b = {x}"
    proof -
      from 1 have "max_vote s i b q \<noteq> {}" unfolding sugg_def by auto
      moreover
      have "max_vote s i b q = dsa.max_quorum_votes (vote s i) q b" by (metis "2" \<open>inv4 s\<close> inv4_def)
      moreover 
      have "ballot_array.conservative_array (vote s i)" using \<open>conservative_array s\<close> by auto
      moreover note dsa_p.max_vote_e_or_singleton
      ultimately show ?thesis using that by (metis \<open>q \<in> quorums\<close>) 
    qed
    moreover 
    have "v = (the_elem (fst ` (dsa.max_quorum_votes (vote s i) q b)))" using 1 2 \<open>inv4 s\<close>
      by (auto simp add:inv4_def sugg_def)
    ultimately show "dsa.proved_safe_at (ballot s) (vote s i) q b v" using \<open>q\<in>quorums\<close> 2 \<open>inv3 s\<close>
      unfolding dsa.proved_safe_at_def inv3_def joined_def
      by (metis (full_types) image_empty image_insert insertI1 option.exhaust the_elem_eq)
  qed
  thus ?thesis by (metis (mono_tags, lifting) IOA.invariant_def conservative inv3 inv4)
qed

abbreviation safe where "safe s \<equiv> \<forall> i . ballot_array.safe  quorums (ballot s) (vote s i)"
declare ballot_array.safe_def[inv_defs]

lemma aqcuire_leadership_ok:
  fixes a q s t i v safe_at 
  defines "safe_at w \<equiv> dsa.safe_at (ballot t) (vote t i) w (ballot t a)"
  assumes "acquire_leadership a q s t" and "inv12 s" and "inv4 s" and "inv3 s" and "safe s"
    and "conservative_array s"
  shows "case suggestion t i (ballot t a) of Some v \<Rightarrow> safe_at v | None \<Rightarrow> safe_at v"
proof -
  let ?b = "ballot s a" 
  have 3:"?b = ballot t a" using \<open>acquire_leadership a q s t\<close> by (auto simp add:inv_defs safe_at_def)
  have 1:"q\<in>quorums" and 2:"\<And> a . a \<in> q \<Longrightarrow> ballot s a \<ge> ?b" using \<open>inv3 s\<close> \<open>acquire_leadership a q s t\<close> 
    by (auto simp add:inv3_def) 
  have 4:"vote s = vote t" and 5:"ballot s = ballot t" using \<open>acquire_leadership a q s t\<close> by auto
  have 6:"suggestion t i ?b = sugg s i ?b q" using \<open>acquire_leadership a q s t\<close> by auto
  show ?thesis
  proof (cases "suggestion t i ?b")
    case None
    with 6 have 7:"sugg s i ?b q = None" by auto
    have "dsa.proved_safe_at (ballot s) (vote s i) q ?b v"
    proof -
      have "max_vote s i ?b q = {}" using 7 by (auto simp add:sugg_def split!:if_splits) 
      hence "dsa.max_quorum_votes (vote s i) q ?b = {}" using \<open>inv4 s\<close>
        using assms(2) inv4_def by fastforce 
      thus ?thesis using 1 2 by (auto simp add:dsa.proved_safe_at_def)
    qed
    with \<open>safe s\<close> and \<open>conservative_array s\<close> show ?thesis using 6 7 4 5 3 1
      by (simp add: dsa_p.proved_safe_at_imp_safe_at safe_at_def)
  next
    case (Some w)
    from Some 6 have 7:"sugg s i ?b q = Some w" by auto
    have "dsa.proved_safe_at (ballot s) (vote s i) q ?b w"
    proof -
      have "w = the_elem (fst ` (max_vote s i ?b q))" using 7 by (auto simp add:sugg_def split!:if_splits) 
      hence "w = the_elem (fst ` (dsa.max_quorum_votes (vote s i) q ?b))" using \<open>inv4 s\<close>
        using assms(2) by (auto simp add:inv4_def)
      moreover obtain x where "dsa.max_quorum_votes (vote s i) q ?b = {x}" 
      proof -
        have "dsa.max_quorum_votes (vote s i) q ?b \<noteq> {}" using 7 \<open>inv4 s\<close> assms(2)
          unfolding inv4_def by (simp add:sugg_def)
        thus ?thesis using dsa_p.max_vote_e_or_singleton 1  \<open>conservative_array s\<close> that by blast
      qed
      ultimately show ?thesis using 1 2 by (simp add:dsa.proved_safe_at_def) 
    qed
    with \<open>safe s\<close> and \<open>conservative_array s\<close> show ?thesis using 6 7 4 5 3 1
      by (simp add: dsa_p.proved_safe_at_imp_safe_at safe_at_def)
  qed
qed

definition inv2 where
  -- {* a suggestion is safe. *}
  inv2_def[inv_defs]:
  "inv2 s \<equiv> safe s \<and> (\<forall> i b . case suggestion s i b of Some v \<Rightarrow> safe_at s i v b 
  | None \<Rightarrow> (ampr1_state.leader s (leader b) \<and> ballot s (leader b) = b) \<longrightarrow> (\<forall> v . safe_at s i v b))"

lemma inv2:"invariant the_ioa inv2"
  apply (rule invariantI)
   apply (simp (no_asm_use) add:inv_defs ioa_defs split!:option.splits)
   apply (simp add: dsa_p.safe_at_0)
  subgoal premises prems for s t a
  proof -
    from prems(3) have 1:"\<And> i v b . safe_at s i v b \<Longrightarrow> safe_at t i v b" using safe_mono by auto
    show ?thesis using prems
      apply -
      apply (instantiate_invs_2 invs:inv4 inv3 inv1 inv7 inv12 conservative)
      apply (drule is_trans_E)
      subgoal premises prems
      proof -
        have 2:?thesis if "suggestion t = suggestion s" and "ampr1_state.leader t = ampr1_state.leader s"
          and "ballot t = ballot s" using that 1 \<open>inv1 t\<close> \<open>inv2 s\<close>
          apply (auto simp add:inv_defs split:option.splits) apply metis by (metis option.distinct(1))
        show ?thesis using prems
          apply ((induct_tac rule:trans_cases, simp); rm_trans_rel_assm)
          subgoal premises prems for c (* propose *)
          proof -
            show ?thesis using \<open>inv2 s\<close> \<open>propose c s t\<close> 
              by (force simp add:inv_defs split!:option.splits) 
          qed
          subgoal premises prems for i v (* learn *)
          proof -
            show ?thesis using \<open>inv2 s\<close> \<open>learn i v s t\<close> by (simp add:inv_defs)
          qed
          subgoal premises prems for a b (* join_ballot *) 
            using \<open>inv2 s\<close> \<open>join_ballot a b s t\<close> 1
            apply (auto simp add:inv_defs split:option.splits)
            by (metis option.distinct(1))
          subgoal premises prems for a i v (* do_vote *)
            using \<open>do_vote a i v s t\<close> 2 by simp
          subgoal premises prems for a i b v (* suggest *)
            apply (auto simp add:inv2_def split:option.split)
            subgoal using \<open>suggest a i b v s t\<close> \<open>inv2 s\<close> by (simp add:inv2_def)
            subgoal using \<open>suggest a i b v s t\<close> \<open>inv2 s\<close> by (force simp add:inv2_def split:option.splits)
            subgoal premises prems2 for i2 b2 w
            proof (cases "suggestion s i2 b2")
              case None
              then show ?thesis using \<open>suggest a i b v s t\<close> \<open>inv2 s\<close> prems2 \<open>inv7 s\<close>
                apply (cases s, cases t, auto simp add:inv2_def inv7_def split:option.splits)
                by (metis option.distinct(1))
            next
              case (Some v2)
              then show ?thesis using \<open>suggest a i b v s t\<close> \<open>inv2 s\<close> prems2
                by (simp add:inv2_def split:option.splits)
            qed
            done
          subgoal premises prems for a q (* acquire_leadership *)
          proof -
            have "safe s" using \<open>inv2 s\<close> by (simp add:inv2_def)
            have "leader (ballot t a) = a" and "q \<in> quorums" using \<open>acquire_leadership a q s t\<close> by auto
            have "safe t" using \<open>inv2 s\<close> \<open>acquire_leadership a q s t\<close> by (auto simp add:inv2_def)
            note 3 = aqcuire_leadership_ok[OF \<open>acquire_leadership a q s t\<close> \<open>inv12 s\<close> \<open>inv4 s\<close> \<open>inv3 s\<close> \<open>safe s\<close> \<open>conservative_array s\<close>]
            show ?thesis using \<open>safe t\<close> 
              apply (auto simp add:inv2_def split:option.splits)
              subgoal premises prems2 for i2 b2 v2
                apply (cases "b2 = ballot t a")
                subgoal by (metis "3" option.case_eq_if \<open>suggestion t i2 b2 = None\<close>)
                subgoal premises prems3 using \<open>acquire_leadership a q s t\<close> \<open>inv2 s\<close>
                  apply (cases s, cases t, auto simp add:inv2_def split:option.splits)
                  by (metis (no_types, lifting) ampr1_state.select_convs(2) ampr1_state.select_convs(4) ampr1_state.select_convs(6) fun_upd_apply option.distinct(1) prems2(2) prems2(3) prems2(4) prems3)
                done
              subgoal for i2 b2 x2 using 3 \<open>acquire_leadership a q s t\<close> \<open>inv2 s\<close> 
                apply (cases s, cases t, auto simp add:inv2_def fun_upd_def split:option.splits)
              proof -
                fix propCmd :: "'b set" and ballota :: "'a \<Rightarrow> nat" and votea :: "nat \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> 'b option" and suggestion :: "nat \<Rightarrow> nat \<Rightarrow> 'b option" and onebs :: "'a \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> ('b \<times> nat) set) option" and leadera :: "'a \<Rightarrow> bool"
                assume a1: "\<And>i v. case sugg \<lparr>propCmd = propCmd, ballot = ballota, vote = votea, suggestion = suggestion, onebs = onebs, leader = leadera\<rparr> i (ballota a) q of None \<Rightarrow> safe_at \<lparr>propCmd = propCmd, ballot = ballota, vote = votea, suggestion = \<lambda>i x. if x = ballota a then sugg \<lparr>propCmd = propCmd, ballot = ballota, vote = votea, suggestion = suggestion, onebs = onebs, leader = leadera\<rparr> i (ballota a) q else suggestion i x, onebs = onebs, leader = \<lambda>x. x = a \<or> leadera x\<rparr> i v (ballot \<lparr>propCmd = propCmd, ballot = ballota, vote = votea, suggestion = \<lambda>i x. if x = ballota a then sugg \<lparr>propCmd = propCmd, ballot = ballota, vote = votea, suggestion = suggestion, onebs = onebs, leader = leadera\<rparr> i (ballota a) q else suggestion i x, onebs = onebs, leader = \<lambda>x. x = a \<or> leadera x\<rparr> a) | Some v \<Rightarrow> safe_at \<lparr>propCmd = propCmd, ballot = ballota, vote = votea, suggestion = \<lambda>i x. if x = ballota a then sugg \<lparr>propCmd = propCmd, ballot = ballota, vote = votea, suggestion = suggestion, onebs = onebs, leader = leadera\<rparr> i (ballota a) q else suggestion i x, onebs = onebs, leader = \<lambda>x. x = a \<or> leadera x\<rparr> i v (ballot \<lparr>propCmd = propCmd, ballot = ballota, vote = votea, suggestion = \<lambda>i x. if x = ballota a then sugg \<lparr>propCmd = propCmd, ballot = ballota, vote = votea, suggestion = suggestion, onebs = onebs, leader = leadera\<rparr> i (ballota a) q else suggestion i x, onebs = onebs, leader = \<lambda>x. x = a \<or> leadera x\<rparr> a)"
                assume "sugg \<lparr>propCmd = propCmd, ballot = ballota, vote = votea, suggestion = suggestion, onebs = onebs, leader = leadera\<rparr> i2 (ballota a) q = Some x2"
                then have "(case Some x2 of None \<Rightarrow> dsa.safe_at ballota (votea i2) x2 (ballota a) | Some b \<Rightarrow> safe_at \<lparr>propCmd = propCmd, ballot = ballota, vote = votea, suggestion = \<lambda>n na. if na = ballota a then sugg \<lparr>propCmd = propCmd, ballot = ballota, vote = votea, suggestion = suggestion, onebs = onebs, leader = leadera\<rparr> n (ballota a) q else suggestion n na, onebs = onebs, leader = \<lambda>a. a = a \<or> leadera a\<rparr> i2 b (ballot \<lparr>propCmd = propCmd, ballot = ballota, vote = votea, suggestion = \<lambda>n na. if na = ballota a then sugg \<lparr>propCmd = propCmd, ballot = ballota, vote = votea, suggestion = suggestion, onebs = onebs, leader = leadera\<rparr> n (ballota a) q else suggestion n na, onebs = onebs, leader = \<lambda>a. a = a \<or> leadera a\<rparr> a)) = (case sugg \<lparr>propCmd = propCmd, ballot = ballota, vote = votea, suggestion = suggestion, onebs = onebs, leader = leadera\<rparr> i2 (ballota a) q of None \<Rightarrow> safe_at \<lparr>propCmd = propCmd, ballot = ballota, vote = votea, suggestion = \<lambda>n na. if na = ballota a then sugg \<lparr>propCmd = propCmd, ballot = ballota, vote = votea, suggestion = suggestion, onebs = onebs, leader = leadera\<rparr> n (ballota a) q else suggestion n na, onebs = onebs, leader = \<lambda>a. a = a \<or> leadera a\<rparr> i2 x2 (ballot \<lparr>propCmd = propCmd, ballot = ballota, vote = votea, suggestion = \<lambda>n na. if na = ballota a then sugg \<lparr>propCmd = propCmd, ballot = ballota, vote = votea, suggestion = suggestion, onebs = onebs, leader = leadera\<rparr> n (ballota a) q else suggestion n na, onebs = onebs, leader = \<lambda>a. a = a \<or> leadera a\<rparr> a) | Some b \<Rightarrow> safe_at \<lparr>propCmd = propCmd, ballot = ballota, vote = votea, suggestion = \<lambda>n na. if na = ballota a then sugg \<lparr>propCmd = propCmd, ballot = ballota, vote = votea, suggestion = suggestion, onebs = onebs, leader = leadera\<rparr> n (ballota a) q else suggestion n na, onebs = onebs, leader = \<lambda>a. a = a \<or> leadera a\<rparr> i2 b (ballot \<lparr>propCmd = propCmd, ballot = ballota, vote = votea, suggestion = \<lambda>n na. if na = ballota a then sugg \<lparr>propCmd = propCmd, ballot = ballota, vote = votea, suggestion = suggestion, onebs = onebs, leader = leadera\<rparr> n (ballota a) q else suggestion n na, onebs = onebs, leader = \<lambda>a. a = a \<or> leadera a\<rparr> a))"
                  by simp
                then show "dsa.safe_at ballota (votea i2) x2 (ballota a)"
                  using a1
                  by (smt \<open>sugg \<lparr>propCmd = propCmd, ballot = ballota, vote = votea, suggestion = suggestion, onebs = onebs, leader = leadera\<rparr> i2 (ballota a) q = Some x2\<close> ampr1_state.select_convs(2) ampr1_state.select_convs(3) option.simps(5)) 
              qed
              done
          qed
          done
      qed
      done
  qed
  done
declare inv2[invs]

definition inv9 where
  inv9_def[inv_defs]:"inv9 s \<equiv> \<forall> i a b . ballot s a < b \<longrightarrow> vote s i a b = None"

lemma  inv9:"invariant the_ioa inv9"
apply (rule invariantI)
apply (force simp add:inv_defs ioa_defs)
  apply (unfold_to_trans_rel)
  apply ((induct_tac rule:trans_cases, simp); rm_reachable; rm_trans_rel_assm;
      (simp add:inv_defs; fail)?)
done
declare inv9[invs]

lemma chosen_mono: assumes "chosen s i v" and "s \<midarrow>a\<midarrow>the_ioa\<longrightarrow> t"
  shows "chosen t i v" using assms
apply (unfold_to_trans_rel)
apply ((induct_tac rule:trans_cases, simp); rm_trans_rel_assm)
apply (auto simp add:inv_defs split:option.splits)[3] defer
apply (auto simp add:inv_defs split:option.splits)[1]
apply (cases s, cases t, auto simp add:inv_defs ballot_array.chosen_def ballot_array.chosen_at_def split:option.splits)
  by (metis option.distinct(1))

(*
definition inv10 where inv4_def[inv_defs]:
  "inv10 s \<equiv> \<forall> i l . case learned s l i of Some v \<Rightarrow> chosen s i v | None \<Rightarrow> True"

lemma  inv10:"invariant the_ioa inv4"
apply (rule invariantI)
apply (force simp add:inv_defs)
apply instantiate_invs_2
apply (unfold_to_trans_rel)
apply (induct_tac rule:trans_cases, simp)
apply (auto simp add:inv_defs split:option.splits)[3] defer
apply (auto simp add:inv_defs split:option.splits)[1]
apply (insert chosen_mono[simplified inv_defs])
apply (auto simp add:inv4_def inv5_def  split:option.splits) oops
by (metis (mono_tags) ampr1_state.select_convs(3) ampr1_state.surjective ampr1_state.update_convs(3) fun_upd_same)
declare inv4[invs]


subsection {* Finally, the proof of agreement. *}

definition agreement where agreement_def[inv_defs]:
  "agreement s \<equiv> \<forall> i l1 l2 . let v = learned s l1 i; w = learned s l2 i 
    in v \<noteq> None \<and> w \<noteq> None \<longrightarrow> v = w"

lemma agreement:"invariant the_ioa agreement"
proof -
  text {* We prove that @{term inv4} and @{term  safe} imply @{term agreement}. 
    Therefore, since they are invariant, @{term agreement} is invariant} *}
  have "agreement s" if "inv4 s" and "safe s" for s
  proof (auto simp add:inv_defs)
    fix i l1 l2 v w
    assume a1:"learned s l1 i = Some v" and a2:"learned s l2 i = Some w"
    with \<open>inv4 s\<close> have "chosen s i v" and "chosen s i w" by (auto simp add:inv_defs split:option.splits)
    with \<open>safe s\<close> show "v = w" by (metis ballot_array_props.intro ballot_array_props.safe_imp_agreement quorums_axioms)
  qed
  thus ?thesis using inv4 inv8_inv2_safe oops by (metis (mono_tags, lifting) IOA.invariant_def)
qed
    
*)

end

end