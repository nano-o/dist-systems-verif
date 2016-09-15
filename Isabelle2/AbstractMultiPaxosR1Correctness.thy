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

method inv_cases uses invs declares inv_defs =
  (rule invariantI; (
      ((match premises in "?s \<in> ioa.start ?ioa" \<Rightarrow> \<open>-\<close>))
      | instantiate_invs_2 invs:invs; simp only:is_trans_simp;
        ((induct_tac rule:trans_cases | print_term "''case analysis failed''"), simp?); rm_trans_rel_assm
        ) )

subsection {* Invariants *}

definition inv1 where inv1_def[inv_defs]:
  "inv1 s \<equiv> \<forall> a . is_leader s a \<longrightarrow> leader (ballot s a) = a"

lemma inv1: "invariant the_ioa inv1" by (try_inv)

definition inv2 where inv2_def[inv_defs]:
  "inv2 s \<equiv> \<forall> a b i . leader b = a \<and> (ballot s a < b \<or> (ballot s a = b \<and> \<not> is_leader s a))
    \<longrightarrow> suggestion s i b = None"

lemma inv2: "invariant the_ioa inv2"  by (try_inv invs:inv1)

definition inv3 where inv3_def[inv_defs]:
  -- {* acceptors only vote for the suggestion. *}
  "inv3 s \<equiv> \<forall> i a b . let v = vote s a i b in v \<noteq> None \<longrightarrow> v = suggestion s i b"

lemma inv3: "invariant the_ioa inv3"  by (try_inv invs:inv1 inv2)

definition conservative where
  "conservative s \<equiv>  \<forall> i . ballot_array.conservative_array (flip (vote s) i)"

lemma conservative: "invariant the_ioa conservative"
proof -
  have "\<And> s . inv3 s \<Longrightarrow> conservative s"
    apply (simp add:inv_defs ballot_array.conservative_def ballot_array.conservative_array_def
       conservative_def split:option.splits) by (metis option.inject)
  with inv3 show ?thesis  using IOA.invariant_def by blast
qed

abbreviation safe_at where "safe_at s i \<equiv> ballot_array.safe_at quorums (ballot s) (flip (vote s) i)"

lemma safe_mono:
  -- {* @{term safe_at} is monotonic. A key lemma to simplify invariant proofs. *}
  assumes "s \<midarrow>a\<midarrow>the_ioa\<longrightarrow> t" and "safe_at s i v b"
  shows "safe_at t i v b"
proof -
  have "is_prefix (ballot s) (ballot t) (flip (vote s) i) (flip (vote t) i)" using \<open>s \<midarrow>a\<midarrow>the_ioa\<longrightarrow> t\<close>
    by (simp add:inv_defs ioa_defs; induct_tac rule:trans_cases, auto simp add:is_prefix_def inv_defs split:option.split_asm)
  thus ?thesis
  using assms ballot_array_prefix.safe_at_mono
  by (metis ballot_array_prefix_axioms_def ballot_array_prefix_def quorums_axioms) 
qed

context begin

definition inv4 where inv4_def[inv_defs]:
  "inv4 s \<equiv> \<forall> b i q . joined s q b \<and> q \<in> quorums \<longrightarrow> 
  (case sugg s i b q of  Some v \<Rightarrow> dsa.proved_safe_at (ballot s) (flip (vote s) i) q b v
  | None \<Rightarrow> (\<forall> v . dsa.proved_safe_at (ballot s) (flip (vote s) i) q b v))"
  
text {* To show that @{term inv4} is invariant, we will use two auxiliary invariants. *}

text {* First, we show that an acceptor that has sent a oneb for ballot b has indeed joined b, and that it includes
  its maximum vote before b. *}

definition inv4_1 where "inv4_1 s \<equiv> \<forall> a b f i . onebs s a b = Some f 
      \<longrightarrow> f i = dsa.acc_max (flip (vote s) i) a b \<and> ballot s a \<ge> b"

text {* Then, we show that @{term max_vote} is the maximum vote before b over a quorum that has joined b. *}

definition inv4_2 where "inv4_2 s \<equiv> \<forall> i b q . joined s q b \<longrightarrow> 
    (max_vote s i b q = dsa.max_quorum_votes (flip (vote s) i) q b) \<and> (\<forall> a \<in> q . ballot s a \<ge> b)"
  
private 
lemma inv4_1:"invariant the_ioa inv4_1"
  -- {* The @{term do_vote} case necessitates to show that the value of @{term dsa.acc_max} dose not change as a result of the vote.  *}
  apply (try_inv inv_defs:inv4_1_def)
  subgoal premises prems for s t _ a2 i2 v unfolding inv4_1_def
      -- {* the @{term do_vote} case *}
  proof (clarify, rule conjI)
    fix a b f i
    assume "onebs t a b = Some f"
    hence "onebs s a b = Some f" using \<open>do_vote a2 i2 v s t\<close> unfolding do_vote_def by auto
    hence "f i = dsa.acc_max (flip (vote s) i) a b" and "b \<le> ballot s a" using \<open>inv4_1 s\<close> unfolding inv4_1_def by auto
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
  
private
lemma inv4_2:"invariant the_ioa inv4_2"
proof - 
  have "inv4_2 s" if "inv4_1 s" for s unfolding inv4_2_def
  proof (clarsimp, rule conjI)
    fix i b q
    assume "joined s q b"
    hence "(the (onebs s a b)) i = dsa.acc_max (flip (vote s) i) a b" if "a \<in> q" for a
      using \<open>inv4_1 s\<close> that by (simp add: ampr1_ioa.joined_def inv4_1_def) 
    thus "max_vote s i b q = dsa.max_quorum_votes (flip (vote s) i) q b" 
      unfolding max_vote_def dsa.max_quorum_votes_def by auto
    show "\<forall>a\<in>q. b \<le> ballot s a" using \<open>inv4_1 s\<close> \<open>joined s q b\<close> unfolding joined_def inv4_1_def by auto
  qed
  thus ?thesis using IOA.invariant_def  inv4_1 by blast 
qed

lemma inv4:"invariant the_ioa inv4"
proof -
  have "inv4 s" if "inv4_2 s" and "conservative s" for s unfolding inv4_def
  proof (clarify)
    fix b i q
    assume  "joined s q b" and "q \<in> quorums"
    have "max_vote s i b q = dsa.max_quorum_votes (flip (vote s) i) q b" by (metis \<open>joined s q b\<close>  \<open>inv4_2 s\<close> inv4_2_def)
    let ?proved="dsa.proved_safe_at (ballot s) (flip (vote s) i) q b"
    show "case sugg s i b q of  Some v \<Rightarrow> ?proved v | None \<Rightarrow> (\<forall> v . ?proved v)"
    proof (cases "sugg s i b q")
      case None
      hence "dsa.max_quorum_votes (flip (vote s) i) q b = {}" unfolding sugg_def
          \<open>max_vote s i b q = dsa.max_quorum_votes (flip (vote s) i) q b\<close> by auto
      moreover from \<open>inv4_2 s\<close> and \<open>joined s q b\<close> have "\<And> a . a \<in> q \<Longrightarrow> ballot s a \<ge> b"
        using inv4_2_def by blast 
      ultimately show ?thesis using \<open>q \<in> quorums\<close> None unfolding dsa.proved_safe_at_def joined_def by auto 
    next
      case (Some v)
        -- {* Here the difficulty lies in the use of @{term the_elem} in @{thm sugg_def} *}
      obtain x where "dsa.max_quorum_votes (flip (vote s) i) q b = {x}"
      proof -
        from Some have "max_vote s i b q \<noteq> {}" unfolding sugg_def by auto
        moreover
        note \<open>max_vote s i b q = dsa.max_quorum_votes (flip (vote s) i) q b\<close>  and \<open>conservative s\<close> 
        moreover note dsa_p.max_vote_e_or_singleton
        ultimately show ?thesis using that unfolding conservative_def by (metis \<open>q \<in> quorums\<close>) 
      qed
      moreover 
      have "v = (the_elem (fst ` (dsa.max_quorum_votes (flip (vote s) i) q b)))" using Some \<open>joined s q b\<close> \<open>inv4_2 s\<close>
        by (auto simp add:inv4_2_def sugg_def)
      ultimately show ?thesis using \<open>q\<in>quorums\<close> \<open>joined s q b\<close> \<open>inv4_2 s\<close> Some
        unfolding dsa.proved_safe_at_def inv4_2_def by auto
    qed
  qed
  thus ?thesis using IOA.invariant_def conservative inv4_2 by blast 
qed

end

abbreviation safe where "safe s \<equiv> \<forall> i . ballot_array.safe  quorums (ballot s) (flip (vote s) i)"
declare ballot_array.safe_def[inv_defs]

lemma aqcuire_leadership_safe:
  fixes a q s t i v safe_at 
  defines "safe_at w \<equiv> dsa.safe_at (ballot t) (flip (vote t) i) w (ballot t a)"
  assumes "acquire_leadership a q s t" and "inv4 s" and "safe s" and "conservative s"
  shows "case suggestion t i (ballot t a) of Some v \<Rightarrow> safe_at v | None \<Rightarrow> safe_at v"
    -- {* Using @{thm inv4} and @{thm dsa_p.proved_safe_at_imp_safe_at}, we show that chaging leader is safe. *}
proof -
  let ?b = "ballot s a"
  have 1:"q \<in> quorums" and 2:"joined s q ?b" using \<open>inv4 s\<close> \<open>acquire_leadership a q s t\<close> by (auto simp add:inv4_def) 
  hence 3:"case sugg s i ?b q of None \<Rightarrow> \<forall>v. dsa.proved_safe_at (ballot s) (flip (vote s) i) q ?b v 
    | Some v \<Rightarrow> dsa.proved_safe_at (ballot s) (flip (vote s) i) q ?b v" using \<open>inv4 s\<close> using inv4_def by blast 
  have 4:"vote s = vote t" and 5:"ballot s = ballot t"
    and 6:"suggestion t i ?b = sugg s i ?b q" using \<open>acquire_leadership a q s t\<close> by auto 
  show ?thesis
  proof (cases "suggestion t i ?b")
    case None
    with \<open>acquire_leadership a q s t\<close> have "sugg s i ?b q = None" by auto
    with 3 have "dsa.proved_safe_at (ballot s) (flip (vote s) i) q ?b v" by simp 
    thus ?thesis  using "1" "4" "5" None assms(4) assms(5) dsa_p.proved_safe_at_imp_safe_at 
      by (simp add: safe_at_def conservative_def dsa_p.proved_safe_at_imp_safe_at)
  next
    case (Some w)
    from Some 6 have 7:"sugg s i ?b q = Some w" by auto
    hence "dsa.proved_safe_at (ballot s) (flip (vote s) i) q ?b w" using "3" by auto 
    with \<open>safe s\<close> and \<open>conservative s\<close> show ?thesis using 6 7 4 5 3 1
      by (simp add: conservative_def dsa_p.proved_safe_at_imp_safe_at safe_at_def)
  qed
qed

definition inv5 where
  -- {* a suggestion is safe. *}
  inv5_def[inv_defs]:
  "inv5 s \<equiv> safe s 
    \<and> (\<forall> i b . case suggestion s i b of Some v \<Rightarrow> safe_at s i v b 
      | None \<Rightarrow> (is_leader s (leader b) \<and> ballot s (leader b) = b) \<longrightarrow> (\<forall> v . safe_at s i v b))"

method insert_safe_mono = 
  match premises in P:"?s \<midarrow>?a\<midarrow>the_ioa\<longrightarrow> ?t" \<Rightarrow> \<open>insert safe_mono[OF P]\<close>

method inv_cases_2 uses invs declares inv_defs =
  (rule invariantI; (
      ((match premises in "?s \<in> ioa.start ?ioa" \<Rightarrow> \<open>-\<close>))
      | instantiate_invs_2 invs:invs; insert_safe_mono, simp only:is_trans_simp;
        ((induct_tac rule:trans_cases | print_term "''case analysis failed''"), simp?); rm_trans_rel_assm
        ) )

lemma inv5:"invariant the_ioa inv5"
  apply (inv_cases_2 invs:inv4 inv3 inv1 conservative)
        apply (simp (no_asm_use) add:inv_defs ioa_defs split!:option.splits, simp add: dsa_p.safe_at_0) (* base case *)
       apply (force simp add:inv5_def split:option.splits) (* propose *)
      apply (force simp add:inv_defs split:option.splits) (* learn *)
     apply (simp add:inv_defs split:option.splits; metis option.distinct(1)) (* join_ballot *)
  subgoal premises prems for s t _ a i v unfolding inv5_def (* do_vote *)
  proof (rule conjI)
    note mono = \<open>\<And>i v b. safe_at s i v b \<Longrightarrow> safe_at t i v b\<close>
    from \<open>do_vote a i v s t\<close> have "suggestion t = suggestion s" and "is_leader t = is_leader  s" and "ballot t = ballot s" by auto
    with \<open>inv5 s\<close> and mono show " \<forall>i b. case suggestion t i b of None \<Rightarrow>
      is_leader t (leader b) \<and> ballot t (leader b) = b \<longrightarrow> (\<forall>v. safe_at t i v b)
      | Some v \<Rightarrow> safe_at t i v b" apply (auto simp add:inv5_def split:option.splits) by (metis option.distinct(1))
    show "safe t" using mono \<open>inv5 s\<close> \<open>inv3 t\<close> \<open>suggestion t = suggestion s\<close> by (auto simp add:inv3_def inv5_def dsa.safe_def split:option.splits; metis)
  qed
   apply (simp add:inv_defs split:option.splits; metis option.distinct(1)) (* suggest *)
  subgoal premises prems for s t _ a q unfolding inv5_def (* acquire_leadership *)
  proof (rule conjI)
    note mono = \<open>\<And>i v b. safe_at s i v b \<Longrightarrow> safe_at t i v b\<close>
    show "safe t" using \<open>inv5 s\<close> mono and \<open>acquire_leadership a q s t\<close> by (simp add:inv5_def)
    have "safe s" using inv5_def \<open>inv5 s\<close> by blast
    note aqcuire_leadership_safe[OF \<open>acquire_leadership a q s t\<close> \<open>inv4 s\<close> \<open>safe s\<close> \<open>conservative s\<close>]
    moreover have "ballot t = ballot s" and "vote t = vote s" 
      and "\<And> b i . b \<noteq> ballot s a \<Longrightarrow> suggestion t i b = suggestion s i b" 
      and "is_leader t = (is_leader s)(a := True)" using \<open>acquire_leadership a q s t\<close> by simp_all
    ultimately show " \<forall>i b. case suggestion t i b of None \<Rightarrow>
      is_leader t (leader b) \<and> ballot t (leader b) = b \<longrightarrow> (\<forall>v. safe_at t i v b)
      | Some v \<Rightarrow> safe_at t i v b" using mono \<open>inv5 s\<close> \<open>inv1 s\<close> mono
      -- {* TODO: make this cleaner. *}
      apply (auto simp add:inv5_def inv1_def conservative_def split:option.splits)
         apply (metis option.case_eq_if)
        apply (metis option.simps(5))
       apply (metis fun_upd_same inv1_def option.distinct(1) prems(8))
    proof -
      fix i :: nat and b :: nat and x2 :: 'b
      assume a1: "ballot t = ballot s"
      assume a2: "vote t = vote s"
      assume a3: "suggestion t i b = Some x2"
      assume a4: "\<And>b i. b \<noteq> ballot s a \<Longrightarrow> suggestion t i b = suggestion s i b"
      assume a5: "\<forall>i b. (ballot s (leader b) = b \<longrightarrow> is_leader s (leader b) \<longrightarrow> (\<exists>y. suggestion s i b = Some y) \<or> (\<forall>v. dsa.safe_at (ballot s) (\<lambda>y. vote s y i) v b)) \<and> (\<forall>x2. suggestion s i b = Some x2 \<longrightarrow> dsa.safe_at (ballot s) (\<lambda>y. vote s y i) x2 b)"
      assume "\<And>i v. case suggestion t i (ballot s a) of None \<Rightarrow> dsa.safe_at (ballot t) (\<lambda>y. vote t y i) v (ballot t a) | Some v \<Rightarrow> dsa.safe_at (ballot t) (\<lambda>y. vote t y i) v (ballot t a)"
      then have "\<And>n b. case suggestion t n (ballot s a) of None \<Rightarrow> dsa.safe_at (ballot s) (\<lambda>a. vote s a n) b (ballot t a) | Some b \<Rightarrow> dsa.safe_at (ballot t) (\<lambda>a. vote t a n) b (ballot t a)"
        using a2 a1 by metis
      then have f6: "\<And>b. case suggestion t i (ballot s a) of None \<Rightarrow> dsa.safe_at (ballot s) (\<lambda>a. vote s a i) b (ballot t a) | Some b \<Rightarrow> dsa.safe_at (ballot t) (\<lambda>a. vote t a i) b (ballot t a)"
        by blast
      have f7: "ballot s a = b \<or> suggestion s i b = Some x2"
        using a4 a3 by (metis (full_types))
      have "ballot s a = b \<longrightarrow> dsa.safe_at (ballot s) (\<lambda>a. vote s a i) x2 b"
        using f6 a3 a2 a1 by force
      then show "dsa.safe_at (ballot s) (\<lambda>a. vote s a i) x2 b"
        using f7 a5 by blast
    qed
  qed
  done

definition inv6 where
  inv6_def[inv_defs]:"inv6 s \<equiv> \<forall> i a b . ballot s a < b \<longrightarrow> flip (vote s) i a b = None"

lemma  inv6:"invariant the_ioa inv6"
by (try_inv)

definition inv7 where inv7_def[inv_defs]:
  "inv7 s \<equiv> \<forall> i a b v . flip (vote s) i a b = Some v \<longrightarrow> safe_at s i v b"

lemma inv7:"invariant the_ioa inv7"
  apply (inv_cases_2 invs:inv5)
        apply (auto simp add:inv7_def ioa_defs inv5_def option.splits) (* automatic from here *)
proof -
  fix s :: "('b, 'a, ?'l) ampr1_state" and aa :: 'a and i :: nat and v :: 'b
  assume a1: "\<And>ia va b. dsa.safe_at (ballot s) (\<lambda>y. vote s y ia) va b \<Longrightarrow> dsa.safe_at (ballot s) (\<lambda>y. (if y = aa then (vote s aa)(i := vote s aa i(ballot s aa \<mapsto> v)) else vote s y) ia) va b"
  assume a2: "\<forall>i b. case suggestion s i b of None \<Rightarrow> is_leader s (leader b) \<and> ballot s (leader b) = b \<longrightarrow> (\<forall>v. dsa.safe_at (ballot s) (\<lambda>y. vote s y i) v b) | Some v \<Rightarrow> dsa.safe_at (ballot s) (\<lambda>y. vote s y i) v b"
  assume "suggestion s i (ballot s aa) = Some v"
  then have "case Some v of None \<Rightarrow> is_leader s (leader (ballot s aa)) \<and> ballot s (leader (ballot s aa)) = ballot s aa \<longrightarrow> (\<forall>b. dsa.safe_at (ballot s) (\<lambda>a. vote s a i) b (ballot s aa)) | Some b \<Rightarrow> dsa.safe_at (ballot s) (\<lambda>a. vote s a i) b (ballot s aa)"
    using a2 by metis
  then show "dsa.safe_at (ballot s) (\<lambda>a. (if a = aa then (vote s aa)(i := vote s aa i(ballot s aa \<mapsto> v)) else vote s a) i) v (ballot s aa)"
    using a1 by simp
qed
  
end

end