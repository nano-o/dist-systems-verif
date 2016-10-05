section {* Properties of ballot arrays. *}

theory BallotArrayProperties
imports BallotArrays Quorums "~~/src/HOL/Library/Monad_Syntax"
begin

text {* 
In this theory we show the two main properties of ballot-arrays:
1) If a value v is @{term "ballot_array.proved_safe_at_abs q b v"}, then it is @{term "ballot_array.safe_at v b"}}
2) If a ballot array increases, according to the prefix definition below, then every
value that was @{term "ballot_array.safe_at v b"} before is still @{term "ballot_array.safe_at v b"}}}
*}

subsection {* Correctness of the @{term proved_safe_at} computation *}

context ballot_array
begin

definition a_votes where "a_votes a bound \<equiv> {(v,b) . b < bound \<and> vote a b = Some v}"

lemma a_votes_finite:
  shows "finite (a_votes a bound)"
proof - 
  have 1:"finite (S \<bind> f)" if "finite S" and "\<And> x . x \<in> S \<Longrightarrow> finite (f x)" for S f
    by (simp add: bind_UNION that)
  have 2:"a_votes a bound = {b . b < bound} \<bind> (\<lambda> b . case vote a b of Some v \<Rightarrow> {(v,b)} | None  \<Rightarrow> {})"
    (is "?votes = Set.bind ?bals ?f")
    by (auto simp add: Set.bind_def a_votes_def split!:option.split)
  have 3:"finite ?bals"
    by simp 
  have 4:"finite (?f b)" for b by (simp split!:option.split)
  show ?thesis
    by (metis (no_types, lifting) 2 3 1 4)
qed

definition q_votes where "q_votes q bound \<equiv> {(v,b) . b < bound \<and> (\<exists> a \<in> q . vote a b = Some v)}"

end

locale ballot_array_props = ballot_array quorums + quorums quorums for quorums
begin

lemma q_votes_q_votes:
  "q_votes q bound = (\<Union> a\<in>q . a_votes a bound)"
    by (auto simp add:q_votes_def a_votes_def)
  
lemma q_votes_finite:
  assumes "q \<in> quorums"
  shows "finite (q_votes q bound)" using assms(1) a_votes_finite quorums_axioms
  by (auto simp add:a_votes_def q_votes_q_votes quorums_def)
  
context 
begin 

lemma safe_at_0:"safe_at v (0::nat)"
by (auto simp add:safe_at_def)

(* Only used in safe \<Rightarrow> agreement *)
private lemma chosen_at_is_choosable:
  assumes "chosen_at v b"
  shows "choosable v b" using assms
  by (auto simp add:chosen_at_def choosable_def)

(*<*)
(* Not used *)
private lemma safe_at_prec:
  assumes "safe_at v b" and "b2 < b"
  shows "safe_at v b2"
  using assms by (meson order.strict_trans safe_at_def)
(*>*)

(* Only used in safe \<Rightarrow> agreement *)
private lemma chosen_at_same:
  assumes "chosen_at v1 b1" and "chosen_at v2 b1"
  shows "v1 = v2" 
by (metis assms chosen_at_def option.inject quorum_inter_witness)

(*<*)
(* Not used *)
private lemma all_choosable_no_safe:
  assumes "\<And> (v::'b) . choosable v b"
  and "safe_at v (Suc b)" and "(v1::'b) \<noteq> v2"
  shows False
  by (metis assms(1) assms(2) assms(3) lessI safe_at_def)
(*>*) 

lemma safe_imp_agreement:
  assumes "safe" and "chosen v\<^sub>1" and "chosen v\<^sub>2"
  shows "v\<^sub>1 = v\<^sub>2"
  -- {* This follows the proof of Proposition 1 from the paper "Generalized Consensus and Paxos" *}
proof -
  { text {* The main argument as a lemma, to avoid repetitions*}
    fix b\<^sub>1 b\<^sub>2 v\<^sub>1 v\<^sub>2
    assume 1:"chosen_at v\<^sub>1 b\<^sub>1" and 2:"chosen_at v\<^sub>2 b\<^sub>2"
    with this obtain q\<^sub>1 and q\<^sub>2 where 3:"\<And> a . a \<in> q\<^sub>1 \<Longrightarrow> (vote) a b\<^sub>1 = (Some v\<^sub>1)" 
    and 4:"\<And> a . a \<in> q\<^sub>2 \<Longrightarrow> (vote) a b\<^sub>2 = (Some v\<^sub>2)" and 5:"q\<^sub>1 \<in> quorums" and 6:"q\<^sub>2 \<in> quorums"
      by (fastforce simp add:chosen_at_def)
    have "v\<^sub>1 = v\<^sub>2" if "b\<^sub>1 < b\<^sub>2"
    proof -
      have 9:"choosable v\<^sub>1 b\<^sub>1" using 1 chosen_at_is_choosable by fast
      have 10:"safe_at v\<^sub>2 b\<^sub>2"
      proof -
        obtain a where "a \<in> q\<^sub>2" using 6 by (metis quorum_inter_witness)
        with this assms(1) 4 6 have "safe_at (the (vote a b\<^sub>2)) b\<^sub>2"
          by (metis option.case_eq_if option.distinct(1) safe_def)
        moreover have "the (vote a b\<^sub>2) = v\<^sub>2" using `a \<in> q\<^sub>2` 4 by force
        ultimately show ?thesis by auto
      qed
      thus ?thesis using 9 10 assms(1) that by (metis safe_at_def)
    qed }
  moreover
  obtain b\<^sub>1 and b\<^sub>2 where 1:"chosen_at v\<^sub>1 b\<^sub>1" and 2:"chosen_at v\<^sub>2 b\<^sub>2" using assms(2,3)
    by (auto simp add:chosen_def)
  ultimately
  show ?thesis using chosen_at_same 1 2 by (metis linorder_neqE_nat)
qed

subsection {* Proof that the proved_safe_at computation is correct. *}

lemma proved_safe_at_cases:
  assumes "proved_safe_at_abs q i v"
    -- {* There are two cases: 
    (a) an acceptor a in the quorum q voted in round k < i, 
    and k is the maximum round smaller than i in which an acceptor in q voted;
    (b) no acceptor in the quorum q voted in any round k < i *}
  obtains 
    (a) k a
  where "a \<in> q" and "vote a k = Some v" and "k < i"
    and "\<And> a\<^sub>2 l . \<lbrakk>a\<^sub>2 \<in> q; k < l; l < i\<rbrakk> \<Longrightarrow> vote a\<^sub>2 l = None"
  | (b) "\<And> a k . \<lbrakk>a \<in> q; k < i\<rbrakk>  \<Longrightarrow> vote a k = None"
proof -
  have "q \<in> quorums" and ballot_q:"\<And> a . a \<in> q \<Longrightarrow> ballot a \<ge> i" 
    using \<open>proved_safe_at_abs q i v\<close> by (auto simp add:proved_safe_at_abs_def)
  show ?thesis 
  proof (cases "\<exists> a \<in> q . \<exists> l . l < i \<and> vote a l \<noteq> None")
    case False thus ?thesis using that by blast
  next
    case True
    let ?votes="{(w,m) . m < i \<and> (\<exists> a \<in> q . vote a m = Some w)}"
    have 1:"v \<in> (fst ` (max_by_key ?votes snd))"  using True \<open>proved_safe_at_abs q i v\<close>
      by (simp add:proved_safe_at_abs_def)
    with this obtain x where 4:"x \<in> max_by_key ?votes snd" and 5:"fst x = v" by blast
    have 2:"finite ?votes" using \<open>q \<in> quorums\<close> q_votes_finite
      by (simp add: q_votes_def) 
    have 3:"?votes \<noteq> {}" using True by auto 
    have 6:"\<And> a\<^sub>2 l . \<lbrakk>a\<^sub>2 \<in> q; snd x < l; l < i\<rbrakk> \<Longrightarrow> vote a\<^sub>2 l = None" and 9:"snd x < i"
      using 4 3 apply (auto simp add:max_by_key[OF 2, of snd]) by (meson not_le option.exhaust)
    obtain a where 7:"a \<in> q" and 8:"vote a (snd x) = Some v" using \<open>x \<in> max_by_key ?votes snd\<close> 5
      by (auto simp add:max_by_key[OF 2, of snd])
    show ?thesis using that using 5 7 8 9 6 by auto
  qed
qed

text {* The main lemma. Inspired by section 2.2.2 of the paper "Fast Paxos", by Leslie Lamport. *}

lemma proved_safe_at_abs_imp_safe_at:
  assumes "\<And> a j w . \<lbrakk>j < i; vote a j = Some w\<rbrakk> \<Longrightarrow> safe_at w j"
  and "proved_safe_at_abs q i v" and "conservative_array"
  shows "safe_at v (i::nat)"
proof (cases "i = 0")
  case True thus ?thesis
    by (metis not_less0 safe_at_def)
next
  case False
  have "q \<in> quorums" and ballot_q:"\<And> a . a \<in> q \<Longrightarrow> ballot a \<ge> i" 
    using \<open>proved_safe_at_abs q i v\<close> by (auto simp add:proved_safe_at_abs_def)
  show ?thesis using \<open>proved_safe_at_abs q i v\<close>
  proof (cases rule:proved_safe_at_cases)
    case b
    text {* We prove that no value is choosable at any @{text "j < i"}; 
      therefore, anything is safe at i *}
    { fix j w
      assume "j < i"  and "choosable w j"
      from \<open>choosable w j\<close> obtain q2 where "q2 \<in> quorums" and q2_votes:"\<And> a . a \<in> q2 \<Longrightarrow>
        (ballot a) > j \<Longrightarrow> vote a j = Some w" by (auto simp add:choosable_def)
      from \<open>q2 \<in> quorums\<close> b \<open>j < i\<close> quorum_inter_witness \<open>q \<in> quorums\<close> ballot_q
      obtain a where "a \<in> q" and "a \<in> q2" and "ballot a > j"
        by (metis dual_order.strict_trans1)
      from \<open>a \<in> q\<close> b \<open>j < i\<close> have "vote a j = None" by metis
      moreover from \<open>ballot a > j\<close> q2_votes \<open>a \<in> q2\<close>  have "vote a j = Some w" by metis 
      ultimately have False by auto }
    thus "safe_at v i" by (auto simp add:safe_at_def)
  next
    case (a k a)
    have "v' = v" if "choosable v' j" and "j < i" for j v'
    proof -
      text {* First obtain an acceptor that has voted for v' in j *}
      obtain a2 where "a2 \<in> q" and "vote a2 j = Some v'"
      proof -
        from \<open>choosable v' j\<close> obtain q2 where "q2 \<in> quorums" and q2_votes:"\<And> a . a \<in> q2 \<Longrightarrow>
          (ballot a) > j \<Longrightarrow> vote a j = Some v'" by (auto simp add:choosable_def)
        from \<open>q2 \<in> quorums\<close> \<open>q \<in> quorums\<close> ballot_q quorum_inter_witness \<open>j < i\<close> 
          obtain a2 where "a2 \<in> q" and "a2 \<in> q2" and "ballot a2 > j" by (metis dual_order.strict_trans1)
        have "vote a2 j = Some v'" by (metis \<open>a2 \<in> q2\<close> \<open>j < ballot a2\<close> q2_votes) 
        from that \<open>vote a2 j = Some v'\<close> \<open>a2 \<in> q\<close> show ?thesis by simp
      qed
      text {* We consider the following three cases. *}
      consider (aa) "j < k" | (bb) "j = k" | (cc) "k < j" by fastforce
      thus ?thesis
      proof cases
        case aa
        text {* v' is choosable at j < k. Since there is a vote for v at k and the ballot array 
          before i is safe by assumption, we get that v' = v *}
        have "safe_at v k" using assms(1) \<open>vote a k = Some v\<close> \<open>k < i\<close> by metis
        with aa show ?thesis using that by (metis safe_at_def)
      next
        case cc
        text {* In this case we reach a contradiction because we can find a quorum which passed j 
          and did note vote at j, thus no value can be choosable at j. *}
        from cc and a(4) \<open>j < i\<close> \<open>a2 \<in> q\<close> have "vote a2 j = None" by metis
        with \<open>vote a2 j = Some v'\<close> have False by auto
        thus ?thesis by auto
      next
        case bb
        with \<open>conservative_array\<close> \<open>vote a2 j = Some v'\<close> \<open>vote a k = Some v\<close> show ?thesis 
          by (simp add:conservative_def conservative_array_def split: option.splits)
      qed
    qed
    thus ?thesis by (metis safe_at_def)
  qed
qed

end

end

subsection {* Monotonicity *}

text {* We define a prefix relation on ballot arrays and show that a value safe at b remains 
  safe at b when the ballot array grows *}

definition is_prefix where
  "is_prefix b1 b2 v1 v2 \<equiv> \<forall> a . b1 a \<le> b2 a
    \<and> (\<forall> b . (b < b1 a \<or> (b = b1 a \<and> v1 a b \<noteq> None)) \<longrightarrow> v1 a b = v2 a b)"

locale ballot_array_prefix = quorums quorums for  quorums :: "'a set set" +
  -- {* @{typ 'a} is the type of acceptors *}
  fixes ballot1 :: "'a \<Rightarrow> nat"
  and vote1 :: "'a \<Rightarrow> nat \<Rightarrow> 'v option"
  and ballot2 :: "'a \<Rightarrow> nat"
  and vote2 :: "'a \<Rightarrow> nat \<Rightarrow> 'v option"
  assumes "is_prefix ballot1 ballot2 vote1 vote2"
begin

interpretation ba_1:ballot_array quorums ballot1 vote1 
using quorums_axioms by (unfold_locales)
interpretation ba_2:ballot_array quorums ballot2 vote2
using quorums_axioms by (unfold_locales)

lemma choosable_decreases:
  assumes "ba_2.choosable v b"
  shows "ba_1.choosable v b"
  using assms ballot_array_prefix_axioms
  nitpick[card 'v = 1, card 'a = 1, verbose, card nat = 2, card "'v option" = 2, card "nat option" = 3, expect=none]
  by (auto simp add: is_prefix_def ba_2.choosable_def ba_1.choosable_def ballot_array_prefix_def ballot_array_prefix_axioms_def quorums_def)
    (meson dual_order.strict_trans1)

lemma safe_at_mono:
  assumes "ba_1.safe_at v b"
  shows "ba_2.safe_at v b"
  by (metis assms ba_1.safe_at_def ba_2.safe_at_def choosable_decreases)

lemma chosen_mono:
  assumes "ba_1.chosen v" and "ba_1.well_formed"
  shows "ba_2.chosen v" using assms ballot_array_prefix_axioms
  unfolding ba_1.chosen_def ba_2.chosen_def ballot_array_prefix_def quorums_def ballot_array_prefix_axioms_def
    is_prefix_def ba_2.chosen_at_def ba_1.chosen_at_def ba_1.well_formed_def apply auto
  by (metis not_less_iff_gr_or_eq option.distinct(1))
  
lemma safe_votes:
  assumes ba_1.safe and "\<And> b a v . \<lbrakk>vote1 a b \<noteq> vote2 a b; vote2 a b = Some v\<rbrakk> \<Longrightarrow> ba_1.safe_at v b"
  shows ba_2.safe
proof (auto simp add:ballot_array.safe_def split:option.splits)
  fix a b v
  assume "vote2 a b = Some v"
  show "ba_2.safe_at v b"
  proof (cases "vote1 a b = Some v")
    case True
    with assms(1) and safe_at_mono show ?thesis by (metis ba_1.safe_def option.simps(5))
  next
    case False
    from assms(2) have "ba_1.safe_at v b" using False \<open>vote2 a b = Some v\<close> by auto
    thus ?thesis using safe_at_mono by blast
  qed
qed

lemma safe_mono:
  -- {* Does not hold. *}
  assumes "ba_2.safe" and "ba_2.well_formed" and "ba_1.well_formed"
  shows "ba_1.safe"
nitpick[verbose, card 'v = 2, card 'a = 2, verbose,  card nat = 2, card "'v option" = 3, expect=potential]
oops

end

text {* A new prefix definition that accounts for acceptors crashing and loosing their state. 
  However, this is not going to work (see below). *}

definition is_prefix_2 where
  "is_prefix_2 qs b1 b2 v1 v2 \<equiv> \<forall> a . 
    ((b1 a \<le> b2 a) \<and> (\<forall> b . (b < b1 a \<or> (b = b1 a \<and> v1 a b \<noteq> None)) \<longrightarrow> v1 a b = v2 a b))
    \<or> ((\<exists> q \<in> qs . \<forall> a2 \<in> q . b1 a2 \<le> b2 a) \<and> (\<forall> b . v2 a b = None))"
  
locale ballot_array_prefix_2 = quorums quorums for  quorums :: "'a set set" +
  -- {* @{typ 'a} is the type of acceptors *}
  fixes ballot1 :: "'a \<Rightarrow> nat"
    and vote1 :: "'a \<Rightarrow> nat \<Rightarrow> 'v option"
    and ballot2 :: "'a \<Rightarrow> nat"
    and vote2 :: "'a \<Rightarrow> nat \<Rightarrow> 'v option"
  assumes "is_prefix_2 quorums ballot1 ballot2 vote1 vote2"
begin

interpretation ba_1:ballot_array quorums ballot1 vote1 
using quorums_axioms by (unfold_locales)
interpretation ba_2:ballot_array quorums ballot2 vote2
using quorums_axioms by (unfold_locales)

lemma choosable_decreases:
  assumes "ba_2.choosable v b" and "\<exists> q \<in> quorums . ba_1.joined b q"
  shows "ba_1.choosable v b"
  using assms ballot_array_prefix_2_axioms
  nitpick[card 'v = 2, card 'a = 3, verbose, card nat = 2, card "'v option" = 3, card "nat option" = 3, expect=none]
  apply (auto simp add:ballot_array_prefix_2_axioms_def ballot_array_prefix_2_def is_prefix_2_def
      ba_2.choosable_def ba_1.choosable_def ba_1.joined_def quorums_def)
proof -
  fix q :: "'a set" and qa :: "'a set" and x :: "'a set"
  assume a1: "qa \<in> quorums"
  assume a2: "\<forall>q. q \<in> quorums \<longrightarrow> (\<exists>a\<in>q. b < ballot1 a \<and> vote1 a b \<noteq> Some v)"
  assume a3: "\<forall>a. ballot1 a \<le> ballot2 a \<and> (\<forall>b. (b < ballot1 a \<longrightarrow> vote1 a b = vote2 a b) \<and> (b = ballot1 a \<and> (\<exists>y. vote1 a b = Some y) \<longrightarrow> vote1 a (ballot1 a) = vote2 a (ballot1 a))) \<or> (\<exists>q\<in>quorums. \<forall>a2\<in>q. ballot1 a2 \<le> ballot2 a) \<and> (\<forall>b. vote2 a b = None)"
  assume a4: "\<forall>a\<in>qa. b < ballot2 a \<longrightarrow> vote2 a b = Some v"
  obtain aa :: "'a set \<Rightarrow> 'a" where
    f5: "\<forall>A. A \<notin> quorums \<or> aa A \<in> A \<and> b < ballot1 (aa A) \<and> vote1 (aa A) b \<noteq> Some v"
    using a2 by moura
  then have f6: "aa qa \<in> qa \<and> b < ballot1 (aa qa) \<and> vote1 (aa qa) b \<noteq> Some v"
    using a1 by metis
  have "\<forall>a. ballot1 a \<le> ballot2 a \<and> (\<forall>n. (\<not> n < ballot1 a \<or> vote1 a n = vote2 a n) \<and> ((n \<noteq> ballot1 a \<or> (\<forall>v. vote1 a n \<noteq> Some v)) \<or> vote1 a (ballot1 a) = vote2 a (ballot1 a))) \<or> (\<exists>A. A \<in> quorums \<and> (\<forall>aa. aa \<notin> A \<or> ballot1 aa \<le> ballot2 a)) \<and> (\<forall>n. vote2 a n = None)"
    using a3 by metis
  then obtain AA :: "'a \<Rightarrow> 'a set" where
    "\<forall>a. ballot1 a \<le> ballot2 a \<and> (\<forall>n. (\<not> n < ballot1 a \<or> vote1 a n = vote2 a n) \<and> (n \<noteq> ballot1 a \<or> (\<forall>v. vote1 a n \<noteq> Some v) \<or> vote1 a (ballot1 a) = vote2 a (ballot1 a))) \<or> AA a \<in> quorums \<and> (\<forall>aa. aa \<notin> AA a \<or> ballot1 aa \<le> ballot2 a) \<and> (\<forall>n. vote2 a n = None)"
    by moura
  then show False
    using f6 f5 a4 by (metis dual_order.strict_trans1 option.simps(3))
qed     

lemma safe_at_mono:
  assumes "ba_1.safe_at v b" and "\<exists> q \<in> quorums . ba_1.joined b q"
  shows "ba_2.safe_at v b" 
  using assms choosable_decreases 
  unfolding ba_1.safe_at_def ba_2.safe_at_def ba_1.joined_def
proof -
  assume a1: "\<exists>q\<in>quorums. \<forall>a\<in>q. b \<le> ballot1 a"
  assume a2: "\<forall>b2 v2. b2 < b \<and> ba_1.choosable v2 b2 \<longrightarrow> v = v2"
  assume a3: "\<And>v b. \<lbrakk>ba_2.choosable v b; \<exists>q\<in>quorums. \<forall>a\<in>q. b \<le> ballot1 a\<rbrakk> \<Longrightarrow> ba_1.choosable v b"
  { fix nn :: nat and vv :: 'v
    have "\<forall>A n. \<exists>a. \<forall>v va. (A \<notin> quorums \<or> \<not> ba_2.choosable v n \<or> a \<in> A \<or> ba_1.choosable v n) \<and> (A \<notin> quorums \<or> \<not> n \<le> ballot1 a \<or> \<not> ba_2.choosable va n \<or> ba_1.choosable va n)"
      using a3 by metis
    then have "\<not> nn < b \<or> vv = v \<or> \<not> ba_2.choosable vv nn"
      using a2 a1 by (metis dual_order.trans nat_less_le) }
  then show "\<forall>n va. n < b \<and> ba_2.choosable va n \<longrightarrow> v = va"
    by metis
qed

text {* To use this lemma, we will have to prove that @{term ballot_array.leader_driven_array}
  is invariant. However this is not the case in the recovery Paxos, since an acceptor can 
  jump back ballots. *}

lemma safe_votes:
  assumes ba_1.safe and ba_1.leader_driven_array and ba_2.leader_driven_array
    and "\<And> b a v . \<lbrakk>vote1 a b \<noteq> vote2 a b; vote2 a b = Some v\<rbrakk> \<Longrightarrow> ba_1.safe_at v b \<and> ballot1 a = b"
    and "\<And> a . ballot1 a = ballot2 a"
  shows ba_2.safe 
  nitpick[card 'v = 2, card 'a = 3, verbose, card nat = 2, card "'v option" = 3, card "nat option" = 3, expect=none]
proof (auto simp add:ballot_array.safe_def split:option.splits)
  fix a b v
  assume 1:"vote2 a b = Some v"
  show "ba_2.safe_at v b"
  proof (cases "vote1 a b = Some v")
    case True
    with assms(1,2) and safe_at_mono show ?thesis 
      apply (auto simp add:ba_1.safe_def ba_1.leader_driven_array_def
          ba_2.leader_driven_array_def ba_1.safe_at_def ba_2.safe_at_def split:option.splits)
      by (metis (full_types))
  next
    case False
    have "ba_1.safe_at v b" using assms(4) 1 False by force
    moreover obtain q where "q \<in> quorums" and "ba_1.joined b q" 
    proof -
      obtain q where "q \<in> quorums" and "ba_2.joined b q" using 1 assms(3) by (force simp add:ba_2.leader_driven_array_def)
      thus ?thesis using that assms(5)  by (simp add:ba_2.joined_def ba_1.joined_def)
    qed
    ultimately show ?thesis using safe_at_mono by force
  qed
qed
    
end

end