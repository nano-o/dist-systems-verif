section {* Properties of ballot arrays. *}

theory BallotArrayProperties
imports Main BallotArrays3 Quorums2
begin

context ballot_array
begin

subsection {* Properties of max_vote *}

context begin
  -- {* A context to hide some lemmas *}

private lemma finite_voted_bals:"finite {b::nat . \<exists> a . a \<in> q \<and> b \<le> bound \<and> vote a b \<noteq> None}"
proof -
  have "{b . \<exists> a . a \<in> q \<and> b \<le> bound \<and> vote a b \<noteq> None} \<subseteq> {b . b \<le> bound}"
    by auto
  moreover have "finite {b::nat . b \<le> bound}" by simp
  ultimately show ?thesis
  by (metis (no_types, lifting) finite_subset)
qed

private lemma max_voted_round_1:
  assumes "a \<in> q" and "(b::nat) \<le> bound" 
  and "case max_voted_round_q q bound of None \<Rightarrow> True | Some b\<^sub>m \<Rightarrow> b > b\<^sub>m"
  shows "vote a b = None"
proof (cases "max_voted_round_q q bound")
case None 
  thus ?thesis using assms(1,2)
  by (auto simp add:max_voted_round_q_def split:split_if_asm)
next
  case (Some b\<^sub>m\<^sub>a\<^sub>x)
  with this obtain a2 b2 v where "a2 \<in> q \<and> b2 \<le> bound \<and> vote a2 b2 = Some v"
  by (auto simp add:max_voted_round_q_def split:split_if_asm)
  hence "{b . \<exists> a . a \<in> q \<and> b \<le> bound \<and> vote a b \<noteq> None} \<noteq> {}" by auto
  with this obtain b2 a2 where "a2 \<in> q \<and> b2 \<le> bound \<and> vote a2 b2 \<noteq> None"
    by auto
  moreover note finite_voted_bals
  moreover have "b > Max {b . \<exists> a . a \<in> q \<and> b \<le> bound \<and> vote a b \<noteq> None}" using Some assms(3)
    by (auto simp add:max_voted_round_q_def split:split_if_asm)
  ultimately
  show ?thesis by (metis (mono_tags, lifting) Max.coboundedI assms(1,2) leD mem_Collect_eq) 
qed

private lemma max_voted_round_2 :
  assumes "max_voted_round_q q (bound::nat) = Some (b::nat)"
  obtains a where "a \<in> q" and "vote a b \<noteq> None" and "b \<le> bound"
proof -
  from assms have "b = Max {b . \<exists> a . a \<in> q \<and> b \<le> bound \<and> vote a b \<noteq> None}"
    by (auto simp add:max_voted_round_q_def split:split_if_asm)
  moreover note finite_voted_bals
  moreover obtain a2 b2 where "a2 \<in> q \<and> b2 \<le> bound \<and> vote a2 b2 \<noteq> None"
    using assms by (auto simp add:max_voted_round_q_def) (metis option.distinct(1))
  ultimately show ?thesis using that
  by (smt Max_in empty_iff finite_nat_set_iff_bounded_le mem_Collect_eq) 
qed

lemma is_safe_prop:
  assumes "is_safe q (bound::nat) v"
  obtains a b\<^sub>m\<^sub>a\<^sub>x where 
    "vote a b\<^sub>m\<^sub>a\<^sub>x = Some v" and "is_safe q bound v" and "a \<in> q"
    and "\<And> a2 b2 . \<lbrakk>a2 \<in> q; b2 > b\<^sub>m\<^sub>a\<^sub>x; b2 \<le> bound\<rbrakk> \<Longrightarrow> vote a2 b2 = None"
    and "b\<^sub>m\<^sub>a\<^sub>x \<le> bound" 
  | "\<And> a b . \<lbrakk>a \<in> q; b \<le> bound\<rbrakk> \<Longrightarrow> vote a b = None"
  nitpick[verbose, card 'v = 2, card 'a = 3, card nat = 2, card "'v option" = 3, card "nat option" = 3, expect=none]
proof -
  consider
    (a) "max_voted_round_q q bound = None"
  | (b) b\<^sub>m\<^sub>a\<^sub>x where "max_voted_round_q q bound = Some b\<^sub>m\<^sub>a\<^sub>x" by blast
  thus ?thesis
  proof (cases)
    case (a)
    thus ?thesis using that by (simp add: max_voted_round_1 option.case_eq_if) 
  next
    case (b)
    with assms max_voted_round_2 max_voted_round_1
    obtain a where "a \<in> q" and "vote a b\<^sub>m\<^sub>a\<^sub>x = Some v" and 1:"b\<^sub>m\<^sub>a\<^sub>x \<le> bound"
    and "\<And> a2 b2 . \<lbrakk>a2 \<in> q; b2 \<le> bound; b2 > b\<^sub>m\<^sub>a\<^sub>x\<rbrakk> \<Longrightarrow> vote a2 b2 = None"
      by (auto simp add:is_safe_def split add:option.splits) meson
    thus ?thesis using that assms by blast
  qed
qed

end

end

subsection {* Correctness of the @{term proved_safe_at} computation *}

locale ballot_array_props = ballot_array + quorums
begin

context 
begin 

lemma "safe_at v (bot::nat)"
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
      by (auto simp add:chosen_at_def)
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

text {* The main lemma. Inspired by section 2.2.2 of the paper "Fast Paxos", by Leslie Lamport. *}

lemma proved_safe_at_imp_safe_at:
  assumes "\<And> a j w . \<lbrakk>j < i; vote a j = Some w\<rbrakk> \<Longrightarrow> safe_at w j"
  and "proved_safe_at q i v" and "conservative_array"
  shows "safe_at v (i::nat)"
proof (cases "i = 0")
  case True thus ?thesis
    by (metis not_less0 safe_at_def) 
next
  case False
  text {* There are two cases: 
    (a) an acceptor a in the quorum q voted in round k < i, 
    and k is the maximum round smaller than i in which an acceptor in q voted;
    (b) no acceptor in the quorum q voted in any round k < i *}
  consider
    (a) k a
      where "a \<in> q" and "vote a k = Some v" and "k < i"
      and "\<And> a\<^sub>2 l . \<lbrakk>a\<^sub>2 \<in> q; k < l; l < i\<rbrakk> \<Longrightarrow> vote a\<^sub>2 l = None"
  | (b) "\<And> a k . \<lbrakk>a \<in> q; k < i\<rbrakk>  \<Longrightarrow> vote a k = None" 
    using False assms(2) is_safe_prop by (simp add:proved_safe_at_def split add:nat.splits) (smt less_Suc_eq_le)
  thus ?thesis
  text {* now we prove the thesis by considering the cases (a) and (b) separately *}
  proof (cases)
    case b
    text {* We prove that no value is choosable at any @{text "j < i"}; 
      therefore, anything is safe at i *}
    { fix j w
      assume 1:"j < i"  and 2:"choosable w j"
      from \<open>choosable w j\<close> obtain q2 where 3:"q2 \<in> quorums" and 4:"\<And> a . a \<in> q2 \<Longrightarrow>
        (ballot a) > j \<Longrightarrow> vote a j = Some w" by (auto simp add:choosable_def)
      from \<open>q2 \<in> quorums\<close> \<open>proved_safe_at q i v\<close> \<open>j < i\<close> quorum_inter_witness 
      obtain a where 5:"a \<in> q" and 6:"a \<in> q2" and 7:"ballot a > j"
        by (auto simp add:proved_safe_at_def split add:nat.splits option.splits)
          (metis dual_order.strict_trans1)
      from \<open>ballot a > j\<close> \<open>a \<in> q\<close> b have "vote a j = None" by (metis "1" "5")
      moreover from \<open>ballot a > j\<close> 4 \<open>a \<in> q2\<close>  have "vote a j = Some w" by metis 
      ultimately have False by auto }
    thus "safe_at v i" by (auto simp add:safe_at_def)
  next
    case a
    have "v' = v" if "choosable v' j" and "j < i" for j v'
    proof -
      text {* First obtain an acceptor that has voted for v' in j *}
      obtain a2 where "a2 \<in> q" and "vote a2 j = Some v'"
      proof -
        from \<open>proved_safe_at q i v\<close> `i \<noteq> 0` 
        have "q \<in> quorums" and q_ballots:"\<And> a . a \<in> q \<Longrightarrow> ballot a \<ge> i" 
          by (auto simp add:proved_safe_at_def split add:nat.splits)
        from \<open>choosable v' j\<close> obtain q2 where "q2 \<in> quorums" and q2_votes:"\<And> a . a \<in> q2 \<Longrightarrow>
          (ballot a) > j \<Longrightarrow> vote a j = Some v'" by (auto simp add:choosable_def)
        from \<open>q2 \<in> quorums\<close> \<open>q \<in> quorums\<close> q_ballots quorum_inter_witness \<open>j < i\<close> 
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
          by (simp add:conservative_def conservative_array_def split add:option.splits)
      qed
    qed
    thus ?thesis
      by (metis safe_at_def) 
  qed
qed

lemma proved_safe_imp_safe:
  assumes "\<And> b a v . vote a b = Some v \<Longrightarrow> \<exists> q \<in> quorums .
    proved_safe_at q b v \<and>  (\<forall> a \<in> q . ballot a \<ge> b)"
  and conservative_array
  shows safe
  nitpick[verbose, card 'a = 3, card 'b = 2, card nat = 3, card "'b option" = 2, card "nat option" = 4, expect=none]
  proof (auto simp add: safe_def split add:option.split)
    fix a b w
    assume "vote a b = Some w"
    thus "safe_at w b" 
    by (induct b arbitrary:w a rule:nat_less_induct)
      (metis (full_types) assms(1,2) proved_safe_at_imp_safe_at)
  qed

text {* The lemma @{thm proved_safe_imp_safe} says that as long as acceptors vote for things that 
  are proven safe, and only a unique value can be vote for in a given ballot, 
  then the ballot array is safe. }*}

end

end

subsection {* Monotonicity *}

text {* We define a prefix relation on ballot arrays and show that a value safe b remains 
  safe at be when the ballot array grows *}

context begin

definition is_prefix where
  "is_prefix b1 b2 v1 v2 \<equiv> \<forall> a . b1 a \<le> b2 a 
    \<and> (\<forall> b . (b < b1 a \<or> (b = b1 a \<and> v1 a b \<noteq> None)) \<longrightarrow> v1 a b = v2 a b)"

end

locale ballot_array_prefix =
  -- {* @{typ 'a} is the type of acceptors *}
  fixes ballot1 :: "'a \<Rightarrow> nat"
  and vote1 :: "'a \<Rightarrow> nat \<Rightarrow> 'v option"
  and ballot2 :: "'a \<Rightarrow> nat"
  and vote2 :: "'a \<Rightarrow> nat \<Rightarrow> 'v option"
  and quorums :: "'a set set"
  assumes "BallotArrayProperties.is_prefix ballot1 ballot2 vote1 vote2"
begin

interpretation ba_1:ballot_array ballot1 vote1 quorums  .
interpretation ba_2:ballot_array ballot2 vote2 quorums  .

lemma choosable_decreases:
  assumes "ba_2.choosable v b"
  shows "ba_1.choosable v b"
  using assms ballot_array_prefix_axioms
  nitpick[card 'v = 1, card 'a = 1, verbose, card nat = 2, card "'v option" = 2, card "nat option" = 3, expect=none]
  by (auto simp add: BallotArrayProperties.is_prefix_def ballot_array.choosable_def ballot_array_prefix_def)
   (metis dual_order.strict_trans1)

lemma safe_at_mono:
  assumes "ba_1.safe_at v b"
  shows "ba_2.safe_at v b"
  by (metis assms ballot_array.safe_at_def choosable_decreases)

lemma 
  assumes "\<forall>a \<in> q. b < ballot1 a" 
  shows "ba_1.is_safe q b v = ba_2.is_safe q b v" 
  nitpick[verbose, card 'v = 3, card 'a = 4, card nat = 4, card "'v option" = 4,
card "nat option" = 5, expect=none]
  apply (auto simp add:ballot_array.is_safe_def split add:option.splits) 
oops

lemma proved_safe_at_mono:
  assumes "ba_1.proved_safe_at q b v"
  shows "ba_2.proved_safe_at q b v"
using assms ballot_array_prefix_axioms
nitpick[card 'v = 3, card 'a = 3, verbose,  card nat = 3, card "'v option" = 4,
card "nat option" = 4, expect=none]
apply (auto simp add:ballot_array.proved_safe_at_def BallotArrayProperties.is_prefix_def ballot_array_prefix_def
  split add:nat.splits option.splits)
apply (meson order_trans)
(* TODO: Here we have to prove that max_vote is preserved when the ballot array grows *) 
oops

(* A wrong lemma *)
lemma safe_mono:
  assumes "ba_2.safe" and "ba_2.well_formed" and "ba_1.well_formed"
  shows "ba_1.safe"
nitpick[verbose, card 'v = 2, card 'a = 2, verbose,  card nat = 2, card "'v option" = 3, expect=potential] 
oops

end

end