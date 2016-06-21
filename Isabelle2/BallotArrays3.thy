section {* Definition of ballot arrays *}

theory BallotArrays3 
imports Main "~~/src/HOL/Library/Monad_Syntax" LinorderOption Quorums2
begin

lemma Max_Max:
  assumes "finite Xs" and "Union Xs \<noteq> {}" and "\<And> X . X \<in> Xs \<Longrightarrow> X \<noteq> {} \<and> finite X"
  shows "Max (Max ` Xs) = Max (Union Xs)" (is "?A = ?B")
nitpick[verbose, card 'a = 2, card "'a option" = 3, expect=none]
proof -
  have 0:"finite (Union Xs)" using assms(1,3) by auto
  hence 1:"?B \<in> Union Xs"
    by (metis Max_in assms(2))
  have "finite (Max ` Xs)" by (metis assms(1) finite_imageI)
  moreover have "Max ` Xs \<noteq> {}" using assms(2) by (metis Sup_empty image_is_empty) 
  ultimately have 3:"?A \<in> (Max ` Xs)" and "\<And> x . x \<in> Max ` Xs \<Longrightarrow> x \<le> ?A"
    by (metis Max_in, metis Max_ge \<open>finite (Max ` Xs)\<close>)
  show ?thesis by (smt 1 3 Max_ge Max_mono Sup_upper UnionE 0 antisym assms(1,3) finite_imageI image_iff) 
qed

lemma Max_bot:"\<lbrakk>finite (S::'b::{linorder,order_bot} set); S \<noteq> {}; s \<in> S; Max S = bot\<rbrakk> \<Longrightarrow> s = bot"
by (metis Max.coboundedI bot.extremum_uniqueI)

lemma max_insert_none:
  fixes S :: "'b::linorder option set"
  assumes "S \<noteq> {}" and "finite S"
  shows "Max (insert None S) = Max S"
using bot_def Max_insert assms bot.extremum max_def by metis

lemma Some_Max_commute:
  fixes S::"'b::linorder set" assumes "S \<noteq> {}" and "finite S"
  shows "Max (Some ` S) = Some (Max S)"
proof -
  have "mono (Some::('b::linorder \<Rightarrow> 'b option))" 
  proof (auto simp add:mono_def)
    fix x y :: "'b::linorder"
    assume "x \<le> y"
    thus "Some x \<le> Some y"
      by (metis less_eq_def less_eq_o.simps(3)) 
  qed
  thus ?thesis
  by (metis assms(1) assms(2) mono_Max_commute) 
qed

locale ballot_array = quorums quorums for quorums::"'a set set" +
  -- {* @{typ 'a} is the type of acceptors *}
  fixes ballot :: "'a \<Rightarrow> nat"
  and vote :: "'a \<Rightarrow> nat \<Rightarrow> 'v option"
begin

definition conservative where
  "conservative b \<equiv> \<forall> a1 . \<forall> a2 .
    let v1 = vote a1 b; v2 = vote a2 b in 
      case v1 of Some x \<Rightarrow> (case v2 of Some y \<Rightarrow> x = y | None \<Rightarrow> True) | None \<Rightarrow> True"

definition conservative_array where
  "conservative_array \<equiv> \<forall> b . conservative b"

text {* Here the @{term Max} is the one from @{text Lattices_Big} *}

definition proved_safe_at_2 where
  "proved_safe_at_2 q b v \<equiv>
    q \<in> quorums \<and> (\<forall> a \<in> q . ballot a \<ge> b) \<and>
    (if \<exists> a b\<^sub>2 . a \<in> q \<and> b\<^sub>2 < b \<and> vote a b\<^sub>2 \<noteq> None
    then \<exists> a b\<^sub>2 . a \<in> q \<and> b\<^sub>2 < b \<and> vote a b\<^sub>2 = Some v
      \<and> (\<forall> a\<^sub>2 b\<^sub>3 . a\<^sub>2 \<in> q \<and> b\<^sub>3 > b\<^sub>2 \<and> b\<^sub>3 < b \<longrightarrow> vote a\<^sub>2 b\<^sub>3 = None)
    else True)" (* TODO: why not Max ...? *)

definition proved_safe_at_2_a where
  "proved_safe_at_2_a q b v \<equiv>
    q \<in> quorums \<and> (\<forall> a \<in> q . ballot a \<ge> b) \<and>
    (if \<exists> a \<in> q . \<exists> b\<^sub>2 . b\<^sub>2 < b \<and> vote a b\<^sub>2 \<noteq> None
    then \<exists> a \<in> q . vote a (Max {b\<^sub>2 . \<exists> a \<in> q . b\<^sub>2 < b \<and> vote a b\<^sub>2 \<noteq> None}) = Some v
    else True)"

lemma "proved_safe_at_2_a q b v = proved_safe_at_2 q b v"
nitpick[verbose, card 'v = 2, card 'a = 3, card nat = 2, card "'v option" = 3,
card "nat option" = 3, card "nat option option" = 4, expect=none]
oops

definition voted_bal where
  "voted_bal a v_bal b \<equiv> v_bal < b \<and> vote a v_bal \<noteq> None"

lemma finite_voted_bal:"finite {b\<^sub>a. voted_bal a b\<^sub>a b}"
by (simp add: voted_bal_def)

definition chosen_at where
  "chosen_at v b \<equiv> \<exists> q . q \<in> quorums \<and> (\<forall> a \<in> q . (vote) a b = (Some v))"

definition chosen where
  "chosen v \<equiv> \<exists> b . chosen_at v b"
  
definition choosable where
  "choosable v b \<equiv>
    \<exists> q . q \<in> quorums \<and> (\<forall> a \<in> q . ballot a > b \<longrightarrow> vote a b = Some v)"

definition safe_at where
  "safe_at v b \<equiv>
    \<forall> b2 . \<forall> v2 . ((b2 < b \<and> choosable v2 b2) \<longrightarrow> (v = v2))"

definition safe where
  "safe \<equiv> \<forall> b . \<forall> a . case vote a b of None \<Rightarrow> True | Some v \<Rightarrow> safe_at v b"
  
definition well_formed where
  "well_formed \<equiv> \<forall> a b . ballot a < b \<longrightarrow> vote a b = None"

subsection {* Computing safe values in a distributed implementation *}

context begin

private
lemma q_finite[elim]:"\<And> q . q \<in> quorums \<Longrightarrow> finite q" using quorums_axioms quorums_def by auto
private
lemma q_ne[elim]:"\<And> q . q \<in> quorums \<Longrightarrow> q \<noteq> {}" using quorums_axioms quorums_def
  using quorum_inter_witness by auto 
private
lemma quorums_ne[intro]:"quorums = {} \<Longrightarrow> False"  using quorums_axioms quorums_def by auto

subsubsection {* A first high-level version *}

text {* The set of maximum ballots in quorum q. *}

definition voted_sets where "voted_sets q b \<equiv> {{b\<^sub>a . b\<^sub>a < b \<and> vote a b\<^sub>a \<noteq> None} 
  | a . a \<in> q \<and> {b\<^sub>a . b\<^sub>a < b \<and>  vote a b\<^sub>a \<noteq> None} \<noteq> {}}"

lemma in_voted_sets_finite[elim]: 
  assumes "q \<in> quorums" and "x \<in> voted_sets q b"
  shows "finite x" using assms by (auto simp add:voted_sets_def)

lemma in_voted_sets_ne[elim]: 
  assumes "q \<in> quorums" and "vs \<in> voted_sets q b"
  shows "vs \<noteq> {}" using assms by (auto simp add:voted_sets_def)

lemma voted_sets_finite[elim]: assumes "q \<in> quorums" shows "finite (voted_sets q b)" using assms
proof -
  have "finite q" using assms by auto
  thus ?thesis by (auto simp add:voted_sets_def)
qed

definition max_voted_sets_image where "max_voted_sets_image q b \<equiv> Max ` voted_sets q b"

lemma max_voted_sets_image_finite[elim]:
  assumes "q \<in> quorums" shows "finite (max_voted_sets_image q b)"
proof -
  have "finite {a \<in> q . {b\<^sub>a . b\<^sub>a < b \<and>  vote a b\<^sub>a \<noteq> None} \<noteq> {}}" using \<open>q \<in> quorums\<close> by force
  hence "finite {{b\<^sub>a . b\<^sub>a < b \<and> vote a b\<^sub>a \<noteq> None} | a . a \<in> q \<and> {b\<^sub>a . b\<^sub>a < b \<and>  vote a b\<^sub>a \<noteq> None} \<noteq> {}}" by auto
  thus "finite (max_voted_sets_image q b)" by (auto simp add:max_voted_sets_image_def voted_sets_def)
qed

lemma max_voted_sets_image_ne[elim]:
  assumes "q \<in> quorums" and "a \<in> q" and "{b\<^sub>a . b\<^sub>a < b \<and>  vote a b\<^sub>a \<noteq> None} \<noteq> {}"
  shows "max_voted_sets_image q b \<noteq> {}"
proof -
  have "{a \<in> q . {b\<^sub>a . b\<^sub>a < b \<and>  vote a b\<^sub>a \<noteq> None} \<noteq> {}} \<noteq> {}" using assms(2,3)
    by (metis (mono_tags, lifting) Collect_empty_eq)
  thus "max_voted_sets_image q b \<noteq> {}" by (auto simp add:max_voted_sets_image_def voted_sets_def)
qed

lemma voted_sets_union:"Union (voted_sets q b) = {b\<^sub>a . b\<^sub>a < b \<and> (\<exists> a \<in> q . vote a b\<^sub>a \<noteq> None)}"
nitpick[verbose, card 'v = 3, card 'a = 3, card nat = 3, card "'v option" = 4,
card "nat option" = 4, card "nat option option" = 5, expect=none]
by (auto simp add:voted_sets_def)

lemma Max_max_voted_sets_image[elim]:assumes "q \<in> quorums" shows "Max (max_voted_sets_image q b) = Max {b\<^sub>a . b\<^sub>a < b \<and> (\<exists> a \<in> q . vote a b\<^sub>a \<noteq> None)}"
nitpick[verbose, card 'v = 3, card 'a = 3, card nat = 3, card "'v option" = 4,
card "nat option" = 4, card "nat option option" = 5, expect=none]
proof (cases "Union (voted_sets q b) = {}")
  case True
  have "max_voted_sets_image q b = {}"
  proof -
    { assume "max_voted_sets_image q b \<noteq> {}"
      with this obtain vs where "vs \<in> voted_sets q b" by (auto simp add:max_voted_sets_image_def)
      hence "Union (voted_sets q b) \<noteq> {}" by (auto simp add:voted_sets_def) }
    with True show ?thesis by auto
  qed
  moreover have "{b\<^sub>a . b\<^sub>a < b \<and> (\<exists> a \<in> q . vote a b\<^sub>a \<noteq> None)} = {}"
    using True voted_sets_union by blast
  ultimately show ?thesis by metis
next
  case False 
  have 2:"finite (voted_sets q b)" using \<open>q \<in> quorums\<close> by fastforce
  have 3:"\<And> vs . vs \<in> voted_sets q b \<Longrightarrow> vs \<noteq> {} \<and> finite vs" using \<open>q \<in> quorums\<close> by (fastforce simp add:voted_sets_def)
  show ?thesis using Max_Max[OF 2 False 3, simplified] voted_sets_union by (simp add:max_voted_sets_image_def)
qed

definition proved_safe_at_3_a where 
  "proved_safe_at_3_a q b v \<equiv> q \<in> quorums \<and> (\<forall> a \<in> q . ballot a \<ge> b) \<and>
    (if (voted_sets q b = {}) then True else (\<exists> a \<in> q . vote a (Max (max_voted_sets_image q b)) = Some v))"

lemma assumes "q \<in> quorums" shows "proved_safe_at_3_a q b v = proved_safe_at_2_a q b v" (is "?A = ?B")
nitpick[verbose, card 'v = 2, card 'a = 3, card nat = 2, card "'v option" = 3,
card "nat option" = 3, card "nat option option" = 4, expect=none] 
oops
  
subsubsection {* A more detailed version *}

text {* The maximum voted ballot, per acceptor. Computed locally be an acceptor. *}
definition acc_max_bal where
  "acc_max_bal b a \<equiv> if {b\<^sub>a . b\<^sub>a < b \<and>  vote a b\<^sub>a \<noteq> None} \<noteq> {}
    then Some (Max {b\<^sub>a . b\<^sub>a < b \<and> vote a b\<^sub>a \<noteq> None})
    else None"

text {* The set of maximum voted ballot in a quorum. *}
definition q_max_bals where "q_max_bals q b \<equiv> acc_max_bal b ` q"

definition proved_safe_at_3 where 
  "proved_safe_at_3 q b v \<equiv> q \<in> quorums \<and> (\<forall> a \<in> q . ballot a \<ge> b) \<and>
    (case Max (q_max_bals q b) of None \<Rightarrow> True
    | Some b\<^sub>m \<Rightarrow> \<exists> a \<in> q . vote a b\<^sub>m = Some v)"

lemma q_max_bals_finite:
  assumes "q \<in> quorums"
  shows "finite (q_max_bals q b)"
  using assms by (auto simp add:q_max_bals_def)

lemma q_max_bals_ne: 
  assumes "q \<in> quorums"
  shows "q_max_bals q b \<noteq> {}"
using assms q_max_bals_def by (simp add: q_ne) 

lemma q_max_bals:"q_max_bals q b = (if (\<exists> a \<in> q . {b\<^sub>a . b\<^sub>a < b \<and>  vote a b\<^sub>a \<noteq> None} = {})
          then {None} \<union> (Some ` (max_voted_sets_image q b)) else (Some ` (max_voted_sets_image q b)))" 
      by (auto simp add:image_def Let_def acc_max_bal_def q_max_bals_def max_voted_sets_image_def voted_sets_def, blast, blast, metis)

lemma max_q_max_bals:
  assumes "q \<in> quorums" shows "Max (q_max_bals q b) = 
  (if (\<exists> a \<in> q . {b\<^sub>a . b\<^sub>a < b \<and>  vote a b\<^sub>a \<noteq> None} = {})
          then (if max_voted_sets_image q b = {} then None else Some (Max (max_voted_sets_image q b))) else (Some ( Max (max_voted_sets_image q b))))" 
nitpick[verbose, card 'v = 2, card 'a = 3, card nat = 2, card "'v option" = 3,
card "nat option" = 3, card "nat option option" = 4, expect=none]
oops

lemma q_max_bals_is_Max_max_voted_sets_image[intro]:
  assumes "a \<in> q" and "q \<in> quorums" and "{b\<^sub>a . b\<^sub>a < b \<and>  vote a b\<^sub>a \<noteq> None} \<noteq> {}"
  shows "Max (q_max_bals q b) = Some (Max (max_voted_sets_image q b))"
  using q_max_bals max_insert_none 
proof -
  have "finite (Some ` (max_voted_sets_image q b))"
    by (metis assms(2) finite_imageI max_voted_sets_image_finite) 
  have "(Some ` (max_voted_sets_image q b)) \<noteq> {}"
    by (metis (mono_tags) assms(1-3)  empty_is_image max_voted_sets_image_ne) 
  from q_max_bals                                       
  consider (a) "q_max_bals q b = {None} \<union> (Some ` (max_voted_sets_image q b))" | (b) "q_max_bals q b = (Some ` (max_voted_sets_image q b))" by meson
  thus ?thesis 
  proof (cases)
    case a thus ?thesis using max_insert_none[of "Some ` (max_voted_sets_image q b)"]
      by (metis Some_Max_commute \<open>Some ` max_voted_sets_image q b \<noteq> {}\<close> \<open>finite (Some ` max_voted_sets_image q b)\<close>assms(2) image_empty insert_is_Un max_voted_sets_image_finite)
  next
    case b thus ?thesis
      by (metis Some_Max_commute \<open>Some ` max_voted_sets_image q b \<noteq> {}\<close> assms(2) empty_is_image max_voted_sets_image_finite)
  qed
qed

lemma q_max_none_2:
  assumes "q \<in> quorums"
  shows "(Max (q_max_bals q b) = None) = (\<forall> a \<in> q . {b\<^sub>a . b\<^sub>a < b \<and>  vote a b\<^sub>a \<noteq> None} = {})" (is "?A = ?B")
proof -
  { assume "q \<in> quorums"
    have "(q_max_bals q b = {None}) = (\<forall> a \<in> q . {b\<^sub>a . b\<^sub>a < b \<and>  vote a b\<^sub>a \<noteq> None} = {})" (is "?A = ?B")
    proof 
      show "?A \<Longrightarrow> ?B" by (force simp add:q_max_bals_def image_def acc_max_bal_def)
      show "?B \<Longrightarrow> ?A" using \<open>q \<in> quorums\<close> by (auto simp add:acc_max_bal_def q_max_bals_def image_def, blast) 
    qed }
  thus ?thesis
  using Max_bot[of "q_max_bals q b"]
    by (metis (mono_tags) Max_singleton assms option.distinct(1) q_max_bals_is_Max_max_voted_sets_image)
qed

lemma assumes "q \<in> quorums" shows "proved_safe_at_2_a q b v = proved_safe_at_3 q b v" (is "?A = ?B")
nitpick[verbose, card 'v = 2, card 'a = 3, card nat = 2, card "'v option" = 3,
card "nat option" = 3, card "nat option option" = 4, expect=none]
proof (simp add:proved_safe_at_3_def, cases "Max (q_max_bals q b)", simp_all)
  assume "Max (q_max_bals q b) = None"
  with q_max_none_2 show "proved_safe_at_2_a q b v = (q \<in> quorums \<and> (\<forall>a\<in>q. b \<le> ballot a))"
    by (auto simp add:proved_safe_at_2_a_def)
next
  oops

end

end

end