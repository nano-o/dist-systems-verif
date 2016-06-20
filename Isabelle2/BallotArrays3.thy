section {* Definition of ballot arrays *}

theory BallotArrays3 
imports Main "~~/src/HOL/Library/Monad_Syntax" LinorderOption
begin

locale ballot_array =
  -- {* @{typ 'a} is the type of acceptors *}
  fixes ballot :: "'a \<Rightarrow> nat"
  and vote :: "'a \<Rightarrow> nat \<Rightarrow> 'v option"
  and quorums :: "'a set set"
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

definition voted_bal where
  "voted_bal a v_bal b \<equiv> v_bal < b \<and> vote a v_bal \<noteq> None"

lemma finite_voted_bal:"finite {b\<^sub>a. voted_bal a b\<^sub>a b}"
by (metis ballot_array.voted_bal_def bounded_nat_set_is_finite mem_Collect_eq)

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

definition acc_max_bal where
  "acc_max_bal b a \<equiv> if {b\<^sub>a . b\<^sub>a < b \<and>  vote a b\<^sub>a \<noteq> None} \<noteq> {}
    then Some (Max {b\<^sub>a . b\<^sub>a < b \<and> vote a b\<^sub>a \<noteq> None})
    else None"

(*
lemma Max_bot:"\<lbrakk>finite (S::'b::{linorder,order_bot} set); S \<noteq> {}; s \<in> S; Max S = bot\<rbrakk> \<Longrightarrow> s = bot"
nitpick[verbose, card 'b = 3, card "'b option" = 4, expect=none]
by (metis Max.coboundedI bot.extremum_uniqueI)

lemma Max_Max:
  assumes "finite Xs" and "Xs \<noteq> {}" and "\<And> X . X \<in> Xs \<Longrightarrow> X \<noteq> {} \<and> finite X"
  shows "let m = Max (Max ` Xs) in (\<exists> X \<in> Xs . m \<in> X) \<and> (\<forall> X \<in> Xs . \<forall> x \<in> X . x \<le> m)" 
nitpick[verbose, card 'b = 3, card "'b option" = 4, expect=none]
proof -
  have 1:"\<And> X . X \<in> Xs \<Longrightarrow> let m = Max X in m \<in> X \<and> (\<forall> x \<in> X . x \<le> m)"
    by (metis Max.coboundedI Max_in assms(3))
  have 2:"let m = Max (Max ` Xs) in m \<in> Max ` Xs \<and> (\<forall> x \<in> Max ` Xs . x \<le> m)"
    by (metis (full_types) Max_ge Max_in assms(1) assms(2) finite_imageI image_is_empty) 
  show ?thesis by (smt 1 2 imageE imageI order_trans)
qed

lemma Max_Max_2:
  assumes "finite Xs" and "Xs \<noteq> {}" and "\<And> X . X \<in> Xs \<Longrightarrow> X \<noteq> {} \<and> finite X"
  shows "Max (Max ` Xs) = Max (Union Xs)" 
nitpick[verbose, card 'b = 3, card "'b option" = 4, expect=none]
using Max_Max
by (smt Max_eqI UnionE UnionI assms(1) assms(2) assms(3) finite_Union) *)

definition q_max_bal where "q_max_bal q b \<equiv> acc_max_bal b ` q"

definition proved_safe_at_3 where 
  "proved_safe_at_3 q b v \<equiv> q \<in> quorums \<and> (\<forall> a \<in> q . ballot a \<ge> b) \<and>
    (case Max (q_max_bal q b) of None \<Rightarrow> True
    | Some b\<^sub>m \<Rightarrow> \<exists> a \<in> q . vote a b\<^sub>m = Some v)"

lemma q_max_bal_finite:
  assumes "finite q" and "q \<noteq> {}"
  shows "finite (q_max_bal q b)"
  using assms by (metis finite_imageI q_max_bal_def)

lemma q_max_bal_ne: 
  assumes "finite q" and "q \<noteq> {}"
  shows "q_max_bal q b \<noteq> {}"
by (metis assms(2) image_is_empty q_max_bal_def)

text {* The set of maximum ballots in quorum q. *}

definition maxs where "maxs q b \<equiv> Max ` {{b\<^sub>a . b\<^sub>a < b \<and> vote a b\<^sub>a \<noteq> None} 
  | a . a \<in> q \<and> {b\<^sub>a . b\<^sub>a < b \<and>  vote a b\<^sub>a \<noteq> None} \<noteq> {}}"

lemma maxs_finite:
  assumes "finite q" and "q \<noteq> {}" shows "finite (maxs q b)"
proof -
  have "finite {a \<in> q . {b\<^sub>a . b\<^sub>a < b \<and>  vote a b\<^sub>a \<noteq> None} \<noteq> {}}" using \<open>finite q\<close> by auto
  hence "finite {{b\<^sub>a . b\<^sub>a < b \<and> vote a b\<^sub>a \<noteq> None} | a . a \<in> q \<and> {b\<^sub>a . b\<^sub>a < b \<and>  vote a b\<^sub>a \<noteq> None} \<noteq> {}}" by auto
  thus "finite (maxs q b)" by (auto simp add:maxs_def)
qed

lemma maxs_ne:
  assumes "finite q" and "a \<in> q" and "{b\<^sub>a . b\<^sub>a < b \<and>  vote a b\<^sub>a \<noteq> None} \<noteq> {}"
  shows "maxs q b \<noteq> {}"
proof -
  have "{a \<in> q . {b\<^sub>a . b\<^sub>a < b \<and>  vote a b\<^sub>a \<noteq> None} \<noteq> {}} \<noteq> {}" using assms(2,3)
    by (metis (mono_tags, lifting) Collect_empty_eq)
  thus "maxs q b \<noteq> {}" by (auto simp add:maxs_def)
qed

lemma q_max_bal:"q_max_bal q b = (if (\<exists> a \<in> q . {b\<^sub>a . b\<^sub>a < b \<and>  vote a b\<^sub>a \<noteq> None} = {})
          then {None} \<union> (Some ` (maxs q b)) else (Some ` (maxs q b)))" 
      apply (auto simp add:image_def Let_def acc_max_bal_def q_max_bal_def maxs_def)
      apply blast apply blast apply metis done

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

lemma q_max_bal_is_Max_maxs:
  assumes "a \<in> q" and "finite q" and "{b\<^sub>a . b\<^sub>a < b \<and>  vote a b\<^sub>a \<noteq> None} \<noteq> {}"
  shows "Max (q_max_bal q b) = Some (Max (maxs q b))"
  using q_max_bal max_insert_none 
proof -
  have "finite (Some ` (maxs q b))"
    by (metis assms(1) assms(2) ballot_array.maxs_finite equals0D finite_imageI) 
  have "(Some ` (maxs q b)) \<noteq> {}"
    by (metis (mono_tags) assms(1) assms(2) assms(3) ballot_array.maxs_ne empty_is_image) 
  from q_max_bal                                       
  consider (a) "q_max_bal q b = {None} \<union> (Some ` (maxs q b))" | (b) "q_max_bal q b = (Some ` (maxs q b))" by meson
  thus ?thesis 
  proof (cases)
    case a thus ?thesis using max_insert_none[of "Some ` (maxs q b)"]
    by (metis \<open>Some ` maxs q b \<noteq> {}\<close> \<open>finite (Some ` maxs q b)\<close> assms(2) ballot_array.Some_Max_commute ballot_array.maxs_finite ballot_array.q_max_bal_def image_empty insert_is_Un insert_not_empty) 
  next
    case b thus ?thesis
      by (metis \<open>Some ` maxs q b \<noteq> {}\<close> assms(2) ballot_array.Some_Max_commute ballot_array.maxs_finite empty_is_image q_max_bal_def)
  qed
qed

lemma q_max_none:
  assumes "finite q" and "q \<noteq> {}"
  shows "(q_max_bal q b = {None}) = (\<forall> a \<in> q . {b\<^sub>a . b\<^sub>a < b \<and>  vote a b\<^sub>a \<noteq> None} = {})" (is "?A = ?B")
proof 
  show "?A \<Longrightarrow> ?B" by (force simp add:q_max_bal_def image_def acc_max_bal_def)
  show "?B \<Longrightarrow> ?A" using \<open>q \<noteq> {}\<close> by (auto simp add:acc_max_bal_def q_max_bal_def image_def)
qed 

lemma "proved_safe_at_2 q b v = proved_safe_at_3 q b v" (is "?A = ?B")
nitpick[verbose, card 'v = 1, card 'a = 1, card nat = 1, card "'v option" = 2,
card "nat option" = 2, card "nat option option" = 3]
proof 
  show "?A \<Longrightarrow> ?B" 
nitpick[verbose, card 'v = 1, card 'a = 1, card nat = 1, card "'v option" = 2,
card "nat option" = 2, card "nat option option" = 3]
  oops

end

end