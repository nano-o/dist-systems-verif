theory Paxos
imports "/home/nano/Documents/IO-Automata/IOA_Automation"  "~~/src/HOL/Eisbach/Eisbach_Tools"
  "/home/nano/Documents/IO-Automata/Simulations" "~~/src/HOL/Library/Monad_Syntax"
  "~~/src/HOL/Library/FSet"
  Transfer
begin

datatype ('v,'acc,'l, 'b::linorder) p_action =
  Propose 'v
| Learn 'v 'l
| Vote 'acc
| JoinBallot 'b 'acc

(* TODO: using 'b::linorder confuses the record package. *)
record ('v, 'acc, 'b) p_state =
  propCmd :: "'v fset"
  ballot :: "'acc \<Rightarrow> 'b option"
  vote :: "'acc \<Rightarrow> 'b \<Rightarrow> 'v option"
  suggestion :: "'b \<Rightarrow> 'v option"
    -- {* The suggestion of the leader of round b *}

fun less_eq_o where 
  "less_eq_o None _ = True"
| "less_eq_o (Some x) None = False"
| "less_eq_o (Some x) (Some y) = (x \<le> y)"

fun less_o where
  "less_o None None = False" 
| "less_o None _ = True"
| "less_o (Some x) None = False"
| "less_o (Some x) (Some y) = (x < y)"

subsection {* Transfer between nat option and nat *}

interpretation lifting_syntax .

fun nno where 
  "nno (x::nat) None = (x = 0)"
| "nno x (Some y) = (x = Suc y)"

lemma zero_None_trans[transfer_rule]:"nno (0::nat) None"
by (auto simp add:rel_fun_def)

lemma less_trans[transfer_rule]:"(nno ===> nno ===> (op \<longleftrightarrow>)) ((op \<le>)::nat \<Rightarrow> nat \<Rightarrow> bool) less_eq_o"
apply(auto simp add:rel_fun_def)
apply (metis Suc_le_mono antisym_conv2 le_0_eq less_eq_o.elims(3) option.discI option.inject nno.elims(2) zero_less_Suc)
by (metis Suc_le_mono eq_iff less_eq_o.elims(2) less_imp_le_nat option.discI option.inject nno.elims(2) zero_less_Suc)

lemma all_trans[transfer_rule]: "((nno ===> (op \<longleftrightarrow>)) ===> (op \<longleftrightarrow>)) All All"
apply(auto simp add:rel_fun_def)
apply (metis split_option_all nno.simps(1) nno.simps(2))
by (metis nat_induct nno.simps(1) nno.simps(2))

text {* Test of transfer *}
lemma haha[rule_format]: "\<forall> y . less_eq_o None (y::nat option)"
apply transfer_start
apply transfer_step
apply transfer_step
apply transfer_step
apply transfer_end
apply auto
done

instantiation option :: (linorder) linorder
begin

definition less_eq_def:"o1 \<le> o2 = less_eq_o o1 o2"
definition less_def:"o1 < o2 = less_o o1 o2"

instance 
apply(intro_classes)
apply (auto simp add:less_eq_def less_def)
apply (metis le_cases less_eq_o.elims(3) less_o.elims(2) less_o.simps(1) less_o.simps(2) not_le option.inject)
apply (metis less_eq_o.elims(2) less_o.elims(2) less_o.simps(1) less_o.simps(2) not_le option.inject)
apply (metis less_eq_o.elims(3) less_o.simps(2) less_o.simps(4) not_le)
apply (metis less_eq_o.elims(3) less_eq_o.simps(1) option.sel order_refl)
apply (smt less_eq_o.elims(2) less_eq_o.elims(3) less_o.simps(1) less_o.simps(2) option.inject order_trans)
apply (metis dual_order.antisym less_eq_o.elims(2) less_eq_o.simps(2) option.inject)
by (metis le_cases less_eq_o.elims(3) option.discI option.inject)

end

class linorder_bot = linorder + order_bot

locale Paxos = IOA +
  fixes acceptors::"'acc fset" and learners::"'l fset" and quorums::"'acc fset fset"
  (*and max::"('b::linorder) set \<Rightarrow> 'b"*)
  assumes "acceptors \<noteq> {||}"
    and "learners \<noteq> {||}"
    and "\<And> q1 q2 . \<lbrakk>q1 |\<in>| quorums; q2 |\<in>| quorums\<rbrakk> \<Longrightarrow> q1 |\<inter>| q2 \<noteq> {||}"
    and "\<And> q . q |\<in>| quorums \<Longrightarrow> q |\<subseteq>| acceptors"
    and "quorums \<noteq> {||}" (*
    and "\<And> bs . finite bs \<Longrightarrow> max bs \<in> bs"
    and "\<And> b bs . \<lbrakk>finite bs; b \<in> bs\<rbrakk> \<Longrightarrow> b \<le> max bs"*)
begin

text {* If Nitpick can find a model then the assumptions are not contradictory *}
lemma False nitpick oops

definition conservative where
  "conservative r b \<equiv> \<forall> a1 . \<forall> a2 . a1 |\<in>| acceptors \<and> a2 |\<in>| acceptors \<longrightarrow> (
    let v1 = (vote r) a1 b; v2 = (vote r) a2 b in 
      (v1 \<noteq> None \<and> v2 \<noteq> None) \<longrightarrow> v1 = v2)"

definition conservative_array where
  "conservative_array r \<equiv> \<forall> b . conservative r b"

fun max_vote_2 where
  "max_vote_2 votes (0::nat) = votes 0 \<bind> (\<lambda> v . Some (0,v))"
| "max_vote_2 votes (Suc b) = 
    ( case (votes (Suc b)) of None \<Rightarrow> max_vote_2 votes b
      |  Some v \<Rightarrow> Some (Suc b, v) )"

lemma assumes "i \<le> b" and "votes i \<noteq> None"
  shows "case (max_vote_2 votes b) of None \<Rightarrow> False | Some (m,v) \<Rightarrow> i \<le> m"
using assms
proof (induct votes b rule:max_vote_2.induct)
  case 1 thus ?case by fastforce
next
  case 2 thus ?case by auto (metis case_prodI le_Suc_eq option.case_eq_if option.sel option.simps(3))
qed

declare option.split[split]

lemma
  "case (max_vote_2 votes b) of None \<Rightarrow> True | Some (m,v) \<Rightarrow> m \<le> b \<and> votes m = Some v"
proof (induct votes b rule:max_vote_2.induct)
case (1 votes) thus ?case 
  apply (auto)
    apply (metis (no_types, lifting) Pair_inject bind_eq_Some_conv option.inject)
  apply (smt bind_eq_Some_conv option.sel prod.inject)
  done
next
  case (2 votes b) thus ?case by auto
qed

text {* Here the max is the one from Lattices_Big *}

definition max_acc_voted_round where
  "max_acc_voted_round r a bound \<equiv> Max {b . vote r a b \<noteq> None \<and> b \<le> bound}"
  
definition max_voted_round where
  "max_voted_round r q bound \<equiv> Max {max_acc_voted_round r a bound | a . a |\<in>| q}"
  
definition max_voted_round_2 where
  "max_voted_round_2 r q bound \<equiv> 
    if \<exists> b a . a |\<in>| q \<and> b \<le> bound \<and> vote r a b \<noteq> None
    then Some (Max {b . \<exists> a . a |\<in>| q \<and> b \<le> bound \<and> vote r a b \<noteq> None})
    else None"

lemma assumes "n > Max {j . P j}"
  and "finite {j . P j}"
  shows "\<not> P n" using assms
  by (metis Max_ge mem_Collect_eq not_le)

lemma finite_voted_bals:"finite {b::nat . \<exists> a . a |\<in>| q \<and> b \<le> bound \<and> vote r a b \<noteq> None}"
proof -
  have "{b . \<exists> a . a |\<in>| q \<and> b \<le> bound \<and> vote r a b \<noteq> None} \<subseteq> {b . b \<le> bound}"
    by auto
  moreover have "finite {b::nat . b \<le> bound}" by simp
  ultimately show ?thesis
  by (metis (no_types, lifting) finite_subset) 
qed

lemma max_voted_round_none:
  assumes "a |\<in>| q" and "(b::nat) \<le> bound" 
  and "max_voted_round_2 r q bound = None \<or> b > the (max_voted_round_2 r q bound)"
  shows "vote r a b = None"
proof (cases "max_voted_round_2 r q bound")
case None 
  thus ?thesis using assms(1,2)
  by (auto simp add:max_voted_round_2_def split:split_if_asm)
next
  case (Some b\<^sub>m\<^sub>a\<^sub>x)
  with this obtain a2 b2 v where "a2 |\<in>| q \<and> b2 \<le> bound \<and> vote r a2 b2 = Some v"
  by (auto simp add:max_voted_round_2_def split:split_if_asm)
  hence "{b . \<exists> a . a |\<in>| q \<and> b \<le> bound \<and> vote r a b \<noteq> None} \<noteq> {}" by auto
  with this obtain b2 a2 where "a2 |\<in>| q \<and> b2 \<le> bound \<and> vote r a2 b2 \<noteq> None"
    by auto
  moreover note finite_voted_bals
  moreover have "b > Max {b . \<exists> a . a |\<in>| q \<and> b \<le> bound \<and> vote r a b \<noteq> None}" using Some assms(3)
    by (auto simp add:max_voted_round_2_def split:split_if_asm)
  ultimately
  show ?thesis by (metis (mono_tags, lifting) Max.coboundedI assms(1,2) leD mem_Collect_eq) 
qed

lemma max_voted_round_some :
  assumes "max_voted_round_2 r q (bound::nat) = Some (b::nat)"
  obtains a where "a |\<in>| q" and "vote r a b \<noteq> None" and "b \<le> bound"
proof -
  from assms have "b = Max {b . \<exists> a . a |\<in>| q \<and> b \<le> bound \<and> vote r a b \<noteq> None}"
    by (auto simp add:max_voted_round_2_def split:split_if_asm)
  moreover note finite_voted_bals
  moreover obtain a2 b2 where "a2 |\<in>| q \<and> b2 \<le> bound \<and> vote r a2 b2 \<noteq> None"
    using assms by (auto simp add:max_voted_round_2_def) (metis option.distinct(1))
  ultimately show ?thesis using that
  by (smt Max_in empty_iff finite_nat_set_iff_bounded_le mem_Collect_eq) 
qed
 
definition max_vote where
  "max_vote r q bound \<equiv>
    case max_voted_round_2 r q bound of
      None \<Rightarrow> None
    | Some b \<Rightarrow> 
        let max_voter = (SOME a . a |\<in>| q \<and> vote r a b \<noteq> None)
        in (vote r) max_voter b"

lemma max_vote_some_prop:
  assumes "max_vote r q (bound::nat) = Some v"
  obtains a b\<^sub>m\<^sub>a\<^sub>x where "vote r a b\<^sub>m\<^sub>a\<^sub>x = max_vote r q bound" and "a |\<in>| q"
  and "\<And> a2 b2 . \<lbrakk>a2 |\<in>| q; b2 > b\<^sub>m\<^sub>a\<^sub>x; b2 \<le> bound\<rbrakk> \<Longrightarrow> vote r a2 b2 = None"
  and "b\<^sub>m\<^sub>a\<^sub>x \<le> bound"
proof -
  from assms obtain b\<^sub>m\<^sub>a\<^sub>x where 0:"max_voted_round_2 r q bound = Some (b\<^sub>m\<^sub>a\<^sub>x::nat)"
    by (auto simp add:max_vote_def) (metis (lifting) not_None_eq option.simps(4)) 
  with max_voted_round_some obtain a where
    "a |\<in>| q" and "vote r a b\<^sub>m\<^sub>a\<^sub>x \<noteq> None" and 1:"b\<^sub>m\<^sub>a\<^sub>x \<le> bound" by metis
  hence 
    "let a2 = SOME a . a |\<in>| q \<and> vote r a b\<^sub>m\<^sub>a\<^sub>x \<noteq> None in a2 |\<in>| q \<and> vote r a2 b\<^sub>m\<^sub>a\<^sub>x \<noteq> None"
      by (metis (mono_tags, lifting) someI_ex)
  moreover have "\<And> a2 b2 . \<lbrakk>a2 |\<in>| q; b2 \<le> bound; b2 > b\<^sub>m\<^sub>a\<^sub>x\<rbrakk> \<Longrightarrow> vote r a2 b2 = None" 
    using max_voted_round_none by (metis "0" option.sel)  
  moreover have "max_vote r q bound = (vote r) (SOME a . a |\<in>| q \<and> vote r a b\<^sub>m\<^sub>a\<^sub>x \<noteq> None) b\<^sub>m\<^sub>a\<^sub>x"
    using 0 by (auto simp add:max_vote_def)
  ultimately show ?thesis using that 1
    by (metis (no_types, lifting))
qed

lemma max_vote_none_prop:
  assumes "max_vote r q (bound::nat) = None"
  shows "\<And> a b . \<lbrakk>a |\<in>| q; b \<le> bound\<rbrakk> \<Longrightarrow> vote r a b = None"
using assms
apply (simp add:max_vote_def split add:option.split_asm)
    apply (smt max_voted_round_none)
  apply (smt Paxos.max_voted_round_some Paxos_axioms not_None_eq option.simps(3) someI_ex)
done
  
definition proved_safe_at where
  "proved_safe_at r Q b v \<equiv>
    case b of 0 \<Rightarrow> True
  | Suc c \<Rightarrow> (case (max_vote r Q c) of (* note that here c is b-1 *)
      None \<Rightarrow> True
    | Some v' \<Rightarrow> v = v')"

definition chosen_at where
  "chosen_at r v b \<equiv> \<exists> q . q |\<in>| quorums \<and> (\<forall> a . a |\<in>| q \<longrightarrow> (vote r) a b = (Some v))"

definition chosen where
  "chosen r v \<equiv> \<exists> b . chosen_at r v b"
  
definition choosable where
  "choosable r v b \<equiv>
    \<exists> q . q |\<in>| quorums \<and> (\<forall> a . a |\<in>| q \<longrightarrow> (
      (ballot r a) > Some b \<longrightarrow> (vote r) a b = Some v))"

definition safe_at where
  "safe_at r v b \<equiv>
    (\<forall> b2 . \<forall> v2 .
      ((b2 < b \<and> choosable r v2 b2) \<longrightarrow> (v = v2)))"

definition safe where
  "safe r \<equiv> \<forall> b . \<forall> a . a |\<in>| acceptors \<longrightarrow> 
    (let vote = (vote r) a b in (vote \<noteq> None \<longrightarrow> safe_at r (the vote) b))"
  
definition well_formed where
  "well_formed r \<equiv> \<forall> a b . a |\<in>| acceptors \<and> (ballot r) a < b  
    \<longrightarrow> (vote r) a (the b) = None"

lemma "safe_at r v (bot::'a::linorder_bot)"
by (auto simp add:safe_at_def)

lemma chosen_at_is_choosable:
  assumes "chosen_at r v b"
  shows "choosable r v b" using assms
  by (auto simp add:chosen_at_def choosable_def)

lemma safe_at_prec:
  assumes "safe_at r v (b::nat)" and "b2 < b"
  shows "safe_at r v b2"
  using assms by (meson order.strict_trans safe_at_def)

lemma quorum_inter_witness:
  assumes "q1 |\<in>| quorums" and "q2 |\<in>| quorums"
  obtains a where "a |\<in>| q1" and "a |\<in>| q2"
  using assms Paxos_axioms Paxos_def
  by (metis all_not_fin_conv finter_iff)

lemma quorum_vote:
  assumes "q1 |\<in>| quorums" and "q2 |\<in>| quorums"
  and "\<And> a . a |\<in>| q1 \<Longrightarrow> vote r a b = Some v1"
  and "\<And> a . a |\<in>| q2 \<Longrightarrow> vote r a b = Some v2"
  shows "v1 = v2"
proof -
  obtain a where "a |\<in>| q1" and "a |\<in>| q2"
  proof -
    have "q1 |\<inter>| q2 \<noteq> {||}" using assms(1,2)
      by (metis Paxos_axioms Paxos_def)
    hence "\<exists> a . a |\<in>| q1 \<and> a |\<in>| q2"
      by (metis assms(1) assms(2) quorum_inter_witness) 
    with that show ?thesis by auto
  qed
  thus ?thesis using assms(3,4) by force
qed

lemma chosen_at_same:
  assumes "chosen_at r v1 b1" and "chosen_at r v2 b1"
  shows "v1 = v2" using quorum_vote assms
  by (auto simp add:chosen_at_def) fast

lemma all_choosable_no_safe:
  assumes "\<And> (v::'v) . choosable r v b"
  and "safe_at r v (Suc b)" and "(v1::'v) \<noteq> v2"
  shows False using assms 
  by (auto simp add:safe_at_def)(metis lessI)

lemma safe_is_safe:
  assumes "safe r" and "chosen r v\<^sub>1" and "chosen r v\<^sub>2"
  shows "v\<^sub>1 = v\<^sub>2"
  -- {* This follows the proof of Proposition 1 from "Generalized Consensus and Paxos" *}
proof -
  text {* The main argument as a lemma to avoid repetitions*}
  { fix b\<^sub>1 b\<^sub>2 v\<^sub>1 v\<^sub>2
    assume 1:"chosen_at r v\<^sub>1 b\<^sub>1" and 2:"chosen_at r v\<^sub>2 b\<^sub>2"
    with this obtain q\<^sub>1 and q\<^sub>2 where 3:"\<And> a . a |\<in>| q\<^sub>1 \<Longrightarrow> (vote r) a b\<^sub>1 = (Some v\<^sub>1)" 
    and 4:"\<And> a . a |\<in>| q\<^sub>2 \<Longrightarrow> (vote r) a b\<^sub>2 = (Some v\<^sub>2)" and 5:"q\<^sub>1 |\<in>| quorums" and 6:"q\<^sub>2 |\<in>| quorums"
    by (auto simp add:chosen_at_def)
    have "v\<^sub>1 = v\<^sub>2" if "b\<^sub>1 < b\<^sub>2"
    proof -
      have 9:"choosable r v\<^sub>1 b\<^sub>1" using 1 chosen_at_is_choosable by fast
      have 10:"safe_at r v\<^sub>2 b\<^sub>2"
      proof -
        obtain a where "a |\<in>| q\<^sub>2" using 6 by (metis quorum_inter_witness)
        with this assms(1) 4 6 have "safe_at r (the (vote r a b\<^sub>2)) b\<^sub>2" 
          using Paxos_axioms Paxos_def apply auto (* Prood reconstruction fails without calling auto first *)
            by (metis Paxos_def fset_rev_mp option.discI option.sel safe_def)
        moreover have "the (vote r a b\<^sub>2) = v\<^sub>2" using `a |\<in>| q\<^sub>2` 4 by force
        ultimately show ?thesis by auto
      qed
      thus ?thesis using 9 10 assms(1) that by (metis safe_at_def)
    qed }
  note main = this
  obtain b\<^sub>1 and b\<^sub>2 where 1:"chosen_at r v\<^sub>1 b\<^sub>1" and 2:"chosen_at r v\<^sub>2 b\<^sub>2" using assms(2,3)
  by (auto simp add:chosen_def)
  have ?thesis if "b\<^sub>1 = b\<^sub>2" by (metis "1" "2" chosen_at_same that)
  moreover
  have ?thesis if "b\<^sub>1 < b\<^sub>2" using main 1 2 that by blast
  moreover 
  have ?thesis if "b\<^sub>2 < b\<^sub>1" using main 1 2 that by blast
  ultimately show ?thesis by fastforce
qed

lemma proved_safe:
  assumes "safe s" and "q |\<in>| quorums"
  and "\<And> a . a |\<in>| q \<Longrightarrow> ballot s a \<ge> Some i"
  and "proved_safe_at s q i v"
  shows "safe_at s v (i::nat)"
proof (cases "i = 0")
  case True thus ?thesis
    by (metis not_less0 safe_at_def) 
next
  case False
  consider (a) k a
    where "a |\<in>| q" and "vote s a k = Some v" and "k < i"
    and "\<And> a\<^sub>2 l . \<lbrakk>a\<^sub>2 |\<in>| q; k < l; l < i\<rbrakk> \<Longrightarrow> vote s a\<^sub>2 l = None"
  | (b) "\<And> a k . \<lbrakk>a |\<in>| q; k < i\<rbrakk>  \<Longrightarrow> vote s a k = None"
  proof (cases "max_vote s q (i-1)")
    case None 
    hence "\<And> a k . \<lbrakk>a |\<in>| q; k < i\<rbrakk>  \<Longrightarrow> vote s a k = None" 
      using False by (metis Suc_diff_eq_diff_pred Suc_leI diff_is_0_eq gr0I max_vote_none_prop)
    thus ?thesis using that by auto
  next
    case (Some v') 
    with this obtain k a where "a |\<in>| q" and "vote s a k = Some v" and "k < i"  
      and "\<And> a\<^sub>2 l . \<lbrakk>a\<^sub>2 |\<in>| q; k < l; l < i\<rbrakk> \<Longrightarrow> vote s a\<^sub>2 l = None"
      using False assms(4)
      by (simp add:proved_safe_at_def)
      (smt False Nitpick.case_nat_unfold Some Suc_pred less_Suc_eq_le max_vote_some_prop option.case_eq_if option.sel option.simps(3)) 
    thus ?thesis using that by auto
  qed
  thus ?thesis
  proof (cases)
    case b 
    { fix j v
      assume 1:"j < i"  and 2:"choosable s v j"
      from 2 obtain q2 where 3:"q2 |\<in>| quorums" and 4:"\<And> a . a |\<in>| q2 \<Longrightarrow>
        (ballot s a) > Some j \<Longrightarrow> (vote s) a j = Some v"
        by (auto simp add:choosable_def)
      from 3 assms(2) obtain a where 5:"a |\<in>| q" and 6:"a |\<in>| q2"
        using quorum_inter_witness by metis
      have 8:"ballot s a \<ge> Some j" using assms(3)
        by (metis "1" "5" less_eq_def less_eq_o.simps(3) less_imp_le order_trans) 
      have 9:"vote s a j = Some v" using assms(3)
        by (metis "1" "4" "5" "6" "8" leD le_neq_trans less_eq_def less_eq_o.simps(3))
      from b have False by (metis "1" "5" "9" option.distinct(1)) }
    thus ?thesis by (auto simp add:safe_at_def)
  next
    case a
    have "v' = v" if "choosable s v' j" and "j < i" for j v'
    proof -
      consider (aa) "j < k" | (bb) "j = k" | (cc) "k < j" by fastforce
      hence ?thesis
      proof cases
      case aa
      have "a |\<in>| acceptors"
        by (metis Paxos_axioms Paxos_def a(1) assms(2) fset_mp) 
      hence "safe_at s v k" using  assms(1)
        by (metis a(2) option.discI option.sel safe_def)
      with aa show ?thesis using that by (metis safe_at_def) 
    next
      case cc
      from that obtain q2 where 3:"q2 |\<in>| quorums" and 4:"\<And> a . a |\<in>| q2 \<Longrightarrow>
        (ballot s a) > Some j \<Longrightarrow> (vote s) a j = Some v'"
        by (auto simp add:choosable_def)
      from 3 assms(2) obtain a2 where 5:"a2 |\<in>| q" and 6:"a2 |\<in>| q2" 
        using quorum_inter_witness by metis
      from 5 assms(3) that(2) have 7:"ballot s a2 \<ge> Some j"
        by (metis less_eq_def less_eq_o.simps(3) less_imp_le order_trans) 
      from 7 6 4 have 8:"vote s a2 j = Some v'"
        by (metis "5" antisym_conv2 assms(3) leD less_eq_def less_eq_o.simps(3) that(2)) 
      show ?thesis using a(4) 5 that(2) 8 cc by (metis option.distinct(1))
    next
      case bb (* Here we probably need the fact that the array is conservative: *)
      have 1:"\<And> a . a |\<in>| acceptors \<Longrightarrow> vote s a k = Some v" sorry
      from that obtain q2 where 3:"q2 |\<in>| quorums" and 4:"\<And> a . a |\<in>| q2 \<Longrightarrow>
        (ballot s a) > Some j \<Longrightarrow> (vote s) a j = Some v'"
        by (auto simp add:choosable_def)
      from 3 assms(2) obtain a2 where 5:"a2 |\<in>| q" and 6:"a2 |\<in>| q2" 
        using quorum_inter_witness by metis
      have 7:"ballot s a2 \<ge> Some k"
        by (metis "5" a(3) assms(3) less_eq_def less_eq_o.simps(3) less_imp_le order_trans)
      have 8:"a2 |\<in>| acceptors"
        by (metis "5" Paxos_axioms Paxos_def assms(2) order.not_eq_order_implies_strict pfsubsetD) 
      have 9:"vote s a2 k = Some v"
        by (metis "1" "8")
      show ?thesis
        by (metis "4" "5" "6" "7" "9" antisym_conv2 assms(3) bb leD less_eq_def less_eq_o.simps(3) option.sel that(2)) 
    qed
    thus ?thesis by (auto simp add:safe_at_def)
  qed
  thus ?thesis
  by (metis Paxos.safe_at_def Paxos_axioms) 
  qed 
qed
  
section {* Paxos IOA *}

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
  "join_ballot a b s s' \<equiv> b > (ballot s a) \<and> s' = s\<lparr>ballot := (ballot s)(a := b)\<rparr>"

definition start_ballot where
  "start_ballot b s s' \<equiv> suggestion s b = None \<and>
    (\<exists> q v . q |\<in>| quorums \<and> proved_safe_at s q b v
      \<and> v |\<in>| propCmd s \<and> s' = s\<lparr>suggestion := (suggestion s)(b := Some v)\<rparr>)"

definition do_vote where
  "do_vote a s s' \<equiv> let bo = ballot s a; b = the bo in
    bo \<noteq> None \<and> vote s a b = None \<and> s' = s\<lparr>vote := (vote s)(a := (vote s a)(b := suggestion s b))\<rparr>"

definition learn where
  "learn l v s s' \<equiv> chosen s v \<and> s = s'"

fun p_trans_fun  where
  "p_trans_fun r (Propose c) r' = propose c r r'"
| "p_trans_fun r (JoinBallot b a) r' = join_ballot a b r r'"
| "p_trans_fun r (Vote a) r' = do_vote a r r'"
| "p_trans_fun r (Learn v l) r' = learn l v r r'"

definition p_trans where
  "p_trans \<equiv> { (r,a,r') . p_trans_fun r a r'}"

definition p_ioa where
  "p_ioa \<equiv> \<lparr>ioa.asig = p_asig, start = p_start, trans = p_trans\<rparr>"

end 

text {* We create a locale for the proof in order to fix the type variables appearing in p_ioa_def
  Otherwise we run into problem with polymorphism and Eisbach *}

locale paxos_proof = IOA + Paxos +
  fixes the_ioa
  defines "the_ioa \<equiv> p_ioa"
begin

lemmas p_ioa_defs =  
   is_trans_def actions_def p_trans_def p_start_def
   externals_def p_ioa_def p_asig_def

declare p_ioa_defs[inv_proofs_defs]

lemma gt_not_none:
  "b\<^sub>1 < (b\<^sub>2::'e::linorder option) \<Longrightarrow> b\<^sub>2 \<noteq> None"
by (metis less_def less_o.elims(2) option.discI)

declare propose_def[simp] join_ballot_def[simp] do_vote_def[simp]
  learn_def[simp]

definition inv1 where
  "inv1 s \<equiv> \<forall> a b . a |\<in>| acceptors \<and> vote s a b \<noteq> None 
    \<longrightarrow> vote s a b = suggestion s b"
declare inv1_def[inv_proofs_defs]

declare the_ioa_def[inv_proofs_defs]

lemma inv1:"invariant the_ioa inv1"
apply try_solve_inv2
apply (smt fun_upd_apply p_state.ext_inject p_state.surjective p_state.update_convs(3))
done
declare inv1[invs]

declare well_formed_def[inv_proofs_defs]
lemma well_formed_inductive:
  "invariant the_ioa well_formed"
apply try_solve_inv2
apply auto
apply (smt fun_upd_apply gt_not_none neq_iff option.collapse option.sel p_state.ext_inject p_state.surjective p_state.update_convs(3))
done
declare well_formed_inductive[invs]

declare conservative_array_def[inv_proofs_defs]
lemma conservative_inductive:
  "invariant the_ioa conservative_array"
apply (try_solve_inv2 inv_proofs_defs:inv_proofs_defs conservative_def)
apply metis
done

lemma 
  "\<lbrakk>reachable p_ioa s; chosen s v\<^sub>1; chosen s v\<^sub>2\<rbrakk> \<Longrightarrow> v\<^sub>1 = v\<^sub>2 " oops

end

end