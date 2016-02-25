theory Paxos
imports "../../IO-Automata/IOA"  "~~/src/HOL/Eisbach/Eisbach_Tools" 
  "../../IO-Automata/Simulations" "~~/src/HOL/Library/Monad_Syntax"
begin

class wellorder_bot = wellorder + bot +
  assumes bot:"\<And> x . bot \<le> x"

sublocale wellorder_bot \<subseteq> order_bot
using bot by (unfold_locales, auto)
  
datatype ('v,'acc,'l, 'b::wellorder_bot) p_action =
  Propose 'v
| Learn 'v 'l
| Vote 'v 'acc
| JoinBallot 'b 'acc

record ('v,'acc, 'b::linorder) p_state =
  propCmd :: "'v set"
  ballot :: "'acc \<Rightarrow> 'b option"
  vote :: "'acc \<Rightarrow> 'b \<Rightarrow> 'v option"

definition (in linorder) max_opt where
  "max_opt ao bo \<equiv> ao \<bind> (\<lambda> a . bo \<bind> (\<lambda> b . Some (max a b)))"
  
interpretation x: folding_idem max_opt "None::('b::linorder) option"
apply unfold_locales 
apply (case_tac x; case_tac y)
apply (auto simp add:comp_def max_opt_def fun_eq_iff)[4]
apply (case_tac xa)
apply auto[2]
using max.left_commute apply blast
apply (case_tac x)
apply(auto simp add:comp_def fun_eq_iff max_opt_def)
done

notation  x.F ("Max _" [99])

locale Paxos = IOA +
  fixes acceptors::"'acc set" and learners::"'l set" and quorums::"'acc set set"
  assumes "acceptors \<noteq> {}" and "finite acceptors"
    and "learners \<noteq> {}" and "finite learners"
    and "\<And> q1 q2 . \<lbrakk>q1 \<in> quorums; q2 \<in> quorums\<rbrakk> \<Longrightarrow> q1 \<inter> q2 \<noteq> {}"
    and "\<And> q . q \<in> quorums \<Longrightarrow> q \<subseteq> acceptors"
    and "finite quorums"
    and "quorums \<noteq> {}"
begin

definition p_asig where
  "p_asig \<equiv> 
    \<lparr> inputs = { a . \<exists> c . a = Propose c  },
      outputs = { a . \<exists> v . \<exists> l \<in> learners . a = Learn v l },
      internals = {a . \<exists> v . \<exists> acc \<in> acceptors . a = Vote v acc} 
        \<union> {a . \<exists> b . \<exists> acc \<in> acceptors . a = JoinBallot b acc}\<rparr>"

definition p_start where
  "p_start \<equiv> {\<lparr>propCmd = {}, ballot = (\<lambda> a . None), vote = (\<lambda> a b . None)\<rparr>}"

definition propose where
  "propose c r r' \<equiv> (r' = r\<lparr>propCmd := (propCmd r) \<union> {c}\<rparr>)"

definition conservative where
  "conservative r b \<equiv> \<forall> a1 \<in> acceptors . \<forall> a2 \<in> acceptors .
    let v1 = (vote r) a1 b; v2 = (vote r) a2 b in 
      (v1 \<noteq> None \<and> v2 \<noteq> None) \<longrightarrow> v1 = v2"

definition conservative_array where
  "conservative_array r \<equiv> \<forall> b . conservative r b"
  
definition max_acc_voted_round where
  "max_acc_voted_round r a bound \<equiv> Max {(vote r) a b | b . b \<le> bound}"
  
definition max_voted_round where
  "max_voted_round r q bound \<equiv> Max {max_acc_voted_round r a bound | a . a \<in> q}"
 
definition max_vote where
  "max_vote r q bound \<equiv>
    case max_voted_round r q bound of
      None \<Rightarrow> None
    | Some b \<Rightarrow> 
        let max_voter = (SOME a . a \<in> q \<and> max_acc_voted_round r a bound = Some b)
        in (vote r) max_voter b"
    
definition proved_safe_at where
  "proved_safe_at r Q b \<equiv> 
    case (max_vote r Q (b-1)) of 
      None \<Rightarrow> UNIV
    | Some v \<Rightarrow> {v}"

definition chosen_at where
  "chosen_at r v b \<equiv> \<exists> q \<in> quorums . \<forall> a \<in> q . (vote r) a b = (Some v)"

definition chosen where
  "chosen r v \<equiv> \<exists> b . chosen_at r v b"

definition higher where
  "higher bo b \<equiv> case bo of None \<Rightarrow> False | Some b2 \<Rightarrow> b2 > b"
  
definition choosable where
  "choosable r v b \<equiv>
    (\<exists> q \<in> quorums . (\<forall> a \<in> q . (case (ballot r) a of
          None \<Rightarrow> True
        | Some ba \<Rightarrow> (ba > b \<longrightarrow> (vote r) a b = Some v))))"

definition safe_at where
  "safe_at r v b \<equiv>
    (\<forall> b2 . \<forall> v2 .
      ((b2 < b \<and> choosable r v2 b2) \<longrightarrow> (v = v2)))"

definition safe where
  "safe r \<equiv> \<forall> b . \<forall> a \<in> acceptors . let vote = (vote r) a b in (vote \<noteq> None \<longrightarrow> safe_at r (the vote) b)"
  
definition well_formed where
  "well_formed r \<equiv> \<forall> a \<in> acceptors . \<forall> b . 
    (case (ballot r) a of None \<Rightarrow> True | Some ab \<Rightarrow> ab < b) \<longrightarrow> (vote r) a b = None"

lemma "safe_at r v (bot::'b::wellorder_bot)"
by (auto simp add:safe_at_def)

lemma chosen_at_is_choosable:
  assumes "chosen_at r v b"
  shows "choosable r v b" using assms
  by (auto simp add:chosen_at_def choosable_def) (smt option.case_eq_if)

lemma safe_at_prec:
  assumes "safe_at r v (b::nat)" and "b2 < b"
  shows "safe_at r v b2"
  using assms by (meson order.strict_trans safe_at_def)

lemma quorum_inter_witness:
  assumes "q1 \<in> quorums" and "q2 \<in> quorums"
  obtains a where "a \<in> q1" and "a \<in> q2"
  using assms Paxos_axioms Paxos_def
by (metis disjoint_iff_not_equal)

lemma quorum_vote:
  assumes "q1 \<in> quorums" and "q2 \<in> quorums"
  and "\<And> a . a \<in> q1 \<Longrightarrow> vote r a b = Some v1"
  and "\<And> a . a \<in> q2 \<Longrightarrow> vote r a b = Some v2"
  shows "v1 = v2"
proof -
  obtain a where "a \<in> q1" and "a \<in> q2"
  proof -
    have "q1 \<inter> q2 \<noteq> {}" using assms(1,2)
      by (metis Paxos_axioms Paxos_def)
    hence "\<exists> a . a \<in> q1 \<and> a \<in> q2"
      by (metis disjoint_iff_not_equal) 
    with that show ?thesis by auto
  qed
  thus ?thesis using assms(3,4) by force
qed   

lemma chosen_at_same:
  assumes "chosen_at r v1 b1" and "chosen_at r v2 b1"
  shows "v1 = v2" using quorum_vote assms
  by (auto simp add:chosen_at_def) fast

lemma
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
    with this obtain q\<^sub>1 and q\<^sub>2 where 3:"\<And> a . a \<in> q\<^sub>1 \<Longrightarrow> (vote r) a b\<^sub>1 = (Some v\<^sub>1)" 
    and 4:"\<And> a . a \<in> q\<^sub>2 \<Longrightarrow> (vote r) a b\<^sub>2 = (Some v\<^sub>2)" and 5:"q\<^sub>1 \<in> quorums" and 6:"q\<^sub>2 \<in> quorums"
    by (auto simp add:chosen_at_def)
    have "v\<^sub>1 = v\<^sub>2" if "b\<^sub>1 < b\<^sub>2"
    proof -
      have 9:"choosable r v\<^sub>1 b\<^sub>1" using 1 chosen_at_is_choosable by fast
      have 10:"safe_at r v\<^sub>2 b\<^sub>2"
      proof -
        obtain a where "a \<in> q\<^sub>2" using 6 by (metis quorum_inter_witness)
        with this assms(1) 4 6 have "safe_at r (the (vote r a b\<^sub>2)) b\<^sub>2"
          by (metis Paxos_axioms Paxos_def option.discI safe_def subsetCE)
        moreover have "the (vote r a b\<^sub>2) = v\<^sub>2" using `a \<in> q\<^sub>2` 4 by force
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
 
(* 
fun p_trans_fun  where
  "p_trans_fun r (Propose c) r' = propose c r r'"
| "p_trans_fun r (FromPrev s) r' = from_prev s r r'"
| "p_trans_fun r (ToNext s) r' = to_next s r r'"
| "p_trans_fun r (Learn s l) r' = learn l s r r'"
| "p_trans_fun r (Init_Acc) r' = init_acc r r'"
| "p_trans_fun r (Accept) r' = accept r r'"

definition p_trans where
  "p_trans \<equiv> { (r,a,r') . p_trans_fun r a r'}"

definition p_ioa where
  "p_ioa \<equiv> \<lparr>ioa.asig = p_asig, start = p_start, trans = p_trans\<rparr>" *)

end 
    
locale PaxosImpl = Paxos +
fixes ballots and rep_num::"'a \<Rightarrow> nat" and div_op::"nat \<Rightarrow> nat \<Rightarrow> nat"
assumes "\<And> a1 a2 . ballots a2 \<inter> ballots a1 = {}"
(*assumes "\<And> a . rep_num a \<in> (0::nat)..(card UNIV::'a set)"*)
begin

fun next_ballot where
  "next_ballot a (hs::nat) = ((div_op hs (card acceptors) + 1) * (card acceptors) + (rep_num a))"

end
  
end
