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

lemma
  assumes "chosen_at r v (b::nat)"
  shows "choosable r v b" using assms
  by (auto simp add:chosen_at_def choosable_def) (smt option.case_eq_if)

lemma safe_at_prec:
  assumes "safe_at r v (b::nat)" and "b2 < b"
  shows "safe_at r v b2"
  using assms by (meson order.strict_trans safe_at_def)

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

lemma
  assumes "safe_at (r::('v, 'acc, nat)p_state) v b" and "(v1::'v) \<noteq> v2" and "b \<noteq> 0"
  shows "\<exists> q \<in> quorums . \<forall> a \<in> q . case ballot r a of None \<Rightarrow> False | Some b2 \<Rightarrow> b2 \<ge> b"
  using assms
  proof(induct b)
    case 0 thus ?case by auto
  next
    case (Suc b)
    assume "b \<noteq> 0"
    obtain q where "q \<in> quorums" and "\<And> a . a \<in> q \<Longrightarrow> case ballot r a of None \<Rightarrow> False | Some b2 \<Rightarrow> b2 \<ge> b"
      using Suc.hyps Suc.prems(2,3)
    by auto (metis (full_types) Suc.hyps Suc.prems(1) \<open>b \<noteq> 0\<close> lessI safe_at_prec)
    assume "case ballot r a of None \<Rightarrow> False | Some b2 \<Rightarrow> b2 = b" if "a \<in> q" for a
    hence "choosable r v b" for v
      by (smt Suc_leI Suc_n_not_le_n \<open>q \<in> quorums\<close> choosable_def option.case_eq_if)
    hence False using Suc.prems(1)
      by (auto simp add:safe_at_def) (metis assms(2) lessI)
    oops
    
lemma
  fixes v b v1 v2 r
  assumes "safe_at (r::('v, 'acc, nat)p_state) v (Suc b)" and "(v1::'v) \<noteq> v2"
  obtains q co where
  "q \<in> quorums" and "\<And> a . a \<in> q \<Longrightarrow> case ballot r a of None \<Rightarrow> False | Some b2 \<Rightarrow> b2 \<ge> Suc b"
  and "case co of None \<Rightarrow> True | Some c \<Rightarrow> (
    c \<le> b 
    \<and> safe_at r v c
    \<and> (\<forall> a \<in> q . (case vote r a c of None \<Rightarrow> True | Some v2 \<Rightarrow> v2 = v))
    \<and> (\<forall> a \<in> q . \<forall> d . (d > c \<and> d \<le> b) \<longrightarrow> vote r a d = None))"
  and "\<And> d a . \<lbrakk>d \<ge> (case co of None \<Rightarrow> (0::nat) | Some c \<Rightarrow> Suc c); d \<le> b; a \<in> q\<rbrakk> \<Longrightarrow> vote r a d = None"
    nitpick[card 'acc=1, card 'l = 1, card 'v=2, show_all, card "'x option"=50,
      card nat = 2, show_all]

lemma safe1:
  assumes "safe (r::('v, 'acc, nat)p_state)"
  and "chosen_at r v1 b1" and "chosen_at r v2 b2"
  and "b1 \<le> b2"
  shows "v1 = v2" using assms
proof (induct b2) print_cases
  case 0 
  from "0.prems"(2-4) show ?case using quorum_vote
  by (auto simp add:chosen_at_def) fast
next
  case (Suc b2)
  { assume "b1 = Suc b2"
    hence ?thesis using Suc.hyps Suc.prems chosen_at_same by metis }
  moreover
  { assume "b1 \<le> b2"
    hence ?thesis sorry }
  ultimately show ?thesis by (metis Suc.prems(4) le_SucE) 
qed

lemma safe:
  assumes "safe (r::('v, 'acc, nat)p_state)"
  and "chosen r v1" and "chosen r v2"
  shows "v1 = v2" 
proof -
  obtain b1 b2 where b1:"chosen_at r v1 b1"
  and b2:"chosen_at r v2 b2" using assms(2,3) 
    by (auto simp add:chosen_def)
  have ?thesis if "b1 \<le> b2" using safe1 assms(1) b1 b2 that by metis
  moreover
  have ?thesis if "b2 \<le> b1" using safe1 assms(1) b1 b2 that by metis
  ultimately show ?thesis by linarith
qed
  
  
  
(* 
lemma 
  assumes "safe_at r (v::'v) (b::nat)" and "v1 \<noteq> (v2::'v)"
  obtains 
    "b = 0"
  | Q where "Q \<in> quorums"
    and "\<And> a . a \<in> Q \<Longrightarrow> ballot r a \<noteq> None" 
proof -
  { assume "b \<noteq> 0"
    { assume "\<And> Q . Q \<in> quorums \<Longrightarrow> (\<And> a . a \<in> Q \<Longrightarrow> ballot r a = None)"
      hence "\<And> v . choosable r v b" using Paxos_axioms by (auto simp add:choosable_def Paxos_def)
      with assms and `b \<noteq> 0` have False apply (auto simp add:safe_at_def choosable_def)  }
    hence "\<exists> Q "
  thus ?thesis using that 
    

lemma 
  assumes "safe_at r v (b::nat)"
  obtains 
    "b = bot"
  | Q where "Q \<in> quorums"
    and "\<And> a . a \<in> Q \<Longrightarrow> ballot r a \<noteq> None \<and> the (ballot r a) \<ge> b" 
proof -
  { assume notbot:"b \<noteq> bot"
    assume "\<And> Q \<in> quorums . \<forall> a \<in> Q . ballot r a \<noteq> None \<and> the (ballot r a) \<ge> b"
    have "\<exists> Q \<in> quorums . \<forall> a \<in> Q . ballot r a \<noteq> None \<and> the (ballot r a) \<ge> b"
    
    }
  
  { assume "b \<noteq> bot"
    hence "\<exists> Q \<in> quorums . \<forall> a \<in> Q . ballot r a \<noteq> None \<and> the (ballot r a) \<ge> b"
      using assms
      apply (induct b)
      subgoal by (simp add:safe_at_def)
      apply (simp add:safe_at_def choosable_def) 
    }
  with that show ?thesis (*by blast*)
qed
  
  
lemma 
  assumes "safe_at r v (b::'b::wellorder_bot)"
  obtains 
    "b = bot"
  | Q where "Q \<in> quorums"
    and "\<And> a . a \<in> Q \<Longrightarrow> ballot r a \<noteq> None \<and> the (ballot r a) \<ge> b"
  (*nitpick[card 'a = 2, card 'acc = 1, card 'b = 4]*)

lemma 
  assumes "well_formed r" and "safe r"
  and "chosen r v1" and "chosen r v2"
  shows "v1 = v2" (*nitpick[card 'a = 2, card 'acc = 3, card 'b = 4]*)
  oops    
 *)
 
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
