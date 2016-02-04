theory Paxos
imports "/home/nano/Documents/IO-Automata/IOA"  "~~/src/HOL/Eisbach/Eisbach_Tools" 
  "/home/nano/Documents/IO-Automata/Simulations" "~~/src/HOL/Library/Monad_Syntax"
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

lemma "v \<in> vals \<Longrightarrow> safe_at r v (bot::'b::wellorder_bot)"
by (auto simp add:safe_at_def)

lemma
  assumes "chosen_at r v (b::nat)"
  shows "choosable r v b" using assms
  by (auto simp add:chosen_at_def choosable_def) (smt option.case_eq_if) 

lemma safe_at_prec:
  assumes "safe_at r v (b::nat)" and "b2 < b"
  shows "safe_at r v b2"
  using assms by (meson order.strict_trans safe_at_def)
  
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
