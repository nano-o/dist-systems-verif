theory Paxos
imports "/home/nano/Documents/IO-Automata/IOA"  "~~/src/HOL/Eisbach/Eisbach_Tools"
  "/home/nano/Documents/IO-Automata/Simulations" "~~/src/HOL/Library/Monad_Syntax"
  "~~/src/HOL/Library/FSet"
  Transfer
begin

datatype ('v,'acc,'l, 'b::linorder) p_action =
  Propose 'v
| Learn 'v 'l
| Vote 'v 'acc
| JoinBallot 'b 'acc

record ('v,'acc, 'b::linorder) p_state =
  propCmd :: "'v fset"
  ballot :: "'acc \<Rightarrow> 'b option"
  vote :: "'acc \<Rightarrow> 'b \<Rightarrow> 'v option"

fun less_eq_o where 
  "less_eq_o None _ = True"
| "less_eq_o (Some x) None = False"
| "less_eq_o (Some x) (Some y) = (x \<le> y)"

fun less_o where
  "less_o None None = False" 
| "less_o None _ = True"
| "less_o (Some x) None = False"
| "less_o (Some x) (Some y) = (x < y)"

subsection {* Transfer betwee nat option and nat *}

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
  and max::"('b::linorder) set \<Rightarrow> 'b"
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

definition p_asig where
  "p_asig \<equiv> 
    \<lparr> inputs = { a . \<exists> c . a = Propose c  },
      outputs = { a . \<exists> v . \<exists> l . l |\<in>| learners \<and> a = Learn v l },
      internals = {a . \<exists> v . \<exists> acc . acc |\<in>| acceptors \<and> a = Vote v acc} 
        \<union> {a . \<exists> b . \<exists> acc . acc |\<in>| acceptors \<and> a = JoinBallot b acc}\<rparr>"

definition p_start where
  "p_start \<equiv> {\<lparr>propCmd = {||}, ballot = (\<lambda> a . None), vote = (\<lambda> a b . None)\<rparr>}"

definition propose where
  "propose c r r' \<equiv> (r' = r\<lparr>propCmd := (propCmd r) |\<union>| {|c|}\<rparr>)"

definition conservative where
  "conservative r b \<equiv> \<forall> a1 . \<forall> a2 . a1 |\<in>| acceptors \<and> a2 |\<in>| acceptors \<longrightarrow> (
    let v1 = (vote r) a1 b; v2 = (vote r) a2 b in 
      (v1 \<noteq> None \<and> v2 \<noteq> None) \<longrightarrow> v1 = v2)"

definition conservative_array where
  "conservative_array r \<equiv> \<forall> b . conservative r b"
  
text {* Here the max is the one from Lattices_Big *}
definition max_acc_voted_round where
  "max_acc_voted_round r a bound \<equiv> Max {(vote r) a b | b . b \<le> bound}"
  
definition max_voted_round where
  "max_voted_round r q bound \<equiv> Max {max_acc_voted_round r a bound | a . a |\<in>| q}"
 
definition max_vote where
  "max_vote r q bound \<equiv>
    case max_voted_round r q bound of
      None \<Rightarrow> None
    | Some b \<Rightarrow> 
        let max_voter = (SOME a . a |\<in>| q \<and> max_acc_voted_round r a bound = Some b)
        in (vote r) max_voter b"
    
definition proved_safe_at where
  "proved_safe_at r Q b v \<equiv>
    case (max_vote r Q (b-1)) of
      None \<Rightarrow> True
    | Some v' \<Rightarrow> v = v'"

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
  "well_formed r \<equiv> \<forall> a . a |\<in>| acceptors \<longrightarrow> 
    (\<forall> b . (ballot r) a < Some b  \<longrightarrow> (vote r) a b = None)"

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
  assumes "safe r" and "q |\<in>| quorums"
  and "\<And> a . a |\<in>| q \<Longrightarrow> case ballot s a of None \<Rightarrow> False | Some b\<^sub>a \<Rightarrow> b\<^sub>a \<ge> i"
  and "proved_safe_at s q i v"
  shows "safe_at s v i"
proof -
  consider k a 
    where "a |\<in>| q" and "\<And> a\<^sub>2 . a\<^sub>2 |\<in>| q \<Longrightarrow> case ballot s a\<^sub>2 of None \<Rightarrow> False | Some b \<Rightarrow> b \<le> k"
    and "vote s a (the (ballot s a)) = Some v"
  | "\<And>a . a |\<in>| q \<Longrightarrow> ballot s a = None"
  oops
(*
  have "v = w" if "choosable s w j" and "j < i" for w j 
  proof -
    from that(1)
    obtain q\<^sub>w where "q\<^sub>w \<in> quorums"
      and "\<And> a . \<lbrakk>a \<in> q\<^sub>w; case ballot s a of None \<Rightarrow> False | Some b \<Rightarrow> b > j\<rbrakk> \<Longrightarrow> vote s a j = Some w"
      by (auto simp add:choosable_def)  (smt option.case_eq_if)
  qed
  thus ?thesis by (auto simp add:safe_at_def)
qed *)

lemma 
  assumes "proved_safe_at r Q b v"
  shows "safe_at r b v" oops
  
section {* Paxos IOA *}

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

end
