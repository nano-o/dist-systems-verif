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

lemma "finite { y . \<exists> x . x |\<in>| (X::'a fset) \<and> y = E x}" oops

lemma
  assumes "q |\<in>| quorums" and "max_voted_round r q bound = Some (b::nat)"
  obtains a where "a |\<in>| q \<and> max_acc_voted_round r a bound = Some b"
proof -
  have 1:"q \<noteq> {||}" using assms(1)
    by (metis Paxos_axioms Paxos_def finter_fempty_left)
  from 1 have 2:"{max_acc_voted_round r a bound | a . a |\<in>| q} \<noteq> {}"
    by (metis (mono_tags, lifting) Collect_empty_eq all_not_fin_conv) 
  have 3:"finite {max_acc_voted_round r a bound | a . a |\<in>| q}"
  proof -
    have "finite q" 
  with assms(2) obtain x where "x \<in> {max_acc_voted_round r a bound | a . a |\<in>| q}"
    and "x = Max {max_acc_voted_round r a bound | a . a |\<in>| q}"
  apply (auto simp add:max_voted_round_def) oops

definition max_vote where
  "max_vote r q bound \<equiv>
    case max_voted_round r q bound of
      None \<Rightarrow> None
    | Some b \<Rightarrow> 
        let max_voter = (SOME a . a |\<in>| q \<and> max_acc_voted_round r a bound = Some b)
        in (vote r) max_voter b"
    
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
  and "\<And> a . a |\<in>| q \<Longrightarrow> ballot s a \<ge> Some i"
  and "proved_safe_at s q i v" and "i \<noteq> 0"
  shows "safe_at s v i"
proof -
  consider k a
    where "a |\<in>| q" and "vote s a k = Some v" and "\<And> a\<^sub>2 . a\<^sub>2 |\<in>| q \<Longrightarrow> ballot s a\<^sub>2 \<le> Some k"
    and "k < i"
  | "\<And>a . a |\<in>| q \<Longrightarrow> ballot s a = None"
  using assms(4,5)
  apply (auto simp add:proved_safe_at_def)
  apply (cases i)
  apply (auto simp add:max_vote_def)
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