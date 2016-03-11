theory Paxos
imports "/home/nano/Documents/IO-Automata/IOA_Automation"  "~~/src/HOL/Eisbach/Eisbach_Tools"
  "/home/nano/Documents/IO-Automata/Simulations" "~~/src/HOL/Library/Monad_Syntax"
  "~~/src/HOL/Library/FSet"
  LinorderOption
begin

section {* State and actions of the Paxos algorithm *}

datatype ('v,'acc,'l) p_action =
  Propose 'v
| Learn 'v 'l
| Vote 'acc
| JoinBallot nat 'acc
| StartBallot nat

(* Note: using 'b::linorder confuses the record package. *)
record ('v, 'acc, 'b) p_state =
  propCmd :: "'v fset"
  ballot :: "'acc \<Rightarrow> 'b option"
  vote :: "'acc \<Rightarrow> 'b \<Rightarrow> 'v option"
  suggestion :: "'b \<Rightarrow> 'v option"
    -- {* The suggestion of the leader of round b *}

section {* Properties of the state *}

locale Paxos = IOA +
  fixes acceptors::"'acc fset" and learners::"'l fset" and quorums::"'acc fset fset"
  assumes "acceptors \<noteq> {||}"
    and "learners \<noteq> {||}"
    and "\<And> q1 q2 . \<lbrakk>q1 |\<in>| quorums; q2 |\<in>| quorums\<rbrakk> \<Longrightarrow> q1 |\<inter>| q2 \<noteq> {||}"
    and "\<And> q . q |\<in>| quorums \<Longrightarrow> q |\<subseteq>| acceptors"
    and "quorums \<noteq> {||}"
begin

text {* If Nitpick can find a model then the assumptions are not contradictory *}
lemma False nitpick oops

text {* A state is conservative when for every ballot b: if a1 and a2 have voted in b, 
  then their vote is the same *}

definition conservative where
  "conservative r b \<equiv> \<forall> a1 . \<forall> a2 . a1 |\<in>| acceptors \<and> a2 |\<in>| acceptors \<longrightarrow> (
    let v1 = (vote r) a1 b; v2 = (vote r) a2 b in 
      (v1 \<noteq> None \<and> v2 \<noteq> None) \<longrightarrow> v1 = v2)"

definition conservative_array where
  "conservative_array r \<equiv> \<forall> b . conservative r b"

text {* Here the max is the one from Lattices_Big *}

definition max_voted_round where
  "max_voted_round r a bound \<equiv> Max {b . vote r a b \<noteq> None \<and> b \<le> bound}"
  
definition max_voted_round_q where
  "max_voted_round_q r q bound \<equiv> 
    if \<exists> b a . a |\<in>| q \<and> b \<le> bound \<and> vote r a b \<noteq> None
    then Some (Max {b . \<exists> a . a |\<in>| q \<and> b \<le> bound \<and> vote r a b \<noteq> None})
    else None"

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
  and "max_voted_round_q r q bound = None \<or> b > the (max_voted_round_q r q bound)"
  shows "vote r a b = None"
proof (cases "max_voted_round_q r q bound")
case None 
  thus ?thesis using assms(1,2)
  by (auto simp add:max_voted_round_q_def split:split_if_asm)
next
  case (Some b\<^sub>m\<^sub>a\<^sub>x)
  with this obtain a2 b2 v where "a2 |\<in>| q \<and> b2 \<le> bound \<and> vote r a2 b2 = Some v"
  by (auto simp add:max_voted_round_q_def split:split_if_asm)
  hence "{b . \<exists> a . a |\<in>| q \<and> b \<le> bound \<and> vote r a b \<noteq> None} \<noteq> {}" by auto
  with this obtain b2 a2 where "a2 |\<in>| q \<and> b2 \<le> bound \<and> vote r a2 b2 \<noteq> None"
    by auto
  moreover note finite_voted_bals
  moreover have "b > Max {b . \<exists> a . a |\<in>| q \<and> b \<le> bound \<and> vote r a b \<noteq> None}" using Some assms(3)
    by (auto simp add:max_voted_round_q_def split:split_if_asm)
  ultimately
  show ?thesis by (metis (mono_tags, lifting) Max.coboundedI assms(1,2) leD mem_Collect_eq) 
qed

lemma max_voted_round_some :
  assumes "max_voted_round_q r q (bound::nat) = Some (b::nat)"
  obtains a where "a |\<in>| q" and "vote r a b \<noteq> None" and "b \<le> bound"
proof -
  from assms have "b = Max {b . \<exists> a . a |\<in>| q \<and> b \<le> bound \<and> vote r a b \<noteq> None}"
    by (auto simp add:max_voted_round_q_def split:split_if_asm)
  moreover note finite_voted_bals
  moreover obtain a2 b2 where "a2 |\<in>| q \<and> b2 \<le> bound \<and> vote r a2 b2 \<noteq> None"
    using assms by (auto simp add:max_voted_round_q_def) (metis option.distinct(1))
  ultimately show ?thesis using that
  by (smt Max_in empty_iff finite_nat_set_iff_bounded_le mem_Collect_eq) 
qed
 
definition max_vote where
  "max_vote r q bound \<equiv>
    case max_voted_round_q r q bound of
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
  from assms obtain b\<^sub>m\<^sub>a\<^sub>x where 0:"max_voted_round_q r q bound = Some (b\<^sub>m\<^sub>a\<^sub>x::nat)"
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

lemma "safe_at r v (bot::nat)"
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

text {* The main lemma *}

lemma proved_safe_is_safe:
  assumes "safe s" and "q |\<in>| quorums"
  and "\<And> a . a |\<in>| q \<Longrightarrow> ballot s a \<ge> Some i"
  and "proved_safe_at s q i v" and "conservative_array s"
  shows "safe_at s v (i::nat)"
proof (cases "i = 0")
  case True thus ?thesis
    by (metis not_less0 safe_at_def) 
next
  case False
  consider 
    (a) k a
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
      have 9:"vote s a j = Some v"
        by (metis (no_types, hide_lams) "1" "4" "5" "6" assms(3) less_def less_o.simps(4) not_le order_trans) 
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
        have 8:"vote s a2 j = Some v'"
          by (metis (mono_tags, lifting) "4" "5" "6" assms(3) leD leI less_eq_def less_eq_o.simps(3) order_trans that(2)) 
        show ?thesis using a(4) 5 that(2) 8 cc by (metis option.distinct(1))
      next
        case bb (* Here we probably need the fact that the array is conservative: *)
        have 1:"vote s a k = Some v" if "a |\<in>| acceptors" and " vote s a k \<noteq> None"  for a using that assms(5) 
          by (auto simp add:conservative_array_def conservative_def)
            (metis (no_types, hide_lams) Paxos_axioms Paxos_def a(1) a(2) assms(2) option.inject order.not_eq_order_implies_strict pfsubsetD)  
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
          by (metis "1" "4" "5" "6" "7" "8" assms(3) bb leD less_eq_def less_eq_o.simps(3) option.discI order.not_eq_order_implies_strict that(2))
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
  "join_ballot a b s s' \<equiv> Some b > (ballot s a) \<and> s' = s\<lparr>ballot := (ballot s)(a := Some b)\<rparr>"

definition start_ballot where
  "start_ballot b s s' \<equiv> suggestion s b = None \<and>
    (\<exists> q v . q |\<in>| quorums \<and> proved_safe_at s q b v \<and> (\<forall> a . a |\<in>| q \<longrightarrow> ballot s a \<ge> Some b)
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
| "p_trans_fun r (StartBallot b) r' = start_ballot b r r'"

definition p_trans where
  "p_trans \<equiv> { (r,a,r') . p_trans_fun r a r'}"

definition p_ioa where
  "p_ioa \<equiv> \<lparr>ioa.asig = p_asig, start = p_start, trans = p_trans\<rparr>"

end 

section {* Correctness proof *}

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
  learn_def[simp] start_ballot_def[simp]

definition inv1 where
  "inv1 s \<equiv> \<forall> a b . a |\<in>| acceptors \<and> vote s a b \<noteq> None 
    \<longrightarrow> vote s a b = suggestion s b"
declare inv1_def[inv_proofs_defs]

declare the_ioa_def[inv_proofs_defs]

lemma inv1:"invariant the_ioa inv1"
apply try_solve_inv2
apply (smt fun_upd_apply p_state.ext_inject p_state.surjective p_state.update_convs(3))
apply (metis (no_types, lifting) map_upd_Some_unfold option.discI p_state.ext_inject p_state.surjective p_state.update_convs(4))
done

(* Does not seem needed. Is it? *)
declare well_formed_def[inv_proofs_defs]
lemma well_formed_inductive:
  "invariant the_ioa well_formed"
apply try_solve_inv2
apply auto
apply (smt fun_upd_apply gt_not_none neq_iff option.collapse option.sel p_state.ext_inject p_state.surjective p_state.update_convs(3))
done
(*declare well_formed_inductive[invs]*)

declare conservative_array_def[inv_proofs_defs]
lemma conservative_inductive:
  "invariant the_ioa conservative_array"
apply (try_solve_inv2 inv_proofs_defs:inv_proofs_defs conservative_def invs:invs inv1)
apply metis
apply metis
done
declare conservative_inductive[invs]

lemma safe_mono:
  assumes "safe_at s v b" and "s \<midarrow>a\<midarrow>the_ioa\<longrightarrow> t"
  shows "safe_at t v b" using assms
apply (cases a)
        apply (auto simp add:inv_proofs_defs safe_at_def choosable_def)[2] (* propose, learn *)
    defer (* join_ballot *)
    apply (simp add:inv_proofs_defs safe_at_def choosable_def)[1]
    apply (metis less_def order.strict_trans) 
  defer (* vote *)
  apply (simp add:inv_proofs_defs safe_at_def choosable_def)
  apply (smt fun_upd_apply neq_iff option.sel p_state.select_convs(2) p_state.select_convs(3) p_state.surjective p_state.update_convs(3))
  (* That was amazing, Sledgehammer found it before I had time to think about why it would be true... *)
apply (simp add:inv_proofs_defs safe_at_def choosable_def) (* start_ballot *)
apply (metis p_state.ext_inject p_state.surjective p_state.update_convs(4))
done

definition inv2 where
  "inv2 s \<equiv> safe s \<and> (\<forall> b . case suggestion s b of None \<Rightarrow> True | Some v \<Rightarrow> safe_at s v b)"
declare inv2_def[inv_proofs_defs]

lemma inv2:
  "invariant the_ioa inv2"
apply(rule invariantI)
    apply (force simp add:inv_proofs_defs safe_def)
  apply instantiate_invs_2
  apply (case_tac a)
          subgoal premises prems for s t a v
          proof -
            from prems(2,5) have 1:"propose v s t"
              by(auto simp add:inv_proofs_defs) 
            hence 2:"\<And> b . suggestion s b = suggestion t b" 
              by(auto simp add:inv_proofs_defs)
            have 3:"safe t" using 1 prems(1) 
              by (auto simp add:inv_proofs_defs safe_def safe_at_def choosable_def) 
            from 1 2 3 safe_mono show ?thesis 
              by (auto simp add:inv2_def)
                (metis inv2_def option.case_eq_if prems(1) prems(2))
          qed
        subgoal by (auto simp add:inv_proofs_defs) (* learn *)
      subgoal premises prems for s t act a
      proof - 
        from prems(2,5) have 1:"do_vote a s t"
          by(auto simp add:inv_proofs_defs)
        hence 2:"\<And> b . suggestion s b = suggestion t b" 
          by (auto simp add:inv_proofs_defs)
            (metis p_state.ext_inject p_state.surjective p_state.update_convs(3))
        have 3:"safe t" using prems(1) 1 apply(auto simp add:inv2_def safe_def)
        proof - (* Auto-generated *)
          fix b :: nat and aa :: 'a
          assume a1: "let bo = ballot s a; b = the bo in (\<exists>y. bo = Some y) \<and> vote s a b = None \<and> t = s \<lparr>vote := (vote s)(a := (vote s a)(b := suggestion s b))\<rparr>"
          assume a2: "\<forall>b a. a |\<in>| acceptors \<longrightarrow> (let vote = vote s a b in (\<exists>y. vote = Some y) \<longrightarrow> safe_at s (the vote) b)"
          assume a3: "\<forall>b. case suggestion s b of None \<Rightarrow> True | Some v \<Rightarrow> safe_at s v b"
          assume a4: "aa |\<in>| acceptors"
          { fix cc :: 'c
            have ff1: "\<forall>p. \<exists>f fa fb fc u. p = \<lparr>propCmd = f::'c fset, ballot = fa::'a \<Rightarrow> nat option, vote = fb, suggestion = fc, \<dots> = u::unit\<rparr>"
              by (metis p_state.cases_scheme)
            obtain nn :: nat where
              ff2: "ballot s a = Some nn \<and> vote s a (the (ballot s a)) = None \<and> t = s \<lparr>vote := (vote s) (a := (vote s a) (the (ballot s a) := suggestion s (the (ballot s a))))\<rparr>"
              using a1 by metis
            then have ff3: "vote t = (vote s) (a := (vote s a)(the (Some nn) := suggestion s (the (Some nn))))"
              using ff1 by (metis p_state.select_convs(3) p_state.update_convs(3))
            then have ff4: "vote t a = (vote s a)(the (Some nn) := suggestion s (the (Some nn)))"
              by (metis fun_upd_apply)
            then have ff5: "vote t a (the (Some nn)) = suggestion s (the (Some nn))"
              by (metis fun_upd_apply)
            have ff6: "\<And>aa. vote t aa = vote s aa \<or> a = aa"
              using ff3 by (metis fun_upd_apply)
            have "\<And>n. vote t a n = vote s a n \<or> the (Some nn) = n"
              using ff4 by (metis fun_upd_apply)
            then have "vote t aa b \<noteq> Some cc \<or> safe_at t (the (vote t aa b)) b"
              using ff6 ff5 ff2 a4 a3 a2 by (metis option.case_eq_if prems(2) safe_mono) }
          then show "let z = vote t aa b in (\<exists>c. z = Some c) \<longrightarrow> safe_at t (the z) b"
            by metis
        qed
        from 1 2 3 safe_mono show ?thesis 
          by (auto simp add:inv2_def)
            (metis inv2_def option.case_eq_if prems(1) prems(2))
      qed
    subgoal premises prems for s t act b a
    proof -
      from prems(2,5) have 1:"join_ballot a b s t"
        by(auto simp add:inv_proofs_defs)
      hence 2:"\<And> b . suggestion s b = suggestion t b" 
        by (auto simp add:inv_proofs_defs)
      have 3:"safe t" using prems(1) 1 by (auto simp add:inv2_def safe_def) (metis prems(2) safe_mono)
      from 1 2 3 safe_mono show ?thesis 
        by (auto simp add:inv2_def)
          (metis inv2_def option.case_eq_if prems(1) prems(2))
    qed
  subgoal premises prems for s t act b
  proof -
    from prems(2,5) have 1:"start_ballot b s t"
      by(auto simp add:inv_proofs_defs)
    have 3:"safe t" using prems(1) 1 by (auto simp add:inv2_def safe_def) (metis prems(2) safe_mono)
    from 1 obtain q v where 2:"q |\<in>| quorums" and 4:"proved_safe_at s q b v" 
      and 5:"t = s\<lparr>suggestion := suggestion s(b \<mapsto> v)\<rparr>" and 6:"\<And> a . a |\<in>| q \<Longrightarrow> ballot s a \<ge> Some b"
      by auto
    have 2:"\<And> b . case suggestion t b of None \<Rightarrow> True | Some v \<Rightarrow> safe_at t v b"
      using 1 2 4 5 6 prems(1,2,3) apply(simp add:inv2_def)
        by (metis option.case_eq_if proved_safe_is_safe safe_mono)
    from 2 3 show ?thesis by (auto simp add:inv2_def)
  qed
done
declare inv2[invs]

lemma safe_inv:
  "invariant the_ioa safe"
apply(rule invariantI)
    apply (force simp add:safe_def inv_proofs_defs)
  apply instantiate_invs_2
  apply (case_tac a)
          apply (force simp add:safe_def inv_proofs_defs safe_at_def choosable_def)
        apply (force simp add:safe_def inv_proofs_defs safe_at_def choosable_def)
      apply (auto simp add:is_trans_def the_ioa_def p_ioa_def p_trans_def inv2_def)
done
declare safe_inv[invs]

definition agreement where 
  "agreement s \<equiv> \<forall> v w . chosen s v \<and> chosen s w \<longrightarrow> v = w"
lemma agreement:"invariant the_ioa agreement"
apply(rule invariantI)
    apply(auto simp add: inv_proofs_defs agreement_def chosen_def chosen_at_def)[1]
    apply (metis fempty_iff quorum_inter_witness)
  apply instantiate_invs_2
  apply (insert safe_is_safe)
  apply (force simp add:agreement_def)
done

end

end