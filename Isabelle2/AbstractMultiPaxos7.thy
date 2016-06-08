theory AbstractMultiPaxos7
imports Quorums "../../IO-Automata/Simulations" "../../IO-Automata/IOA_Automation" BallotArrays3
begin

section {* Definition of the Abstract MultiPaxos I/O-automaton *}

subsection {* State and actions *}

text {* The actions (labels on transitions) of the I/O-automaton *}

datatype ('v,'a,'l) amp_action =
  Propose 'v
| Learn nat 'v 'l
| Vote 'a "'a set" nat 'v
  -- {* an acceptor votes in a ballot according to a quorum *}
| JoinBallot 'a nat

text {* The states of the I/O-automaton *}

record ('v,'a) amp_state =
  propCmd :: "'v set"
  ballot :: "'a \<Rightarrow> nat option"
  vote :: "nat \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> 'v option"

locale amp_ioa = IOA + 
  fixes acceptors::"'a set" and quorums::"'a set set"
  fixes learners::"'l set"
begin

definition amp_asig where
  "amp_asig \<equiv>
    \<lparr> inputs = { Propose c | c . True},
      outputs = { Learn i v l | i v l . l \<in> learners},
      internals = {Vote a i q b | a i b q . a \<in> acceptors} \<union> {JoinBallot a b | a b . a \<in> acceptors}\<rparr>"

definition amp_start where
  -- {* The initial state *}
  "amp_start \<equiv> {\<lparr>propCmd = {}, ballot = (\<lambda> a . None), vote = (\<lambda> i a b . None) \<rparr>}"

subsection {* The transitions *}

definition propose where
  "propose c r r' \<equiv> (r' = r\<lparr>propCmd := (propCmd r) \<union> {c}\<rparr>)"

definition join_ballot where
  "join_ballot a b s s' \<equiv> 
    a \<in> acceptors \<and> Some b > (ballot s a) \<and> s' = s\<lparr>ballot := (ballot s)(a := Some b)\<rparr>"

abbreviation proved_safe_at where 
  -- {* v is proved safe in instance i at ballot b by quorum q *}
  "proved_safe_at s i q b v \<equiv> ballot_array.proved_safe_at  (vote s i) q b v"

abbreviation conservative_at where 
  "conservative_at s i \<equiv> ballot_array.conservative_array (vote s i) acceptors"

definition do_vote where
  "do_vote a i q v s s' \<equiv> a \<in> acceptors \<and> (case ballot s a of None \<Rightarrow> False 
    | Some b \<Rightarrow>
        proved_safe_at s i q b v
        \<and> q \<in> quorums
        \<and> (\<forall> a2 . a2 \<in> q \<longrightarrow> ballot s a2 \<ge> Some b)
        \<and> conservative_at s' i
        \<and> vote s i a b = None 
        \<and> s' = s\<lparr>vote := (vote s)(i := (vote s i)(a := (vote s i a)(b := Some v)))\<rparr>)"

abbreviation chosen where 
  "chosen s i v \<equiv> ballot_array.chosen (vote s i) quorums v"

definition learn where
  "learn l i v s s' \<equiv> chosen s i v \<and> s = s'"

(* Here it's better to have all existentially quantified parameters in the action itself, in
  order to avoid annoying quantifiers. *)
fun amp_trans_rel  where
  "amp_trans_rel r (Propose c) r' = propose c r r'"
| "amp_trans_rel r (JoinBallot a b) r' = join_ballot a b r r'"
| "amp_trans_rel r (Vote a q i v) r' = do_vote a i q v r r'"
| "amp_trans_rel r (Learn i v l) r' = learn l i v r r'"

definition amp_trans where
  "amp_trans \<equiv> { (r,a,r') . amp_trans_rel r a r'}"

subsection {* The I/O-automaton *}

definition amp_ioa where
  "amp_ioa \<equiv> \<lparr>ioa.asig = amp_asig, start = amp_start, trans = amp_trans\<rparr>"

end

section {* The agreement proof *}

locale amp_proof = IOA + quorums acceptors quorums + 
    amp_ioa acceptors quorums learners for acceptors :: "'a set" 
    and quorums and learners :: "'l set" +
  fixes the_ioa :: "(('v,'a)amp_state, ('v,'a,'l)amp_action) ioa"
  defines "the_ioa \<equiv> amp_ioa"
begin

subsection {* Automation setup and a few lemmas *}

lemmas amp_ioa_defs =  
   is_trans_def actions_def amp_trans_def amp_start_def
   externals_def amp_ioa_def amp_asig_def

declare amp_ioa_defs[inv_proofs_defs]
declare the_ioa_def[inv_proofs_defs]

declare propose_def[simp] join_ballot_def[simp] do_vote_def[simp]
  learn_def[simp]

lemma vote_one_inst_only:
  assumes "do_vote a i q v s s'" and "i \<noteq> j"
  shows "vote s j a = vote s' j a "
using assms
apply auto
    apply (case_tac "ballot s a")
apply auto
done

lemma vote_ballot_unch:
  assumes "do_vote a i q v s s'"
  shows "ballot s = ballot s'"
using assms by (auto split add:option.split_asm)


subsection {* @{term conservative_array}  is an inductive invariant*}

declare ballot_array.conservative_array_def[inv_proofs_defs]
abbreviation conservative_array where 
"conservative_array s \<equiv>  \<forall> i . conservative_at s i"

lemma conservative_inductive:
  "invariant the_ioa conservative_array"
apply (try_solve_inv2 inv_proofs_defs:inv_proofs_defs invs:invs)
    apply (force simp add:ballot_array.conservative_def)
  apply (case_tac a)
        apply (force simp add:inv_proofs_defs)
      apply (force simp add:inv_proofs_defs)
    defer
    apply (force simp add:inv_proofs_defs)
  apply (match premises in R[thin]:"reachable ?ioa ?s" \<Rightarrow> \<open>-\<close>)
  subgoal premises prems for s t act a q i v using prems
  proof -
    from prems(2,3)
    obtain b where 1:"a \<in> acceptors" and 2:"ballot s a = Some b" 
    and 3:"proved_safe_at s i q b v"
    and 6:"ballot_array.conservative_array  (vote t i) acceptors"
    and 4:"vote s i a b = None" and 5:"t = s\<lparr>vote := (vote s)(i := (vote s i)(a := (vote s i a)(b := Some v)))\<rparr>"
        apply (case_tac "ballot s a")
          by (auto simp add:inv_proofs_defs)
    show "conservative_array t"
    proof (auto simp add: ballot_array.conservative_array_def)
      fix j b
      have "ballot_array.conservative (vote t j) acceptors b" if "i \<noteq> j"
      proof -
        have "ballot_array.conservative (vote s j) acceptors b" using prems(1)
          by (auto simp add: ballot_array.conservative_array_def ballot_array.conservative_def)
        thus ?thesis using that 5 by (auto simp add: ballot_array.conservative_def)
      qed
      moreover
      have "ballot_array.conservative (vote t j) acceptors b" if "i = j"
        using 6 that by auto (metis ballot_array.conservative_array_def)
      ultimately show "ballot_array.conservative (vote t j) acceptors b" by auto
    qed
  qed 
done
declare conservative_inductive[invs]


subsection {* @{term safe}  is an inductive invariant*}

abbreviation safe_at where "safe_at s i \<equiv> ballot_array.safe_at (ballot s) (vote s i) quorums"

lemma safe_mono:
  -- {* @{term safe_at} is monotonic *}
  assumes "safe_at s i v b" and "s \<midarrow>a\<midarrow>the_ioa\<longrightarrow> t"
  shows "safe_at t i v b" using assms
apply (cases a)
         (* propose, learn *)
        apply (auto simp add:inv_proofs_defs ballot_array.safe_at_def ballot_array.choosable_def)[2]
    defer 
    (* join_ballot *)
    apply (simp add:inv_proofs_defs ballot_array.safe_at_def ballot_array.choosable_def)[1]
    apply (metis less_def order.strict_trans)
  (* vote *)
  apply (simp add:inv_proofs_defs ballot_array.safe_at_def ballot_array.choosable_def split add:option.split_asm)
  apply (metis neq_iff)
done

abbreviation safe where "safe s \<equiv> \<forall> i . ballot_array.safe (ballot s) (vote s i) quorums acceptors"

lemma safe_inv:
  "invariant the_ioa safe"
apply(rule invariantI)
    apply (force simp add:ballot_array.safe_def inv_proofs_defs)
  apply instantiate_invs_2
  apply (case_tac a)
        (* propose *)
        apply (force simp add:ballot_array.safe_def inv_proofs_defs ballot_array.safe_at_def ballot_array.choosable_def)
      (* learn *)
      apply (force simp add:ballot_array.safe_def inv_proofs_defs ballot_array.safe_at_def ballot_array.choosable_def)
    (* vote *)
    subgoal premises prems for s t act a q i v
    proof (auto simp add:ballot_array.safe_def Let_def split add:option.split)
      fix j b a\<^sub>2 v\<^sub>2
      assume 1:"a\<^sub>2 \<in> acceptors" and 2:"vote t j a\<^sub>2 b = Some v\<^sub>2"
      have l:"safe_at t j v\<^sub>2 b" if  "vote s j a\<^sub>2 b = vote t j a\<^sub>2 b"
      proof -
        have "safe_at s j v\<^sub>2 b" using that 1 2 prems(1) by (simp add:ballot_array.safe_def split add:option.split_asm)
        thus ?thesis using prems(2) safe_mono by blast
      qed
      show "safe_at t j v\<^sub>2 b"
      proof (cases "i = j \<and> a\<^sub>2 = a")
        case False
        have "vote s j a\<^sub>2 b = vote t j a\<^sub>2 b" using False prems(2,5) vote_one_inst_only
          by (auto simp add:is_trans_def the_ioa_def amp_ioa_def amp_trans_def split add:option.split_asm)
        with l show ?thesis by auto
      next
        case True
        have 6:"do_vote a\<^sub>2 j q v s t" using prems(2,5) 1 True by (auto simp add:inv_proofs_defs)
        with this obtain b\<^sub>2 where 3:"ballot s a\<^sub>2 = Some b\<^sub>2" and 4:"proved_safe_at s j q b\<^sub>2 v"
        and 5:"t = s\<lparr>vote := (vote s)(j := (vote s j)(a\<^sub>2 := (vote s j a\<^sub>2)(b\<^sub>2 := Some v)))\<rparr>"
        and 7:"\<And> a2 . a2 \<in> q \<Longrightarrow> ballot s a2 \<ge> Some b\<^sub>2" and 8:"q \<in> quorums"
          by (auto split add:option.split_asm)
        have ?thesis if "b \<noteq> b\<^sub>2"
        proof -
          have "vote s j a\<^sub>2 b = vote t j a\<^sub>2 b" using 5
            by (smt amp_state.ext_inject amp_state.surjective amp_state.update_convs(3) fun_upd_apply that) 
          with l show ?thesis by auto
        qed
        moreover have ?thesis if "b = b\<^sub>2"
        proof -
          have "v = v\<^sub>2" using that True
            by (smt "2" "5" amp_state.ext_inject amp_state.surjective amp_state.update_convs(3) fun_upd_apply map_upd_Some_unfold)
          hence 9:"vote t j a\<^sub>2 b = Some v\<^sub>2" using 5 that by force
          hence "safe_at s j v\<^sub>2 b\<^sub>2" 
            using ballot_array_props.proved_safe_is_safe[of quorums acceptors "ballot s" "(vote s j)" q b\<^sub>2 v] 4 3 7 8 prems(1,3) that `v = v\<^sub>2`
            by auto (metis ballot_array_props_def quorums_axioms)
          with safe_mono prems(2) that True show ?thesis by blast
        qed
        ultimately show ?thesis by auto
      qed
    qed
  (* join_ballot *)
  subgoal premises prems for s t act a b
  proof (auto simp add:ballot_array.safe_def split add:option.split)
    fix i b\<^sub>2 a\<^sub>2 v
    assume "vote t i a\<^sub>2 b\<^sub>2 = Some v" and "a\<^sub>2 \<in> acceptors"
    note 1 = this
    have 2:"vote t i a\<^sub>2 b\<^sub>2 = vote s i a\<^sub>2 b\<^sub>2" using prems(2,5) by (auto simp add:inv_proofs_defs)
    hence 3:"safe_at s i v b\<^sub>2" using 1 prems(1)
      by (metis ballot_array.safe_def option.simps(5)) 
    with safe_mono prems(2,5)
    show "safe_at t i v b\<^sub>2" apply (auto simp add:inv_proofs_defs)
      by (metis amp_proof.safe_mono amp_proof_axioms amp_state.select_convs(3) amp_state.simps(2) amp_state.surjective amp_state.update_convs(2) prems(2) the_ioa_def) 
  qed
done
declare safe_inv[invs]

subsection {* Finally, the proof that agreement holds. *}

definition agreement where 
  "agreement s \<equiv> \<forall> v w i . chosen s i v \<and> chosen s i w \<longrightarrow> v = w"

lemma agreement:"invariant the_ioa agreement"
apply(rule invariantI)
    apply(auto simp add: inv_proofs_defs agreement_def ballot_array.chosen_def ballot_array.chosen_at_def)[1]
    apply (metis empty_iff quorum_inter_witness)
  apply instantiate_invs_2
  apply (meson agreement_def ballot_array_props.intro ballot_array_props.safe_is_safe quorums_axioms)
done

end

end