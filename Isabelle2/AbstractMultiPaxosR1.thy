theory AbstractMultiPaxosR1
imports  IOA BallotArrays DistributedSafeAt Paxos_Sig
begin

text {*
1) Acceptors vote for a suggestion, and leaders use the distributed implementation of the safe-at computation.
2) Explicit 1b messages.
3) Explicit learning.
4) Catch-up.
5) Localizing suggestions (the leader function).
6) Explicit leadership acquisition.
*}

record ('v,'a,'l) ampr1_state =
  propCmd :: "'v set"
  ballot :: "'a \<Rightarrow> bal"
  vote :: "inst \<Rightarrow> 'a \<Rightarrow> bal \<rightharpoonup> 'v"
  suggestion :: "inst \<Rightarrow> bal \<rightharpoonup> 'v"
  onebs :: "'a \<Rightarrow> bal \<rightharpoonup> (inst \<rightharpoonup> ('v\<times>bal))"
  learned :: "'l \<Rightarrow> inst \<rightharpoonup> 'v"
  leader :: "'a \<Rightarrow> bool"

global_interpretation dsa:distributed_safe_at quorums ballot vote for quorums ballot vote 
  defines acc_max = dsa.acc_max and max_quorum_votes = dsa.max_quorum_votes .

locale ampr1_ioa = IOA +
  fixes quorums::"'a set set" and leader :: "bal \<Rightarrow> 'a"
  -- {* @{term leader} determines the leader of a ballot. *}
begin

definition start where
  -- {* The initial state *}
  "start \<equiv> {\<lparr>propCmd = {}, ballot = (\<lambda> a . 0), vote = (\<lambda> i a . Map.empty), 
    suggestion = \<lambda> i . Map.empty, onebs = \<lambda> a . Map.empty, learned = \<lambda> l . Map.empty,
    leader = \<lambda> a . leader 0 = a\<rparr>}"

subsection {* The transitions *}

definition propose where
  "propose c r r' \<equiv> (r' = r\<lparr>propCmd := (propCmd r) \<union> {c}\<rparr>)"

definition join_ballot where
  "join_ballot a b s s' \<equiv>
    let onebs' = \<lambda> i . dsa.acc_max (vote s i) a b
    in
      b > (ballot s a)
      \<and> s' = s\<lparr>ballot := (ballot s)(a := b),
        onebs := (onebs s)(a := (onebs s a)(b \<mapsto> onebs')),
        leader := (ampr1_state.leader s)(a := False)\<rparr>"

definition acquire_leadership where
  "acquire_leadership a q s s' \<equiv> let b = ballot s a in
    leader b = a
    \<and> q \<in> quorums
    \<and> \<not> ampr1_state.leader s a
    \<and> (\<forall> a \<in> q . onebs s a b \<noteq> None)
    \<and> s' = s\<lparr>leader := (ampr1_state.leader s)(a := True),
        suggestion := \<lambda> i . (suggestion s i)(b :=
          let a_max = \<lambda> a . the (onebs s a b) i; m = dsa.max_quorum_votes q a_max
          in if m = {} then None else Some (fst (the_elem m)))\<rparr>"
  -- {* This is well-defined only when m has at most cardinality one (i.e. the array is conservative).
  When the suggestion is set to None, it means that any value is safe. *}

definition suggest where "suggest a i b v s s' \<equiv>
          v \<in> propCmd s
        \<and> ballot s a = b
        \<and> ampr1_state.leader s a
        \<and> suggestion s i b = None
        \<and> s' = s\<lparr>suggestion := (suggestion s)(i := (suggestion s i)(b \<mapsto> v))\<rparr>"

definition do_vote where
  "do_vote a i v s s' \<equiv> let b = ballot s a in
          vote s i a b = None
        \<and> suggestion s i b = Some v
        \<and> s' = s\<lparr>vote := (vote s)(i := (vote s i)(a := (vote s i a)(b := Some v)))\<rparr>"

abbreviation chosen where
  "chosen s i v \<equiv> ballot_array.chosen quorums (vote s i) v"

definition learn where
  "learn l i v s s' \<equiv> chosen s i v \<and> s' = s\<lparr>learned := (learned s)(l := (learned s l)(i := Some v))\<rparr>"

definition catch_up where
  "catch_up l1 l2 i v s s' \<equiv> learned s l2 i = Some v
    \<and> s' = s\<lparr>learned := (learned s)(l1 := (learned s l1)(i := Some v))\<rparr>"

fun trans_rel where
  "trans_rel r (Propose c) r' = propose c r r'"
| "trans_rel r Internal r' = (
    (\<exists> a b . join_ballot a b r r')
    \<or> (\<exists> a i v . do_vote a i v r r')
    \<or> (\<exists> a i b v . suggest a i b v r r')
    \<or> (\<exists> l1 l2 i v . catch_up l1 l2 i v r r')
    \<or> (\<exists> a q . acquire_leadership a q r r'))"
| "trans_rel r (Learn i v l) r' = learn l i v r r'"

lemma trans_cases[consumes 1]:
  assumes "trans_rel r a r'"
  obtains 
  (propose) c where "propose c r r'"
| (learn) l i v where "learn l i v r r'"
| (join_ballot) a b where "join_ballot a b r r'"
| (do_vote) a i v where "do_vote a i v r r'"
| (suggest) a i b v where "suggest a i b v r r'"
| (catch_up) l1 l2 i v where "catch_up l1 l2 i v r r'"
| (acquire) a q where "acquire_leadership a q r r'"
  using assms apply induct apply simp
  by (metis ampr1_ioa.trans_rel.simps(1) ampr1_ioa.trans_rel.simps(3) paxos_action.exhaust trans_rel.simps(2)) 

definition trans where
  "trans \<equiv> { (r,a,r') . trans_rel r a r'}"

subsection {* The I/O-automaton *}

definition ioa where
  "ioa \<equiv> \<lparr>ioa.asig = paxos_asig, start = start, trans = trans\<rparr>"

lemmas simps = ioa_def asig_def start_def trans_def propose_def join_ballot_def
  do_vote_def learn_def suggest_def catch_up_def acquire_leadership_def

end

end