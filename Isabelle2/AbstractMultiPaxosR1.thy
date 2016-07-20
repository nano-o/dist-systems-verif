theory AbstractMultiPaxosR1
imports  "../../IO-Automata/IOA" BallotArrays DistributedSafeAt
begin

text {*
1) Acceptors vote for a suggestion, and leaders use the distributed implementation of the safe-at computation.
2) Explicit 1b messages.
3) Explicit learning.
4) Catch-up.
5) Localizing suggestions (the leader function).
6) Explicit leadership acquisition.
*}

type_synonym bal = nat
type_synonym inst = nat
text {* TODO: how to use real types, and the transfer package? *}

record ('v,'a,'l) amp_state =
  propCmd :: "'v set"
  ballot :: "'a \<Rightarrow> bal"
  vote :: "'a \<Rightarrow> inst \<Rightarrow> bal \<rightharpoonup> 'v"
  suggestion :: "inst \<Rightarrow> bal \<rightharpoonup> 'v"
  onebs :: "'a \<Rightarrow> bal \<rightharpoonup> (inst \<rightharpoonup> ('v \<times> bal))"
  learned :: "'l \<Rightarrow> inst \<rightharpoonup> 'v"
  leader :: "'a \<Rightarrow> bool"

locale amp_ioa = IOA +
  fixes quorums::"'a set set" and leader :: "bal \<Rightarrow> 'a"
  -- {* @{term leader} determines the leader of a ballot. *}
begin

datatype ('vv,'aa,'ll) amp_action =
  Propose 'vv
| Learn nat 'vv 'll
| Internal

definition amp_asig where
  "amp_asig \<equiv>
    \<lparr> inputs = { Propose c | c . True},
      outputs = { Learn i v l | i v l . True},
      internals = {Internal}\<rparr>"

definition amp_start where
  -- {* The initial state *}
  "amp_start \<equiv> {\<lparr>propCmd = {}, ballot = (\<lambda> a . 0), vote = (\<lambda> a i. Map.empty), 
    suggestion = (\<lambda> i . Map.empty), onebs = \<lambda> a . Map.empty, learned = \<lambda> l . Map.empty,
    leader = \<lambda> a . leader 0 = a\<rparr>}"

subsection {* The transitions *}

definition propose where
  "propose c r r' \<equiv> (r' = r\<lparr>propCmd := (propCmd r) \<union> {c}\<rparr>)"

definition join_ballot where
  "join_ballot a b s s' \<equiv> 
    let onebs' = \<lambda> i . distributed_safe_at.acc_max (\<lambda>a. vote s a i) a b
    in
      b > (ballot s a) 
      \<and> s' = s\<lparr>ballot := (ballot s)(a := b),
        onebs := (onebs s)(a := (onebs s a)(b := Some onebs')),
        leader := (amp_state.leader s)(a := False)\<rparr>"

definition acquire_leadership where
  "acquire_leadership a q s s' \<equiv> let b = ballot s a in 
    leader b = a
    \<and> q \<in> quorums
    \<and> \<not> amp_state.leader s a 
    \<and> (\<forall> a \<in> q . onebs s a b \<noteq> None)
    \<and> s' = s\<lparr>leader := (amp_state.leader s)(a := True), 
        suggestion := (\<lambda>i . (suggestion s i)(b :=
          let m = distributed_safe_at.max_pair q (\<lambda> a . the (onebs s a b) i) in
            map_option fst m))\<rparr>"

definition suggest where "suggest a i b v s s' \<equiv>
          v \<in> propCmd s
        \<and> ballot s a = b
        \<and> amp_state.leader s a
        \<and> suggestion s i b = None
        \<and> s' = s\<lparr>suggestion := (suggestion s)(i := (suggestion s i)(b := Some v))\<rparr>"

definition do_vote where
  "do_vote a i v s s' \<equiv> let b = ballot s a in
          vote s a i b = None
        \<and> suggestion s i b = Some v
        \<and> s' = s\<lparr>vote := (vote s)(a := (vote s a)(i := (vote s a i)(b := Some v)))\<rparr>"

abbreviation chosen where
  "chosen s i v \<equiv> ballot_array.chosen quorums (\<lambda>a. vote s a i) v"

definition learn where
  "learn l i v s s' \<equiv> chosen s i v \<and> s' = s\<lparr>learned := (learned s)(l := (learned s l)(i := Some v))\<rparr>"

definition catch_up where
  "catch_up l1 l2 i v s s' \<equiv> learned s l2 i = Some v 
    \<and> s' = s\<lparr>learned := (learned s)(l1 := (learned s l1)(i := Some v))\<rparr>"

fun amp_trans_rel where
  "amp_trans_rel r (Propose c) r' = propose c r r'"
| "amp_trans_rel r Internal r' = (
    (\<exists> a b . join_ballot a b r r')
    \<or> (\<exists> a i v . do_vote a i v r r')
    \<or> (\<exists> a i b v . suggest a i b v r r')
    \<or> (\<exists> l1 l2 i v . catch_up l1 l2 i v r r')
    \<or> (\<exists> a q . acquire_leadership a q r r'))"
| "amp_trans_rel r (Learn i v l) r' = learn l i v r r'"

lemma trans_cases[consumes 1]:
  assumes "amp_trans_rel r a r'"
  obtains 
  (propose) c where "propose c r r'"
| (learn) l i v where "learn l i v r r'"
| (join_ballot) a b where "join_ballot a b r r'"
| (do_vote) a i v where "do_vote a i v r r'"
| (suggest) a i b v where "suggest a i b v r r'"
| (catch_up) l1 l2 i v where "catch_up l1 l2 i v r r'"
| (acquire) a q where "acquire_leadership a q r r'"
using assms by induct auto

definition amp_trans where
  "amp_trans \<equiv> { (r,a,r') . amp_trans_rel r a r'}"

subsection {* The I/O-automaton *}

definition amp_ioa where
  "amp_ioa \<equiv> \<lparr>ioa.asig = amp_asig, start = amp_start, trans = amp_trans\<rparr>"

lemmas simps = amp_ioa_def amp_asig_def amp_start_def amp_trans_def propose_def join_ballot_def 
  do_vote_def learn_def

end

end