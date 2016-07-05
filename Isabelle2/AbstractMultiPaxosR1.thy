theory AbstractMultiPaxosR1
imports  "../../IO-Automata/IOA" BallotArrays3 DistributedSafeAt
begin

text {* 
1) Acceptors vote for a suggestion, and leaders use the distributed implementation of the safe-at computation.
2) Explicit 1b messages.
*}

type_synonym bal = nat
type_synonym inst = nat
text {* TODO: how to use and real type and the transfer package? *}

record ('v,'a) amp_state =
  propCmd :: "'v set"
  ballot :: "'a \<Rightarrow> bal"
  vote :: "inst \<Rightarrow> 'a \<Rightarrow> bal \<rightharpoonup> 'v"
  suggestion :: "inst \<Rightarrow> bal \<rightharpoonup> 'v"
  onebs :: "'a \<Rightarrow> bal \<rightharpoonup> (inst \<rightharpoonup> ('v\<times>bal))"

locale amp_ioa = IOA +
  fixes quorums::"'a set set"
  fixes learners::"'l set"
begin

datatype ('vv,'aa,'ll) amp_action =
  Propose 'vv
| Learn nat 'vv 'll
| Internal

definition amp_asig where
  "amp_asig \<equiv>
    \<lparr> inputs = { Propose c | c . True},
      outputs = { Learn i v l | i v l . l \<in> learners},
      internals = {Internal}\<rparr>"

definition amp_start where
  -- {* The initial state *}
  "amp_start \<equiv> {\<lparr>propCmd = {}, ballot = (\<lambda> a . 0), vote = (\<lambda> i a . Map.empty), 
    suggestion = \<lambda> i . Map.empty, onebs = \<lambda> a . Map.empty \<rparr>}"

subsection {* The transitions *}

definition propose where
  "propose c r r' \<equiv> (r' = r\<lparr>propCmd := (propCmd r) \<union> {c}\<rparr>)"

definition join_ballot where
  "join_ballot a b s s' \<equiv> 
    let onebs' = \<lambda> i . distributed_safe_at.acc_max (vote s i) a b
    in
      b > (ballot s a) \<and> s' = s\<lparr>ballot := (ballot s)(a := b),
        onebs := (onebs s)(a := (onebs s a)(b \<mapsto> onebs'))\<rparr>"

definition suggest where
  "suggest i b v q s s' \<equiv>
          v \<in> propCmd s
        \<and> suggestion s i b = None
        \<and> q \<in> quorums
        \<and> (\<forall> a \<in> q . onebs s a b \<noteq> None)
        \<and> (let m = distributed_safe_at.max_pair q (\<lambda> a . the (onebs s a b) i) in 
            (case m of None \<Rightarrow> True | Some (v',b') \<Rightarrow> v = v')
            \<and> s' = s\<lparr>suggestion := (suggestion s)(i := (suggestion s i)(b \<mapsto> v))\<rparr>)"

definition do_vote where
  "do_vote a i v s s' \<equiv> let b = ballot s a in
          vote s i a b = None
        \<and> suggestion s i b = Some v
        \<and> s' = s\<lparr>vote := (vote s)(i := (vote s i)(a := (vote s i a)(b := Some v)))\<rparr>"

abbreviation chosen where
  "chosen s i v \<equiv> ballot_array.chosen quorums (vote s i) v"

definition learn where
  "learn i v s s' \<equiv> chosen s i v \<and> s = s'"

fun amp_trans_rel where
  "amp_trans_rel r (Propose c) r' = propose c r r'"
| "amp_trans_rel r Internal r' = (
    (\<exists> a b . join_ballot a b r r')
    \<or> (\<exists> a i v . do_vote a i v r r')
    \<or> (\<exists> i b v q . suggest i b v q r r'))"
| "amp_trans_rel r (Learn i v l) r' = learn i v r r'"

lemma trans_cases[consumes 1]:
  assumes "amp_trans_rel r a r'"
  obtains 
  (propose) c where "propose c r r'"
| (learn) i v where "learn i v r r'"
| (join_ballot) a b where "join_ballot a b r r'"
| (do_vote) a i v where "do_vote a i v r r'"
| (suggest) i b v q where "suggest i b v q r r'"
using assms apply induct apply auto done

definition amp_trans where
  "amp_trans \<equiv> { (r,a,r') . amp_trans_rel r a r'}"

subsection {* The I/O-automaton *}

definition amp_ioa where
  "amp_ioa \<equiv> \<lparr>ioa.asig = amp_asig, start = amp_start, trans = amp_trans\<rparr>"

lemmas simps = amp_ioa_def amp_asig_def amp_start_def amp_trans_def propose_def join_ballot_def 
  do_vote_def learn_def

end


end