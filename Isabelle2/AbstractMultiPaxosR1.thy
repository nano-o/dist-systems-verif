theory AbstractMultiPaxosR1
imports  "../../IO-Automata/IOA" BallotArrays3 DistributedSafeAt
begin

text {* 
1) added a suggestions that acceptors then vote for, and used the distributed implementation of the safe-at computation.
*}

record ('v,'a) amp_state =
  propCmd :: "'v set"
  ballot :: "'a \<Rightarrow> nat"
  vote :: "nat \<Rightarrow> 'a \<Rightarrow> nat \<rightharpoonup> 'v"
  suggestion :: "nat \<Rightarrow> nat \<rightharpoonup> 'v"

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
    suggestion = \<lambda> i . Map.empty \<rparr>}"

subsection {* The transitions *}

definition propose where
  "propose c r r' \<equiv> (r' = r\<lparr>propCmd := (propCmd r) \<union> {c}\<rparr>)"

definition join_ballot where
  "join_ballot a b s s' \<equiv>
    b > (ballot s a) \<and> s' = s\<lparr>ballot := (ballot s)(a := b)\<rparr>"

abbreviation proved_safe_at where 
  -- {* v is proved safe in instance i at ballot b by quorum q *}
  "proved_safe_at s i q b v \<equiv> distributed_safe_at.proved_safe_at (ballot s) (vote s i) quorums q b v"

abbreviation conservative_at where
  "conservative_at s i \<equiv> ballot_array.conservative_array (vote s i)"

definition suggest where
  "suggest i b v q s s' \<equiv>
          v \<in> propCmd s 
        \<and> suggestion s i b = None
        \<and> proved_safe_at s i q b v
        \<and> s' = s\<lparr>suggestion := (suggestion s)(i := (suggestion s i)(b \<mapsto> v))\<rparr>"

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