theory AbstractMultiPaxosWithRecovery
imports  IOA BallotArrays Paxos_Sig
begin                          

section {* Definition of the Abstract MultiPaxos I/O-automaton *}

subsection {* State and actions *}

record ('v,'a) ampr_state =
  propCmd :: "'v set"
  ballot :: "'a \<Rightarrow> bal"
  vote :: "'a \<Rightarrow> bal \<Rightarrow> inst \<Rightarrow> 'v option"
  lowest :: "'a \<Rightarrow> inst"
  log :: "'a \<Rightarrow> inst \<Rightarrow> 'v option"

locale ampr_ioa =
  fixes quorums::"'a set set"
begin

definition start where
  -- {* The initial state *}
  "start \<equiv> {\<lparr>propCmd = {}, ballot = (\<lambda> a . 0), vote = (\<lambda> a b i . None),
  lowest = \<lambda> a . 0, log = \<lambda> a i . None\<rparr>}"

subsection {* The transitions *}

definition propose where
  "propose c r r' \<equiv> (r' = r\<lparr>propCmd := (propCmd r) \<union> {c}\<rparr>)"

definition join_ballot where
  "join_ballot a b s s' \<equiv>
    b > (ballot s a) \<and> s' = s\<lparr>ballot := (ballot s)(a := b)\<rparr>"

interpretation ba:ballot_array quorums ballot vote for ballot vote .

abbreviation proved_safe_at where 
  -- {* v is proved safe in instance i at ballot b by quorum q *}
  "proved_safe_at s i q b v \<equiv> 
    ba.proved_safe_at_abs (ballot s) (flip (vote s) i) q b v"

abbreviation conservative_at where
  "conservative_at s i \<equiv> ballot_array.conservative_array (flip (vote s) i)"

definition do_vote where
  "do_vote a i q v s s' \<equiv> let b = ballot s a in
          v \<in> propCmd s
        \<and> i \<ge> lowest s a
        \<and> vote s a b i = None
        \<and> proved_safe_at s i q b v
        \<and> q \<in> quorums
        \<and> conservative_at s' i
        \<and> s' = s\<lparr>vote := (vote s)(a := (vote s a)(b := (vote s a b)(i := Some v)))\<rparr>"

abbreviation chosen where
  "chosen s i v \<equiv> ba.chosen (flip (vote s) i) v"

definition learn where
  "learn a i vs s s' \<equiv> (\<forall> j \<in> {0..<length vs} . chosen s (i+j) (vs!(j+1)))
    \<and> (\<exists> new_log . (\<forall> j \<in> {0..<length vs} . new_log (i+j) = Some (vs!(j+1)))
        \<and> (\<forall> j \<in> {0..<i} \<union> {i+length vs..} . new_log j = log s a j)
        \<and> s' = s\<lparr>log := (log s)(a := new_log)\<rparr>)"

fun trans_rel where
  "trans_rel r (Propose c) r' = propose c r r'"
| "trans_rel r Internal r' = (
    (\<exists> a b . join_ballot a b r r')
    \<or> (\<exists> a q i v . do_vote a i q v r r'))"
| "trans_rel r (Learn a i vs) r' = learn a i vs r r'"

lemma trans_cases: assumes "trans_rel r a r'"
  obtains 
  (propose) c where "propose c r r'"
| (learn) a i vs where "learn a i vs r r'"
| (join_ballot) a b where "join_ballot a b r r'"
| (do_vote) a i q v where "do_vote a i q v r r'"
  using assms apply induct apply auto
  by (metis trans_rel.elims(2))

definition trans where
  "trans \<equiv> { (r,a,r') . trans_rel r a r'}"

subsection {* The I/O-automaton *}

definition ioa where
  "ioa \<equiv> \<lparr>ioa.asig = paxos_asig, start = start, trans = trans\<rparr>"

lemmas simps = ioa_def paxos_asig_def start_def trans_def propose_def join_ballot_def 
  do_vote_def learn_def

end

end