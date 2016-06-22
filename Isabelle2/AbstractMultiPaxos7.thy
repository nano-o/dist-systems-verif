theory AbstractMultiPaxos7
imports  "../../IO-Automata/IOA" BallotArrays3
begin

section {* Definition of the Abstract MultiPaxos I/O-automaton *}

subsection {* State and actions *}

text {* The actions (labels on transitions) of the I/O-automaton *}

text {* The states of the I/O-automaton *}

record ('v,'a) amp_state =
  propCmd :: "'v set"
  ballot :: "'a \<Rightarrow> nat"
  vote :: "nat \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> 'v option"

locale amp_ioa = IOA +
  fixes quorums::"'a set set"
  fixes learners::"'l set"
begin

datatype ('vv,'aa,'ll) amp_action =
  Propose 'vv
| Learn nat 'vv 'll
| Vote 'aa "'aa set" nat 'vv
  -- {* an acceptor votes in an instance according to a quorum *}
| JoinBallot 'aa nat

definition amp_asig where
  "amp_asig \<equiv>
    \<lparr> inputs = { Propose c | c . True},
      outputs = { Learn i v l | i v l . l \<in> learners},
      internals = {Vote a i q b | a i b q . True} \<union> {JoinBallot a b | a b . True}\<rparr>"

definition amp_start where
  -- {* The initial state *}
  "amp_start \<equiv> {\<lparr>propCmd = {}, ballot = (\<lambda> a . 0), vote = (\<lambda> i a b . None) \<rparr>}"

subsection {* The transitions *}

definition propose where
  "propose c r r' \<equiv> (r' = r\<lparr>propCmd := (propCmd r) \<union> {c}\<rparr>)"

definition join_ballot where
  "join_ballot a b s s' \<equiv> 
    b > (ballot s a) \<and> s' = s\<lparr>ballot := (ballot s)(a := b)\<rparr>"

abbreviation proved_safe_at where 
  -- {* v is proved safe in instance i at ballot b by quorum q *}
  "proved_safe_at s i q b v \<equiv> ballot_array.proved_safe_at_2 quorums (ballot s) (vote s i) q b v"

abbreviation conservative_at where
  "conservative_at s i \<equiv> ballot_array.conservative_array (vote s i)"

definition do_vote where
  "do_vote a i q v s s' \<equiv> let b = ballot s a in
          v \<in> propCmd s
        \<and> vote s i a b = None
        \<and> proved_safe_at s i q b v
        \<and> q \<in> quorums
        \<and> conservative_at s' i
        \<and> s' = s\<lparr>vote := (vote s)(i := (vote s i)(a := (vote s i a)(b := Some v)))\<rparr>"

abbreviation chosen where 
  "chosen s i v \<equiv> ballot_array.chosen quorums (vote s i) v"

definition learn where
  "learn l i v s s' \<equiv> chosen s i v \<and> s = s'"

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

lemmas simps = amp_ioa_def amp_asig_def amp_start_def amp_trans_def propose_def join_ballot_def 
  do_vote_def learn_def

end

end