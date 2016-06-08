theory AbstractMultiPaxos7
imports  "../../IO-Automata/IOA" BallotArrays3
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
          v \<in> propCmd s
        \<and> proved_safe_at s i q b v
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

end