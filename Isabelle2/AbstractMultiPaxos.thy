theory AbstractMultiPaxos
imports  IOA BallotArrays Paxos_Sig
begin                          

section {* Definition of the Abstract MultiPaxos I/O-automaton *}

subsection {* State and actions *}

record ('v,'a) amp_state =
  propCmd :: "'v set"
  ballot :: "'a \<Rightarrow> nat"
  vote :: "inst \<Rightarrow> 'a \<Rightarrow> bal \<Rightarrow> 'v option"
  -- {* TODO: according to Isabelle's canonical argument order, 
  it shoudl be @{typ "'a \<Rightarrow> bal \<Rightarrow> inst \<Rightarrow> 'v option"} *}

locale amp_ioa =
  fixes quorums::"'a set set"
begin

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
  "proved_safe_at s i q b v \<equiv> ballot_array.proved_safe_at_abs quorums (ballot s) (vote s i) q b v"

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
<<<<<<< HEAD
  "learn i v s s' \<equiv> chosen s i v \<and> s = s'"
=======
  "learn i vs s s' \<equiv> (\<forall> v \<in> set vs . chosen s i v) \<and> s = s'"
>>>>>>> giuliano_2

fun amp_trans_rel where
  "amp_trans_rel r (Propose c) r' = propose c r r'"
| "amp_trans_rel r Internal r' = (
    (\<exists> a b . join_ballot a b r r')
    \<or> (\<exists> a q i v . do_vote a i q v r r'))"
<<<<<<< HEAD
| "amp_trans_rel r (Learn i v) r' = learn i v r r'"
=======
| "amp_trans_rel r (Learn a i vs) r' = learn i vs r r'"
>>>>>>> giuliano_2

lemma trans_cases: assumes "amp_trans_rel r a r'"
  obtains 
  (propose) c where "propose c r r'"
<<<<<<< HEAD
| (learn) i v where "learn i v r r'"
| (join_ballot) a b where "join_ballot a b r r'"
| (do_vote) a i q v where "do_vote a i q v r r'"
  using assms apply induct apply auto
  by (meson amp_trans_rel.elims(2)) 
=======
| (learn) i vs where "learn i vs r r'"
| (join_ballot) a b where "join_ballot a b r r'"
| (do_vote) a i q v where "do_vote a i q v r r'"
  using assms apply induct apply auto
  by (metis amp_trans_rel.elims(2))
>>>>>>> giuliano_2

definition amp_trans where
  "amp_trans \<equiv> { (r,a,r') . amp_trans_rel r a r'}"

subsection {* The I/O-automaton *}

definition amp_ioa where
  "amp_ioa \<equiv> \<lparr>ioa.asig = paxos_asig, start = amp_start, trans = amp_trans\<rparr>"

lemmas simps = amp_ioa_def paxos_asig_def amp_start_def amp_trans_def propose_def join_ballot_def 
  do_vote_def learn_def

end

end