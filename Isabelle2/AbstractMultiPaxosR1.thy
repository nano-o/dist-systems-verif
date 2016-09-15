theory AbstractMultiPaxosR1
imports  IOA BallotArrays DistributedSafeAt Paxos_Sig
begin

text {* TODO: according to Isabelle's canonical argument order, @{typ bal} should come before @{typ inst} *}

record ('v,'a,'l) ampr1_state =
  propCmd :: "'v set"
  ballot :: "'a \<Rightarrow> bal"
  vote :: "'a \<Rightarrow> inst \<Rightarrow> bal \<rightharpoonup> 'v"
  suggestion :: "inst \<Rightarrow> bal \<rightharpoonup> 'v"
  onebs :: "'a \<Rightarrow> bal \<rightharpoonup> (inst \<Rightarrow> ('v\<times>bal) set)"
  is_leader :: "'a \<Rightarrow> bool"
  -- {* TODO: @{term is_leader} is redundant, as it is equivalent to being in an owned ballot and having received
  a quorum of onebs. *}

locale ampr1_ioa =
  fixes quorums::"'a set set" and leader :: "bal \<Rightarrow> 'a"
  -- {* @{term leader} determines the leader of a ballot. *}
begin

sublocale dsa:distributed_safe_at quorums ballot vote for ballot vote .

definition start_s where
  -- {* The initial state *}
  "start_s \<equiv> \<lparr>propCmd = {}, ballot = (\<lambda> a . 0), vote = (\<lambda> a i . Map.empty), 
    suggestion = \<lambda> i . Map.empty, onebs = \<lambda> a . Map.empty,
    is_leader = \<lambda> a . leader 0 = a\<rparr>"

definition start where "start \<equiv> {start_s}"
  
subsection {* The transitions *}

definition propose where
  "propose c r r' \<equiv> (r' = r\<lparr>propCmd := (propCmd r) \<union> {c}\<rparr>)"

definition join_ballot where
  "join_ballot a b s s' \<equiv>
    let onebs' = \<lambda> i . dsa.acc_max (flip (vote s) i) a b
    in
      b > (ballot s a)
      \<and> s' = s\<lparr>ballot := (ballot s)(a := b),
        onebs := (onebs s)(a := (onebs s a)(b \<mapsto> onebs')) ,
        is_leader := (is_leader s)(a := False)\<rparr>"
  
  
definition max_vote where max_vote_def:
  "max_vote s i b q \<equiv> max_by_key (\<Union> a \<in> q . the (onebs s a b) i) snd"

definition sugg where sugg_def: "sugg s i b q \<equiv>
  let m = max_vote s i b q in if m = {} then None else Some (the_elem (fst ` m))"
  
definition joined where "joined s q b \<equiv> \<forall> a \<in> q . onebs s a b \<noteq> None"
  
definition decided_below where "decided_below s i b \<equiv> 
  \<exists> v b' . b' < b \<and> dsa.chosen_at (flip (vote s) i) v b"
  
definition acquire_leadership where
  -- {* Upon acquiring leadership, the leader makes suggestions in all instances but an 
  arbitrary subset of the instances whose outcome is already decided. This implies that new
  suggestions (after acquiring leadership) can only be made in undecided intances, because a None
  suggestion does indicates that the instance is safe only if it is not decided in a lower ballot. *}
  "acquire_leadership a q s s' \<equiv> let b = ballot s a in
    leader b = a
    \<and> q \<in> quorums
    \<and> \<not> is_leader s a
    \<and> joined s q b
    \<and> is_leader s' = (is_leader s)(a := True)
    \<and> (\<forall> i . suggestion s' i = (suggestion s i)(b := sugg s i b q) 
      \<or> (decided_below s i b \<and> suggestion s' i = (suggestion s i)))
    \<and> propCmd s' = propCmd s \<and> ballot s' = ballot s \<and> vote s' = vote s \<and> onebs s' = onebs s"

definition suggest where "suggest a i b v s s' \<equiv>
          v \<in> propCmd s
        \<and> ballot s a = b
        \<and> is_leader s a
        \<and> suggestion s i b = None
        \<and> \<not> decided_below s i b
        \<and> s' = s\<lparr>suggestion := (suggestion s)(i := (suggestion s i)(b \<mapsto> v))\<rparr>"

definition do_vote where
  "do_vote a i v s s' \<equiv> let b = ballot s a in
          vote s a i b = None
        \<and> suggestion s i b = Some v
        \<and> s' = s\<lparr>vote := (vote s)(a := (vote s a)(i := (vote s a i)(b := Some v)))\<rparr>"

abbreviation chosen where
  "chosen s i v \<equiv> ballot_array.chosen quorums (flip (vote s) i) v"

definition learn where
  "learn i v s s' \<equiv> chosen s i v \<and> s' = s"

fun trans_rel where
  "trans_rel r (Propose c) r' = propose c r r'"
| "trans_rel r Internal r' = (
    (\<exists> a b . join_ballot a b r r')
    \<or> (\<exists> a i v . do_vote a i v r r')
    \<or> (\<exists> a i b v . suggest a i b v r r')
    \<or> (\<exists> a q . acquire_leadership a q r r'))"
| "trans_rel r (Learn i v) r' = learn i v r r'"

lemma trans_cases:
  assumes "trans_rel r a r'"
  obtains 
  (propose) c where "propose c r r'"
| (learn) i v where "learn i v r r'"
| (join_ballot) a b where "join_ballot a b r r'"
| (do_vote) a i v where "do_vote a i v r r'"
| (suggest) a i b v where "suggest a i b v r r'"
| (acquire) a q where "acquire_leadership a q r r'"
  using assms apply induct apply simp
  by (metis ampr1_ioa.trans_rel.simps(1) ampr1_ioa.trans_rel.simps(3) paxos_action.exhaust trans_rel.simps(2)) 

definition trans where
  "trans \<equiv> { (r,a,r') . trans_rel r a r'}"

subsection {* The I/O-automaton *}

definition ioa where
  "ioa \<equiv> \<lparr>ioa.asig = paxos_asig, start = start, trans = trans\<rparr>"

lemmas simps = ioa_def paxos_asig_def start_def trans_def propose_def join_ballot_def
  do_vote_def learn_def suggest_def acquire_leadership_def

end

end