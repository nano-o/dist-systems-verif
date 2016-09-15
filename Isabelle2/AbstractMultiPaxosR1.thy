theory AbstractMultiPaxosR1
imports  IOA BallotArrays DistributedSafeAt Paxos_Sig
begin

text {* TODO: according to Isabelle's canonical argument order, @{typ bal} should come before @{typ inst} *}

record ('v,'a,'l) ampr1_state =
  propCmd :: "'v set"
  ballot :: "'a \<Rightarrow> bal"
  vote :: "inst \<Rightarrow> 'a \<Rightarrow> bal \<rightharpoonup> 'v"
  suggestion :: "inst \<Rightarrow> bal \<rightharpoonup> 'v"
  onebs :: "'a \<Rightarrow> bal \<rightharpoonup> (inst \<Rightarrow> ('v\<times>bal) set)"
  is_leader :: "'a \<Rightarrow> bool"

locale ampr1_ioa =
  fixes quorums::"'a set set" and leader :: "bal \<Rightarrow> 'a"
  -- {* @{term leader} determines the leader of a ballot. *}
begin

sublocale dsa:distributed_safe_at quorums ballot vote for ballot vote .

definition start_s where
  -- {* The initial state *}
  "start_s \<equiv> \<lparr>propCmd = {}, ballot = (\<lambda> a . 0), vote = (\<lambda> i a . Map.empty), 
    suggestion = \<lambda> i . Map.empty, onebs = \<lambda> a . Map.empty,
    leader = \<lambda> a . leader 0 = a\<rparr>"

definition start where "start \<equiv> {start_s}"
  
subsection {* The transitions *}

definition propose where
  "propose c r r' \<equiv> (r' = r\<lparr>propCmd := (propCmd r) \<union> {c}\<rparr>)"

definition join_ballot where
  "join_ballot a b s s' \<equiv>
    let onebs' = \<lambda> i . dsa.acc_max (vote s i) a b
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
  
definition acquire_leadership where
  "acquire_leadership a q s s' \<equiv> let b = ballot s a in
    leader b = a
    \<and> q \<in> quorums
    \<and> \<not> is_leader s a
    \<and> joined s q b
    \<and> s' = s\<lparr>is_leader := (is_leader s)(a := True),
        suggestion := \<lambda> i . (suggestion s i)(b := sugg s i b q)\<rparr>"

definition suggest where "suggest a i b v s s' \<equiv>
          v \<in> propCmd s
        \<and> ballot s a = b
        \<and> is_leader s a
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