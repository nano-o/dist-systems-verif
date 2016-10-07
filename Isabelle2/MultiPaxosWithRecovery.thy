theory MultiPaxosWithRecovery
imports IOA BallotArrays Paxos_Sig 
begin

record ('v,'a) ampr1_state =
  propCmd :: "'v set"
  ballot :: "'a \<Rightarrow> bal"
  vote :: "'a \<Rightarrow> inst \<Rightarrow> bal \<rightharpoonup> 'v"
  suggestion :: "inst \<Rightarrow> bal \<rightharpoonup> 'v"
  -- {* @{term suggestion} is part of the local state of leaders. *}
  twoas :: "inst \<Rightarrow> bal \<rightharpoonup> 'v"
  -- {* suggestion is forgotten upon a crash, but the twoa messages stay in the network. *}
  inst_status :: "bal \<rightharpoonup> inst \<rightharpoonup> 'v option"
  -- {* @{term inst_status} is set upon acquiring leadership; if @{term "inst_status s b = Some m"},
  @{term "m i = Some None"} means that  all values are safe, 
  @{term "m i = Some (Some v)"} means that only @{term v} is known safe, and @{term "m i = None"} 
  means that the status of the instance is unknown. *}
  log :: "'a \<Rightarrow> inst \<Rightarrow> 'v option"
  -- {* The log is used to transfer decisions to replicas which need to catch up,
  and for windowing (wait for a quorum to have a decision in its log before moving the window) *}
  lowest :: "'a \<Rightarrow> inst"
  -- {* Lowest instance in which the acceptor is allowed to participate. *}

locale ampr1_ioa =
  fixes quorums::"'a set set" and leader :: "bal \<Rightarrow> 'a" and window :: nat
  -- {* @{term leader} determines the leader of a given ballot. *}
begin

interpretation ba:ballot_array quorums ballot vote for ballot vote .

definition start_s where
  -- {* The initial state *}
  "start_s \<equiv> \<lparr>propCmd = {}, ballot = (\<lambda> a . 0), vote = (\<lambda> a i . Map.empty), 
    suggestion = \<lambda> i . Map.empty, twoas = \<lambda> i . Map.empty,
    inst_status = \<lambda> b . if b = 0 then Some Map.empty else None,
    log = \<lambda> a . Map.empty, lowest = \<lambda> a . 0\<rparr>"

definition start where "start \<equiv> {start_s}"
  
subsection {* The transitions *}

definition propose where
  "propose c r r' \<equiv> (r' = r\<lparr>propCmd := (propCmd r) \<union> {c}\<rparr>)"

definition join_ballot where
  "join_ballot a b s s' \<equiv>
      b > (ballot s a)
      \<and> s' = s\<lparr>ballot := (ballot s)(a := b)\<rparr>"
 
definition sugg where sugg_def: "sugg s i b q \<equiv>
  if \<exists> a \<in> q . \<exists> b' . b' < b \<and> vote s a i b' \<noteq> None
  then let votes = {(w,b') . b' < b \<and> (\<exists> a \<in> q . vote s a i b' = Some w)}
    in Some (the_elem (fst ` (max_by_key votes snd)))
  else None"
  
definition joined where
  -- {* q joined ballot b and all its members have info starting at least from instance i. *}
  "joined s q b i \<equiv> \<forall> a \<in> q .  lowest s a \<ge> i \<and> ballot s a \<ge> b"
  
definition next_avail where
  "next_avail s a \<equiv> Min {i . log s a i = None}"

definition acquire_leadership where
  "acquire_leadership a q s s' \<equiv> let b = ballot s a in
    leader b = a
    \<and> q \<in> quorums
    \<and> inst_status s b = None
    \<and> (let n = next_avail s a in
        joined s q b n
        \<and> inst_status s' = (inst_status s)(b := 
            Some (\<lambda> i . if i < n then None else Some (sugg s i b q)))
        \<and> (\<forall> i . suggestion s' i = (suggestion s i)(b := (if i < n then None else sugg s i b q))
          \<or> suggestion s' i = (suggestion s i)))
    \<and> (\<forall> i . twoas s' i = (twoas s i)(b := suggestion s' i b))
    \<and> propCmd s' = propCmd s \<and> ballot s' = ballot s \<and> vote s' = vote s 
    \<and> log s' = log s"
  
definition suggest where "suggest a i b v s s' \<equiv>
  v \<in> propCmd s
  \<and> ballot s a = b
  \<and> i \<ge> next_avail s a
  \<and> (\<forall> j \<le> i-window . \<exists> q \<in> quorums . \<forall> a \<in> q . log s a j \<noteq> None)
  \<and> suggestion s i b = None
  \<and> (case inst_status s b of Some f \<Rightarrow> f i = None | _ \<Rightarrow> False)
  \<and> s' = s\<lparr>suggestion := (suggestion s)(i := (suggestion s i)(b \<mapsto> v)),
      twoas := (twoas s)(i := (twoas s i)(b \<mapsto> v))\<rparr>"
  
definition do_vote where
  "do_vote a i v s s' \<equiv> let b = ballot s a in
    i \<ge> lowest s a
    \<and> vote s a i b = None
    \<and> twoas s i b = Some v
    \<and> s' = s\<lparr>vote := (vote s)(a := (vote s a)(i := (vote s a i)(b := Some v)))\<rparr>"

definition chosen where
  "chosen s i v \<equiv> ba.chosen (flip (vote s) i) v"

definition learn where
  "learn a i v s s' \<equiv>
    chosen s i v
    \<and> s' = s\<lparr>log := (log s)(a := (log s a)(i := Some v))\<rparr>"
  
definition recover where
  -- {* sets the ballot and the lowest instance. *}
  "recover a s s' \<equiv> 
      (\<exists> q \<in> quorums . let m = Max {ballot s a | a . a \<in> q} in
          \<exists> su . (\<forall> i b . (leader b = a \<and> su i b = None) \<or> (leader b \<noteq> a \<and> su i b = suggestion s i b))
          \<and> s' = s\<lparr>ballot := (ballot s)(a := m),
            lowest := (lowest s)(a := next_avail s (leader m) + window),
            suggestion := su\<rparr> )"
  
fun trans_rel where
  "trans_rel r (Propose c) r' = propose c r r'"
| "trans_rel r Internal r' = (
    (\<exists> a b . join_ballot a b r r')
    \<or> (\<exists> a i v . do_vote a i v r r')
    \<or> (\<exists> a i b v . suggest a i b v r r')
    \<or> (\<exists> a q . acquire_leadership a q r r')
    \<or> (\<exists> a . recover a r r') )"
| "trans_rel r (Learn a i vs) r' =
    (\<exists> v . learn a i v r r' \<and> vs = [v])"

lemma trans_cases:
  assumes "trans_rel r a r'"
  obtains 
  (propose) c where "propose c r r'"
| (learn) a i v where "learn a i v r r'"
| (join_ballot) a b where "join_ballot a b r r'"
| (do_vote) a i v where "do_vote a i v r r'"
| (suggest) a i b v where "suggest a i b v r r'"
| (acquire) a q where "acquire_leadership a q r r'"
| (recover) a where "recover a r r'"
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