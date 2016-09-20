theory AbstractMultiPaxosR1
imports  IOA BallotArrays DistributedSafeAt Paxos_Sig "~~/src/HOL/Library/Monad_Syntax"
begin

text {* There are some things (e.g. chosen and safe) that can be computed non-atomically,
  but the computation has the same effect as if it was done atomically. Can this simplify proofs? *}

text {* About recovery without stable storage.
  Assume that pipelinening is limited to a window of n: a leader waits for a quorum 
  to know the decision of instance m-n before starting instance m.
  For an acceptor to recover, contact a quorum and select the highest ballot bmax among its members.
  Then ask the leader of bmax what is the highest completed instance j it knows about.
  Mark all instances after j+n as safe to participate in.
  Also, when a leader acquires leadership, it can broadcast its highest completed instance.
  *}

text {* About recovery with a stable ballot number.
  Similar to recovery without stable storage: one cannot know which promises were made.
*}

record ('v,'a) ampr1_state =
  propCmd :: "'v set"
  ballot :: "'a \<Rightarrow> bal"
  vote :: "'a \<Rightarrow> inst \<Rightarrow> bal \<rightharpoonup> 'v"
  suggestion :: "inst \<Rightarrow> bal \<rightharpoonup> 'v"
  -- {* @{term suggestion} is part of the local state of leaders. *}
  twoas :: "inst \<Rightarrow> bal \<rightharpoonup> 'v"
  -- {* suggestion is forgotten upon a crash, but the twoa messages stay in the network. *}
  onebs :: "'a \<Rightarrow> bal \<rightharpoonup> (inst \<times> (inst \<Rightarrow> ('v\<times>bal) set))"
  -- {* the lowest instance, and the max vote per instance (an empty set or a singleton) or the decision *}
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
  crashed :: "'a \<Rightarrow> bool"

locale ampr1_ioa =
  fixes quorums::"'a set set" and leader :: "bal \<Rightarrow> 'a" and window :: nat
  -- {* @{term leader} determines the leader of a ballot. *}
begin

sublocale dsa:distributed_safe_at quorums ballot vote for ballot vote .

definition start_s where
  -- {* The initial state *}
  "start_s \<equiv> \<lparr>propCmd = {}, ballot = (\<lambda> a . 0), vote = (\<lambda> a i . Map.empty), 
    suggestion = \<lambda> i . Map.empty, twoas = \<lambda> i . Map.empty, onebs = \<lambda> a . Map.empty,
    inst_status = \<lambda> b . if b = 0 then Some Map.empty else None,
    log = \<lambda> a . Map.empty, lowest = \<lambda> a . 0, crashed = \<lambda> a . False\<rparr>"

definition start where "start \<equiv> {start_s}"
  
subsection {* The transitions *}

definition propose where
  "propose c r r' \<equiv> (r' = r\<lparr>propCmd := (propCmd r) \<union> {c}\<rparr>)"

definition join_ballot where
  "join_ballot a b s s' \<equiv>
    let i_info = \<lambda> i . dsa.acc_max (flip (vote s) i) a b
    in
      crashed s a = False
      \<and> b > (ballot s a)
      \<and> s' = s\<lparr>ballot := (ballot s)(a := b),
        onebs := (onebs s)(a := (onebs s a)(b \<mapsto> (lowest s a, i_info)))\<rparr>"
  
definition join_started_ballot where "join_started_ballot a b s s' \<equiv>
  crashed s a = False
  \<and> inst_status s b \<noteq> None (* this means the ballot is started *)
  \<and> ballot s a < b
  \<and> s' = s\<lparr>ballot := (ballot s)(a := b)\<rparr>"
  
definition max_vote where max_vote_def:
  "max_vote s i b q \<equiv> max_by_key (\<Union> a \<in> q . snd (the (onebs s a b)) i) snd"

definition sugg where sugg_def: "sugg s i b q \<equiv>
  let m = max_vote s i b q in if m = {} then None else Some (the_elem (fst ` m))"
  
definition joined where 
  -- {* q joined ballot b and all its members have info starting at least from instance i. *}
  "joined s q b i \<equiv> \<forall> a \<in> q .  case onebs s a b of Some (j,f) \<Rightarrow> j \<le> i  | None \<Rightarrow> False"
  
definition next_avail where
  "next_avail s a \<equiv> Min {i . log s a i = None}"

definition acquire_leadership where
  "acquire_leadership a q s s' \<equiv> let b = ballot s a in
    crashed s a = False
    \<and> leader b = a
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
    \<and> onebs s' = onebs s \<and> log s' = log s"
  
definition suggest where "suggest a i b v s s' \<equiv>
  crashed s a = False
  \<and> v \<in> propCmd s
  \<and> ballot s a = b
  \<and> i \<ge> next_avail s a
  \<and> i < next_avail s a + window
  \<and> suggestion s i b = None
  \<and> (case inst_status s b of Some f \<Rightarrow> f i = None | _ \<Rightarrow> False)
  \<and> s' = s\<lparr>suggestion := (suggestion s)(i := (suggestion s i)(b \<mapsto> v)),
      twoas := (twoas s)(i := (twoas s i)(b \<mapsto> v))\<rparr>"
  
definition do_vote where
  "do_vote a i v s s' \<equiv> let b = ballot s a in
    crashed s a = False
    \<and> i \<ge> lowest s a
    \<and> vote s a i b = None
    \<and> twoas s i b = Some v
    \<and> s' = s\<lparr>vote := (vote s)(a := (vote s a)(i := (vote s a i)(b := Some v)))\<rparr>"

definition chosen where
  "chosen s i v \<equiv> dsa.chosen (flip (vote s) i) v"

definition learn where
  "learn a i v s s' \<equiv>
    crashed s a = False
    \<and> chosen s i v
    \<and> s' = s\<lparr>log := (log s)(a := (log s a)(i := Some v))\<rparr>"

definition crash where
  -- {* Suggestions are erased. *}
  "crash a s s' \<equiv> \<exists> su . 
    (\<forall> i b . (leader b = a \<and> su i b = None) \<or> (leader b \<noteq> a \<and> su i b = suggestion s i b))
    \<and> s' = s\<lparr>suggestion := su, crashed := (crashed s)(a := True)\<rparr>"
  
definition recover where
  -- {* sets the ballot and the lowest instance. *}
  "recover a s s' \<equiv> 
    crashed s a = True
    \<and> (\<exists> q \<in> quorums . let m = Max {ballot s a | a . a \<in> q} in
      True
      \<and> s' = s\<lparr>ballot := (ballot s)(a := m),
          crashed := (crashed s)(a := False),
          lowest := (lowest s)(a := next_avail s (leader m) + window)\<rparr> )"
  
fun trans_rel where
  "trans_rel r (Propose c) r' = propose c r r'"
| "trans_rel r Internal r' = (
    (\<exists> a b . join_ballot a b r r')
    \<or> (\<exists> a i v . do_vote a i v r r')
    \<or> (\<exists> a i b v . suggest a i b v r r')
    \<or> (\<exists> a q . acquire_leadership a q r r')
    \<or> (\<exists> a b . join_started_ballot a b r r')
    \<or> (\<exists> a . crash a r r') )"
  | "trans_rel r (Learn a i vs) r' = (
    (\<exists> v . learn a i v r r' \<and> vs = [v])
    \<or> (\<exists> a . recover a r r') )"

lemma trans_cases:
  assumes "trans_rel r a r'"
  obtains 
  (propose) c where "propose c r r'"
| (learn) a i v where "learn a i v r r'"
| (join_ballot) a b where "join_ballot a b r r'"
| (do_vote) a i v where "do_vote a i v r r'"
| (suggest) a i b v where "suggest a i b v r r'"
| (acquire) a q where "acquire_leadership a q r r'"
| (join_started) a b where "join_started_ballot a b r r'"
| (recover) a where "recover a r r'"
| (crash) a where "crash a r r'"
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