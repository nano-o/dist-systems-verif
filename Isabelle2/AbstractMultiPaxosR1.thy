theory AbstractMultiPaxosR1
imports  IOA BallotArrays DistributedSafeAt Paxos_Sig
begin

record ('v,'a) ampr1_state =
  propCmd :: "'v set"
  ballot :: "'a \<Rightarrow> bal"
  vote :: "'a \<Rightarrow> inst \<Rightarrow> bal \<rightharpoonup> 'v"
  suggestion :: "inst \<Rightarrow> bal \<rightharpoonup> 'v"
    -- {* @{term suggestion} is part of the local state of leaders. *}
  twoas :: "inst \<Rightarrow> bal \<rightharpoonup> 'v"
  -- {* suggestion is forgotten upon a crash, but the twoa messages stay in the network. *}
  onebs :: "'a \<Rightarrow> bal \<rightharpoonup> (inst \<Rightarrow> ('v\<times>bal) set)"
  inst_status :: "bal \<rightharpoonup> inst \<rightharpoonup> 'v"
  -- {* @{term inst_status} is set upon acquiring leadership; if @{term "inst_status s b = Some m"}, them @{term "m i = None"} means that 
  all values are safe, and @{term "m i = Some v"} means that only @{term v} is known safe. *}
  log :: "'a \<Rightarrow> inst \<Rightarrow> 'v option"
  -- {* The log is there to transfer it to replicas who need to catch up. *}
  crashed :: "'a \<Rightarrow> bool"

locale ampr1_ioa =
  fixes quorums::"'a set set" and leader :: "bal \<Rightarrow> 'a"
  -- {* @{term leader} determines the leader of a ballot. *}
begin

sublocale dsa:distributed_safe_at quorums ballot vote for ballot vote .

definition start_s where
  -- {* The initial state *}
  "start_s \<equiv> \<lparr>propCmd = {}, ballot = (\<lambda> a . 0), vote = (\<lambda> a i . Map.empty), 
    suggestion = \<lambda> i . Map.empty, twoas = \<lambda> i . Map.empty, onebs = \<lambda> a . Map.empty,
    inst_status = \<lambda> b . if b = 0 then Some Map.empty else None,
    log = \<lambda> a . Map.empty, crashed = \<lambda> a . False\<rparr>"

definition start where "start \<equiv> {start_s}"
  
subsection {* The transitions *}

definition propose where
  "propose c r r' \<equiv> (r' = r\<lparr>propCmd := (propCmd r) \<union> {c}\<rparr>)"

definition join_ballot where
  "join_ballot a b s s' \<equiv>
    let onebs' = \<lambda> i . dsa.acc_max (flip (vote s) i) a b
    in
      crashed s a = False
      \<and> b > (ballot s a)
      \<and> s' = s\<lparr>ballot := (ballot s)(a := b),
        onebs := (onebs s)(a := (onebs s a)(b \<mapsto> onebs'))\<rparr>"
  
definition join_started_ballot where "join_started_ballot a b s s' \<equiv>
  crashed s a = False
  \<and> inst_status s b \<noteq> None 
  \<and> ballot s a < b
  \<and> s' = s\<lparr>ballot := (ballot s)(a := b)\<rparr>"
  
definition max_vote where max_vote_def:
  "max_vote s i b q \<equiv> max_by_key (\<Union> a \<in> q . the (onebs s a b) i) snd"

definition sugg where sugg_def: "sugg s i b q \<equiv>
  let m = max_vote s i b q in if m = {} then None else Some (the_elem (fst ` m))"
  
definition joined where "joined s q b \<equiv> \<forall> a \<in> q . onebs s a b \<noteq> None"
  
definition acquire_leadership where
  -- {* Upon acquiring leadership, the leader makes suggestions in an
  arbitrary set of instances which have a unique safe value. *}
  "acquire_leadership a q s s' \<equiv> let b = ballot s a in
    crashed s a = False
    \<and> leader b = a
    \<and> q \<in> quorums
    \<and> joined s q b
    \<and> inst_status s b = None
    \<and> inst_status s' = (inst_status s)(b := Some (\<lambda> i . sugg s i b q))
    \<and> (\<forall> i . suggestion s' i = (suggestion s i)(b := sugg s i b q) 
      \<or> suggestion s' i = (suggestion s i))
    \<and> (\<forall> i . twoas s' i = (twoas s i)(b := suggestion s' i b))
    \<and> propCmd s' = propCmd s \<and> ballot s' = ballot s \<and> vote s' = vote s 
    \<and> onebs s' = onebs s \<and> log s' = log s"
  
definition suggest where "suggest a i b v s s' \<equiv>
  crashed s a = False
  \<and> v \<in> propCmd s
  \<and> ballot s a = b
  \<and> suggestion s i b = None
  \<and> (case inst_status s b of Some f \<Rightarrow> f i = None | _ \<Rightarrow> False)
  \<and> s' = s\<lparr>suggestion := (suggestion s)(i := (suggestion s i)(b \<mapsto> v)),
    twoas := (twoas s)(i := (twoas s i)(b \<mapsto> v))\<rparr>"
  
definition do_vote where
  "do_vote a i v s s' \<equiv> let b = ballot s a in
    crashed s a = False
    \<and> vote s a i b = None
    \<and> twoas s i b = Some v
    \<and> s' = s\<lparr>vote := (vote s)(a := (vote s a)(i := (vote s a i)(b := Some v)))\<rparr>"

definition chosen where
  "chosen s i v \<equiv> dsa.chosen (flip (vote s) i) v"

definition learn where
  "learn a i v s s' \<equiv>
    crashed s a = False
    \<and> s' = s\<lparr>log := (log s)(a := (log s a)(i := Some v))\<rparr>
    \<and> chosen s i v"
  
definition crash where
  "crash a s s' \<equiv> \<exists> su . 
    (\<forall> i b . (leader b = a \<and> su i b = None) \<or> (leader b \<noteq> a \<and> su i b = suggestion s i b))
    \<and> s' = s\<lparr>suggestion := su, crashed := (crashed s)(a := True)\<rparr>"
  
definition recover where
  -- {* Download the log from a2. Models recovery after a crash; ballot is persistent.
    We increment the ballot if we see we're the leader, to make sure not to produce inconsistent suggestions. 
    TODO: maybe split in two: first set the ballot, then transfer. *}
  "recover a1 a2 i vs s s' \<equiv> 
    crashed s a1 = True
    \<and> (\<forall> j . i \<le> j \<and> j < i+(length vs) \<longrightarrow> log s a2 j = Some (vs!(j-i+1)))
    \<and> s' = s\<lparr>ballot := (ballot s)(a1 := (let b = ballot s a1 in
        if leader b = a1 then Suc b else b)),
      log := (log s)(a1 := (log s a2)),
      crashed := (crashed s)(a1 := False)\<rparr>"
  
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
    (* \<or> (\<exists> a\<^sub>1 a\<^sub>2 . recover a\<^sub>1 a\<^sub>2 i vs r r') *) )"

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
(* | (recover) a\<^sub>1 a\<^sub>2 i vs where "recover a\<^sub>1 a\<^sub>2 i vs r r'" *)
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