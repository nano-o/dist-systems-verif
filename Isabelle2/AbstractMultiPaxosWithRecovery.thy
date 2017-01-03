theory AbstractMultiPaxosWithRecovery
imports  IOA BallotArrays Paxos_Sig
begin                          

text {*
An abstraction of a MultiPaxos in which a process can crash, loose its state, and rejoin the protocol.
\<^item> There is an integer "lookahead" such that no process makes a proposition at instance i before
all instances lower or equal than i-lookahead-1 are decided.
\<^item> Process have an integer variable @{term "lowest"}, and they do not participate in any instance
lower that @{term "lowest"}.
\<^item> Let @{term "instance_bound"} be the largest instance such that all lower instances and itself are decided.
A process recovering from a crash computes an upper bound on @{term "instance_bound"} and sets @{term "lowest"} to that upper bound.
It can then join any ballot, since no promises may have been made in instances higher than @{term "instance_bound"}
\<^item> Ghost variables are added to keep track of the state lost during a crash, 
and to make local ballots always increasing: above @{term "instance_bound"}, a local ballot is always 0.

About the abstraction:
\<^item> The local state of processes is mostly the same in both the abstract and the implementation.
\<^item> The abstraction uses predicates on the local states of processes that are monotonic, 
and take action when a predicate becomes true.
\<^item> In a distributed implementation, read the distributed state piece by piece asynchronously. If action is taken,
it can also be taken if the state was read atomically at the same point in the abstract version.

*}
  
section {* Definition of the Abstract MultiPaxos I/O-automaton *}

subsection {* State and actions *}

record ('v,'a) ampr_state =
  propCmd :: "'v set"
  ballot :: "'a \<Rightarrow> bal"
  vote :: "'a \<Rightarrow> bal \<Rightarrow> inst \<Rightarrow> 'v option"
  suggestion :: "bal \<Rightarrow> inst \<Rightarrow> 'v option"
  lowest :: "'a \<Rightarrow> inst"
  log :: "'a \<Rightarrow> inst \<Rightarrow> 'v option"
  ghost_ballot :: "'a \<Rightarrow> inst \<Rightarrow> bal"
  ghost_vote :: "'a \<Rightarrow> bal \<Rightarrow> inst \<Rightarrow> 'v option"

locale ampr_ioa =
  fixes quorums::"'a set set" and lookahead :: "nat"
  -- {* @{term "lookahead+1"} instances can be run in parallel. *}
begin
  
definition is_learned_by_set where "is_learned_by_set l i q \<equiv> \<forall> a \<in> q . l a i \<noteq> None"

definition learned_by_quorum_consec where 
  "learned_by_quorum_consec l \<equiv> {i . \<forall> j \<le> i . \<exists> q \<in> quorums . is_learned_by_set l j q}"

definition instance_bound where "instance_bound l \<equiv> 
  if learned_by_quorum_consec l \<noteq> {}
  then Max (learned_by_quorum_consec l) + lookahead + 1
  else lookahead"
  -- {* No instance greater than that can have any vote. *}
  
definition start where
  -- {* The initial state *}
  "start \<equiv> {\<lparr>propCmd = {}, ballot = (\<lambda> a . 0), vote = (\<lambda> a b i . None),
    suggestion = \<lambda> b i . None,
    lowest = \<lambda> a . 0, log = \<lambda> a i . None, 
    ghost_ballot = (\<lambda> a i . 0), ghost_vote = (\<lambda> a b i . None)\<rparr>}"

subsection {* The transitions *}

definition propose where
  "propose c r r' \<equiv> (r' = r\<lparr>propCmd := (propCmd r) \<union> {c}\<rparr>)"

definition join_ballot where
  "join_ballot a b s s' \<equiv>
    b > (ballot s a) \<and> s' = s\<lparr>ballot := (ballot s)(a := b), 
      ghost_ballot := (ghost_ballot s)(a :=
        (\<lambda> i . if (ghost_ballot s a i) \<le> b \<and> instance_bound (log s) \<ge> i 
          then b else ghost_ballot s a i))\<rparr>"
  -- {* Note that we increase the ballot only below @{term instance_bound}.
  Also, it does not hurt to increase the ghost ballot below lowest because no action 
  will ever be taken again in those instances. *}

interpretation ba:ballot_array quorums ballot vote for ballot vote .

abbreviation ba_vote where "ba_vote s i \<equiv> \<lambda> a b . vote s a b i"
abbreviation ghost_ba_vote where "ghost_ba_vote s i \<equiv> \<lambda> a b . ghost_vote s a b i"

abbreviation proved_safe_at where
  -- {* v is proved safe in instance i at ballot b by quorum q *}
  "proved_safe_at s b i q v \<equiv> 
    ba.proved_safe_at_abs (ballot s) (ba_vote s i) q b v
    \<and> (\<forall> a \<in> q . i \<ge> lowest s a)"

abbreviation conservative_at where
  "conservative_at s i \<equiv> ballot_array.conservative_array (ba_vote s i)"

definition bounded where "bounded s \<equiv> (* where is this used? *)
  \<forall> a b i . (vote s a b i \<noteq> None \<and> i > lookahead)
    \<longrightarrow> (i-lookahead-1) \<in> learned_by_quorum_consec (log s)"
  -- {* New votes cannot be cast in instance i before instances lower than @{term "i-lookahead"} 
  have all been completed by a quorum of acceptors. *}

definition suggest where
  "suggest b i q v s s' \<equiv>
    suggestion s b i = None
    \<and> v \<in> propCmd s
    \<and> proved_safe_at s b i q v
    \<and> (\<forall> a \<in> q . i \<ge> lowest s a)
    \<and> (i-lookahead-1) \<in> learned_by_quorum_consec (log s)
    \<and> s' = s\<lparr>suggestion := (suggestion s)(b := (suggestion s b)(i := Some v))\<rparr>"
 
definition do_vote where
  "do_vote a i v s s' \<equiv> let b = ballot s a in
        suggestion s b i = Some v
        \<and> i \<ge> lowest s a
        \<and> vote s a b i = None
        \<and> s' = s\<lparr>vote := (vote s)(a := (vote s a)(b := (vote s a b)(i := Some v))),
            ghost_vote := (ghost_vote s)(a := (ghost_vote s a)(b := (ghost_vote s a b)(i := Some v)))\<rparr>"

abbreviation chosen where
  "chosen s i v \<equiv> ba.chosen (ba_vote s i) v"
  
abbreviation ghost_chosen where
  "ghost_chosen s i v \<equiv> ba.chosen (ghost_ba_vote s i) v"

definition learn where
  "learn a i vs s s' \<equiv> 
    (\<forall> j \<in> {0..<length vs} . chosen s (i+j) (vs!j))
    \<and> s' = s\<lparr>log := (log s)(a :=
        (\<lambda> j . if j \<in> {i..<i+length vs} then Some (vs!(j-i)) else log s a j)), 
        ghost_ballot := (\<lambda> a .
          (\<lambda> i . if i \<in> {instance_bound (log s)<..instance_bound (log s')}
            then ballot s a else ghost_ballot s a i))\<rparr>"

definition learned_by_one where 
  "learned_by_one l q \<equiv> {i . \<exists> a \<in> q . l a i \<noteq> None}"
  
definition safe_instance where 
  "safe_instance l q \<equiv>
    if learned_by_one l q \<noteq> {} then Max (learned_by_one l q) + lookahead + 2 else lookahead + 1"
  
definition crash where
  -- {* Why reset things here? Wouldn't it be sufficient to set lowest? *}
  "crash a q s s' \<equiv> q \<in> quorums \<and> a \<notin> q \<and> (
    let  low = safe_instance (log s) q
    in (\<exists> new_log b .
      (\<forall> i v . (new_log i = Some v) = (\<exists> a \<in> q . log s a i = Some v))
      \<and> s' = s\<lparr>vote := (vote s)(a := \<lambda> b i . None), ballot := (ballot s)(a := b),
        lowest := (lowest s)(a := low), log := (log s)(a := new_log),
        ghost_ballot := (\<lambda> a . (* The instance bound might increase as a result of the crashed process learning more than it had before the crash. *)
          (\<lambda> i . if i \<in> {instance_bound (log s)<..instance_bound (log s')}
            then ballot s' a else ghost_ballot s a i))\<rparr> ))"

fun trans_rel where
  "trans_rel r (Propose c) r' = propose c r r'"
| "trans_rel r Internal r' = (
    (\<exists> a b . join_ballot a b r r')
    \<or> (\<exists> a i v . do_vote a i v r r')
    \<or> (\<exists> b i q v . suggest b i q v r r')
    \<or> (\<exists> a q . crash a q r r') )"
| "trans_rel r (Learn a i vs) r' = learn a i vs r r'"

lemma trans_cases:
  assumes "trans_rel r a r'"
  obtains
  (propose) c where "propose c r r'"
| (learn) a i vs where "learn a i vs r r'"
| (join_ballot) a b where "join_ballot a b r r'"
| (crash) a q where "crash a q r r'"
| (do_vote) a i v where "do_vote a i v r r'"
| (suggest) b i q v where "suggest b i q v r r'"
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