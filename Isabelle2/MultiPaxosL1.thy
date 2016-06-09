section {* A first refinement of AbstractMultiPaxos. *}

theory MultiPaxosL1    
imports "../../IO-Automata/IOA_Automation" BallotArrays3
begin                   


record ('v,'a) mp_state =
  propCmd :: "'v set"
  ballot :: "'a \<Rightarrow> nat option"
  vote :: "nat \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> 'v option"
  suggestion :: "nat \<Rightarrow> nat \<Rightarrow> 'v option"

locale mp1 = IOA + fixes acceptors :: "'a set" and quorums :: "'a set set"
  fixes learners :: "'l set"
  and is_leader :: "'a \<Rightarrow> nat \<Rightarrow> bool"
  assumes "\<And> i . \<exists>! a . is_leader a i"
begin

datatype ('v,'aa,'ll) mp_action =
  Propose 'v
| Learn nat 'v 'll
| Vote 'aa nat 'v
  -- {* an acceptor votes in an instance *}
| JoinBallot 'aa nat
| Suggest 'aa 'v nat nat "'aa set"

definition mp_asig where
  "mp_asig \<equiv>
    \<lparr> inputs = { Propose c | c . True},
      outputs = { Learn i v l | i v l . l \<in> learners},
      internals = {Vote a i b | a i b . a \<in> acceptors} \<union> {JoinBallot a b | a b . a \<in> acceptors}
        \<union> {Suggest a v i b q | a v i b q . a \<in> acceptors \<and> q \<in> quorums}\<rparr>"

definition mp_start where
  -- {* The initial state *}
  "mp_start \<equiv> {\<lparr>propCmd = {}, ballot = (\<lambda> a . None), vote = (\<lambda> i a b . None), 
    suggestion = (\<lambda> i b . None) \<rparr>}"

subsection {* The transitions *}

definition propose where
  "propose c r r' \<equiv> (r' = r\<lparr>propCmd := (propCmd r) \<union> {c}\<rparr>)"

definition join_ballot where
  "join_ballot a b s s' \<equiv> 
    a \<in> acceptors \<and> Some b > (ballot s a) \<and> s' = s\<lparr>ballot := (ballot s)(a := Some b)\<rparr>"

abbreviation proved_safe_at where 
  -- {* v is proved safe in instance i at ballot b by quorum q *}
  "proved_safe_at s i q b v \<equiv> ballot_array.proved_safe_at  (vote s i) q b v"

definition suggest where
  "suggest s s' a v i b q \<equiv> 
      v \<in> propCmd s
    \<and> is_leader a b
    \<and> ballot s a = Some b
    \<and> suggestion s i b = None
    \<and> proved_safe_at s i q b v
    \<and> q \<in> quorums 
    \<and> (\<forall> a2 \<in> q . ballot s a2 \<ge> Some b)
    \<and> s' = s\<lparr>suggestion := (suggestion s)(i := (suggestion s i)(b := Some v))\<rparr>"

definition do_vote where
  "do_vote a i v s s' \<equiv> a \<in> acceptors \<and> (case ballot s a of None \<Rightarrow> False 
    | Some b \<Rightarrow> suggestion s i b = Some v
        \<and> s' = s\<lparr>vote := (vote s)(i := (vote s i)(a := (vote s i a)(b := Some v)))\<rparr>)"

abbreviation chosen where 
  "chosen s i v \<equiv> ballot_array.chosen (vote s i) quorums v"

definition learn where
  "learn l i v s s' \<equiv> chosen s i v \<and> s = s'"

fun mp_trans_rel  where
  "mp_trans_rel r (Propose c) r' = propose c r r'"
| "mp_trans_rel r (JoinBallot a b) r' = join_ballot a b r r'"
| "mp_trans_rel r (Vote a i v) r' = do_vote a i v r r'"
| "mp_trans_rel r (Learn i v l) r' = learn l i v r r'"
| "mp_trans_rel r (Suggest a v i b q) r' = suggest r r' a v i b q"

definition mp_trans where
  "mp_trans \<equiv> { (r,a,r') . mp_trans_rel r a r'}"

subsection {* The I/O-automaton *}

definition mp_ioa where
  "mp_ioa \<equiv> \<lparr>ioa.asig = mp_asig, start = mp_start, trans = mp_trans\<rparr>"

lemmas simps = mp_ioa_def mp_asig_def mp_start_def mp_trans_def learn_def suggest_def 
  join_ballot_def propose_def do_vote_def

end

end 