section {* Definition of ballot arrays *}

theory BallotArrays
imports Main MaxByKey
begin

text {* A ballot array represents a history of execution of a Paxos-like algorithm, i.e. the current 
  ballot of every acceptor, and the history of all votes ever cast by every acceptor . *}

locale ballot_array =
  fixes quorums :: "'a set set"
  and ballot :: "'a \<Rightarrow> nat"
    -- {* The current ballot *}
  and vote :: "'a \<Rightarrow> nat \<rightharpoonup> 'v"
    -- {* The history of votes *}
begin

definition conservative where
  "conservative b \<equiv> \<forall> a1 . \<forall> a2 .
    let v1 = vote a1 b; v2 = vote a2 b in
      case v1 of Some x \<Rightarrow> (case v2 of Some y \<Rightarrow> x = y | None \<Rightarrow> True) | None \<Rightarrow> True"

definition conservative_array where
  -- {* A ballot array is conservative when all votes cast in a given ballot are the same. *}
  "conservative_array \<equiv> \<forall> b . conservative b"

text {* Here the @{term Max} is the one from @{text Lattices_Big} *}

definition proved_safe_at_abs_2 where
  -- {* Any value that has been proved safe at ballot b can be voted for in ballot b. *}
  "proved_safe_at_abs_2 q b v \<equiv>
    q \<in> quorums \<and> (\<forall> a \<in> q . ballot a \<ge> b) \<and>
    (if \<exists> a \<in> q . \<exists> b\<^sub>2 . b\<^sub>2 < b \<and> vote a b\<^sub>2 \<noteq> None
    then let votes = {(w,b\<^sub>2) . b\<^sub>2 < b \<and> (\<exists> a \<in> q . vote a b = Some w)}
      in v \<in> fst ` (max_by_key votes snd)
    else True)"

definition proved_safe_at_abs where
  -- {* Any value that has been proved safe at ballot b can be voted for in ballot b. *}
  "proved_safe_at_abs q b v \<equiv>
    q \<in> quorums \<and> (\<forall> a \<in> q . ballot a \<ge> b) \<and>
    (if \<exists> a \<in> q . \<exists> b\<^sub>2 . b\<^sub>2 < b \<and> vote a b\<^sub>2 \<noteq> None
    then let max_bal = Max {b\<^sub>2 . \<exists> a \<in> q . b\<^sub>2 < b \<and> vote a b\<^sub>2 \<noteq> None}
      in \<exists> a \<in> q . vote a max_bal = Some v
    else True)"

definition chosen_at where
  "chosen_at v b \<equiv> \<exists> q . q \<in> quorums \<and> (\<forall> a \<in> q . vote a b = (Some v))"

definition chosen where
  "chosen v \<equiv> \<exists> b . chosen_at v b"
  
definition choosable where
  -- {* A value is choosable at ballot b when there is a quorum such that any acceptor in
  this quorum that is past ballot b has voted for v. 
  In a Paxos execution, choosable is monotonically decreasing. *}
  "choosable v b \<equiv>
    \<exists> q . q \<in> quorums \<and> (\<forall> a \<in> q . ballot a > b \<longrightarrow> vote a b = Some v)"

definition safe_at where
  "safe_at v b \<equiv>
    \<forall> b2 . \<forall> v2 . ((b2 < b \<and> choosable v2 b2) \<longrightarrow> (v = v2))"

definition safe where
  "safe \<equiv> \<forall> b . \<forall> a . case vote a b of None \<Rightarrow> True | Some v \<Rightarrow> safe_at v b"
  
definition well_formed where
  "well_formed \<equiv> \<forall> a b . ballot a < b \<longrightarrow> vote a b = None"

end

end