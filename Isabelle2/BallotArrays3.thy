section {* Definition of ballot arrays *}

theory BallotArrays3
imports Main LinorderOption
begin

locale ballot_array =
  -- {* @{typ 'a} is the type of acceptors *}
  fixes ballot :: "'a \<Rightarrow> nat"
  and vote :: "'a \<Rightarrow> nat \<Rightarrow> 'v option"
  and quorums :: "'a set set"
begin

definition conservative where
  "conservative b \<equiv> \<forall> a1 . \<forall> a2 .
    let v1 = vote a1 b; v2 = vote a2 b in 
      case v1 of Some x \<Rightarrow> (case v2 of Some y \<Rightarrow> x = y | None \<Rightarrow> True) | None \<Rightarrow> True"

definition conservative_array where
  "conservative_array \<equiv> \<forall> b . conservative b"

text {* Here the @{term Max} is the one from @{text Lattices_Big} *}
    
definition max_voted_round_q where
  "max_voted_round_q q bound \<equiv> 
    if \<exists> b a . a \<in> q \<and> b \<le> bound \<and> vote a b \<noteq> None
    then Some (Max {b . \<exists> a . a \<in> q \<and> b \<le> bound \<and> vote a b \<noteq> None})
    else None"
 
definition max_vote where 
  "max_vote q bound \<equiv>
    case max_voted_round_q q bound of
      None \<Rightarrow> None
    | Some b \<Rightarrow> 
        let max_voter = (SOME a . a \<in> q \<and> vote a b \<noteq> None)
        in vote max_voter b"

definition proved_safe_at where
  "proved_safe_at Q b v \<equiv>
    (case b of 0 \<Rightarrow> True
    | Suc c \<Rightarrow> Q \<in> quorums \<and> (\<forall> a \<in> Q . ballot a \<ge> b) \<and>
      (case (max_vote Q c) of (* note that here c is b-1 *)
        None \<Rightarrow> True
      | Some v' \<Rightarrow> v = v'))"

definition chosen_at where
  "chosen_at v b \<equiv> \<exists> q . q \<in> quorums \<and> (\<forall> a . a \<in> q \<longrightarrow> (vote) a b = (Some v))"

definition chosen where
  "chosen v \<equiv> \<exists> b . chosen_at v b"
  
definition choosable where
  "choosable v b \<equiv>
    \<exists> q . q \<in> quorums \<and> (\<forall> a . a \<in> q \<longrightarrow> (
      ballot a > b \<longrightarrow> vote a b = Some v))"

definition safe_at where
  "safe_at v b \<equiv>
    (\<forall> b2 . \<forall> v2 .
      ((b2 < b \<and> choosable v2 b2) \<longrightarrow> (v = v2)))"

definition safe where
  "safe \<equiv> \<forall> b . \<forall> a . case vote a b of None \<Rightarrow> True | Some v \<Rightarrow> safe_at v b"
  
definition well_formed where
  "well_formed \<equiv> \<forall> a b . ballot a < b \<longrightarrow> vote a b = None"

end

end