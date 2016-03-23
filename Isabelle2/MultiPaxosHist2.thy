theory MultiPaxosHist2
imports 
  MultiPaxos3
begin

text {* A version of MultiPaxos with history variables added *}

text {* TODO: Prove that MultiPaxos refines it, preferably automatically *}

record 'v mph_state =
  mp_state :: "'v mp_state"
  vote_hist :: "inst \<Rightarrow>f acc \<Rightarrow>f bal \<Rightarrow>f 'v cmd option"

context mp_ioa begin

definition init_state :: "nat \<Rightarrow> 'v mph_state" where
  "init_state n \<equiv> \<lparr>
    mp_state = mp_start,
    vote_hist = K$ K$ K$ None \<rparr>"

end