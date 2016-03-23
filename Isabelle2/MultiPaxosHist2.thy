theory MultiPaxosHist2
imports 
  MultiPaxos3
begin

text {* A version of MultiPaxos with history variables added *}

text {* TODO: Prove that MultiPaxos refines it, preferrably automatically *}

record 'v mph_state =
  mp_state :: "'v mp_state"
  vote_hist :: "inst \<Rightarrow>f acc \<Rightarrow>f bal \<Rightarrow>f 'v cmd option"

definition init_state :: "acc fset \<Rightarrow> 'v mph_state" where
  "init_state accs \<equiv> \<lparr>
    mp_state = MultiPaxos3.init_state accs,
    vote_hist = K$ K$ K$ None \<rparr>"

end