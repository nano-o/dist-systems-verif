theory MultiPaxosL1Correctness
imports MultiPaxosL1 AbstractMultiPaxos7 "../../IO-Automata/Simulations"
begin

term "amp_ioa.amp_ioa"

term "mp1.mp_ioa"

locale l1correctness = mp1
begin

interpretation amp: amp_ioa acceptors quorums learners .

fun rn where 
  "rn (Propose v) = Some (amp.Propose v)"
| "rn (Learn i v l) = Some (amp.Learn i v l)"
| "rn (Vote a q i v) = Some (amp.Vote a q i v)"
| "rn (JoinBallot a i) = Some (amp.JoinBallot a i)"
| "rn (Suggest a v i b q) = None"

definition amp_ioa_2 where
  "amp_ioa_2 \<equiv> rename amp.amp_ioa rn"

lemma "traces mp_ioa \<subseteq> traces amp_ioa_2" oops

end


end
