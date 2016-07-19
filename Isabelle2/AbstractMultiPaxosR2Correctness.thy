theory AbstractMultiPaxosR2Correctness
imports AbstractMultiPaxosR1 AbstractMultiPaxosR2 Simulations
begin

print_locale ampr2_ioa

locale ampr2_proof = IOA + quorums quorums + ampr2_ioa quorums for
     quorums :: "'a set set" +
  fixes ampr2_ioa :: "(('v,'a,'l)ampr2_state, ('v,'a,'l)ampr1.action) ioa"
  and ampr1_ioa :: "(('v,'a,'l)ampr1_state, ('v,'a,'l)ampr1.action) ioa"
  defines "ampr2_ioa \<equiv> ioa" and "ampr1_ioa \<equiv> ampr1.ioa"
begin

definition ref_map where "ref_map s \<equiv> \<lparr>
  ampr1_state.propCmd = propCmd s,
  ampr1_state.ballot = ballot s,
  ampr1_state.vote = (\<lambda> i a . vote s a i),
  ampr1_state.suggestion = suggestion s,
  ampr1_state.onebs = onebs s,
  ampr1_state.learned = learned s,
  ampr1_state.leader = ampr2_state.leader s\<rparr>"

term "ampr1_ioa"
term "ampr2_ioa"

lemma "IOA.is_ref_map ref_map ampr2_ioa ampr1.ioa" oops

end