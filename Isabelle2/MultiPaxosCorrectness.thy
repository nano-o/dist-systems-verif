theory MultiPaxosCorrectness
imports AbstractMultiPaxos MultiPaxosHist2
begin

definition pending_of_a where
  "pending_of_a s \<equiv>  
    fold (\<lambda> i r . case (pending s) $ i of None \<Rightarrow> r | Some c \<Rightarrow> {|c|} |\<union>| r) 
      (finfun_to_list ((pending s))) {||}"

definition prop_cmp_of_mp where 
  "prop_cmp_of_mp s \<equiv> 
    fold (\<lambda> a r . pending_of_a (node_states s $ a) |\<union>| r)
      (finfun_to_list (node_states s)) {||}"

abbreviation peal_3 where 
  "peal_3 ff \<equiv> finfun_apply ((\<lambda> ff . finfun_apply ((\<lambda> ff . finfun_apply ff) o$ ff)) o$ ff)"

definition ref_map :: "'v mph_state \<Rightarrow> ('v cmd, nat) amp_state" where
  "ref_map s \<equiv> \<lparr>propCmd = prop_cmp_of_mp (mp_state s), 
    ballot = finfun_apply ((\<lambda> acc_s . ballot acc_s) o$ (node_states (mp_state s))), 
    vote = peal_3 (vote_hist s)\<rparr>"

end