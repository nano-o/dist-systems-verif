theory MultiPaxosCorrectness
imports AbstractMultiPaxos MultiPaxosHist
begin

definition pending_of_a where
  "pending_of_a s a \<equiv> fold (\<lambda> i r . case (pending s) $ a $ i of None \<Rightarrow> r | Some c \<Rightarrow> {|c|} |\<union>| r) 
    (finfun_to_list ((pending s) $ a)) {||}"

definition prop_cmp_of_mp where 
  "prop_cmp_of_mp s \<equiv> fold (\<lambda> a r . pending_of_a s a |\<union>| r) (finfun_to_list (pending s)) {||}"

abbreviation peal_3 where "peal_3 ff \<equiv> finfun_apply ((\<lambda> ff . finfun_apply ((\<lambda> ff . finfun_apply ff) o$ ff)) o$ ff)"

definition ref_map :: "'v mph_state \<Rightarrow> ('v cmd,nat) amp_state" where
  "ref_map s \<equiv> \<lparr>propCmd = prop_cmp_of_mp s, ballot = finfun_apply (ballot s), 
    vote = peal_3 (vote_hist s)\<rparr>"

end