theory MultiPaxosCorrectness
imports AbstractMultiPaxos MultiPaxos4
begin

definition pending_of_a where
  "pending_of_a s a \<equiv> if (id s = a) then fold (\<lambda> i r . case (pending s) $ i of None \<Rightarrow> r | Some c \<Rightarrow> {|c|} |\<union>| r) 
    (finfun_to_list (pending s)) {||} else {||}"

definition prop_cmp_of_mp where 
  "prop_cmp_of_mp s \<equiv> (let state = node_states s in
    fold (\<lambda> a r . pending_of_a (state $ a) a |\<union>| r) (finfun_to_list (state)) {||})"

abbreviation peal_3 where "peal_3 ff \<equiv> finfun_apply ((\<lambda>ff. finfun_apply((\<lambda>ff. finfun_apply ff) o$ ff)) o$ ff)"

definition ballot_of_s where
  "ballot_of_s s \<equiv> (let state = node_states s in
    (\<lambda>a . ballot (state $ a)))"

definition vote_of_a where
  "vote_of_a s i b \<equiv> ((vote_hist s) $ i $ b)"

definition vote_of_s where
  "vote_of_s s \<equiv> (let state = node_states s in
    (\<lambda>i a b. vote_of_a (state $ a) i b))"

definition ref_map :: "'v mp_state \<Rightarrow> ('v cmd, nat) amp_state" where
  "ref_map s \<equiv> \<lparr>propCmd = prop_cmp_of_mp s, ballot = (ballot_of_s s), 
    vote = (vote_of_s s)\<rparr>"

locale refineSim = IOA + mp_ioa + abs_multi_paxos +
  fixes mpaxos_ioa apaxos_ioa
  defines "mpaxos_ioa \<equiv> p_ioa" and "apaxos_ioa \<equiv> amp_ioa"
begin
lemma "is_ref_map ref_map mpaxos_ioa apaxos_ioa"


end