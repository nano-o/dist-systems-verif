theory MultiPaxosCorrectness2
imports AbstractMultiPaxos MultiPaxos3 "../../IO-Automata/Simulations"
begin
datatype 'v Common_actions =
  Propose acc "'v cmd"
| Learn acc inst "'v cmd"
| Vote acc acc "acc fset" inst bal "'v cmd"(* leader voter *)
| Join acc acc bal (* leader acceptor *)
| Receive_fwd acc acc 'v
| Send_1as acc
| Receive_1b acc acc "inst \<Rightarrow>f ('v cmd \<times> bal) option" bal
| Receive_2b acc acc inst bal "'v cmd"

text {* Renaming amp *} 
fun rn2 where
  "rn2 (Common_actions.Propose a v) = Some (amp_action.Propose v)"
| "rn2 (Common_actions.Learn a i v) = Some (amp_action.Learn i v a)"
| "rn2 (Common_actions.Join l a b) = Some (amp_action.JoinBallot a b)"
| "rn2 (Common_actions.Vote l a q i b v) = Some (amp_action.Vote a q i v)"
| "rn2 _ = None"

text {* Renaming mp *}
fun rn1 where 
  "rn1 (Common_actions.Propose a v) = Some (mp_action.Propose a v)"
| "rn1 (Common_actions.Learn a i v) = Some (mp_action.Learn a i v)"
| "rn1 (Common_actions.Join l a b) = Some (mp_action.Receive_1a_send_1b l a b)"
| "rn1 (Common_actions.Vote l a q i b v) = Some (mp_action.Receive_2a_send_2b l a i b v)"
| "rn1 (Common_actions.Receive_fwd a1 a2 v) = Some (mp_action.Receive_fwd a1 a2 v)"
| "rn1 (Common_actions.Send_1as l) = Some (mp_action.Send_1as l)"
| "rn1 (Common_actions.Receive_1b a1 a2 vs b) = Some (mp_action.Receive_1b a1 a2 vs b)"
| "rn1 (Common_actions.Receive_2b a1 a2 i b v) = Some (mp_action.Receive_2b a1 a2 i b v)"

locale mp_ioa_correctness = mp_ioa +
  assumes "nas > 0"
begin

definition mp_quorums where
  "mp_quorums \<equiv> Abs_fset {q . 2 * fcard q > nas \<and> (\<forall> a . a |\<in>| q \<longrightarrow> a < nas) }"

lemma  
  assumes "q |\<in>| mp_quorums"
  shows "2 * fcard q > nas" using assms
oops

sublocale amp_ioa "accs nas" "{||}" "accs nas"
using mp_ioa_correctness_axioms
apply unfold_locales
apply (simp add: mp_ioa_correctness_def)
apply (induct rule:accs.induct)
apply auto
done

sublocale quorums "accs nas" "mp_quorums"
using mp_ioa_correctness_axioms oops

definition pending_of_a where
  "pending_of_a s \<equiv>  
    fold (\<lambda> i r . case (pending s) $ i of None \<Rightarrow> r | Some c \<Rightarrow> {|c|} |\<union>| r) 
      (finfun_to_list ((pending s))) {||}"

definition prop_cmp_of_mp where 
  "prop_cmp_of_mp s \<equiv> 
    fold (\<lambda> a r . pending_of_a (node_states s $ a) |\<union>| r)
      (finfun_to_list (node_states s)) {||}"

definition fwd_sim :: "'v mp_state \<Rightarrow> ('v cmd, nat) amp_state set" where
  "fwd_sim s \<equiv> 
    let last_bal_of = \<lambda> a i . last_ballot ((node_states s) $ a) $ i;
        last_vote_of = \<lambda> a i . vote ((node_states s) $ a) $ i
    in
      {t . propCmd t = prop_cmp_of_mp s 
        \<and> amp_state.ballot t = 
          (let f = (finfun_apply ((\<lambda> acc_s . ballot acc_s) o$ (node_states s)))
          in (\<lambda> a . if (0 < a \<and> a \<le> nas) then f a else None))
        \<and> (\<forall> i a . case (last_bal_of a i) of None \<Rightarrow> \<forall> b . amp_state.vote t i a b = None
            | Some b \<Rightarrow> \<forall> c . c > b \<longrightarrow> amp_state.vote t i a c = None 
                \<and> amp_state.vote t i a b = last_vote_of a i)}"

abbreviation amp_ioa_2 where 
  "amp_ioa_2 \<equiv> rename amp_ioa rn2"

abbreviation mp_ioa_2 where 
  "mp_ioa_2 \<equiv> rename mp_ioa rn1"

theorem
  "is_forward_sim fwd_sim mp_ioa_2 amp_ioa_2" using mp_ioa_correctness_axioms init_acc
apply(auto simp add: is_forward_sim_def)
apply(auto simp add:fwd_sim_def rename_def amp_ioa_def amp_start_def mp_ioa_def mp_start_def
  mp_ioa_correctness_def init_acc_state_def)[1]



end

end