theory MultiPaxos4Correctness
imports AbstractMultiPaxosFinfun MultiPaxos4 "../../IO-Automata/Simulations"
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

lemma card_accs: "fcard (accs nas) = nas"
  proof -
    have "\<And> n . card {1..<Suc n} = n" by simp
    thus ?thesis using accs_def_2
    by (metis eq_onp_same_args fcard.abs_eq finite_atLeastLessThan)
  qed

sublocale card_quorums "accs nas"
apply (unfold_locales)
by (metis card_accs fcard_fempty less_numeral_extra(3) 
  mp_ioa_correctness_axioms mp_ioa_correctness_def)

sublocale amp_ioa "accs nas" "{||}" "accs nas"
using mp_ioa_correctness_axioms
apply unfold_locales
apply (simp add: mp_ioa_correctness_def)
apply (induct rule:accs.induct)
apply auto
done

definition cmd_of_status where "cmd_of_status s \<equiv> case s of pending v \<Rightarrow> {|v|} | decided v \<Rightarrow> {|v|} | _ \<Rightarrow> {||}"

definition acc_prop_cmds where
  -- \<open>maps an acceptor to the state of locally seen commands\<close>
  "acc_prop_cmds s \<equiv> ((\<lambda> ss . fbind ss cmd_of_status) o (((op |`|) o$ finfun_apply) accs nas)) 
    o$ (inst_status o$ (node_states s))"

definition prop_cmds where
  -- \<open>The commands seen by at least one acceptor\<close>
  "prop_cmds s \<equiv> ffUnion 
    (finfun_fset_image (acc_prop_cmds s))"

definition prop_cmds_2 where
  "prop_cmds_2 s \<equiv> {c . \<exists> a i . a |\<in>| accs nas 
    \<and> (case (inst_status (node_states s $ a) $ i) of decided x \<Rightarrow> x = Cmd c 
      | pending x \<Rightarrow> x = Cmd c | _ \<Rightarrow> False)}"

lemma 
  assumes "\<And> a . finfun_default (inst_status (node_states s $ a)) = not_started"
  shows "finite (prop_cmds_2 s)" oops

lemma "prop_cmds mp_start = {||}"
proof -
  have "acc_prop_cmds mp_start = (K$ {||})" using init_nodes_state_2_is_finfun
apply(simp add:mp_start_def prop_cmds_def init_nodes_state_2_def acc_prop_cmds_def) oops

definition fwd_sim :: "'v mp_state \<Rightarrow> ('v cmd, nat) amp_state set" where
  "fwd_sim s \<equiv> 
    let last_bal_of = last_ballot o$ (node_states s); (* acc \<Rightarrow> inst \<Rightarrow> bal option *)
        last_vote_of = vote o$ (node_states s) (* acc \<Rightarrow> inst \<Rightarrow> bal option *)
    in {t . propCmd t = prop_cmds s
        \<and> amp_state.ballot t = ballot o$ (node_states s)
        \<and> (\<forall> i a . case (last_bal_of $ a $ i) of None \<Rightarrow> \<forall> b . amp_state.vote t $ i $ a $ b = None
            | Some b \<Rightarrow> \<forall> c . c > b \<longrightarrow> amp_state.vote t $ i $ a $ c = None 
                \<and> amp_state.vote t $ i $ a $ b = last_vote_of $ a $ i)}"

abbreviation amp_ioa_2 where 
  "amp_ioa_2 \<equiv> rename amp_ioa rn2"

abbreviation mp_ioa_2 where 
  "mp_ioa_2 \<equiv> rename mp_ioa rn1"


lemma "t \<in> fwd_sim mp_start \<Longrightarrow> amp_state.ballot t = (K$ None)" oops

theorem
  "is_forward_sim fwd_sim mp_ioa_2 amp_ioa_2" using mp_ioa_correctness_axioms init_acc
apply(auto simp add: is_forward_sim_def)
apply(auto simp add:fwd_sim_def rename_def amp_ioa_def amp_start_def mp_ioa_def mp_start_def
  mp_ioa_correctness_def init_acc_state_def)[1]
oops

end

end