theory AbstractMultiPaxosR2Code
imports AbstractMultiPaxosR2
begin

definition n :: nat where "n \<equiv> 3"
  -- {* The number of processes *}

definition accs where "accs \<equiv> {1..n}"
  -- {* The set of acceptors *}

definition leader where "leader (b::nat) \<equiv> (b mod n) + 1"
                      
global_interpretation cq:card_quorums accs
  defines qs = "cq.quorums" and nas = "cq.nas"
apply (unfold_locales)
apply (simp add: accs_def n_def)
apply (simp add: accs_def)
done

global_interpretation ampr2_ioa qs leader
  defines ampr2_start = start
  and ampr2_join_ballot = join_ballot
  and ampr2_acquire_leadership = acquire_leadership
  and ampr2_suggest = suggest
  and ampr2_do_vote = do_vote
  and ampr2_learn = learn
  and ampr2_catch_up = catch_up
  .

export_code ampr2_start propose acc_max join_ballot
  ampr2_join_ballot ampr2_acquire_leadership
  ampr2_suggest ampr2_do_vote learn catch_up in Scala

value "ampr2_start::(nat, nat, nat) ampr2_state set"

end