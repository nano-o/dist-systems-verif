theory AbstractMultiPaxosR2Code
imports AbstractMultiPaxosR2
begin

definition n :: nat where "n \<equiv> 3"
  -- {* The number of processes *}

definition accs where "accs \<equiv> {1..n}"
  -- {* The set of acceptors *}

definition leader where "leader (b::nat) \<equiv> (b mod n) + 1"
                      
global_interpretation card_quorums accs
  defines qs = "quorums" and num_accs = "nas"
  -- {* @{term num_accs} is there just for code generation *}
apply (unfold_locales)
apply (simp add: accs_def n_def)
apply (simp add: accs_def)
done

global_interpretation ampr2_ioa qs leader
  defines ampr2_start = start (*and ampr2_acc_max = distributed_safe_at.acc_max*) 
  and ampr2_join_ballot = join_ballot
    and ampr2_acquire_leadership = acquire_leadership
  .

export_code ampr2_start in SML
export_code propose in SML
export_code acc_max in Scala
export_code join_ballot in Scala
export_code ampr2_join_ballot in Scala
export_code ampr2_acquire_leadership in Scala

value "ampr2_start::(nat, nat, nat) ampr2_state set"

end