theory AbstractMultiPaxosR3Code
imports AbstractMultiPaxosR3 "~~/src/HOL/Library/FinFun_Syntax"
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
  defines ampr2_start = start and ampr2_propose = propose and ampr2_acc_max = acc_max 
  and ampr2_max_by_key = max_by_key and ampr2_join_ballot = join_ballot
  and ampr2_suggest = suggest and ampr2_vote = do_vote and ampr2_learn = learn
  and ampr2_catch_up = catch_up and ampr2_acquire_leadership = acquire_leadership.

export_code ampr2_start ampr2_propose ampr2_max_by_key ampr2_acc_max ampr2_join_ballot 
  ampr2_suggest ampr2_vote ampr2_catch_up ampr2_acquire_leadership ampr2_learn in Scala

value "ampr2_start::(nat, nat, nat) ampr2_state set"

end