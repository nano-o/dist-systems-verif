theory AbstractMultiPaxosR3_Code
imports AbstractMultiPaxosR3
begin

definition n :: nat where "n \<equiv> 3"
  -- {* The number of processes *}

definition accs where "accs \<equiv> {1..n}"
  -- {* The set of acceptors *}

definition leader where "leader (b::nat) \<equiv> (b mod n) + 1"
  
definition next_bal :: "nat \<Rightarrow> nat \<Rightarrow> nat" where "next_bal b a \<equiv> 
  (b div n + 1) * n + a"
  
global_interpretation cq:card_quorums accs
  defines qs = "cq.quorums" and nas = "cq.nas"
  apply (unfold_locales)
   apply (simp add: accs_def n_def)
  apply (simp add: accs_def)
  done

global_interpretation my_amp_r3:amp_r3 leader next_bal accs qs 
  defines start = my_amp_r3.global_start
    and trans = my_amp_r3.trans_rel
    and propose = my_amp_r3.propose
    and try_acquire_leadership = my_amp_r3.try_acquire_leadership
    and process_msg = my_amp_r3.process_msg
    and local_start = my_amp_r3.local_start
    and receive_fwd = my_amp_r3.receive_fwd
    and receive_1a = my_amp_r3.receive_1a
    and do_2a = my_amp_r3.do_2a
  .

subsection {* Code generation *}

export_code local_start propose try_acquire_leadership process_msg checking Scala

end