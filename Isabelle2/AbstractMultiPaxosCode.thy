theory AbstractMultiPaxosCode
imports AbstractMultiPaxosR1
begin

print_locale amp_ioa

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

text {* That works *}
value qs

record amp_state_2 =
  propCmd :: "nat set"
  ballot :: "nat \<Rightarrow> bal"
  vote :: "inst \<Rightarrow> nat \<Rightarrow> bal \<rightharpoonup> nat"
  suggestion :: "inst \<Rightarrow> bal \<rightharpoonup> nat"
  onebs :: "nat \<Rightarrow> bal \<rightharpoonup> (inst \<rightharpoonup> (nat\<times>bal))"
  learned :: "nat \<Rightarrow> inst \<rightharpoonup> nat"
  leader_ :: "nat \<Rightarrow> bool"

definition amp_start_2 where
  -- {* The initial state *}
  "amp_start_2 \<equiv> {\<lparr>amp_state_2.propCmd = {}, amp_state_2.ballot = (\<lambda> a . 0), amp_state_2.vote = (\<lambda> i a . Map.empty), 
    amp_state_2.suggestion = \<lambda> i . Map.empty, amp_state_2.onebs = \<lambda> a . Map.empty, amp_state_2.learned = \<lambda> l . Map.empty,
    amp_state_2.leader_ = \<lambda> a . leader 0 = a\<rparr>}"

text {* Fails *}
value "amp_start_2"

global_interpretation amp_ioa quorums leader 
  defines mytest = "amp_ioa.amp_start" .


export_code mytest in SML

end