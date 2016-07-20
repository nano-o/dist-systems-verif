theory AbstractMultiPaxosR2Code
imports AbstractMultiPaxosR1 "~~/src/HOL/Library/FinFun_Syntax"
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
  ballot :: "nat \<Rightarrow>f bal"

definition amp_start_2 where
  -- {* The initial state *}
  "amp_start_2 \<equiv> {\<lparr>amp_state_2.propCmd = {}, amp_state_2.ballot = (K$ 0)\<rparr>}"

text {* Fails. Should we lift to finfun? How? The problem seems to come from records *}
value "amp_start_2"

record test_rec = x :: "nat \<Rightarrow> bal"
record test_rec_2 = x :: "nat \<Rightarrow>f bal"
value "\<lparr>x = \<lambda> a . (0::nat)\<rparr>"
-- {* works *}
value "{\<lparr>x = \<lambda> a . (0::nat)\<rparr>}"
-- {* fails *}
value "{\<lparr>x = (K$ 0)\<rparr>}"
-- {* works *}
value "{(\<lambda> a::nat . (0::nat))}"
-- {* fails too *}
term List.coset
global_interpretation amp_ioa quorums leader 
  defines mytest = "amp_ioa.amp_start" .


export_code mytest in SML

end