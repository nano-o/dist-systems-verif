theory Log
imports Main
begin

fun largestinseq_carry :: "nat \<Rightarrow> (nat \<times> 'b) list \<Rightarrow> nat" where
"largestinseq_carry x [] = x" |  
"largestinseq_carry x ((y,z) # xs) = (if (y=x+1) then (largestinseq_carry y xs) else x )"  
 
definition largestinseq :: "(nat \<times> 'b) list \<Rightarrow> nat" where
"largestinseq xs \<equiv> largestinseq_carry 0 xs"
declare largestinseq_def[simp]

value "largestinseq [(1,a),(2,a),(3,a)]"

definition largestprefix :: "(nat \<times> 'b) list \<Rightarrow> (nat \<times> 'b) list" where
"largestprefix xs \<equiv> filter (\<lambda>(y,z). y\<le>(largestinseq (xs))) (xs)"
declare largestprefix_def[simp]

(*Note: This assumes that the list was sorted to begin with.. 
if this assumption is wrong then it should be "else  sort_key (\<lambda>(x,z). x) xs" below *)
definition distinct_Sorted_Insert :: "(nat \<times> 'b) \<Rightarrow> (nat \<times> 'b) list \<Rightarrow> (nat \<times> 'b) list" where
"distinct_Sorted_Insert x xs \<equiv> (if x \<notin> set xs then sort_key  (\<lambda>(x,z). x) (x # xs) else xs)"
declare distinct_Sorted_Insert_def[simp]

value "distinct_Sorted_Insert (2,a) [(1,a),(2,a),(4,a)]"
value "largestprefix  [(1,a),(2,a),(4,a)]"

end
