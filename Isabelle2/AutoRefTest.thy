theory AutoRefTest            
  imports Main "$AFP/Collections/Refine_Dflt" Groups_Big
begin

typ "'a \<rightharpoonup> 'a"
term i_map
term map_iterator

section \<open>First example\<close>

definition "abs_sum s \<equiv> do {
  FOREACH s (\<lambda>x r. RETURN (x+r)) 0
}"

schematic_goal ls_sum_impl':
  assumes [autoref_rules]: "(l,s)\<in>\<langle>nat_rel\<rangle>dflt_rs_rel"
  shows "(RETURN ?c,abs_sum s)\<in> \<langle>nat_rel\<rangle>nres_rel"
  unfolding abs_sum_def
  apply (autoref_monadic(plain,trace))
  done

concrete_definition ls_sum_impl' uses ls_sum_impl'
export_code ls_sum_impl' in SML
code_thms ls_sum_impl'

section \<open>Second example\<close>
text \<open>Using @{term FOREACH} on @{term dom} does not work.\<close>

experiment begin

definition test_spec :: "(nat \<rightharpoonup> nat) \<Rightarrow> nat nres" 
  where "test_spec m \<equiv> SPEC (\<lambda> n . n = (\<Sum> x \<in> (dom m) . the (m x)))"
                                         
definition test :: "(nat \<rightharpoonup> nat) \<Rightarrow> nat nres" 
  where "test m \<equiv> FOREACH (dom m) (\<lambda> x r . RETURN (the (m x)+r)) 0"
  
lemma assumes "finite (dom m)" shows "test m \<le> test_spec m"
  using assms unfolding test_def test_spec_def
  apply -
  apply (refine_vcg FOREACH_rule[where I="\<lambda>it r . r = (\<Sum> x \<in> (dom m - it) . the (m x))"])
    apply (auto simp add:it_step_insert_iff)
  done

schematic_goal test_impl:
  assumes [autoref_rules]: "(r,m)\<in>\<langle>nat_rel,nat_rel\<rangle>dflt_rm_rel"
  shows "(RETURN ?c,test m)\<in> \<langle>nat_rel\<rangle>nres_rel"
  unfolding test_def
  supply [[autoref_trace_failed_id]]
  apply (autoref_monadic(trace))
  oops
end

subsection \<open>Peter's solution\<close>

context begin

private
definition test_spec :: "(nat \<rightharpoonup> nat) \<Rightarrow> nat nres"
  where "test_spec m \<equiv> SPEC (\<lambda> n . n = (\<Sum> x \<in> (dom m) . the (m x)))"

private
definition test :: "(nat \<rightharpoonup> nat) \<Rightarrow> nat nres"
  where "test m \<equiv> FOREACH (map_to_set m) (\<lambda> (k,v) r . RETURN (v+r)) 0"

lemma test_correct:
  assumes "finite (dom m)" shows "test m \<le> test_spec m"
  using assms unfolding test_def test_spec_def
  apply -
  apply (refine_vcg FOREACH_rule[where 
          I="\<lambda>it r . r = (\<Sum> (k,v) \<in> (map_to_set m - it) . v)"])
  apply (auto simp add:it_step_insert_iff finite_map_to_set) thm sum.reindex_cong
  apply (rule sum.reindex_cong[where l="\<lambda>k. (k,the (m k))"])
  apply (auto simp: map_to_set_def)
  done

schematic_goal test_impl:
  assumes [autoref_rules]: "(r,m)\<in>\<langle>nat_rel,nat_rel\<rangle>dflt_rm_rel"
  shows "(RETURN ?c, test m) \<in> \<langle>nat_rel\<rangle>nres_rel"
  unfolding test_def
  supply [[autoref_trace_failed_id]] (* enable id-op tracing *)
  apply (autoref_monadic(trace)) (* phase id_op fails *)
  done

private
concrete_definition test_impl uses test_impl (*
export_code test_impl in SML
code_thms test_impl *)

end

section {* The paxos computation *}
  
definition inst_votes where 
  "inst_votes f i A \<equiv> {(v,b) . \<exists> a \<in> A . \<exists> h . f a = Some h \<and> h i = Some (Some (v,b))}"

definition inv :: "('a \<rightharpoonup> (nat \<rightharpoonup> (('v \<times> nat) option))) \<Rightarrow> (nat \<rightharpoonup> ('v \<times> nat)) 
    \<Rightarrow> 'a set \<Rightarrow> nat set \<Rightarrow> bool"  
  where "inv f g A I \<equiv> \<forall> i \<in> I . \<forall> v b . (g i = Some (v,b)) \<longleftrightarrow>
    (let vs_i = inst_votes f i A in vs_i \<noteq> {} \<and> (v,b) \<in> vs_i \<and> b = Max (snd ` vs_i))"
  
definition spec :: "('a \<rightharpoonup> (nat \<rightharpoonup> (('v \<times> nat) option))) \<Rightarrow> (nat \<rightharpoonup> ('v \<times> nat)) nres" 
  where "spec f \<equiv> SPEC (\<lambda> g . inv f g UNIV UNIV)"
  
definition impl_1 :: "('a \<rightharpoonup> ('i \<rightharpoonup> (('v \<times> 'b::linorder) option))) \<Rightarrow> ('i \<rightharpoonup> ('v \<times> 'b)) nres"
  where "impl_1 f \<equiv>
  FOREACH (map_to_set f) (\<lambda> (a,is) r . 
    FOREACH (map_to_set is) (\<lambda> (i,vbo) r2 . RETURN 
      (case vbo of None \<Rightarrow> r2 | Some (v,b) \<Rightarrow>
        (case r2 i of None \<Rightarrow> r2(i \<mapsto> (v,b)) 
        | Some (v2,b2) \<Rightarrow> if b \<ge> b2 then r2(i \<mapsto> (v,b)) else r2))) r)
  Map.empty"
  
lemma 
  fixes f::"('a::finite \<rightharpoonup> (nat \<rightharpoonup> (('v \<times> nat) option)))"
  assumes "\<And> a . a \<in> dom f \<Longrightarrow> finite (dom (the (f a)))"
  shows "impl_1 f \<le> spec f"
  using assms unfolding impl_1_def spec_def
  apply -
  apply (refine_vcg FOREACH_rule[where  
        I="\<lambda> it r . let as = (UNIV::'a set) - (fst ` it) in inv f r as UNIV"])
     apply (simp add:finite_map_to_set)
    apply (auto simp add:map_to_set_def inv_def Let_def inst_votes_def)[1]
   defer apply simp
  subgoal premises prems for kv it s a fa using prems
  apply (refine_vcg FOREACH_rule[where 
        I="\<lambda> it2 r2 . let is = (dom s - dom fa) \<union> (dom fa) - (fst ` it2); 
          as = UNIV - fst ` (it - {kv}) in inv f r2 as is"])
       apply (simp add:finite_map_to_set; fastforce simp add:map_to_set_def)
    (* First problem is that we need to show that the max remains unchanged for
      instances not in dom fa *)
    oops
  
  
schematic_goal impl_1:
  assumes [autoref_rules]: 
    "(r,f)\<in>\<langle>nat_rel,\<langle>nat_rel,\<langle>\<langle>nat_rel,nat_rel\<rangle>prod_rel\<rangle>option_rel\<rangle>dflt_rm_rel\<rangle>dflt_rm_rel"
  shows "(RETURN ?c, impl_1 f) \<in> \<langle>\<langle>nat_rel,\<langle>nat_rel,nat_rel\<rangle>prod_rel\<rangle>dflt_rm_rel\<rangle>nres_rel"
  unfolding impl_1_def
  supply [[autoref_trace_failed_id]] (* enable id-op tracing *)
  apply (autoref_monadic(trace))
  done

concrete_definition concrete_impl_1 uses impl_1
export_code concrete_impl_1 in SML


end