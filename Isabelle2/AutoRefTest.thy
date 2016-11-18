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
  
definition inst_inv where 
  "inst_inv vs vbo \<equiv> case vbo of Some (v,b) \<Rightarrow> (vs \<noteq> {} \<and> (v,b) \<in> vs \<and> b = Max (snd ` vs))
    | None \<Rightarrow> vs = {}"
  
lemma inst_votes_union:
  "inst_votes f i (A \<union> B) = inst_votes f i A \<union> inst_votes f i B"
  by (auto simp add:inst_votes_def)

definition inv :: "('a \<rightharpoonup> (nat \<rightharpoonup> (('v \<times> nat) option))) \<Rightarrow> (nat \<rightharpoonup> ('v \<times> nat)) 
  \<Rightarrow> 'a set \<Rightarrow> nat set \<Rightarrow> bool"  
  where "inv f g A I \<equiv> (\<forall> i \<in> I . let vs_i = inst_votes f i A in inst_inv vs_i (g i))"
  
definition spec :: "('a \<rightharpoonup> (nat \<rightharpoonup> (('v \<times> nat) option))) \<Rightarrow> (nat \<rightharpoonup> ('v \<times> nat)) nres" 
  where "spec f \<equiv> SPEC (\<lambda> g . inv f g UNIV UNIV)"
 (*
definition inner_loop :: "('a\<times>) 'i \<rightharpoonup> ('v \<times> 'b)" where "inner_loop" *)
  
definition impl_1 :: "('a \<rightharpoonup> ('i \<rightharpoonup> (('v \<times> 'b::linorder) option))) \<Rightarrow> ('i \<rightharpoonup> ('v \<times> 'b)) nres"
  where "impl_1 f \<equiv>
  FOREACH (map_to_set f) (\<lambda> (a,is) r . 
    FOREACH (map_to_set is) (\<lambda> (i,vbo) r2 . RETURN 
      (case vbo of None \<Rightarrow> r2 | Some (v,b) \<Rightarrow>
        (case r2 i of None \<Rightarrow> r2(i \<mapsto> (v,b)) 
        | Some (v2,b2) \<Rightarrow> if b \<ge> b2 then r2(i \<mapsto> (v,b)) else r2))) r)
  Map.empty"
  
lemma step_insert_image_iff:
  assumes "f ` it \<subseteq> S" and "(k,v) \<in> it" and "\<And> k v1 v2 . \<lbrakk>(k,v1) \<in> it; (k,v2)\<in> it\<rbrakk> \<Longrightarrow> v1 = v2" 
    and "\<And> k1 k2 v1 v2 . k1 \<noteq> k2 \<Longrightarrow> f (k1,v1) \<noteq> f (k2,v2)"
  shows "S - f ` (it - {(k,v)}) = insert (f (k,v)) (S - f ` it)"
proof -
  have "f ` (it - {(k,v)}) = (f ` it) - f ` {(k,v)}" 
    using \<open>(k,v) \<in> it\<close> assms(3,4) by auto (blast, metis)
  thus "S - f ` (it - {(k,v)}) = insert (f (k,v)) (S - (f ` it))"
    using \<open>f ` it \<subseteq> S\<close> and \<open>(k,v) \<in> it\<close> by (simp add: it_step_insert_iff) 
qed

lemma it_step_insert_image_fst_iff:
  assumes  "fst ` it \<subseteq> S" and "(k,v) \<in> it" and "it \<subseteq> map_to_set m"
  shows "S - fst ` (it - {(k,v)}) = insert (fst (k,v)) (S - fst ` it)"
proof -
  have 1:"\<And> k v1 v2 . \<lbrakk>(k,v1) \<in> it; (k,v2)\<in> it\<rbrakk> \<Longrightarrow> v1 = v2" using \<open>it \<subseteq> map_to_set m\<close>
    by (meson Refine_Misc.map_to_set_inj subsetCE)
  have 2:"\<And> k1 k2 v1 v2 . k1 \<noteq> k2 \<Longrightarrow> fst (k1,v1) \<noteq> fst (k2,v2)"
    by simp
  from step_insert_image_iff[OF assms(1,2) 1 2] show ?thesis by auto
qed

lemma 
  fixes f::"('a::finite \<rightharpoonup> (nat \<rightharpoonup> (('v \<times> nat) option)))"
  assumes "\<And> a . a \<in> dom f \<Longrightarrow> finite (dom (the (f a)))"
  shows "impl_1 f \<le> spec f"
  using assms unfolding impl_1_def spec_def
  apply -
  apply (refine_vcg FOREACH_rule[where  
        I="\<lambda> it r . let as = (UNIV::'a set) - (fst ` it) in inv f r as UNIV"])
     apply (simp add:finite_map_to_set)
    apply (auto simp add:map_to_set_def inv_def Let_def inst_votes_def inst_inv_def)[1]
   defer apply simp
  subgoal premises prems for kv it s a fa
  proof -
    define as' where "as' \<equiv> UNIV - fst ` (it - {kv})"
    define as where "as \<equiv> UNIV - fst ` it"
    have 1:"as' = (insert a as)" unfolding as_def as'_def
      using it_step_insert_image_fst_iff[of it UNIV a fa] \<open>kv \<in> it\<close> \<open>it \<subseteq> map_to_set f\<close>
      by (auto simp add:\<open>kv = (a, fa)\<close>)
    have 2:"f a = Some fa" using  \<open>kv = (a,fa)\<close> \<open>it \<subseteq> map_to_set f\<close> \<open>kv \<in> it\<close> by auto
        (metis (mono_tags, lifting) in_pair_collect_simp map_to_set_def mem_Collect_eq subset_Collect_conv)
    have 3:"inv f s as UNIV" using as_def prems(4) by auto
    have 4:"fa2 = fa" if "(a,fa2) \<in> it" for fa2 using \<open>kv = (a,fa)\<close> \<open>it \<subseteq> map_to_set f\<close> \<open>kv \<in> it\<close> that
        by (metis (no_types, lifting) Refine_Misc.map_to_set_inj subsetCE)
    define inner where "inner \<equiv> 
      FOREACH (map_to_set fa) (\<lambda> (i,vbo) r2 . RETURN 
        (case vbo of None \<Rightarrow> r2 | Some (v,b) \<Rightarrow>
          (case r2 i of None \<Rightarrow> r2(i \<mapsto> (v,b))
          | Some (v2,b2) \<Rightarrow> if b \<ge> b2 then r2(i \<mapsto> (v,b)) else r2))) s"
    have "inner \<le> SPEC (\<lambda>r. inv f r as' UNIV)" unfolding inner_def
      apply (refine_vcg FOREACH_rule[where I="\<lambda> it2 r2 . let 
            is_1 = (dom s \<inter> (fst ` it2)) \<union> (dom s - dom fa); is_2 = ((dom s \<union> dom fa) - (fst ` it2)) in
            inv f r2 as' is_2 \<and> inv f r2 as is_1 \<and> (fst ` it2) \<subseteq> dom fa"])
      subgoal using "2" assms finite_map_to_set by fastforce
      subgoal unfolding Let_def (* The invariant is true of the initial state *)
      proof (intro conjI)
        let ?is_1="(dom s \<inter> fst ` map_to_set fa) \<union> (dom s - dom fa)"
        let ?is_2="(dom s \<union> dom fa) - fst ` map_to_set fa"
        have "?is_2 = dom s - dom fa" by (simp add: Un_Diff map_to_set_dom) 
        show "inv f s as' ?is_2" unfolding inv_def Let_def
        proof 
          fix i
          assume "i \<in> ?is_2"
          hence "fa i = None"  by (auto simp add:\<open>?is_2 = dom s - dom fa\<close>)
          hence "inst_votes f i {a} = {}" using \<open>f a = Some fa\<close> by (simp add:inst_votes_def)
          hence "inst_votes f i as' = inst_votes f i as" by (auto simp add: \<open>as' = insert a as\<close> inst_votes_def)
          thus "inst_inv (inst_votes f i as') (s i)" using \<open>inv f s as UNIV\<close> by (simp add:inv_def)
        qed  
        show "inv f s as ?is_1" using \<open>inv f s as UNIV\<close> by (simp add:inv_def)
        show "fst ` map_to_set fa \<subseteq> dom fa" by (simp add: map_to_set_dom)
      qed
      subgoal premises prems for kv2 it2 s2 i hi (* The inductive step. *)
        unfolding Let_def
      proof (intro conjI)
        thm prems
        define s3 where "s3 \<equiv> (case hi of None \<Rightarrow> s2 | Some (v, b) \<Rightarrow>
          (case s2 i of None \<Rightarrow> s2(i \<mapsto> (v, b))
          | Some (v2, b2) \<Rightarrow> if b2 \<le> b then s2(i \<mapsto> (v, b)) else s2))"
        define is_2' where "is_2' \<equiv> (dom s \<union> dom fa) - (fst ` (it2 - {kv2}))"
        define is_2 where "is_2 \<equiv> (dom s \<union> dom fa) - (fst ` it2)"
        define is_1 where "is_1 \<equiv> (dom s \<inter> fst ` it2) \<union> (dom s - dom fa)"
        define is_1' where "is_1' \<equiv> (dom s \<inter> fst ` (it2 - {kv2})) \<union> (dom s - dom fa)"
        have 5:"is_2' = insert i is_2"  
        proof -
          have "fst ` it2 \<subseteq> (dom s \<union> dom fa)" using \<open>it2 \<subseteq> map_to_set fa\<close> by (auto simp add: map_to_set_dom)
          with it_step_insert_image_fst_iff[of it2 "dom s \<union> dom fa" i hi] \<open>it2 \<subseteq> map_to_set fa\<close> \<open>kv2 = (i,hi)\<close> \<open>kv2 \<in> it2\<close> 
          show ?thesis by (auto simp add:is_2'_def is_2_def)
        qed
        have 6:"inv f s2 as' is_2" unfolding is_2_def using prems(3) by auto
        have 7:"inv f s2 as is_1" unfolding is_1_def by (meson prems(3))
        have 8:"fa i = Some hi" using \<open>kv2 = (i,hi)\<close> \<open>it2 \<subseteq> map_to_set fa\<close> \<open>kv2 \<in> it2\<close>
          by (metis (mono_tags, lifting) in_pair_collect_simp map_to_set_def mem_Collect_eq subset_Collect_conv)
        have 9:"hi2 = hi" if "(i,hi2) \<in> it2" for hi2 using \<open>kv2 = (i,hi)\<close> \<open>it2 \<subseteq> map_to_set fa\<close> \<open>kv2 \<in> it2\<close> that
          by (metis (no_types, lifting) Refine_Misc.map_to_set_inj subsetCE)
        have 10:"i \<notin> is_2" using \<open>kv2 \<in> it2\<close> \<open>kv2 = (i,hi)\<close> unfolding is_2_def by (simp add: img_fst)
        have 11:"is_1' \<subseteq> is_1 - {i}" unfolding is_1_def is_1'_def using "5" is_2'_def "8" by blast
        have 12:"fst ` it2 \<subseteq> dom fa" by (meson prems(3))
        have "AutoRefTest.inv f s3 as' is_2'"
        proof (auto simp add:inv_def)
          fix j
          assume "j \<in> is_2'"
          define vs' where "vs' \<equiv> inst_votes f j as'"
          define vs where "vs \<equiv> inst_votes f j as"
          have 4:"vs' = (inst_votes f j {a}) \<union> vs" unfolding vs'_def vs_def by (metis "1" insert_is_Un inst_votes_union) 
          show "inst_inv vs' (s3 j)"
          proof (cases "i = j")
            case True
            show ?thesis
            proof (cases hi)
              case None
              hence "inst_votes f j {a} = {}" unfolding inst_votes_def using "8" 2 \<open>i=j\<close> by auto
              hence "vs' = vs" using "4" by blast 
              moreover have "s3 j = s2 j" by (simp add: None s3_def)
              moreover have "inst_inv vs (s2 j)"
              proof -
                have "j \<in> is_1 \<or> j \<in> (fst ` it2) - dom s"
              ultimately show ?thesis by auto
            next
              case (Some a)
              then show ?thesis sorry
            qed
          next
            case False
            show ?thesis
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