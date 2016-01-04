theory Composition
imports ComposableGC "/home/nano/Documents/IO-Automata/Simulations" "~~/src/HOL/Eisbach/Eisbach_Tools"
begin

datatype ('a,'c,'l) comp_action = 
  Propose1 'c
| Propose2 'c
| Learn1 'a 'l
| Learn2 'a 'l
| Switch 'a
| ToNext 'a

definition comp_asig where
  "comp_asig \<equiv> 
    \<lparr> inputs = { a . \<exists> c . a = Propose1 c \<or> a = Propose2 c},
      outputs = { a . \<exists> s p . a = Learn1 s p \<or> a = Learn2 s p \<or> a = ToNext s },
      internals = { a . \<exists> s . a = Switch s} \<rparr>"

context ComposableGC
begin

fun rn1 where
  "rn1 (Propose1 c) = Some (cgc_action.Propose c)"
| "rn1 (Switch s) = Some (cgc_action.ToNext s)"
| "rn1 (Learn1 s l) = Some (cgc_action.Learn s l)"
| "rn1 (Learn2 s l) = None"
| "rn1 (ToNext s) = None"
| "rn1 (Propose2 s) = None"

fun rn2 where
  "rn2 (Propose2 c) = Some (cgc_action.Propose c)"
| "rn2 (Switch s) = Some (cgc_action.FromPrev s)"
| "rn2 (Learn1 s l) = None"
| "rn2 (Learn2 s l) = Some (cgc_action.Learn s l)"
| "rn2 (ToNext s) = Some (cgc_action.ToNext s)"
| "rn2 (Propose1 c) = None"

fun rn3 where
  "rn3 (Propose2 c) = Some (cgc_action.Propose c)"
| "rn3 (Propose1 c) = Some (cgc_action.Propose c)"
| "rn3 (Switch s) = None"
| "rn3 (Learn1 s l) = Some (cgc_action.Learn s l)"
| "rn3 (Learn2 s l) = Some (cgc_action.Learn s l)"
| "rn3 (ToNext s) = Some (cgc_action.ToNext s)"

definition initial where
  "initial \<equiv> cgc_ioa\<lparr>start := {\<lparr>propCmd = {}, learned = \<lambda> p . {}, fromPrev = {\<bottom>}, toNext = {} \<rparr>}\<rparr>"

definition composition where
  "composition \<equiv> hide ((rename initial rn1) \<parallel> (rename cgc_ioa rn2)) {a . \<exists> s . a = Switch s}"

definition spec where
  "spec \<equiv> rename initial rn3"

named_theorems inv_defs 

definition inv1::"('a,'b,'c)cgc_state \<times> ('a,'b,'c)cgc_state \<Rightarrow> bool" where
  "inv1 r \<equiv> let r1 = fst r; r2 = snd r in
    (\<forall> s \<in> cgc_state.fromPrev r2 . \<forall> l . \<forall> s' \<in> learned r1 l . s' \<preceq> s)"
declare inv1_def[inv_defs]

definition inv2::"('a,'b,'c)cgc_state \<times> ('a,'b,'c)cgc_state \<Rightarrow> bool" where
  "inv2 r \<equiv> let r1 = fst r; r2 = snd r in 
    cgc_state.fromPrev r2 = cgc_state.toNext r1"
declare inv2_def[inv_defs]

definition inv3 where
  "inv3 r \<equiv> let r1 = fst r; r2 = snd r in
    cgc_state.fromPrev r1 = {\<bottom>}"
declare inv3_def[inv_defs]

definition inv4 where
  "inv4 r \<equiv> let r1 = fst r; r2 = snd r in
    \<forall> l . \<forall> s \<in> learned r2 l . \<exists> s' \<in> cgc_state.fromPrev r2 . s' \<preceq> s"
declare inv4_def[inv_defs]

definition inv5 where
  "inv5 r \<equiv> let r1 = fst r; r2 = snd r in
    \<forall> s \<in> cgc_state.toNext r2 . \<exists> s' \<in> cgc_state.fromPrev r2 . s' \<preceq> s"
declare inv5_def[inv_defs]

definition inv6 where
  "inv6 r \<equiv> let r1 = fst r; r2 = snd r in
    \<forall> s  \<in> cgc_state.toNext r1 . s \<in> non_trivial r1"
declare inv6_def[inv_defs]

lemmas cgc_ioa_defs = composition_def par2_def asig_comp2_def cgc_ioa_def rename_def
    rename_set_def cgc_asig_def is_trans_def actions_def cgc_trans_def initial_def hide_def 
    propose_def 
lemmas actions_defs = learn_def fromPrev_def toNext_def
    hide_asig_def externals_def cgc_start_def spec_def
lemmas ref_defs = refines_def actions_def trace_def schedule_def filter_act_def

named_theorems invs
named_theorems mydefs
declare cgc_ioa_defs[mydefs]
declare actions_defs[mydefs]

method bring_invs =
  -- "bring all the invariants in the premises"
  ( (insert invs) -- "insert invariant theorems in the premises; 
      this will allow us to use [thin] to get rid of them after use",
    ( (match premises in I[thin]:"invariant composition ?inv"
        and R:"reachable composition ?s" \<Rightarrow> 
            \<open>insert I[simplified invariant_def, rule_format, OF R]\<close>)+
        -- "for each invariant theorem, use the reachability assumption to obtain the invariant",
      (match premises in R[thin]:"reachable composition ?s" \<Rightarrow> succeed)
        -- "finally get rid of the reachability assumption"
        )? -- "don't fail if there are no invariants to bring"
    )

method try_solve_inv declares mydefs =
  ( rule invariantI, 
    force simp add:mydefs inv_defs -- "solve the base case",
    bring_invs,
    match premises in T:"?s \<midarrow>a\<midarrow>composition\<longrightarrow> ?t" for a \<Rightarrow> \<open>case_tac a\<close> 
      -- "do case analysis on the action";
    auto simp add:mydefs inv_defs)

lemma inv2:"invariant composition inv2"
  by try_solve_inv
declare inv2[invs]

lemma inv1:"invariant composition inv1"
  by try_solve_inv
declare inv1[invs]

lemma inv3:"invariant composition inv3"
  by try_solve_inv
declare inv3[invs]

lemma inv4:"invariant composition inv4"
  by (try_solve_inv mydefs:non_trivial_def less_eq_def)
declare inv4[invs]

lemma inv5:"invariant composition inv5"
  by (try_solve_inv mydefs:non_trivial_def less_eq_def)
declare inv5[invs]

lemma inv6:"invariant composition inv6"
  apply (try_solve_inv mydefs:non_trivial_def less_eq_def)
  apply (metis subset_insertI2)
  done
declare inv6[invs]

named_theorems lems

lemma l1[lems]:
  assumes "s\<^sub>0 \<preceq> s\<^sub>1" and "s\<^sub>2 = s\<^sub>1 \<star> cs"
  shows "compat2 s\<^sub>0 s\<^sub>2"
  using assms
by (metis less_eq_def local.compat2_def local.trans) 

lemma l2[lems]:
  assumes "s1 = \<bottom> \<star> cs" and "s2 = s1 \<star> cs'"
  obtains cs'' where "s2 = \<bottom> \<star> cs''" and "set cs'' = set cs \<union> set cs'"
  using assms
  by (metis inf_sup_aci(5) pre_CStruct.exec_append set_append)

definition refmap where
  "refmap r \<equiv> let r1 = fst r; r2 = snd r in 
    \<lparr>cgc_state.propCmd = propCmd r1 \<union> propCmd r2, 
      cgc_state.learned = (\<lambda> l . learned r1 l \<union> learned r2 l),
      cgc_state.fromPrev = {\<bottom>}, 
      toNext = cgc_state.toNext r2\<rparr>"

method app_fun_eq_iff =
  (match conclusion in "(\<lambda> x . ?B x) = (\<lambda> x . ?A x)" \<Rightarrow> \<open>simp add:fun_eq_iff\<close>)

method split_conjs =
  (rule conjI);split_conjs?

lemma refok:"is_ref_map refmap composition spec"
apply(simp add:is_ref_map_def refmap_def, rule conjI; clarify)
 apply(force simp add:mydefs)
 apply(bring_invs)
 apply(case_tac ab, auto)

   apply(rule_tac x="refmap (a,b)" in exI)
   apply(rule_tac x="[(Propose1 x1,refmap (aa,ba))]" in exI)
   apply(force simp add:mydefs ref_defs refmap_def)

   apply(rule_tac x="refmap (a,b)" in exI)
   apply(rule_tac x="[(Propose2 x2,refmap (aa,ba))]" in exI)
   apply(force simp add:mydefs ref_defs refmap_def)

   apply(rule_tac x="refmap (a,b)" in exI)
   apply(rule_tac x="[(Learn1 x31 x32,refmap (aa,ba))]" in exI)
   apply (simp add:ref_defs spec_def actions_defs cgc_ioa_defs actions_defs inv_defs refmap_def non_trivial_def)
   apply(split_conjs?)
   apply (app_fun_eq_iff?, force?)
   apply (metis Un_iff compat_sym l1 less_eq_def)
   apply (metis pre_CStruct.trans)
   apply (app_fun_eq_iff?, force?)

   apply(rule_tac x="refmap (a,b)" in exI)
   apply(rule_tac x="[(Learn2 x41 x42,refmap (aa,ba))]" in exI)
   apply (simp add:ref_defs spec_def actions_defs cgc_ioa_defs actions_defs inv_defs refmap_def non_trivial_def)
   apply(split_conjs?)
   apply (insert l2)
   apply (metis sup.mono)
   apply (metis Un_iff l1)
   apply (app_fun_eq_iff)

   apply(rule_tac x="refmap (a,b)" in exI)
   apply(rule_tac x="[]" in exI)
   apply(force simp add:mydefs ref_defs refmap_def)

   apply(rule_tac x="refmap (a,b)" in exI)
   apply(rule_tac x="[(ToNext x6,refmap (aa,ba))]" in exI)
   apply (simp add:ref_defs spec_def actions_defs cgc_ioa_defs actions_defs inv_defs refmap_def non_trivial_def)
   apply(split_conjs?)
   apply (insert l2)
   apply (metis sup.mono)
   apply (metis Un_iff less_eq_def pre_CStruct.trans)
done

lemma trace_incl:"traces composition \<subseteq> traces spec"
apply(rule ref_map_soundness[of refmap])
  apply(insert refok, force)
  apply(simp add:mydefs)
  apply(intro set_eqI; case_tac x; force)
done

theorem composition: "composition =<| spec"
apply(simp add:ioa_implements_def)
apply(intro conjI)
  apply(simp add:mydefs)
  apply(intro set_eqI; case_tac x; force)
  apply(simp add:mydefs)
  apply(intro set_eqI; case_tac x; force)
  apply (insert trace_incl, auto)
done

end

end