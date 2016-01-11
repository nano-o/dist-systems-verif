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

definition inv1 where
  "inv1 r \<equiv> let r1 = fst r; r2 = snd r in
    (\<forall> s \<in> cgc_state.fromPrev r2 . \<forall> l \<in> learners . \<forall> s' \<in> learned r1 l . s' \<preceq> s)"
declare inv1_def[inv_defs]

definition inv2 where
  "inv2 r \<equiv> let r1 = fst r; r2 = snd r in 
    cgc_state.fromPrev r2 = cgc_state.toNext r1"
declare inv2_def[inv_defs]

definition inv3 where
  "inv3 r \<equiv> let r1 = fst r; r2 = snd r in
    cgc_state.fromPrev r1 = {\<bottom>}"
declare inv3_def[inv_defs]

definition inv4 where
  "inv4 r \<equiv> let r1 = fst r; r2 = snd r in
    \<forall> l \<in> learners . \<forall> s \<in> learned r2 l . 
      \<exists> S cs . S \<noteq> {} \<and> S \<subseteq> cgc_state.fromPrev r2
        \<and> s = \<Sqinter>S \<star> cs \<and> set cs \<subseteq> propCmd r2"
declare inv4_def[inv_defs]

definition inv5 where
  "inv5 r \<equiv> let r1 = fst r; r2 = snd r in
    \<forall> s \<in> cgc_state.toNext r2 . 
      \<exists> S cs . S \<noteq> {} \<and> S \<subseteq> cgc_state.fromPrev r2 
        \<and> s = \<Sqinter>S \<star> cs \<and> set cs \<subseteq> propCmd r2"
declare inv5_def[inv_defs]

definition inv8 where
  "inv8 r \<equiv> let r1 = fst r; r2 = snd r in
    \<forall> s \<in> cgc_state.toNext r1 . 
      \<exists> cs . s = \<bottom> \<star> cs \<and> set cs \<subseteq> propCmd r1"
declare inv8_def[inv_defs]

definition inv9 where
  "inv9 r \<equiv> let r1 = fst r; r2 = snd r in
    \<forall> S . S \<noteq> {} \<and> S \<subseteq> cgc_state.toNext r1 \<longrightarrow>
      (\<exists> cs . \<Sqinter>S = \<bottom> \<star> cs \<and> set cs \<subseteq> propCmd r1)"
declare inv9_def[inv_defs]

definition inv7 where
  "inv7 r \<equiv> let r1 = fst r; r2 = snd r in
    finite (cgc_state.toNext r1) \<and> finite (cgc_state.toNext r2)"
declare inv7_def[inv_defs]

definition inv10 where
  "inv10 r \<equiv> let r1 = fst r; r2 = snd r in
    \<forall> l\<^sub>1 \<in> learners. \<forall> l\<^sub>2 \<in> learners . \<forall> s\<^sub>1 \<in> learned r1 l\<^sub>1 . \<forall> s\<^sub>2 \<in> learned r2 l\<^sub>2 . s\<^sub>1 \<preceq> s\<^sub>2"
declare inv10_def[inv_defs]

definition inv11 where
  "inv11 r \<equiv> let r1 = fst r; r2 = snd r in
    \<forall> l\<^sub>1 \<in> learners. \<forall> s\<^sub>1 \<in> learned r1 l\<^sub>1 . \<forall> s\<^sub>2 \<in> cgc_state.toNext r2 . s\<^sub>1 \<preceq> s\<^sub>2"
declare inv11_def[inv_defs]

definition inv12 where
  "inv12 r \<equiv> let r1 = fst r; r2 = snd r in
    \<forall> l \<in> learners. \<forall> s \<in> learned r2 l . \<exists> cs .  s = \<bottom> \<star> cs \<and> set cs \<subseteq> propCmd r1 \<union> propCmd r2"
declare inv12_def[inv_defs]

definition inv13 where
  "inv13 r \<equiv> let r1 = fst r; r2 = snd r in
    \<forall> s \<in> cgc_state.toNext r2 . \<exists> cs .  s = \<bottom> \<star> cs \<and> set cs \<subseteq> propCmd r1 \<union> propCmd r2"
declare inv13_def[inv_defs]

lemmas cgc_ioa_defs = composition_def par2_def asig_comp2_def cgc_ioa_def rename_def
    rename_set_def cgc_asig_def is_trans_def actions_def cgc_trans_def initial_def hide_def 
    propose_def 
lemmas actions_defs = learn_def fromPrev_def toNext_def
    hide_asig_def externals_def cgc_start_def spec_def
lemmas ref_defs = refines_def actions_def trace_def schedule_def filter_act_def

named_theorems invs
  -- "named theorem for use by the tactics below"
named_theorems aux_invs
  -- "auxiliary invariants used to prove the invariants needed for the refinement proof"
named_theorems ref_invs
  -- "the invariants needed for the refinement proof"
named_theorems mydefs
  -- "definitions to unfold"
declare cgc_ioa_defs[mydefs]
declare actions_defs[mydefs]

text {* A usefull lemma (l4) *}

lemma l3:
  assumes "\<And> s . s \<in> S \<Longrightarrow> s\<^sub>0 \<preceq> s" and "finite S" and "S \<noteq> {}"
  shows "s\<^sub>0 \<preceq> \<Sqinter>S" using assms
by (metis local.boundedI)

lemma l4:
  assumes "\<exists> S cs . S \<noteq> {} \<and> S \<subseteq> S\<^sub>i \<and> s = \<Sqinter>S \<star> cs" and "finite S\<^sub>i"
  and "\<And> s\<^sub>l s\<^sub>i. s\<^sub>l \<in> S\<^sub>l \<and> s\<^sub>i \<in> S\<^sub>i \<Longrightarrow> s\<^sub>l \<preceq> s\<^sub>i" and "s\<^sub>l \<in> S\<^sub>l"
  shows "s\<^sub>l \<preceq> s" using assms
  proof -
    obtain aa :: "'a set \<Rightarrow> 'a \<Rightarrow> 'a" where
      f1: "\<And>A a. (infinite A \<or> A = {} \<or> aa A a \<in> A \<or> a \<preceq> \<Sqinter> A) \<and> (infinite A \<or> \<not> a \<preceq> aa A a \<or> A = {} \<or> a \<preceq> \<Sqinter> A)"
      using l3 by moura
    obtain AA :: "'a set" and bbs :: "'b list" where
      "AA \<subseteq> S\<^sub>i \<and> {} \<noteq> AA \<and> \<Sqinter> AA \<star> bbs = s"
      using assms(1) by moura
    then show ?thesis
      using f1 by (metis antimono assms(2) assms(3) assms(4) less_eq_def pre_CStruct.trans subset_empty)
  qed

lemma l5[simp]:
  "\<lbrakk>S \<subseteq> {\<bottom>}; S \<noteq> {}\<rbrakk> \<Longrightarrow> \<Sqinter>S = \<bottom>"
by (metis singleton subset_singletonD) 

method bring_invs declares invs =
  -- "bring all the invariants in the premises"
  ( (insert invs) -- "insert invariant theorems in the premises; 
      this will allow us to use [thin] to get rid of them after use",
    ( (match premises in I[thin]:"invariant composition ?inv"
        and R:"reachable composition ?s" \<Rightarrow> 
            \<open>insert I[simplified invariant_def, rule_format, OF R]\<close>)+
        -- "for each invariant theorem, use the reachability assumption to obtain the invariant",
    (match premises in R[thin]:"reachable composition ?s" 
      and T:"?s \<midarrow>?a\<midarrow>composition\<longrightarrow> ?t" \<Rightarrow> 
        \<open>insert reachable_n[OF R T]\<close>),
    (insert invs),(match premises in I[thin]:"invariant composition ?inv"
        and R:"reachable composition ?s" \<Rightarrow> 
            \<open>insert I[simplified invariant_def, rule_format, OF R]\<close>)+,
    (match premises in R[thin]:"reachable composition ?s" \<Rightarrow> succeed)
        -- "finally get rid of the reachability assumption"
        )? -- "don't fail if there are no invariants to bring"
    )

method try_solve_inv declares mydefs invs =
  ( rule invariantI, 
    force simp add:mydefs inv_defs -- "solve the base case",
    bring_invs invs:invs,
    match premises in T:"?s \<midarrow>a\<midarrow>composition\<longrightarrow> ?t" for a \<Rightarrow> \<open>case_tac a\<close> 
      -- "do case analysis on the action";
    simp add:mydefs inv_defs )

lemma inv2:"invariant composition inv2"
  by try_solve_inv
declare inv2[aux_invs]

lemma inv1:"invariant composition inv1"
  by (try_solve_inv invs:aux_invs)
declare inv1[aux_invs]

lemma inv3:"invariant composition inv3"
  by try_solve_inv
declare inv3[aux_invs]
declare inv3[ref_invs]

lemma inv4:"invariant composition inv4"
  apply (try_solve_inv invs:aux_invs  mydefs:non_trivial_def less_eq_def)
  subgoal by (metis subset_insertI2)
  subgoal by (metis subset_insertI2)
  subgoal by (metis subset_insertI2)
  subgoal by metis
  done
declare inv4[aux_invs]

lemma inv7:"invariant composition inv7"
  by (try_solve_inv invs:aux_invs)
declare inv7[aux_invs]

lemma inv5:"invariant composition inv5"
  apply (try_solve_inv invs:aux_invs mydefs:non_trivial_def less_eq_def)
  subgoal by (metis subset_insertI2)
  subgoal by metis
  subgoal by (metis subset_insertI2)
  subgoal by metis
  done
declare inv5[aux_invs]

lemma inv8:"invariant composition inv8"
  apply (try_solve_inv invs:aux_invs mydefs:non_trivial_def less_eq_def)
  subgoal by (metis subset_insertI2)
  subgoal by metis
  subgoal by (metis singleton subset_singletonD)
  done
declare inv8[aux_invs]

lemma inv9:"invariant composition inv9"
  apply (try_solve_inv invs:aux_invs mydefs:non_trivial_def less_eq_def)
  subgoal by (metis subset_insertI2)
  subgoal by metis
  subgoal premises prems for s t a x5
  proof -
    have 1:"\<And> S s1 . \<lbrakk>S \<subseteq> insert x5 (cgc_state.toNext (fst s)); s1 \<in> S\<rbrakk> 
      \<Longrightarrow> \<exists>cs. s1 = \<bottom> \<star> cs \<and> set cs \<subseteq> propCmd (fst s)" using prems(11) by auto
    have 2:"finite (cgc_state.toNext (fst s))" using prems by auto 
    show ?thesis 
    proof clarify
      fix S x
      assume a1:"S \<noteq> {}" and a2:"S \<subseteq> insert x5 (cgc_state.toNext (fst s))"
      hence 4:"\<And> s1 . s1 \<in> S \<Longrightarrow> \<exists>cs. s1 = \<bottom> \<star> cs \<and> set cs \<subseteq> propCmd (fst s)" 
        using 1 by auto
      have 5:"finite S" using 2 a2 by (metis finite_insert infinite_super) 
      from 4 5 a1 glb_common_set[of "S" "propCmd (fst s)"] 
        show "\<exists>cs. \<Sqinter> S = \<bottom> \<star> cs \<and> set cs \<subseteq> propCmd (fst s)" by fast
    qed
  qed
done
declare inv9[aux_invs]

lemma inv10:"invariant composition inv10"
  apply (try_solve_inv invs: aux_invs)
  subgoal by (smt l4 singletonD singletonI)
  subgoal by (smt insert_iff l4)
  done
declare inv10[ref_invs]

lemma inv11:"invariant composition inv11"
  apply (try_solve_inv invs: aux_invs)
  subgoal by (smt l4 singletonD singletonI)
  subgoal by (smt insert_iff l4)
  done
declare inv11[ref_invs]

lemma inv12:"invariant composition inv12"
  apply (try_solve_inv invs: aux_invs)
  subgoal by (metis subset_insertI2)
  subgoal by (metis subset_insertI2)
  defer
  subgoal by metis
  subgoal by metis
  apply (clarsimp simp add:non_trivial_def)
  subgoal by (metis (full_types) Un_commute pre_CStruct.exec_append set_append sup.mono)
done
declare inv12[ref_invs]

lemma inv13:"invariant composition inv13"
  apply (try_solve_inv invs: aux_invs)
  subgoal by (metis subset_insertI2)
  subgoal by (metis subset_insertI2)
  subgoal by metis
  subgoal by metis
  subgoal by (smt inf_sup_aci(5) pre_CStruct.exec_append set_append sup_mono)
  done
declare inv13[ref_invs]

definition refmap where
  "refmap r \<equiv> let r1 = fst r; r2 = snd r in 
    \<lparr>cgc_state.propCmd = propCmd r1 \<union> propCmd r2, 
      cgc_state.learned = (\<lambda> l . learned r1 l \<union> learned r2 l) ,
      cgc_state.fromPrev = {\<bottom>}, 
      toNext = cgc_state.toNext r2\<rparr>"

method split_conjs =
  (rule conjI);split_conjs?

lemma refok:"is_ref_map refmap composition spec"
apply(simp add:is_ref_map_def refmap_def, rule conjI; clarify)
  subgoal by (force simp add:mydefs)

  apply(bring_invs invs:ref_invs)
  apply(case_tac ab, auto)

    apply(rule_tac x="refmap (a,b)" in exI)
    apply(rule_tac x="[(Propose1 x1,refmap (aa,ba))]" in exI)
    subgoal by (force simp add:mydefs ref_defs refmap_def)

    apply(rule_tac x="refmap (a,b)" in exI)
    apply(rule_tac x="[(Propose2 x2,refmap (aa,ba))]" in exI)
    subgoal by (force simp add:mydefs ref_defs refmap_def)
    
    apply(rule_tac x="refmap (a,b)" in exI)
    apply(rule_tac x="[(Learn1 x31 x32,refmap (aa,ba))]" in exI)
    apply (simp add:ref_defs spec_def actions_defs cgc_ioa_defs actions_defs inv_defs refmap_def non_trivial_def)
    apply (split_conjs?)
    subgoal by (metis Un_upper1 subset_trans)
    subgoal by (metis Un_iff compat2_def insertI1 local.refl)
    subgoal by (metis insert_iff)
    subgoal by (simp add:fun_eq_iff)

    apply(rule_tac x="refmap (a,b)" in exI)
    apply(rule_tac x="[(Learn2 x41 x42,refmap (aa,ba))]" in exI)
    apply (simp add:ref_defs spec_def actions_defs cgc_ioa_defs actions_defs inv_defs refmap_def non_trivial_def)
    apply clarsimp
    apply (split_conjs?)
    subgoal by (metis (mono_tags, lifting) insertI1 insert_absorb2 insert_not_empty singleton singleton_insert_inj_eq)
    subgoal by (metis Un_iff compat2_def insertI1 local.refl)
    subgoal by (simp add:fun_eq_iff)

    apply(rule_tac x="refmap (a,b)" in exI)
    apply(rule_tac x="[]" in exI)
    subgoal by (force simp add:mydefs ref_defs refmap_def)

    apply (rule_tac x="refmap (a,b)" in exI)
    apply (rule_tac x="[(ToNext x6,refmap (aa,ba))]" in exI)
    apply (simp add:ref_defs spec_def actions_defs cgc_ioa_defs actions_defs inv_defs refmap_def non_trivial_def)
    apply clarsimp
    apply (split_conjs?)
    subgoal by (metis insert_absorb2 insert_not_empty singleton singleton_insert_inj_eq)
    subgoal by (metis Un_iff)    
done

lemma trace_incl:"traces composition \<subseteq> traces spec"
apply(rule ref_map_soundness[of refmap])
  subgoal by (insert refok, force)
  subgoal by (simp add:mydefs, intro set_eqI; case_tac x; force)
done

theorem composition: "composition =<| spec"
apply(simp add:ioa_implements_def)
apply(intro conjI)
  subgoal by (simp add:mydefs, intro set_eqI; case_tac x; force)
  subgoal by (simp add:mydefs, intro set_eqI; case_tac x; force)
  subgoal by (insert trace_incl, auto)
done

end

end