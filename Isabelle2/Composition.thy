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

declare glb_common_set_obtains[lems]

lemma l3[lems]:
  assumes "\<And> s . s \<in> S \<Longrightarrow> s\<^sub>0 \<preceq> s" and "finite S" and "S \<noteq> {}"
  shows "s\<^sub>0 \<preceq> \<Sqinter>S" using assms
by (metis local.boundedI)

method bring_invs =
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

method try_solve_inv declares mydefs =
  ( rule invariantI, 
    force simp add:mydefs inv_defs -- "solve the base case",
    bring_invs,
    match premises in T:"?s \<midarrow>a\<midarrow>composition\<longrightarrow> ?t" for a \<Rightarrow> \<open>case_tac a\<close> 
      -- "do case analysis on the action";
    simp add:mydefs inv_defs )

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
  apply (try_solve_inv mydefs:non_trivial_def less_eq_def)
  subgoal by (metis subset_insertI2)
  subgoal by (metis subset_insertI2)
  subgoal by (metis subset_insertI2)
  subgoal by metis
  done
declare inv4[invs]

lemma inv7:"invariant composition inv7"
  by try_solve_inv
declare inv7[invs]

lemma inv5:"invariant composition inv5"
  apply (try_solve_inv mydefs:non_trivial_def less_eq_def)
  subgoal by (metis subset_insertI2)
  subgoal by metis
  subgoal by (metis subset_insertI2)
  subgoal by metis
  done
declare inv5[invs]

lemma inv8:"invariant composition inv8"
  apply (try_solve_inv mydefs:non_trivial_def less_eq_def)
  subgoal by (metis subset_insertI2)
  subgoal by metis
  subgoal by (metis singleton subset_singletonD)
  done
declare inv8[invs]

lemma inv9:"invariant composition inv9"
  apply (try_solve_inv mydefs:non_trivial_def less_eq_def)
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
declare inv9[invs]
  

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

  apply(bring_invs)
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
    subgoal by (smt ComposableGC.l3 ComposableGC_axioms Un_iff antimono compat_sym l1 pre_CStruct.trans subset_empty)
    subgoal
    proof -
    fix a :: "('a, 'b, 'c) cgc_state" and b :: "('a, 'b, 'c) cgc_state" and aa :: "('a, 'b, 'c) cgc_state" and ba :: "('a, 'b, 'c) cgc_state" and x31 :: 'a and x32 :: 'c
    assume a1: "(\<exists>S. S \<noteq> {} \<and> S \<subseteq> {\<bottom>} \<and> (\<exists>cs. set cs \<subseteq> propCmd a \<and> x31 = \<Sqinter> S \<star> cs)) \<and> x32 \<in> learners \<and> (\<forall>l\<in>learners. \<forall>s'\<in>learned a l. compat2 s' x31) \<and> (\<forall>x\<in>cgc_state.toNext a. x31 \<preceq> x) \<and> aa = a \<lparr>learned := (learned a) (x32 := insert x31 (learned a x32))\<rparr> \<and> b = ba"
    assume a2: "finite (cgc_state.toNext a) \<and> finite (cgc_state.toNext ba)"
    assume a3: "\<forall>s\<in>cgc_state.toNext ba. \<exists>S. S \<noteq> {} \<and> S \<subseteq> cgc_state.toNext a \<and> (\<exists>cs. s = \<Sqinter> S \<star> cs \<and> set cs \<subseteq> propCmd ba)"
    { fix aaa :: 'a
      obtain AA :: "'a \<Rightarrow> 'a set" and bbs :: "'a \<Rightarrow> 'b list" where
        ff1: "\<forall>aa. aa \<notin> cgc_state.toNext ba \<or> AA aa \<noteq> {} \<and> AA aa \<subseteq> cgc_state.toNext a \<and> aa = \<Sqinter> AA aa \<star> bbs aa \<and> set (bbs aa) \<subseteq> propCmd ba"
        using a3 by metis
      { assume "aaa \<in> cgc_state.toNext ba"
        { assume "cgc_state.toNext a \<noteq> {}"
          moreover
          { assume "cgc_state.toNext a \<noteq> {} \<and> aaa \<in> cgc_state.toNext ba"
            moreover
            { assume "AA aaa \<noteq> {} \<and> \<not> x31 \<preceq> aaa \<and> cgc_state.toNext a \<noteq> {}"
              moreover
              { assume "\<exists>aa. \<not> aa \<preceq> aaa \<and> AA aaa \<noteq> {} \<and> aa \<preceq> \<Sqinter> cgc_state.toNext a"
                then have "(\<exists>a. \<not> a \<preceq> aaa \<and> a \<preceq> \<Sqinter> AA aaa) \<or> {} \<noteq> AA aaa \<and> \<not> \<Sqinter> cgc_state.toNext a \<preceq> \<Sqinter> AA aaa \<or> aaa \<notin> cgc_state.toNext ba \<or> x31 \<preceq> aaa"
                  by (metis local.trans)
                then have "AA aaa \<subseteq> cgc_state.toNext a \<longrightarrow> aaa \<notin> cgc_state.toNext ba \<or> x31 \<preceq> aaa"
                  using ff1 a2 by (metis antimono less_eq_def local.trans) }
              ultimately have "AA aaa \<subseteq> cgc_state.toNext a \<longrightarrow> aaa \<notin> cgc_state.toNext ba \<or> x31 \<preceq> aaa"
                using a2 a1 by (metis l3) }
            ultimately have "AA aaa \<subseteq> cgc_state.toNext a \<longrightarrow> aaa \<notin> cgc_state.toNext ba \<or> x31 \<preceq> aaa"
              using ff1 by metis }
          ultimately have "AA aaa \<subseteq> cgc_state.toNext a \<longrightarrow> aaa \<notin> cgc_state.toNext ba \<or> x31 \<preceq> aaa"
            by metis }
        then have "aaa \<notin> cgc_state.toNext ba \<or> x31 \<preceq> aaa"
          using ff1 by (metis empty_iff subsetI subset_antisym) }
      then have "aaa \<notin> cgc_state.toNext ba \<or> x31 \<preceq> aaa"
        by metis }
    then show "\<forall>a\<in>cgc_state.toNext ba. x31 \<preceq> a"
      by metis
    qed
    subgoal by (simp add:fun_eq_iff)

    apply(rule_tac x="refmap (a,b)" in exI)
    apply(rule_tac x="[(Learn2 x41 x42,refmap (aa,ba))]" in exI)
    apply (simp add:ref_defs spec_def actions_defs cgc_ioa_defs actions_defs inv_defs refmap_def non_trivial_def)
    apply (split_conjs?)
    subgoal
    proof -
      fix a :: "('a, 'b, 'c) cgc_state" and b :: "('a, 'b, 'c) cgc_state" and aa :: "('a, 'b, 'c) cgc_state" and ba :: "('a, 'b, 'c) cgc_state" and x41 :: 'a and x42 :: 'c
      assume a1: "a = aa \<and> (\<exists>S. S \<noteq> {} \<and> S \<subseteq> cgc_state.toNext aa \<and> (\<exists>cs. set cs \<subseteq> propCmd b \<and> x41 = \<Sqinter> S \<star> cs)) \<and> x42 \<in> learners \<and> (\<forall>l\<in>learners. \<forall>s'\<in>learned b l. compat2 s' x41) \<and> (\<forall>x\<in>cgc_state.toNext b. x41 \<preceq> x) \<and> cgc_state.toNext aa \<noteq> {} \<and> ba = b \<lparr>learned := (learned b)(x42 := insert x41 (learned b x42))\<rparr>"
      assume a2: "\<forall>S. S \<noteq> {} \<and> S \<subseteq> cgc_state.toNext aa \<longrightarrow> (\<exists>cs. \<Sqinter> S = \<bottom> \<star> cs \<and> set cs \<subseteq> propCmd aa)"
      obtain AA :: "'a set" and bbs :: "'b list" where
        f3: "a = aa \<and> (AA \<noteq> {} \<and> AA \<subseteq> cgc_state.toNext aa \<and> set bbs \<subseteq> propCmd b \<and> x41 = \<Sqinter> AA \<star> bbs) \<and> x42 \<in> learners \<and> (\<forall>c. c \<notin> learners \<or> (\<forall>a. a \<notin> learned b c \<or> compat2 a x41)) \<and> (\<forall>a. a \<notin> cgc_state.toNext b \<or> x41 \<preceq> a) \<and> cgc_state.toNext aa \<noteq> {} \<and> ba = b \<lparr>learned := (learned b)(x42 := insert x41 (learned b x42))\<rparr>"
        using a1 by auto
      obtain bbsa :: "'a set \<Rightarrow> 'b list" where
        f4: "\<forall>A. (A = {} \<or> \<not> A \<subseteq> cgc_state.toNext aa) \<or> \<Sqinter> A = \<bottom> \<star> bbsa A \<and> set (bbsa A) \<subseteq> propCmd aa"
        using a2 by metis
      then have "set (bbsa AA) \<union> set bbs \<subseteq> propCmd aa \<union> propCmd b"
        using f3 by (metis sup.mono)
      then have "set (append bbs (bbsa AA)) \<subseteq> propCmd b \<union> propCmd aa"
        by (metis Un_commute set_append)
      then show "\<exists>A. A \<noteq> {} \<and> A \<subseteq> {\<bottom>} \<and> (\<exists>bs. set bs \<subseteq> propCmd aa \<union> propCmd b \<and> x41 = \<Sqinter> A \<star> bs)"
        using f4 f3 by (metis Un_commute empty_not_insert pre_CStruct.exec_append singleton subsetI)
    qed
    subgoal by (metis (mono_tags, lifting) ComposableGC.l3 ComposableGC_axioms Un_iff antimono l1 pre_CStruct.trans)
    subgoal by (simp add:fun_eq_iff)

    apply(rule_tac x="refmap (a,b)" in exI)
    apply(rule_tac x="[]" in exI)
    subgoal by (force simp add:mydefs ref_defs refmap_def)

    apply (rule_tac x="refmap (a,b)" in exI)
    apply (rule_tac x="[(ToNext x6,refmap (aa,ba))]" in exI)
    apply (simp add:ref_defs spec_def actions_defs cgc_ioa_defs actions_defs inv_defs refmap_def non_trivial_def)
    apply (split_conjs?)
    subgoal
    proof -
      fix a :: "('a, 'b, 'c) cgc_state" and b :: "('a, 'b, 'c) cgc_state" and aa :: "('a, 'b, 'c) cgc_state" and ba :: "('a, 'b, 'c) cgc_state" and x6 :: 'a
      assume a1: "\<forall>S. S \<noteq> {} \<and> S \<subseteq> cgc_state.toNext aa \<longrightarrow> (\<exists>cs. \<Sqinter> S = \<bottom> \<star> cs \<and> set cs \<subseteq> propCmd aa)"
      assume a2: "\<exists>S. S \<noteq> {} \<and> S \<subseteq> cgc_state.toNext aa \<and> (\<exists>cs. x6 = \<Sqinter> S \<star> cs \<and> set cs \<subseteq> propCmd b)"
      obtain bbs :: "'a set \<Rightarrow> 'b list" where
        f3: "\<forall>A. (A = {} \<or> \<not> A \<subseteq> cgc_state.toNext aa) \<or> \<Sqinter> A = \<bottom> \<star> bbs A \<and> set (bbs A) \<subseteq> propCmd aa"
        using a1 by metis
      obtain AA :: "'a set" and bbsa :: "'b list" where
        f4: "AA \<noteq> {} \<and> AA \<subseteq> cgc_state.toNext aa \<and> x6 = \<Sqinter> AA \<star> bbsa \<and> set bbsa \<subseteq> propCmd b"
        using a2 by moura
      then have "set (bbs AA) \<union> set bbsa \<subseteq> propCmd aa \<union> propCmd b"
        using f3 by (metis sup.mono)
      then have "set (append bbsa (bbs AA)) \<subseteq> propCmd b \<union> propCmd aa"
        by (metis Un_commute set_append)
      then show "\<exists>A. A \<noteq> {} \<and> A \<subseteq> {\<bottom>} \<and> (\<exists>bs. set bs \<subseteq> propCmd aa \<union> propCmd b \<and> x6 = \<Sqinter> A \<star> bs)"
        using f4 f3 by (metis Un_commute empty_not_insert pre_CStruct.exec_append singleton subsetI)
    qed
    subgoal by (metis UnE Un_absorb1 finite_Un less_eq_def local.boundedI local.trans subset_eq)
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