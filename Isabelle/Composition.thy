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

definition inv1 where
  "inv1 r \<equiv> let r1 = fst r; r2 = snd r in
    (\<forall> s \<in> cgc_state.fromPrev r2 . \<forall> l . \<forall> s' \<in> learned r1 l . s' \<preceq> s)"

definition inv2 where
  "inv2 r \<equiv> let r1 = fst r; r2 = snd r in 
    cgc_state.fromPrev r2 = cgc_state.toNext r1"

definition inv3 where
  "inv3 r \<equiv> let r1 = fst r; r2 = snd r in
    cgc_state.fromPrev r1 = {\<bottom>}"

definition inv4 where
  "inv4 r \<equiv> let r1 = fst r; r2 = snd r in
    \<forall> l . \<forall> s \<in> learned r2 l . \<exists> s' \<in> cgc_state.fromPrev r2 . s' \<preceq> s"

definition inv5 where
  "inv5 r \<equiv> let r1 = fst r; r2 = snd r in
    \<forall> s \<in> cgc_state.toNext r2 . \<exists> s' \<in> cgc_state.fromPrev r2 . s' \<preceq> s"

lemmas defs1 = composition_def par2_def asig_comp2_def cgc_ioa_def rename_def cgc_start_def
    rename_set_def cgc_asig_def is_trans_def actions_def cgc_trans_def initial_def hide_def propose_def learn_def fromPrev_def toNext_def
    hide_asig_def externals_def cgc_start_def spec_def

lemmas ref_defs = refines_def actions_def trace_def schedule_def filter_act_def

lemma inv2:"invariant composition inv2"
apply (rule invariantI)
  apply(simp add:defs1 inv2_def)
  apply(case_tac "a")
  apply(auto simp add:defs1 inv2_def)
done

lemma inv1:"invariant composition inv1"
apply (rule invariantI)
  apply(simp add:defs1 inv1_def )
  apply(drule_tac inv2[simplified invariant_def, rule_format])
  apply(case_tac "a")
  apply(auto simp add:defs1 inv1_def inv2_def non_trivial_def)
done

lemma inv3:"invariant composition inv3"
apply (rule invariantI)
  apply(simp add:defs1 inv3_def)
  apply(case_tac "a")
  apply(auto simp add:defs1 inv3_def)
done

lemma inv4:"invariant composition inv4"
apply (rule invariantI)
  apply(simp add:defs1 inv4_def)
  apply(case_tac "a")
  apply(thin_tac "reachable composition s")
  apply(auto simp add:defs1 inv4_def non_trivial_def less_eq_def)
done

lemma inv5:"invariant composition inv5"
apply (rule invariantI)
  apply(simp add:defs1 inv5_def)
  apply(case_tac "a")
  apply(thin_tac "reachable composition s")
  apply(auto simp add:defs1 inv5_def non_trivial_def less_eq_def)
done

lemmas inv11 = inv1[simplified invariant_def]
thm inv11[split_format(complete)]
lemmas invs[simplified invariant_def, rule_format] = inv1 inv2

lemma l1:
  assumes "s\<^sub>0 \<preceq> s\<^sub>1" and "s\<^sub>2 = s\<^sub>1 \<star> cs"
  shows "compat2 s\<^sub>0 s\<^sub>2"
  using assms
by (metis less_eq_def local.compat2_def local.trans) 

abbreviation refmap where
  "refmap r \<equiv> let r1 = fst r; r2 = snd r in 
    \<lparr>cgc_state.propCmd = propCmd r1 \<union> propCmd r2, 
      cgc_state.learned = (\<lambda> l . learned r1 l \<union> learned r2 l),
      cgc_state.fromPrev = {\<bottom>}, 
      toNext = cgc_state.toNext r2\<rparr>"

method my_allE for y :: 'a =
(match premises in I [thin]: "\<forall> x :: 'a. ?Q x" \<Rightarrow>
  \<open>rule allE [where x = y, OF I ]\<close>)

method print_inv =
  match invs in M [thin] :"\<And> s . reachable composition s \<Longrightarrow> ?Inv" \<Rightarrow> \<open>print_fact M\<close>

lemma refok:"is_ref_map refmap composition spec"
apply(simp add:is_ref_map_def, rule conjI; clarify)
 apply(simp add:defs1)
 apply(case_tac ab, auto)
   apply(thin_tac "reachable composition (a, b)")
   apply(rule_tac x="refmap (a,b)" in exI)
   apply(rule_tac x="[(Propose1 x1,refmap (aa,ba))]" in exI)
   apply(simp add:defs1 ref_defs)

   apply(thin_tac "reachable composition (a, b)")
   apply(rule_tac x="refmap (a,b)" in exI)
   apply(rule_tac x="[(Propose2 x2,refmap (aa,ba))]" in exI)
   apply(simp add:defs1 ref_defs)

   prefer 3
   apply(thin_tac "reachable composition (a, b)")
   apply(rule_tac x="refmap (a,b)" in exI)
   apply(rule_tac x="[]" in exI)
   apply(simp add:defs1 ref_defs)

   apply(rule_tac x="refmap (a,b)" in exI)
   apply(rule_tac x="[(Learn1 x31 x32,refmap (aa,ba))]" in exI)
   apply(frule_tac inv1[simplified invariant_def, rule_format])
   apply(frule_tac inv3[simplified invariant_def, rule_format])
   apply(frule_tac inv2[simplified invariant_def, rule_format])
   apply(frule_tac inv4[simplified invariant_def, rule_format])
   apply(frule_tac inv5[simplified invariant_def, rule_format])
   apply(thin_tac "reachable composition (a,b)")
   proof -
    fix r1 r2 l r1' r2' s
    assume learn:"(r1, r2) \<midarrow>Learn1 s l\<midarrow>composition\<longrightarrow> (r1', r2')" and inv1:"inv1 (r1, r2)" and inv2:"inv2 (r1, r2)" and inv3:"inv3 (r1,r2)" and inv4:"inv4 (r1,r2)"
    and inv5:"inv5 (r1,r2)"
    show "refines (refmap (r1, r2), [(Learn1 s l, refmap (r1', r2'))]) (r1, r2) (Learn1 s l) (r1', r2') spec refmap"
    proof -
      from learn have 1:"learn l s r1 r1'" and 2:"r2 = r2'"
        by (auto simp add: defs1)
      have "learn l s (refmap (r1, r2)) (refmap (r1',r2'))"
      proof -
        have "s \<in> non_trivial (refmap (r1, r2))" using 1 inv3 
          by (auto simp add:learn_def inv3_def non_trivial_def)
        moreover
        have "cgc_state.fromPrev (refmap (r1, r2)) \<noteq> {}" using inv3
          by (auto simp add:inv3_def)
        moreover 
        have "let learned1 = learned (refmap (r1, r2)) in (refmap (r1', r2')) = (refmap (r1, r2))\<lparr>learned := (learned1(l := learned1 l \<union> {s}))\<rparr>"
          using 1 2
          by (auto simp add:learn_def fun_eq_iff)
        moreover 
        have "\<forall> l . \<forall> s' \<in> learned (refmap (r1, r2)) l . compat2 s' s"
        proof auto
          fix l s'
          assume "s' \<in> learned r1 l"
          thus "compat2 s' s" using 1 by (simp add:learn_def)
        next
          fix l s'
          assume 3:"s' \<in> learned r2 l"
          with this obtain s'' where 4:"s'' \<preceq> s'" and 5:"s'' \<in> cgc_state.fromPrev r2" using inv4
            by (auto simp add:inv4_def)
          moreover
          have "s \<preceq> s''" using 5 inv1 inv2 1 by (auto simp add:inv2_def inv1_def learn_def)
          ultimately
          show "compat2 s' s" using l1
            by (metis compat_sym less_eq_def) 
        qed
        moreover
        have "\<forall> s' \<in> cgc_state.toNext (refmap (r1, r2)) . s \<preceq> s'"
        proof auto
          fix s'
          assume "s' \<in> cgc_state.toNext r2"
          with this obtain s'' where 4:"s'' \<preceq> s'" and 5:"s'' \<in> cgc_state.fromPrev r2" using inv5
            by (auto simp add:inv5_def)
          have 6:"s \<preceq> s''" using 5 inv1 inv2 1 by (auto simp add:inv2_def inv1_def learn_def)
          show "s \<preceq> s'" using 4 6
            by (metis pre_CStruct.trans)
        qed
        ultimately
        show ?thesis by (auto simp add:learn_def)
      qed
      thus ?thesis by (auto simp add:defs1 ref_defs)
    qed next

lemma trace_incl:"traces composition \<subseteq> traces spec"
apply(rule ref_map_soundness[of refmap])
  defer
  apply(simp add:defs1)
  apply(intro set_eqI; case_tac x; force)
  apply(insert refok, auto)
done

theorem composition: "composition =<| spec"
apply(simp add:ioa_implements_def)
apply(intro conjI)
  apply(simp add:defs1)
  apply(intro set_eqI; case_tac x; force)
  apply(simp add:defs1)
  apply(intro set_eqI; case_tac x; force)
  apply (insert trace_incl, auto)
done

end

end