theory Composition
imports ComposableGC "/home/nano/Documents/IO-Automata/Simulations"
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
  "initial \<equiv> cgc_ioa\<lparr>start := {\<lparr>propCmd = {}, learned = \<lambda> p . None, fromPrev = {\<bottom>}, toNext = {} \<rparr>}\<rparr>"

definition composition where
  "composition \<equiv> hide ((rename initial rn1) \<parallel> (rename cgc_ioa rn2)) {a . \<exists> s . a = Switch s}"

definition spec where
  "spec \<equiv> rename initial rn3"

definition inv1 where
  "inv1 r \<equiv> let r1 = fst r; r2 = snd r in
    (\<forall> s \<in> cgc_state.fromPrev r2 . \<forall> l . 
      case cgc_state.learned r1 l of Some s' \<Rightarrow> s' \<preceq> s | None \<Rightarrow> True)"

definition inv2 where
  "inv2 r \<equiv> let r1 = fst r; r2 = snd r in 
    cgc_state.fromPrev r2 = cgc_state.toNext r1"

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

abbreviation refmap where
  "refmap r \<equiv> let r1 = fst r; r2 = snd r in 
    \<lparr>cgc_state.propCmd = propCmd r1 \<union> propCmd r2, 
      cgc_state.learned = (\<lambda> l . case learned r2 l of None \<Rightarrow> learned r1 l | _ \<Rightarrow> learned r2 l), 
      cgc_state.fromPrev = {\<bottom>}, 
      toNext = cgc_state.toNext r2\<rparr>"

lemma refok:"is_ref_map refmap composition spec"
apply(simp add:is_ref_map_def, rule conjI; clarify)
 apply(simp add:defs1)
 apply(case_tac ab, auto)
   apply(thin_tac "reachable composition (a, b)")
   apply(rule_tac x="refmap (a,b)" in exI)
   apply(rule_tac x="[(Propose1 x1,refmap (aa,ba))]" in exI)
   apply(simp add:defs1 ref_defs)
   apply(simp add:fun_eq_iff, rule allI) 
   apply(case_tac "learned ba x", force+)

   apply(thin_tac "reachable composition (a, b)")
   apply(rule_tac x="refmap (a,b)" in exI)
   apply(rule_tac x="[(Propose2 x2,refmap (aa,ba))]" in exI)
   apply(simp add:defs1 ref_defs)
   apply(simp add:fun_eq_iff, rule allI) 
   apply(case_tac "learned b x", auto)

   prefer 3
   apply(thin_tac "reachable composition (a, b)")
   apply(rule_tac x="refmap (a,b)" in exI)
   apply(rule_tac x="[]" in exI)
   apply(simp add:defs1 ref_defs)
   apply auto
   apply(simp add:fun_eq_iff, rule allI) 
   apply(case_tac "learned b x", auto)

  apply(thin_tac "reachable composition (a, b)")
   apply(rule_tac x="refmap (a,b)" in exI)
   apply(rule_tac x="[(Learn1 x31 x32,refmap (aa,ba))]" in exI)
   apply(simp add:defs1 ref_defs)
sorry

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