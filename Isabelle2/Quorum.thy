theory Quorum
imports ComposableGC  "~~/src/HOL/Eisbach/Eisbach_Tools" 
  "../../IO-Automata/Simulations"
begin

datatype ('a,'c,'l) q_action =
  Propose 'c 
| Learn 'a 'l
| FromPrev 'a
| ToNext 'a
| Init_Acc
| Accept

datatype acc_status =
  Idle | Ready | Stopped

record ('a,'c,'l,'p) q_state =
  propCmd :: "'c set"
  learned :: "'l \<Rightarrow> 'a set"
  from_prev :: "'a set"
  to_next :: "'a set"
  acc_cstruct :: "'p \<Rightarrow> 'a"
  acc_status :: "'p \<Rightarrow> acc_status"

locale Quorum = CStruct + IOA +
  fixes learners::"'l set" and acceptors::"'p set"
  assumes "acceptors \<noteq> {}"
begin

definition q_asig where
  "q_asig \<equiv> 
    \<lparr> inputs = { a . \<exists> c . a = Propose c  } \<union> { a . \<exists> s . a = FromPrev s },
      outputs = { a . \<exists> s p . a = Learn s p } \<union> { a . \<exists> s . a = ToNext s },
      internals = {Init_Acc, Accept} \<rparr>"

definition q_start where
  "q_start \<equiv> {\<lparr>propCmd = {}, learned = \<lambda> p . {}, from_prev = {}, to_next = {},
    acc_cstruct = \<lambda> p . \<bottom>, acc_status = \<lambda> p . Idle\<rparr>}"

definition propose where
  "propose c r r' \<equiv> (r' = r\<lparr>propCmd := (propCmd r) \<union> {c}\<rparr>)"

definition from_prev where
  "from_prev s r r' \<equiv> (r' = r\<lparr>from_prev := (q_state.from_prev r) \<union> {s}\<rparr>)"

definition to_next where
  "to_next s r r' \<equiv> \<exists> p \<in> acceptors .
    acc_cstruct r p = s \<and> acc_status r p = Ready
    \<and> (r' = r\<lparr>to_next := (q_state.to_next r) \<union> {s},
        acc_status := (acc_status r)(p := Stopped)\<rparr>)"

definition learn where
  "learn l s r r' \<equiv> 
    l \<in> learners
    \<and> (\<forall> p \<in> acceptors . acc_cstruct r p = s)
    \<and> r' = r\<lparr>learned := (learned r)(l := learned r l \<union> {s})\<rparr>"

definition init_acc where
  "init_acc r r' \<equiv> \<exists> p . \<exists> s \<in> q_state.from_prev r .
    acc_status r p = Idle
    \<and> r' = r\<lparr>acc_status := (acc_status r)(p := Ready), acc_cstruct := (acc_cstruct r)(p := s)\<rparr>"

definition accept where
  "accept r r' \<equiv> \<exists> p \<in> acceptors . \<exists> c \<in> q_state.propCmd r .
    acc_status r p = Ready
    \<and> r' = r\<lparr>acc_status := (acc_status r)(p := Ready), 
        acc_cstruct := (acc_cstruct r)(p := acc_cstruct r p \<bullet> c)\<rparr>"

fun q_trans_fun  where
  "q_trans_fun r (Propose c) r' = propose c r r'"
| "q_trans_fun r (FromPrev s) r' = from_prev s r r'"
| "q_trans_fun r (ToNext s) r' = to_next s r r'"
| "q_trans_fun r (Learn s l) r' = learn l s r r'"
| "q_trans_fun r (Init_Acc) r' = init_acc r r'"
| "q_trans_fun r (Accept) r' = accept r r'"

definition q_trans where
  "q_trans \<equiv> { (r,a,r') . q_trans_fun r a r'}"

definition q_ioa where
  "q_ioa \<equiv> \<lparr>ioa.asig = q_asig, start = q_start, trans = q_trans\<rparr>"

end

locale QProof = Quorum + c:ComposableGC
begin 

fun rn where
  "rn (Propose c) = Some (cgc_action.Propose c)"
| "rn (Learn a l) = Some (cgc_action.Learn a l)"
| "rn (FromPrev a) = Some (cgc_action.FromPrev a)"
| "rn (ToNext c) = Some (cgc_action.ToNext c)"
| "rn (Accept) = None"
| "rn (Init_Acc) = None"

definition spec where "spec \<equiv> rename c.cgc_ioa rn"

lemmas ioa_defs = spec_def par2_def asig_comp2_def c.cgc_ioa_def rename_def
    rename_set_def c.cgc_asig_def is_trans_def actions_def c.cgc_trans_def hide_def 
    propose_def q_ioa_def q_trans_def q_asig_def c.cgc_start_def q_start_def q_trans_def
lemmas actions_defs = learn_def
    hide_asig_def externals_def c.cgc_start_def spec_def c.learn_def c.fromPrev_def c.toNext_def
    spec_def accept_def init_acc_def c.propose_def from_prev_def to_next_def
lemmas ref_defs = refines_def actions_def trace_def schedule_def filter_act_def

named_theorems mydefs
  -- "definitions to unfold"
declare ioa_defs[mydefs]
declare actions_defs[mydefs]

definition refmap where
  "refmap r \<equiv> 
    \<lparr> cgc_state.propCmd = propCmd r,
      cgc_state.learned  = learned r,
      cgc_state.fromPrev = q_state.from_prev r,
      cgc_state.toNext = q_state.to_next r \<rparr>"

named_theorems inv_defs 
named_theorems invs
  -- "named theorem for use by the tactics below"
named_theorems aux_invs
  -- "auxiliary invariants used to prove the invariants needed for the refinement proof"
named_theorems ref_invs
  -- "the invariants needed for the refinement proof"

method bring_invs declares invs =
  -- "bring all the invariants in the premises"
  ( (insert invs) -- "insert invariant theorems in the premises; 
      this will allow us to use [thin] to get rid of them after use",
    ( (match premises in I[thin]:"invariant q_ioa ?inv"
        and R:"reachable q_ioa ?s" \<Rightarrow> 
            \<open>insert I[simplified invariant_def, rule_format, OF R]\<close>)+
        -- "for each invariant theorem, use the reachability assumption to obtain the invariant",
    (match premises in R[thin]:"reachable q_ioa ?s" 
      and T:"?s \<midarrow>?a\<midarrow>q_ioa\<longrightarrow> ?t" \<Rightarrow> 
        \<open>insert reachable_n[OF R T]\<close>),
    (insert invs),(match premises in I[thin]:"invariant q_ioa ?inv"
        and R:"reachable q_ioa ?s" \<Rightarrow> 
            \<open>insert I[simplified invariant_def, rule_format, OF R]\<close>)+,
    (match premises in R[thin]:"reachable q_ioa ?s" \<Rightarrow> succeed)
        -- "finally get rid of the reachability assumption"
        )? -- "don't fail if there are no invariants to bring"
    )

method try_solve_inv declares mydefs invs =
  ( rule invariantI, 
    simp add:mydefs inv_defs -- "solve the base case",
    bring_invs invs:invs,
    match premises in T:"?s \<midarrow>a\<midarrow>q_ioa\<longrightarrow> ?t" for a \<Rightarrow> \<open>case_tac a\<close> 
      -- "do case analysis on the action";
    simp add:mydefs inv_defs )

definition inv1 where
  "inv1 r \<equiv> \<forall> p \<in> acceptors . q_state.acc_status r p \<noteq> Idle \<longrightarrow> q_state.from_prev r \<noteq> {}"
declare inv1_def[inv_defs]

definition inv2 where
  "inv2 r \<equiv> \<forall> p \<in> acceptors . q_state.acc_status r p \<noteq> Idle \<longrightarrow> \<Sqinter> (q_state.from_prev r) \<preceq> acc_cstruct r p"
declare inv2_def[inv_defs]

definition inv3 where
  "inv3 r \<equiv> finite (q_state.from_prev r) \<and> finite (q_state.to_next r)"
declare inv3_def[inv_defs]

lemma inv3:"invariant q_ioa inv3"
apply try_solve_inv
apply auto
done
declare inv3[invs]

lemma inv1:"invariant q_ioa inv1"
apply try_solve_inv
subgoal by auto
subgoal by auto
subgoal by force
done
declare inv1[invs]

method my_bexE = match premises in E[thin]:"\<exists> p \<in> ?S . ?P p" \<Rightarrow> 
    \<open>rule_tac E[THEN bexE]\<close>
    -- "a useless method (just do elim bexE)"

lemma inv2:"invariant q_ioa inv2"
apply try_solve_inv
apply auto
apply (metis (no_types, lifting) equals0D glb_insert pre_CStruct.trans)
apply (metis acc_status.distinct(1))
apply (metis (full_types) coboundedI)
apply (metis (full_types) coboundedI)
by (smt less_bullet pre_CStruct.trans)
declare inv2[invs]

lemma refok:"is_ref_map refmap q_ioa spec" 
apply(simp add:is_ref_map_def refmap_def, rule conjI; clarify)
  subgoal by (force simp add:mydefs)

  apply(bring_invs invs:ref_invs)
  apply(case_tac a, auto)

    apply(rule_tac x="refmap s" in exI)
    apply(rule_tac x="[(Propose x1,refmap t)]" in exI)
    subgoal by (simp add:mydefs ref_defs refmap_def)
    
    defer

    apply(rule_tac x="refmap s" in exI)
    apply(rule_tac x="[(FromPrev x3,refmap t)]" in exI)
    subgoal by (simp add:ioa_defs actions_defs ref_defs refmap_def)

    defer    

    apply(rule_tac x="refmap s" in exI)
    apply(rule_tac x="[]" in exI)
    apply (simp add:ioa_defs actions_defs ref_defs refmap_def) 
    subgoal by force

    apply(rule_tac x="refmap s" in exI)
    apply(rule_tac x="[]" in exI)
    apply (simp add:ioa_defs actions_defs ref_defs refmap_def) 
    subgoal by force
      
  sorry

lemma trace_incl:"traces q_ioa \<subseteq> traces spec"
apply(rule ref_map_soundness[of refmap])
  subgoal by (insert refok, force)
  subgoal by (simp add:mydefs, intro set_eqI; case_tac x; force)
done

theorem composition: "q_ioa =<| spec"
apply(simp add:ioa_implements_def)
apply(intro conjI)
  subgoal by (simp add:mydefs, intro set_eqI; case_tac x; force)
  subgoal by (simp add:mydefs, intro set_eqI; case_tac x; force)
  subgoal by (insert trace_incl, auto)
done

end

end