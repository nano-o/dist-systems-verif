section {* MultiPaxosL1 refines AbstractMultiPaxos7 *}

theory MultiPaxosL1Correctness
imports MultiPaxosL1 AbstractMultiPaxos7 "../../IO-Automata/Simulations"
  BallotArrayProperties
begin

locale l1_correctness = mp1  quorums learners for  quorums learners +
  fixes the_ioa :: "(('v,'a)mp_state, ('v,'a,'b)mp_action) ioa"
  defines "the_ioa \<equiv> mp_ioa"
    -- {* Here I just made this definition to "bind" all type variables so that I don't get
      weird behavior in apply scripts. *}
begin

interpretation amp: amp_ioa quorums learners .

context begin

subsection {* Renaming the IOAs to a common signature *}

private
datatype ('vv,'aa,'ll)common_act =
  Learn nat 'vv 'll
| Propose 'vv
| Vote 'aa nat 'vv
| VoteQ 'aa "'aa set" nat 'vv
| JoinBallot 'aa nat
| Suggest 'aa 'vv nat nat "'aa set"

fun rn_1 where   
  "rn_1 (Propose v) = Some (mp_action.Propose v)"
| "rn_1 (Learn i v l) = Some (mp_action.Learn i v l)"
| "rn_1 (VoteQ a q i v) = None"
| "rn_1 (JoinBallot a i) = Some (mp_action.JoinBallot a i)"
| "rn_1 (Vote a i v) = Some (mp_action.Vote a i v)"
| "rn_1 (Suggest a v i b q) = Some (mp_action.Suggest a v i b q)"

fun rn_2 where 
  "rn_2 (Propose v) = Some (amp.Propose v)"
| "rn_2 (Learn i v l) = Some (amp.Learn i v l)"
| "rn_2 (VoteQ a q i v) = Some (amp.Vote a q i v)"
| "rn_2 (JoinBallot a i) = Some (amp.JoinBallot a i)"
| "rn_2 (Vote a i v) = None"
| "rn_2 (Suggest a v i b q) = None"

definition amp_ioa_2 :: "(('v, 'a) amp_state, ('v, 'a, 'b) common_act) ioa" where
  "amp_ioa_2 \<equiv> rename amp.amp_ioa rn_2"

definition mp_ioa_2 :: "(('v, 'a) mp_state, ('v, 'a, 'b) common_act) ioa" where
  "mp_ioa_2 \<equiv> rename mp_ioa rn_1"

subsection {* Invariants *}

lemmas ioa_simps = rename_def rename_set_def refines_def is_trans_def trace_def
  externals_def schedule_def filter_act_def
lemmas simps = amp_ioa_2_def mp_ioa_2_def amp.simps simps ioa_simps
declare simps[inv_proofs_defs]

text {* A suggestion is safe_at. *}

definition inv1 :: "('v, 'a) mp_state \<Rightarrow> bool" where 
  "inv1 s \<equiv> \<forall> i b v . case suggestion of 
    Some v \<Rightarrow> ballot_array.safe_at s 
  | None \<Rightarrow> True"

definition inv3 :: "('v, 'a) mp_state \<Rightarrow> bool" where 
  -- {* votes are always equal to the suggestion. Why do I need this? *}
  "inv3 s \<equiv> \<forall> (a::'a) i b .
    case mp_state.vote s i a b of Some v \<Rightarrow> 
      (case suggestion s i b of Some w \<Rightarrow> v = w | None \<Rightarrow> False)
    | None \<Rightarrow> True"

lemmas inv_defs = inv3_def inv1_def

declare option.splits[split]

lemma inv3[invs]:"invariant mp_ioa inv3"
  -- {* Why is this one so painful? *}
apply (try_solve_inv2 inv_proofs_defs:inv_proofs_defs inv_defs ballot_array.conservative_array_def
  ballot_array.conservative_def)
apply (case_tac a; rm_reachable)
apply ((auto simp add:inv_proofs_defs inv_defs ballot_array.conservative_array_def
  ballot_array.conservative_def))
apply (metis option.collapse)
apply (metis option.collapse)
apply (metis option.collapse)
apply (metis option.collapse)
apply (metis option.collapse)
apply (metis option.collapse)
apply (metis option.collapse)
defer
apply (metis option.collapse)
apply (metis option.collapse)
by (metis option.simps(3))

lemma inv2[invs]:"invariant mp_ioa inv1"
apply (try_solve_inv2 inv_proofs_defs:inv_proofs_defs inv_defs ballot_array.conservative_array_def
  ballot_array.conservative_def)
apply (case_tac a; (auto simp add:inv_proofs_defs inv_defs ballot_array.conservative_array_def
  ballot_array.conservative_def; fail)?; rm_reachable)
subgoal premises p for s t act a _ i v
proof - 
  have "do_vote a i v s t" oops

subsection {* A refinement mapping proof *}

definition f where "f s \<equiv> \<lparr>
    propCmd = mp_state.propCmd s,
    ballot = mp_state.ballot s,
    vote = mp_state.vote s \<rparr>"

lemma "is_ref_map f mp_ioa_2 amp_ioa_2"
proof (auto simp add:is_ref_map_def)
  fix s
  assume "s \<in> start mp_ioa_2"
  thus "f s \<in> start amp_ioa_2" by (simp add:ioa_simps simps f_def)
next
  fix s t a 
  assume "reachable mp_ioa_2 s" and trans:"s \<midarrow>a\<midarrow>mp_ioa_2\<longrightarrow> t"
  show "\<exists>aa b. refines (aa, b) s a t amp_ioa_2 f"
  proof (cases a)
    case (Propose v)
    let ?s = "f s"
    let ?a = "[(Propose v, f t)]"
    show ?thesis using Propose trans
        apply (intro exI[where ?x="?s"] exI[where ?x="?a"], auto simp add:refines_def)
      apply (auto simp add:simps f_def)
    done
  next
    case (Learn x y z)
    let ?s = "f s"
    let ?a = "[(Learn x y z, f t)]"
    show ?thesis using Learn trans
        apply (intro exI[where ?x="?s"] exI[where ?x="?a"], auto simp add:refines_def)
      apply (auto simp add:simps  f_def)
    done
  next
  defer
    case (JoinBallot x y)
    let ?s = "f s"
    let ?a = "[(JoinBallot x y, f t)]"
    show ?thesis using JoinBallot trans
        apply (intro exI[where ?x="?s"] exI[where ?x="?a"], auto simp add:refines_def)
      apply (auto simp add:simps f_def)
    done
  next
    case (Suggest x1 x2 x3 x4 x5)
    let ?s = "f s"
    let ?a = "[]"
    show ?thesis using Suggest trans
        apply (intro exI[where ?x="?s"] exI[where ?x="?a"], auto simp add:refines_def)
      apply (auto simp add:simps f_def)
    done
  next (* Now I need an invariant saying that the suggestion comes from a quorum with all the right properties. *) oops
  

lemma "traces mp_ioa_2 \<subseteq> traces amp_ioa_2" oops

end


end
