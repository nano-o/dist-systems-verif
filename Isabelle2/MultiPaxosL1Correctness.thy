theory MultiPaxosL1Correctness
imports MultiPaxosL1 AbstractMultiPaxos7 "../../IO-Automata/Simulations"
begin

locale l1_correctness = mp1
begin

interpretation amp: amp_ioa acceptors quorums learners .

fun rn where 
  "rn (Propose v) = Some (amp.Propose v)"
| "rn (Learn i v l) = Some (amp.Learn i v l)"
| "rn (Vote a q i v) = Some (amp.Vote a q i v)"
| "rn (JoinBallot a i) = Some (amp.JoinBallot a i)"
| "rn (Suggest a v i b q) = None"

definition f where "f s \<equiv> \<lparr>
    propCmd = mp_state.propCmd s,
    ballot = mp_state.ballot s,
    vote = mp_state.vote s \<rparr>"

definition amp_ioa_2 where
  "amp_ioa_2 \<equiv> rename amp.amp_ioa rn"

lemmas ioa_simps = rename_def rename_set_def refines_def is_trans_def trace_def
  externals_def schedule_def filter_act_def
lemmas simps = amp_ioa_2_def amp.simps f_def simps ioa_simps

definition inv1 where 
  "inv1 s \<equiv> let v = suggestion s in 
    (v \<in> propCmd s \<and> (\<exists> q \<in> quorums . True))"

lemma "is_ref_map f mp_ioa amp_ioa_2"
proof (auto simp add:is_ref_map_def)
  fix s
  assume "s \<in> start mp_ioa"
  thus "f s \<in> start amp_ioa_2" by (simp add:ioa_simps simps)
next
  fix s t a 
  assume "reachable mp_ioa s" and trans:"s \<midarrow>a\<midarrow>mp_ioa\<longrightarrow> t"
  show "\<exists>aa b. refines (aa, b) s a t amp_ioa_2 f"
  proof (cases a)
    case (Propose v)
    let ?s = "f s"
    let ?a = "[(Propose v, f t)]"
    show ?thesis using Propose trans
        apply (intro exI[where ?x="?s"] exI[where ?x="?a"], auto simp add:refines_def)
      apply (auto simp add:simps)
    done
  next
    case (Learn x y z)
    let ?s = "f s"
    let ?a = "[(Learn x y z, f t)]"
    show ?thesis using Learn trans
        apply (intro exI[where ?x="?s"] exI[where ?x="?a"], auto simp add:refines_def)
      apply (auto simp add:simps)
    done
  next
  defer
    case (JoinBallot x y)
    let ?s = "f s"
    let ?a = "[(JoinBallot x y, f t)]"
    show ?thesis using JoinBallot trans
        apply (intro exI[where ?x="?s"] exI[where ?x="?a"], auto simp add:refines_def)
      apply (auto simp add:simps)
    done
  next
    case (Suggest x1 x2 x3 x4 x5)
    let ?s = "f s"
    let ?a = "[]"
    show ?thesis using Suggest trans
        apply (intro exI[where ?x="?s"] exI[where ?x="?a"], auto simp add:refines_def)
      apply (auto simp add:simps)
    done
  next (* Now I need an invariant saying that the suggestion comes from a quorum with all the right properties. *) oops
  

lemma "traces mp_ioa \<subseteq> traces amp_ioa_2" oops

end


end
