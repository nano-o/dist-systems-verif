theory AbstractMultiPaxosR2
imports  AbstractMultiPaxosR1 "~~/src/HOL/Library/FinFun"
begin

text {*
1) Acceptors vote for a suggestion, and leaders use the distributed implementation of the safe-at computation.
2) Explicit 1b messages.
3) Explicit learning.
4) Catch-up.
5) Localizing suggestions (the leader function).
6) Explicit leadership acquisition.
7) Per-acceptor state.
8) finfuns.
*}

unbundle finfun_syntax
unbundle lifting_syntax

definition flip_def[simp]:"flip f \<equiv> \<lambda> x y . f y x"

section {* A test *}

definition acc_max_2 where
  "acc_max_2 (bound::nat) votes \<equiv> 
    if (\<exists> b < bound . votes b \<noteq> None)
    then Some (the_elem (max_by_key {(v,b) . b < bound \<and> votes b = Some v} snd))
    else None"

lemma acc_max_2_code[code]:
  "acc_max_2 bound votes = (
    if (\<exists> b \<in> {0..<bound} . votes b \<noteq> None)
    then let votes = ((\<lambda> b . votes b \<bind> (\<lambda> v . Some (v,b))) ` {0..<bound}) \<bind> option_as_set in
      Some (the_elem (max_by_key votes snd))
    else None)" sorry

context
begin

text {* The restriction operator is not executable, so does not work. *}

private
lemma acc_max_2_code_2: 
  "acc_max_2 bound votes = (
    if (\<exists> b \<in> {0..<bound} . votes b \<noteq> None)
    then let votes = ran ((\<lambda> b . votes b \<bind> (\<lambda> v . Some (v,b))) |` {0..<bound}) in
      Some (the_elem (max_by_key votes snd))
    else None)" oops
end

lemma "acc_max_2 b (vote s i a) = acc_max (vote s i) a b"
  by (auto simp add:acc_max_2_def acc_max_def distributed_safe_at.acc_max_def)


subsection {* Implementing the @{text acquire_leadership} action*}

locale acquire_leadership = 
  fixes onebs :: "'a \<Rightarrow>f bal \<Rightarrow>f (inst \<Rightarrow>f ('v\<times>bal) option) option"
  fixes b :: bal
begin
  
definition onebs' where "onebs' \<equiv> (\<lambda> ff1 . (\<lambda> off2 . the off2) o$ ff1) o$ onebs"

definition votes_at_b where "votes_at_b \<equiv> ((flip finfun_apply) b) o$ onebs'"
  
definition fold_fun where "fold_fun a ff \<equiv> 
  (case_prod union) o$ ($ option_as_set o$ (votes_at_b $ a), ff $)"

definition inst_votes where "inst_votes q \<equiv>
  Finite_Set.fold fold_fun (K$ {}) q"

lemma inst_votes_code[code]:"inst_votes (set xs) = fold fold_fun xs (K$ {})"
proof (induct xs)
  case Nil
  then show ?case by (auto simp add:inst_votes_def)
next
  case (Cons a xs)
  interpret folding_idem "fold_fun" "K$ {}"
    apply (unfold_locales)
    by (auto simp add:fun_eq_iff expand_finfun_eq fold_fun_def)
  show ?case using insert_idem
    by (metis (mono_tags, lifting) Cons.hyps List.finite_set comp_fun_commute eq_fold fold_commute_apply fold_simps(2) list.simps(15) inst_votes_def) 
qed

definition maxs where "maxs q \<equiv> (flip max_by_key snd) o$ inst_votes q"

definition the_suggestion :: "('v\<times>bal) set \<Rightarrow> 'v option" where "the_suggestion m \<equiv> 
  if m = {} then None else Some (fst (the_elem m))"

definition suggestion :: "nat \<Rightarrow>f nat \<Rightarrow>f 'v option \<Rightarrow> 'a set \<Rightarrow> nat \<Rightarrow>f nat \<Rightarrow>f 'v option" 
  where "suggestion old q \<equiv> (\<lambda> (m, ff) . ff(b $:= the_suggestion m))
    o$ ($ maxs q, old $)"
  
end

global_interpretation al:acquire_leadership onebs b
  for onebs b .

lift_definition finfun_acc_max_2 :: "nat \<Rightarrow> (nat \<Rightarrow>f 'c option) \<Rightarrow> ('c \<times> nat) option"
  is acc_max_2 .

section {* The IOA *}

record ('v,'a,'l) ampr2_state =
  propCmd :: "'v set"
  ballot :: "'a \<Rightarrow>f bal"
  vote :: "'a \<Rightarrow>f inst \<Rightarrow>f bal \<Rightarrow>f 'v option"
  vote2 :: "'a \<Rightarrow>f bal \<Rightarrow>f inst \<Rightarrow>f 'v option"
  suggestion :: "inst \<Rightarrow>f bal \<Rightarrow>f 'v option"
  onebs :: "'a \<Rightarrow>f bal \<Rightarrow>f (inst \<Rightarrow>f ('v\<times>bal) option) option"
  learned :: "'l \<Rightarrow>f inst \<Rightarrow>f 'v option"
  leader :: "'a \<Rightarrow>f bool"

locale ampr2_ioa = ampr1:ampr1_ioa quorums leader for quorums :: "'a set set" and leader
begin

definition asig where
  "asig \<equiv>
    \<lparr> inputs = { ampr1.Propose c | c . True},
      outputs = { ampr1.Learn i v l | i v l . True},
      internals = {ampr1.Internal}\<rparr>"

definition start where
  -- {* The initial state *}
  "start \<equiv> {\<lparr>propCmd = {}, ballot = K$ 0, vote = K$ K$ K$ None, 
    suggestion = K$ K$ None, onebs = K$ K$ None, learned = K$ K$ None,
    leader = (K$ False)(leader 0 $:= True)\<rparr>}"

subsection {* The transitions *}

definition propose where
  "propose c r r' \<equiv> (r' = r\<lparr>propCmd := (propCmd r) \<union> {c}\<rparr>)"

definition join_ballot where
  "join_ballot a b s s' \<equiv>
    let onebs'  = (finfun_acc_max_2 b) o$ (vote s $ a)
    in
      b > (ballot s $ a)
      \<and> s' = s\<lparr>ballot := (ballot s)(a $:= b),
        onebs := (onebs s)(a $:= (onebs s $ a)(b $:= Some onebs')),
        leader := (ampr2_state.leader s)(a $:= False)\<rparr>"

definition acquire_leadership where
  "acquire_leadership a q (s::('v,'a,'l) ampr2_state) s' \<equiv> let b = ballot s $ a in
    leader b = a
    \<and> q \<in> quorums
    \<and> \<not> ampr2_state.leader s $ a 
    \<and> (\<forall> a \<in> q . onebs s $ a $ b \<noteq> None)
    \<and> s' = s\<lparr>leader := (ampr2_state.leader s)(a $:= True),
        suggestion := al.suggestion (onebs s) b (suggestion s) q\<rparr>"

definition suggest where "suggest a i b v s s' \<equiv>
          v \<in> propCmd s
        \<and> ballot s $ a = b
        \<and> ampr2_state.leader s $ a
        \<and> (suggestion s $ i) $ b = None
        \<and> s' = s\<lparr>suggestion := (suggestion s)(i $:= (suggestion s $ i)(b $:= Some v))\<rparr>"

definition do_vote where
  "do_vote a i v s s' \<equiv> let b = ballot s $ a in
          vote s $ a $ i $ b = None
        \<and> (suggestion s $ i) $ b = Some v
        \<and> s' = s\<lparr>vote := (vote s)(a $:= (vote s $ a)(i $:= (vote s $ a $ i)(b $:= Some v)))\<rparr>"

term finfun_Ex

definition voted_v where "voted_v (s::('v,'a,'l) ampr2_state) i b v \<equiv>
  (\<lambda> ff1 . ff1 $ i $ b = Some v) o$ vote s"
  
definition voted_v_2 where "voted_v_2 (s::('v,'a,'l) ampr2_state) i q v \<equiv>
  vote s"

text {* Proving a code equation for that seems tough... *}

definition flip_binary_finfun :: "'a \<Rightarrow>f 'b \<Rightarrow>f 'c \<Rightarrow> 'b \<Rightarrow>f 'a \<Rightarrow>f 'c" where
  "flip_binary_finfun ff \<equiv> Abs_finfun (\<lambda> b . Abs_finfun (\<lambda> a . (ff $ a $ b)))"
  
lift_definition flip_binary_finfun_2 :: "'a \<Rightarrow>f 'b \<Rightarrow>f 'c \<Rightarrow> 'b \<Rightarrow>f 'a \<Rightarrow>f 'c"
  is "\<lambda> f . \<lambda> x y . f y x" oops
  
notepad begin
  fix votes :: "'a \<Rightarrow>f inst \<Rightarrow>f bal \<Rightarrow>f 'v option"
  fix i :: inst
  fix q :: "'a set"
  fix v :: 'v
  define at_i where "at_i \<equiv> (flip op$ i) o$ votes"
  define per_bal where "per_bal \<equiv> flip_binary_finfun at_i"
  define decision_at_bal where "decision_at_bal \<equiv> 
    (\<lambda> ff . finfun_All ((\<lambda> vo . vo = Some v) o$ ff)) o$ per_bal"
  define decided where "decided \<equiv> finfun_Ex decision_at_bal"
end
  
definition chosen where
  "chosen s i v \<equiv> \<exists> b . \<exists> q \<in> quorums . finfun_All (voted_v s i b v)"
  
notepad begin
  fix votes :: "inst \<Rightarrow>f bal \<Rightarrow>f 'a \<Rightarrow>f 'v option"
  fix i :: inst
  fix q :: "'a set"
  fix v :: 'v
  define at_i :: "bal \<Rightarrow>f 'a \<Rightarrow>f 'v option" where 
    "at_i \<equiv> votes $ i"
  define decision_at_bal where "decision_at_bal \<equiv> 
    (\<lambda> ff . finfun_All ((\<lambda> vo . vo = Some v) o$ ff)) o$ at_i"
    -- {* TODO: forall in quorum! *}
  define decided where "decided \<equiv> finfun_Ex decision_at_bal"
end

definition learn where
  "learn l i v s s' \<equiv> chosen s i v \<and> s' = s\<lparr>learned := (learned s)(l := (learned s l)(i := Some v))\<rparr>"

definition catch_up where
  "catch_up l1 l2 i v s s' \<equiv> learned s l2 i = Some v
    \<and> s' = s\<lparr>learned := (learned s)(l1 := (learned s l1)(i := Some v))\<rparr>"

fun trans_rel where
  "trans_rel r (ampr1.Propose c) r' = propose c r r'"
| "trans_rel r ampr1.Internal r' = (
    (\<exists> a b . join_ballot a b r r')
    \<or> (\<exists> a i v . do_vote a i v r r')
    \<or> (\<exists> a i b v . suggest a i b v r r')
    \<or> (\<exists> l1 l2 i v . catch_up l1 l2 i v r r')
    \<or> (\<exists> a q . acquire_leadership a q r r'))"
| "trans_rel r (ampr1.Learn i v l) r' = learn l i v r r'"

lemma trans_cases[consumes 1]:
  assumes "trans_rel r a r'"
  obtains 
  (propose) c where "propose c r r'"
| (learn) l i v where "learn l i v r r'"
| (join_ballot) a b where "join_ballot a b r r'"
| (do_vote) a i v where "do_vote a i v r r'"
| (suggest) a i b v where "suggest a i b v r r'"
| (catch_up) l1 l2 i v where "catch_up l1 l2 i v r r'"
| (acquire) a q where "acquire_leadership a q r r'"
using assms by induct auto

lemma trans_cases_2[consumes 1]:
  assumes "trans_rel r aa r'"
  obtains 
  (propose) c where "propose c r r'" and "aa = ampr1.action.Propose c"
| (learn) l i v where "learn l i v r r'" and "aa = ampr1.action.Learn i v l"
| (join_ballot) a b where "join_ballot a b r r'" and "aa = ampr1.action.Internal"
| (do_vote) a i v where "do_vote a i v r r'" and "aa = ampr1.action.Internal"
| (suggest) a i b v where "suggest a i b v r r'" and "aa = ampr1.action.Internal"
| (catch_up) l1 l2 i v where "catch_up l1 l2 i v r r'" and "aa = ampr1.action.Internal"
| (acquire) a q where "acquire_leadership a q r r'" and "aa = ampr1.action.Internal"
using assms by induct auto

definition trans where
  "trans \<equiv> { (r,a,r') . trans_rel r a r'}"

subsection {* The I/O-automaton *}

definition ioa where
  "ioa \<equiv> \<lparr>ioa.asig = asig, start = start, trans = trans\<rparr>"

lemmas simps = ioa_def asig_def start_def trans_def propose_def join_ballot_def 
  do_vote_def learn_def suggest_def catch_up_def acquire_leadership_def

end

end