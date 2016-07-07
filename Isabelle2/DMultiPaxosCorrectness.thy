theory DMultiPaxosCorrectness
imports "../../IO-Automata/Simulations" "../../IO-Automata/IOA_Automation" 
  "~~/src/HOL/Library/Monad_Syntax" "~~/src/HOL/Library/Code_Target_Numeral"
  "~~/src/HOL/Library/FinFun_Syntax"
begin

type_synonym acc = nat
type_synonym bal = nat
type_synonym inst = nat
typedecl cmd
consts accs :: "acc set"

datatype msgs = 
  Msg1a bal|
  Msg1b acc inst bal "bal \<times> cmd option"|
  Msg2a inst bal cmd

record mp_state = 
  ballot :: "acc \<Rightarrow>f bal"
  vote ::"acc \<Rightarrow>f inst \<Rightarrow>f bal \<Rightarrow>f cmd option"
  network :: "msgs set"
  propCmds :: "cmd option set"

definition maxAcceptorVote::"acc \<Rightarrow> inst \<Rightarrow> mp_state \<Rightarrow> (bal \<times> cmd option)" where
  "maxAcceptorVote a i s \<equiv> 
    let bals = finfun_to_list ((vote s) $ a $ i);
      bals_flt = (filter (\<lambda>b. (((vote s) $ a $ i) $ b) \<noteq> None) bals) @ [0];
      maxBal = (fold max bals_flt (bals_flt!0));
      v = (if maxBal > 0 then (((vote s) $ a $ i) $ maxBal) else None) in
    (maxBal, v)"

definition safe_at where
  "safe_at m1bmsgs \<equiv> (let 
    m1bnum = card m1bmsgs in
    if (m1bnum * 2 > card accs) then True
    else False)"

definition safeVote::"msgs set \<Rightarrow> mp_state \<Rightarrow> cmd option set" where
  "safeVote m1bmsgs state \<equiv> let 
      m1bpair = image (\<lambda>nm. case nm of (Msg1b _ _ _ vs) \<Rightarrow> vs) m1bmsgs;
      m1bBal = image (\<lambda>x. fst x) m1bpair;
      maxBal = the_elem (Set.filter (\<lambda>le. \<forall>x \<in> m1bBal. x \<le> le) m1bBal);
      maxVal = image (\<lambda>x. snd x) (Set.filter (\<lambda>le. fst le = maxBal) m1bpair);
      safeVal = Set.remove None maxVal in
   if (safeVal \<noteq> {}) then safeVal else propCmds state"

inductive_set reach :: "mp_state set"
where
init:
  "\<lparr> ballot = (K$ 0), vote = (K$ K$ K$ None),
    network = {}, propCmds = {}\<rparr> \<in> reach"
| propose:
  "\<lbrakk> s \<in> reach; c \<notin> propCmds s \<rbrakk> \<Longrightarrow>
    s\<lparr> propCmds := (propCmds s) \<union> {c} \<rparr> \<in> reach"
| phase1a:
  "\<lbrakk> s \<in> reach; Msg1a b \<notin> network s \<rbrakk> \<Longrightarrow>
    s\<lparr> network := (network s) \<union> {Msg1a b} \<rparr> \<in> reach"
| phase1b:
  "\<lbrakk> s \<in> reach; Msg1a b \<in> network s; a \<in> accs; 
    (ballot s) $ a < b; (maxBal, v) = (maxAcceptorVote a i s); Msg1b a i b (maxBal, v) \<notin> network s \<rbrakk> \<Longrightarrow>
    s\<lparr> ballot := (ballot s)(a $:= b), network := (network s) \<union> {Msg1b a i b (maxBal,v)} \<rparr> \<in> reach"
| phase2a:
  "\<lbrakk> s \<in> reach; 
    m2anum = card (Set.filter (\<lambda>nm. case nm of Msg2a i2 b2 _ \<Rightarrow> (i2 = i \<and> b2 = b)| _ \<Rightarrow> False) (network s)); m2anum = 0; 
    m1bmsgs = Set.filter (\<lambda>nm. case nm of Msg1b _ i2 b2 _ \<Rightarrow> (i2 = i \<and> b2 = b)| _ \<Rightarrow> False) (network s);
    safe_at m1bmsgs; safeVal = safeVote m1bmsgs s; Some c \<in> safeVal \<rbrakk> \<Longrightarrow>
    s\<lparr> network := (network s) \<union> {Msg2a i b c} \<rparr> \<in> reach"
| vote_cmd:
  "\<lbrakk> s \<in> reach; a \<in> accs; b = (ballot s) $ a; Msg2a i b c \<in> network s\<rbrakk> \<Longrightarrow>
    s\<lparr> vote := (vote s)(a $:= ((vote s) $ a) (i $:= ((vote s) $ a $ i)(b $:= Some c))) \<rparr> \<in> reach"

lemma set_joint[simp]:
  assumes "finite accs" and "q1 \<subseteq> accs" and "q2 \<subseteq> accs" and 
  "2 * card q1 > card accs" and "2 * card q2 > card accs"
  shows "q1 \<inter> q2 \<noteq> {}"
proof
  assume "q1 \<inter> q2 = {}"
  hence 1:"card q1 + card q2 \<le> card accs" using assms(1,2,3)
    by (metis Un_subset_iff card_Un_disjoint card_mono finite_subset)
  have 2:"card q1 + card q2 > card accs" using assms(4,5)
    using add.commute add_less_imp_less_right le_less_trans less_imp_le_nat mult_2 not_le by linarith
  thus "False" using "1" leD by blast
qed

lemma set_prop[simp]:
  assumes "m2anum = card (Set.filter (\<lambda>nm. case nm of Msg2a i2 b2 x \<Rightarrow> i2 = i \<and> b2 = b
    | _ \<Rightarrow> False) s)" and "m2anum = 0" and "finite s"
  shows "Msg2a i b c \<notin> s"
proof
  assume "Msg2a i b c \<in> s"
  hence "Msg2a i b c \<in> (Set.filter (\<lambda>nm. case nm of Msg2a i2 b2 x \<Rightarrow> i2 = i \<and> b2 = b | _ \<Rightarrow> False) s)" by simp
  hence "(Set.filter (\<lambda>nm. case nm of Msg2a i2 b2 x \<Rightarrow> i2 = i \<and> b2 = b | _ \<Rightarrow> False) s) \<noteq> {}" by blast
  hence "m2anum \<noteq> 0" using assms(1,3)
    by (simp add: Collect_mem_eq Finite_Set.card_0_eq Set.filter_def finite_Collect_conjI)
  thus "False" using assms(2) by blast
qed

lemma cmd_safe[simp]:
  assumes "s \<in> reach" and "Msg2a i b c \<in> network s" and "finite accs" and "finite (network s)"
  shows "2 * card (Set.filter (\<lambda>nm. case nm of Msg1b _ i2 b2 _ \<Rightarrow> (i2 = i \<and> b2 = b)| _ \<Rightarrow> False) (network s)) > card accs"
using assms
proof(induct set: reach)
  case (init)
    show ?case using init.prems(1) by auto 
next
  case (propose s v)
    have " Msg2a i b c \<in> network s" using propose.prems(1)
      by (simp add: mp_state.ext_inject mp_state.surjective mp_state.update_convs(4))
    thus ?case using propose.prems(2,3) propose.hyps(2)
      using mp_state.iffs mp_state.surjective mp_state.update_convs(4) by auto
next
  case (phase1a s)
  have " Msg2a i b c \<in> network s" using phase1a.prems(1)
    by (simp add: Un_empty_right Un_insert_right insertE mp_state.ext_inject mp_state.surjective mp_state.update_convs(3) msgs.simps(7))
  thus ?case using phase1a.prems(2,3) phase1a.hyps(2)
    by (smt Collect_cong Set.filter_def Un_insert_right finite_Un insert_iff mp_state.ext_inject mp_state.surjective mp_state.update_convs(3) msgs.simps(10) sup_bot.right_neutral)  
next
  case (vote_cmd s a' b' i' c')
  have " Msg2a i b c \<in> network s" using vote_cmd.prems(1)
    by (simp add: mp_state.ext_inject mp_state.surjective mp_state.update_convs(2))
  thus ?case using vote_cmd.prems(2,3) vote_cmd.hyps(2)
    by (simp add: mp_state.ext_inject mp_state.surjective mp_state.update_convs(2))
next
  case (phase1b s b' a' maxB v' i')
  have " Msg2a i b c \<in> network s" using phase1b.prems(1)
    using UnE mp_state.ext_inject mp_state.surjective mp_state.update_convs(3) msgs.simps(9) singletonD by auto
  hence 0:"card accs < 2 * card (Set.filter (\<lambda>a. case a of Msg1b x i2 b2 xa \<Rightarrow> i2 = i \<and> b2 = b | _ \<Rightarrow> False) (network s))"
    using phase1b.prems(2,3) phase1b.hyps(2)
      by (simp add: finite_Un mp_state.select_convs(3) mp_state.surjective mp_state.update_convs(3))
  have "(network s) \<subseteq> (network (s\<lparr>ballot := (ballot s)(a' $:= b'), network := network s \<union> {Msg1b a' i' b' (maxB, v')}\<rparr>))"
    by (simp add: Un_empty_right Un_insert_right mp_state.ext_inject mp_state.surjective mp_state.update_convs(3) subset_insertI)
  hence 1:"Set.filter (\<lambda>a. case a of Msg1b x i2 b2 xa \<Rightarrow> i2 = i \<and> b2 = b | _ \<Rightarrow> False) (network s) \<subseteq>
    Set.filter (\<lambda>a. case a of Msg1b x i2 b2 xa \<Rightarrow> i2 = i \<and> b2 = b | _ \<Rightarrow> False) (network (s\<lparr>ballot := (ballot s)(a' $:= b'), network := network s \<union> {Msg1b a' i' b' (maxB, v')}\<rparr>))"
      by (simp add: subset_eq)
  have "finite (Set.filter (\<lambda>a. case a of Msg1b x i2 b2 xa \<Rightarrow> i2 = i \<and> b2 = b | _ \<Rightarrow> False) (network (s\<lparr>ballot := (ballot s)(a' $:= b'), network := network s \<union> {Msg1b a' i' b' (maxB, v')}\<rparr>)))"
    using phase1b.prems(3)
      by (simp add: Collect_mem_eq Set.filter_def finite_Collect_conjI)
  hence "card (Set.filter (\<lambda>a. case a of Msg1b x i2 b2 xa \<Rightarrow> i2 = i \<and> b2 = b | _ \<Rightarrow> False) (network s)) \<le>
    card (Set.filter (\<lambda>a. case a of Msg1b x i2 b2 xa \<Rightarrow> i2 = i \<and> b2 = b | _ \<Rightarrow> False) (network (s\<lparr>ballot := (ballot s)(a' $:= b'), network := network s \<union> {Msg1b a' i' b' (maxB, v')}\<rparr>)))"
      using phase1b.prems(3) 1 card_mono by blast 
  thus ?case using 0 using le_less_trans nat_mult_less_cancel_disj not_le by linarith 
next
  case (phase2a s m2anum i' b' m1bmsgs safeVal c')
  thus ?case
  proof(cases "i = i' \<and> b = b'")
    case True
    hence 0:"card accs < 2 * card (Set.filter (\<lambda>nm. case nm of
      Msg1b x i2 b2 xa \<Rightarrow> i2 = i \<and> b2 = b | _ \<Rightarrow> False) (network s))" using phase2a.hyps(5,6) unfolding safe_at_def
        using mult.commute by presburger
    have "(Set.filter (\<lambda>nm. case nm of Msg1b x i2 b2 xa \<Rightarrow> i2 = i \<and> b2 = b
      | _ \<Rightarrow> False) (network s)) \<subseteq> (Set.filter (\<lambda>a. case a of  Msg1b x i2 b2 xa \<Rightarrow> i2 = i \<and> b2 = b
        | _ \<Rightarrow> False) (network (s\<lparr>network :=  network s \<union> {Msg2a i' b' c'}\<rparr>)))" by auto
    hence "card (Set.filter (\<lambda>nm. case nm of Msg1b x i2 b2 xa \<Rightarrow> i2 = i \<and> b2 = b
      | _ \<Rightarrow> False) (network s)) \<le> card (Set.filter (\<lambda>a. case a of  Msg1b x i2 b2 xa \<Rightarrow> i2 = i \<and> b2 = b
        | _ \<Rightarrow> False) (network (s\<lparr>network :=  network s \<union> {Msg2a i' b' c'}\<rparr>)))" using phase2a.prems(3)
          by (simp add: Collect_mem_eq Set.filter_def card_mono finite_Collect_conjI)
    thus ?thesis  using 0 le_less_trans nat_mult_less_cancel_disj not_le by linarith
  next
    case False
    hence "Msg2a i b c \<in> network s" using phase2a.prems(1)
      using Un_insert_right insert_iff mp_state.cases mp_state.select_convs(3) mp_state.update_convs(3) msgs.inject(3) sup_bot.right_neutral by auto
    hence "card accs < 2 * card (Set.filter (\<lambda>a. case a of Msg1b x i2 b2 xa \<Rightarrow> i2 = i \<and> b2 = b
      | _ \<Rightarrow> False) (network s))" using phase2a.prems(2,3) phase2a.hyps(2)
        by (simp add: finite_Un mp_state.ext_inject mp_state.surjective mp_state.update_convs(3))
    thus ?thesis
      by (smt Collect_cong Set.filter_def Un_insert_right insert_iff mp_state.ext_inject mp_state.surjective mp_state.update_convs(3) msgs.simps(12) sup_bot.comm_neutral)
  qed
qed

lemma single_i_b[simp]:
  assumes "s \<in> reach" and "Msg2a i b c \<in> network s" and "finite accs" and "finite (network s)"
  shows "card (Set.filter (\<lambda>nm. case nm of Msg2a i2 b2 _ \<Rightarrow> (i2 = i \<and> b2 = b)| _ \<Rightarrow> False) (network s)) = 1"
using assms
proof(induct set: reach)
  case init
    thus ?case by (simp add: equals0D mp_state.select_convs(3))
next
  case propose
    thus ?case using mp_state.iffs mp_state.surjective mp_state.update_convs(4) by fastforce
next
  case (phase1a s b')
    have "Msg2a i b c \<in> network s" using phase1a.prems(1)
      by (simp add: UnE empty_iff insert_iff mp_state.select_convs(3) mp_state.surjective mp_state.update_convs(3) msgs.distinct(3)) 
    thus ?case using phase1a.prems(2,3) phase1a.hyps(2)
      by (smt Collect_cong Set.filter_def Un_insert_right finite_Un insert_iff mp_state.ext_inject mp_state.surjective mp_state.update_convs(3) msgs.simps(10) sup_bot.right_neutral)
next
  case (vote_cmd s a' b' i' c')
  have " Msg2a i b c \<in> network s" using vote_cmd.prems(1)
    by (simp add: mp_state.ext_inject mp_state.surjective mp_state.update_convs(2))
  thus ?case using vote_cmd.prems(2,3) vote_cmd.hyps(2)
    using mp_state.ext_inject mp_state.surjective mp_state.update_convs(2) by fastforce  
next
  case (phase1b s b' a' maxBal v' i')
    have 0:"Msg2a i b c \<in> network s" using phase1b.prems(1)
      by (simp add: Un_insert_right insert_iff mp_state.cases mp_state.select_convs(3) mp_state.update_convs(3) msgs.simps(9) sup_bot.right_neutral)
    have "finite (network s)" using phase1b.prems(3)
      by (simp add: finite_Un mp_state.select_convs(3) mp_state.surjective mp_state.update_convs(3))
    hence "card (Set.filter(\<lambda>a. case a of  Msg2a i2 b2 x \<Rightarrow> i2 = i \<and> b2 = b | _ \<Rightarrow> False) (network s)) = 1" 
      using 0 phase1b.prems(2) phase1b.hyps(2) by blast
    thus ?case
      by (smt Collect_cong Set.filter_def UnCI Un_insert_right insertE mp_state.select_convs(3) mp_state.surjective mp_state.update_convs(3) msgs.case(2) sup_bot.comm_neutral) 
next
  case (phase2a s m2anum i' b' m1bmsgs safeVal c')
    thus ?case
    proof(cases "i = i' \<and> b = b'")
      case True
        assume 0:"i = i' \<and> b = b'"
        hence "card (Set.filter (\<lambda>a. case a of Msg2a i2 b2 x \<Rightarrow> i2 = i \<and> b2 = b
          | _ \<Rightarrow> False) (network s)) = 0" using phase2a.hyps(3,4) by auto
        hence "Set.filter (\<lambda>a. case a of Msg2a i2 b2 x \<Rightarrow> i2 = i \<and> b2 = b
          | _ \<Rightarrow> False) (network s) = {}" using phase2a.prems(3)
            by (simp add: Collect_mem_eq Set.filter_def card_0_eq finite_Collect_conjI finite_Un mp_state.select_convs(3) mp_state.surjective mp_state.update_convs(3))
        hence "Set.filter (\<lambda>a. case a of Msg2a i2 b2 x \<Rightarrow> i2 = i \<and> b2 = b
          | _ \<Rightarrow> False) (network(s\<lparr>network :=  network s \<union> {Msg2a i' b' c'}\<rparr>)) = {Msg2a i b c'}" using 0
            using CollectD Collect_cong Set.filter_def Un_iff insertI2 member_filter mp_state.ext_inject mp_state.surjective mp_state.update_convs(3) msgs.simps(12) singletonI singleton_conv2 by auto    
        thus ?thesis using phase2a.prems(3) by auto
    next
      case False
        assume 1:"\<not> (i = i' \<and> b = b')"
        hence "Msg2a i b c \<in> network s" using phase2a.prems(1,3) by auto
        hence "card (Set.filter (\<lambda>a. case a of Msg2a i2 b2 x \<Rightarrow> i2 = i \<and> b2 = b | _ \<Rightarrow> False) (network s)) = 1"
          using phase2a.hyps(2) phase2a.prems(2,3) finite_Un mp_state.ext_inject mp_state.surjective mp_state.update_convs(3) by fastforce
        thus ?thesis using 1
          by (smt Collect_cong Set.filter_def Un_insert_right insert_iff mp_state.ext_inject mp_state.surjective mp_state.update_convs(3) msgs.simps(12) sup_bot.comm_neutral)
    qed
qed

lemma single_i_b_c[simp]:
  assumes "s \<in> reach" and "Msg2a i b c \<in> network s" and "finite accs" and "finite (network s)"
  shows "Set.filter (\<lambda>nm. case nm of Msg2a i2 b2 _ \<Rightarrow> (i2 = i \<and> b2 = b)| _ \<Rightarrow> False) (network s) = {Msg2a i b c}"
proof-
  have "card (Set.filter (\<lambda>nm. case nm of  Msg2a i2 b2 x \<Rightarrow> i2 = i \<and> b2 = b
    | _ \<Rightarrow> False) (network s)) = 1" using assms single_i_b by blast
  thus ?thesis using assms(2,4)
    by (smt Collect_cong Set.filter_def card_eq_1_iff mem_Collect_eq msgs.simps(12) singleton_conv2)
qed

lemma vote_msg2a[simp]:
  assumes "s \<in> reach" and "(vote s) $ a $ i $ b = Some c" and "finite accs" and "finite (network s)"
  shows "Msg2a i b c \<in> network s"
using assms
proof(induct set: reach)
  case init
    thus ?case by (simp add: finfun_const_apply mp_state.select_convs(2) option.distinct(1))
next
  case propose
    thus ?case by (metis mp_state.ext_inject mp_state.surjective mp_state.update_convs(4))
next
  case phase1a
    thus ?case by (metis UnCI finite_Un mp_state.ext_inject mp_state.surjective mp_state.update_convs(3)) 
next
  case phase1b
    thus ?case
      by (metis UnCI finite_Un mp_state.ext_inject mp_state.surjective mp_state.update_convs(1) mp_state.update_convs(3)) 
next
  case phase2a
    thus ?case by (metis UnCI finite_Un mp_state.ext_inject mp_state.surjective mp_state.update_convs(3))
next
  case vote_cmd
    thus ?case
      by (smt finfun_upd_apply_same finfun_upd_triv finfun_update_twist mp_state.ext_inject mp_state.surjective mp_state.update_convs(2) mp_state.update_convs(5) option.inject) 
qed

lemma safe_inv[simp]:
  assumes "s \<in> reach" and "finite accs" and "finite (network s)" and "acc\<^sub>1 \<in> accs" and "acc\<^sub>2 \<in> accs" and "acc\<^sub>1 \<noteq> acc\<^sub>2"
  and "cmd1 = ((vote s) $ acc\<^sub>1 $ i $ b)" and "cmd2 = ((vote s) $ acc\<^sub>2 $ i $ b)" and "cmd1 \<noteq> None" and "cmd2 \<noteq> None"
  shows "cmd1 = cmd2"
using assms
proof(induct set: reach)
  case init
    thus ?case by (simp add: finfun_const_apply mp_state.select_convs(2))
next
  case (propose s v)
    thus ?case by (simp add: mp_state.ext_inject mp_state.surjective mp_state.update_convs(4))
next
  case phase1a
    thus ?case by (simp add: mp_state.ext_inject mp_state.surjective mp_state.update_convs(3))
next
  case phase2a
    thus ?case by (metis finite_Un mp_state.ext_inject mp_state.surjective mp_state.update_convs(3)) 
next
  case (phase1b s b' a' maxNal v' i')
    thus ?case
      by (simp add: mp_state.ext_inject mp_state.surjective mp_state.update_convs(1) mp_state.update_convs(3)) 
next
  case (vote_cmd s a' b' i' c')
    thus ?case
    proof(cases "acc\<^sub>1 = a' \<and> i = i' \<and> b = b'")
      case True
        assume 0:"acc\<^sub>1 = a' \<and> i = i' \<and> b = b'"
        have 1:"i = i' \<and> b = b'" using 0 by blast
        have 2:"cmd2 = (vote s) $ acc\<^sub>2 $ i $ b" using vote_cmd.prems(7,5) 0
          by (simp add: finfun_upd_apply mp_state.ext_inject mp_state.surjective mp_state.update_convs(2))
        have 3:"cmd1 = Some c'" using vote_cmd.prems(6) 0
          by (simp add: finfun_upd_apply mp_state.ext_inject mp_state.surjective mp_state.update_convs(2))
        hence "Msg2a i b c' \<in> network (s\<lparr>vote := (vote s)(a' $:= (vote s $ a')(i' $:= (vote s $ a' $  i')(b' $:= Some
          c')))\<rparr>)" using vote_cmd.prems(6) 1 vote_cmd.hyps(5) vote_msg2a
            by (metis (no_types, lifting) mp_state.ext_inject mp_state.surjective mp_state.update_convs(2) mp_state.update_convs(5)) 
        hence 4:"Msg2a i b c' \<in> network s" using 1 vote_cmd.hyps(5) by blast
        have "Msg2a i b (the cmd2) \<in> network s" using 2 vote_cmd.hyps(1) vote_cmd.prems(1,2,9) vote_msg2a
          by (metis (no_types, lifting) mp_state.ext_inject mp_state.surjective mp_state.update_convs(2) mp_state.update_convs(5) option.exhaust_sel) 
        hence "Some c' = cmd2" using 3 4 assms(1,2,3,7,8) single_i_b_c
          by (metis msgs.inject(3) option.collapse the_elem_eq vote_cmd.prems(9) vote_msg2a)
        thus ?thesis using 3 by auto
    next
      case False
        assume 0:"\<not>(acc\<^sub>1 = a' \<and> i = i' \<and> b = b')"
        thus ?thesis
        proof(cases "acc\<^sub>2 = a' \<and> i = i' \<and> b = b'")
          case True
            assume 1:"acc\<^sub>2 = a' \<and> i = i' \<and> b = b'"
            hence 2:"i = i' \<and> b = b'" by blast
            have 3:"cmd1 = (vote s) $ acc\<^sub>1 $ i $ b" using vote_cmd.prems(6,5) 1
              by (simp add: finfun_upd_apply mp_state.ext_inject mp_state.surjective mp_state.update_convs(2))
            have 4:"cmd2 = Some c'" using vote_cmd.prems(7) 1
              by (simp add: finfun_upd_apply mp_state.ext_inject mp_state.surjective mp_state.update_convs(2))
            hence "Msg2a i b c' \<in> network (s\<lparr>vote := (vote s)(a' $:= (vote s $ a')(i' $:= (vote s $ a' $  i')(b' $:= Some
              c')))\<rparr>)" using vote_cmd.prems(7) 2 vote_cmd.hyps(5) vote_msg2a
                by (metis (no_types, lifting) mp_state.ext_inject mp_state.surjective mp_state.update_convs(2) mp_state.update_convs(5)) 
            hence 5:"Msg2a i b c' \<in> network s" using 2 vote_cmd.hyps(5) by blast
            have "Msg2a i b (the cmd1) \<in> network s" using 3 assms(2,3) vote_cmd.hyps(1) vote_cmd.prems(1,2,8) vote_msg2a
              by (metis (no_types, lifting) mp_state.ext_inject mp_state.surjective mp_state.update_convs(2) mp_state.update_convs(5) option.exhaust_sel) 
            hence "Some c' = cmd1" using 4 5 vote_cmd.prems(1,8) assms(1,3,7,8) vote_msg2a single_i_b_c
              by (metis msgs.inject(3) option.collapse the_elem_eq)
            thus ?thesis using 4 by auto
        next
          case False
            assume 1:"\<not>(acc\<^sub>2 = a' \<and> i = i' \<and> b = b')"
            have 2:"cmd1 = (vote s) $ acc\<^sub>1 $ i $ b" using vote_cmd.prems(6) 0
              by (smt finfun_upd_apply_same finfun_upd_triv finfun_update_twist mp_state.ext_inject mp_state.surjective mp_state.update_convs(2) mp_state.update_convs(5))
            have "cmd2 = (vote s) $ acc\<^sub>2 $ i $ b" using vote_cmd.prems(7) 1
              by (smt finfun_upd_apply_same finfun_upd_triv finfun_update_twist mp_state.ext_inject mp_state.surjective mp_state.update_convs(2) mp_state.update_convs(5))
            thus ?thesis using 2 vote_cmd.prems(1,2,3,4,5,8,9) vote_cmd.hyps(2)
              by (simp add: mp_state.ext_inject mp_state.surjective mp_state.update_convs(2))
        qed
  qed
qed

end