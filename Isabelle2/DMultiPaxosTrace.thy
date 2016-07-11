theory DMultiPaxosTrace
imports "~~/src/HOL/Library/FinFun_Syntax"
begin

type_synonym acc = nat
type_synonym bal = nat
type_synonym inst = nat
type_synonym cmd = nat

datatype msgs = 
  Msg1a bal|
  Msg1b acc inst bal "bal \<times> cmd option"|
  Msg2a inst bal cmd

datatype event = 
  Propose cmd|
  Phase1a bal|
  Phase1b acc inst bal "bal \<times> cmd option"|
  Phase2a inst bal cmd nat|
  VoteCmd acc inst bal cmd


(* record mp_state = 
  ballot :: "acc \<Rightarrow> bal"
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

fun transit::"event list \<Rightarrow> mp_state" where
  "transit [] = \<lparr>ballot = (\<lambda>a. 0), vote = (K$ K$ K$ None),
    network = {}, propCmds = {}\<rparr>"
  |"transit (e#es) = (let s = transit es; ns = network s in
    case e of Propose c \<Rightarrow> (let pCmds = propCmds s in
        if Some c \<notin> pCmds then s\<lparr> propCmds := pCmds \<union> {Some c} \<rparr> else s)
      |Phase1a b \<Rightarrow> if (b > 0 \<and> Msg1a b \<notin> ns) then s\<lparr> network := ns \<union> {Msg1a b} \<rparr> else s
      |Phase1b a i b vs \<Rightarrow> (let (maxBal, v) = (maxAcceptorVote a i s); b' = ballot s a in 
        if (Msg1a b \<in> ns \<and> b' < b \<and> (Msg1b a i b (maxBal, v)) \<notin> ns) 
          then s\<lparr> ballot := (ballot s)(a := b), network := ns \<union> {Msg1b a i b (maxBal,v)} \<rparr> else s)
      |Phase2a i b c \<Rightarrow> (let m2anum = card (Set.filter (\<lambda>nm. case nm of Msg2a i2 b2 _ \<Rightarrow> (i2 = i \<and> b2 = b)| _ \<Rightarrow> False) ns)
        in if m2anum = 0 then (let m1bmsgs = Set.filter (\<lambda>nm. case nm of Msg1b _ i2 b2 _ \<Rightarrow> (i2 = i \<and> b2 = b)| _ \<Rightarrow> False) ns
          in if safe_at m1bmsgs then (let safeVal = safeVote m1bmsgs s in
            if Some c \<in> safeVal then s\<lparr> network := ns \<union> {Msg2a i b c} \<rparr> else s) else s) else s)
      |VoteCmd a i b c \<Rightarrow> if (b = (ballot s) a \<and> Msg2a i b c \<in> ns) 
        then s\<lparr> vote := (vote s)(a $:= ((vote s) $ a) (i $:= ((vote s) $ a $ i)(b $:= Some c))) \<rparr>
        else s)" *)

fun propCmds :: "event list \<Rightarrow> cmd option set" where
  "propCmds [] = {}"
  |"propCmds ((Propose c)#es) = (insert (Some c) (propCmds es))"
  |"propCmds (_#es) = (propCmds es)"

definition safe_at where
  "safe_at m1bmsgs nas \<equiv> (let m1bnum = card m1bmsgs in
    if (m1bnum * 2 > nas) then True else False)"

definition safeVote::"msgs set \<Rightarrow> event list \<Rightarrow> cmd option set" where
  "safeVote m1bmsgs state \<equiv> let 
      m1bpair = image (\<lambda>nm. case nm of (Msg1b _ _ _ vs) \<Rightarrow> vs) m1bmsgs;
      m1bBal = image (\<lambda>x. fst x) m1bpair;
      maxBal = the_elem (Set.filter (\<lambda>le. \<forall>x \<in> m1bBal. x \<le> le) m1bBal);
      maxVal = image (\<lambda>x. snd x) (Set.filter (\<lambda>le. fst le = maxBal) m1bpair);
      safeVal = Set.remove None maxVal in
   if (safeVal \<noteq> {}) then safeVal else propCmds state"

definition maxAcceptorVote::"(bal \<Rightarrow>f cmd option) \<Rightarrow> (bal \<times> cmd option)" where
  "maxAcceptorVote vs \<equiv> 
    let bals = finfun_to_list vs;
      bals_flt = (filter (\<lambda>b. (vs $ b) \<noteq> None) bals) @ [0];
      maxBal = (fold max bals_flt (bals_flt!0));
      v = (if maxBal > 0 then (vs $ maxBal) else None) in
    (maxBal, v)"

fun ballot :: "event list \<Rightarrow> acc \<Rightarrow> bal" and
  network :: "event list \<Rightarrow> msgs set" and
  vote :: "event list \<Rightarrow> acc \<Rightarrow> inst \<Rightarrow> (bal \<Rightarrow>f cmd option)" where
    "ballot [] a = 0"
    |"ballot (e#s) a = (let b = ballot s a in
      case e of Phase1b a' i' b' vs \<Rightarrow> if (a' = a \<and> b < b' \<and> (Msg1a b') \<in> network s) then b' else b |  _ \<Rightarrow> b)"
    |"network [] = {}"
    |"network (e#s) = (case e of Phase1a b \<Rightarrow> (let ns = network s in if (Msg1a b \<notin> ns) then ns \<union> {Msg1a b} else ns)
        |Phase1b a i b vs \<Rightarrow> (let ns = network s in (if (ballot s a < b \<and> (Msg1a b) \<in> ns) then
          (let (maxBal, v) = (maxAcceptorVote (vote s a i)) in 
            if ((Msg1b a i b (maxBal, v)) \<notin> ns) 
              then ns \<union> {Msg1b a i b (maxBal,v)} else ns) else ns))
        |Phase2a i b c nas \<Rightarrow> (if card (Set.filter (\<lambda>a. case a of Msg2a i2 b2 _ \<Rightarrow> (i2 = i \<and> b2 = b)| _ \<Rightarrow> False) (network s)) = 0 then 
          (let m1bmsgs = Set.filter (\<lambda>a. case a of Msg1b _ i2 b2 _ \<Rightarrow> (i2 = i \<and> b2 = b)| _ \<Rightarrow> False) (network s)
            in if safe_at m1bmsgs nas then (let safeVal = safeVote m1bmsgs s in
              if Some c \<in> safeVal then (network s) \<union> {Msg2a i b c} else (network s)) else (network s)) else (network s))
        |_ \<Rightarrow> network s)"
    |"vote [] a i = (K$ None)"
    |"vote (e#s) a i = (let vs = (vote s a i) in
        case e of VoteCmd a' i' b' c' \<Rightarrow> 
          if (a = a' \<and> i = i' \<and> b' = (ballot s a) \<and> Msg2a i b' c' \<in> network s) then vs(b' $:= Some c') else vs
      |_ \<Rightarrow> vs)"

fun paxos where
  "paxos [] = True"
| "paxos ((Propose c) # es) = True"
| "paxos ((Phase1a b) # es) = (b > 0 \<and> paxos es)"
| "paxos ((Phase1b a i b r) # es) = (started b es \<and> ballot_2 a es \<le> b \<and> r = last_vote_2 a i es \<and> paxos es)"
| "paxos ((Phase2a i b c) # es) = (safe_value i b c es \<and> paxos es)"
| "paxos ((VoteCmd a i b c) # es) = (suggestion i b es = Some c \<and> paxos es)"

thm network.simps(2)
lemma network_prop1[simp]:"network (Phase1a b # s) = network s \<or> network (Phase1a b # s) = network s \<union> {Msg1a b}"
   by (smt event.simps(27) network.simps(2))
lemma network_prop2[simp]:"network (Phase1b a i b vs # s) = network s \<or> network (Phase1b a i b vs # s) = network s \<union> {Msg1b a i b (maxAcceptorVote (vote s a i))}"
  by (smt event.simps(28) maxAcceptorVote_def network.simps(2) split_conv)
lemma network_prop3[simp]:"network (Phase2a i b c nas # s) = network s \<or> network (Phase2a i b c nas # s) = network s \<union> {Msg2a i b c}"
  by (smt event.simps(29) network.simps(2))
lemma network_prop4[simp]:"network ((Phase2a i b c nas) # es) = (if card (Set.filter (\<lambda>a. case a of Msg2a i2 b2 _ \<Rightarrow> (i2 = i \<and> b2 = b)| _ \<Rightarrow> False) (network es)) = 0 then 
  (let m1bmsgs = Set.filter (\<lambda>a. case a of Msg1b _ i2 b2 _ \<Rightarrow> (i2 = i \<and> b2 = b)| _ \<Rightarrow> False) (network es)
    in if safe_at m1bmsgs nas then (let safeVal = safeVote m1bmsgs es in
      if Some c \<in> safeVal then (network es) \<union> {Msg2a i b c} else (network es)) else (network es)) else (network es))"
using network.simps(2)[of _ es] by simp

lemma vote_prop1[simp]:"vote (VoteCmd a' i' b c # s) a i = (vote s a i) \<or> vote (VoteCmd a' i' b c # s) a i = (vote s a i)(b $:= Some c)"
  by (smt event.simps(30) vote.simps(2))

lemma vote_prop2[simp]:"(vote (VoteCmd a' i' b c # s) a i) $ b = ((vote s a i) $ b) \<or> (vote (VoteCmd a' i' b c # s) a i) $ b = Some c"
  using vote_prop1 by (metis finfun_upd_apply)
  
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

lemma set_prop1[simp]:
  assumes "Msg2a i b c \<in> s" and "finite s"
  shows "card (Set.filter (\<lambda>nm. case nm of Msg2a i2 b2 x \<Rightarrow> i2 = i \<and> b2 = b | _ \<Rightarrow> False) s) > 0"
using assms set_prop by blast

lemma set_prop2[simp]:
  assumes "Set.filter (\<lambda>nm. case nm of Msg2a i2 b2 x \<Rightarrow> i2 = i \<and> b2 = b | _ \<Rightarrow> False) s \<noteq> {}" and "finite s"
  shows "\<exists>c. Msg2a i b c \<in> s"
using assms unfolding Set.filter_def
proof-
  obtain e where 1:"e \<in> {a \<in> s. case a of Msg2a i2 b2 x \<Rightarrow> i2 = i \<and> b2 = b | _ \<Rightarrow> False}" using assms(1) by fastforce
  obtain c where "Msg2a i b c = e" using 1
    by (smt mem_Collect_eq msgs.exhaust msgs.simps(10) msgs.simps(11) msgs.simps(12))
  thus ?thesis using 1 mem_Collect_eq by blast
qed

lemma set_prop3[simp]:
  assumes "card (Set.filter (\<lambda>nm. case nm of Msg2a i2 b2 x \<Rightarrow> i2 = i \<and> b2 = b | _ \<Rightarrow> False) s) > 0" and "finite s"
  shows "\<exists>c. Msg2a i b c \<in> s"
using set_prop2 by (metis assms(1) assms(2) card_empty less_nat_zero_code)

lemma set_prop4[simp]:
  assumes "\<forall>c. Msg2a i b c \<notin> s" and "finite s"
  shows "card (Set.filter (\<lambda>nm. case nm of Msg2a i2 b2 x \<Rightarrow> i2 = i \<and> b2 = b | _ \<Rightarrow> False) s) = 0"
using set_prop3 assms card_empty set_prop2 by blast

lemma single_2a[simp]:
  assumes "Msg2a i b c \<in> network s" and "finite accs" and "finite (network s)"
  shows "card (Set.filter (\<lambda>nm. case nm of Msg2a i2 b2 _ \<Rightarrow> (i2 = i \<and> b2 = b)| _ \<Rightarrow> False) (network s)) = 1"
using assms
proof(induct s)
  case Nil
    thus ?case by (simp add: empty_iff network.simps(1))
next
  case (Cons e es)
    thus ?case
    proof(induct e arbitrary:es)
      case Propose
        thus ?case using event.simps(26) network.simps(2) by (metis (no_types, lifting)) 
    next
      case (Phase1a b')
        have 1:"card (Set.filter (\<lambda>a. case a of Msg2a i2 b2 x \<Rightarrow> i2 = i \<and> b2 = b
          | _ \<Rightarrow> False) (network es)) = 1" using Phase1a.prems
            by (metis UnE finite_Un msgs.simps(7) network_prop1 singletonD)
         have "network (Phase1a b' # es) = (network es) \<or> network (Phase1a b' # es)= network es \<union> {Msg1a b'}"
          using network_prop1 by blast
        thus ?case using 1 by (smt Collect_cong Set.filter_def UnCI UnE msgs.simps(10) singletonD)
    next
      case (Phase1b a' i' b' vs)
        have 0:"network (Phase1b a' i' b' vs # es) = (network es) \<or> network (Phase1b a' i' b' vs # es)= network es \<union> {Msg1b a' i' b' (maxAcceptorVote (vote es a' i'))}"
          using network_prop2 by blast
        hence 1:"Msg2a i b c \<in> network es" using Phase1b.prems(2)
          using UnE msgs.distinct(5) singletonD by blast
        hence 2:"card (Set.filter (\<lambda>a. case a of Msg2a i2 b2 x \<Rightarrow> i2 = i \<and> b2 = b
          | _ \<Rightarrow> False) (network es)) = 1" using Phase1b.prems 0 finite_Un by (metis (no_types, lifting)) 
        thus ?case using 0 by (smt Collect_cong Set.filter_def UnCI UnE msgs.simps(11) singletonD)
    next
      case (VoteCmd a' i' b' c')
        thus ?case using event.simps(30) network.simps(2) by (metis (no_types, lifting)) 
    next
      case (Phase2a i' b' c' nas)
        {
          assume "network (Phase2a i' b' c' nas # es) = network es"
          hence "card (Set.filter (\<lambda>a. case a of Msg2a i2 b2 x \<Rightarrow> i2 = i \<and> b2 = b
            | _ \<Rightarrow> False) (network (Phase2a i' b' c' nas # es))) = 1" using Phase2a.prems by presburger
        }
        moreover
        {
          assume 1:"network (Phase2a i' b' c' nas # es) = network es \<union> {Msg2a i' b' c'}"
          hence 5:"card (Set.filter (\<lambda>a. case a of Msg2a i2 b2 x \<Rightarrow> i2 = i \<and> b2 = b
            | _ \<Rightarrow> False) (network es \<union> {Msg2a i' b' c'})) = 1"
          proof(cases "Msg2a i' b' c' \<in> network es")
            case True
              assume 0:"Msg2a i' b' c' \<in> network es"
              hence "network (Phase2a i' b' c' nas # es) = network es"
                using "1" Un_insert_right insert_absorb sup_bot_right by blast
              thus ?thesis using 1 calculation by presburger
          next
            case False
              assume 0:"Msg2a i' b' c' \<notin> network es"
              thus ?thesis
              proof(cases "i = i' \<and> b = b'")
                case True
                  assume 2:"i = i' \<and> b = b'"
                  have 3:"card (Set.filter (\<lambda>a. case a of  Msg2a i2 b2 _ \<Rightarrow> (i2 = i \<and> b2 = b)
                    | _ \<Rightarrow> False) (network es)) = 0"
                  proof-
                    {
                      assume 3:"card (Set.filter (\<lambda>a. case a of Msg2a i2 b2 _ \<Rightarrow> (i2 = i \<and> b2 = b)
                        | _ \<Rightarrow> False) (network es)) \<noteq> 0"
                      hence "network ((Phase2a i b c' nas) # es) = network es" using network_prop4 by presburger
                      hence "False" using 2 1 0 using UnI2 insertI1 by blast
                    }
                    thus ?thesis by blast
                  qed
                  have "finite (network es)" using Phase2a.prems(4) by (metis 1 finite_Un)
                  hence "Set.filter (\<lambda>a. case a of  Msg2a i2 b2 x \<Rightarrow> i2 = i \<and> b2 = b
                    | _ \<Rightarrow> False) (network es) = {}" using 3
                      by (simp add: Collect_mem_eq Finite_Set.card_0_eq Set.filter_def finite_Collect_conjI)
                  thus ?thesis using 0 1 2 Phase2a.prems(2,4)
                    by (smt UnE card_eq_1_iff insertCI member_filter msgs.case(3) singletonD)
              next
                case False  
                  assume 2:"\<not>(i = i' \<and> b = b')"
                  hence "Msg2a i b c \<in> network es" using Phase2a.prems(2) 1 UnE msgs.inject(3) singletonD by blast
                  hence "card (Set.filter (\<lambda>a. case a of Msg2a i2 b2 x \<Rightarrow> i2 = i \<and> b2 = b | _ \<Rightarrow> False) (network es)) = 1"
                    using Phase2a.prems(1,3,4) by (metis "1" Un_infinite)
                  thus ?thesis using 2 0
                    by (smt Collect_cong Set.filter_def Un_insert_right insert_iff msgs.case(3) sup_bot.comm_neutral)
              qed
          qed
        }
        thus ?case by (metis calculation network_prop3) 
    qed
qed

lemma single_2a_set[simp]:
  assumes "Msg2a i b c \<in> network s" and "finite accs" and "finite (network s)"
  shows "Set.filter (\<lambda>nm. case nm of Msg2a i2 b2 _ \<Rightarrow> (i2 = i \<and> b2 = b)| _ \<Rightarrow> False) (network s) = {Msg2a i b c}"
proof-
  have "card (Set.filter (\<lambda>nm. case nm of  Msg2a i2 b2 x \<Rightarrow> i2 = i \<and> b2 = b
    | _ \<Rightarrow> False) (network s)) = 1" using assms single_2a by blast
  thus ?thesis using assms(1,3)
    by (smt Collect_cong Set.filter_def card_eq_1_iff mem_Collect_eq msgs.simps(12) singleton_conv2)
qed

lemma vote_msg2a[simp]:
  assumes "((vote s) a i) $ b = Some c" and "finite accs" and "finite (network s)"
  shows "Msg2a i b c \<in> network s"
using assms
proof(induct s)
  case Nil
    thus ?case by (simp add: finfun_const_apply option.simps(3) vote.simps(1))
next
  case (Cons e es)
    thus ?case
    proof(induct e)
      case Propose
        thus ?case by (metis (no_types, lifting) event.simps(26) network.simps(2) vote.simps(2))
    next
      case Phase1a
        thus ?case by (metis (no_types, lifting) UnCI event.simps(27) finite_Un network_prop1 vote.simps(2))
    next
      case Phase1b
        thus ?case by (metis (no_types, lifting) UnCI event.simps(28) finite_Un network_prop2 vote.simps(2))
    next
      case Phase2a
        thus ?case by (smt UnCI event.simps(29) finite_Un network_prop4 vote.simps(2))
    next
      case VoteCmd
        thus ?case by (smt event.simps(30) finfun_upd_apply network.simps(2) option.inject vote.simps(2))
    qed
qed
  
lemma safe_inv[simp]:
  assumes "finite accs" and "finite (network s)" and "acc\<^sub>1 \<in> accs" and "acc\<^sub>2 \<in> accs" and "acc\<^sub>1 \<noteq> acc\<^sub>2"
  and "cmd1 = ((vote s) acc\<^sub>1 i $ b)" and "cmd2 = ((vote s) acc\<^sub>2 i $ b)" and "cmd1 \<noteq> None" and "cmd2 \<noteq> None"
  shows "cmd1 = cmd2" 
using assms
proof(induct s)
  case Nil
    thus ?case by (simp add: vote.simps(1))
next
  case (Cons e es)
    thus ?case
    proof(induct e)
      case Propose
        thus ?case by (simp add: event.simps(26) network.simps(2) vote.simps(2))
    next  
      case Phase1a
        thus ?case by (smt event.simps(27) finite_Un network.simps(2) vote.simps(2))
    next
      case Phase1b
        have 1:"cmd1 = (vote es acc\<^sub>1 i) $ b" using Phase1b.prems(6,7) by simp
        have "cmd2 = (vote es acc\<^sub>2 i) $ b" using Phase1b.prems(6,8) by simp
        thus ?case using 1 Phase1b.prems by (metis finite_Un network_prop2)
    next
      case Phase2a
        have 1:"cmd1 = (vote es acc\<^sub>1 i) $ b" using Phase2a.prems(6,7) by simp
        have "cmd2 = (vote es acc\<^sub>2 i) $ b" using Phase2a.prems(7,8) by simp
        thus ?case using 1 Phase2a.prems by (metis finite_Un network_prop3) 
    next
      case (VoteCmd a i' b' c)
        thus ?case
        proof(cases "acc\<^sub>1 = a \<and> i = i' \<and> b = b'")
          case True
            assume 0:"acc\<^sub>1 = a \<and> i = i' \<and> b = b'"
            have 1:"cmd2 = (vote es acc\<^sub>2 i) $ b" using VoteCmd.prems(8,6) 0
              by (smt event.simps(30) vote.simps(2))
            have 2:"cmd1 = Some c \<or> cmd1 = ((vote es acc\<^sub>1 i) $ b)" using VoteCmd.prems(7) 0 vote_prop2 by blast
            {
              assume "cmd1 = ((vote es acc\<^sub>1 i) $ b)"
              hence "cmd1 = cmd2" using 1 VoteCmd.prems(1,2,3,4,5,6,9,10)
                by (simp add: event.simps(30) network.simps(2))
            }
            moreover
            {
              assume 3:"cmd1 = Some c"
              have "Msg2a i b c \<in> network ((VoteCmd a i' b' c) # es)" using VoteCmd.prems 1 vote_msg2a 3 by blast
              hence 4:"Msg2a i b c \<in> network es" using 1
                by (metis (no_types, lifting) event.simps(30) network.simps(2)) 
              have "Msg2a i b (the cmd2) \<in> network es" using 1 VoteCmd.prems(2,3,10) vote_msg2a
                by (metis (no_types, lifting) event.simps(30) network.simps(2) option.collapse)
              hence "Some c = cmd2" using 4assms(2,3,4,8,9) single_2a_set
                by (metis "3" assms(6) assms(7) empty_iff insert_iff msgs.inject(3) option.collapse vote_msg2a)
              hence "cmd1 = cmd2" using 3 by simp
            }
            thus ?thesis using 2 calculation by linarith
        next
          case False
            assume 0:"\<not>(acc\<^sub>1 = a \<and> i = i' \<and> b = b')"
            thus ?thesis
            proof(cases "acc\<^sub>2 = a \<and> i = i' \<and> b = b'")
              case True
                assume 1:"acc\<^sub>2 = a \<and> i = i' \<and> b = b'"
                hence 2:"i = i' \<and> b = b'" by blast
                have 3:"cmd1 = (vote s acc\<^sub>1 i) $ b" using VoteCmd.prems(7,6) 1 assms(6) by blast
                have 4:"cmd2 = Some c \<or> cmd2 = ((vote es acc\<^sub>2 i) $ b)" using VoteCmd.prems(8) 1 vote_prop2 by blast
                {
                  assume 5:"cmd2 = ((vote es acc\<^sub>2 i) $ b)"
                  hence "cmd1 = cmd2" using VoteCmd.prems(1,2,3,4,5,6,9,10) 3
                    by (smt True VoteCmd.prems(7) event.simps(30) network.simps(2) vote.simps(2))
                }
                moreover
                {
                  assume 5:"cmd2 = Some c"
                  have "Msg2a i b c \<in> network ((VoteCmd a i' b' c) # es)" using VoteCmd.prems(2,3,8) 2 vote_msg2a 5 by blast
                  hence 6:"Msg2a i b c \<in> network s" using 2 5 assms(2) assms(7) vote_msg2a by blast 
                  have "Msg2a i b (the cmd1) \<in> network s" using 3 assms(2,3) VoteCmd.prems(2,3,9) vote_msg2a
                    by (metis option.collapse)
                  hence "Some c = cmd1" using 4 5 VoteCmd.prems(2,9) assms(2,3,7,8) vote_msg2a single_2a_set
                    by (metis empty_iff insert_iff msgs.inject(3) option.collapse)
                  hence "cmd1 = cmd2" using 5 by simp
                }
                thus ?thesis using 4 calculation by linarith
            next
              case False
                assume 1:"\<not>(acc\<^sub>2 = a \<and> i = i' \<and> b = b')"
                have 2:"cmd1 = (vote es acc\<^sub>1 i) $ b" using VoteCmd.prems(7) 0 vote_prop2
                  by (smt event.simps(30) finfun_upd_apply_other vote.simps(2))
                have "cmd2 = (vote es acc\<^sub>2 i) $ b" using VoteCmd.prems(8) 1 vote_prop2
                  by (smt event.simps(30) finfun_upd_apply_other vote.simps(2))
                thus ?thesis using 2 VoteCmd.prems(1,2,3,4,5,6,9,10) event.simps(30) network.simps(2) by auto
            qed
        qed
    qed
qed

end