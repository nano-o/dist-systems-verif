theory DMultiPaxosTrace2
imports "~~/src/HOL/Library/FinFun_Syntax"
begin

type_synonym acc = nat
type_synonym bal = nat
type_synonym inst = nat
type_synonym cmd = nat

definition nas where "nas \<equiv> 3"

datatype event = 
  Phase1a bal|
  Phase1b acc inst bal "(bal \<times> cmd) option"|
  Phase2a inst bal cmd |
  VoteCmd acc inst bal cmd

fun started where
  "started b [] = False"
| "started b ((Phase1a b2)#es) = (b = b2 \<or> started b es)"
| "started b (_ # es) = started b es"

fun ballot_2 where
  "ballot_2 a [] = 0"
| "ballot_2 a (e#es) = (let b = (ballot_2 a es) in
    case e of Phase1b a2 _ b2 _ \<Rightarrow> (if a = a2 \<and> b < b2 then b2 else b) | _ \<Rightarrow> b)"

fun last_vote_2 where
  "last_vote_2 a i [] = None"
| "last_vote_2 a i (e#es) = (case e of VoteCmd a2 i2 b c \<Rightarrow> 
    (if (a = a2 \<and> i = i2) then Some (b,c) else last_vote_2 a i es)
    | _ \<Rightarrow> last_vote_2 a i es)"

definition is_quorum where "is_quorum s \<equiv> 2 * (card s) > nas"

(*fun safe_value_rec where
  "safe_value_rec _ b c [] seen m = 
    (if is_quorum seen then (case m of None \<Rightarrow> True | Some (b2,c2) \<Rightarrow> c = c2) else False)"
| "safe_value_rec i b c ((VoteCmd a i2 b2 c2)#es) seen m =
    (if (a \<notin> seen \<and> i2 = i) then
      let seen' = (seen \<union> {a});
          m' = (if b2 < b then (case m of None \<Rightarrow> Some (b2,c2) | Some (b3,c3) \<Rightarrow> if b2 > b3 
            then Some (b2,c2) else m) else m)
      in if is_quorum seen' 
        then (case m' of None \<Rightarrow> True | Some (b3,c3) \<Rightarrow> c = c3)
        else safe_value_rec i b c es seen' m' 
    else safe_value_rec i b c es seen m)"
| "safe_value_rec i b c (_#es) seen m = safe_value_rec i b c es seen m"*)

fun safe_value_rec where
  "safe_value_rec i b c [] seen m = 
    (if is_quorum seen then (case m of None \<Rightarrow> True | Some (b2,c2) \<Rightarrow> c = c2) else False)"
| "safe_value_rec i b c ((Phase1b a i2 b2 vs)#es) seen m =
    (if (a \<notin> seen \<and> i2 = i \<and> b2 = b) then
      let seen' = (seen \<union> {a});
          m' = (case m of None \<Rightarrow> vs | Some (b3,c3) \<Rightarrow> (case vs of None \<Rightarrow> Some (b3,c3)|
            Some(b4,c4) \<Rightarrow> (if b4 > b3 then Some(b4,c4) else m)))
      in if is_quorum seen' 
        then (case m' of None \<Rightarrow> True | Some (b3,c3) \<Rightarrow> c = c3)
        else safe_value_rec i b c es seen' m' 
    else safe_value_rec i b c es seen m)"
| "safe_value_rec i b c (_#es) seen m = safe_value_rec i b c es seen m"

definition safe_value where 
  "safe_value i b c es = safe_value_rec i b c es {} None"

lemma assumes "b > 0" shows "\<not> safe_value i b c es" quickcheck oops

fun suggestion where 
  "suggestion i b [] = None"
| "suggestion i b ((Phase2a i2 b2 c)#es) = (if i2 = i \<and> b2 = b then Some c else suggestion i b es)"
| "suggestion i b (_#es) = suggestion i b es"

fun decide_rec where
  "decide_rec i b c [] seen = False"
| "decide_rec i b c ((VoteCmd a i2 b2 c2)#es) seen = (if (i = i2 \<and> b = b2 \<and> a \<notin> seen) then
    let seen' = seen \<union> {a} 
    in if (is_quorum seen') 
      then c2 = c
      else decide_rec i b c es seen'
  else decide_rec i b c es seen)"
| "decide_rec i b c (_#es) seen = decide_rec i b c es seen"

definition decide where "decide i b c es \<equiv> decide_rec i b c es {}"

fun paxos where
  "paxos [] = True"
| "paxos ((Phase1a b) # es) = (b > 0 \<and> paxos es)"
| "paxos ((Phase1b a i b r) # es) = (started b es \<and> ballot_2 a es \<le> b \<and> r = last_vote_2 a i es \<and> paxos es)"
| "paxos ((Phase2a i b c) # es) = (safe_value i b c es \<and> paxos es)"
| "paxos ((VoteCmd a i b c) # es) = (suggestion i b es = Some c \<and> paxos es)"

lemma "\<lbrakk>paxos es; ballot_2 a es = b\<rbrakk> \<Longrightarrow> \<not>(started b es)" quickcheck oops

lemma assumes "paxos es" and "a \<noteq> a2" 
  shows "\<not> (paxos ((Phase1b a2 i b r) # (Phase1b a i b r) # es))" quickcheck oops

lemma assumes "paxos es"
  shows "\<not> (paxos ((Phase2a i b c) # es))" quickcheck oops

lemma assumes "paxos es" and "a \<noteq> a2" 
  shows "last_vote_2 a i es = None \<or> last_vote_2 a2 i es = None" nitpick oops

lemma assumes "paxos es" shows "\<not> started b es" quickcheck oops

lemma assumes "paxos es" 
  shows "\<not> (started b es \<and> ballot_2 a es \<le> 1 \<and> r = last_vote_2 a i es \<and> r \<noteq> None)" quickcheck[eval="ballot_2 a es"]
oops

lemma assumes "paxos es" and "b \<noteq> 0" shows "suggestion i b es = None" nitpick
oops 

lemma assumes "paxos (e#es)"
  shows "\<not> (e = Phase1b a i b r)" quickcheck oops


lemma assumes "paxos es" and "decide i b c es" and "decide i b2 c2 es"
  shows "c2 = c" quickcheck

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

end