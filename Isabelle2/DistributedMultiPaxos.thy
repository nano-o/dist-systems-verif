theory DistributedMultiPaxos
imports Main  "~~/src/HOL/Library/Monad_Syntax" "~~/src/HOL/Library/Code_Target_Numeral"
  "~~/src/HOL/Library/FinFun_Syntax" "~~/src/HOL/Library/FSet" LinorderOption
begin

type_synonym acc = nat
type_synonym bal = nat
type_synonym inst = nat

datatype 'v msgs = 
  Msg1a (ballot:bal)|
  Msg1b (acceptor:acc) (insts:inst) (ballot:bal) (last_vs:"bal \<times> 'v option")|
  Msg2a (insts:inst) (ballot:bal) (comm:"'v")

record 'v acc_state =
  ballot :: "bal"
  vote :: "inst \<Rightarrow>f bal \<Rightarrow>f 'v option"

record 'v mp_state = 
  acc_bal :: "acc \<Rightarrow>f 'v acc_state"
  network :: "'v msgs set"
  propCmds :: "'v option set"

definition init_acc_state :: "'v acc_state" where
  "init_acc_state \<equiv> \<lparr>ballot = 0, vote = K$ K$ None\<rparr>" 

primrec init_acc::"nat \<Rightarrow> (acc \<Rightarrow>f 'v acc_state)"  where
  "init_acc 0 = (K$ init_acc_state)"
  |"init_acc (Suc n) = (init_acc n)(n $:= init_acc_state)"

definition init where
  "init nas \<equiv> \<lparr>acc_bal = init_acc nas, network = {}, propCmds = {}\<rparr>"

definition propose where
  "propose c state \<equiv> state\<lparr>propCmds := propCmds state \<union> {c}\<rparr>"

definition phase1a where
  "phase1a b state \<equiv> state\<lparr>network := network state \<union> {Msg1a b}\<rparr>"

definition vote_cmd::"acc \<Rightarrow> bal \<Rightarrow> inst \<Rightarrow> 'v \<Rightarrow> 'v mp_state \<Rightarrow> 'v mp_state" where
  "vote_cmd avt bvt ivt cmdv state \<equiv> (let 
    a_state = ((acc_bal state) $ avt) in
    if (ballot a_state = bvt) then
      (let ns = network state; 
        m2amsgs = Set.filter (\<lambda>nm. case nm of (Msg2a i b _) \<Rightarrow> (ivt = i \<and> bvt = b)| _ \<Rightarrow> False) ns; 
        m2anum = card m2amsgs in
      if (m2anum > 0) then
      (
        let m2acmd = image (\<lambda>nm. case nm of (Msg2a i b cv) \<Rightarrow> cv) m2amsgs in
        if (cmdv \<in> m2acmd) then
          (let a_state1 = a_state\<lparr>vote := (vote a_state)(ivt $:= ((vote a_state $ ivt)(bvt $:= Some cmdv)))\<rparr> in
          state\<lparr>acc_bal := (acc_bal state)(avt $:= a_state1)\<rparr>)
        else state)
      else state)
    else state)"

definition maxAcceptorVote::"inst \<Rightarrow> (bal list) \<Rightarrow> 'v acc_state \<Rightarrow> (bal \<times> 'v option)" where
  "maxAcceptorVote i bals a_state \<equiv> 
    let bals_flt = (filter (\<lambda>b. (((vote a_state) $ i) $ b) \<noteq> None) bals) @ [0];
      maxBal = (fold max bals_flt (bals_flt!0));
      v = (if maxBal > 0 then (((vote a_state) $ i) $ maxBal) else None) in
    (maxBal, v)"

definition phase1b where
  "phase1b a b bals inss state \<equiv> (let a_state = (acc_bal state)$a; ns = network state in
    if (ballot a_state < b \<and> (Msg1a b) \<in> ns) then
      let a_state1 = a_state\<lparr>ballot := b\<rparr>;
      messages = map (\<lambda>i. Msg1b a i b (maxAcceptorVote i bals a_state1)) inss in
      state\<lparr>acc_bal := (acc_bal state)(a $:= a_state1), network := ns \<union> set messages\<rparr>
    else state)"

definition safe_at where
  "safe_at m1bmsgs quonum \<equiv> (let 
    m1bnum = card m1bmsgs in
    if (m1bnum \<ge> quonum) then True
    else False)"

definition safeVote::"'v msgs set \<Rightarrow> 'v mp_state \<Rightarrow> 'v option set" where
  "safeVote m1bmsgs state \<equiv> let 
      m1bpair = image (\<lambda>nm. case nm of (Msg1b _ _ _ vs) \<Rightarrow> vs) m1bmsgs;
      m1bBal = image (\<lambda>x. fst x) m1bpair;
      maxBal = the_elem (Set.bind (Set.filter (\<lambda>le. \<forall>x \<in> m1bBal. x \<le> le) m1bBal) (\<lambda>x. {x}));
      maxVal = image (\<lambda>x. snd x) (Set.filter (\<lambda>le. fst le = maxBal) m1bpair);
      safeVal = Set.remove None maxVal in
   if (safeVal \<noteq> {}) then safeVal else propCmds state"

definition phase2a where
  "phase2a b2a i2a quonum v state \<equiv> (let ns = network state; 
    m2amsgs = Set.filter (\<lambda>nm. case nm of Msg2a i b _ \<Rightarrow> (b2a = b \<and> i2a = i)| _ \<Rightarrow> False) ns; 
    m2anum = card m2amsgs in
  if (m2anum = 0) then
    (let m1bmsgs = Set.filter (\<lambda>nm. case nm of Msg1b _ i b _ \<Rightarrow> (b2a = b \<and> i2a = i)| _ \<Rightarrow> False) ns in
      if (safe_at m1bmsgs quonum) then
        (let safeVal = safeVote m1bmsgs state in
        if (Some v \<in> safeVal) then 
          state\<lparr>network := (network state) \<union> {Msg2a i2a b2a v}\<rparr>
        else state)
      else state)
  else state)"

definition safe_inv::"acc set \<Rightarrow>'v mp_state \<Rightarrow> inst \<Rightarrow> nat \<Rightarrow> bool" where
  "safe_inv accs s i nas \<equiv> (let acc_state = acc_bal s in
    \<forall>acc\<^sub>1 \<in> accs. \<forall>acc\<^sub>2 \<in> accs. acc\<^sub>1 \<noteq> acc\<^sub>2 \<longrightarrow>
    (let acc_state1 = (acc_state $ acc\<^sub>1); acc_state2 = (acc_state $ acc\<^sub>1);
      bal1 = (ballot acc_state1); bal2 = (ballot acc_state2) in
      case ((vote acc_state1) $ i $ bal1) of None \<Rightarrow> True |
      Some cm \<Rightarrow> (
        case ((vote acc_state2) $ i $ bal2) of None \<Rightarrow> True |
          Some cs \<Rightarrow> (cm = cs))))"

text {* We need to rename a few modules to let the Scala compiler resolve circular dependencies. *}
code_identifier
  code_module Code_Numeral \<rightharpoonup> (Scala) MicroCheckerLib
| code_module Groups \<rightharpoonup> (Scala) MicroCheckerLib
| code_module Rings \<rightharpoonup> (Scala) MicroCheckerLib
| code_module Optiona \<rightharpoonup> (Scala) MicroCheckerLib
| code_module List \<rightharpoonup> (Scala) MicroCheckerLib
| code_module FinFun \<rightharpoonup> (Scala) MicroCheckerLib
| code_module FSet \<rightharpoonup> (Scala) MicroCheckerLib
| code_module Cardinality \<rightharpoonup> (Scala) MicroCheckerLib
| code_module Fun \<rightharpoonup> (Scala) MicroCheckerLib
| code_module HOL \<rightharpoonup> (Scala) MicroCheckerLib
| code_module Product_Type \<rightharpoonup> (Scala) MicroCheckerLib
| code_module Phantom_Type \<rightharpoonup> (Scala) MicroCheckerLib
| code_module String \<rightharpoonup> (Scala) MicroCheckerLib
| code_module Orderings \<rightharpoonup> (Scala) MicroCheckerLib
| code_module Num \<rightharpoonup> (Scala) MicroCheckerLib
| code_module Finite_Set \<rightharpoonup> (Scala) MicroCheckerLib
| code_module Set \<rightharpoonup> (Scala) MicroCheckerLib
| code_module Nat \<rightharpoonup> (Scala) MicroCheckerLib
| code_module LinorderOption \<rightharpoonup> (Scala) MicroCheckerLib
| code_module Divides \<rightharpoonup> (Scala) MicroCheckerLib
| code_module Serialization  \<rightharpoonup> (Scala) MicroCheckerLib
| code_module Conditionally_Complete_Lattices \<rightharpoonup> (Scala) MicroCheckerLib
| code_module Complete_Lattices \<rightharpoonup> (Scala) MicroCheckerLib
| code_module Complete_Partial_Order \<rightharpoonup> (Scala) MicroCheckerLib
| code_module Lattices \<rightharpoonup> (Scala) MicroCheckerLib

export_code init propose phase1a maxAcceptorVote phase1b safe_at safeVote phase2a vote_cmd safe_inv
   in Scala file "DistributedMultiPaxos.scala"

end