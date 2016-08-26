theory DistributedMultiPaxos
imports Main  "~~/src/HOL/Library/Monad_Syntax" "~~/src/HOL/Library/Code_Target_Numeral"
  "~~/src/HOL/Library/FinFun_Syntax" "~~/src/HOL/Library/FSet" LinorderOption
  "../../IO-Automata/IOA" BallotArrays
begin

type_synonym acc = nat
type_synonym bal = nat
type_synonym inst = nat

datatype 'v msgs = 
  Msg1a (ballot:bal)|
  Msg1b (acceptor:acc) (insts:inst) (ballot:bal) (last_vs:"bal \<times> 'v option")|
  Msg2a (insts:inst) (ballot:bal) (comm:"'v")

record 'v state = 
  ballot :: "acc \<Rightarrow>f bal"
  vote :: "acc \<Rightarrow>f inst \<Rightarrow>f bal \<Rightarrow>f 'v option"
  network :: "'v msgs set"
  propCmds :: "'v option set"

definition init where
  "init \<equiv> \<lparr>ballot = K$ 0, vote = K$ K$ K$ None, network = {}, propCmds = {}\<rparr>"

definition propose where
  "propose c s \<equiv> s\<lparr>propCmds := propCmds s \<union> {c}\<rparr>"

definition phase1a where
  "phase1a b s \<equiv> s\<lparr>network := network s \<union> {Msg1a b}\<rparr>"

definition vote_cmd::"acc \<Rightarrow> bal \<Rightarrow> inst \<Rightarrow> 'v \<Rightarrow> 'v state \<Rightarrow> 'v state" where
  "vote_cmd a b i v s \<equiv> (
    if (ballot s $ a = b) then
      (let ns = network s; 
        m2amsgs = Set.filter (\<lambda>nm. case nm of (Msg2a i2a b2a _) \<Rightarrow> (i2a = i \<and> b2a = b)| _ \<Rightarrow> False) ns; 
        m2anum = card m2amsgs in
      if (m2anum > 0) then
      (
        let m2acmd = image (\<lambda>nm. case nm of (Msg2a i b cv) \<Rightarrow> cv) m2amsgs in
        if (v \<in> m2acmd) then
          (s\<lparr>vote := (vote s)(a $:= (vote s $ a)(i $:= ((vote s $ a $ i)(b $:= Some v))))\<rparr>)
        else s)
      else s)
    else s)"

definition maxAcceptorVote::"acc \<Rightarrow> inst \<Rightarrow> (bal list) \<Rightarrow> 'v state \<Rightarrow> (bal \<times> 'v option)" where
  "maxAcceptorVote a i bals s \<equiv> 
    let bals_flt = (filter (\<lambda>b. (((vote s) $ a $ i) $ b) \<noteq> None) bals) @ [0];
      maxBal = (fold max bals_flt (bals_flt!0));
      v = (if maxBal > 0 then (((vote s) $ a $ i) $ maxBal) else None) in
    (maxBal, v)"

definition phase1b where
  "phase1b a b bals inss s \<equiv> (let ns = network s in
    if (ballot s $ a < b \<and> (Msg1a b) \<in> ns) then
      let messages = map (\<lambda>i. Msg1b a i b (maxAcceptorVote a i bals s)) inss in
      s\<lparr>ballot := (ballot s)(a $:= b), network := ns \<union> set messages\<rparr>
    else s)"

definition safe_at where
  "safe_at m1bmsgs quonum \<equiv> (let 
    m1bnum = card m1bmsgs in
    if (m1bnum \<ge> quonum) then True
    else False)"

definition safeVote::"'v msgs set \<Rightarrow> 'v state \<Rightarrow> 'v option set" where
  "safeVote m1bmsgs s \<equiv> let 
      m1bpair = image (\<lambda>nm. case nm of (Msg1b _ _ _ vs) \<Rightarrow> vs) m1bmsgs;
      m1bBal = image (\<lambda>x. fst x) m1bpair;
      maxBal = the_elem (Set.bind (Set.filter (\<lambda>le. \<forall>x \<in> m1bBal. x \<le> le) m1bBal) (\<lambda>x. {x}));
      maxVal = image (\<lambda>x. snd x) (Set.filter (\<lambda>le. fst le = maxBal) m1bpair);
      safeVal = Set.remove None maxVal in
   if (safeVal \<noteq> {}) then safeVal else propCmds s"

definition phase2a where
  "phase2a i b quonum v s \<equiv> (let ns = network s; 
    m2amsgs = Set.filter (\<lambda>nm. case nm of Msg2a i2a b2a _ \<Rightarrow> (i2a = i \<and> b2a = b)| _ \<Rightarrow> False) ns; 
    m2anum = card m2amsgs in
  if (m2anum = 0) then
    (let m1bmsgs = Set.filter (\<lambda>nm. case nm of Msg1b _ i2a b2a _ \<Rightarrow> (i2a = i \<and> b2a = b)| _ \<Rightarrow> False) ns in
      if (safe_at m1bmsgs quonum) then
        (let safeVal = safeVote m1bmsgs s in
        if (Some v \<in> safeVal) then 
          s\<lparr>network := (network s) \<union> {Msg2a i b v}\<rparr>
        else s)
      else s)
  else s)"

definition safe_inv::"acc set \<Rightarrow>'v state \<Rightarrow> inst \<Rightarrow> nat \<Rightarrow> bool" where
  "safe_inv accs s i nas \<equiv> (
    \<forall>acc\<^sub>1 \<in> accs. \<forall>acc\<^sub>2 \<in> accs. acc\<^sub>1 \<noteq> acc\<^sub>2 \<longrightarrow>
    (let bal1 = (ballot s $ acc\<^sub>1); bal2 = (ballot s $ acc\<^sub>2) in
      case ((vote s) $ acc\<^sub>1 $ i $ bal1) of None \<Rightarrow> True |
      Some cm \<Rightarrow> (
        case ((vote s) $ acc\<^sub>2 $ i $ bal2) of None \<Rightarrow> True |
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