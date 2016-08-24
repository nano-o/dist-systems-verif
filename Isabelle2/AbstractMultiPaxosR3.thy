section {* Distributed and executable algorithm *}

theory AbstractMultiPaxosR3
imports Main "~~/src/HOL/Library/FinFun" "~~/src/HOL/Library/FSet" "~~/src/HOL/Library/Mapping"
begin

unbundle finfun_syntax

abbreviation(input) flip where "flip f \<equiv> \<lambda> x y . f y x"
type_synonym bal = nat
type_synonym inst = nat

subsection {* Local state and transitions *}

datatype 'v inst_status =
  Decided 'v | Proposed 'v | Free

record ('a, 'v) local_state =
  -- {* The local state of an acceptor. *}
  id :: 'a
  acceptors :: "'a set"
  ballot :: bal
  log :: "inst \<Rightarrow>f 'v inst_status"
  last_voted :: bal
    -- {* Last ballot in which the acceptor voted. *}
  votes :: "inst \<Rightarrow>f 'v option"
  onebs :: "bal \<Rightarrow>f (inst \<Rightarrow>f ('v\<times>bal) option) option"
    -- {* The oneb messages received when the acceptor tries to acquire leadership. *}
  twobs :: "inst \<Rightarrow>f bal \<Rightarrow>f 'a set"
    -- {* the twob messages received when the acceptor is a leader. *}

datatype ('a,'v) msg =
  Phase1a 'a bal
  | Phase1b 'a bal "inst \<Rightarrow>f ('v \<times> bal) option"
  | Phase2a 'a inst bal 'v
  | Phase2b 'a inst bal
  | Decision inst 'v
  | Fwd 'v

datatype ('a,'v) packet =
  Packet 'a 'a  "('a,'v) msg"

locale local_defs =
  fixes a::'a
  and as::"'a set"
  and leader ::"bal \<Rightarrow> 'a"
  and quorums :: "'a set set"
begin

definition local_start where "local_start \<equiv>
  \<lparr>id = a, acceptors = as, ballot = 0, log = K$ Free,
    last_voted = 0, votes = K$ None,
    onebs = K$ None, twobs = K$ K$ {}\<rparr>"

definition next_inst where "next_inst s \<equiv>
  finfun_to_list (log s)"
  
definition do_2a where "do_2a s v \<equiv> 
  let 
    inst = 0
  in True"
  
definition propose where "propose s v \<equiv> 
  if leader (ballot s) = id s 
  then (s, {Fwd v})
  else (s, {Fwd v})"
  
end

subsection {* Global system IOA. *}

record ('a,'v) global_state =
  local_states :: "'a \<Rightarrow> ('a, 'v)local_state"
  network :: "('a, 'v) packet set"

subsection {* Code generation *}

global_interpretation local_defs a as leader quorums for a as leader quorums 
  defines start = local_defs.local_start .

export_code start in Scala
  
end