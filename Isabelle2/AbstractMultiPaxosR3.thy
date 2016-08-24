theory AbstractMultiPaxosR3
imports Main "~~/src/HOL/Library/FinFun" "~~/src/HOL/Library/FSet"
begin

unbundle finfun_syntax

abbreviation(input) flip where "flip f \<equiv> \<lambda> x y . f y x"
type_synonym bal = nat
type_synonym inst = nat

record ('a, 'v) local_state =
  -- {* The local state of an acceptor. *}
  id :: 'a
  acceptors :: "'a set"
  ballot :: bal
  decisions :: "inst \<Rightarrow>f 'v option"
  leader :: bool
  last_voted :: bal
    -- {* Last ballot in which the acceptor voted. *}
  votes :: "inst \<Rightarrow>f 'v option"
  onebs :: "bal \<Rightarrow>f (inst \<Rightarrow>f ('v\<times>bal) option) option"
    -- {* The oneb messages received when the acceptor tries to acquire leadership. *}
  twobs :: "inst \<Rightarrow>f bal \<Rightarrow>f 'a fset"
    -- {* the twob messages received when the acceptor is a leader. *}
  next_inst :: inst
    -- {* The next instance to use for proposing a command. *}

datatype ('a,'v) msg =
  Phase1a 'a bal
  | Phase1b 'a bal "inst \<Rightarrow>f ('v \<times> bal) option"
  | Phase2a 'a inst bal 'v
  | Phase2b 'a inst bal
  | Decision inst 'v
  | Fwd 'v

datatype ('a,'v) packet =
  Packet 'a 'a  "('a,'v) msg"

record ('a,'v) global_state =
  local_states :: "'a \<Rightarrow> ('a, 'v)local_state"
  network :: "('a, 'v) packet set"

end