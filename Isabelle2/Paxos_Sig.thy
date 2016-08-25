theory Paxos_Sig
imports Main Utils IOA
begin

datatype 'v paxos_action =
  Propose 'v
  | Learn inst 'v
  | Internal

definition paxos_asig where
"paxos_asig \<equiv>
  \<lparr> inputs = { Propose c | c . True},
    outputs = { Learn i v | i v . True},
    internals = {Internal} \<rparr>"

end