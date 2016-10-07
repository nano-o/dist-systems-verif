theory Paxos_Sig
imports Main Utils IOA
begin

datatype ('a,'v) paxos_action =
  Propose 'v
  | Learn 'a inst "'v list"
    -- {* learn about a list of instances starting at the given instance. *}
  | Internal

definition paxos_asig where
"paxos_asig \<equiv>
  \<lparr> inputs = { Propose c | c . True},
    outputs = { Learn a i vs | a i vs . True},
    internals = {Internal} \<rparr>"

end