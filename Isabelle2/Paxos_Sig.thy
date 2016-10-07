theory Paxos_Sig
imports Main Utils IOA
begin

<<<<<<< HEAD
datatype 'v paxos_action =
  Propose 'v
  | Learn inst 'v
=======
datatype ('a,'v) paxos_action =
  Propose 'v
  | Learn 'a inst "'v list"
    -- {* learn about a list of instances starting at the given instance. *}
>>>>>>> giuliano_2
  | Internal

definition paxos_asig where
"paxos_asig \<equiv>
  \<lparr> inputs = { Propose c | c . True},
<<<<<<< HEAD
    outputs = { Learn i v | i v . True},
=======
    outputs = { Learn a i vs | a i vs . True},
>>>>>>> giuliano_2
    internals = {Internal} \<rparr>"

end