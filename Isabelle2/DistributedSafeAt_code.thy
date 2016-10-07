section {* Just checking that code generation works *}

theory DistributedSafeAt_code
  imports DistributedSafeAt
begin

global_interpretation dsa:distributed_safe_at quorums ballot vote for quorums ballot vote 
  defines acc_max = dsa.acc_max and max_quorum_votes = dsa.max_quorum_votes .

term acc_max
thm acc_max_def

export_code acc_max in Scala

end