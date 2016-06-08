theory MultiPaxos4
imports "~~/src/HOL/Library/Monad_Syntax" "~~/src/HOL/Library/Code_Target_Numeral"
  LinorderOption  "../../IO-Automata/IOA" "FinFun_Supplemental" Pair_order
begin

section {* An executable version of MultiPaxos, using finite functions (FinFun.thy) *}

subsection {* Actions, messages, and state. *}

datatype 'v cmd = Cmd (the_val: 'v) | NoOp

type_synonym bal = nat
type_synonym inst = nat
type_synonym acc = nat

datatype 'v msg =
  Phase1a (from_leader: acc) (ballot:bal)
| Phase1b (last_votes:"inst \<Rightarrow>f ('v cmd \<times> bal) option") (new_ballot: bal) (acceptor:acc)
| Phase2a (inst: inst) (for_ballot:bal) (suggestion:"'v cmd") (leader: acc)
| Phase2b (inst: inst) (ballot:bal) (acceptor: acc) (cmd: "'v cmd")
| Fwd (val: 'v)
  -- {* Forwards a proposal to another proposer (the leader) *}

datatype 'v packet =
  -- {* A message with sender/destination information *}
  Packet (sender: acc) (dst: acc) (msg: "'v msg")

(*<*)
(* TODO: use that? *)
datatype 'v vote_info = voted "'v cmd" bal | not_voted
(*>*)

datatype 'v inst_status = not_started | pending "'v cmd" | decided (decision:"'v cmd")

text {* The local state of an acceptor. Contains the acceptors identifier @{text "acc_state.self"}) 
  and the set of all acceptors @{text "acc_state.acceptors"} *}
record 'v acc_state =
  self :: acc
  acceptors :: "acc fset"
    -- {* The set of all acceptors *}
  ballot :: "bal option"
    -- {* the highest ballot in which an acceptor participated *}
  vote :: "inst \<Rightarrow>f 'v cmd option"
    -- {* The last vote cast by an acceptor, for each instance *}
  last_ballot :: "inst \<Rightarrow>f bal option"
    -- {* For an acceptor a, this is the ballot in which "vote a" was cast, for each instance *}
  onebs :: "bal \<Rightarrow>f acc \<Rightarrow>f inst \<Rightarrow>f ('v cmd \<times> bal) option option"
    -- {* For a ballot b, an acceptor a, and an instance i,
      this is the 1b information received from a in ballot b about instance i. *}
  twobs :: "inst \<Rightarrow>f bal \<Rightarrow>f acc fset"
    -- {* fset describing the 2b messages received, indexed by instance and ballot. *}
  next_inst :: "inst"
    -- {* The next instane to use *}
  inst_status :: "inst \<Rightarrow>f 'v inst_status"
    -- {* Status of the given instance *}
  leader :: "bool"
    -- {* Does this acceptor believe itself to be the leader? *}

text {* Why do we need this? Can't we use Abs_fst {0..<n} directly? *}
fun accs where
  -- {* A function to build a set of acceptors of a given size. *}
  "accs (0::nat) = {||}"
| "accs (Suc n) = (accs n) |\<union>| {|n|}"

lemma "accs 3 = {|1,2,0|}" quickcheck oops

lemma accs_def_2:"accs n = Abs_fset {0..<n}"
proof (induct n)
  case 0 thus ?case
    by (simp add: bot_fset_def)
next
  case (Suc n) thus ?case by simp
    (metis atLeastLessThanSuc eq_onp_same_args finite_atLeastLessThan finsert.abs_eq le0)
qed

definition init_acc_state :: "nat \<Rightarrow> acc \<Rightarrow> 'v acc_state" where
  "init_acc_state n a \<equiv> \<lparr>
    self = a,
    acc_state.acceptors = accs n,
    ballot = None,
    vote = K$ None,
    last_ballot = K$ None,
    onebs = K$ K$ K$ None,
    twobs = K$ K$ {||},
    next_inst = 1, (* instances start at 1 *)
    inst_status = K$ not_started,
    leader = False\<rparr>"

definition nr where
  -- {* The number of replicas *}
  "nr s \<equiv> fcard (acceptors s)"

subsection {* Event handlers *}

definition leader_of_bal where
  "leader_of_bal s b \<equiv> case b of None \<Rightarrow> 0 | Some b \<Rightarrow>
    (b mod (nr s))"

definition suc_bal :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat"
  -- {* The smallest ballot belonging to replica a and greater than ballot b, when there are N replicas *}
  where "suc_bal a b N \<equiv> (b div N + 1) * N + a"

fun nx_bal where
  -- {* Function used by a replica to choose the next ballot to use when trying to become the leader. *}
  "nx_bal a None N = suc_bal a 0 N"
| "nx_bal a (Some b) N = suc_bal a b N"

definition send_all where 
  "send_all s a m \<equiv> fimage (\<lambda> a2 . Packet (self s) a2 m)  (acceptors s |-| {|a|})"

definition do_2a where
  "do_2a s v \<equiv>
    let
      a = self s;
      inst = (next_inst s);
      b = the (ballot s);
      msg = Phase2a inst b v a;
      new_state = s\<lparr>next_inst := (inst+1),
        inst_status := finfun_update_code (inst_status s) inst (pending v),
        twobs := finfun_update_code (twobs s) inst ((K$ {||})(b $:= {|a|}))\<rparr>
    in
      (new_state, send_all s a msg)"

definition propose :: "'v \<Rightarrow> 'v acc_state \<Rightarrow> ('v acc_state \<times> 'v packet fset)" where
  -- {* If leader, then go ahead with 2a, otherwise forward to the leader. *}
  "propose v s \<equiv> let a = self s in
    (if (leader_of_bal s (ballot s) = a \<and> leader s)
      then do_2a s (Cmd v)
      else ( if (leader_of_bal s (ballot s) = a)
        then (s,{||}) (* TODO: here we loose the proposal... *)
        else (s, {|Packet a (leader_of_bal s (ballot s)) (Fwd v)|})) )"
 
(* What if the target process is not the leader anymore? TODO: Then let's forward it again. *)
definition receive_fwd  :: "'v \<Rightarrow> 'v acc_state \<Rightarrow> ('v acc_state \<times> 'v packet fset)" where
  "receive_fwd v s \<equiv> let a = self s in 
    (if (leader_of_bal s (ballot s) = a) then do_2a s (Cmd v) else (s, ({||})))"

definition last_votes where
  -- {* returns a finfun describing the last vote cast in each instance. *}
  "last_votes s \<equiv> let
    combiner = (\<lambda> (vo,bo) . vo \<bind> (\<lambda> v . bo \<bind> (\<lambda> b . Some (v,b))))
  in combiner o$ ($ vote s, last_ballot s $)"

definition send_1a :: "'v acc_state \<Rightarrow> ('v acc_state \<times> 'v packet fset)" where
  -- {* a tries to become the leader. *}
  "send_1a s \<equiv> let
      a = self s;
      b = nx_bal a (ballot s) (nr s);
      msg_1a = Phase1a a b;
      s = s\<lparr>ballot := Some b, 
        onebs := (onebs s)(b $:= (onebs s $ b)(a $:= (\<lambda> x . Some x) o$ last_votes s))\<rparr>
   in
     (s, send_all s a msg_1a)"

definition receive_1a :: "acc \<Rightarrow> bal \<Rightarrow> 'v acc_state \<Rightarrow> ('v acc_state \<times> 'v packet fset)" where
  "receive_1a l b s \<equiv>
    let bal = ballot s; a = self s in
      (if bal < Some b
       then
          (let
            msg_1b = Phase1b (last_votes s) b a;
            packet = Packet a l msg_1b;
            state = s\<lparr>ballot := Some b\<rparr>
          in
          (state, {|packet|}))
       else (s, {||}))"

definition update_onebs ::
  "'v acc_state \<Rightarrow> bal \<Rightarrow> acc \<Rightarrow> (inst \<Rightarrow>f ('v cmd \<times> bal) option) \<Rightarrow> 'v acc_state" where
  -- {* Update the map of highest voted values when receiving a 1b
    message from a2 for ballot bal containing @{term last_vs} *}
  "update_onebs s bal a2 last_vs \<equiv> let
      onebs_bal_a2 = (\<lambda> x . Some x) o$ last_vs
    in s\<lparr>onebs := (onebs s)(bal $:= (onebs s $ bal)(a2 $:= onebs_bal_a2))\<rparr>"

definition one_b_quorum_received where
  "one_b_quorum_received b s \<equiv> 
    let at_b = onebs s $ b
    in 2 * fcard (finfun_fset_dom at_b) > nr s"

text {* 
  When a quorum of 1b messages is received, we complete all started instances by sending 2b messages containing a safe value.
  If an instance has not been started but a higher instance has been started, we complete
  it by sending a no-op message.
  TODO: why do we need the no-ops? we could also reuse instances where everything is safe...
  It's because holes block the execution of higher commands while we have no new client commands to propose.
  But that's unlikely under high load...

  For now we propose values to all the instances ever started.
*}
definition receive_1b :: "(inst \<Rightarrow>f ('v cmd \<times> bal) option) \<Rightarrow> bal \<Rightarrow> acc \<Rightarrow>
    'v acc_state \<Rightarrow> ('v acc_state \<times> 'v packet fset)" where
 "receive_1b last_vs bal a2 s \<equiv> (let a = self s in (
    if (Some bal = ballot s \<and> \<not> leader s) (* if leadership has not been acquired in the current ballot *)
    then
      (let s2 = update_onebs s bal a2 last_vs
       in (if one_b_quorum_received bal s2
          then ( let 
              onebs_at_bal = onebs s $ bal; (* acc \<Rightarrow> inst \<Rightarrow> (vote \<times> bal) option *)
              inst_packets = (\<lambda> i . let
                  inst_votes = (\<lambda> ff . ff $ i \<bind> id) o$ onebs_at_bal; (* acc \<Rightarrow> (vote \<times> bal) option *)
                  to_linorder = \<lambda> x . x \<bind> Some o snd; (* We compare votes by ballot *)
                  inst_max_es = image_max_es to_linorder inst_votes; (* Invariant: is a singleton *)
                  msg = (\<lambda> vote . case (vote \<bind> Some o fst) of None \<Rightarrow> Phase2a i bal (NoOp::'v cmd) a
                    | Some v \<Rightarrow> Phase2a i bal v a)
                in fbind inst_max_es (\<lambda> vote . send_all s a (msg vote)));
              instances = ffUnion (finfun_fset_image ((\<lambda> ff . (finfun_fset_dom ff)) o$ onebs_at_bal));
              packets = fbind instances inst_packets;
              next_i = Max (fset instances);
              s3 = s2\<lparr>leader := True, next_inst := next_i\<rparr>
            in (s3, packets) )
          else (s2, {||}) ) )
    else (s, {||})) )"

definition receive_2a :: "inst \<Rightarrow> bal \<Rightarrow> 'v cmd \<Rightarrow> acc \<Rightarrow> 'v acc_state \<Rightarrow> ('v acc_state \<times> 'v packet fset)" where
  "receive_2a i b v l s =
    (let a = self s; bal = (ballot s) in
      (if (bal = Some b)
        then (s\<lparr>vote := finfun_update_code (vote s) i (Some v),
          twobs := finfun_update_code (twobs s) i ((K$ {||})(b $:= {|a|}))\<rparr>, 
          send_all s a (Phase2b i b a v))
        else (s, {||})))"

definition is_decided where 
  "is_decided s i \<equiv> case (inst_status s $ i) of decided _ \<Rightarrow> True | _ \<Rightarrow> False"

definition new_twobs where "new_twobs s i b a \<equiv> finsert a (twobs s $ i $ b)"

definition update_twobs where "update_twobs s i b new \<equiv> 
  s\<lparr>twobs := finfun_update_code (twobs s) i (twobs s $ i)(b $:= new)\<rparr>"

definition receive_2b :: "inst \<Rightarrow> bal \<Rightarrow> acc \<Rightarrow> 'v cmd  \<Rightarrow> 'v acc_state \<Rightarrow> ('v acc_state \<times> 'v packet fset)" where
  "receive_2b i b a2 v s \<equiv> let a = self s in 
    (if (\<not> is_decided s i)
      then
        (let 
            new_twobs = new_twobs s i b a2;
            s2 = update_twobs s i b new_twobs
        in
          (if (2 * fcard new_twobs > nr s)
            then let 
                s3 = s2\<lparr>inst_status := (inst_status s)(i $:= decided v)\<rparr> in
              (s3, {||})
            else (s2, {||}) ) )
      else
        (s, {||}) )"

text {* output transition could return an option *}
definition learn :: "inst \<Rightarrow> 'v  \<Rightarrow> 'v acc_state \<Rightarrow> ('v acc_state \<times> 'v packet fset) option" where 
  "learn i v s \<equiv>
    case (inst_status s $ i) of decided x \<Rightarrow> 
      (case x of NoOp \<Rightarrow> None 
      | Cmd c \<Rightarrow> (if v = c then Some (s, {||}) else None))
    | _ \<Rightarrow> None"

fun process_msg where
  "process_msg (Phase1a l b) s = receive_1a l b s"
| "process_msg (Phase1b lvs b a) s = receive_1b lvs b a s"
| "process_msg (Phase2a i b cm l) s = receive_2a i b cm l s"
| "process_msg (Phase2b i b a cm) s = receive_2b i b a cm s"
| "process_msg (Fwd v) s = receive_fwd v s"

text {* Serializing finfuns to lists *}

definition serialize_finfun where
  "serialize_finfun ff = fold (\<lambda> k l . (k, ff $ k)#l) (finfun_to_list ff) []"

definition deserialize_finfun where
  "deserialize_finfun l \<equiv> foldr (\<lambda> kv r . finfun_update_code r (fst kv) (snd kv)) l (K$ None)"

subsection {* Code generation *}

text {* We need to rename a few modules to let the Scala compiler resolve circular dependencies. *}
code_identifier
  code_module Code_Numeral \<rightharpoonup> (Scala) Nat
| code_module List \<rightharpoonup> (Scala) Set

export_code learn send_1a propose process_msg init_acc_state
  serialize_finfun deserialize_finfun in Scala file "simplePaxos.scala"

subsection {* The I/O-automata *}

record 'v mp_state = 
  node_states :: "nat \<Rightarrow>f 'v acc_state"
  network :: "'v packet fset"

datatype 'v mp_action =
  Receive_fwd acc acc 'v
| Propose acc "'v cmd"
| Send_1as acc
| Receive_1a_send_1b acc acc bal
| Receive_1b acc acc "inst \<Rightarrow>f ('v cmd \<times> bal) option" bal
| Receive_2a_send_2b acc acc inst bal "'v cmd"
| Receive_2b acc acc inst bal "'v cmd"
| Learn acc inst "'v cmd"

locale mp_ioa = IOA +
  fixes nas :: nat
    -- {* The number of acceptors *}
begin

definition mp_asig where
  "mp_asig \<equiv>
    \<lparr> inputs = { Propose a c | a c . a |\<in>| accs nas},
      outputs = { Learn l i v | i v l . l |\<in>| accs nas},
      internals = {Receive_fwd a1 a2 v | a1 a2 v . a1 |\<in>| accs nas \<and> a2 |\<in>| accs nas}
        \<union> {Send_1as a | a . a |\<in>| accs nas}
        \<union> {Receive_1a_send_1b a1 a2 b | a1 a2 b . a1 |\<in>| accs nas \<and> a2 |\<in>| accs nas}
        \<union> {Receive_1b a1 a2 f b | a1 a2 f b . a1 |\<in>| accs nas \<and> a2 |\<in>| accs nas}
        \<union> {Receive_2a_send_2b a1 a2 i b c | a1 a2 i b c . a1 |\<in>| accs nas \<and> a2 |\<in>| accs nas}
        \<union> {Receive_2b a1 a2 i b c | a1 a2 i b c. a1 |\<in>| accs nas \<and> a2 |\<in>| accs nas}
        \<union> {Learn a i c | a i c . a |\<in>| accs nas}\<rparr>"

(*<*)
fun init_nodes_state where
  "init_nodes_state (0::nat) n = undefined"
| "init_nodes_state (Suc i) n = 
    (if Suc i > n then undefined else (init_nodes_state i n)(Suc i $:= init_acc_state n (Suc i)))"
(*>*)

definition init_nodes_state_2_fun where 
  "init_nodes_state_2_fun \<equiv> \<lambda> a . if a |\<in>| accs nas then init_acc_state nas a else undefined"

definition init_nodes_state_2 where
  "init_nodes_state_2 \<equiv> Abs_finfun init_nodes_state_2_fun"

(*<*)
lemma init_nodes_state_2_is_finfun: "init_nodes_state_2_fun \<in> finfun"
apply(simp add:finfun_def init_nodes_state_2_fun_def)
apply (rule exI[where x="undefined"])
apply auto
subgoal proof -
show ?thesis (is "finite ?S")
  proof -
    have "?S \<subseteq> {a . a |\<in>| accs nas}" by blast
    moreover have "finite {a . a |\<in>| accs nas}"
    by (metis (full_types) Abs_fset_cases Abs_fset_inverse equalityI mem_Collect_eq notin_fset subsetI) 
    ultimately show ?thesis by auto
  qed
qed
done

lemma init_acc: 
assumes "a \<le> n" and "a > 0"
shows "(init_nodes_state a n) $ a = init_acc_state n a" using assms
by (induct a n arbitrary:n rule:init_nodes_state.induct, auto)
(*>*)

definition mp_start where
  "mp_start \<equiv> \<lparr>node_states = (init_nodes_state_2), network = {||}\<rparr>"

definition update_state where 
  "update_state a a_s packets s \<equiv>
    s\<lparr>node_states := (node_states s)(a $:= a_s),
      network := network s |\<union>| packets\<rparr>"

inductive mp_trans where
  "propose v (node_states s $ a) = (new_s, ps) \<Longrightarrow>
    mp_trans (s, Propose a (Cmd v), update_state a new_s ps s)"
| "\<lbrakk>receive_fwd v (node_states s $ dest) = (new_s, ps); 
    Packet src dest (Fwd v) |\<in>| network s\<rbrakk> \<Longrightarrow>
      mp_trans (s, Receive_fwd src dest v, update_state a new_s ps s)"
| "\<lbrakk>receive_1a l b (node_states s $ dest) = (new_s, ps);
    Packet src dest (Phase1a l b) |\<in>| network s; l = src\<rbrakk> \<Longrightarrow>
    mp_trans (s, Receive_1a_send_1b src dest b, update_state dest new_s ps s)"
| "send_1a (node_states s $ l) = (new_s, ps) \<Longrightarrow>
    mp_trans (s, Send_1as l, update_state l new_s ps s)"
| "\<lbrakk>receive_1b vs b l (node_states s $ l) = (new_s, ps); 
    Packet src l (Phase1b vs b a) |\<in>| network s; src = a\<rbrakk> \<Longrightarrow>
      mp_trans (s, Receive_1b src l vs b, update_state l new_s ps s)"
| "\<lbrakk>receive_2b i b l cm (node_states s $ l) = (new_s, ps);
    Packet src l (Phase2b i b a cm) |\<in>| network s; src = a\<rbrakk> \<Longrightarrow>
      mp_trans (s, Receive_2b a l i b cm, update_state l new_s ps s)"
| "\<lbrakk>receive_2a i b cm dest (node_states s $ dest) = (new_s, ps);
    Packet src dest (Phase2a i b cm l) |\<in>| network s; src = l\<rbrakk> \<Longrightarrow>
      mp_trans (s, Receive_2a_send_2b l dest i b cm, update_state dest new_s ps s)"
| "learn i v (node_states s $ a) = Some (new_s, ps) \<Longrightarrow>
    mp_trans (s, Learn a i (Cmd v), update_state a new_s ps s)"

definition mp_ioa where
  "mp_ioa \<equiv> \<lparr>ioa.asig = mp_asig, start = {mp_start}, trans = {(s,a,t) . mp_trans (s, a, t)}\<rparr>"

end

end