theory MultiPaxos4
imports Main  "~~/src/HOL/Library/Monad_Syntax" "~~/src/HOL/Library/Code_Target_Numeral"
  LinorderOption "~~/src/HOL/Library/FinFun_Syntax" "~~/src/HOL/Library/FSet"
  "../../IO-Automata/IOA" Serialization
begin

text {* A version of MultiPaxos using FinFuns *}

text {* TODO: implement checkpointing *}

subsection {* Ordering on pairs *}

fun less_eq_pair where
  "less_eq_pair (x,y) (u,v) = (y \<le> v)"

fun less_pair where 
  "less_pair (x,y) (u,v) = (y < v)"

instantiation prod :: (type,order) preorder
begin

definition less_eq_def: "less_eq x y = less_eq_pair x y"
definition less_def: "less x y = less_pair x y"

instance
apply(intro_classes)
apply (auto simp add:less_eq_def less_def)
done

end

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
| Vote (inst: inst) (cmd: "'v cmd")
  -- {* Instructs a learner that a value has been decided. Not used for now... *}
| Fwd (val: 'v)
  -- {* Forwards a proposal to another proposer (the leader) *}

datatype 'v  packet =
  -- {* A message with sender/destination information *}
  Packet (sender: acc) (dst: acc) (msg: "'v msg")

value "{0, 1, 2} = {1, 0, 2}"

record 'v acc_state =
  id :: acc
  leader :: "bool"
    -- {* The set of all acceptors *}

  ballot :: "bal option"
  decided :: "inst \<Rightarrow>f 'v cmd option"
    -- {* the highest ballot in which an acceptor participated *}
  vote :: "inst \<Rightarrow>f 'v cmd option"
    -- {* The last vote cast by an acceptor, for each instance *}
  last_ballot :: "inst \<Rightarrow>f bal option"
    -- {* For an acceptor a, this is the ballot in which "vote a" was cast, for each instance *}
  onebs :: "bal \<Rightarrow>f inst \<Rightarrow>f (acc \<times> ('v cmd \<times> bal) option) set"
    -- {* For an acceptor a and a ballot b, lists of 1b-message descriptions, indexed by ballot then instance. *}
  twobs :: "inst \<Rightarrow>f bal \<Rightarrow>f acc set"
    -- {* For an acceptor a: lists describing the 2b messages, indexed by instance then ballot. *}

  next_inst :: "nat"
  last_decision :: "nat option"
  working_instances :: "inst \<Rightarrow>f nat" 
    -- {* 0: not started; 1: processing; 2: closed *}

  commit_buffer :: "inst \<Rightarrow>f 'v cmd option"
  last_committed :: "inst"
  
fun accs where
  "accs (0::nat) = []"
| "accs (Suc n) = append (accs n) [n]"

definition nr where
  -- {* The number of replicas *}
  "nr acceptors \<equiv> card acceptors"

text {* A few functions to export to Scala for use by the runtime. *}

definition get_ballot where "get_ballot s \<equiv> ballot s"

definition is_leader where "is_leader s \<equiv> leader s"

definition get_leader where 
  "get_leader s nas \<equiv> case ballot s of Some (b::nat) \<Rightarrow> Some (b mod nas) | _ \<Rightarrow> None"

definition get_next_instance where
  "get_next_instance s \<equiv> next_inst s"

definition init_acc_state :: "acc \<Rightarrow> 'v acc_state" where
  "init_acc_state a \<equiv> \<lparr>
    id = a,
    leader = False,

    ballot = None,
    decided = K$ None,
    vote = K$ None, 
    last_ballot = K$ None,
    onebs = K$ K$ {},
    twobs = K$ K$ {},

    next_inst = 1, (* instances start at 1 *)
    last_decision = None,
    working_instances =  K$ 0,

    commit_buffer =  K$ None,
    last_committed = 0
   \<rparr>" 

subsection {* Event handlers *}

text {* If we had finfun_Ex we could do this better.
  Here we use instance 0 by default, but that's arbitrary. *}
definition one_b_quorum_received where
  "one_b_quorum_received b s nas \<equiv> 
    let at_b_i = onebs s $ b $ 0
    in 2 * card at_b_i > nas"

fun getOwnedBallot where 
  "getOwnedBallot a (Suc b) N = (if ((Suc b) mod N = a) then (Suc b)
    else (getOwnedBallot a b N))"
| "getOwnedBallot a 0 N = 0"

definition suc_bal :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat"
  -- {* The smallest ballot belonging to replica a and greater than ballot b, when there are N replicas *}
  where "suc_bal a b N \<equiv> getOwnedBallot a (b + N) N"

fun nx_bal where
  "nx_bal a None N = suc_bal a 0 N"
| "nx_bal a (Some b) N = suc_bal a b N"

definition leader_of_bal where
  "leader_of_bal s b nas \<equiv> case b of None \<Rightarrow> 0 | Some b \<Rightarrow>
    (b mod nas)"

definition send_all where "send_all state acc ms acceptors \<equiv> image (\<lambda> a2 . Packet (id state) a2 ms)  (acceptors - {acc})"

definition do_2a where
  "do_2a s v acceptors \<equiv>
    let
      a = id s;
      inst = (next_inst s);
      b = the (ballot s);
      msg = Phase2a inst b v a;
      new_state = s\<lparr>next_inst := (inst+1),
        twobs := finfun_update_code (twobs s) inst ((K$ {})(b $:= {a})),
        working_instances := (working_instances s)(inst $:=1) (* Added by ian to track working instances *)
       \<rparr>
    in
      (new_state, send_all s a msg acceptors)"

definition propose :: "'v \<Rightarrow> 'v acc_state \<Rightarrow> nat \<Rightarrow> acc set \<Rightarrow> ('v acc_state \<times> 'v packet set)" where
  -- {* If leader, then go ahead with 2a, otherwise forward to the leader. *}
  "propose v s nas acceptors \<equiv> let a = id s; leader_bal = (leader_of_bal s (ballot s) nas) 
    in
    (if (leader_bal = a \<and> leader s)
      then do_2a s (Cmd v) acceptors
      else (if (leader_bal = a)
        then (s,{}) (* TODO: here we loose the proposal... *)
        else (s, {Packet a leader_bal (Fwd v)})))"
 
(* What if the target process is not the leader anymore? TODO: Then let's forward it again. *)
definition receive_fwd  :: "'v \<Rightarrow> 'v acc_state \<Rightarrow> nat \<Rightarrow> acc set \<Rightarrow> ('v acc_state \<times> 'v packet set)" where
  "receive_fwd v s nas acceptors \<equiv> let a = id s in 
    (if (leader_of_bal s (ballot s) nas = a \<and> leader s) then do_2a s (Cmd v) acceptors else (s, ({})))"

definition send_1a :: "'v acc_state \<Rightarrow> nat \<Rightarrow> acc set \<Rightarrow> ('v acc_state \<times> 'v packet set)" where
  -- {* a tries to become the leader *}
  "send_1a s nas acceptors \<equiv>
    (let
        a = id s;
        b = nx_bal a (ballot s) nas;
        msg_1a = Phase1a a b in
      (s\<lparr>ballot := Some b\<rparr>, image (\<lambda> a2 . Packet a a2 msg_1a) acceptors))"

definition receive_1a :: "acc \<Rightarrow> bal \<Rightarrow> 'v acc_state \<Rightarrow> ('v acc_state \<times> 'v packet set)" where
  "receive_1a l b s \<equiv>
    (let bal = ballot s; a = id s in
      (if (bal = None \<or> ((the bal) < b))
       then
          (let
            combiner = (\<lambda> (vo,bo) . vo \<bind> (\<lambda> v . bo \<bind> (\<lambda> b . Some (v,b))));
            x = ($ vote s, last_ballot s $);
            last_votes = combiner o$ x ;

            msg_1b = Phase1b last_votes b a;
            packet = Packet a l msg_1b;
            state = s\<lparr>ballot := Some b\<rparr>
          in
          (state, {packet}))
       else (s, {})))"

definition update_onebs :: 
  "'v acc_state \<Rightarrow> bal \<Rightarrow> acc \<Rightarrow> (inst \<Rightarrow>f ('v cmd \<times> bal) option) \<Rightarrow> 'v acc_state" where
  -- {* Update the list of highest voted values when receiving a 1b
    message from a2 for ballot bal containing last_vs *}
  "update_onebs s bal a2 last_vs \<equiv>
    let
      a = id s;
      combiner = \<lambda> (xs, y) . (if ((a2, y) \<in> xs) then xs else (insert (a2, y) xs));
      pair_map = ($ (onebs s $ bal), last_vs $);
      at_bal = combiner o$ pair_map
    in s\<lparr>onebs := (onebs s)(bal $:= at_bal)\<rparr>"

definition highest_voted :: "(nat \<Rightarrow>f (acc \<times> ('v cmd \<times> nat) option) set) \<Rightarrow> (nat \<Rightarrow> ('v cmd) option)" where
  -- {* Makes sense only if no list in the map is empty. *}
  "highest_voted onebs_bal \<equiv>
    let
        onebs_i = (\<lambda>i. image (\<lambda>s. snd s) (onebs_bal $ i));
        (*votes = (map snd) o$ m;*)
        (*highest = (\<lambda> l . if (l = []) then None else (fold max l (l!0)) \<bind> (\<lambda> vb . Some (fst vb)))*)
        highest = (\<lambda> l . if (l = {}) then None else (the_elem (Set.filter (\<lambda>le. \<forall>x \<in> l. x \<le> le) l)) \<bind> (\<lambda> vb . Some (fst vb)))
    in highest o onebs_i"

text {* Instead of trying to define the max as a recursive function, let's use finfun_to_list. *}
value "((K$ False)(5 $:= True)(4 $:= False)(2 $:= True)) $ (2::int)"
value "finfun_to_list (((K$ False)(5 $:= True)(4 $:= False)(2 $:= True))::(nat \<Rightarrow>f bool))"

text {* 
  When a quorum of 1b messages is received, we complete all started instances by sending 2b messages containing a safe value.
  If an instance has not been started but a higher instance has been started, we complete
  it by sending a no-op message.
  TODO: why do we need the no-ops? we could also reuse instances where everything is safe...
  It's because holes block the execution of higher commands while we have no new client commands to propose.
  But that's unlikely under high load...

  For now we propose values to all the instances ever started.
*}
definition receive_1b :: "(inst \<Rightarrow>f ('v cmd \<times> bal) option) \<Rightarrow> bal \<Rightarrow> acc \<Rightarrow> 'v acc_state \<Rightarrow> nat \<Rightarrow> acc set \<Rightarrow> ('v acc_state \<times> 'v packet set)" where
 "receive_1b last_vs bal a2 s nas acceptors \<equiv> (let a = id s in (
    if (Some bal = ballot s)
    then
      (let s1 = update_onebs s bal a2 last_vs
       in (if one_b_quorum_received bal s1 nas 
          then (let
              onebs_bal = onebs s1 $ bal;
              h = highest_voted onebs_bal;
              max_i = let l = (finfun_to_list onebs_bal) in (if l = [] then 0 else hd (rev l));
              s2 = s1\<lparr>leader := True\<rparr>;
              maxInst = (next_inst s2);
              (*Modified*)
              s3 = s2\<lparr>next_inst := (if max_i+1 < maxInst then maxInst else max_i+1)\<rparr>;
              twoa_is = [1..<max_i+1];
              (* TODO: the following might traverse all the finfun, which is a problem when there are many instances. *)
              s4 = fold (\<lambda> i s . s\<lparr>twobs := finfun_update_code (twobs s) i ((twobs s $ i)(bal $:= {a}))\<rparr>) twoa_is s3;
              msgs = map (\<lambda> i . case h i of 
                  None \<Rightarrow> Phase2a i bal NoOp a
                | Some v \<Rightarrow> Phase2a i bal v a) twoa_is;
              pckts = map (\<lambda> m . send_all s a m acceptors) msgs
            in (s4, fold (op \<union>) pckts {}) )
          else (s1, {}) ) )
    else (s, {})) )"

definition is_decided where "is_decided s i \<equiv> decided s $ i \<noteq> None"

definition new_twobs where "new_twobs a ori_twobs \<equiv> insert a ori_twobs"

definition update_twobs where "update_twobs s i b new \<equiv>
  s\<lparr>twobs := finfun_update_code (twobs s) i (twobs s $ i)(b $:= new)\<rparr>"

definition update_decided where 
  "update_decided s i v \<equiv> s\<lparr>
        decided := finfun_update_code (decided s) i (Some v), 
        last_decision := Some i,
        commit_buffer := (commit_buffer s)(i $:= Some v)
\<rparr>"

definition receive_2_addl  :: "inst \<Rightarrow> bal \<Rightarrow> 'v cmd \<Rightarrow> acc \<Rightarrow> 'v acc_state \<Rightarrow> nat \<Rightarrow> 'v acc_state" where
 "receive_2_addl i b v l s nas \<equiv>
    (let a = id s; ori_twobs = (twobs s $ i $ b) in
    if (l \<in> ori_twobs) then s 
     else (let s2 = update_twobs s i b (new_twobs l ori_twobs); votes = (card (twobs s2 $ i $ b))
     in (
          if (2 * votes \<le> nas) (* Build the quorum *)
          then (
            (s2)
          ) else ( 
              if ( ((nas div 2)+1) = votes) (* Decision Time *)
              then ( 
               (update_decided s2 i v)
              ) else ( 
                  if (nas = votes) (* Last Message *)
                  then ( 
                    let s3= s2\<lparr> working_instances := (working_instances s)(i $:= 2)\<rparr>
                    in (s3)
                  ) else (s2) (*extra messages -- but not the last one*)
              )
          )             
        ))
    )"     

definition receive_2_first  :: "inst \<Rightarrow> bal \<Rightarrow> 'v cmd \<Rightarrow> acc \<Rightarrow> 'v acc_state \<Rightarrow> nat \<Rightarrow> 'v acc_state" where
 "receive_2_first i b v l s nas \<equiv>
    (let a = id s; bal = (ballot s); s2 = s\<lparr>vote := finfun_update_code (vote s) i (Some v),
                    twobs := finfun_update_code (twobs s) i ((K$ {})((the bal) $:= {a,l})),
                    next_inst := i + 1,
                    working_instances := (working_instances s)(i $:= 1)\<rparr>
     in (
          if (3 < nas)
          then ( 
            (s2)
          ) else ( 
              if (3 = nas)
              then ( 
                (update_decided s2 i v)
              ) else ( (*nr = 2 *) (*Decided and not working as no more message to receive*)
                   let s3= s2\<lparr> working_instances := (working_instances s)(i $:= 2)\<rparr> (*This is still working as we have 1 more message to receive *)
                   in (update_decided s3 i v)
              )
          )             
        )
     )"


            
definition receive_2 :: "inst \<Rightarrow> bal \<Rightarrow> 'v cmd \<Rightarrow> acc \<Rightarrow> 'v acc_state \<Rightarrow> nat \<Rightarrow> 'v acc_state" where
  "receive_2 i b v l s nas \<equiv>
  (if ((working_instances s) $ i > 0) (* This is not the first message from the instance *)
        then (
          receive_2_addl i b v l s nas
      ) else (* This is the first message, treat like a propose *)
     (
          receive_2_first i b v l s nas
     ))"

definition receive_2a :: "inst \<Rightarrow> bal \<Rightarrow> 'v cmd \<Rightarrow> acc \<Rightarrow> 'v acc_state \<Rightarrow> nat \<Rightarrow> acc set \<Rightarrow> ('v acc_state \<times> 'v packet set)" where
  "receive_2a i b v l s nas acceptors \<equiv> (receive_2 i b v l s nas, send_all s (id s) (Phase2b i b (id s) v) acceptors)"

definition receive_2b :: "inst \<Rightarrow> bal \<Rightarrow> acc \<Rightarrow> 'v cmd  \<Rightarrow> 'v acc_state \<Rightarrow> nat \<Rightarrow> ('v acc_state \<times> 'v packet set)" where
  "receive_2b i b a2 v s nas \<equiv> (receive_2 i b v a2 s nas, {})"

definition get_last_decision where 
  "get_last_decision s \<equiv> the (decided s $ (the (last_decision s)))"

value "largestprefix [(1,v1), (2,v2), (4,v4)]"

text {* output transition could return an option *}
definition learn :: "inst \<Rightarrow> 'v  \<Rightarrow> 'v acc_state \<Rightarrow> ('v acc_state \<times> 'v packet set) option" where 
  "learn i v s \<equiv> 
    case (decided s $ i) of None \<Rightarrow> None |
      Some cm \<Rightarrow> (case cm of NoOp \<Rightarrow> None 
        | Cmd c \<Rightarrow> (if v = c then Some (s, {}) else None))"

text {* Serializing finfuns to lists *}

text {* Finfun Filter for snapshots  *}
definition finfun_filter :: "'a::linorder \<Rightarrow>f 'b \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow>f 'b" where
  "finfun_filter ff d truncloc\<equiv> fold (\<lambda> k l . if (k \<le> truncloc) then (l) else ((l)( k $:= (ff $ k)))) (finfun_to_list ff) (K$ d) "

value "let ff = ((K$ 0) :: int \<Rightarrow>f int)(1 $:= 42)(42 $:= 0)(43 $:= 1) in (finfun_filter_v1 ff 0 2) "

section {* The I/O-automata *}

record 'v mp_state = 
  node_states :: "nat \<Rightarrow>f 'v acc_state"
  network :: "'v packet set"

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

definition mp_acclist where "mp_acclist n \<equiv>  (accs n)"
definition mp_acceptors where "mp_acceptors n \<equiv> (set (mp_acclist n))"

definition mp_asig where
  "mp_asig \<equiv>
    \<lparr> inputs = { Propose a c | a c . a \<in> (mp_acceptors nas)},
      outputs = { Learn l i v | i v l . l \<in> (mp_acceptors nas)},
      internals = {Receive_fwd a1 a2 v | a1 a2 v . a1 \<in> (mp_acceptors nas) \<and> a2 \<in> (mp_acceptors nas)}
        \<union> {Send_1as a | a . a \<in> (mp_acceptors nas)}
        \<union> {Receive_1a_send_1b a1 a2 b | a1 a2 b . a1 \<in> (mp_acceptors nas) \<and> a2 \<in> (mp_acceptors nas)}
        \<union> {Receive_1b a1 a2 f b | a1 a2 f b . a1 \<in> (mp_acceptors nas) \<and> a2 \<in> (mp_acceptors nas)}
        \<union> {Receive_2a_send_2b a1 a2 i b c | a1 a2 i b c . a1 \<in> (mp_acceptors nas) \<and> a2 \<in> (mp_acceptors nas)}
        \<union> {Receive_2b a1 a2 i b c | a1 a2 i b c. a1 \<in> (mp_acceptors nas) \<and> a2 \<in> (mp_acceptors nas)}
        \<union> {Learn a i c | a i c . a \<in> (mp_acceptors nas)}\<rparr>"

fun init_nodes_state::"nat \<Rightarrow> nat \<Rightarrow>f 'a acc_state" where
  "init_nodes_state (0::nat) = (K$ init_acc_state 0)"
| "init_nodes_state (Suc i) = (init_nodes_state i)(i $:= init_acc_state (i))"

(*fun init_nodes_state where
  "init_nodes_state (0::nat) n = (K$ init_acc_state n 0)"
| "init_nodes_state (Suc i) n = 
    (if Suc i > n then undefined else (init_nodes_state i n)(Suc i $:= init_acc_state n (Suc i)))"*)

lemma init_acc: 
assumes "a \<ge> 0"
shows "(init_nodes_state (Suc a)) $ a = init_acc_state a" using assms
by (induct a rule:init_nodes_state.induct, auto)

definition mp_start where
  "mp_start \<equiv> \<lparr>node_states = (init_nodes_state nas), network = {}\<rparr>"

definition update_state where 
  "update_state a a_s packets s \<equiv>
    s\<lparr>node_states := (node_states s)(a $:= a_s),
      network := network s \<union> packets\<rparr>"

fun mp_transit where
  "mp_transit s (Receive_fwd src dest v) = (if Packet src dest (Fwd v) \<in> network s 
    then (let (new_s, ps) = receive_fwd v (node_states s $ dest) nas (mp_acceptors nas) in 
      update_state dest new_s ps s)
    else s)"
|  "mp_transit s (Propose a (Cmd v)) = (let (new_s, ps) = propose v (node_states s $ a) nas (mp_acceptors nas) in
    update_state a new_s ps s)" 
| "mp_transit s (Receive_1a_send_1b src dest b) = (if (Packet src dest (Phase1a src b) \<in> network s) 
    then let (new_s, ps) = receive_1a src b (node_states s $ dest) in
      update_state dest new_s ps s 
    else s)"
| "mp_transit s (Send_1as l) = (let (new_s, ps) = send_1a (node_states s $ l) nas (mp_acceptors nas) in
    update_state l new_s ps s)"
| "mp_transit s (Receive_1b src l vs b) = (if (Packet src l (Phase1b vs b src) \<in> network s)
    then let (new_s, ps) = receive_1b vs b src (node_states s $ l) nas (mp_acceptors nas) in
      update_state l new_s ps s 
    else s)"
| "mp_transit s (Receive_2b a l i b cm) = (if (Packet a l (Phase2b i b a cm) \<in> network s)
    then let (new_s, ps) = receive_2b i b a cm (node_states s $ l) nas in
      update_state l new_s ps s 
    else s)"
| "mp_transit s (Receive_2a_send_2b l dest i b cm) = (if (Packet l dest (Phase2a i b cm l) \<in> network s)
    then (let (new_s, ps) = receive_2a i b cm l (node_states s $ dest) nas (mp_acceptors nas) in
        update_state dest new_s ps s)
    else s)"
| "mp_transit s (Learn a i (Cmd v)) = (case (learn i v (node_states s $ a)) of (Some st) \<Rightarrow> 
  (let (new_s, ps) = st in update_state a new_s ps s)| None \<Rightarrow> s)"

end

global_interpretation mp_ioa_3:mp_ioa "3"
defines mp_acceptors =  mp_ioa_3.mp_acclist and mp_start = mp_ioa_3.mp_start and mp_transit = mp_ioa_3.mp_transit
done

definition safe_at::"'v mp_state \<Rightarrow> inst \<Rightarrow> bool" where
  "safe_at s i \<equiv> (let acceptors = set (mp_acceptors 3) in
    \<forall>acc\<^sub>1 \<in> acceptors. \<forall>acc\<^sub>2 \<in> acceptors. acc\<^sub>1 \<noteq> acc\<^sub>2 \<longrightarrow>
    (case (decided ((node_states s) $ acc\<^sub>1) $ i) of None \<Rightarrow> True |
      Some cm \<Rightarrow> (
        case (decided ((node_states s) $ acc\<^sub>2) $ i) of None \<Rightarrow> True |
          Some cs \<Rightarrow> (cm = cs))))"

definition get_decided::"'v mp_state \<Rightarrow> acc \<Rightarrow> inst \<Rightarrow> 'v cmd option" where
  "get_decided s acc i \<equiv> (decided ((node_states s) $ acc) $ i)"

definition ballot_constraint where
  "ballot_constraint s bound \<equiv>
    let 
      n_s = node_states s;
      bals = (\<lambda> a_s . ballot a_s) o$ n_s;
      as = finfun_to_list bals;
      bal_list = map (\<lambda> a . bals $ a) as;
      bal_list_sorted = sort bal_list;
      max_bal = if bal_list_sorted = [] then None else bal_list_sorted ! (length bal_list_sorted - 1)
    in
    max_bal \<le> Some bound"

definition inst_constraint where
  "inst_constraint s bound \<equiv>
    let 
      n_s = node_states s;
      insts = (\<lambda> a_s . next_inst a_s) o$ n_s;
      as = finfun_to_list insts;
      inst_list = map (\<lambda> a . insts $ a) as;
      inst_list_sorted = sort inst_list;
      max_inst = if inst_list_sorted = [] then 1 else inst_list_sorted ! (length inst_list_sorted - 1)
    in
    max_inst \<le> bound"

subsection {* Code generation *}

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

export_code learn send_1a propose get_last_decision init_acc_state
  serialize_finfun deserialize_finfun get_ballot is_leader get_leader
mp_ioa_3.mp_start mp_ioa_3.mp_transit safe_at get_decided ballot_constraint inst_constraint
   in Scala file "MultiPaxos4.scala"

end