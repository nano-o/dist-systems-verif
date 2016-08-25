chapter {* Distributed and executable algorithm *}

theory AbstractMultiPaxosR3 
  imports Utils "~~/src/HOL/Library/FinFun" MaxByKey IOA Quorums
begin

unbundle finfun_syntax

type_synonym bal = nat
type_synonym inst = nat

section {* Local state and transitions *}

subsection {* Data structures *}

locale amp_r3 =
  fixes leader :: "bal \<Rightarrow> 'a::linorder"
  and next_bal :: "bal \<Rightarrow> 'a \<Rightarrow> bal"
  and as :: "'a set"
  and quorums :: "'a set set"
begin
  

datatype 'v inst_status =
  Decided 'v | Proposed 'v | Free
  -- {* An instance is in status @{term Free} locally when the acceptor has not itself proposed 
    or seen a decision in that instance, or seen a proposal. *}

end

record ('a, 'v) local_state =
  -- {* The local state of an acceptor. *}
  id :: 'a
  acceptors :: "'a set"
  ballot :: bal
  log :: "inst \<Rightarrow>f 'v amp_r3.inst_status"
    -- {* Last ballot in which the acceptor voted. *}
  votes :: "inst \<Rightarrow>f ('v \<times> bal) option"
  onebs :: "bal \<Rightarrow>f ('a \<Rightarrow>f inst \<Rightarrow>f ('v\<times>bal) option) option"
    -- {* The oneb messages received when the acceptor tries to acquire leadership. *}
  twobs :: "inst \<Rightarrow>f bal \<Rightarrow>f 'a set"
    -- {* the twob messages received (they are broadcast). *}

context amp_r3
begin

datatype ('aa,'vv) msg =
  Phase1a bal
  | Phase1b bal "inst \<Rightarrow>f ('vv \<times> bal) option"
  | Phase2a inst bal 'vv
  | Phase2b 'aa inst bal 'vv
  (* | Decision inst 'v *)
  | Fwd 'vv

datatype ('aa,'vv) packet =
  Packet 'aa  "('aa,'vv) msg"

definition local_start where "local_start a \<equiv>
  \<lparr>id = a, acceptors = as, ballot = 0, log = K$ Free,
    votes = K$ None, onebs = K$ None, twobs = K$ K$ {}\<rparr>"

subsection {* The propose action *} 

fun last_contiguous :: "nat list \<Rightarrow> nat" where 
  "last_contiguous [x] = x"
| "last_contiguous (x#y#xs) = (if y = Suc x then last_contiguous (y#xs) else x)"

definition send_all where
  "send_all s m \<equiv> (\<lambda> a . Packet a m) ` (acceptors s - {id s})"

definition next_inst where "next_inst s \<equiv>
  last_contiguous (finfun_to_list (log s))"
  -- {* TODO: optimize using a definition with finfun_rec. *}
  
definition do_2a where "do_2a s v \<equiv>
  let
    i = next_inst s;
    b = ballot s;
    s' = s\<lparr>log := (log s)(i $:= Proposed v),
      twobs := (twobs s)(i $:= (twobs s $ i)(b $:= {id s}))\<rparr>;
    msgs = send_all s (Phase2a i b v)
  in (s', msgs)"
  
definition propose where "propose s v \<equiv> 
  let l = leader (ballot s) in
    if l = id s 
    then do_2a s v
    else (s, {Packet l (Fwd v)})"
  -- {* TODO: Here we loose the proposal if it happens during an unsuccessful
  leadership acquisition attempt. *}

subsection {* The @{text receive_fwd} action *}

definition receive_fwd where "receive_fwd s v \<equiv>
  let l = leader (ballot s) in
    if l = id s
    then do_2a s v
    else (s, {Packet l (Fwd v)})"
  -- {* TODO: Here we loose the proposal if it happens during an unsuccessful
  leadership acquisition attempt. *}
  
end

subsection {* The @{text try_acquire_leadership} action *}

locale update_onebs =
  fixes onebs :: "bal \<Rightarrow>f ('a \<Rightarrow>f inst \<Rightarrow>f ('v\<times>bal) option) option"
  and votes :: "inst \<Rightarrow>f ('v \<times> bal) option"
  and  b :: bal and a :: 'a
begin 
  abbreviation(input) at_b where "at_b \<equiv> onebs $ b"
  abbreviation(input) from_none where "from_none \<equiv> (K$ K$ None)(a $:= votes)"
  abbreviation(input) from_existing where "from_existing \<equiv> \<lambda> ff . ff(a $:= votes)"
  definition new_onebs where "new_onebs \<equiv>
    case at_b of None \<Rightarrow> onebs(b $:= Some from_none)
    | Some ff \<Rightarrow> onebs(b $:= Some (from_existing ff))"
end

global_interpretation uonebs:update_onebs onebs votes b a for onebs votes b a 
  defines new_onebs = update_onebs.new_onebs .

context amp_r3 begin

definition try_acquire_leadership where "try_acquire_leadership s \<equiv>
  let
    b = next_bal (ballot s) (id s);
    s' = s\<lparr>onebs := new_onebs (onebs s) (votes s) b (id s), ballot := b\<rparr>;
    msgs = send_all s (Phase1a b)
  in (s, msgs)"

subsection {* The @{text receive_1a} action *}

definition receive_1a where "receive_1a s b \<equiv> if b > ballot s then
      let 
        msgs = {Packet (leader b) (Phase1b b (votes s))};
        s' = s\<lparr>ballot := b\<rparr>
      in (s', msgs)
    else (s, {})"

end 

subsection {* The @{text receive_1b} action *}

locale receive_1b =
  fixes votes :: "'a \<Rightarrow>f inst \<Rightarrow>f ('v\<times>bal) option"
  fixes as :: "'a set"
  fixes log :: "inst \<Rightarrow>f 'v amp_r3.inst_status"
begin

definition per_inst where "per_inst \<equiv> op$ votes ` as"
definition votes_per_inst where "votes_per_inst \<equiv> \<lambda> s . Finite_Set.fold
  (\<lambda> ff1 ff2 . (\<lambda> (vo, vs) . option_as_set vo \<union> vs) o$ ($ ff1, ff2 $) ) (K$ {}) s"
lemma votes_per_inst_code[code]:
  "votes_per_inst (set (x#xs)) = 
    (\<lambda> (vo, vs) . option_as_set vo \<union> vs) o$ ($ x, votes_per_inst (set xs) $)"
proof -
  define f :: "'b \<Rightarrow>f 'c option \<Rightarrow> 'b \<Rightarrow>f 'c set \<Rightarrow> 'b \<Rightarrow>f 'c set"
    where "f \<equiv> \<lambda> ff1 ff2 . (\<lambda> (vo, vs) . option_as_set vo \<union> vs) o$ ($ ff1, ff2 $)"
  interpret folding_idem f "K$ {}" 
    apply (unfold_locales)
     apply (auto simp add:f_def option_as_set_def fun_eq_iff expand_finfun_eq split!:option.splits)
    done
  let ?fold_expr = "\<lambda> s . Finite_Set.fold f (K$ {}) s"
  from insert_idem[of "set xs" x] have "?fold_expr (set (x#xs)) = f x (?fold_expr (set xs))"
    by (simp add:votes_per_inst_def option_as_set_def eq_fold split!:option.splits)
  thus ?thesis by (auto simp add:votes_per_inst_def f_def)
qed
  
definition max_per_inst where "max_per_inst \<equiv> (flip max_by_key snd) o$ (votes_per_inst per_inst)"
  
definition new_log where "new_log \<equiv> (\<lambda> (is, m) .
    case is of amp_r3.Decided _ \<Rightarrow> is | _ \<Rightarrow> (
      if m = {} then amp_r3.Free else amp_r3.Proposed ((fst o the_elem) m)) )
  o$ ($ log, max_per_inst $)"
  
definition msgs where "msgs \<equiv> 
  let 
    is = finfun_to_list new_log;
    to_propose = map (\<lambda> i . (i, the_elem (max_per_inst $ i))) is;
    msg_list = map (\<lambda> (i,v,b) . (amp_r3.Phase2a i b v)) to_propose
  in set msg_list"

end

global_interpretation r1:receive_1b votes as log for votes as log
  defines new_log = "receive_1b.new_log"
    and msgs = "receive_1b.msgs"
  .

context amp_r3 begin

definition receive_1b where "receive_1b s b vs \<equiv>
  let s' = s\<lparr>onebs := new_onebs (onebs s) vs b (id s)\<rparr>
  in (if (set (finfun_to_list (the (onebs s' $ b))) = acceptors s) 
    then let
        s'' = s'\<lparr>log := new_log (the (onebs s $ b)) (acceptors s) (log s)\<rparr>;
        msgs = msgs (the (onebs s $ b)) (acceptors s) (log s)
      in (s'', Set.bind msgs (send_all s)) 
    else (s', {}))"

subsection {* The @{text receive_2a} action *}

abbreviation(input) decided where "decided s i \<equiv> 
  case (log s $ i) of Decided _ \<Rightarrow> True | _ \<Rightarrow> False"
  
definition receive_2a where "receive_2a s i b v \<equiv>
  if b \<ge> ballot s then
    let s' = s\<lparr>votes := (votes s)(i $:= Some (v, b)),
      twobs := (twobs s)(i $:= (twobs s $ i)(b $:= insert (id s) (twobs s $ i $ b))),
      ballot := b\<rparr>;
      msgs = send_all s (Phase2b (id s) i b v)
    in (s', msgs)
  else (s, {})"
  
subsection {* The @{text receive_1b} action *}

definition receive_2b where "receive_2b s i b a v \<equiv>
  if (~ decided s i)
  then let
      s' = s\<lparr>twobs := (twobs s)(i $:= (twobs s $ i)(b $:= insert a (twobs s $ i $ b)))\<rparr>
    in (
      if (twobs s' $ i $ b = (acceptors s))
      then let s'' = s'\<lparr>log := (log s)(i $:= Decided v)\<rparr>
        in (s'', {})
      else (s', {}) )
  else (s, {})"

subsection {* The @{text proces_msg} action *}

fun process_msg where
  "process_msg s (Phase1a b) = receive_1a s b"
  | "process_msg s (Phase2a i b v) = receive_2a s i b v"
  | "process_msg s (Phase2b a i b v) = receive_2b s i b a v"
  | "process_msg s (Phase1b b vs) = receive_1b s b vs"
  | "process_msg s (Fwd v) = receive_fwd s v"

end

subsection {* Global system IOA. *}

context amp_r3 begin

datatype 'v action =
  Propose 'v
| Learn nat 'v
| Internal

definition asig where
  "asig \<equiv>
    \<lparr> inputs = { Propose c | c . True},
      outputs = { Learn i v | i v . True},
      internals = {Internal}\<rparr>"

end 

record ('a,'v) global_state =
  local_states :: "'a \<Rightarrow> ('a, 'v)local_state"
  network :: "('a, 'v) amp_r3.packet set"

context amp_r3 begin

definition global_start where "global_start \<equiv>
  \<lparr>local_states = (\<lambda> a . local_start a), network = {}\<rparr>"

inductive_set trans_rel :: "(('a,'v) global_state \<times> 'v action \<times> ('a,'v) global_state) set" where
  "\<lbrakk>(Packet a m) \<in> network s; process_msg ((local_states s) a) m = (sa', ms); m = Phase2b a i b v;
    log ((local_states s) a) \<noteq> log sa'\<rbrakk>
    \<Longrightarrow> (s, Learn i v, 
      s\<lparr>local_states := (local_states s)(a := sa'), network := network s \<union> ms\<rparr>) \<in> trans_rel"
| "\<lbrakk>(Packet a m) \<in> network s; process_msg ((local_states s) a) m = (sa', ms)\<rbrakk>
    \<Longrightarrow> (s, Internal, 
      s\<lparr>local_states := (local_states s)(a := sa'), network := network s \<union> ms\<rparr>) \<in> trans_rel"
| "\<lbrakk>propose ((local_states s) a) v = (sa', ms)\<rbrakk>
    \<Longrightarrow> (s, Propose v, 
      s\<lparr>local_states := (local_states s)(a := sa'), network := network s \<union> ms\<rparr>) \<in> trans_rel"
| "\<lbrakk>try_acquire_leadership ((local_states s) a) = (sa', ms)\<rbrakk>
    \<Longrightarrow> (s, Propose v, 
      s\<lparr>local_states := (local_states s)(a := sa'), network := network s \<union> ms\<rparr>) \<in> trans_rel"

end

definition n :: nat where "n \<equiv> 3"
  -- {* The number of processes *}

definition accs where "accs \<equiv> {1..n}"
  -- {* The set of acceptors *}

definition leader where "leader (b::nat) \<equiv> (b mod n) + 1"
  
definition next_bal :: "nat \<Rightarrow> nat \<Rightarrow> nat" where "next_bal b a \<equiv> 
  (b div n + 1) * n + a"
  
global_interpretation cq:card_quorums accs
  defines qs = "cq.quorums" and nas = "cq.nas"
  apply (unfold_locales)
   apply (simp add: accs_def n_def)
  apply (simp add: accs_def)
  done

global_interpretation my_amp_r3:amp_r3 leader next_bal accs qs 
  defines start = my_amp_r3.global_start
    and trans = my_amp_r3.trans_rel
    and propose = my_amp_r3.propose
    and try_acquire_leadership = my_amp_r3.try_acquire_leadership
    and process_msg = my_amp_r3.process_msg
    and local_start = my_amp_r3.local_start
    and receive_fwd = my_amp_r3.receive_fwd
    and receive_1a = my_amp_r3.receive_1a
  .

definition ioa where
  "ioa \<equiv> \<lparr>ioa.asig = amp_r3.asig, ioa.start = {start}, ioa.trans = trans\<rparr>"

subsection {* Code generation *}

export_code local_start propose try_acquire_leadership process_msg in Scala

end