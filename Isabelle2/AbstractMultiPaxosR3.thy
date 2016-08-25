section {* Distributed and executable algorithm *}

theory AbstractMultiPaxosR3 
  imports Main "~~/src/HOL/Library/FinFun" MaxByKey
begin

unbundle finfun_syntax

abbreviation(input) flip where "flip f \<equiv> \<lambda> x y . f y x"
type_synonym bal = nat
type_synonym inst = nat

subsection {* Local state and transitions *}

datatype 'v inst_status =
  Decided 'v | Proposed 'v | Free
  -- {* An instance is in status @{term Free} locally when the acceptor has not itself proposed 
  or seen a decision in that instance; but, another acceptor might have proposed something. *}

record ('a, 'v) local_state =
  -- {* The local state of an acceptor. *}
  id :: 'a
  acceptors :: "'a set"
  ballot :: bal
  log :: "inst \<Rightarrow>f 'v inst_status"
    -- {* Last ballot in which the acceptor voted. *}
  votes :: "inst \<Rightarrow>f ('v \<times> bal) option"
  onebs :: "bal \<Rightarrow>f ('a \<Rightarrow>f inst \<Rightarrow>f ('v\<times>bal) option) option"
    -- {* The oneb messages received when the acceptor tries to acquire leadership. *}
  twobs :: "inst \<Rightarrow>f bal \<Rightarrow>f 'a set"
    -- {* the twob messages received (they are broadcast). *}

datatype ('a,'v) msg =
  Phase1a bal
  | Phase1b 'a bal "inst \<Rightarrow>f ('v \<times> bal) option"
  | Phase2a inst bal 'v
  | Phase2b 'a inst bal
  | Decision inst 'v
  | Fwd 'v

datatype ('a,'v) packet =
  Packet 'a  "('a,'v) msg"

definition send_all where
  "send_all s m \<equiv> (\<lambda> a . Packet a m) ` (acceptors s - {id s})"
  
locale local_defs =
  fixes leader :: "bal \<Rightarrow> 'a"
  and next_bal :: "bal \<Rightarrow> 'a \<Rightarrow> bal"
  and quorums :: "'a set set"
begin

definition local_start where "local_start a as \<equiv>
  \<lparr>id = a, acceptors = as, ballot = 0, log = K$ Free,
    votes = K$ None, onebs = K$ None, twobs = K$ K$ {}\<rparr>"
  
end

fun last_contiguous :: "nat list \<Rightarrow> nat" where 
  "last_contiguous [x] = x"
| "last_contiguous (x#y#xs) = (if y = Suc x then last_contiguous (y#xs) else x)"
  
context local_defs
begin

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

definition receive_fwd where "receive_fwd s v \<equiv>
  let l = leader (ballot s) in
    if l = id s
    then do_2a s v
    else (s, {Packet l (Fwd v)})"
  -- {* TODO: Here we loose the proposal if it happens during an unsuccessful
  leadership acquisition attempt. *}
  
end

notepad begin
  fix onebs :: "bal \<Rightarrow>f (inst \<Rightarrow>f 'a \<Rightarrow>f ('v\<times>bal) option) option"
  fix votes :: "inst \<Rightarrow>f ('v \<times> bal) option"
  fix b :: bal
  fix a :: 'a
  define at_b where "at_b \<equiv> onebs $ b"
  define from_none where "from_none \<equiv> (\<lambda> vo . (K$ None)(a $:= vo)) o$ votes"
  define from_existing where "from_existing \<equiv> (\<lambda> (ff,x) . ff(a $:= x)) o$ ($ the at_b, votes $)"
  define new_onebs where "new_onebs \<equiv> 
    case at_b of None \<Rightarrow> onebs(b $:= Some from_none)
    | Some ff \<Rightarrow> onebs(b $:= Some from_existing)"
end

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

context local_defs begin

definition try_acquire_leadership where "try_acquire_leadership s \<equiv>
  let
    b = next_bal (ballot s) (id s);
    s' = s\<lparr>onebs := new_onebs (onebs s) (votes s) b (id s), ballot := b\<rparr>;
    msgs = send_all s (Phase1a b)
  in (s, msgs)"

definition receive_1a where "receive_1a s b \<equiv> if b > ballot s then
      let 
        msgs = {Packet (leader b) (Phase1b (id s) b (votes s))};
        s' = s\<lparr>ballot := b\<rparr>
      in (s', msgs)
    else (s, {})"

end 

text {* An experiment. Would be executable, but then how to relate it to a high-level spec?
  I.e., how to transfer to normal functions? *}

definition option_as_set where "option_as_set x \<equiv> case x of None \<Rightarrow> {} | Some y \<Rightarrow> {y}"
  
locale receive_1b =
  fixes votes :: "'a \<Rightarrow>f inst \<Rightarrow>f ('v\<times>bal) option"
  fixes as :: "'a set"
  fixes log :: "inst \<Rightarrow>f 'v inst_status"
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
    case is of Decided _ \<Rightarrow> is | _ \<Rightarrow> (
      if m = {} then Free else Proposed ((fst o the_elem) m)) )
  o$ ($ log, max_per_inst $)"
  
definition msgs where "msgs \<equiv> 
  let 
    is = finfun_to_list new_log;
    to_propose = map (\<lambda> i . (i, the_elem (max_per_inst $ i))) is;
    msg_list = map (\<lambda> (i,v,b) . (Phase2a i b v)) to_propose
  in set msg_list"

end

global_interpretation r1:receive_1b votes as log for votes as log
  defines new_log = "receive_1b.new_log"
    and msgs = "receive_1b.msgs"
  .

context local_defs begin

definition receive_1b where "receive_1b s b vs \<equiv>
  let s' = s\<lparr>onebs := new_onebs (onebs s) vs b (id s)\<rparr>
  in (if (set (finfun_to_list (the (onebs s' $ b))) = acceptors s) 
    then let
        s' = s\<lparr>log := new_log (the (onebs s $ b)) (acceptors s) (log s)\<rparr>;
        msgs = msgs (the (onebs s $ b)) (acceptors s) (log s)
      in (s', (send_all s) ` msgs) 
    else (s', {}))"

  
end

subsection {* Global system IOA. *}

record ('a,'v) global_state =
  local_states :: "'a \<Rightarrow> ('a, 'v)local_state"
  network :: "('a, 'v) packet set"

subsection {* Code generation *}

global_interpretation ldefs:local_defs leader next_bal quorums for leader next_bal quorums 
  defines start = local_defs.local_start
    and do_2a = local_defs.do_2a
    and propose = local_defs.propose
    and receive_fwd = local_defs.receive_fwd
    and try_acquire_leadership = local_defs.try_acquire_leadership
    and receive_1a = local_defs.receive_1a
    and receive_1b = local_defs.receive_1b
  .

export_code start do_2a propose receive_fwd 
  try_acquire_leadership receive_1a receive_1b in Scala
  
end