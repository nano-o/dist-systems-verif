theory AbstractMultiPaxosR4
imports Utils MaxByKey IOA Quorums Paxos_Sig
begin

datatype 'v inst_status =
  Decided 'v | Active | Free

record ('a, 'v) acc_r4 =
  -- {* The local state of an acceptor. *}
  id :: 'a
  acceptors :: "'a set"
  ballot :: bal
  log :: "inst \<Rightarrow> 'v inst_status"
    -- {* Last ballot in which the acceptor voted. *}
  votes :: "inst \<rightharpoonup> ('v \<times> bal)"
  onebs :: "bal \<Rightarrow> 'a \<rightharpoonup> inst \<rightharpoonup> ('v\<times>bal)"
    -- {* The oneb messages received when the acceptor tries to acquire leadership. *}
  twobs :: "inst \<Rightarrow> bal \<Rightarrow> 'a set"
    -- {* the twob messages received (they are broadcast). *}
  
datatype ('a,'v) msg_r4 =
  Phase1a bal
  | Phase1b 'a bal "inst \<rightharpoonup> ('v \<times> bal)"
  | Phase2a inst bal 'v
  | Phase2b 'a inst bal 'v
  | Fwd 'v
  
datatype ('a,'v) packet_r4 =
  Packet 'a  "('a,'v) msg_r4"

record ('a,'v) s_r4 =
  lstate :: "'a \<Rightarrow> ('a, 'v)acc_r4"
  network :: "('a, 'v) packet_r4 set"

locale amp_r4 =
  fixes leader :: "bal \<Rightarrow> 'a::linorder"
  and next_bal :: "bal \<Rightarrow> 'a \<Rightarrow> bal"
  and as :: "'a set"
  and quorums :: "'a set set"
begin

definition start where "start \<equiv> 
  \<lparr>lstate = \<lambda> a .
    \<lparr>id = a, acceptors = as, ballot = 0, log = \<lambda> i . Free,
      votes = \<lambda> i . None, onebs = \<lambda> b a . None, twobs = \<lambda> i b . {}\<rparr>,
   network = {}\<rparr>"

definition send_all where send_all_def:
  "send_all s m \<equiv> { Packet a m | a . a \<in> acceptors s \<and> a \<noteq> id s}"

section {* The actions *}

definition do_2a where "do_2a s s' msgs v \<equiv>
  \<exists> i . log s i = Free \<and> (let b = ballot s in
      s' = s\<lparr>log := (log s)(i := Active),
        twobs := (twobs s)(i := (twobs s i)(b := {id s}))\<rparr>
      \<and> msgs = send_all s (Phase2a i b v))"
  
definition propose where "propose s s' msgs v \<equiv>
  let l = leader (ballot s) in
    if l = id s
    then do_2a s s' msgs v
    else s' = s \<and> msgs = {Packet l (Fwd v)}"

definition receive_fwd where "receive_fwd s s' msgs v \<equiv>
  propose s s' msgs v"

definition try_acquire_leadership where "try_acquire_leadership s s' msgs \<equiv>
  let b = next_bal (ballot s) (id s) in 
    s' = s\<lparr>onebs := (onebs s)(b := (onebs s b)(id s := Some (votes s))), ballot := b\<rparr>
    \<and> msgs = send_all s (Phase1a b)"
  
definition receive_1a where "receive_1a s s' msgs b \<equiv> if b > ballot s 
  then s' = s\<lparr>ballot := b\<rparr> \<and> msgs = {Packet (leader b) (Phase1b (id s) b (votes s))}
  else s' = s \<and> msgs = {}"

 
definition receive_2a where "receive_2a s s' msgs i b v \<equiv> 
  if b \<ge> ballot s then 
    s' = s\<lparr>votes := (votes s)(i := Some (v, b)),
      twobs := (twobs s)(i := (twobs s i)(b := insert (id s) (twobs s i b))),
      ballot := b\<rparr>
    \<and> msgs = send_all s (Phase2b (id s) i b v)
  else s' = s \<and> msgs = {}"

abbreviation(input) decided where "decided s i \<equiv> 
  case (log s i) of Decided _ \<Rightarrow> True | _ \<Rightarrow> False"
  
definition receive_2b where "receive_2b s s' msgs i b a v \<equiv>
  ~ decided s i
  \<and> (let s1 = s\<lparr>twobs := (twobs s)(i := (twobs s i)(b := insert a (twobs s i b)))\<rparr> in
    True)
  (* if (~ decided s i) then 
    let s1 = s\<lparr>twobs := (twobs s)(i := (twobs s i)(b := insert a (twobs s i b)))\<rparr> in
      if \<exists> q \<in> quorums . twobs s i b = q then 
        \<exists> q \<in> quorums . twobs s i b = q
      else s' = s1 \<and> msgs = {}
  else s' = s \<and> msgs = {} *)"

subsection {* The 1b action. *}

definition new_log where "new_log s b q \<equiv>
  \<lambda> i . case log s i of Decided v \<Rightarrow> Decided v | _ \<Rightarrow>
    (let m = max_by_key {(v,b) . (\<exists> a \<in> q . (the (onebs s b a)) i = Some (v,b))} snd in
      if m = {} then Free else Active)"
  
definition msgs_after_1b where "msgs_after_1b s b q \<equiv>
  \<lambda> i . case log s i of Decided _ \<Rightarrow> {} | _ \<Rightarrow>
    (let m = max_by_key {(v,b) . (\<exists> a \<in> q . (the (onebs s b a)) i = Some (v,b))} snd in
      if m = {} then {} else {Phase2a i b v | v . v \<in> fst ` m})"

definition receive_1b where "receive_1b s s' msgs a b vs \<equiv> if b = ballot s then
  let s1 = s\<lparr>onebs := (onebs s)(b := (onebs s b)(a := Some vs))\<rparr> in
    (if \<exists> q \<in> quorums . \<forall> a \<in> q . onebs s b a \<noteq> None 
      then \<exists> q \<in> quorums . \<forall> a \<in> q . onebs s b a \<noteq> None 
        \<and> s' = s1\<lparr>log := new_log s b q\<rparr>
        \<and> msgs = \<Union> ((msgs_after_1b s b q) ` UNIV)
      else s' = s1 \<and> msgs = {})
  else s' = s \<and> msgs = {}"
  
end