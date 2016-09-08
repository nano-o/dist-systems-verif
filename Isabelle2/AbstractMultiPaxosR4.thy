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

definition to_all where to_all_def:
  "to_all s m \<equiv> { Packet a m | a . a \<in> acceptors s \<and> a \<noteq> id s}"

section {* The actions *}

definition do_2a where "do_2a s s' a v \<equiv>
  \<exists> i . let sa = lstate s a; b = ballot sa in 
    s' = s\<lparr>lstate := (lstate s)(a := sa\<lparr>log := (log sa)(i := Active),
        twobs := (twobs sa)(i := (twobs sa i)(b := {id sa}))\<rparr>),
    network := network s \<union> to_all sa (Phase2a i b v)\<rparr>"
  
definition propose where "propose s s' a v \<equiv>
  let sa = lstate s a; b = ballot sa; l = leader b in
    if l = a
    then do_2a s s' a v
    else s' = s\<lparr>network := network s \<union> {Packet l (Fwd v)}\<rparr>"

definition receive_fwd where "receive_fwd s s' \<equiv>
  \<exists> a v . \<exists> p \<in> network s . p = Packet a (Fwd v) \<and> propose s s' a v"

definition try_acquire_leadership where "try_acquire_leadership s s' a \<equiv>
  let sa = lstate s a; b = ballot sa; b = next_bal b a in 
    s' = s\<lparr>lstate := (lstate s)(a := sa\<lparr>onebs := (onebs sa)(b := (onebs sa b)(a := Some (votes sa))), ballot := b\<rparr>),
      network := network s \<union> to_all sa (Phase1a b)\<rparr>"
  
definition receive_1a where "receive_1a s s' \<equiv> \<exists> b a . \<exists> p \<in> network s . p = Packet a (Phase1a b) \<and> (
  let sa = lstate s a; ba = ballot sa in b > ba 
    \<and> s' = s\<lparr>lstate := (lstate s)(a := sa\<lparr>ballot := b\<rparr>), 
      network := {Packet (leader b) (Phase1b a b (votes sa))}\<rparr> )"
 
definition receive_2a where "receive_2a s s' \<equiv> \<exists> a i b v . \<exists> p \<in> network s .
  p = Packet a (Phase2a i b v) \<and> ( 
    let sa = lstate s a; ba = ballot sa in 
      b \<ge> ba
      \<and> s' = s\<lparr>lstate := (lstate s)(a := sa\<lparr>votes := (votes sa)(i := Some (v, b)),
          twobs := (twobs sa)(i := (twobs sa i)(b := insert a (twobs sa i b))),
          ballot := b\<rparr>),
        network := network s \<union> to_all sa (Phase2b a i b v)\<rparr> )"

abbreviation(input) decided where "decided s i \<equiv> 
  case (log s i) of Decided _ \<Rightarrow> True | _ \<Rightarrow> False"
  
definition receive_2b where "receive_2b s s' \<equiv> \<exists> a i b v . \<exists> p \<in> network s .
  p = Packet a (Phase2b a i b v) \<and> (
  let sa = lstate s a; ba = ballot sa in 
    ~ decided sa i \<and> ( 
    let s1 = sa\<lparr>twobs := (twobs sa)(i := (twobs sa i)(b := insert a (twobs sa i b)))\<rparr> in 
      (\<exists> q \<in> quorums . twobs s1 i b = q
        \<and> s' = s\<lparr>lstate := (lstate s)(a := s1\<lparr>log := (log sa)(i := Decided v)\<rparr>)\<rparr> )
      \<or> (s' = s\<lparr>lstate := (lstate s)(a := s1) \<rparr>) ) )"

subsection {* The 1b action. *}

definition new_log where "new_log s b q \<equiv>
  \<lambda> i . case log s i of Decided v \<Rightarrow> Decided v | _ \<Rightarrow>
    (let m = max_by_key {(v,b) . (\<exists> a \<in> q . (the (onebs s b a)) i = Some (v,b))} snd in
      if m = {} then Free else Active)"
  
definition msgs_after_1b where "msgs_after_1b s b q \<equiv>
  \<lambda> i . case log s i of Decided _ \<Rightarrow> {} | _ \<Rightarrow>
    (let m = max_by_key {(v,b) . (\<exists> a \<in> q . (the (onebs s b a)) i = Some (v,b))} snd in
      if m = {} then {} else {Phase2a i b v | v . v \<in> fst ` m})"

definition receive_1b where "receive_1b s s' \<equiv> \<exists> a b vs . \<exists> p \<in> network s .
  p = Packet a (Phase1b a b vs) \<and> (
  let sa = lstate s a; ba = ballot sa in
    b = ba \<and> (
    let s1 = sa\<lparr>onebs := (onebs sa)(b := (onebs sa b)(a := Some vs))\<rparr> in
      (\<exists> q \<in> quorums . \<forall> a \<in> q . onebs sa b a \<noteq> None 
        \<and> s' = s\<lparr>lstate := (lstate s)(a := s1\<lparr>log := new_log sa b q\<rparr>), 
          network := network s \<union> (Set.bind (Set.bind UNIV (msgs_after_1b sa b q)) (to_all sa))\<rparr> ) ) )"
  
end