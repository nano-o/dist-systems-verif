theory ComposableGC
imports CStruct "/home/nano/Documents/IO-Automata/IOA"
begin

datatype ('a,'c,'l) cgc_action = 
  Propose 'c 
| Learn 'a 'l
| FromPrev 'a
| ToNext 'a

record ('a,'c,'l)cgc_state =
  propCmd :: "'c set"
  learned :: "'l \<Rightarrow> 'a set"
  fromPrev :: "'a set"
  toNext :: "'a set"

locale ComposableGC = CStruct + IOA 
begin

definition cgc_asig where
  "cgc_asig \<equiv> 
    \<lparr> inputs = { a . \<exists> c . a = Propose c  } \<union> { a . \<exists> s . a = FromPrev s },
      outputs = { a . \<exists> s p . a = Learn s p } \<union> { a . \<exists> s . a = ToNext s },
      internals = {} \<rparr>"

definition cgc_start where
  "cgc_start \<equiv> {\<lparr>propCmd = {}, learned = \<lambda> p . {}, fromPrev = {}, toNext = {} \<rparr>}"

definition propose  where
  "propose c r r' \<equiv> (r' = r\<lparr>propCmd := (propCmd r) \<union> {c}\<rparr>)"

definition fromPrev where
  "fromPrev s r r' \<equiv> (r' = r\<lparr>fromPrev := (cgc_state.fromPrev r) \<union> {s}\<rparr>)"

definition non_trivial where
  "non_trivial r \<equiv> { s . \<exists> s\<^sub>0 cs . s\<^sub>0 \<in> cgc_state.fromPrev r \<and> set cs \<subseteq> propCmd r \<and> s = s\<^sub>0 \<star> cs }"

(* TODO: for using \<Squnion>, we would need a lattice parameterized by an explicit carrier set. See HOL/Algebra/Lattice.thy maybe *)
(* TODO: what about the relation with fromPrev? Is \<in> non_trivial sufficient?*)
definition toNext where
  "toNext s r r' \<equiv>
    s \<in> non_trivial r
    \<and> (\<forall> l . \<forall> s' \<in> (learned r l) . s' \<preceq> s)
    \<and> (r' = r\<lparr>toNext := (cgc_state.toNext r) \<union> {s}\<rparr>)"

definition learn where
  "learn l s r r' \<equiv> s \<in> non_trivial r
    \<and> (\<forall> l . \<forall> s' \<in> learned r l . compat2 s' s)
    \<and> (\<forall> s' \<in> cgc_state.toNext r . s \<preceq> s')
    \<and> cgc_state.fromPrev r \<noteq> {}
    \<and> r' = r\<lparr>learned := (learned r)(l := learned r l \<union> {s})\<rparr>"

fun cgc_trans_fun  where
  "cgc_trans_fun r (Propose c) r' = propose c r r'"
| "cgc_trans_fun r (FromPrev s) r' = fromPrev s r r'"
| "cgc_trans_fun r (ToNext s) r' = toNext s r r'"
| "cgc_trans_fun r (Learn s l) r' = learn l s r r'"

definition cgc_trans where
  "cgc_trans \<equiv> { (r,a,r') . cgc_trans_fun r a r'}"

definition cgc_ioa where
  "cgc_ioa \<equiv> \<lparr>ioa.asig = cgc_asig, start = cgc_start, trans = cgc_trans\<rparr>"

end

end