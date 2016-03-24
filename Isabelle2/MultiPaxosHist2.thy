theory MultiPaxosHist2
imports 
  MultiPaxos3
begin

text {* A version of MultiPaxos with history variables added. *}

text {* TODO: Prove that MultiPaxos refines it, preferably automatically *}

record 'v mph_state =
  mp_state :: "'v mp_state"
  vote_hist :: "inst \<Rightarrow>f acc \<Rightarrow>f bal \<Rightarrow>f 'v cmd option"

locale mph_ioa = mp_ioa 
begin

definition mph_start :: "'v mph_state" where
  "mph_start \<equiv> \<lparr>
    mp_state = mp_start,
    vote_hist = K$ K$ K$ None \<rparr>"

definition mph_trans where
  "mph_trans \<equiv> {(s,act,t) . 
    let 
      s1 = mp_state s;
      t1 = mp_state t;
      voted_a_i = (\<lambda> a i . 
        (let last_a_i = \<lambda> s . last_ballot (node_states s $ a) $ i in
          last_a_i s1 \<noteq> last_a_i t1))
    in
      (s1, act, t1) \<in> IOA.trans mp_ioa 
      \<and> (if (\<exists> a i . voted_a_i a i) 
        then 
          let p = SOME p . voted_a_i (fst p) (snd p);
              a = fst p;
              i = snd p
          in vote_hist t = (vote_hist s)(i $:= (vote_hist s $ i)
            (a $:= (vote_hist s $ i $ a)
              ((the ((last_ballot (node_states t1 $ a)) $ i)) $:= vote (node_states s1 $ a) $ i)))
        else vote_hist s = vote_hist t )}"

definition mph_ioa where 
  "mph_ioa \<equiv> \<lparr>ioa.asig = mp_asig, start = {mph_start}, trans = mph_trans\<rparr>"

end

end