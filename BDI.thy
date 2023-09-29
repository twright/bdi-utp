theory BDI
  imports "Z_Machines.Z_Machine"
begin

enumtype Belief = "init" | not_at_goal | in_danger | stopped

enumtype Action = null | move | emergency_stop | remove_danger

enumtype BelMod = lrn | fgt

type_synonym 'b Update = "(BelMod \<times> 'b)"

(*
datatype 'b Update = lrn 'b | fgt 'b 

instantiation Update :: (default) default
begin

definition default_Update :: "'a Update" where 
"default_Update = lrn default"

instance ..

end
*)

(*
type_synonym Plan = "Belief Update list \<times> Action"
*)

type_synonym Plan = "Belief Update list \<times> Action"

enumtype Phase = p | s | e

fun upd :: "Belief set \<Rightarrow> Belief Update list \<Rightarrow> Belief set" where
"upd B ((lrn, b) # xs) = upd (B \<union> {b}) xs"|
"upd B ((fgt, b) # xs) = upd (B - {b}) xs"|
"upd B [] = B"

(*
fun upd :: "Belief \<Rightarrow> Belief Update \<Rightarrow> Belief" where
"upd B (lrn, b) = b" | "upd B (fgt, b) = (if b = B then init else B)"
*)

zstore BDI_st =
  beliefs :: "Belief set"
  pl :: "Plan"
  phase :: Phase
  trm :: "bool"

zoperation Terminate = 
  pre "phase = p"
  update "[trm \<leadsto> True]"

definition BeliefUpdates :: "Belief Update list set"
  where "BeliefUpdates = UNIV"

zoperation Perceive =
  params bm \<in> "BeliefUpdates"
  pre "phase = p"
  update "[phase \<leadsto> s, beliefs \<leadsto> upd beliefs bm]"

(*
fun plan :: "Belief \<Rightarrow> Plan" where
"plan init = ([], null)" |
"plan not_at_goal = ([], move)" |
"plan in_danger = ([lrn stopped], emergency_stop)" |
"plan stopped = ([fgt stopped], remove_danger)"
*)
(*
fun plan :: "Belief \<Rightarrow> Plan" where
"plan init = ((lrn, init), null)" |
"plan not_at_goal = ((lrn, init), move)" |
"plan in_danger = ((lrn, stopped), emergency_stop)" |
"plan stopped = ((fgt, stopped), remove_danger)"
*)
fun plan :: "Belief \<Rightarrow> Belief Update list \<times> Action" where
"plan init        = ([],            null)"|
"plan not_at_goal = ([],            move)"|
"plan in_danger   = ([(lrn, stopped)], emergency_stop)"|
"plan stopped     = ([(fgt, stopped)], remove_danger)"

zoperation Select =
  params pl' \<in> "{plan b | b . b \<in> beliefs}"
  pre "phase = s \<and> beliefs \<noteq> {}"
  update "[phase \<leadsto> e, pl \<leadsto> pl']"

zoperation NullSelect =
  pre "phase = s \<and> beliefs = {}"
  update "[phase \<leadsto> e]"

zoperation Execute =
  params p \<in> "{snd pl}"
  pre "phase = e"
  update "[beliefs \<leadsto> upd beliefs (fst pl), phase \<leadsto> p]"

zmachine BDI_Machine =
  over BDI_st
  init "[beliefs \<leadsto> {}, pl \<leadsto> ([], null), phase \<leadsto> p, trm \<leadsto> False]"
  operations Terminate Perceive Select NullSelect Execute
  until "trm"

animate BDI_Machine

lemma "deadlock_free BDI_Machine"
  apply deadlock_free
  apply (auto simp add: BeliefUpdates_def)
  apply (meson Phase.exhaust_disc)
  apply (metis surj_pair)
  apply (meson Phase.exhaust)+
  done

end