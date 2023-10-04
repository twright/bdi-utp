theory BDI_waypoints
  imports "Z_Machines.Z_Machine"
begin

type_synonym Name = string
(* for symplicity assume all values are nats *)
type_synonym Ctx = "string \<Rightarrow> nat"

datatype Action
  = move
  | await_decontamination
  | inspect
  | null

instantiation Action :: Haskell_Show.show
begin

fun show_Action :: "Action \<Rightarrow> string" where 
"show_Action move = ''move''"|
"show_Action await_decontamination = ''await_decontamination''"|
"show_Action inspect = ''inspect''"|
"show_Action null = ''null''"

instance ..

end

instantiation Action :: default
begin

definition default_Action :: "Action" where 
"default_Action = null"

instance ..

end

type_synonym ConcParamAction = "Action \<times> nat list"
type_synonym AbstParamAction = "Action \<times> Name list"

enumtype BelMod = lrn | fgt

enumtype BelSign = pos | neg

datatype Belief =
    goal_inspect
  | location_coordinate
  | danger_red
  | danger_orange
  | going
  | arrived
  | next_location
  | location
  | move_failure
type_synonym ParamBelief = "Belief \<times> nat list"

instantiation Belief :: Haskell_Show.show
begin

fun show_Belief :: "Belief \<Rightarrow> string" where 
"show_Belief goal_inspect = ''goal_inspect''"|
"show_Belief location_coordinate = ''location_coordinate''"|
"show_Belief danger_red = ''danger_red''"|
"show_Belief danger_orange = ''danger_orange''"|
"show_Belief going = ''going''"|
"show_Belief arrived = ''arrived''"|
"show_Belief next_location = ''next_location''"|
"show_Belief location = ''location''"|
"show_Belief move_failure = ''move_failure''"

instance ..

end

datatype Symbol = Var Name | Val nat
type_synonym BelPat = "nat list \<Rightarrow> Belief"

datatype AbstPat = 
    pat BelSign Belief "Name list"
    | patlist "AbstPat list"

instantiation AbstPat :: default
begin

definition default_AbstPat :: "AbstPat" where 
"default_AbstPat = patlist []"

instance ..

end

datatype ConcPat = 
    cpat BelSign Belief "nat list"
  | cpatlist "ConcPat list"

instantiation ConcPat :: default
begin

definition default_ConcPat :: "ConcPat" where 
"default_ConcPat = cpatlist []"

instance ..

end

fun instantiate_pat :: "Ctx \<Rightarrow> AbstPat \<Rightarrow> ConcPat" where
"instantiate_pat C (pat s b xs) = (cpat s b (map C xs))"|
"instantiate_pat C (patlist xs) = (cpatlist (map (instantiate_pat C) xs))"

fun free_vars :: "AbstPat \<Rightarrow> Name set" where
"free_vars (pat s b xs) = set xs"|
"free_vars (patlist xs) = foldl union {} (map free_vars xs)"

(*
inductive_set
  bel_patterns  :: "AbstPat \<Rightarrow> AbstPat set"
  for p :: "AbstPat"
  where
"b \<in> B \<Longrightarrow> cpat pos b xs \<in> bel_patterns B"|
"b \<notin> B \<Longrightarrow> cpat neg b xs \<in> bel_patterns B"|
"cpatlist [] \<in> bel_patterns B"|
"x \<in> bel_patterns B \<Longrightarrow> cpatlist xs \<in> bel_patterns B \<Longrightarrow> cpatlist (x # xs) \<in> bel_patterns B"
 *)

fun pat_extentions :: "AbstPat \<Rightarrow> AbstPat set" where
"pat_extentions (pat s p xs) = {patlist (ys + [pat s p xs] + zs) | ys zs . True}"|
"pat_extentions (patlist xs) = {patlist (ys + xs + zs) | ys zs . True}"

fun pat_instantiations :: "AbstPat \<Rightarrow> (Ctx \<times> ConcPat) set" where
"pat_instantiations p = {(C, instantiate_pat C p) | C . True}"

fun pos_beliefs :: "Belief set \<Rightarrow> (BelSign \<times> Belief) set" where
"pos_beliefs B = { (pos, b) | b . b \<in> B }"

fun neg_beliefs :: "Belief set \<Rightarrow> (BelSign \<times> Belief) set" where
"neg_beliefs B = { (neg, b) | b . b \<in> B }"

inductive_set
  bel_patterns  :: "ParamBelief set \<Rightarrow> ConcPat set"
  for B :: "ParamBelief set"
  where
"(b, xs) \<in> B \<Longrightarrow> cpat pos b xs \<in> bel_patterns B"|
"(b, xs) \<notin> B \<Longrightarrow> cpat neg b xs \<in> bel_patterns B"|
"cpatlist [] \<in> bel_patterns B"|
"x \<in> bel_patterns B \<Longrightarrow> cpatlist xs \<in> bel_patterns B \<Longrightarrow>
cpatlist (x # xs) \<in> bel_patterns B"

fun pat_matches :: "AbstPat \<Rightarrow> ParamBelief set \<Rightarrow> Ctx set" where
"pat_matches p B = { C | C pc . (C, pc) \<in> pat_instantiations p \<and> pc \<in> bel_patterns B }"

fun instantiate_act :: "Ctx \<Rightarrow> AbstParamAction \<Rightarrow> ConcParamAction" where
"instantiate_act C (act, xs) = (act, map C xs)"

type_synonym 'b Update = "(BelMod \<times> 'b)"

fun update_seq :: "ConcPat \<Rightarrow> ParamBelief Update list" where
"update_seq (cpat s b xs) = [((if s = pos then lrn else fgt), (b, xs))]"|
"update_seq (cpatlist []) = []"|
"update_seq (cpatlist (x # xs)) = (update_seq x) + (update_seq (cpatlist xs))"

type_synonym PlanAct = "(ParamBelief Update list \<times> ConcParamAction)"
(*
priority :: nat
pattern :: AbstPat
belief_update_pattern :: AbstPat
action_pattern :: AbstParamAction
*)
type_synonym Plan = "(nat \<times> AbstPat \<times> AbstPat \<times> AbstParamAction) set"

enumtype Phase = perceive | select | exec

fun upd :: "ParamBelief set \<Rightarrow> ParamBelief Update list \<Rightarrow> ParamBelief set" where
"upd B ((lrn, b) # xs) = upd (B \<union> {b}) xs"|
"upd B ((fgt, b) # xs) = upd (B - {b}) xs"|
"upd B [] = B"

zstore BDI_st =
  beliefs :: "ParamBelief set"
  pl :: "PlanAct"
  phase :: Phase
  trm :: "bool"

zoperation Terminate = 
  pre "phase = perceive"
  update "[trm \<leadsto> True]"

definition BeliefUpdates :: "ParamBelief Update list set"
  where "BeliefUpdates = UNIV"

term "upd {} [] :: ParamBelief set"

zoperation Perceive =
  params bm \<in> "BeliefUpdates"
  pre "phase = perceive"
  update "[phase \<leadsto> select, beliefs \<leadsto> upd beliefs bm]"

(*
goal_inspect(Location), location_coordinate(Location, X, Y), ~danger_red, ~danger_orange, ~going(door) -(1)> +going(Location), -goal_inspect(Location), do(move(X, Y))

arrived, going(door) -(2)> -going(door), do(await_decontamination)
arrived, going(OldLocation), next_location(OldLocation, NewLocation) -(1)> -going(OldLocation), +goal_inspect(NL), -arrived, do(inspect(OldLocation))
arrived, ~going(OldLocation) -(1)>  -arrived, do(null)
move_failure -(1)> do(null)

danger_red, ~going(door), location(door, X, Y) -(2)> +going(door), move(X, Y)
danger_orange, ~going(door), location(door, X, Y) -(2)> +going(door), move(X, Y) ﻿
 *)
definition plan :: Plan where
"plan = {
  (
    1,
    patlist [pat pos goal_inspect [''Location''],
             pat pos location_coordinate [''Location'', ''X'', ''Y''],
             pat neg danger_red [],
             pat neg danger_orange [],
             pat neg going [''door'']],
    patlist [pat pos going [''Location''],
             pat neg goal_inspect [''Location'']],
    (move, [''X'', ''Y''])
  ),
  (
    2,
    patlist [pat pos arrived [],
             pat pos going [''door'']],
    patlist [pat neg going [''door'']],
    (await_decontamination, [])
  ),
  (
    1,
    patlist [pat pos going [''OldLocation''],
             pat pos next_location [''OldLocation'', ''NewLocation'']],
    patlist [pat neg going [''OldLocation''],
             pat pos goal_inspect [''NL''],
             pat neg arrived []],
    (inspect, [])
  ),
  (
    1,
    patlist [pat pos arrived [],
             pat neg going [''OldLocation'']],
    patlist [pat neg arrived []],
    (null, [])
  ),
  (
    1,
    patlist [pat pos move_failure []],
    patlist [],
    (null, [])
  ),
  (
    2,
    patlist [pat pos danger_red [],
             pat neg going [''door''],
             pat pos location [''door'', ''X'', ''Y'']],
    patlist [pat pos going [''door'']],
    (move, [''X'', ''Y''])
  ),
  (
    2,
    patlist [pat pos danger_orange [],
             pat neg going [''door''],
             pat pos location [''door'', ''X'', ''Y'']],
    patlist [pat pos going [''door'']],
    (move, [''X'', ''Y''])
  )
}"

fun next_steps_pri :: "nat \<Rightarrow> Plan \<Rightarrow> ParamBelief set \<Rightarrow> PlanAct set" where
"next_steps_pri pri pla B = {
  (update_seq (instantiate_pat C r), instantiate_act C a)
  | p r a C . (pri, p, r, a) \<in> pla \<and> C \<in> pat_matches p B
}"

fun min_priority :: "Plan \<Rightarrow> ParamBelief set \<Rightarrow> nat option" where
"min_priority p B = (
  if \<exists>i . next_steps_pri i p B \<noteq> {}
  then Some (Least (\<lambda> n . next_steps_pri n p B \<noteq> {}))
  else None)"

lemma min_none_cond: "(min_priority p B = None) = (\<forall>i . next_steps_pri i p B = {})"
  by (auto split: option.splits)

definition null_plan_act :: PlanAct where
"null_plan_act = ([], (null, []))"

fun next_steps :: "Plan \<Rightarrow> ParamBelief set \<Rightarrow> PlanAct set" where
"next_steps p B = (case min_priority p B of
  Some n \<Rightarrow> next_steps_pri n p B |
  None   \<Rightarrow> {null_plan_act}
)"

lemma next_steps_nonempty: "next_steps p B \<noteq> {}"
proof (cases "min_priority p B")
  case None
  have "next_steps p B = {null_plan_act}"
    apply(simp only: next_steps.simps None)
    by simp
  then show ?thesis
    by blast
next
  case (Some n)
  have "Some n = Some (Least (\<lambda> n . next_steps_pri n p B \<noteq> {}))" (is "Some n = Some (Least ?f)")
    by (metis Some min_priority.elims option.distinct(1))
  hence "n = Least ?f"
    by blast
  hence "next_steps_pri n p B \<noteq> {}"
    by (metis (mono_tags, lifting) LeastI Some ifSomeE min_priority.elims)
  moreover have "next_steps p B = next_steps_pri n p B"
    apply(simp only: next_steps.simps Some)
    by simp
  ultimately show ?thesis
    by simp
qed

term "([], (null, [])) :: PlanAct"

term "next_steps plan {}"

zoperation Select =
  params pl' \<in> "next_steps plan beliefs"
  pre "phase = select \<and> beliefs \<noteq> {}"
  update "[phase \<leadsto> exec, pl \<leadsto> pl']"

zoperation NullSelect =
  pre "phase = select \<and> beliefs = {}"
  update "[phase \<leadsto> exec]"

zoperation Execute =
  params p \<in> "{snd pl}"
  pre "phase = exec"
  update "[beliefs \<leadsto> upd beliefs (fst pl), phase \<leadsto> perceive]"

zmachine BDI_Machine =
  over BDI_st  init "[beliefs \<leadsto> {}, pl \<leadsto> ([], (null, [])), phase \<leadsto> perceive, trm \<leadsto> False]"
  operations Terminate Perceive Select NullSelect Execute
  until "trm"

(* animate BDI_Machine *)

term "plan"

lemma "deadlock_free BDI_Machine"
  apply deadlock_free
  apply (auto simp add: BeliefUpdates_def)
  apply (meson Phase.exhaust_disc)
  apply (smt (z3) LeastI)
  apply (meson Phase.exhaust)+
  apply (metis null_plan_act_def)
  apply (meson Phase.exhaust)+
  done
  
end