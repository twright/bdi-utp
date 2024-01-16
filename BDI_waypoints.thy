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

definition "perceptibles = {move_failure, location_coordinate}"

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

fun pat_extentions :: "AbstPat \<Rightarrow> AbstPat set" where
"pat_extentions (pat s p xs) = {patlist (ys + [pat s p xs] + zs) | ys zs . True}"|
"pat_extentions (patlist xs) = {patlist (ys + xs + zs) | ys zs . True}"

fun pat_instantiations :: "AbstPat \<Rightarrow> (Ctx \<times> ConcPat) set" where
"pat_instantiations p = {(C, instantiate_pat C p) | C . True}"

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


(* - could split up internal beliefs and perception beliefs
 * - from perception?
 *)

fun upd :: "ParamBelief set \<Rightarrow> ParamBelief Update list \<Rightarrow> ParamBelief set" where
"upd B ((lrn, b) # xs) = upd (B \<union> {b}) xs"|
"upd B ((fgt, b) # xs) = upd (B - {b}) xs"|
"upd B [] = B"

zstore BDI_st =
  beliefs :: "ParamBelief set"
  pl :: "PlanAct"
  phase :: Phase
  trm :: "bool"
  (* perceivables :: "Belief set" *)
(*
  where inv1: "(location, [door, X1, Y1]) \<in> beliefs \<and> (location, [door, X2, Y2]) \<in> beliefs \<longrightarrow> X1 = X2 \<and> Y1 = Y2"
*)

zoperation Terminate = 
  pre "phase = perceive"
  update "[trm \<leadsto> True]"

(*
definition BeliefUpdates :: "ParamBelief Update list set"
  where "BeliefUpdates = UNIV"
*)
fun belief_updates :: "Belief set \<Rightarrow> ParamBelief Update list set" where
"belief_updates perm = {[(bm, (b, ns)) . bm \<leftarrow> bms, b \<leftarrow> bs, ns \<leftarrow> nss, b \<in> perm] | bms bs nss . True }"

lemma belief_updates_permitted:
  "xs \<in> belief_updates perm \<Longrightarrow> (bm, (b, ns)) \<in> set xs \<Longrightarrow> b \<in> perm"
  apply(auto)
  by (meson empty_iff)

lemma upd_fgt_lrn:
  assumes "(x \<in> bels) \<noteq> (x \<in> (upd bels bel_up))"
  shows "(fgt, x) \<in> set bel_up \<or> (lrn, x) \<in> set bel_up"
  using assms apply clarsimp
proof (induction bel_up arbitrary: x bels)
  case Nil
  then show ?case
  by simp
next
  case (Cons a bel_up)
  then show ?case
    apply(case_tac a)
    apply(case_tac aa)
     apply (metis (no_types, lifting) Un_insert_right insert_iff list.set(2) sup_bot.right_neutral upd.simps(1))
    apply(auto)
    using Cons.IH apply blast
    apply (metis Cons.IH Diff_iff)
    done
qed

lemma nonpermitted_belief_update:
  assumes "b \<notin> perm" "bel_up \<in> belief_updates perm"
  shows "((b, ns) \<in> bels) = ((b, ns) \<in> (upd bels bel_up))"
  by (meson assms(1) assms(2) belief_updates_permitted upd_fgt_lrn)

term "upd {} [] :: ParamBelief set"

(* add on a whitelist or a blacklist *)
zoperation Perceive =
  params bel_up \<in> "belief_updates perceptibles"
  pre "phase = perceive"
  update "[phase \<leadsto> select, beliefs \<leadsto> upd beliefs bel_up]"

(*
 - always believes going or believes arrived
 - never believes it is going to two different places
 *)

(*
goal_inspect(Location), location_coordinate(Location, X, Y), ~danger_red, ~danger_orange, ~going(door)
-(1)> +going(Location), -goal_inspect(Location), do(move(X, Y))

arrived, going(door) -(2)> -going(door), do(await_decontamination)
arrived, going(OldLocation), next_location(OldLocation, NewLocation)
-(1)> -going(OldLocation), +goal_inspect(NL), -arrived, do(inspect(OldLocation))
arrived, ~going(OldLocation) -(1)> -arrived, do(null)
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

definition BDI_init :: "BDI_st subst" where
"BDI_init = [beliefs \<leadsto> {}, pl \<leadsto> ([], (null, [])), phase \<leadsto> perceive, trm \<leadsto> False]"

declare BDI_init_def [simp]

zmachine BDI_Machine =
  over BDI_st 
  init BDI_init
(*  invariant BDI_st_inv *)
  operations Terminate Perceive Select NullSelect Execute
  until "trm"

(* animate BDI_Machine *)

term "plan"

zexpr unique_door_location is "\<forall> door X1 X2 Y1 Y2 . (location, [door, X1, Y1]) \<in> beliefs
                                                  \<and> (location, [door, X2, Y2]) \<in> beliefs
                                                 \<longrightarrow> X1 = X2 \<and> Y1 = Y2"
zexpr initial_phase is "phase = Phase.perceive"
zexpr unique_going_location is "\<forall> X1 X2 . (going, [X1]) \<in> beliefs
                                        \<and> (going, [X2]) \<in> beliefs
                                       \<longrightarrow> X1 = X2"

(* Side condition: never perceive that you are going somewhere *)

lemma "BDI_init establishes initial_phase"
  by zpog_full

lemma "BDI_init establishes unique_going_location"
  by zpog_full

lemma "Terminate() preserves unique_going_location"
  by zpog_full

lemma "NullSelect() preserves unique_going_location"
  by zpog_full

lemma "Select(xs, a, ys) preserves unique_going_location"
  by zpog_full

lemma perceive_preserves_nonperceivables:
  assumes "(b \<notin> perceptibles)"
  shows "Perceive(xs) preserves \<guillemotleft>(b, ns)\<guillemotright> \<in> beliefs"
proof -
  {
    fix beliefs bms bs nss
    assume 2: "xs = [(bm, b, ns) . bm \<leftarrow> bms, b \<leftarrow> bs, ns \<leftarrow> nss, b \<in> perceptibles]"
    have 3: "xs \<in> belief_updates perceptibles"
      by (auto simp add: 2)
    have "((b, ns) \<in> beliefs) = ((b, ns) \<in> upd beliefs xs)"
      using nonpermitted_belief_update
      using 3 assms by blast
  }
  hence 1: "\<And>beliefs bms bs nss. xs = [(bm, b, ns) . bm \<leftarrow> bms, b \<leftarrow> bs, ns \<leftarrow> nss, b \<in> perceptibles] \<Longrightarrow>
                                 ((b, ns) \<in> beliefs) = ((b, ns) \<in> upd beliefs xs)" .
  show ?thesis
    apply(zpog_full)
    using 1 by blast
qed

(* Together these lemmata should be sufficient for establishing the unique_going_location
 * property compositionally *)

lemma perceive_preserves_going:
  "Perceive(xs) preserves (going, [X]) \<in> beliefs"
  by (simp add: perceive_preserves_nonperceivables perceptibles_def)

lemma perceive_preserves:
  "Perceive(xs) preserves X1 = X2"
  by (zpog_full)

lemma hoare_forall_single: 
  assumes "\<forall> x. \<^bold>{Q x\<^bold>}P\<^bold>{R x\<^bold>}"
  shows "\<^bold>{\<forall> x. Q x\<^bold>}P\<^bold>{\<forall> x. R x\<^bold>}"
  using assms apply(hoare_wlp_auto)
  apply expr_auto
  apply(simp add: hoare_triple_def)
  by (smt (verit, best) wlp_itree_def)
  (* by metis *)

lemma hoare_forall_double:
  assumes "\<And> x y. \<^bold>{Q x y\<^bold>}P\<^bold>{R x y\<^bold>}"
  shows "\<^bold>{\<forall> x y. Q x y\<^bold>}P\<^bold>{\<forall> x y. R x y\<^bold>}"
  using assms apply(hoare_wlp_auto)
  apply expr_auto
  apply(simp add: hoare_triple_def)
  by (smt (verit, best) wlp_itree_def)

lemma hoare_implies:
  assumes "\<^bold>{a\<^bold>}P\<^bold>{a\<^bold>}" "\<^bold>{b\<^bold>}P\<^bold>{b\<^bold>}"
  shows "\<^bold>{a\<longrightarrow>b\<^bold>}P\<^bold>{a\<longrightarrow>b\<^bold>}"
  using assms by hoare_wlp_auto

lemma preserves_implies:
  assumes "Perceive(xs) preserves a" "Perceive(xs) preserves b"
  shows "Perceive(xs) preserves (a \<longrightarrow> b)"
  by (simp add: hoare_alt_def)

lemma preserves_neg:
  assumes "Perceive(xs) preserves a"
  shows "Perceive(xs) preserves (\<not> a)"
  by (simp add: hoare_alt_def)

(* It should be possible to replace this with a compositional proof based on the lemmata above,
 * however, technical issues to do with how UTP expressions are parsed are getting in the way of
 * this *)
lemma perceive_pereserves_unique_going:
  "Perceive(xs) preserves unique_going_location"
proof -
  {
    fix beliefs::"ParamBelief set"
    fix bms bs nss X1 X2
    assume 1: "\<forall>X1 X2. (going, [X1]) \<in> beliefs \<and> (going, [X2]) \<in> beliefs \<longrightarrow> X1 = X2"
    assume 2: "xs = [(bm, b, ns) . bm \<leftarrow> bms, b \<leftarrow> bs, ns \<leftarrow> nss, b \<in> perceptibles]" (is "xs = ?xs")
    have 5: "?xs \<in> belief_updates perceptibles"
      by (auto)
    assume 3: "(going, [X1]) \<in> upd beliefs ?xs"
    assume 4: "(going, [X2]) \<in> upd beliefs ?xs"
    have 6: "going \<notin> perceptibles"
      by (simp add: perceptibles_def)
    have 7: "(going, [X1]) \<in> beliefs" "(going, [X2]) \<in> beliefs"
      using 6 5 3 nonpermitted_belief_update apply presburger
      using 6 5 4 nonpermitted_belief_update apply presburger
      done
    then have "X1 = X2"
      using 1 by auto
  }
  thus ?thesis
    apply(simp add: unique_going_location_def)
    apply(zpog_full)
    done
qed

lemma "deadlock_free BDI_Machine"
  apply deadlock_free
  apply (auto)
  apply (meson Phase.exhaust_disc)
  apply (smt (z3) LeastI)
  apply (meson Phase.exhaust)+
  apply metis
  apply (meson Phase.exhaust)+
  apply (metis null_plan_act_def)
  apply (meson Phase.exhaust)+
  done

(* 
 - small model: model checking of specific example to general result
 - monitoring action: I expect these things to happen when an action is taken
*)

(*
zexpr phase_order is
"phase = select \<longrightarrow> phase\<acute> = exec"
*)

end