theory
  BDI_inspector
imports
  BDI_zmachines
begin

text \<open> This machine describes a nuclear radiation detection robot \<close>

text \<open> Some ideas for properties:
 - always believes going or believes arrived
 - never believes it is going to two different places \<close>

text \<open> The machine should implement the following plan:
goal_inspect(Location), location_coordinate(Location, X, Y), ~danger_red, ~danger_orange, ~going(door)
-(1)> +going(Location), -goal_inspect(Location), do(move(X, Y))

arrived, going(door) -(2)> -going(door), do(await_decontamination)
arrived, going(OldLocation), next_location(OldLocation, NewLocation)
-(1)> -going(OldLocation), +goal_inspect(NL), -arrived, do(inspect(OldLocation))
arrived, ~going(OldLocation) -(1)> -arrived, do(null)
move_failure -(1)> do(null)

danger_red, ~going(door), location(door, X, Y) -(2)> +going(door), move(X, Y)
danger_orange, ~going(door), location(door, X, Y) -(2)> +going(door), move(X, Y) ﻿
 \<close>


def_consts
plan = "{
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

section \<open>Machine definition\<close>

zmachine BDI_Machine =
  over BDI_st 
  init BDI_init
  invariant exec_next_steps
  operations Terminate Perceive Select NullSelect Execute
  until "trm"

subsection \<open>Impossible action should not occur\<close>

zexpr impossible_action_impossible is "\<forall> xs. (impossible_action, xs) \<notin> set act_tr"

lemma "BDI_init establishes impossible_action_impossible"
  by (zpog_full)

lemma "Perceive(xs) preserves impossible_action_impossible"
  by (zpog_full)

lemma "NullSelect() preserves impossible_action_impossible"
  by (zpog_full)

lemma "Select(xs) preserves impossible_action_impossible"
  by (zpog_full)

lemma "Terminate() preserves impossible_action_impossible"
  by (zpog_full)

lemma "Execute() preserves impossible_action_impossible under exec_next_steps"
  apply (zpog_full)
  apply(auto simp add: plan_def)
  apply (metis Action.distinct(19) null_plan_act_def prod.inject snd_conv)
  done

subsection \<open>An unlearnable action should never become believed\<close>

fun unlearnable_unbelieved_prop where
"unlearnable_unbelieved_prop bs = (\<forall> xs. (unlearnable, xs) \<notin> bs)"

zexpr unlearnable_unbelieved is "unlearnable_unbelieved_prop beliefs"

lemma unlearnable_unbelieved_prop_preservation: "preserves_belief_set_prop plan (unlearnable_unbelieved_prop)"
  apply(rule rulewise_plan_preservation_weak)
  apply(simp add: plan_def)
  done

lemma "Execute(xs) preserves unlearnable_unbelieved under exec_next_steps"
proof -
  have "Execute(xs) preserves unlearnable_unbelieved_prop beliefs under exec_next_steps"
    using exec_prop_preservation unlearnable_unbelieved_prop_preservation by blast
  thus ?thesis
    by (hoare_wlp_auto)
qed

lemma "Perceive(xs) preserves unlearnable_unbelieved"
proof -
  {
    fix beliefs::"ParamBelief set"
    fix bms :: "BelMod list"
    fix bs
    fix nss :: "nat list list"
    fix zs
    assume 1: "\<forall>xs. (unlearnable, xs) \<notin> beliefs"
    let ?ys = "[(bm, b, ns) . bm \<leftarrow> bms, b \<leftarrow> bs, ns \<leftarrow> nss, b \<in> perceptibles]"
    have 5: "?ys \<in> belief_updates perceptibles"
      by (auto)
    have 6: "unlearnable \<notin> perceptibles"
      by (simp add: perceptibles_def)
    have "(unlearnable, zs) \<notin> upd beliefs ?ys"
      using "1" "5" "6" nonpermitted_belief_update by blast
  }
  thus ?thesis
    apply(simp add: unlearnable_unbelieved_def)
    apply(zpog_full)
    done
qed

subsection \<open>Unique going location proofs\<close>

zexpr unique_going_location is "\<forall> X1 X2 . (going, [X1]) \<in> beliefs
                                        \<and> (going, [X2]) \<in> beliefs
                                       \<longrightarrow> X1 = X2"

lemma "BDI_init establishes unique_going_location"
  by zpog_full

lemma "Terminate() preserves unique_going_location"
  by zpog_full

lemma "NullSelect() preserves unique_going_location"
  by zpog_full

lemma "Select(xs) preserves unique_going_location"
  by zpog_full

(* Together these lemmata should be sufficient for establishing the unique_going_location
 * property compositionally *)

lemma perceive_preserves_going:
  "Perceive(xs) preserves (going, [X]) \<in> beliefs"
  by (simp add: perceive_preserves_nonperceivables perceptibles_def)

lemma perceive_preserves:
  "Perceive(xs) preserves X1 = X2"
  by (zpog_full)

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

lemma "preserves_belief_set_prop plan (unique_going_location_prop)"
  apply(rule rulewise_plan_preservation_weak)
  apply(simp add: plan_def)
  apply(safe)
  oops

term BDI_Machine

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


end