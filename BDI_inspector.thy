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

(*
def_consts
plan = "{
  (
    1,
    patlist [pat pos going [Var ''OldLocation''],
             pat pos next_location [Var ''OldLocation'', Var ''NewLocation'']],
    patlist [pat neg going [Var ''OldLocation''],
             pat pos goal_inspect [Var ''NewLocation''],
             pat neg arrived []],
    (inspect, [])
  )
}"
*)

def_consts
plan = "{
  (
    1,
    patlist [pat pos goal_inspect [Var ''Location''],
             pat pos location_coordinate [Var ''Location'', Var ''X'', Var ''Y''],
             pat neg danger_red [],
             pat neg danger_orange [],
             pat neg going [Val (Atom ''door'')]],
    patlist [pat pos going [Var ''Location''],
             pat neg goal_inspect [Var ''Location'']],
    (move, [Var ''X'', Var ''Y''])
  ),
  (
    1,
    patlist [pat pos going [Var ''OldLocation''],
             pat pos next_location [Var ''OldLocation'', Var ''NewLocation'']],
    patlist [pat neg going [Var ''OldLocation''],
             pat pos goal_inspect [Var ''NewLocation''],
             pat neg arrived []],
    (inspect, [])
  )
}"

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
    fix nss :: "Value list list"
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

subsection \<open>Goal inspect exclusive with location\<close>

fun goal_inspect_not_going_prop where
"goal_inspect_not_going_prop bs = (\<forall> X . (goal_inspect, [X]) \<in> bs
                                     \<longrightarrow> (going, [X]) \<notin> bs)"
zexpr goal_inspect_not_going is "goal_inspect_not_going_prop beliefs"

lemma "BDI_init establishes goal_inspect_not_going"
  by zpog_full

lemma "Terminate() preserves goal_inspect_not_going"
  by zpog_full

lemma "NullSelect() preserves goal_inspect_not_going"
  by zpog_full

lemma "Select(xs) preserves goal_inspect_not_going"
  by zpog_full

lemma perceive_pereserves_goal_inspect_not_going:
  "Perceive(xs) preserves goal_inspect_not_going"
proof -
  {
    fix beliefs::"ParamBelief set"
    fix bms :: "BelMod list"
    fix bs
    fix nss :: "Value list list"
    fix X
    assume 1: "\<forall>X. (goal_inspect, [X]) \<in> beliefs \<longrightarrow> (going, [X]) \<notin> beliefs"
    let ?xs = "[(bm, b, ns) . bm \<leftarrow> bms, b \<leftarrow> bs, ns \<leftarrow> nss, b \<in> perceptibles]"
    have 5: "?xs \<in> belief_updates perceptibles"
      by (auto)
    assume 3: "(goal_inspect, [X]) \<in> upd beliefs ?xs"
    have 6: "goal_inspect \<notin> perceptibles" "going \<notin> perceptibles"
      by (simp_all add: perceptibles_def)
    have 7: "(goal_inspect, [X]) \<in> beliefs"
      using "3" "5" "6"(1) nonpermitted_belief_update by presburger
    then have "(going, [X]) \<notin> beliefs"
      by (simp add: "1")
    then have "(going, [X]) \<notin> upd beliefs ?xs"
      using "5" "6"(2) nonpermitted_belief_update by blast
  }
  thus ?thesis
    apply(simp add: goal_inspect_not_going_def)
    apply(zpog_full)
    done
qed

lemma "preserves_belief_set_prop plan (goal_inspect_not_going_prop)"
  apply(rule rulewise_plan_preservation_match)
  apply(simp add: plan_def)
  apply(safe)
  oops


subsection \<open>Unique going location proofs\<close>

fun unique_going_location_prop :: "Belief_Set_Prop" where
"unique_going_location_prop bs = (\<forall> X1 X2 . (going, [X1]) \<in> bs
                                          \<and> (going, [X2]) \<in> bs
                                         \<longrightarrow> X1 = X2)"
zexpr unique_going_location is "unique_going_location_prop beliefs"

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
    fix bms :: "BelMod list"
    fix bs
    fix nss :: "Value list list"
    fix X1 X2
    assume 1: "\<forall>X1 X2. (going, [X1]) \<in> beliefs \<and> (going, [X2]) \<in> beliefs \<longrightarrow> X1 = X2"
    let ?xs = "[(bm, b, ns) . bm \<leftarrow> bms, b \<leftarrow> bs, ns \<leftarrow> nss, b \<in> perceptibles]"
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
  apply(rule rulewise_plan_preservation_match)
  apply(simp add: plan_def)
  oops

(*
fun combined_prop where
"combined_prop B = (\<forall> X Y.
                    ((((goal_inspect, [X]) \<in> B \<or> (going, [X]) \<in> B)
                   \<and> ((goal_inspect, [Y]) \<in> B \<or> (going, [Y]) \<in> B))
                \<longrightarrow> X = Y))"
*)

fun combined_prop where
"combined_prop B = ((\<forall> X.
                    (goal_inspect, [X]) \<in> B
                \<longrightarrow> ((\<forall> Y. (going, [Y]) \<notin> B) \<and> (\<forall> Y. (goal_inspect, [Y]) \<in> B \<longrightarrow> X = Y)))
                 \<and>  (\<forall> X.
                    (going, [X]) \<in> B
                \<longrightarrow> ((\<forall> Y. (goal_inspect, [Y]) \<notin> B) \<and> (\<forall> Y. (going, [Y]) \<in> B \<longrightarrow> X = Y))))"

lemma "preserves_belief_set_prop plan (combined_prop)"
  apply(rule rulewise_plan_preservation_match)
  apply(auto simp add: rulewise_plan_preservation_match plan_def)
  done

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