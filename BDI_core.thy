theory BDI_core
  imports "Z_Machines.Z_Machine"
begin

section \<open>Core BDI data types\<close>

type_synonym Name = string
(* for symplicity assume all values are nats *)
datatype Value = Atom Name | Nat nat
type_synonym Ctx = "string \<Rightarrow> Value"

(* make enum types? *)
datatype Action
  = move
  | await_decontamination
  | inspect
  | null
  | impossible_action (* an example of an impossible action *)

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

datatype Symbol = Var Name | Val Value

type_synonym ConcParamAction = "Action \<times> Value list"
type_synonym AbstParamAction = "Action \<times> Symbol list"

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
  | unlearnable (* a belief which can never be learned *)
type_synonym ParamBelief = "Belief \<times> Value list"

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
"show_Belief move_failure = ''move_failure''"|
"show_Belief unlearnable = ''unlearnable''"

instance ..

end

instantiation Value :: Haskell_Show.show
begin

fun show_Value :: "Value \<Rightarrow> string" where 
"show_Value (Atom x) = ''Atom'' + x"|
"show_Value (Nat n) = ''Nat'' + show n"

instance ..

end

datatype AbstPat = 
    pat BelSign Belief "Symbol list"
  | patlist "AbstPat list"

instantiation AbstPat :: default
begin

definition default_AbstPat :: "AbstPat" where 
"default_AbstPat = patlist []"

instance ..

end

datatype ConcPat = 
    cpat BelSign Belief "Value list"
  | cpatlist "ConcPat list"

instantiation ConcPat :: default
begin

definition default_ConcPat :: "ConcPat" where 
"default_ConcPat = cpatlist []"

instance ..

end

type_synonym 'b Update = "(BelMod \<times> 'b)"

type_synonym PlanAct = "(ParamBelief Update list \<times> ConcParamAction)"
(*
priority :: nat
pattern :: AbstPat
belief_update_pattern :: AbstPat
action_pattern :: AbstParamAction
*)
type_synonym Plan = "(nat \<times> AbstPat \<times> AbstPat \<times> AbstParamAction) set"

enumtype Phase = perceive | select | exec

section \<open>Functions\<close>

subsection \<open>Plan rule instantiation\<close>

(* expansion to full patterns involving fixed value params *)
fun eval_name :: "Ctx \<Rightarrow> Symbol \<Rightarrow> Value" where
"eval_name C (Var x) = C x"|
"eval_name C (Val y) = y"

fun instantiate_pat :: "Ctx \<Rightarrow> AbstPat \<Rightarrow> ConcPat" where
"instantiate_pat C (pat s b xs) = (cpat s b (map (eval_name C) xs))"|
"instantiate_pat C (patlist xs) = (cpatlist (map (instantiate_pat C) xs))"

fun free_vars :: "AbstPat \<Rightarrow> Name set" where
"free_vars (pat s b xs) = {x | x.  Var x \<in> set xs}"|
"free_vars (patlist xs) = foldl union {} (map free_vars xs)"

fun pat_extentions :: "AbstPat \<Rightarrow> AbstPat set" where
"pat_extentions (pat s p xs) = {patlist (ys + [pat s p xs] + zs) | ys zs . True}"|
"pat_extentions (patlist xs) = {patlist (ys + xs + zs) | ys zs . True}"

fun pat_instantiations :: "AbstPat \<Rightarrow> (Ctx \<times> ConcPat) set" where
"pat_instantiations p = {(C, instantiate_pat C p) | C . True}"

fun matches_pat :: "AbstPat \<Rightarrow> ParamBelief set \<Rightarrow> Ctx \<Rightarrow> bool" where
"matches_pat (patlist []) B C = True"|
"matches_pat (patlist (x#xs)) B C = (matches_pat x B C
                                   \<and> matches_pat (patlist xs) B C)"|
"matches_pat (pat pos b xs) B C = ((b, map (eval_name C) xs) \<in> B)"|
"matches_pat (pat neg b xs) B C = ((b, map (eval_name C) xs) \<notin> B)"

fun pat_matches :: "AbstPat \<Rightarrow> ParamBelief set \<Rightarrow> Ctx set" where
"pat_matches p B = { C | C . matches_pat p B C }"

(*
fun pat_matches :: "AbstPat \<Rightarrow> ParamBelief set \<Rightarrow> Ctx set" where
"pat_matches p B = { C | C pc . (C, pc) \<in> pat_instantiations p
                              \<and> pc \<in> bel_patterns B }"
 *)

fun instantiate_act :: "Ctx \<Rightarrow> AbstParamAction \<Rightarrow> ConcParamAction" where
"instantiate_act C (act, xs) = (act, map (eval_name C) xs)"

subsection \<open>Belief updates\<close>

fun update_seq :: "ConcPat \<Rightarrow> ParamBelief Update list" where
"update_seq (cpat s b xs) = [((if s = pos then lrn else fgt), (b, xs))]"|
"update_seq (cpatlist []) = []"|
"update_seq (cpatlist (x # xs)) = update_seq x @ update_seq (cpatlist xs)"

fun upd :: "ParamBelief set \<Rightarrow> ParamBelief Update list \<Rightarrow> ParamBelief set" where
"upd B ((lrn, b) # xs) = upd (B \<union> {b}) xs"|
"upd B ((fgt, b) # xs) = upd (B - {b}) xs"|
"upd B [] = B"

fun belief_updates :: "Belief set \<Rightarrow> ParamBelief Update list set" where
"belief_updates perm = {[(bm, (b, ns)) . bm \<leftarrow> bms, b \<leftarrow> bs, ns \<leftarrow> nss, b \<in> perm] | bms bs nss . True }"

subsection \<open>Next step selection\<close>

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

definition null_plan_act :: PlanAct where
"null_plan_act = ([], (null, []))"

fun next_steps :: "Plan \<Rightarrow> ParamBelief set \<Rightarrow> PlanAct set" where
"next_steps p B = (case min_priority p B of
  Some n \<Rightarrow> next_steps_pri n p B |
  None   \<Rightarrow> {null_plan_act}
)"

section \<open>Laws\<close>

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

lemma upd_seq_step:
  shows "b \<in> upd bs xs = (
         (b \<in> bs \<and> (fgt, b) \<notin> set xs)
       \<or> (\<exists> i. i < length xs \<and> (lrn, b) = (nth xs i) \<and> (\<forall> j. j > i \<and> j < length xs \<longrightarrow> (fgt, b) \<noteq> (nth xs j))))"
proof (induction xs arbitrary: bs rule: upd.induct)
  case (1 B b xs)
  then show ?case
    apply(simp)
    apply(safe)
    apply (metis Suc_less_eq Suc_pred in_set_conv_nth less_Suc_eq_0_disj nth_Cons_0)
    apply (smt (verit, ccfv_SIG) Suc_less_eq Suc_pred less_nat_zero_code linorder_neqE_nat nth_Cons_Suc)
    apply (smt (verit, ccfv_threshold) Suc_pred not_gr_zero not_less_eq nth_Cons_Suc zero_less_Suc)
    apply (metis (no_types, lifting) One_nat_def diff_Suc_1 less_Suc_eq_0_disj nth_Cons_0 nth_Cons_Suc old.prod.inject)
    apply (metis (no_types, lifting) One_nat_def diff_Suc_1 in_set_conv_nth less_Suc_eq_0_disj nth_Cons_Suc)
    done
next
  case (2 B b xs)
  then show ?case
    apply(simp)
    apply(safe)
    apply (smt (verit, ccfv_threshold) Suc_pred not_gr_zero not_less_eq nth_Cons_Suc zero_less_Suc)
    apply (smt (verit, ccfv_threshold) Suc_pred not_gr_zero not_less_eq nth_Cons_Suc zero_less_Suc)
    apply (smt (verit, ccfv_SIG) Suc_pred not_gr_zero not_less_eq nth_Cons_Suc zero_less_Suc)
    apply (metis (no_types, lifting) BelMod.distinct_disc(1) One_nat_def diff_Suc_1 less_Suc_eq_0_disj nth_Cons_0 nth_Cons_Suc old.prod.inject)
    apply (metis (no_types, lifting) BelMod.distinct_disc(1) One_nat_def diff_Suc_1 less_Suc_eq_0_disj nth_Cons_0 nth_Cons_Suc old.prod.inject)
    apply (metis (no_types, lifting) BelMod.distinct_disc(1) One_nat_def diff_Suc_1 less_Suc_eq_0_disj nth_Cons_0 nth_Cons_Suc old.prod.inject)
    done
next
  case (3 B)
  then show ?case
    by simp
qed

text \<open>We can characterize the update sequence in terms of whether we learn (lrns) a given belief,
      and whether we subsequently forget (fgts) it\<close>

fun lrns fgts where
"lrns b [] = False"|
"fgts b [] = False"|
"lrns b (x # xs) = ((x = (lrn, b)) \<and> (\<not> fgts b xs) \<or> lrns b xs)"|
"fgts b (x # xs) = ((x = (fgt, b)) \<and> (\<not> lrns b xs) \<or> fgts b xs)"

lemma upd_seq_step_lrns_fgts:
  "b \<in> upd bs xs = ((b \<in> bs \<and> \<not> fgts b xs) \<or> (lrns b xs))"
  apply (induction xs arbitrary: bs rule: upd.induct)
  apply auto
  done

lemma nonpermitted_belief_update:
  assumes "b \<notin> perm" "bel_up \<in> belief_updates perm"
  shows "((b, ns) \<in> bels) = ((b, ns) \<in> (upd bels bel_up))"
  by (meson assms(1) assms(2) belief_updates_permitted upd_fgt_lrn)

lemma min_none_cond: "(min_priority p B = None) = (\<forall>i . next_steps_pri i p B = {})"
  by (auto split: option.splits)

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

end