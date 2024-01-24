theory BDI_zmachines
  imports "Z_Machines.Z_Machine" BDI_core
begin

section \<open> BDI zmachine state \<close>

consts plan::"Plan"

zstore BDI_st =
  beliefs :: "ParamBelief set"
  pl :: "PlanAct"
  phase :: Phase
  (* trace capturing the sequencing of each action *)
  (* do we also need a trace capturing the belief state over time *)
  act_tr :: "ConcParamAction list"
  trm :: "bool"

section \<open> BDI ZMachine operations \<close>

zoperation Terminate = 
  pre "phase = perceive"
  update "[trm \<leadsto> True]"

zoperation Perceive =
  params bel_up \<in> "belief_updates perceptibles"
  pre "phase = perceive"
  update "[phase \<leadsto> select, beliefs \<leadsto> upd beliefs bel_up]"

zoperation Select =
  params pl' \<in> "next_steps plan beliefs"
  pre "phase = select \<and> beliefs \<noteq> {}"
  update "[phase \<leadsto> exec, pl \<leadsto> pl']"

(* should skip straight back to perceive phase if we have no beliefs *)
zoperation NullSelect =
  pre "phase = select \<and> beliefs = {}"
  update "[phase \<leadsto> perceive]"

zoperation Execute =
  pre "phase = exec"
  update "[beliefs \<leadsto> upd beliefs (fst pl), phase \<leadsto> perceive, act_tr \<leadsto> act_tr @ [snd pl]]"

definition BDI_init :: "BDI_st subst" where
"BDI_init = [beliefs \<leadsto> {}, pl \<leadsto> ([], (null, [])), phase \<leadsto> perceive, trm \<leadsto> False, act_tr \<leadsto> []]"

declare BDI_init_def [simp]

section \<open>ZMachine definition\<close>

zmachine BDI_Machine =
  over BDI_st 
  init BDI_init
  operations Terminate Perceive Select NullSelect Execute
  until "trm"

section \<open>Basic BDI invariants\<close>

zexpr exec_next_steps is "phase = Phase.exec \<longrightarrow> pl \<in> next_steps plan beliefs"

lemma "BDI_init establishes exec_next_steps"
  by zpog_full

lemma "Terminate() preserves exec_next_steps"
  by zpog_full

lemma "NullSelect() preserves exec_next_steps"
  by zpog_full

lemma "Select(xs) preserves exec_next_steps"
  by zpog_full

lemma "Execute(p) preserves exec_next_steps"
  by zpog_full

section \<open>Proof laws\<close>

lemma perceive_preserves_nonperceivables:
  assumes "(b \<notin> perceptibles)"
  shows "Perceive(xs) preserves (b, ns) \<in> beliefs"
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

subsection \<open>Belief set properties\<close>

text \<open> Want a good way to say that a given plan preserves a property on belief sets \<close>

type_synonym Belief_Set_Prop = "ParamBelief set \<Rightarrow> bool"

fun preserves_belief_set_prop :: "Plan \<Rightarrow> Belief_Set_Prop \<Rightarrow> bool" where
"preserves_belief_set_prop pla bsp = (\<forall> bs.
                                      \<forall> (up, a) \<in> next_steps pla bs.
                                      bsp bs \<longrightarrow> bsp(upd bs up))"

fun conditionally_preserves_belief_set_prop :: "Plan \<Rightarrow> Belief_Set_Prop \<Rightarrow> Belief_Set_Prop \<Rightarrow> bool" where
"conditionally_preserves_belief_set_prop pla prebsp bsp =
  (\<forall> bs. \<forall> (up, a) \<in> next_steps pla bs. prebsp bs \<and> bsp bs \<longrightarrow> bsp(upd bs up))"

lemma rulewise_plan_preservation:
  assumes "\<forall> (i, p1, p2, a) \<in> pla. \<forall> bs. \<forall> C \<in> pat_matches p1 bs.
           bsp bs \<longrightarrow> bsp (upd bs (update_seq (instantiate_pat C p2)))"
  shows "preserves_belief_set_prop pla bsp"
  using assms by (auto simp add: null_plan_act_def)

lemma rulewise_plan_preservation_match:
  assumes "\<forall> (i, p1, p2, a) \<in> pla. \<forall> bs. \<forall> C.
               matches_pat p1 bs C
           \<longrightarrow> (bsp bs \<longrightarrow> bsp (upd bs (update_seq (instantiate_pat C p2))))"
  shows "preserves_belief_set_prop pla bsp"
  using assms pat_matches_alt_def rulewise_plan_preservation by force

lemma rulewise_plan_preservation_weak:
  assumes "\<forall> (i, p1, p2, a) \<in> pla. \<forall> bs. \<forall> C.
           bsp bs \<longrightarrow> bsp (upd bs (update_seq (instantiate_pat C p2)))"
  shows "preserves_belief_set_prop pla bsp"
  using assms by (auto simp add: null_plan_act_def)

lemma cond_rulewise_plan_preservation:
  assumes "\<forall> (i, p1, p2, a) \<in> pla. \<forall> bs. \<forall> C \<in> pat_matches p1 bs.
           prebsp bs \<and> bsp bs \<longrightarrow> bsp (upd bs (update_seq (instantiate_pat C p2)))"
  shows "conditionally_preserves_belief_set_prop pla prebsp bsp"
  using assms by (auto simp add: null_plan_act_def)

lemma cond_rulewise_plan_preservation_match:
  assumes "\<forall> (i, p1, p2, a) \<in> pla. \<forall> bs. \<forall> C.
             matches_pat p1 bs C
           \<and> prebsp bs \<and> bsp bs \<longrightarrow> bsp (upd bs (update_seq (instantiate_pat C p2)))"
  shows "conditionally_preserves_belief_set_prop pla prebsp bsp"
  by (smt (verit, ccfv_SIG) assms case_prod_beta' cond_rulewise_plan_preservation mem_Collect_eq pat_matches_alt_def)

lemma cond_rulewise_plan_preservation_weak:
  assumes "\<forall> (i, p1, p2, a) \<in> pla. \<forall> bs. \<forall> C.
           prebsp bs \<and> bsp bs \<longrightarrow> bsp (upd bs (update_seq (instantiate_pat C p2)))"
  shows "conditionally_preserves_belief_set_prop pla prebsp bsp"
  using assms by (auto simp add: null_plan_act_def)

lemma exec_prop_preservation:
  assumes "preserves_belief_set_prop plan prop"
  shows "Execute(xs) preserves prop beliefs under exec_next_steps"
  using assms apply (simp add: prog_defs hl_via_wlp wp usubst_eval z_defs del: next_steps.simps)
  by (smt (verit, best) SEXP_def case_prod_beta' taut_def)


lemma exec_prop_preservation_given:
  assumes "conditionally_preserves_belief_set_prop plan preprop prop"
  shows "Execute(xs) preserves prop beliefs under (exec_next_steps \<and> preprop beliefs)"
  using assms apply (simp add: prog_defs hl_via_wlp wp usubst_eval z_defs del: next_steps.simps)
  by (smt (verit, best) SEXP_def case_prod_beta' taut_def)

lemma preserves_implies:
  assumes "Perceive(xs) preserves a" "Perceive(xs) preserves b"
  shows "Perceive(xs) preserves (a \<longrightarrow> b)"
  by (simp add: hoare_alt_def)

lemma preserves_neg:
  assumes "Perceive(xs) preserves a"
  shows "Perceive(xs) preserves (\<not> a)"
  by (simp add: hoare_alt_def)

end