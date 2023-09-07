theory bdi
  imports "UTP-Circus.utp_circus" (* "UTP-Circus.utp_circus_prefix" *) (* "UTP.utp_full" *)
begin

notation GuardCSP (infixr "&&" 60)

utp_lift_notation GuardCSP (1)

subsection {* Preliminaries *}

no_translations
  "a \<^bold>\<rightarrow> P" == "CONST PrefixCSP \<guillemotleft>a\<guillemotright> P"

translations
  "a \<^bold>\<rightarrow> P" == "CONST PrefixCSP \<guillemotleft>a()\<guillemotright> P"

(*
 recall_syntax

text \<open> We change := so that it refers to the Circus operator \<close>

no_adhoc_overloading
  uassigns assigns_r

adhoc_overloading
  uassigns AssignsCSP
              
notation GuardCSP (infixr "&&" 60)

utp_lift_notation GuardCSP (1)

purge_notation while_top ("while _ do _ od")

notation WhileC ("while _ do _ od")

utp_lift_notation WhileC (1)
*)

(*
recall_syntax

no_translations
  "a \<^bold>\<rightarrow> P" == "CONST PrefixCSP \<guillemotleft>a\<guillemotright> P"

translations
  "a \<^bold>\<rightarrow> P" == "CONST PrefixCSP \<guillemotleft>a()\<guillemotright> P"
*)

section \<open> BDI encoding \<close>

datatype '\<beta> Update = lrn '\<beta> (* learn *)
                   | fgt '\<beta> (* forget *)

fun upd :: "'\<beta> set \<Rightarrow> '\<beta> Update list \<Rightarrow> '\<beta> set" where
"upd B [] = B"|
"upd B (lrn b#bs) = upd (union B {b}) bs"|
"upd B (fgt b#bs) = upd (B - {b}) bs"

type_synonym ('\<beta>, '\<alpha>) Plan = "'\<beta> Update list \<times> '\<alpha>"

datatype Phase = p | s | e
datatype Trans = initialise | terminate | perceive | select | execute

alphabet ('\<beta>, '\<alpha>) bdi_state =
  phase        :: "Phase"
  beliefs      :: "'\<beta> set"
  current_plan :: "'\<beta> Update \<times> '\<alpha>"
  test         :: "bool"
  store_nat    :: "nat"

datatype ('\<beta>, '\<alpha>) bdi_ch = believe "'\<beta>" | doo "'\<alpha>" | endd "unit" | trans "Trans" | send_nat "nat"

abbreviation bdi_prefix ::
  "((('\<beta>, '\<alpha>) bdi_state), ('\<beta>, '\<alpha>) bdi_ch) chan \<Rightarrow>
   ((('\<beta>, '\<alpha>) bdi_state), (('\<beta>, '\<alpha>) bdi_ch) + 'ext) chan" where
"bdi_prefix c \<equiv> Inl o c"

type_synonym ('\<beta>, '\<alpha>) bdi_act = "(('\<beta>, '\<alpha>) bdi_state, ('\<beta>, '\<alpha>) bdi_ch) action"
type_synonym ('\<beta>, '\<alpha>) bdi_circus = "('\<beta>, '\<alpha>) bdi_act hrel"


section \<open> Example \<close>

datatype Belief = init | not_at_goal | in_danger | stopped
datatype Action = null | move | emergency_stop | remove_danger


fun plan :: "Belief \<Rightarrow> Belief Update list \<times> Action" where
"plan init        = ([],            null)"|
"plan not_at_goal = ([],            move)"|
"plan in_danger   = ([lrn stopped], emergency_stop)"|
"plan stopped     = ([fgt stopped], remove_danger)"

utp_const plan

term "c \<^bold>\<rightarrow> A"

term "endd \<^bold>\<rightarrow> STOP"
term "x!(1)!(y) \<^bold>\<rightarrow> P" 
term "x!(1)"
term "send_nat!(&store_nat) \<^bold>\<rightarrow> P"
term "($phase =\<^sub>u \<guillemotleft>p\<guillemotright>) && endd() \<^bold>\<rightarrow> STOP"
term "endd() \<^bold>\<rightarrow> STOP"
term "trans!(\<guillemotleft>perceive\<guillemotright>) \<^bold>\<rightarrow> STOP"
term "($phase =\<^sub>u \<guillemotleft>p\<guillemotright>) &\<^sub>C STOP"

definition BDI_end_stop :: "('\<beta>, '\<alpha>) bdi_act hrel" where
"BDI_end_stop = (c \<rightarrow>\<^sub>\<C> A)"

(* :: "('\<beta>, '\<alpha>) bdi_act" *)
definition BDI where [rdes_def]:
"BDI = (
     (($phase =\<^sub>u \<guillemotleft>p\<guillemotright>) &\<^sub>C (endd \<^bold>\<rightarrow> STOP))
)"

(* \<box> (endd \<^bold>\<rightarrow> STOP) *)

(*  \<triangleleft> $st =\<^sub>u \<guillemotleft>p\<guillemotright> \<triangleright> STOP *)

(*
   \<box> ((trans!(perceive) \<rightarrow> believe?(bm) \<rightarrow> $st :=\<^sub>C \<guillemotleft>p\<guillemotright> \<rightarrow>
       beliefs :=\<^sub>C upd(beliefs, bm) \<rightarrow> BDI)  \<triangleleft> $st =\<^sub>u \<guillemotleft>s\<guillemotright> \<triangleright> STOP)
   \<box> ((trans!(select) \<rightarrow> $st :=\<^sub>C \<guillemotleft>e\<guillemotright> \<rightarrow> $current_plan :=\<^sub>C plan \<guillemotleft>current_plan\<guillemotright> \<rightarrow> BDI)
      \<triangleleft> $st =\<^sub>u \<guillemotleft>s\<guillemotright> \<triangleright> STOP)
   \<box> ((trans!(execute) \<rightarrow> do_!(snd \<guillemotleft>current_plan\<guillemotright>) \<rightarrow> $st :=\<^sub>C \<guillemotleft>p\<guillemotright> \<rightarrow> BDI) \<triangleleft> $st =\<^sub>u \<guillemotleft>e\<guillemotright> \<triangleright> STOP)
*)

definition BDI_init where
"BDI_init = trans!initialize \<rightarrow> beliefs :=\<^sub>C {} \<rightarrow> $current_plan :=\<^sub>C (lrn \<guillemotleft>none\<guillemotright>, null) \<rightarrow> $st :=\<^sub>C \<guillemotleft>p\<guillemotright> \<rightarrow> BDI"


end