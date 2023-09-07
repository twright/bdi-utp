theory bdi2
  imports "UTP-Circus.utp_circus_easy_parser"
  (* imports "UTP-Circus.utp_circus" *) (* "UTP-Circus.utp_circus_prefix" *) (* "UTP.utp_full" *)
begin

(*
notation GuardCSP (infixr "&&" 60)

utp_lift_notation GuardCSP (1)
*)

datatype Belief = init | not_at_goal | in_danger | stopped
datatype Action = null | move | emergency_stop | remove_danger

subsection {* Preliminaries *}

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

fun upd :: "Belief set \<Rightarrow> Belief Update \<Rightarrow> Belief set" where
"upd B (lrn b) = union B {b}"|
"upd B (fgt b) = (B - {b})"

syntax
  "_upd"       :: "logic \<Rightarrow> logic \<Rightarrow> logic" ("upd\<^sub>u'(_,_')")

translations
  "upd\<^sub>u(x,y)" == "CONST bop CONST upd x y"

type_synonym ('\<beta>, '\<alpha>) Plan = "'\<beta> Update list \<times> '\<alpha>"

datatype Phase = p | s | e
datatype Trans = initialise | terminate | perceive | select | execute

alphabet bdi_state =
  phase        :: "Phase"
  beliefs      :: "Belief set"
  current_plan :: "Belief Update \<times> Action"
  belief_change :: "Belief Update"

  (* Some extra test variables *)
  test         :: "bool"
  store_nat    :: "nat"

chantype bdi_ch = 
  believe :: "Belief Update"
  doo :: "Action"
  endd :: "bool"
  trans :: "Trans"
  send_nat :: "nat"

(*
datatype ('\<beta>, '\<alpha>) bdi_ch = believe "'\<beta>" | doo "'\<alpha>" | endd "unit" | trans "Trans" | send_nat "nat"
*)

(*
abbreviation bdi_prefix ::
  "((('\<beta>, '\<alpha>) bdi_state), ('\<beta>, '\<alpha>) bdi_ch) chan \<Rightarrow>
   ((('\<beta>, '\<alpha>) bdi_state), (('\<beta>, '\<alpha>) bdi_ch) + 'ext) chan" where
"bdi_prefix c \<equiv> Inl o c"
*)

type_synonym bdi_act = "(bdi_state, bdi_ch) action"
type_synonym bdi_circus = "bdi_act hrel"

(*
utp_lift_notation chan_apply (0)
*)

section \<open> Example \<close>

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
term "(&phase = \<guillemotleft>p\<guillemotright>) && send_nat!(&store_nat) \<^bold>\<rightarrow> Stop"
term "(&phase = \<guillemotleft>p\<guillemotright>) && send_nat!(&store_nat) \<^bold>\<rightarrow> Stop"
term "(&phase = p) && (endd!(\<guillemotleft>True\<guillemotright>) \<^bold>\<rightarrow> Stop)"
term "endd \<^bold>\<rightarrow> Stop"
term "trans!(\<guillemotleft>perceive\<guillemotright>) \<^bold>\<rightarrow> Stop"
term "(&phase = \<guillemotleft>p\<guillemotright>) && trans!(\<guillemotleft>perceive\<guillemotright>) \<^bold>\<rightarrow> Stop"
term "(&phase = \<guillemotleft>p\<guillemotright>) && Stop"
term "Stop :: bdi_act"
term "phase := \<guillemotleft>s\<guillemotright>"
term "(&phase = \<guillemotleft>p\<guillemotright>) && trans!(\<guillemotleft>perceive\<guillemotright>) \<^bold>\<rightarrow> believe?(bm) \<^bold>\<rightarrow> (Stop :: bdi_act)"
term "(&phase = \<guillemotleft>p\<guillemotright>) && trans!(\<guillemotleft>perceive\<guillemotright>) \<^bold>\<rightarrow> believe?(bm) \<^bold>\<rightarrow> (belief_change :=\<^sub>C \<guillemotleft>bm\<guillemotright> :: bdi_act)"
term "(&phase = \<guillemotleft>p\<guillemotright>) && trans!(\<guillemotleft>perceive\<guillemotright>) \<^bold>\<rightarrow> believe?(belief_change) \<^bold>\<rightarrow> (Stop :: bdi_act)"
term "(phase := \<guillemotleft>s\<guillemotright>) :: bdi_act"
term "(phase := \<guillemotleft>s\<guillemotright>) \<^bold>\<rightarrow> Stop"
term "((phase := \<guillemotleft>s\<guillemotright>)) \<^bold>\<rightarrow> (Stop)"
term "(beliefs :=\<^sub>C upd\<^sub>u(&beliefs,&belief_change))"
term "(beliefs :=\<^sub>C upd\<^sub>u(&beliefs,&belief_change)) :: (bdi_state, bdi_ch) action"
term "(beliefs :=\<^sub>C upd\<^sub>u(&beliefs,&belief_change)) \<^bold>\<rightarrow> Stop"
term "((&phase = \<guillemotleft>p\<guillemotright>) && trans!(\<guillemotleft>perceive\<guillemotright>) \<^bold>\<rightarrow> believe?(bm)) :: (bdi_state, bdi_ch) action"
term "belief_change :=\<^sub>C \<guillemotleft>bm\<guillemotright> \<^bold>\<rightarrow> beliefs :=\<^sub>C upd\<^sub>u(beliefs,belief_change) \<^bold>\<rightarrow> Stop" (* :: (bdi_state, bdi_ch) action" *)

declare [[show_types]]

term "(&phase = \<guillemotleft>p\<guillemotright>) && trans!(\<guillemotleft>perceive\<guillemotright>) \<^bold>\<rightarrow> believe?(bm) \<^bold>\<rightarrow> (belief_change :=\<^sub>C \<guillemotleft>bm\<guillemotright> ;; beliefs :=\<^sub>C upd\<^sub>u(beliefs,belief_change) ;; Stop)"
term "belief_change :=\<^sub>C \<guillemotleft>bm\<guillemotright> \<^bold>\<rightarrow> beliefs :=\<^sub>C upd\<^sub>u(beliefs,belief_change) \<^bold>\<rightarrow> Stop"


term "doo!(snd(pl)) \<^bold>\<rightarrow> Stop"
term "(&phase = \<guillemotleft>p\<guillemotright>) && trans!(\<guillemotleft>perceive\<guillemotright>) \<^bold>\<rightarrow> believe?(bm) \<^bold>\<rightarrow> ((((belief_change :=\<^sub>C \<guillemotleft>bm\<guillemotright>) :: (bdi_state, bdi_ch) action) \<^bold>\<rightarrow> Stop) :: (bdi_state, bdi_ch) action)"
term "(&phase = \<guillemotleft>p\<guillemotright>) && trans!(\<guillemotleft>perceive\<guillemotright>) \<^bold>\<rightarrow> believe?(bm) \<^bold>\<rightarrow> ((belief_change :=\<^sub>C \<guillemotleft>bm\<guillemotright>) \<^bold>\<rightarrow> Stop)"
term "trans!(\<guillemotleft>perceive\<guillemotright>) \<^bold>\<rightarrow> believe?(bm) \<^bold>\<rightarrow> (belief_change :=\<^sub>C \<guillemotleft>bm\<guillemotright>) \<^bold>\<rightarrow> (beliefs :=\<^sub>C upd\<^sub>u(beliefs,belief_change)) \<^bold>\<rightarrow> Stop"
term "(&phase = \<guillemotleft>p\<guillemotright>) && trans!(\<guillemotleft>perceive\<guillemotright>) \<^bold>\<rightarrow> believe?(bm) \<^bold>\<rightarrow> (belief_change :=\<^sub>C \<guillemotleft>bm\<guillemotright> ;;  (beliefs :=\<^sub>C upd\<^sub>u(beliefs,belief_change) \<^bold>\<rightarrow> Stop)"
term "trans!(\<guillemotleft>perceive\<guillemotright>) \<^bold>\<rightarrow> (believe?(bm) \<^bold>\<rightarrow> (belief_change :=\<^sub>C \<guillemotleft>bm\<guillemotright>)) ;; (beliefs :=\<^sub>C upd\<^sub>u(beliefs,belief_change) \<^bold>\<rightarrow> Stop)"
term "(&phase = \<guillemotleft>p\<guillemotright>) && trans!(\<guillemotleft>perceive\<guillemotright>) \<^bold>\<rightarrow> believe?(bm) \<^bold>\<rightarrow> (\<lambda>bm. ((belief_change :=\<^sub>C \<guillemotleft>bm\<guillemotright>) \<^bold>\<rightarrow> Stop))"
term "(&phase = \<guillemotleft>p\<guillemotright>) && trans!(\<guillemotleft>perceive\<guillemotright>) \<^bold>\<rightarrow> believe?(bm) \<^bold>\<rightarrow> belief_change :=\<^sub>C \<guillemotleft>bm\<guillemotright> ;;  phase :=\<^sub>C \<guillemotleft>s\<guillemotright> \<^bold>\<rightarrow> beliefs :=\<^sub>C upd\<^sub>u(beliefs,belief_change) \<^bold>\<rightarrow> BDI"
term "(&phase = \<guillemotleft>p\<guillemotright>) && trans!(\<guillemotleft>perceive\<guillemotright>) \<^bold>\<rightarrow> believe?(bm) \<^bold>\<rightarrow> phase :=\<^sub>C \<guillemotleft>s\<guillemotright> \<^bold>\<rightarrow> (Stop:: bdi_act)"
term "(&phase = \<guillemotleft>p\<guillemotright>) && trans!(\<guillemotleft>perceive\<guillemotright>) \<^bold>\<rightarrow> believe?(bm) \<^bold>\<rightarrow> phase :=\<^sub>C \<guillemotleft>s\<guillemotright> \<^bold>\<rightarrow> beliefs :=\<^sub>C upd\<^sub>u(beliefs,bm) \<^bold>\<rightarrow> BDI"
term "(&phase = \<guillemotleft>p\<guillemotright>) && trans!(\<guillemotleft>perceive\<guillemotright>) \<^bold>\<rightarrow> believe?(bm) \<^bold>\<rightarrow> beliefs :=\<^sub>C upd\<^sub>u(beliefs,bm)) ;; BDI"
term "(&phase = \<guillemotleft>p\<guillemotright>) && (trans!(\<guillemotleft>terminate\<guillemotright>) \<^bold>\<rightarrow> endd!(\<guillemotleft>True\<guillemotright>) \<^bold>\<rightarrow> Stop)"
term "(&phase = \<guillemotleft>p\<guillemotright>) && (trans!(\<guillemotleft>perceive\<guillemotright>) \<^bold>\<rightarrow> believe?(bm) \<^bold>\<rightarrow> phase :=\<^sub>C \<guillemotleft>s\<guillemotright> \<^bold>\<rightarrow> (beliefs :=\<^sub>C upd\<^sub>u(beliefs,\<guillemotleft>bm\<guillemotright>)) \<^bold>\<rightarrow> BDI)"
term "(&phase = \<guillemotleft>s\<guillemotright>) && trans!(\<guillemotleft>select\<guillemotright>) \<^bold>\<rightarrow> (&phase = \<guillemotleft>e\<guillemotright>) \<^bold>\<rightarrow> (current_plan :=\<^sub>C plan(beliefs)) \<^bold>\<rightarrow> BDI"
(*
term "beliefs :=\<^sub>C upd(beliefs, \<guillemotleft>{stopped}\<guillemotright>)"
*)

(* :: "('\<beta>, '\<alpha>) bdi_act" *)
definition BDI where [rdes_def]:
"BDI = (
    (&phase = \<guillemotleft>p\<guillemotright>) && trans!(\<guillemotleft>terminate\<guillemotright>) \<^bold>\<rightarrow> endd!(\<guillemotleft>True\<guillemotright>) \<^bold>\<rightarrow> Stop
    \<box>
    (&phase = \<guillemotleft>p\<guillemotright>) && trans!(\<guillemotleft>perceive\<guillemotright>) \<^bold>\<rightarrow> believe?(bm) \<^bold>\<rightarrow> phase :=\<^sub>C \<guillemotleft>s\<guillemotright> \<^bold>\<rightarrow> (beliefs :=\<^sub>C upd\<^sub>u(beliefs,bm)) \<^bold>\<rightarrow> BDI
    \<box>
    (&phase = \<guillemotleft>s\<guillemotright>) && trans!(\<guillemotleft>select\<guillemotright>) \<^bold>\<rightarrow> (&phase = \<guillemotleft>e\<guillemotright>) \<^bold>\<rightarrow> (current_plan :=\<^sub>C plan(beliefs)) \<^bold>\<rightarrow> BDI
    \<box>
    (&phase = \<guillemotleft>e\<guillemotright>) && trans!(\<guillemotleft>execute\<guillemotright>) \<^bold>\<rightarrow> doo!(snd(pl)) \<^bold>\<rightarrow> phase :=\<^sub>C \<guillemotleft>p\<guillemotright> \<^bold>\<rightarrow> (beliefs :=\<^sub>C upd\<^sub>u(beliefs,bm)) \<^bold>\<rightarrow> BDI
)"

(* 
      \<box>
      &phase = p && trans!(perceive) \<rightarrow> beleive?bm \<rightarrow> $st \<rightarrow> BDI(upd(b,bm),pl,s)
      \<box>
      st==s & trans!select -> BDI(b,Select(b),e)
      \<box>
      st==e & trans!execute -> do.snd(pl) -> BDI(upd(b,fst(pl)),pl,p)
*)


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