Require Import states.
Require Import states_fun_rules.

(* STATE *)
Theorem theo_rules_state :
  forall (s : list (NAME * (VALUE * VALUE))),
    ind_rules_state s
    <-> fun_rules_state s = true.
Proof. Admitted.

(* STATES *)
Theorem theo_rules_states :
  forall (ls : list STATE),
    ind_rules_states ls
    <-> fun_rules_states ls = true.
Proof. Admitted.

(* DFRS_TRANSITION_RELATION *)
Theorem theo_rules_dfrs_states :
  forall (s0 : STATE) (states : STATES),
    ind_rules_dfrs_states s0 states
    <-> fun_rules_dfrs_states s0 states = true.
Proof. Admitted.