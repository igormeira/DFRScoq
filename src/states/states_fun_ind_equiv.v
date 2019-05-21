Require Import states.
Require Import states_fun_rules.

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