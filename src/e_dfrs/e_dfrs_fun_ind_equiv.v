Require Import variables.
Require Import states.
Require Import trans_rel.
Require Import e_dfrs.
Require Import e_dfrs_fun_rules.

(* E_DFRS *)
Theorem theo_rules_e_dfrs :
  forall (vars : DFRS_VARIABLES) (states : DFRS_STATES)
         (trs : DFRS_TRANSITION_RELATION),
    ind_rules_e_dfrs vars states trs
    <-> fun_rules_e_dfrs vars states trs = true.
Proof. Admitted.