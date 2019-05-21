Require Import variables.
Require Import state.
Require Import functions.
Require Import s_dfrs.
Require Import s_dfrs_fun_rules.

(* S_DFRS *)

Theorem theo_rules_s_dfrs :
  forall (vars : DFRS_VARIABLES) (initial : DFRS_INITIAL_STATE)
         (funs : DFRS_FUNCTIONS),
    ind_rules_s_dfrs vars initial funs
    <-> fun_rules_s_dfrs vars initial funs = true.
Proof. Admitted.