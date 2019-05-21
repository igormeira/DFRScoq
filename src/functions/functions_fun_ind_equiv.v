Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.

Require Import functions.
Require Import functions_fun_rules.

(* EXPRESSION *)
Theorem theo_rules_disj :
  forall (lb : list BEXP),
    ind_rules_disj lb
    <-> fun_rules_disj lb = true.
Proof. Admitted.

(* ASSIGNMENT *)
Theorem theo_rules_asgmts :
  forall (l : list ASGMT),
    ind_rules_asgmts l
    <-> fun_rules_asgmts l = true.
Proof. Admitted.

(* FUNCTION *)
Theorem theo_rules_function :
  forall (l : list (EXP * EXP * ASGMTS * REQUIREMENT) ),
    ind_rules_function l
    <-> fun_rules_function l = true.
Proof. Admitted.

Theorem theo_rules_dfrs_functions :
  forall (lf : list FUNCTION),
    ind_rules_dfrs_functions lf
    <-> fun_rules_dfrs_functions lf = true.
Proof. Admitted.