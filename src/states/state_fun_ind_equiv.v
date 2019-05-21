Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Import ListNotations.

Require Import state.
Require Import state_fun_rules.
Require Import variables.
Require Import util.
Require Import fun_util.

(* VALUE *)

(* STATE *)
Theorem theo_rules_state :
  forall (s : list (NAME * (VALUE * VALUE))),
    ind_rules_state s
    <-> fun_rules_state s = true.
Proof. Admitted.