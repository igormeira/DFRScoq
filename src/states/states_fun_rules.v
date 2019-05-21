Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Require Import Bool.

Require Export util.
Require Export fun_util.
Require Export variables.
Require Export state.
Require Export state_fun_rules.
Require Export functions.
Require Export states.

Local Open Scope string_scope.

Definition fun_rules_states (l : list STATE) : bool :=
  0 <? List.length l.

(** Rules DFRS_STATES *)
Definition fun_rules_dfrs_states
  (s : STATE) (ss : STATES) : bool :=
    bin_list s ss.(states)
          (fun (s1 s2 : STATE) =>
              beq_state s1 s2).

Local Close Scope string_scope.