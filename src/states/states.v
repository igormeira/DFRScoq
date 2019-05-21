Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Require Import Bool.

Require Export util.
Require Export variables.
Require Export state.
Require Export functions.

Local Open Scope string_scope.

Definition ind_rules_states (l : list STATE) : Prop :=
  0 < List.length l.

Record STATES : Set := mkSTATES {
  states : list STATE;
  rules_states : ind_rules_states states
}.

(** Rules DFRS_STATES *)
Definition ind_rules_dfrs_states
  (s : STATE) (ss : STATES) : Prop :=
    in_list s ss.(states)
          (fun (s1 s2 : STATE) =>
              eq_state s1 s2).

Record DFRS_STATES : Set := mkDFRSSTATES {
  States  : STATES;
  s0'     : STATE;
  rules_dfrs_states : ind_rules_dfrs_states s0' States
}.

Local Close Scope string_scope.