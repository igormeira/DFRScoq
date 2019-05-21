Require Import Coq.Lists.List.
Import ListNotations.

Require Import variables.
Require Import state.
Require Import state_fun_rules.
Require Import functions.
Require Import functions_fun_rules.

(* S_DFRS *)

Fixpoint bcheck_function_entries
(l : list (EXP * EXP * ASGMTS * REQUIREMENT))
(IO T OT : list (VNAME * TYPE)) : bool :=
    match l with
    | []     => true
    | h :: t => bvar_consistent_exp (fst (fst (fst h))) IO T
                && bvar_consistent_exp (snd (fst (fst h))) T T
                && bwell_typed_asgmts (snd (fst h)) OT
                && bcheck_function_entries t IO T OT
    end.

Fixpoint bcheck_functions (lf : list FUNCTION) 
  (IO T OT : list (VNAME * TYPE)) : bool :=
    match lf with
    | []     => true
    | h :: t => bcheck_function_entries h.(function) IO T OT
                && bcheck_functions t IO T OT
    end.

Definition fun_rules_s_dfrs
(vars : DFRS_VARIABLES) (initial : DFRS_INITIAL_STATE)
(funs : DFRS_FUNCTIONS) : bool :=
  let IO := vars.(I).(svars) ++ vars.(O).(svars) in
  let OT := vars.(O).(svars) ++ vars.(T).(stimers) in
  let IOT := IO ++ vars.(T).(stimers) in
  let IOTgcvar := [vars.(gcvar)] ++
                  map (fun x => ((fst x).(vname), snd x)) IOT
  in
    (bwell_typed_state initial.(s0) IOTgcvar)
    && (bcheck_functions funs.(F) IO vars.(T).(stimers) OT).