Require Import Coq.Lists.List.
Import ListNotations.

Require Import variables.
Require Import state.
Require Import functions.

(* S_DFRS *)

Fixpoint check_function_entries
(l : list (EXP * EXP * ASGMTS * REQUIREMENT))
(IO T OT : list (VNAME * TYPE)) : Prop :=
    match l with
    | []     => True
    | h :: t => var_consistent_exp (fst (fst (fst h))) IO T
                /\ var_consistent_exp (snd (fst (fst h))) T T
                /\ well_typed_asgmts (snd (fst h)) OT
                /\ check_function_entries t IO T OT
    end.

Fixpoint check_functions (lf : list FUNCTION) 
  (IO T OT : list (VNAME * TYPE)) : Prop :=
    match lf with
    | []     => True
    | h :: t => check_function_entries h.(function) IO T OT
                /\ check_functions t IO T OT
    end.

Definition ind_rules_s_dfrs
(vars : DFRS_VARIABLES) (initial : DFRS_INITIAL_STATE)
(funs : DFRS_FUNCTIONS) : Prop :=
  let IO := vars.(I).(svars) ++ vars.(O).(svars) in
  let OT := vars.(O).(svars) ++ vars.(T).(stimers) in
  let IOT := IO ++ vars.(T).(stimers) in
  let IOTgcvar := [vars.(gcvar)] ++
                  map (fun x => ((fst x).(vname), snd x)) IOT
  in
    (well_typed_state initial.(s0) IOTgcvar)
    /\ (check_functions funs.(F) IO vars.(T).(stimers) OT).

Record s_DFRS : Set := mkS_DFRS {
  s_dfrs_variables     : DFRS_VARIABLES ;
  s_dfrs_initial_state : DFRS_INITIAL_STATE ;
  s_dfrs_functions     : DFRS_FUNCTIONS
  
  ; rules_s_dfrs : ind_rules_s_dfrs
                      s_dfrs_variables
                      s_dfrs_initial_state
                      s_dfrs_functions
}.