Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Require Import Bool.

Require Export util.
Require Export fun_util.
Require Export variables.
Require Export variables_fun_rules.
Require Export state.
Require Export state_fun_rules.
Require Export functions.
Require Export trans_rel.

Local Open Scope string_scope.



(* TODO: Really necessary? *)
Definition beq_delay (d1 d2 : DELAY) : bool :=
  if beq_nat (delayValue d1) (delayValue d2)
  then true
  else false.

Definition bwell_typed_function_transition (label : TRANS_LABEL) 
  (O T : list (VNAME * TYPE)) : bool :=
  let
    dom_O := map (fun x : (VNAME * TYPE) => (fst x)) O
  in
  let
    dom_T := map (fun x : (VNAME * TYPE) => (fst x)) T
  in
    if blist_in_list (dom_fun [label]) (dom_O ++ dom_T)
       (fun (v v' : VNAME)
          => bstring_dec v.(vname)
                         v'.(vname))
    then true
    else false.

Definition bwell_typed_delay_transition (label : TRANS_LABEL) 
  (I : list (VNAME * TYPE)) : bool :=
  let
    dom_I := map (fun x : (VNAME * TYPE) => (fst x).(vname)) I
  in
  let
    dom_D := dom_del label
  in
    if ((List.length dom_D) =? (List.length dom_I))
       &&
       blist_in_list dom_D dom_I
          (fun (v v' : NAME)
            => bstring_dec v v')
    then true
    else false.

(* ranDiscrete already tests if label is a delay *)
Definition branDiscrete (label : TRANS_LABEL) : bool :=
  match label with
  | func _ => false
  | del  a => match (fst a) with
              | discrete _ => true
              end
  end.

Definition bclock_compatible_transition (label : TRANS_LABEL) 
  (gcvar : (NAME * TYPE)) : bool :=
  if (branDiscrete label) 
  then (beq_type (snd gcvar) Tnat) 
  else true.

(** well_typed_transitions *)
Definition branDel (label : TRANS_LABEL) : bool :=
  match label with
  | del _ => true
  | _     => false
  end.

Definition branFun (label : TRANS_LABEL) : bool :=
  match label with
  | func _ => true
  | _      => false
  end.

Definition bwell_typed_transition (label : TRANS_LABEL) 
  (I O T : list (VNAME * TYPE)) (gcvar : (NAME * TYPE)) : bool :=
  (if branFun label
   then bwell_typed_function_transition label O T else true)
  && 
  (if branDel label 
   then bwell_typed_delay_transition label I
   else true)
  &&
  bclock_compatible_transition label gcvar.

(** DFRS_TRANSITION_RELATION *)

Fixpoint bcheck_same_state_start (trans : list TRANS) (tr : TRANS) : bool :=
  match trans with
  | []     => true
  | h :: t => if beq_state (fst3 h.(STS)) 
                           (fst3 tr.(STS))
              then (branFun (snd3 h.(STS)) && branFun (snd3 tr.(STS))) 
                    || 
                   (branDel (snd3 h.(STS)) && branDel (snd3 tr.(STS)))
              else bcheck_same_state_start t tr
  end.

Fixpoint bis_valid_trans (trans : list TRANS) : bool :=
  match trans with
  | []     => true
  | h :: t => if negb (beq_state (fst3 h.(STS)) 
                                 (trd3 h.(STS)))
                 &&
                 fun_rules_state (fst3 h.(STS)).(state) (*TEST STATE*)
                 &&
                 fun_rules_state (trd3 h.(STS)).(state) (*TEST STATE*)
                 &&
                 bcheck_same_state_start t h
              then bis_valid_trans t
              else false
  end.

(** rules_DFRS_TRANSITION_RELATION *)
Definition fun_rules_dfrs_trans_rel (tr : TRANSREL) : bool :=
  bis_valid_trans tr.(transrel).


Local Close Scope string_scope.