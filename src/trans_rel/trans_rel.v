Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Require Import Bool.

Require Export util.
Require Export fun_util.
Require Export variables.
Require Export states.
Require Export states_fun_rules.
Require Export functions.

Local Open Scope string_scope.

Inductive DELAY : Type :=
  | discrete : nat -> DELAY.

(* TODO: Really necessary? *)
Definition delayValue (d : DELAY) : nat :=
  match d with
  | discrete natural => natural
  end.

Inductive TRANS_LABEL : Type :=
  | func  : (ASGMTS * REQUIREMENT) -> TRANS_LABEL
  | del   : (DELAY * ASGMTS) -> TRANS_LABEL.

Record TRANS : Set := mkTRANS {
  STS : STATE * TRANS_LABEL * STATE
}.

Record TRANSREL : Set := mkTRANSREL {
  transrel : list TRANS;
}.

(** functionTransition *)
Definition functionTransition (label : TRANS_LABEL) : option (ASGMTS * REQUIREMENT) :=
  match label with
  | func a => Some a
  | _      => None
  end.

(** delayTransition *)
Definition delayTransition (label : TRANS_LABEL) : option (DELAY * ASGMTS) :=
  match label with
  | del a => Some a
  | _     => None
  end.

(** well_typed_function_transition *)
Fixpoint dom_fun (label : list TRANS_LABEL) : list VNAME :=
  match label with
  | []     => []
  | h :: t => match h with
              | func a => match ((fst a).(asgmts)) with
                          | []      => []
                          | x :: xs => (fst x.(asgmt)) :: dom_fun t
                          end
              | del  _ => dom_fun t
              end
  end.

Definition well_typed_function_transition (label : TRANS_LABEL) 
  (O T : list (VNAME * TYPE)) : Prop :=
  let
    dom_O := map (fun x : (VNAME * TYPE) => (fst x)) O
  in
  let
    dom_T := map (fun x : (VNAME * TYPE) => (fst x)) T
  in
    list_in_list (dom_fun [label]) (dom_O ++ dom_T)
     (fun (v v' : VNAME)
        => string_dec v.(vname)
                       v'.(vname)).

(** well_typed_delay_transition *)
Fixpoint dom_del (label : TRANS_LABEL) : list NAME :=
  match label with
  | func _ => []
  | del  a => let
                ASGMTS := (snd a).(asgmts)
              in
              (map (fun x : (VNAME * VALUE) 
                    => (fst x).(vname)) 
                    (map (fun a : ASGMT
                          => a.(asgmt)) ASGMTS))
  end.

Definition well_typed_delay_transition (label : TRANS_LABEL) 
  (I : list (VNAME * TYPE)) : Prop :=
  let
    dom_I := map (fun x : (VNAME * TYPE) => (fst x).(vname)) I
  in
  let
    dom_D := dom_del label
  in
    ((List.length dom_D) = (List.length dom_I))
    /\
    (list_in_list dom_D dom_I
        (fun (v v' : NAME)
          => string_dec v v')).

(* ranDiscrete already tests if label is a delay *)
Definition ranDiscrete (label : TRANS_LABEL) : Prop :=
  match label with
  | func _ => False
  | del  a => match (fst a) with
              | discrete _ => True
              end
  end.

Definition clock_compatible_transition (label : TRANS_LABEL) 
  (gcvar : (NAME * TYPE)) : Prop :=
  (ranDiscrete label) -> (eq_type (snd gcvar) Tnat).

(** well_typed_transitions *)
Definition ranDel (label : TRANS_LABEL) : Prop :=
  match label with
  | del _ => True
  | _     => False
  end.

Definition ranFun (label : TRANS_LABEL) : Prop :=
  match label with
  | func _ => True
  | _      => False
  end.

Definition well_typed_transition (label : TRANS_LABEL) 
  (I O T : list (VNAME * TYPE)) (gcvar : (NAME * TYPE)) : Prop :=
  (ranFun label -> well_typed_function_transition label O T)
  /\
  (ranDel label -> well_typed_delay_transition label I)
  /\
  clock_compatible_transition label gcvar.

(** DFRS_TRANSITION_RELATION *)
Fixpoint check_same_state_start (trans : list TRANS) (tr : TRANS) : Prop :=
  match trans with
  | []     => True
  | h :: t => if beq_state (fst3 h.(STS)) 
                           (fst3 tr.(STS))
              then (ranFun (snd3 h.(STS)) /\ ranFun (snd3 tr.(STS))) 
                    \/ 
                   (ranDel (snd3 h.(STS)) /\ ranDel (snd3 tr.(STS)))
              else check_same_state_start t tr
  end.

Fixpoint is_valid_trans (trans : list TRANS) : Prop :=
  match trans with
  | []     => True
  | h :: t => (~(eq_state (fst3 h.(STS)) 
                          (trd3 h.(STS)))
               /\
               ind_rules_state (fst3 h.(STS)).(state) (*TEST STATE*)
               /\
               ind_rules_state (trd3 h.(STS)).(state) (*TEST STATE*)
               /\
               check_same_state_start t h)
               /\
               is_valid_trans t
  end.

(** rules_DFRS_TRANSITION_RELATION *)
Definition ind_rules_dfrs_trans_rel (tr : TRANSREL) : Prop :=
  is_valid_trans tr.(transrel).

Record DFRS_TRANSITION_RELATION := mkDFRSTRANSITIONREL {
  TR : TRANSREL;
  rules_dfrs_trans_rel : ind_rules_dfrs_trans_rel TR
}.

Local Close Scope string_scope.