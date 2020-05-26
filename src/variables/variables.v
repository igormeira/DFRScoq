Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.

Require Import util.

(* VNAME *)
Definition NAME := string.

Local Open Scope string.
Definition gc : NAME := "gc".
Local Close Scope string.

Definition ind_rules_vname (vname : NAME) : Prop :=
  ~ string_dec vname gc.

Record VNAME : Set := mkVNAME {
  vname : NAME
  
  ; rules_vname : ind_rules_vname vname
}.

Definition comp_vname (v1 v2 : VNAME) : Prop :=
  string_dec v1.(vname) v2.(vname).

(* SVARS *)
Inductive TYPE := Tbool | Tint | Tnat.

Definition eq_type (t1 t2 : TYPE) : Prop :=
  match t1,t2 with
  | Tbool, Tbool  => True
  | Tnat, Tnat    => True
  | Tint, Tint    => True
  | _, _          => False
  end.
  
Definition ind_svar_valid_type (t : TYPE) : Prop :=
  eq_type t Tbool \/ eq_type t Tint.
  
Fixpoint ind_svars_valid_type
(svars : list (VNAME * TYPE)) : Prop :=
  match svars with
  | []          => True
  | (n,t) :: tl => ind_svar_valid_type t
                   /\ ind_svars_valid_type tl
  end.

Definition ind_rules_svars
(svars : list (VNAME * TYPE)) : Prop :=
  is_function (map (fun p => fst p) svars) comp_vname
  /\ ~ (length svars = 0)
  /\ ind_svars_valid_type svars.

Record SVARS : Set := mkSVARS {
  svars : list (VNAME * TYPE)
  
  ; rules_svars : ind_rules_svars svars
}.

(* STIMERS *)
Definition ind_stimer_valid_type (t : TYPE) : Prop :=
  eq_type t Tnat.
  
Fixpoint ind_stimers_valid_type
(stimers : list (VNAME * TYPE)): Prop :=
  match stimers with
  | []          => True
  | (n,t) :: tl => ind_stimer_valid_type t
                   /\ ind_stimers_valid_type tl
  end.

Definition ind_rules_stimers
(stimers : list (VNAME * TYPE)) : Prop :=
  is_function (map (fun p => fst p) stimers) comp_vname
  /\ ind_stimers_valid_type stimers.

Record STIMERS : Set := mkSTIMERS {
  stimers : list (VNAME * TYPE)
  
  ; rules_stimers : ind_rules_stimers stimers
}.

(* DFRS_VARIABLES *)
Fixpoint is_valid_disj (l1 l2 : list VNAME) : Prop :=
  match l1 with
  | []     => True
  | h :: t => ~ in_list h l2 comp_vname
              /\ is_valid_disj t l2
  end.

Definition disjoint3
  (p : (list VNAME) * (list VNAME) * (list VNAME))
  : Prop :=
    is_valid_disj (fst3 p) (snd3 p)
    /\ is_valid_disj (fst3 p) (trd3 p)
    /\ is_valid_disj (snd3 p) (trd3 p).

Fixpoint ran_T {V : Type} (l : list (V * TYPE))
               (type : TYPE) : Prop :=
  match l with
  | []     => True
  | h :: t => eq_type (snd h) type /\ ran_T t type
  end.
  
Definition ind_rules_dfrs_variables
  (I O : SVARS) (T : STIMERS)
  (gcvar : (NAME * TYPE)) : Prop :=
    string_dec (fst gcvar) gc
    /\ (eq_type (snd gcvar) Tnat)
    /\ (disjoint3
              (map (fun x : (VNAME * TYPE) => fst x) I.(svars),
               map (fun x : (VNAME * TYPE) => fst x) O.(svars),
               map (fun x : (VNAME * TYPE) => fst x) T.(stimers)))
    /\ ran_T T.(stimers) (snd gcvar).

Record DFRS_VARIABLES : Set := mkDFRS_VARIABLES {
  I : SVARS ;
  O : SVARS ; 
  T : STIMERS ;
  gcvar : NAME * TYPE
  
  ; rules_dfrs_variables : ind_rules_dfrs_variables I O T gcvar
}.