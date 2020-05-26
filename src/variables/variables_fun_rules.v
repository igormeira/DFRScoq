Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.

Require Import variables.
Require Import util.
Require Import fun_util.

(* VNAME *)
Definition fun_rules_vname (vname : NAME) : bool :=
  negb (bstring_dec vname gc).
  
Definition bcomp_vname (v1 v2 : VNAME) : bool :=
  bstring_dec v1.(vname) v2.(vname).

(* SVARS *)
Definition beq_type (t1 t2 : TYPE) : bool :=
  match t1,t2 with
  | Tbool, Tbool  => true
  | Tnat, Tnat    => true
  | Tint, Tint    => true
  | _, _          => false
  end.
  
Definition fun_svar_valid_type (t : TYPE) : bool :=
  beq_type t Tbool || beq_type t Tint.
  
Fixpoint fun_svars_valid_type
(svars : list (VNAME * TYPE)) : bool :=
  match svars with
  | []          => true
  | (n,t) :: tl => if fun_svar_valid_type t
                   then fun_svars_valid_type tl
                   else false
  end.

Definition fun_rules_svars
(svars : list (VNAME * TYPE)) : bool :=
  bis_function (map (fun p => fst p) svars) bcomp_vname
  && negb (length svars =? 0)
  && fun_svars_valid_type svars.
  
(* STIMERS *)
Definition fun_stimer_valid_type (t : TYPE) : bool :=
  beq_type t Tnat.
  
Fixpoint fun_stimers_valid_type
(stimers : list (VNAME * TYPE)): bool :=
  match stimers with
  | []          => true
  | (n,t) :: tl => if fun_stimer_valid_type t
                   then fun_stimers_valid_type tl
                   else false
  end.

Definition fun_rules_stimers
(stimers : list (VNAME * TYPE)) : bool :=
  bis_function (map (fun p => fst p) stimers) bcomp_vname
  && fun_stimers_valid_type stimers.
  
(* DFRS_VARIABLES *)
Fixpoint bis_valid_disj (l1 l2 : list VNAME) : bool :=
  match l1 with
  | []     => true
  | h :: t => if bin_list h l2 bcomp_vname
              then false
              else bis_valid_disj t l2
  end.

Definition bdisjoint3
  (p : (list VNAME) * (list VNAME) * (list VNAME))
  : bool :=
    bis_valid_disj (fst3 p) (snd3 p)
    && bis_valid_disj (fst3 p) (trd3 p)
    && bis_valid_disj (snd3 p) (trd3 p).

Fixpoint bran_T {V : Type} (l : list (V * TYPE))
               (type : TYPE) : bool :=
  match l with
  | []     => true
  | h :: t => if beq_type (snd h) type
              then bran_T t type
              else false
  end.

Definition fun_rules_dfrs_variables
  (I O : SVARS) (T : STIMERS)
  (gcvar : (NAME * TYPE)) : bool :=
    bstring_dec (fst gcvar) gc
    && (beq_type (snd gcvar) Tnat)
    && (bdisjoint3
              (map (fun x : (VNAME * TYPE) => fst x) I.(svars),
               map (fun x : (VNAME * TYPE) => fst x) O.(svars),
               map (fun x : (VNAME * TYPE) => fst x) T.(stimers)))
    && bran_T T.(stimers) (snd gcvar).