Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Bool.

Require Import variables.
Require Import util.
Require Import fun_util.

(* VALUE *)
Inductive VALUE : Type :=
  | b : bool -> VALUE
  | i : Z -> VALUE
  | n : nat -> VALUE.
  
Definition eq_value (v1 v2 : VALUE) : Prop :=
  match v1,v2 with
  | b t1, b t2 => eq t1 t2
  | i t1, i t2 => Z.eq t1 t2
  | n t1, n t2 => t1 = t2
  | _, _ => False
  end.

(* STATE *)
Definition ind_rules_state
(s : list (NAME * (VALUE * VALUE))) : Prop :=
  is_function
    (map (fun var : (NAME * (VALUE * VALUE)) => fst var) s)
    string_dec.

Record STATE : Set := mkSTATE {
  state : list (NAME * (VALUE * VALUE))
  
  ; rules_state : ind_rules_state state
}.

Definition previous_values (s : STATE) : list (NAME * VALUE) :=
  map (fun x => (fst x, (fst (snd x)))) s.(state).

Definition current_values (s : STATE) : list (NAME * VALUE) :=
  map (fun x => (fst x, (snd (snd x)))) s.(state).

Fixpoint find_var_state
(n : NAME) (l : list (NAME * (VALUE * VALUE)))
: option (NAME * (VALUE * VALUE)) :=
  match l with
  | []     => None
  | h :: t => if bstring_dec (fst h) n
              then Some h else find_var_state n t
  end.

Definition is_valid_value
(v : VALUE) (t : TYPE) : Prop :=
  match v with
  | b _ => eq_type t Tbool
  | i _ => eq_type t Tint
  | n _ => eq_type t Tnat
  end.

Definition well_typed_var
(s : STATE) (n : NAME) (t : TYPE) : Prop :=
  let v := find_var_state n s.(state) in
    match v with
    | None   => False
    | Some p => (is_valid_value (fst (snd p)) t)
                /\ (is_valid_value (snd (snd p)) t)
    end.

Fixpoint well_typed_state_var (s:STATE)
(l: list (NAME * TYPE)) : Prop :=
    match l with
    | []     => True
    | h :: t => well_typed_var s (fst h) (snd h)
                /\ well_typed_state_var s t
    end.

Definition well_typed_state (s : STATE)
(l : list (NAME * TYPE)) : Prop :=
  let dom_s := map (fun x => fst x) s.(state) in
  let dom_l := map (fun x => fst x) l in
    same_list dom_s dom_l string_dec
    /\ well_typed_state_var s l.

Definition eq_state_element
(e1 e2 : (NAME * (VALUE * VALUE))) : Prop :=
  string_dec (fst e1) (fst e2)
  /\ eq_value (fst (snd e1)) (fst (snd e2))
  /\ eq_value (snd (snd e1)) (snd (snd e2)).

Fixpoint eq_state_elements (s1 s2 : list (NAME * (VALUE * VALUE))) : Prop :=
  match s1, s2 with
  | []      , []       => True
  | []      , _        => False
  | _       , []       => False
  | h1 :: t1, h2 :: t2 => eq_state_element h1 h2
  end.

Definition eq_state (s1 s2 : STATE) : Prop :=
  same_list s1.(state) s2.(state) eq_state_element.

(* DFRS_INITIAL_STATE *)
Record DFRS_INITIAL_STATE : Set := mkDFRS_INITIAL_STATE {
  s0 : STATE
}.