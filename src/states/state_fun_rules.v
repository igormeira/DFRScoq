Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Bool.

Require Import state.
Require Import variables.
Require Import variables_fun_rules.
Require Import fun_util.

(* VALUE *)
Definition beq_value (v1 v2 : VALUE) : bool :=
  match v1,v2 with
  | b t1, b t2 => eqb t1 t2
  | i t1, i t2 => Z.eqb t1 t2
  | n t1, n t2 => t1 =? t2
  | _, _ => false
  end.

(* STATE *)
Definition fun_rules_state
(s : list (NAME * (VALUE * VALUE))) : bool :=
  bis_function
    (map (fun var : (NAME * (VALUE * VALUE)) => fst var) s)
    bstring_dec.
    
Definition bis_valid_value
(v : VALUE) (t : TYPE) : bool :=
  match v with
  | b _ => beq_type t Tbool
  | i _ => beq_type t Tint
  | n _ => beq_type t Tnat
  end.

Definition bwell_typed_var
(s : STATE) (n : NAME) (t : TYPE) : bool :=
  let v := find_var_state n s.(state) in
    match v with
    | None   => false
    | Some p => (bis_valid_value (fst (snd p)) t)
                && (bis_valid_value (snd (snd p)) t)
    end.

Fixpoint bwell_typed_state_var (s:STATE)
(l: list (NAME * TYPE)) : bool :=
    match l with
    | []     => true
    | h :: t => if bwell_typed_var s (fst h) (snd h)
                then bwell_typed_state_var s t
                else false
    end.

Definition bwell_typed_state (s : STATE)
(l : list (NAME * TYPE)) : bool :=
  let dom_s := map (fun x => fst x) s.(state) in
  let dom_l := map (fun x => fst x) l in
    bsame_list dom_s dom_l bstring_dec
    && bwell_typed_state_var s l.

Definition beq_state_element
(e1 e2 : (NAME * (VALUE * VALUE))) : bool :=
  bstring_dec (fst e1) (fst e2)
  && beq_value (fst (snd e1)) (fst (snd e2))
  && beq_value (snd (snd e1)) (snd (snd e2)).

Fixpoint beq_state_elements (s1 s2 : list (NAME * (VALUE * VALUE))) : bool :=
  match s1, s2 with
  | []      , []       => true
  | []      , _        => false
  | _       , []       => false
  | h1 :: t1, h2 :: t2 => beq_state_element h1 h2
  end.

Definition beq_state (s1 s2 : STATE) : bool :=
  bsame_list s1.(state) s2.(state) beq_state_element.