Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.

Definition string_dec (s1 s2 : string) : Prop :=
  if string_dec s1 s2 then True else False.

(* Not used *)
Fixpoint all_true {T : Type} (f : T -> Prop) (l : list T): Prop :=
  match l with
  | []      => True
  | h :: tl => f h /\ all_true f tl
  end.

Fixpoint in_list {T1 T2 : Type} (x : T1) (l : list T2)
    (comp : T1 -> T2 -> Prop) : Prop :=
  match l with
  | []      => False
  | h :: tl => comp x h \/ in_list x tl comp
  end.
  
Fixpoint list_in_list {T : Type} (l1 l2 : list T)
    (comp : T -> T -> Prop) : Prop :=
  match l1 with
  | []       => True
  | h1 :: t1 => in_list h1 l2 comp
                /\ list_in_list t1 l2 comp
  end.

Fixpoint same_list {T : Type} (l1 l2 : list T)
    (comp : T -> T -> Prop) : Prop :=
  list_in_list l1 l2 comp
  /\ list_in_list l2 l1 comp.

Fixpoint is_function {T : Type} (l : list T)
    (comp : T -> T -> Prop) : Prop :=
  match l with
  | []     => True
  | h :: t => ~ in_list h t comp /\ is_function t comp
  end.

Definition fst3 {A : Type} {B : Type} {C : Type}
  (p:A * B * C) : A := (fst (fst p)).

Definition snd3 {A : Type} {B : Type} {C : Type}
  (p:A * B * C) : B := (snd (fst p)).

Definition trd3 {A : Type} {B : Type} {C : Type}
  (p:A * B * C) : C := snd p.