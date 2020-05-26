Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.

Definition bstring_dec (s1 s2 : string) : bool :=
  if string_dec s1 s2 then true else false.

Fixpoint ball_true {T : Type} (f : T -> bool) (l : list T) : bool :=
  match l with
  | []      => true
  | h :: tl => if f h then ball_true f tl
               else false
  end.

Fixpoint bin_list {T1 T2 : Type} (x : T1) (l : list T2)
    (comp : T1 -> T2 -> bool) : bool :=
  match l with  
  | []      => false
  | h :: tl => if comp x h then true
               else bin_list x tl comp
  end.
  
Fixpoint blist_in_list {T : Type} (l1 l2 : list T)
    (comp : T -> T -> bool) : bool :=
  match l1 with
  | []       => true
  | h1 :: t1 => if bin_list h1 l2 comp
                then blist_in_list t1 l2 comp
                else false
  end.
 
Fixpoint bsame_list {T : Type} (l1 l2 : list T)
    (comp : T -> T -> bool) : bool :=
  blist_in_list l1 l2 comp
  && blist_in_list l2 l1 comp.

Fixpoint bis_function {T : Type} (l : list T)
    (comp : T -> T -> bool) : bool :=
  match l with
  | []     => true
  | h :: t => if bin_list h t comp then false
              else bis_function t comp
  end.