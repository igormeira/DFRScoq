Require Import Coq.Strings.String.
Require Import fun_util.
Require Import util.

Theorem theo_string_dec :
  forall (s1 s2 : string),
    string_dec s1 s2 <->
    bstring_dec s1 s2 = true.
Proof.
  intros. unfold string_dec, bstring_dec.
  destruct (String.string_dec s1 s2) ; split ;
  (intro H' ; try reflexivity) ;
  inversion H'.
Qed.

Theorem theo_all_true :
  forall (T : Type) (l : list T)
    (f1 : T -> Prop) (f2 : T -> bool),
    (forall (t : T), f1 t <-> f2 t = true)
    -> (all_true f1 l <-> ball_true f2 l = true).
Proof.
  intros. split.
  - induction l.
    + simpl. intro H'. reflexivity.
    + simpl. intro H'. destruct H' as [H1 H2].
      rewrite H in H1. rewrite H1.
      apply IHl. apply H2.
  - induction l.
    + simpl. intro H'. reflexivity.
    + simpl. intro H'. destruct (f2 a) eqn:H''.
      * split. 
        { rewrite <- H in H''. apply H''. }
        { apply IHl. apply H'. }
      * inversion  H'.
Qed.

Lemma lemm_in_list :
  forall (T1 T2 : Type)
         (x : T1) (l : list T2)
         (comp : T1 -> T2 -> Prop)
         (bcomp : T1 -> T2 -> bool),
    (forall (v1 : T1) (v2 : T2),
      comp v1 v2 <-> bcomp v1 v2 = true)
    -> (in_list x l comp <->
        bin_list x l bcomp = true).
Proof.
  intros. split.
  - induction l.
    + simpl. intro H'. inversion H'.
    + simpl. intro H'. destruct H' as [H' | H'].
      * apply H in H'. rewrite H'. reflexivity.
      * apply IHl in H'. destruct (bcomp x a).
        { reflexivity. }
        { apply H'. }
  - induction l.
    + simpl. intro H'. inversion H'.
    + simpl. intro H'. destruct (bcomp x a) eqn:H''.
      * left. apply H in H''. apply H''.
      * right. apply IHl. apply H'.
Qed.

Theorem lemm_list_in_list :
  forall (T : Type) (l1 l2 : list T)
         (comp : T -> T -> Prop)
         (bcomp : T -> T -> bool),
    (forall (v1 v2 : T), comp v1 v2 <-> bcomp v1 v2 = true)
    -> (list_in_list l1 l2 comp <-> blist_in_list l1 l2 bcomp = true).
Proof.
  intros. split.
  - induction l1.
    + simpl. intros. reflexivity.
    + intro H1. simpl in H1. destruct H1 as [H1 H2].
      simpl. rewrite lemm_in_list in H1. rewrite H1.
      * apply IHl1. apply H2.
      * apply H.
  - induction l1.
    + simpl. intros. reflexivity.
    + intro H1. simpl in H1. simpl. split.
      destruct (bin_list a l2 bcomp) eqn:H2.
      * rewrite lemm_in_list.
        { apply H2. }
        { apply H. }
      * inversion H1.
      * apply IHl1. destruct (bin_list a l2 bcomp) eqn:H2.
        { apply H1. }
        { inversion H1. }
Qed.

Theorem lemm_same_list :
  forall (T : Type) (l1 l2 : list T)
         (comp : T -> T -> Prop)
         (bcomp : T -> T -> bool),
    (forall (v1 v2 : T), comp v1 v2 <-> bcomp v1 v2 = true)
    -> (same_list l1 l2 comp <-> bsame_list l1 l2 bcomp = true).
Proof.
  intros. split.
  - induction l1.
    + simpl. intro H'. destruct H'.
      * rewrite lemm_list_in_list in H1.
        { rewrite H1. reflexivity. }
        { intros. apply H. }
    + simpl. intro H'. destruct H'. destruct H0.
      rewrite lemm_list_in_list in H2.
      rewrite lemm_in_list in H0.
      * rewrite H0. rewrite H2. rewrite lemm_list_in_list in H1.
        { rewrite H1. reflexivity. }
        { apply H. }
      * apply H.
      * apply H.
  - induction l1.
    + simpl. intro. split.
      * reflexivity.
      * rewrite lemm_list_in_list. rewrite H0. reflexivity.
        apply H.
    + simpl. intro. split.
      * split.
        { destruct (bin_list a l2 bcomp) eqn:H1.
          - rewrite lemm_in_list. rewrite H1. reflexivity.
            + apply H.
          - rewrite lemm_in_list. simpl in H0. inversion H0.
            + apply H. }
        { destruct (blist_in_list l1 l2 bcomp) eqn:H1.
          - destruct (bin_list a l2 bcomp).
            + rewrite lemm_list_in_list. 
              * rewrite H1. reflexivity.
              * apply H.
            + rewrite lemm_list_in_list. 
              * rewrite H1. reflexivity.
              * apply H.
          - destruct (bin_list a l2 bcomp).
            + simpl in H0. inversion H0.
            + simpl in H0. inversion H0. }
      * destruct (blist_in_list l2 (a :: l1) bcomp) eqn:H1.
        { destruct (bin_list a l2 bcomp).
          - rewrite lemm_list_in_list.
            + rewrite H1. reflexivity.
            + apply H.
          - simpl in H0. inversion H0. }
        { destruct (bin_list a l2 bcomp).
          - destruct (blist_in_list l1 l2 bcomp).
            + simpl in H0. inversion H0.
            + simpl in H0. inversion H0.
          - simpl in H0. inversion H0. }
Qed.

Theorem theo_is_function :
  forall (T : Type) (l : list T)
         (comp : T -> T -> Prop)
         (bcomp : T -> T -> bool),
    (forall (v1 v2 : T), comp v1 v2 <-> bcomp v1 v2 = true)
    -> (is_function l comp <-> bis_function l bcomp = true).
Proof.
  intros. split.
  - induction l.
    + simpl. intro H'. reflexivity.
    + simpl. intro H'. destruct H' as [H1 H2].
      destruct (bin_list a l bcomp) eqn:H3.
      * rewrite <- lemm_in_list in H3.
        unfold not in H1. apply H1 in H3.
        inversion H3. apply H.
      * apply IHl. apply H2.
  - induction l.
    + simpl. intro H'. reflexivity.
    + simpl. intro H'. destruct (bin_list a l bcomp) eqn:H2.
      * inversion H'.
      * split.
        { unfold not. intro H''.
          rewrite lemm_in_list in H''.
          rewrite H2 in H''. inversion H''.
          apply H. }
        { apply IHl. apply H'. }
Qed.