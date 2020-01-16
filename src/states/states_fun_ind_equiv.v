Require Import states.
Require Import states_fun_rules.
Require Import util_fun_ind_equiv.

Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Bool.
Require Import Coq.ZArith.ZArith.

(* STATE *)
Theorem lemm_eq_value :
  forall (v1 v2 : VALUE),
    eq_value v1 v2 <->
    beq_value v1 v2 = true.
Proof.
  intros. destruct v1,v2 ; simpl ; split
    ; try (intro H ; inversion H).
    + apply eqb_true_iff. reflexivity.
    + rewrite eqb_true_iff in H. apply H. 
    + apply Z.eqb_eq. reflexivity.
    + rewrite Z.eqb_eq in H. apply H. 
    + apply Nat.eqb_eq. reflexivity.
    + rewrite Nat.eqb_eq in H. apply H.
Qed.

Theorem theo_rules_state :
  forall (s : list (NAME * (VALUE * VALUE))),
    ind_rules_state s
    <-> fun_rules_state s = true.
Proof.
  intros. unfold ind_rules_state, fun_rules_state. split.
  - intro H. destruct List.map.
    + simpl. reflexivity.
    + rewrite theo_is_function in H.
      * rewrite H. reflexivity.
      * intros. apply theo_string_dec.
  - intro H. destruct List.map.
    + rewrite theo_is_function.
      * rewrite H. reflexivity.
      * intros. apply theo_string_dec.
    + rewrite theo_is_function.
      * rewrite H. reflexivity.
      * intros. apply theo_string_dec.
Qed.

Theorem lemm_is_valid_value :
  forall (v : VALUE) (t : TYPE),
    is_valid_value v t <->
    bis_valid_value v t = true.
Proof.
  intros. destruct v, t ; simpl ; split
  ; try (intro H ; inversion H).
  reflexivity. reflexivity.
  reflexivity. reflexivity.
  reflexivity. reflexivity.
Qed.

Theorem lemm_well_typed_var :
  forall (s : STATE) (n : NAME) (t : TYPE),
    well_typed_var s n t <->
    bwell_typed_var s n t =  true.
Proof.
  intros. unfold well_typed_var, bwell_typed_var.
  destruct (find_var_state n (state s)) eqn:H0.
  - split.
    + intro. destruct H. 
      rewrite lemm_is_valid_value in H
      ; rewrite lemm_is_valid_value in H1.
      rewrite H ; rewrite H1 ; reflexivity.
    + intro. rewrite lemm_is_valid_value 
      ; rewrite lemm_is_valid_value.
      rewrite <- andb_true_iff. apply H.
  - symmetry. split.
    + intro. inversion H.
    + intro. inversion H.
Qed.

Theorem lemm_well_typed_state_var :
  forall (s:STATE) (l: list (NAME * TYPE)),
    well_typed_state_var s l <->
    bwell_typed_state_var s l = true.
Proof.
  intros. split. 
  - induction l. 
    + simpl. intro. reflexivity.
    + intro. simpl in H. destruct H as [H1 H2].
      simpl. rewrite lemm_well_typed_var in H1.
      rewrite H1. apply IHl. apply H2.
  - induction l.
    + simpl. reflexivity.
    + intro H1. simpl in H1. simpl.
      destruct (bwell_typed_var s (fst a) (snd a)) eqn:H2.
      * split.
        { rewrite lemm_well_typed_var. apply H2. }
        { apply IHl in H1. apply H1. }
      * inversion H1.
Qed.

Theorem lemm_well_typed_state :
  forall (s : STATE) (l : list (NAME * TYPE)),
  well_typed_state s l <->
  bwell_typed_state s l = true.
Proof.
  intros. unfold well_typed_state, bwell_typed_state. split.
  - intro. rewrite lemm_same_list in H. 
    + rewrite lemm_well_typed_state_var in H.
      inversion H. rewrite H0. rewrite H1. reflexivity.
    + intros. split.
      * intro. rewrite theo_string_dec in H0. rewrite H0. reflexivity.
      * intro. rewrite theo_string_dec. rewrite H0. reflexivity.
  - intro. split.
    + rewrite lemm_same_list.
      * destruct (bwell_typed_state_var s l).
        { rewrite andb_true_iff in H. inversion H. rewrite H0. reflexivity. }
        { rewrite andb_true_iff in H. inversion H. inversion H1. }
      * intro. split.
        { intro. rewrite theo_string_dec in H0. rewrite H0. reflexivity. }
        { intro. rewrite theo_string_dec. rewrite H0. reflexivity. }
    + rewrite lemm_well_typed_state_var. rewrite andb_true_iff in H. 
      inversion H. rewrite H1. reflexivity.
Qed.

Theorem lemm_eq_state_element :
  forall (e1 e2 : (NAME * (VALUE * VALUE))),
  eq_state_element e1 e2 <-> 
  beq_state_element e1 e2 = true. 
Proof.
  intros. unfold eq_state_element, beq_state_element. split.
  - intro H. destruct H. destruct H0.
    rewrite theo_string_dec in H. rewrite H.
    rewrite lemm_eq_value in H0. rewrite H0.
    rewrite lemm_eq_value in H1. rewrite H1.
    simpl. reflexivity.
  - intro H. split.
    + destruct (bstring_dec (fst e1) (fst e2)) eqn:H1.
      * rewrite theo_string_dec. rewrite H1. reflexivity.
      * simpl in H. inversion H.
    + split.
      * destruct (beq_value (fst (snd e1)) (fst (snd e2))) eqn:H1.
        { rewrite lemm_eq_value. rewrite H1. reflexivity. }
        { destruct (bstring_dec (fst e1) (fst e2)).
          - simpl in H. inversion H.
          - simpl in H. inversion H. }
      * destruct (beq_value (snd (snd e1)) (snd (snd e2))) eqn:H1.
        { rewrite lemm_eq_value. rewrite H1. reflexivity. }
        { destruct (bstring_dec (fst e1) (fst e2)).
          - destruct (beq_value (fst (snd e1)) (fst (snd e2))). 
            + simpl in H ; inversion H.
            + simpl in H ; inversion H.
          - destruct (beq_value (fst (snd e1)) (fst (snd e2))).
            + simpl in H. inversion H.
            + simpl in H. inversion H. }
Qed.

Theorem lemm_eq_state_elements :
  forall (s1 s2 : list (NAME * (VALUE * VALUE))),
    eq_state_elements s1 s2 <->
    beq_state_elements s1 s2 = true.
Proof.
  intros. destruct s1, s2.
  - simpl. split. reflexivity. reflexivity.
  - simpl. split.
    + intro. inversion H.
    + intro. inversion H.
  - simpl. split.
    + intro. inversion H.
    + intro. inversion H.
  - simpl. split.
    + intro. rewrite <- lemm_eq_state_element. apply H.
    + intro. rewrite lemm_eq_state_element. apply H.
Qed.

Theorem lemm_eq_state :
  forall (s1 s2 : STATE),
    eq_state s1 s2 <->
    beq_state s1 s2 = true.
Proof.
  intros. unfold eq_state, beq_state. split.
  - intro H. rewrite lemm_same_list in H.
    + rewrite H. reflexivity.
    + intros. apply lemm_eq_state_element.
  - intro H. rewrite lemm_same_list.
    + rewrite H. reflexivity.
    + intros. apply lemm_eq_state_element.
Qed.

(* STATES *)
Theorem theo_rules_states :
  forall (ls : list STATE),
    ind_rules_states ls
    <-> fun_rules_states ls = true.
Proof.
  intros. unfold ind_rules_states, fun_rules_states. split.
  - intro H. rewrite <- Nat.ltb_lt in H. rewrite H. reflexivity.
  - intro H. rewrite <- Nat.ltb_lt. rewrite H. reflexivity.
Qed.

(* DFRS_STATES *)
Theorem theo_rules_dfrs_states :
  forall (s0 : STATE) (states : STATES),
    ind_rules_dfrs_states s0 states
    <-> fun_rules_dfrs_states s0 states = true.
Proof. 
  intros. unfold ind_rules_dfrs_states, fun_rules_dfrs_states. split.
  - intro H. rewrite lemm_in_list in H.
    + rewrite H. reflexivity.
    + intros. simpl. apply lemm_eq_state.
  - intro H. rewrite lemm_in_list.
    + rewrite H. reflexivity.
    + intros. simpl. apply lemm_eq_state.
Qed.