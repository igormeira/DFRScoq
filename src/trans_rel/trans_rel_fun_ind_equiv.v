Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Require Import Bool.

Require Import util_fun_ind_equiv.
Require Import variables.
Require Import variables_fun_rules.
Require Import variables_fun_ind_equiv.
Require Import states.
Require Import states_fun_rules.
Require Import states_fun_ind_equiv.
Require Import functions.
Require Import functions_fun_rules.
Require Import functions_fun_ind_equiv.
Require Import trans_rel.
Require Import trans_rel_fun_rules.

Theorem lemm_well_typed_function_transition:
  forall (label : TRANS_LABEL) (O T : list (VNAME * TYPE)),
    well_typed_function_transition label O T <->
    bwell_typed_function_transition label O T = true.
Proof.
  intros. unfold well_typed_function_transition,
  bwell_typed_function_transition. split.
  - intros. rewrite lemm_list_in_list in H.
    + rewrite H. reflexivity.
    + intros. split.
      * intro. rewrite theo_string_dec in H0. apply H0.
      * intro. rewrite theo_string_dec. apply H0.
  - intros. destruct (blist_in_list (dom_fun [label])
        (map (fun x : VNAME * TYPE => fst x) O ++
         map (fun x : VNAME * TYPE => fst x) T)
        (fun v v' : VNAME => bstring_dec (vname v) (vname v'))) eqn:H1.
    + rewrite lemm_list_in_list.
      * apply H1.
      * intros. split.
        { intro. rewrite theo_string_dec in H0. apply H0. }
        { intro. rewrite theo_string_dec. apply H0. }
    + inversion H.
Qed.

Theorem theo_n_n:
  forall (n : nat),
    n =? n = true.
Proof.
  intros. rewrite Nat.eqb_eq. reflexivity.
Qed.

Theorem lemm_well_typed_delay_transition:
  forall (label : TRANS_LABEL) (I : list (VNAME * TYPE)),
    well_typed_delay_transition label I <->
    bwell_typed_delay_transition label I = true.
Proof.
  intros. unfold well_typed_delay_transition,
  bwell_typed_delay_transition. split.
  - intros. destruct H. rewrite lemm_list_in_list in H0.
    + rewrite H0. rewrite H. simpl.
      destruct (length (dom_del label)) eqn:H1.
      * rewrite <- H. simpl. reflexivity.
      * rewrite <- H. simpl. induction n.
        { simpl. reflexivity. }
        { simpl. rewrite theo_n_n. simpl. reflexivity. }
    + intros. split.
      * intro. rewrite theo_string_dec in H1. apply H1.
      * intro. rewrite theo_string_dec. apply H1.
  - intros. split.
    + destruct ((length (dom_del label) =?
       length (map (fun x : VNAME * TYPE => vname (fst x)) I)) &&
      blist_in_list (dom_del label)
        (map (fun x : VNAME * TYPE => vname (fst x)) I)
        (fun v v' : NAME => bstring_dec v v')) eqn:H1.
      * rewrite andb_true_iff in H1. destruct H1.
        rewrite Nat.eqb_eq in H0. apply H0.
      * inversion H.
    + destruct ((length (dom_del label) =?
       length (map (fun x : VNAME * TYPE => vname (fst x)) I)) &&
      blist_in_list (dom_del label)
        (map (fun x : VNAME * TYPE => vname (fst x)) I)
        (fun v v' : NAME => bstring_dec v v')) eqn:H1.
      * rewrite andb_true_iff in H1. destruct H1.
        rewrite lemm_list_in_list. 
        { apply H1. }
        { intros. split.
          - intro. rewrite <- theo_string_dec. apply H2.
          - intro. rewrite theo_string_dec. apply H2. }
      * inversion H.
Qed.

Theorem lemm_ranDiscrete:
  forall (label : TRANS_LABEL),
    ranDiscrete label <->
    branDiscrete label = true.
Proof.
  intros. split.
  - induction label.
    + intro. simpl in H. inversion H.
    + intro. simpl. destruct (fst p). reflexivity.
  - induction label.
    + intro. simpl in H. inversion H.
    + intro. simpl. destruct (fst p). reflexivity.
Qed.

Theorem lemm_clock_compatible_transition:
  forall (label : TRANS_LABEL) (gcvar : (NAME * TYPE)),
    clock_compatible_transition label gcvar <->
    bclock_compatible_transition label gcvar = true.
Proof.
  intros. unfold clock_compatible_transition,
  bclock_compatible_transition. split.
  - intro. destruct (branDiscrete label) eqn:H1.
    + rewrite <- lemm_eq_type. apply H. rewrite lemm_ranDiscrete.
      apply H1.
    + reflexivity.
  - intros. destruct (branDiscrete label) eqn:H1.
    + rewrite lemm_eq_type. apply H.
    + rewrite lemm_ranDiscrete in H0. rewrite H0 in H1. inversion H1.
Qed.

Theorem lemm_ranDel:
  forall (label : TRANS_LABEL),
    ranDel label <->
    branDel label = true.
Proof.
  intros. split.
  - induction label.
    + intro. simpl in H. inversion H.
    + intro. simpl. reflexivity.
  - induction label.
    + intro. simpl in H. inversion H.
    + intro. simpl. reflexivity.
Qed.

Theorem lemm_ranFun:
  forall (label : TRANS_LABEL),
    ranFun label <->
    branFun label = true.
Proof.
  intros. split.
  - induction label.
    + intro. simpl. reflexivity.
    + intro. simpl in H. inversion H.
  - induction label.
    + intro. simpl. reflexivity.
    + intro. simpl in H. inversion H.
Qed.

Theorem lemm_well_typed_transition:
  forall (label : TRANS_LABEL) (I O T : list (VNAME * TYPE))
  (gcvar : (NAME * TYPE)),
    well_typed_transition label I O T gcvar <->
    bwell_typed_transition label I O T gcvar = true.
Proof.
  intros. unfold well_typed_transition,
  bwell_typed_transition. split.
  - intros. destruct H. destruct H0.
    rewrite lemm_ranFun in H. rewrite andb_true_iff.
    rewrite andb_true_iff. split.
    + split.
      * destruct (branFun label).
        { rewrite <- lemm_well_typed_function_transition.
          apply H. reflexivity. }
        { reflexivity. }
      * rewrite lemm_ranDel in H0. destruct (branDel label).
        { rewrite <- lemm_well_typed_delay_transition.
          apply H0. reflexivity. }
        { reflexivity. }
    + rewrite lemm_clock_compatible_transition in H1.
      apply H1.
  - intros. rewrite andb_true_iff in H. rewrite andb_true_iff in H.
    destruct H. destruct H. split.
    + intro. destruct (branFun label) eqn:H3.
      * rewrite lemm_well_typed_function_transition. apply H.
      * rewrite lemm_ranFun in H2. rewrite H3 in H2. inversion H2.
    + split.
      * intro. destruct (branDel label) eqn:H3.
        { rewrite lemm_well_typed_delay_transition. apply H1. }
        { rewrite lemm_ranDel in H2. rewrite H3 in H2. inversion H2. }
      * rewrite lemm_clock_compatible_transition.
        apply H0.
Qed.

Theorem lemm_check_same_state_start:
  forall (trans : list TRANS) (tr : TRANS),
    check_same_state_start trans tr <->
    bcheck_same_state_start trans tr = true.
Proof.
  intros. split.
  - induction trans.
    + simpl. reflexivity.
    + simpl. intro. destruct (beq_state (fst3 (STS a)) (fst3 (STS tr))).
      * destruct H.
        { destruct H. rewrite orb_true_iff. left.
          rewrite andb_true_iff. split.
          - rewrite lemm_ranFun in H. apply H.
          - rewrite lemm_ranFun in H0. apply H0. }
        { destruct H. rewrite orb_true_iff. right.
          rewrite andb_true_iff. split.
          - rewrite lemm_ranDel in H. apply H.
          - rewrite lemm_ranDel in H0. apply H0. }
      * apply IHtrans. apply H.
  - induction trans.
    + simpl. reflexivity.
    + simpl. intro. destruct (beq_state (fst3 (STS a)) (fst3 (STS tr))).
      * rewrite orb_true_iff in H. destruct H.
        rewrite andb_true_iff in H. destruct H.
        left. split.
        { rewrite lemm_ranFun. apply H. }
        { rewrite lemm_ranFun. apply H0. }
        { right. split.
          - rewrite andb_true_iff in H. destruct H.
            rewrite lemm_ranDel. apply H.
          - rewrite andb_true_iff in H. destruct H.
            rewrite lemm_ranDel. apply H0. }
      * apply IHtrans. apply H.
Qed.

Theorem lemm_is_valid_trans:
  forall (trans : list TRANS),
    is_valid_trans trans <->
    bis_valid_trans trans = true.
Proof.
  intros. split.
  - induction trans.
    + simpl. reflexivity.
    + simpl. intro. destruct H. destruct H.
      destruct H1. destruct H2.
      rewrite lemm_eq_state in H. apply not_true_is_false in H.
      rewrite H. simpl. rewrite theo_rules_state in H1.
      rewrite theo_rules_state in H2. 
      rewrite lemm_check_same_state_start in H3.
      rewrite H1; rewrite H2; rewrite H3; simpl.
      apply IHtrans. apply H0.
  - induction trans.
    + simpl. reflexivity.
    + simpl. intro. destruct ((beq_state (fst3 (STS a)) (trd3 (STS a)))) eqn:H0.
      * simpl in H. inversion H.
      * simpl in H. destruct (fun_rules_state (state (fst3 (STS a))) &&
      fun_rules_state (state (trd3 (STS a))) && 
      bcheck_same_state_start trans a) eqn:H1.
        { split.
          - split.
            + unfold not. rewrite lemm_eq_state. rewrite H0. intro. inversion H2.
            + split.
              * rewrite andb_true_iff in H1. rewrite andb_true_iff in H1.
                destruct H1. destruct H1. rewrite theo_rules_state. apply H1.
              * split.
                { rewrite andb_true_iff in H1. rewrite andb_true_iff in H1.
                destruct H1. destruct H1. rewrite theo_rules_state. apply H3. }
                { rewrite andb_true_iff in H1. rewrite andb_true_iff in H1.
                destruct H1. rewrite lemm_check_same_state_start. apply H2. }
          - apply IHtrans. apply H. }
        { inversion H. }
Qed.

(* DFRS_TRANSITION_RELATION *)
Theorem theo_rules_dfrs_trans_rel :
  forall (tr : TRANSREL),
    ind_rules_dfrs_trans_rel tr
    <-> fun_rules_dfrs_trans_rel tr = true.
Proof.
  intros. unfold ind_rules_dfrs_trans_rel, fun_rules_dfrs_trans_rel. split.
  - intro. rewrite lemm_is_valid_trans in H. apply H.
  - intro. rewrite lemm_is_valid_trans. apply H.
Qed.