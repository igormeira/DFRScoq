Require Import util_fun_ind_equiv.
Require Import variables.
Require Import variables_fun_rules.
Require Import states.
Require Import states_fun_rules.
Require Import states_fun_ind_equiv.
Require Import functions.
Require Import functions_fun_rules.
Require Import functions_fun_ind_equiv.
Require Import s_dfrs.
Require Import s_dfrs_fun_rules.

Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Import ListNotations.

(* S_DFRS *)

Theorem lemm_check_function_entries:
  forall (l : list (EXP * EXP * ASGMTS * REQUIREMENT))
  (IO T OT : list (VNAME * TYPE)),
    check_function_entries l IO T OT <->
    bcheck_function_entries l IO T OT = true.
Proof.
  intros. split.
  - induction l.
    + simpl. reflexivity.
    + intro. simpl. simpl in H.
      destruct H; destruct H0; destruct H1.
      rewrite andb_true_iff; rewrite andb_true_iff;
      rewrite andb_true_iff. split.
      * split.
        { split.
          - rewrite lemm_var_consistent_exp in H. apply H.
          - rewrite lemm_var_consistent_exp in H0. apply H0. }
        { rewrite lemm_well_typed_asgmts in H1. apply H1. }
      * apply IHl. apply H2.
  - induction l.
    + simpl. reflexivity.
    + intro. simpl. simpl in H. rewrite andb_true_iff in H
      ; rewrite andb_true_iff in H; rewrite andb_true_iff in H.
      destruct H; destruct H; destruct H. split.
      * rewrite lemm_var_consistent_exp. apply H.
      * split.
        { rewrite lemm_var_consistent_exp. apply H2. }
        { split.
          - rewrite lemm_well_typed_asgmts. apply H1.
          - apply IHl. apply H0. }
Qed.

Theorem lemm_check_functions :
  forall (lf : list FUNCTION) (IO T OT : list (VNAME * TYPE)),
    check_functions lf IO T OT <->
    bcheck_functions lf IO T OT = true.
Proof.
  intros. split.
  - induction lf.
    + simpl. reflexivity.
    + intro. simpl. simpl in H. destruct H.
      rewrite andb_true_iff. split.
      * rewrite <- lemm_check_function_entries. apply H.
      * apply IHlf. apply H0.
  - induction lf.
    + simpl. reflexivity.
    + intro. simpl. simpl in H. rewrite andb_true_iff in H.
      destruct H. split.
      * rewrite lemm_check_function_entries. apply H.
      * apply IHlf. apply H0.
Qed.

Theorem theo_rules_s_dfrs :
  forall (vars : DFRS_VARIABLES) (initial : DFRS_INITIAL_STATE)
         (funs : DFRS_FUNCTIONS),
    ind_rules_s_dfrs vars initial funs
    <-> fun_rules_s_dfrs vars initial funs = true.
Proof. 
  intros. unfold ind_rules_s_dfrs, fun_rules_s_dfrs. split.
  - simpl. intros. destruct H.
    + rewrite lemm_well_typed_state in H. rewrite lemm_check_functions in H0.
      rewrite H. rewrite H0. simpl. reflexivity.
  - intros. rewrite lemm_well_typed_state. rewrite lemm_check_functions. split.
    destruct (bcheck_functions (F funs) (svars (I vars) ++ svars (O vars))
       (stimers (T vars)) (svars (O vars) ++ stimers (T vars))).
    + simpl in H. simpl. 
      destruct (bwell_typed_state (s0 initial)
       (gcvar vars
        :: List.map (fun x : VNAME * TYPE => (vname (fst x), snd x))
             ((svars (I vars) ++ svars (O vars)) ++ stimers (T vars)))).
      * reflexivity.
      * inversion H.
    + simpl in H. simpl.
      destruct (bwell_typed_state (s0 initial)
       (gcvar vars
        :: List.map (fun x : VNAME * TYPE => (vname (fst x), snd x))
             ((svars (I vars) ++ svars (O vars)) ++ stimers (T vars)))).
      * reflexivity.
      * inversion H.
    + simpl in H.
      destruct (bwell_typed_state (s0 initial)
       (gcvar vars
        :: List.map (fun x : VNAME * TYPE => (vname (fst x), snd x))
             ((svars (I vars) ++ svars (O vars)) ++ stimers (T vars)))).
      * destruct (bcheck_functions (F funs) (svars (I vars) ++ svars (O vars))
       (stimers (T vars)) (svars (O vars) ++ stimers (T vars))).
        { reflexivity. }
        { inversion H. }
      * inversion H.
Qed.