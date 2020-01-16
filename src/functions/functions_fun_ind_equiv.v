Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Bool.Bool.

Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Gt.

Require Import functions.
Require Import functions_fun_rules.
Require Import states_fun_rules.
Require Import states_fun_ind_equiv.
Require Import util_fun_ind_equiv.
Require Import variables_fun_ind_equiv.

(* EXPRESSION *)
Theorem lemm_is_valid_op :
  forall (op : OP) (v : VALUE),
    is_valid_op op v <->
    bis_valid_op op v = true.
Proof.
  intros. split ; destruct op,v ;
  simpl ; intros ; try reflexivity ; try inversion H.
Qed.

Theorem theo_rules_disj:
  forall (lb : list BEXP),
    ind_rules_disj lb <->
    fun_rules_disj lb = true.
Proof.
  intros. unfold ind_rules_disj, fun_rules_disj. split.
  - destruct lb.
    + intro. simpl in H. inversion H.
    + intro. rewrite Nat.ltb_lt. apply H.
  - destruct lb.
    + intro. simpl in H. inversion H.
    + intro. rewrite <- Nat.ltb_lt. apply H.
Qed.

Theorem lemm_var_consistent_be:
  forall (be : BEXP) (f T : list (VNAME * TYPE)),
    var_consistent_be be f T <->
    bvar_consistent_be be f T = true.
Proof.
  intros. unfold var_consistent_be, bvar_consistent_be. split.
  - intro. induction (find_var_declaration (var_name be) f).
    + destruct v, be.
      * simpl in H. simpl.
        destruct H. rewrite lemm_in_list in H.
        { rewrite H. destruct H0. rewrite lemm_is_valid_value in H0.
          rewrite H0. destruct H1. rewrite lemm_is_valid_op in H1.
          rewrite H1. simpl. destruct (bin_list (var_name {| v := v0; op := op; literal := literal |})
    (map (fun x : VNAME * TYPE => fst x) T) variables_fun_rules.bcomp_vname).
          reflexivity. reflexivity. }
        { intros. split.
          - intro. rewrite lemm_comp_vname in H1. apply H1.
          - intro. rewrite <- lemm_comp_vname in H1. apply H1. }
      * simpl in H. simpl.
        destruct H. rewrite lemm_in_list in H.
        { rewrite H. destruct H0. rewrite lemm_is_valid_value in H0.
          rewrite H0. destruct H1. rewrite lemm_is_valid_op in H1.
          rewrite H1. simpl. destruct (bin_list (var_name {| v := v0; op := op; literal := literal |})
    (map (fun x : VNAME * TYPE => fst x) T) variables_fun_rules.bcomp_vname).
          inversion H2. reflexivity. }
        { intros. split.
          - intro. rewrite lemm_comp_vname in H1. apply H1.
          - intro. rewrite <- lemm_comp_vname in H1. apply H1. }
    + destruct H. destruct H0. inversion H0.
  - intro. induction (find_var_declaration (var_name be) f).
    + destruct v, be.
      * simpl in H. simpl. destruct (bin_list (var_name {| v := v0; op := op; literal := literal |})
    (map (fun x : VNAME * TYPE => fst x) T) variables_fun_rules.bcomp_vname).
        { rewrite andb_true_iff in H. rewrite andb_true_iff in H.
          rewrite andb_true_iff in H. destruct H. destruct H.
          destruct H. split.
          - rewrite lemm_in_list.
            + apply H.
            + intros. split.
              * intro. rewrite lemm_comp_vname in H3. apply H3.
              * intro. rewrite <- lemm_comp_vname in H3. apply H3.
          - split.
            + rewrite <- lemm_is_valid_value in H2. apply H2.
            + rewrite lemm_is_valid_op. rewrite H1. split.
              reflexivity. reflexivity. }
        { rewrite andb_true_iff in H. rewrite andb_true_iff in H.
          rewrite andb_true_iff in H. destruct H. destruct H.
          destruct H. split.
          - rewrite lemm_in_list.
            + apply H.
            + intros. split.
              * intro. rewrite lemm_comp_vname in H3. apply H3.
              * intro. rewrite <- lemm_comp_vname in H3. apply H3.
          - split.
            + rewrite <- lemm_is_valid_value in H2. apply H2.
            + rewrite lemm_is_valid_op. rewrite H1. split.
              reflexivity. reflexivity. }
      * simpl in H. simpl. destruct (bin_list (var_name {| v := v0; op := op; literal := literal |})
    (map (fun x : VNAME * TYPE => fst x) T) variables_fun_rules.bcomp_vname).
        { rewrite andb_true_iff in H. rewrite andb_true_iff in H.
          rewrite andb_true_iff in H. destruct H. destruct H.
          destruct H. split.
          - rewrite lemm_in_list.
            + apply H.
            + intros. split.
              * intro. rewrite lemm_comp_vname in H3. apply H3.
              * intro. rewrite <- lemm_comp_vname in H3. apply H3.
          - split.
            + rewrite <- lemm_is_valid_value in H2. apply H2.
            + rewrite lemm_is_valid_op. rewrite H1. split.
              reflexivity. inversion H0. }
        { rewrite andb_true_iff in H. rewrite andb_true_iff in H.
          rewrite andb_true_iff in H. destruct H. destruct H.
          destruct H. split.
          - rewrite lemm_in_list.
            + apply H.
            + intros. split.
              * intro. rewrite lemm_comp_vname in H3. apply H3.
              * intro. rewrite <- lemm_comp_vname in H3. apply H3.
          - split.
            + rewrite <- lemm_is_valid_value in H2. apply H2.
            + rewrite lemm_is_valid_op. rewrite H1. split.
              reflexivity. reflexivity. }
    + rewrite andb_true_iff in H. rewrite andb_true_iff in H.
      rewrite andb_true_iff in H. destruct H. destruct H.
      destruct H. inversion H2.
Qed.

Theorem lemm_var_consistent_dis :
  forall (disjs : list BEXP) (f T : list (VNAME * TYPE)),
    var_consistent_dis disjs f T <->
    bvar_consistent_dis disjs f T = true.
Proof.
  intros. split.
  - induction disjs.
    + simpl. reflexivity.
    + intros. simpl. destruct (bvar_consistent_be a f T) eqn:H2.
      * simpl. apply IHdisjs. simpl in H.
        destruct H as [H0 H1]. apply H1.
      * simpl in H. destruct H as [H0 H1].
        rewrite lemm_var_consistent_be in H0.
        rewrite H2 in H0. inversion H0.
  - induction disjs.
    + simpl. reflexivity.
    + intros. simpl. split.
      * simpl in H. destruct (bvar_consistent_be a f T) eqn:H2.
        rewrite <- lemm_var_consistent_be in H2. apply H2.
        simpl in H. inversion H.
      * simpl in H. destruct (bvar_consistent_be a f T) eqn:H2.
        rewrite andb_true_iff in H. destruct H.
        apply IHdisjs in H0. apply H0.
        simpl in H. inversion H.
Qed.

Theorem lemm_var_consistent_conj:
  forall (conjs : list DISJ) (f T : list (VNAME * TYPE)),
    var_consistent_conj conjs f T <->
    bvar_consistent_conj conjs f T =  true.
Proof.
  intros. split.
  - induction conjs.
    + simpl. reflexivity.
    + intros. simpl. simpl in H. destruct H.
      rewrite lemm_var_consistent_dis in H. rewrite H.
      rewrite andb_true_iff. split.
      * reflexivity.
      * apply IHconjs. apply H0.
  - induction conjs.
    + simpl. reflexivity.
    + intros. simpl. simpl in H. rewrite andb_true_iff in H.
      destruct H. split.
      * rewrite <- lemm_var_consistent_dis in H. apply H.
      * apply IHconjs in H0. apply H0.
Qed.

Theorem lemm_var_consistent_exp:
  forall (exp : EXP) (f T : list (VNAME * TYPE)),
    var_consistent_exp exp f T <->
    bvar_consistent_exp exp f T = true.
Proof.
  intros. unfold var_consistent_exp, bvar_consistent_exp. split.
  - intro. rewrite lemm_var_consistent_conj in H. apply H.
  - intro. rewrite lemm_var_consistent_conj. apply H.
Qed.

(* ASSIGNMENT *)
Theorem theo_rules_asgmts :
  forall (l : list ASGMT),
    ind_rules_asgmts l
    <-> fun_rules_asgmts l = true.
Proof. 
  intros. unfold ind_rules_asgmts, fun_rules_asgmts. split.
  - intro H. rewrite theo_is_function in H.
    + destruct l.
      * simpl in H. rewrite <- Nat.ltb_lt in H. destruct H. inversion H.
      * destruct H. rewrite H0. simpl. reflexivity.
    + split.
      * intro. rewrite theo_string_dec in H0. rewrite H0. reflexivity.
      * intro. rewrite theo_string_dec. rewrite H0. reflexivity.
  - intro. split.
    + destruct l.
      * simpl in H. inversion H.
      * destruct (Datatypes.length (a :: l)).
        { simpl in H. inversion H. }
        { apply gt_Sn_O. }
    + rewrite theo_is_function.
      * destruct (Datatypes.length l).
        { simpl in H. inversion H. }
        { simpl in H. rewrite H. reflexivity. }
      * split.
        { intro. rewrite theo_string_dec in H0. rewrite H0. reflexivity. }
        { intro. rewrite theo_string_dec. rewrite H0. reflexivity. }
Qed.

Theorem lemm_is_valid_asgmts_names:
  forall (la : list ASGMT) (ln : list VNAME),
    is_valid_asgmts_names la ln <->
    bis_valid_asgmts_names la ln = true.
Proof.
  intros. split.
  - induction la.
    + simpl. reflexivity.
    + intro. simpl. simpl in H. destruct H.
      rewrite lemm_in_list in H.
      * rewrite H. apply IHla. apply H0.
      * intros. split.
        { intro. rewrite lemm_comp_vname in H1. apply H1. }
        { intro. rewrite lemm_comp_vname. apply H1. }
  - induction la.
    + simpl. reflexivity.
    + intro. simpl. simpl in H. rewrite andb_true_iff in H.
      destruct H. split.
      * rewrite lemm_in_list.
        { apply H. }
        { intros. split.
          - intro. rewrite lemm_comp_vname in H1. apply H1.
          - intro. rewrite lemm_comp_vname. apply H1. }
      * apply IHla in H0. apply H0.
Qed.

Theorem lemm_well_typed_asgmts:
  forall (la : list ASGMT) (f : list (VNAME * TYPE)),
    well_typed_asgmts la f <->
    bwell_typed_asgmts la f = true.
Proof.
  intros. split.
  - induction la.
    + simpl. reflexivity.
    + intro. simpl. simpl in H.
      destruct (find_var_declaration (fst (asgmt a)) f) eqn:H1.
      * rewrite andb_true_iff; split; rewrite andb_true_iff; split.
        destruct H; destruct H.
        { rewrite <- lemm_in_list.
          - apply H.
          - intros. split.
            + intro. rewrite lemm_comp_vname in H3. apply H3.
            + intro. rewrite lemm_comp_vname. apply H3. }
        { destruct H; destruct H. rewrite <- lemm_is_valid_asgmts_names.
          apply H2. }
        { destruct H. destruct H0. rewrite <- lemm_is_valid_value.
          apply H0. }
        { destruct H. destruct H0. 
          apply IHla. apply H2. }
      * destruct H; destruct H0; inversion H0.
  - induction la.
    + simpl; intro; split; try reflexivity.
    + intro. simpl. simpl in H.
      destruct (find_var_declaration (fst (asgmt a)) f).
      * split; split.
        { rewrite andb_true_iff in H; rewrite andb_true_iff in H.
          destruct H; destruct H. rewrite lemm_in_list.
          - apply H.
          - intros. split.
            + intro. rewrite lemm_comp_vname in H2. apply H2.
            + intro. rewrite lemm_comp_vname. apply H2. }
        { rewrite andb_true_iff in H; rewrite andb_true_iff in H.
          destruct H; destruct H. rewrite lemm_is_valid_asgmts_names.
          apply H1. }
        { rewrite andb_true_iff in H; destruct H;
          rewrite andb_true_iff in H0; destruct H0.
          rewrite lemm_is_valid_value. apply H0. }
        { rewrite andb_true_iff in H; destruct H;
          rewrite andb_true_iff in H0; destruct H0.
          apply IHla. apply H1. }
      * rewrite andb_true_iff in H; destruct H;
        rewrite andb_true_iff in H0; destruct H0.
        inversion H0.
Qed.
 
(* FUNCTION *)
Theorem theo_rules_function :
  forall (l : list (EXP * EXP * ASGMTS * REQUIREMENT) ),
    ind_rules_function l
    <-> fun_rules_function l = true.
Proof. 
  intros. split.
  - induction l.
    + simpl. reflexivity.
    + intro. simpl. simpl in H. destruct H.
      rewrite andb_true_iff. split.
      * destruct ((conjs (fst (fst (fst a))) ++ conjs (snd (fst (fst a))))).
        { simpl in H. inversion H. }
        { rewrite <- Nat.ltb_lt in H. apply H. }
      * apply IHl. apply H0.
  - induction l.
    + simpl. reflexivity.
    + intro. simpl. simpl in H. 
      rewrite andb_true_iff in H. destruct H. split.
      * destruct ((conjs (fst (fst (fst a))) ++ conjs (snd (fst (fst a))))).
        { simpl in H. inversion H. }
        { rewrite <- Nat.ltb_lt. apply H. }
      * apply IHl. apply H0.
Qed.

Theorem theo_rules_dfrs_functions :
  forall (lf : list FUNCTION),
    ind_rules_dfrs_functions lf
    <-> fun_rules_dfrs_functions lf = true.
Proof. 
  intros. unfold ind_rules_dfrs_functions, fun_rules_dfrs_functions. split.
  - intros. destruct (Datatypes.length lf).
    + rewrite <- Nat.ltb_lt in H. rewrite H. reflexivity.
    + rewrite <- Nat.ltb_lt in H. rewrite H. reflexivity.
  - intros. destruct (Datatypes.length lf).
    + rewrite <- Nat.ltb_lt. rewrite H. reflexivity.
    + rewrite <- Nat.ltb_lt. rewrite H. reflexivity.
Qed.