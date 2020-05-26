Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Import ListNotations.

Require Import variables.
Require Import variables_fun_rules.
Require Import util.
Require Import fun_util.
Require Import util_fun_ind_equiv.

(* VNAME *)
Theorem theo_rules_vname :
  forall (vname : NAME),
    ind_rules_vname vname <->
    fun_rules_vname vname = true.
Proof.
  intros. unfold fun_rules_vname, ind_rules_vname. split.
  - intro H. unfold not in H.
    apply eq_true_not_negb.
    unfold not. intro H'.
    rewrite theo_string_dec in H.
    apply H in H'. inversion H'.
  - intro H. unfold not. intro H'.
    rewrite negb_true_iff in H.
    rewrite theo_string_dec in H'.
    rewrite H in H'. inversion H'.
Qed.

Lemma lemm_comp_vname :
  forall (v1 v2 : VNAME),
    comp_vname v1 v2 <->
    bcomp_vname v1 v2 = true.
Proof.
  intros. unfold comp_vname, bcomp_vname.
  apply theo_string_dec.
Qed.

(* SVARS *)
Lemma lemm_eq_type :
  forall (t1 t2 : TYPE),
    eq_type t1 t2 <->
    beq_type t1 t2 = true.
Proof.
  intros [] [] ; split ; try (intro H ; reflexivity) ;
  repeat (simpl ; intro H ; inversion H).
Qed.

Lemma lemm_svar_valid_type :
  forall (t : TYPE),
    ind_svar_valid_type t <->
    fun_svar_valid_type t = true.
Proof.
  intros. unfold ind_svar_valid_type.
  do 2 rewrite -> lemm_eq_type.
  unfold fun_svar_valid_type. split.
  - intro H. destruct H.
    + rewrite H. simpl. reflexivity.
    + rewrite H. apply orb_true_r.
  - intro H. rewrite orb_true_iff in H. apply H.
Qed.

Lemma lemm_svars_valid_type :
  forall (svars : list (VNAME * TYPE)),
    ind_svars_valid_type svars <->
    fun_svars_valid_type svars = true.
Proof.
  intros. induction svars.
  - simpl. split ; reflexivity.
  - destruct a. destruct IHsvars as [IH1 IH2]. split.
    + intro H. simpl. simpl in H. destruct H as [H1 H2].
      apply IH1 in H2. rewrite H2.
      rewrite -> lemm_svar_valid_type in H1.
      rewrite H1. reflexivity.
    + intro H. simpl. split.
      * simpl in H. destruct (fun_svar_valid_type t) eqn:H'.
        { rewrite lemm_svar_valid_type. apply H'. }
        { inversion H. }
      * simpl in H. destruct (fun_svar_valid_type t) eqn:H'.
        { apply IH2. apply H. }
        { inversion H. }
Qed.

Lemma lemm_not_length_equiv_negb_length :
  forall (svars : list (VNAME * TYPE)),
    ~ (length svars = 0) <->
    negb (length svars =? 0) = true.
Proof.
  intros. split.
  - intros. destruct svars.
    + simpl in H. unfold not in H.
      exfalso. apply H. reflexivity.
    + simpl. reflexivity.
  - intros. destruct svars.
    + simpl in H. inversion H.
    + unfold not. intro H'. simpl in H'.
      inversion H'.
Qed.

Theorem theo_rules_svars :
  forall (svars : list (VNAME * TYPE)),
    ind_rules_svars svars <->
    fun_rules_svars svars = true.
Proof.
  intros. split.
  - intro H. unfold ind_rules_svars in H.
    destruct H as [H1 [H2 H3]].
    unfold fun_rules_svars.
    do 2 rewrite andb_true_iff.
    split. 1: split.
    + rewrite <- theo_is_function. apply H1.
      apply lemm_comp_vname.
    + rewrite <- lemm_not_length_equiv_negb_length. apply H2.
    + rewrite <- lemm_svars_valid_type. apply H3.
  - intro H. unfold fun_rules_svars in H.
    do 2 rewrite andb_true_iff in H.
    destruct H as [[H1 H2] H3].
    unfold ind_rules_svars.
    split. 2: split.
    + rewrite theo_is_function. apply H1.
      apply lemm_comp_vname.
    + rewrite lemm_not_length_equiv_negb_length. apply H2.
    + rewrite lemm_svars_valid_type. apply H3.
Qed.

(* STIMERS *)
Lemma lemm_stimer_valid_type :
  forall (t : TYPE),
    ind_stimer_valid_type t <->
    fun_stimer_valid_type t = true.
Proof.
  intros. unfold ind_stimer_valid_type.
  rewrite -> lemm_eq_type.
  unfold fun_stimer_valid_type. reflexivity.
Qed.

Lemma lemm_stimers_valid_type :
  forall (stimers : list (VNAME * TYPE)),
    ind_stimers_valid_type stimers <->
    fun_stimers_valid_type stimers = true.
Proof.
  intros. induction stimers.
  - simpl. split ; reflexivity.
  - destruct a. destruct IHstimers as [IH1 IH2]. split.
    + intro H. simpl. simpl in H. destruct H as [H1 H2].
      apply IH1 in H2. rewrite H2.
      rewrite -> lemm_stimer_valid_type in H1.
      rewrite H1. reflexivity.
    + intro H. simpl. split.
      * simpl in H. destruct (fun_stimer_valid_type t) eqn:H'.
        { rewrite lemm_stimer_valid_type. apply H'. }
        { inversion H. }
      * simpl in H. destruct (fun_stimer_valid_type t) eqn:H'.
        { apply IH2. apply H. }
        { inversion H. }
Qed.

Theorem theo_rules_stimers :
  forall (stimers : list (VNAME * TYPE)),
    ind_rules_stimers stimers <->
    fun_rules_stimers stimers = true.
Proof.
  intros. split.
  - intro H. unfold ind_rules_stimers in H.
    destruct H as [H1 H2].
    unfold fun_rules_stimers.
    rewrite andb_true_iff.
    split.
    + rewrite <- theo_is_function. apply H1.
      apply lemm_comp_vname.
    + rewrite <- lemm_stimers_valid_type. apply H2.
  - intro H. unfold fun_rules_stimers in H.
    rewrite andb_true_iff in H.
    destruct H as [H1 H2].
    unfold ind_rules_stimers.
    split.
    + rewrite theo_is_function. apply H1.
      apply lemm_comp_vname.
    + rewrite lemm_stimers_valid_type. apply H2.
Qed.

(* DFRS_VARIABLES *)
Lemma lemm_is_valid_disj :
  forall (l1 l2 : list VNAME),
    is_valid_disj l1 l2 <->
    bis_valid_disj l1 l2 = true.
Proof.
  intros. induction l1.
  - simpl. split ; reflexivity.
  - destruct a. destruct IHl1 as [IH1 IH2]. split.
    + intro H. simpl. simpl in H. destruct H as [H1 H2].
      destruct (bin_list {| vname := vname; rules_vname := rules_vname |} l2) eqn:H3.
      * rewrite -> lemm_in_list in H1.
        { unfold not in H1. apply H1 in H3. inversion H3. }
        { apply lemm_comp_vname. }
      * apply IH1. apply H2.
    + intro H. simpl. split.
      * unfold not. intro H2. simpl in H.
        rewrite lemm_in_list in H2.
        { rewrite H2 in H. inversion H. }
        { apply lemm_comp_vname. }
      * apply IH2. simpl in H.
        destruct (bin_list {| vname := vname; rules_vname := rules_vname |} l2) eqn:H2.
        { inversion H. }
        { apply H. }
Qed.

Lemma lemm_disjoint3 :
  forall (p : (list VNAME) * (list VNAME) * (list VNAME)),
    (is_valid_disj (fst3 p) (snd3 p)
     /\ is_valid_disj (fst3 p) (trd3 p)
     /\ is_valid_disj (snd3 p) (trd3 p))
    <->
    (bis_valid_disj (fst3 p) (snd3 p)
     && bis_valid_disj (fst3 p) (trd3 p)
     && bis_valid_disj (snd3 p) (trd3 p) = true).
Proof.
  intros. split.
  - intro H. destruct H as [H1 [H2 H3]].
    do 2 rewrite andb_true_iff.
    rewrite <- lemm_is_valid_disj with (l1 := fst3 p) (l2 := snd3 p).    
    rewrite <- lemm_is_valid_disj with (l1 := fst3 p) (l2 := trd3 p).
    rewrite <- lemm_is_valid_disj with (l1 := snd3 p) (l2 := trd3 p).
    split. split.
    + apply H1.
    + apply H2.
    + apply H3.
  - intro H. do 2 rewrite andb_true_iff in H.
    do 3 rewrite <- lemm_is_valid_disj in H.
    destruct H as [[H1 H2] H3]. split. 2: split.
    + apply H1.
    + apply H2.
    + apply H3.
Qed.

Lemma lemm_ran_T :
  forall (V : Type) (l : list (V * TYPE)) (type : TYPE),
    ran_T l type
    <-> bran_T l type = true.
Proof.
  intros. induction l.
  - split.
    + simpl. intro H. reflexivity.
    + intro H. simpl. reflexivity.
  - split ; destruct IHl as [IH1 IH2].
    + intro H. simpl. destruct (beq_type (snd a) type) eqn:H2.
      * apply IH1. simpl in H. destruct H as [H' H''].
        apply H''.
      * simpl in H. destruct H as [H' H''].
        rewrite lemm_eq_type in H'.
        rewrite H' in H2. inversion H2.
    + intro H. simpl. split.
      * rewrite lemm_eq_type. simpl in H.
        destruct (beq_type (snd a) type) eqn:H2.
        { reflexivity. }
        { inversion H. }
      * apply IH2. simpl in H.
        destruct (beq_type (snd a) type) eqn:H2.
        { apply H. }
        { inversion H. }
Qed.

Theorem theo_rules_dfrs_variables :
  forall (I O : SVARS) (T : STIMERS)
         (gcvar : (NAME * TYPE)),
    (string_dec (fst gcvar) gc
     /\ (eq_type (snd gcvar) Tnat)
     /\ (disjoint3
              (map (fun x : (VNAME * TYPE) => fst x) I.(svars),
               map (fun x : (VNAME * TYPE) => fst x) O.(svars),
               map (fun x : (VNAME * TYPE) => fst x) T.(stimers)))
     /\ ran_T T.(stimers) (snd gcvar))
    <->
    (bstring_dec (fst gcvar) gc
     && (beq_type (snd gcvar) Tnat)
     && (bdisjoint3
              (map (fun x : (VNAME * TYPE) => fst x) I.(svars),
               map (fun x : (VNAME * TYPE) => fst x) O.(svars),
               map (fun x : (VNAME * TYPE) => fst x) T.(stimers)))
     && bran_T T.(stimers) (snd gcvar) = true).
Proof.
  intros. split.
  - intros. destruct H as [H1 [H2 [H3 H4]]].
    do 3 rewrite andb_true_iff. split. split. split.
    + rewrite <- theo_string_dec. apply H1.
    + rewrite <- lemm_eq_type. apply H2.
    + rewrite <- lemm_disjoint3
      with (p := (map (fun x : VNAME * TYPE => fst x) (svars I),
       map (fun x : VNAME * TYPE => fst x) (svars O),
       map (fun x : VNAME * TYPE => fst x) (stimers T))).
      apply H3.
    + rewrite <- lemm_ran_T. apply H4.
  - intro H. do 3 rewrite andb_true_iff in H.
    destruct H as [[[H1 H2] H3] H4].
    rewrite <- theo_string_dec in H1.
    rewrite <- lemm_eq_type in H2.
    rewrite <- lemm_disjoint3
      with (p := (map (fun x : VNAME * TYPE => fst x) (svars I),
       map (fun x : VNAME * TYPE => fst x) (svars O),
       map (fun x : VNAME * TYPE => fst x) (stimers T))) in H3.
    rewrite <- lemm_ran_T in H4.
    split. 2: split. 3: split.
    + apply H1.
    + apply H2.
    + apply H3.
    + apply H4.
Qed.