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
Require Import trans_rel_fun_ind_equiv.
Require Import e_dfrs.
Require Import e_dfrs_fun_rules.

Theorem lemm_is_valid_states:
  forall (states : list STATE) (f : list (NAME * TYPE)),
    is_valid_states states f <->
    bis_valid_states states f = true.
Proof.
  intros. split.
  - induction states.
    + simpl. reflexivity.
    + simpl. intro. destruct H.
      rewrite lemm_well_typed_state in H.
      rewrite H. apply IHstates. apply H0.
  - induction states.
    + simpl. reflexivity.
    + simpl. intro. destruct (bwell_typed_state a f) eqn:H0.
      * split.
        { rewrite lemm_well_typed_state. apply H0. }
        { apply IHstates. apply H. }
      * split.
        { inversion H. }
        { inversion H. }
Qed.

Theorem lemm_is_valid_trans:
  forall (trans : list TRANS) (sts : list STATE) 
  (I O T : list (VNAME * TYPE)) (gcvar : (NAME * TYPE)),
    is_valid_trans trans sts I O T gcvar <->
    bis_valid_trans trans sts I O T gcvar = true.
Proof.
  intros. split.
  - induction trans.
    + simpl. reflexivity.
    + simpl. intro. destruct H. destruct H0. destruct H1. destruct H2.
      rewrite lemm_in_list in H.
      * rewrite lemm_in_list in H0.
        { rewrite H0. rewrite lemm_well_typed_transition in H1.
          rewrite H. rewrite H1. simpl. destruct (branFun (snd (fst (STS a)))).
          - rewrite lemm_eq_state in H2. rewrite H2.
            destruct (branDel (snd (fst (STS a)))).
            + destruct (branDiscrete (snd (fst (STS a)))).
              * destruct (beq_state_elements
                          (update_gc
                             (update_state_values (state (fst3 (STS a))) 
                                (fst3 (STS a)) (map (fun x : VNAME * TYPE => vname (fst x)) T)
                                (map (fun x : ASGMT => vname (fst (asgmt x)))
                                   (asgmts
                                      match delayTransition (snd3 (STS a)) with
                                      | Some a => snd a
                                      | None => default_asgmts
                                      end))
                                match delayTransition (snd3 (STS a)) with
                                | Some a => snd a
                                | None => default_asgmts
                                end) (state (fst3 (STS a)))
                             match delayTransition (snd3 (STS a)) with
                             | Some a => fst a
                             | None => discrete 0
                             end) (state (snd (STS a)))).
                { apply IHtrans in H3. apply H3. }
                { inversion H3. }
              * apply IHtrans in H3. apply H3.
            + apply IHtrans in H3. apply H3.
          - apply IHtrans in H2. rewrite H2.
            destruct (branDel (snd (fst (STS a)))).
            + destruct (branDiscrete (snd (fst (STS a)))).
              * destruct (beq_state_elements
                          (update_gc
                             (update_state_values (state (fst3 (STS a))) 
                                (fst3 (STS a)) (map (fun x : VNAME * TYPE => vname (fst x)) T)
                                (map (fun x : ASGMT => vname (fst (asgmt x)))
                                   (asgmts
                                      match delayTransition (snd3 (STS a)) with
                                      | Some a => snd a
                                      | None => default_asgmts
                                      end))
                                match delayTransition (snd3 (STS a)) with
                                | Some a => snd a
                                | None => default_asgmts
                                end) (state (fst3 (STS a)))
                             match delayTransition (snd3 (STS a)) with
                             | Some a => fst a
                             | None => discrete 0
                             end) (state (snd (STS a)))).
                { reflexivity. }
                { inversion H3. }
              * reflexivity.
            + reflexivity. }
        { intros. split.
          - intro. rewrite lemm_eq_state in H4. apply H4.
          - intro. rewrite lemm_eq_state. apply H4. }
      * intros. split.
        { intro. rewrite lemm_eq_state in H4. apply H4. }
        { intro. rewrite lemm_eq_state. apply H4. }
  - induction trans.
    + simpl. reflexivity.
    + simpl. intro. 
      rewrite andb_true_iff in H; destruct H;
      rewrite andb_true_iff in H; destruct H;
      rewrite andb_true_iff in H; destruct H;
      rewrite andb_true_iff in H; destruct H.
      split.
      * rewrite lemm_in_list.
        { apply H. }
        { intros. split.
          - intro. rewrite lemm_eq_state in H4. apply H4.
          - intro. rewrite lemm_eq_state. apply H4. }
      * split.
        { rewrite lemm_in_list.
          - apply H3.
          - intros. split.
            + intro. rewrite lemm_eq_state in H4. apply H4.
            + intro. rewrite lemm_eq_state. apply H4. }
        { split.
          - rewrite lemm_well_typed_transition. apply H2.
          - split.
            + destruct (branFun (snd (fst (STS a)))).
              * rewrite lemm_eq_state. apply H1.
              * apply IHtrans. apply H1.
            + destruct (branDel (snd (fst (STS a)))).
              * destruct (branDiscrete (snd (fst (STS a)))).
                { destruct (beq_state_elements
                             (update_gc
                                (update_state_values (state (fst3 (STS a))) 
                                   (fst3 (STS a)) (map (fun x : VNAME * TYPE => vname (fst x)) T)
                                   (map (fun x : ASGMT => vname (fst (asgmt x)))
                                      (asgmts
                                         match delayTransition (snd3 (STS a)) with
                                         | Some a0 => snd a0
                                         | None => default_asgmts
                                         end))
                                   match delayTransition (snd3 (STS a)) with
                                   | Some a0 => snd a0
                                   | None => default_asgmts
                                   end) (state (fst3 (STS a)))
                                match delayTransition (snd3 (STS a)) with
                                | Some a0 => fst a0
                                | None => discrete 0
                                end) (state (snd (STS a)))).
                  - apply IHtrans. apply H0.
                  - inversion H0. }
                { apply IHtrans. apply H0. }
              * apply IHtrans. apply H0. }
Qed.

(* E_DFRS *)
Theorem theo_rules_e_dfrs :
  forall (vars : DFRS_VARIABLES) (states : DFRS_STATES)
         (trs : DFRS_TRANSITION_RELATION),
    ind_rules_e_dfrs vars states trs
    <-> fun_rules_e_dfrs vars states trs = true.
Proof. 
  intros. unfold ind_rules_e_dfrs, fun_rules_e_dfrs. split.
  - intro. destruct H. rewrite lemm_is_valid_states in H.
    rewrite lemm_is_valid_trans in H0. rewrite H. rewrite H0.
    simpl. reflexivity.
  - intro. rewrite andb_true_iff in H. destruct H. split.
    + rewrite lemm_is_valid_states. apply H.
    + rewrite lemm_is_valid_trans. apply H0.
Qed.
