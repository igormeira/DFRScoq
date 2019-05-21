Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.

Local Open Scope string.

Require Import variables.
Require Import variables_fun_ind_equiv.
Require Import state.
Require Import state_fun_ind_equiv.
Require Import functions.
Require Import functions_fun_ind_equiv.
Require Import s_dfrs.
Require Import s_dfrs_fun_ind_equiv.
Require Import states.
Require Import states_fun_rules.
Require Import states_fun_ind_equiv.
Require Import trans_rel.
Require Import trans_rel_fun_rules.
Require Import trans_rel_fun_ind_equiv.
Require Import e_dfrs.
Require Import e_dfrs_fun_ind_equiv.

(*============ VM: VARIABLES ============*)

(* VNAMES *)
Definition the_coin_sensor' : VNAME.
Proof.
  apply (mkVNAME "the_coin_sensor").
  unfold ind_rules_vname. unfold not.
  intro H. inversion H.
Defined.

Definition the_coin_sensor : VNAME.
Proof.
  apply (mkVNAME "the_coin_sensor").
  apply theo_rules_vname. reflexivity.
Defined.

Definition the_coffee_request_button : VNAME.
Proof.
  apply (mkVNAME "the_coffee_request_button").
  apply theo_rules_vname. reflexivity.
Defined.

Definition the_system_mode : VNAME.
Proof.
  apply (mkVNAME "the_system_mode").
  apply theo_rules_vname. reflexivity.
Defined.
 
Definition the_coffee_machine_output : VNAME.
Proof.
  apply (mkVNAME "the_coffee_machine_output").
  apply theo_rules_vname. reflexivity.
Defined.

Definition the_request_timer : VNAME.
Proof.
  apply (mkVNAME "the_request_timer").
  apply theo_rules_vname. reflexivity.
Defined.

(* SVARS AND STIMERS *)

Definition vm_I : SVARS.
Proof.
  apply (mkSVARS [(the_coin_sensor, Tbool); 
                  (the_coffee_request_button, Tbool)]).
  apply theo_rules_svars. reflexivity.
Defined.

Definition vm_O : SVARS.
Proof.
  apply (mkSVARS [(the_system_mode, Tint);
                  (the_coffee_machine_output, Tint)]).
  apply theo_rules_svars. reflexivity.
Defined.

Definition vm_T : STIMERS.
Proof.
  apply (mkSTIMERS [(the_request_timer, Tnat)]).
  apply theo_rules_stimers. reflexivity.
Defined.

(* VARIABLES *)

Definition vm_gcvar := ("gc", Tnat).

Definition vm_variables : DFRS_VARIABLES.
Proof.
  apply (mkDFRS_VARIABLES vm_I vm_O vm_T vm_gcvar).
  apply theo_rules_dfrs_variables. reflexivity.
Defined.
(*============ VM: VARIABLES ============*)

(*============ VM: INITIAL STATES ============*)

Local Open Scope string.

Definition vm_state : STATE.
Proof. 
  apply (mkSTATE
            [("the_coin_sensor", (b false, b false));
             ("the_coffee_request_button", (b false, b false));
             ("the_system_mode", (i 1, i 1));
             ("the_coffee_machine_output", (i 0, i 0));
             ("the_request_timer", (n 0, n 0));
             ("gc", (n 0, n 0))]).
  apply theo_rules_state. reflexivity.
Defined.

Definition vm_s0 : DFRS_INITIAL_STATE.
Proof.
  apply (mkDFRS_INITIAL_STATE vm_state).
Defined.

(*============ VM: INITIAL STATES ============*)

(*============ VM: FUNCTIONS ============*)

Local Open Scope string.

(* REQ001 *)
Definition req001_sg_disj1 : DISJ.
Proof.
  apply (mkDISJ [mkBEXP (previous (the_coin_sensor)) eq (b false)]).
  apply theo_rules_disj. reflexivity.
Defined.

Definition req001_sg_disj2 : DISJ.
Proof.
  apply (mkDISJ [mkBEXP (current (the_coin_sensor)) eq (b true)]).
  apply theo_rules_disj. reflexivity.
Defined.

Definition req001_sg_disj3 : DISJ.
Proof.
  apply (mkDISJ [mkBEXP (current (the_system_mode)) eq (i 1)]).
  apply theo_rules_disj. reflexivity.
Defined.

Definition req001_sg : EXP.
Proof.
  apply (mkCONJ [req001_sg_disj1; req001_sg_disj2; req001_sg_disj3]).
Defined.

Definition req001_tg : EXP.
Proof.
  apply (mkCONJ []).
Defined.

Definition req001_asgmt1 : ASGMT.
Proof.
  apply (mkASGMT (the_request_timer, (n 0))).
Defined.

Definition req001_asgmt2 : ASGMT.
Proof.
  apply (mkASGMT (the_system_mode, (i 0))).
Defined.

Definition req001_asgmts : ASGMTS.
Proof.
  apply (mkASGMTS [req001_asgmt1; req001_asgmt2]).
  apply theo_rules_asgmts. reflexivity.
Defined.

(* REQ002 *)
Definition req002_sg_disj1 : DISJ.
Proof.
  apply (mkDISJ [mkBEXP (previous (the_coffee_request_button)) eq (b false)]).
  apply theo_rules_disj. reflexivity.
Defined.

Definition req002_sg_disj2 : DISJ.
Proof.
  apply (mkDISJ [mkBEXP (current (the_coffee_request_button)) eq (b true)]).
  apply theo_rules_disj. reflexivity.
Defined.

Definition req002_sg_disj3 : DISJ.
Proof.
  apply (mkDISJ [mkBEXP (previous (the_coin_sensor)) eq (b false)]).
  apply theo_rules_disj. reflexivity.
Defined.

Definition req002_sg_disj4 : DISJ.
Proof.
  apply (mkDISJ [mkBEXP (current (the_coin_sensor)) eq (b false)]).
  apply theo_rules_disj. reflexivity.
Defined.

Definition req002_sg_disj5 : DISJ.
Proof.
  apply (mkDISJ [mkBEXP (current (the_system_mode)) eq (i 0)]).
  apply theo_rules_disj. reflexivity.
Defined.

Definition req002_sg : EXP.
Proof.
  apply (mkCONJ [req002_sg_disj1; req002_sg_disj2; 
                 req002_sg_disj3; req002_sg_disj4;
                 req002_sg_disj5]).
Defined.

Definition req002_tg_disj1 : DISJ.
Proof.
  apply (mkDISJ [mkBEXP (current (the_request_timer)) le (n 30)]).
  apply theo_rules_disj. reflexivity.
Defined.

Definition req002_tg : EXP.
Proof.
  apply (mkCONJ [req002_tg_disj1]).
Defined.

Definition req002_asgmt1 : ASGMT.
Proof.
  apply (mkASGMT (the_request_timer, (n 0))).
Defined.

Definition req002_asgmt2 : ASGMT.
Proof.
  apply (mkASGMT (the_system_mode, (i 3))).
Defined.

Definition req002_asgmts : ASGMTS.
Proof.
  apply (mkASGMTS [req002_asgmt1; req002_asgmt2]).
  apply theo_rules_asgmts. reflexivity.
Defined.

(* REQ003 *)
Definition req003_sg_disj1 : DISJ.
Proof.
  apply (mkDISJ [mkBEXP (previous (the_coffee_request_button)) eq (b false)]).
  apply theo_rules_disj. reflexivity.
Defined.

Definition req003_sg_disj2 : DISJ.
Proof.
  apply (mkDISJ [mkBEXP (current (the_coffee_request_button)) eq (b true)]).
  apply theo_rules_disj. reflexivity.
Defined.

Definition req003_sg_disj3 : DISJ.
Proof.
  apply (mkDISJ [mkBEXP (previous (the_coin_sensor)) eq (b false)]).
  apply theo_rules_disj. reflexivity.
Defined.

Definition req003_sg_disj4 : DISJ.
Proof.
  apply (mkDISJ [mkBEXP (current (the_coin_sensor)) eq (b false)]).
  apply theo_rules_disj. reflexivity.
Defined.

Definition req003_sg_disj5 : DISJ.
Proof.
  apply (mkDISJ [mkBEXP (current (the_system_mode)) eq (i 0)]).
  apply theo_rules_disj. reflexivity.
Defined.

Definition req003_sg : EXP.
Proof.
  apply (mkCONJ [req003_sg_disj1; req003_sg_disj2; 
                 req003_sg_disj3; req003_sg_disj4;
                 req003_sg_disj4]).
Defined.

Definition req003_tg_disj1 : DISJ.
Proof.
  apply (mkDISJ [mkBEXP (current (the_request_timer)) gt (n 30)]).
  apply theo_rules_disj. reflexivity.
Defined.

Definition req003_tg : EXP.
Proof.
  apply (mkCONJ [req003_tg_disj1]).
Defined.

Definition req003_asgmt1 : ASGMT.
Proof.
  apply (mkASGMT (the_request_timer, (n 0))).
Defined.

Definition req003_asgmt2 : ASGMT.
Proof.
  apply (mkASGMT (the_system_mode, (i 2))).
Defined.

Definition req003_asgmts : ASGMTS.
Proof.
  apply (mkASGMTS [req003_asgmt1; req003_asgmt2]).
  apply theo_rules_asgmts. reflexivity.
Defined.

(* REQ004 *)
Definition req004_sg_disj1 : DISJ.
Proof.
  apply (mkDISJ [mkBEXP (current (the_system_mode)) eq (i 3)]).
  apply theo_rules_disj. reflexivity.
Defined.

Definition req004_sg : EXP.
Proof.
  apply (mkCONJ [req004_sg_disj1]).
Defined.

Definition req004_tg_disj1 : DISJ.
Proof.
  apply (mkDISJ [mkBEXP (current (the_request_timer)) le (n 30)]).
  apply theo_rules_disj. reflexivity.
Defined.

Definition req004_tg_disj2 : DISJ.
Proof.
  apply (mkDISJ [mkBEXP (current (the_request_timer)) ge (n 10)]).
  apply theo_rules_disj. reflexivity.
Defined.

Definition req004_tg : EXP.
Proof.
  apply (mkCONJ [req004_tg_disj1; req004_tg_disj2]).
Defined.

Definition req004_asgmt1 : ASGMT.
Proof.
  apply (mkASGMT (the_system_mode, (i 1))).
Defined.

Definition req004_asgmt2 : ASGMT.
Proof.
  apply (mkASGMT (the_coffee_machine_output, (i 1))).
Defined.

Definition req004_asgmts : ASGMTS.
Proof.
  apply (mkASGMTS [req004_asgmt1; req004_asgmt2]).
  apply theo_rules_asgmts. reflexivity.
Defined.

(* REQ005 *)
Definition req005_sg_disj1 : DISJ.
Proof.
  apply (mkDISJ [mkBEXP (current (the_system_mode)) eq (i 2)]).
  apply theo_rules_disj. reflexivity.
Defined.

Definition req005_sg : EXP.
Proof.
  apply (mkCONJ [req005_sg_disj1]).
Defined.

Definition req005_tg_disj1 : DISJ.
Proof.
  apply (mkDISJ [mkBEXP (current (the_request_timer)) le (n 50)]).
  apply theo_rules_disj. reflexivity.
Defined.

Definition req005_tg_disj2 : DISJ.
Proof.
  apply (mkDISJ [mkBEXP (current (the_request_timer)) ge (n 30)]).
  apply theo_rules_disj. reflexivity.
Defined.

Definition req005_tg : EXP.
Proof.
  apply (mkCONJ [req005_tg_disj1; req005_tg_disj2]).
Defined.

Definition req005_asgmt1 : ASGMT.
Proof.
  apply (mkASGMT (the_system_mode, (i 1))).
Defined.

Definition req005_asgmt2 : ASGMT.
Proof.
  apply (mkASGMT (the_coffee_machine_output, (i 0))).
Defined.

Definition req005_asgmts : ASGMTS.
Proof.
  apply (mkASGMTS [req005_asgmt1; req005_asgmt2]).
  apply theo_rules_asgmts. reflexivity.
Defined.

(* FUNCTIONS *)
Definition the_coffee_machine_system : FUNCTION.
Proof.
  apply (mkFUNCTION [
            (req001_sg, req001_tg, req001_asgmts, "REQ001");
            (req002_sg, req002_tg, req002_asgmts, "REQ002");
            (req003_sg, req003_tg, req003_asgmts, "REQ003");
            (req004_sg, req004_tg, req004_asgmts, "REQ004");
            (req005_sg, req005_tg, req005_asgmts, "REQ005")
          ]).
  apply theo_rules_function. reflexivity.
Defined.

Definition vm_functions : DFRS_FUNCTIONS.
Proof.
  apply (mkDFRS_FUNCTIONS [the_coffee_machine_system]).
  apply theo_rules_dfrs_functions. reflexivity.
Defined.

(*============ VM: FUNCTIONS ============*)

(*============ VM: S_DFRS ============*)
Definition vm_s_dfrs : s_DFRS.
Proof.
  apply (mkS_DFRS vm_variables vm_s0 vm_functions).
  apply theo_rules_s_dfrs. reflexivity.
Defined.
(*============ VM: S_DFRS ============*)

(* VM : STATES *)

Definition State2 : STATE.
Proof.
  apply (mkSTATE 
         [("the_coin_sensor", (b false, b false));
          ("the_coffee_request_button", (b false, b false));
          ("the_system_mode", (i 1, i 0));
          ("the_coffee_machine_output", (i 0, i 0));
          ("the_request_timer", (n 0, n 0));
          ("gc", (n 0, n 0))]).
  apply theo_rules_state. reflexivity.
Defined.

Definition State3 : STATE.
Proof.
  apply (mkSTATE 
         [("the_coin_sensor", (b false, b false));
          ("the_coffee_request_button", (b false, b false));
          ("the_system_mode", (i 1, i 0));
          ("the_coffee_machine_output", (i 0, i 0));
          ("the_request_timer", (n 0, n 0));
          ("gc", (n 0, n 1))]).
  apply theo_rules_state. reflexivity.
Defined.

Definition State4 : STATE.
Proof.
  apply (mkSTATE 
         [("the_coin_sensor", (b false, b false));
          ("the_coffee_request_button", (b false, b false));
          ("the_system_mode", (i 1, i 0));
          ("the_coffee_machine_output", (i 0, i 0));
          ("the_request_timer", (n 0, n 1));
          ("gc", (n 0, n 1))]).
  apply theo_rules_state. reflexivity.
Defined.

Definition States : STATES.
Proof.
  apply (mkSTATES [vm_state; State2; State3]).
  apply theo_rules_states. reflexivity.
Defined.

Theorem states_empty_theorem :
  fun_rules_states [] = false.
Proof.
  reflexivity.
Qed.

(* VM : STATES *)

(* VM : DFRS_STATES *)

Definition vm_dfrs_states : DFRS_STATES.
Proof.
  apply (mkDFRSSTATES States vm_state).
  apply theo_rules_dfrs_states. reflexivity.
Defined.

(* VM : DFRS_STATES *)

(* VM : TRANS_REL *)

(** well_typed_function_transition VM *)
Definition transitions_fun := func (req001_asgmts, "REQ001").

Definition Asgmt_I1 := mkASGMT (the_coin_sensor, (b false)).

Definition Asgmts_del : ASGMTS.
Proof.
  apply (mkASGMTS [Asgmt_I1]).
  apply theo_rules_asgmts. reflexivity.
Defined.

Definition transitions_del_fail := del (discrete 0, Asgmts_del).

Example test_well_typed_function_transition :
  bwell_typed_function_transition 
    transitions_fun vm_O.(svars) vm_T.(stimers) = true.
Proof.
  reflexivity.
Qed.

Example test_well_typed_function_transition_2 :
  bwell_typed_function_transition 
    transitions_del_fail vm_O.(svars) vm_T.(stimers) = true.
Proof.
  reflexivity.
Qed.

(** well_typed_function_transition VM *)

(** well_typed_delay_transition VM *)

Example test_well_typed_delay_transition :
  bwell_typed_delay_transition
    transitions_del_fail vm_I.(svars) = false.
Proof.
  reflexivity.
Qed.

Example test_well_typed_delay_transition_2 :
  bwell_typed_delay_transition
    transitions_fun vm_I.(svars) = false.
Proof.
  reflexivity.
Qed.

Definition Asgmt_I2 := mkASGMT (the_coffee_request_button, (b false)).

Definition Asgmts_del_2 : ASGMTS.
Proof.
  apply (mkASGMTS [Asgmt_I1; Asgmt_I2]).
  apply theo_rules_asgmts. reflexivity.
Defined.

Definition transitions_del := del (discrete 1, Asgmts_del_2).

Example test_well_typed_delay_transition_3 :
  bwell_typed_delay_transition
    transitions_del vm_I.(svars) = true.
Proof.
  reflexivity.
Qed.

(** well_typed_delay_transition VM *)

(** clock_compatible_transition VM *)

Example test_clock_compatible_transition :
  bclock_compatible_transition transitions_del vm_gcvar = true.
Proof.
  reflexivity.
Qed.

Example test_clock_compatible_transition_2 :
  bclock_compatible_transition transitions_fun vm_gcvar = true.
Proof.
  reflexivity.
Qed.

Definition gcvar_fail1 := ("gc", Tint).

Definition gcvar_fail2 := ("gc", Tbool).

Example test_clock_compatible_transition_3 :
  bclock_compatible_transition transitions_del gcvar_fail1 = false.
Proof.
  reflexivity.
Qed.

Example test_clock_compatible_transition_4 :
  bclock_compatible_transition transitions_del gcvar_fail2 = false.
Proof.
  reflexivity.
Qed.

(** clock_compatible_transition VM *)

(** well_typed_transition VM *)

Example test_well_typed_transition :
  bwell_typed_transition transitions_fun vm_I.(svars) vm_O.(svars)
    vm_T.(stimers) vm_gcvar = true.
Proof.
  reflexivity.
Qed.

Example test_well_typed_transition_2 :
  bwell_typed_transition transitions_del vm_I.(svars) vm_O.(svars)
    vm_T.(stimers) vm_gcvar = true.
Proof.
  reflexivity.
Qed.

Example test_well_typed_transition_3 :
  bwell_typed_transition transitions_del_fail vm_I.(svars) vm_O.(svars)
    vm_T.(stimers) vm_gcvar = false.
Proof.
  reflexivity.
Qed.

Example test_well_typed_transition_4 :
  bwell_typed_transition transitions_del vm_I.(svars) vm_O.(svars)
    vm_T.(stimers) gcvar_fail1 = false.
Proof.
  reflexivity.
Qed.

(** well_typed_transition VM *)

(** DFRS_TRANSITION_RELATION VM *)

Definition tr_func1 := mkTRANS (vm_state, transitions_fun, State2).

Definition tr_func2 := mkTRANS (State2, transitions_fun, State3).

Definition transrel_1 := mkTRANSREL [tr_func1; tr_func2].

Definition dfrs_transrel_1 : DFRS_TRANSITION_RELATION.
Proof.
  apply (mkDFRSTRANSITIONREL transrel_1).
  apply theo_rules_dfrs_trans_rel. reflexivity.
Defined.

Definition tr_del1 := mkTRANS (vm_state, transitions_del, State2).

Definition tr_del2 := mkTRANS (State2, transitions_del, State3).

Definition transrel_2 := mkTRANSREL [tr_del1; tr_del2].

Definition dfrs_transrel_2 : DFRS_TRANSITION_RELATION.
Proof.
  apply (mkDFRSTRANSITIONREL transrel_2).
  apply theo_rules_dfrs_trans_rel. reflexivity.
Defined.

Definition transrel_3 := mkTRANSREL [tr_func1; tr_del2].

Definition dfrs_transrel_3 : DFRS_TRANSITION_RELATION.
Proof.
  apply (mkDFRSTRANSITIONREL transrel_3).
  apply theo_rules_dfrs_trans_rel. reflexivity.
Defined.

Definition transrel_4 := mkTRANSREL [tr_func1; tr_del1].

Example test_fun_rules_dfrs_transition_relation_4 :
  fun_rules_dfrs_trans_rel transrel_4 = false.
Proof.
  reflexivity.
Qed.

Definition vm_dfrs_tr : DFRS_TRANSITION_RELATION.
Proof.
  apply (mkDFRSTRANSITIONREL transrel_3).
  apply theo_rules_dfrs_trans_rel. reflexivity.
Defined.

(* VM : TRANS_REL *)

(* VM : EXPANDED DFRS *)

Definition Asgmt_T1 := mkASGMT (the_request_timer, (n 0)).

Definition Asgmts_del_3 : ASGMTS.
Proof.
  apply (mkASGMTS [Asgmt_I1; Asgmt_I2; Asgmt_T1]).
  apply theo_rules_asgmts. reflexivity.
Defined.

Theorem nextState_theorem_3to4 :
  (beq_state 
    (nextState State3 vm_T.(stimers) Asgmts_del_3)
     State4) = true.
Proof.
  reflexivity.
Qed.

(* Must be false because of the update in gc value *)
Theorem nextState_theorem_2to3 :
  (beq_state 
    (nextState State2 vm_T.(stimers) Asgmts_del_2)
     State3) = false.
Proof.
  reflexivity.
Qed.

Definition expanded_dfrs : e_DFRS.
Proof.
  apply (mkE_DFRS vm_variables vm_dfrs_states vm_dfrs_tr).
  apply theo_rules_e_dfrs. reflexivity.
Defined.

(* VM : EXPANDED DFRS *)

Local Close Scope string.