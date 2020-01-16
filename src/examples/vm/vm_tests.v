Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Local Open Scope string.

Require Import variables.
Require Import variables_fun_ind_equiv.
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

(*============ VARIABLES ============*)

Definition the_coffee_request_button : VNAME.
Proof.
  apply (mkVNAME "the_coffee_request_button").
  apply theo_rules_vname. reflexivity.
Defined.

Definition the_coin_sensor : VNAME.
Proof.
  apply (mkVNAME "the_coin_sensor").
  apply theo_rules_vname. reflexivity.
Defined.

Definition vm_I : SVARS.
Proof.
  apply (mkSVARS [
              (the_coffee_request_button, Tbool)
              ; (the_coin_sensor, Tbool)
        ]).
  apply theo_rules_svars. reflexivity.
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

Definition vm_O : SVARS.
Proof.
  apply (mkSVARS [
              (the_system_mode, Tint)
              ; (the_coffee_machine_output, Tint)
        ]).
  apply theo_rules_svars. reflexivity.
Defined.

Definition the_request_timer : VNAME.
Proof.
  apply (mkVNAME "the_request_timer").
  apply theo_rules_vname. reflexivity.
Defined.

Definition vm_T : STIMERS.
Proof.
  apply (mkSTIMERS [
              (the_request_timer, Tnat)
        ]).
  apply theo_rules_stimers. reflexivity.
Defined.

Definition vm_gcvar := ("gc", Tnat).

Definition vm_variables : DFRS_VARIABLES.
Proof.
  apply (mkDFRS_VARIABLES vm_I vm_O vm_T vm_gcvar).
  apply theo_rules_dfrs_variables. reflexivity.
Defined.

(*============ INITIAL STATE ============*)

Definition VM_state : STATE.
Proof.
  apply (mkSTATE [
              ("the_coffee_request_button", (b false, b false))
              ; ("the_coin_sensor", (b false, b false))
              ; ("the_system_mode", (i 1, i 1))
              ; ("the_coffee_machine_output", (i 0, i 0))
              ; ("the_request_timer", (n 0, n 0))
              ; ("gc", (n 0, n 0))
        ]).
  apply theo_rules_state. reflexivity.
Defined.

Definition vm_s0 : DFRS_INITIAL_STATE.
Proof.
  apply (mkDFRS_INITIAL_STATE VM_state).
Defined.

(*============ FUNCTIONS ============*)

Definition REQ001_sg_disj1 : DISJ.
Proof.
  apply (mkDISJ [
          mkBEXP (previous (the_coin_sensor)) eq (b false)
        ]).
  apply theo_rules_disj. reflexivity.
Defined.

Definition REQ001_sg_disj2 : DISJ.
Proof.
  apply (mkDISJ [
          mkBEXP (current (the_coin_sensor)) eq (b true)
        ]).
  apply theo_rules_disj. reflexivity.
Defined.

Definition REQ001_sg_disj3 : DISJ.
Proof.
  apply (mkDISJ [
          mkBEXP (current (the_system_mode)) eq (i 1)
        ]).
  apply theo_rules_disj. reflexivity.
Defined.

Definition REQ001_sg : EXP.
Proof.
  apply (mkCONJ [
          REQ001_sg_disj1
          ; REQ001_sg_disj2
          ; REQ001_sg_disj3
        ]).
Defined.

Definition REQ001_tg : EXP.
Proof.
  apply (mkCONJ [
        ]).
Defined.

Definition REQ001_asgmt1 : ASGMT.
Proof.
  apply (mkASGMT (the_request_timer, (n 0))).
Defined.

Definition REQ001_asgmt2 : ASGMT.
Proof.
  apply (mkASGMT (the_system_mode, (i 0))).
Defined.

Definition REQ001_asgmts : ASGMTS.
Proof.
  apply (mkASGMTS [
          REQ001_asgmt1
          ; REQ001_asgmt2
        ]).
  apply theo_rules_asgmts. reflexivity.
Defined.

Definition REQ003_sg_disj1 : DISJ.
Proof.
  apply (mkDISJ [
          mkBEXP (previous (the_coffee_request_button)) ne (b true)
        ]).
  apply theo_rules_disj. reflexivity.
Defined.

Definition REQ003_sg_disj2 : DISJ.
Proof.
  apply (mkDISJ [
          mkBEXP (current (the_coffee_request_button)) eq (b true)
        ]).
  apply theo_rules_disj. reflexivity.
Defined.

Definition REQ003_sg_disj3 : DISJ.
Proof.
  apply (mkDISJ [
          mkBEXP (previous (the_coin_sensor)) eq (b false)
        ]).
  apply theo_rules_disj. reflexivity.
Defined.

Definition REQ003_sg_disj4 : DISJ.
Proof.
  apply (mkDISJ [
          mkBEXP (current (the_coin_sensor)) eq (b false)
        ]).
  apply theo_rules_disj. reflexivity.
Defined.

Definition REQ003_sg_disj5 : DISJ.
Proof.
  apply (mkDISJ [
          mkBEXP (current (the_system_mode)) eq (i 0)
        ]).
  apply theo_rules_disj. reflexivity.
Defined.

Definition REQ003_sg : EXP.
Proof.
  apply (mkCONJ [
          REQ003_sg_disj1
          ; REQ003_sg_disj2
          ; REQ003_sg_disj3
          ; REQ003_sg_disj4
          ; REQ003_sg_disj5
        ]).
Defined.

Definition REQ003_tg_disj1 : DISJ.
Proof.
  apply (mkDISJ [
          mkBEXP (current (the_request_timer)) gt (n 30)
        ]).
  apply theo_rules_disj. reflexivity.
Defined.

Definition REQ003_tg : EXP.
Proof.
  apply (mkCONJ [
          REQ003_tg_disj1
        ]).
Defined.

Definition REQ003_asgmt1 : ASGMT.
Proof.
  apply (mkASGMT (the_request_timer, (n 0))).
Defined.

Definition REQ003_asgmt2 : ASGMT.
Proof.
  apply (mkASGMT (the_system_mode, (i 2))).
Defined.

Definition REQ003_asgmts : ASGMTS.
Proof.
  apply (mkASGMTS [
          REQ003_asgmt1
          ; REQ003_asgmt2
        ]).
  apply theo_rules_asgmts. reflexivity.
Defined.

Definition REQ005_sg_disj1 : DISJ.
Proof.
  apply (mkDISJ [
          mkBEXP (current (the_system_mode)) eq (i 2)
        ]).
  apply theo_rules_disj. reflexivity.
Defined.

Definition REQ005_sg : EXP.
Proof.
  apply (mkCONJ [
          REQ005_sg_disj1
        ]).
Defined.

Definition REQ005_tg_disj1 : DISJ.
Proof.
  apply (mkDISJ [
          mkBEXP (current (the_request_timer)) le (n 50)
        ]).
  apply theo_rules_disj. reflexivity.
Defined.

Definition REQ005_tg_disj2 : DISJ.
Proof.
  apply (mkDISJ [
          mkBEXP (current (the_request_timer)) ge (n 30)
        ]).
  apply theo_rules_disj. reflexivity.
Defined.

Definition REQ005_tg : EXP.
Proof.
  apply (mkCONJ [
          REQ005_tg_disj1
          ; REQ005_tg_disj2
        ]).
Defined.

Definition REQ005_asgmt1 : ASGMT.
Proof.
  apply (mkASGMT (the_system_mode, (i 1))).
Defined.

Definition REQ005_asgmt2 : ASGMT.
Proof.
  apply (mkASGMT (the_coffee_machine_output, (i 0))).
Defined.

Definition REQ005_asgmts : ASGMTS.
Proof.
  apply (mkASGMTS [
          REQ005_asgmt1
          ; REQ005_asgmt2
        ]).
  apply theo_rules_asgmts. reflexivity.
Defined.

Definition REQ004_sg_disj1 : DISJ.
Proof.
  apply (mkDISJ [
          mkBEXP (current (the_system_mode)) eq (i 3)
        ]).
  apply theo_rules_disj. reflexivity.
Defined.

Definition REQ004_sg : EXP.
Proof.
  apply (mkCONJ [
          REQ004_sg_disj1
        ]).
Defined.

Definition REQ004_tg_disj1 : DISJ.
Proof.
  apply (mkDISJ [
          mkBEXP (current (the_request_timer)) le (n 30)
        ]).
  apply theo_rules_disj. reflexivity.
Defined.

Definition REQ004_tg_disj2 : DISJ.
Proof.
  apply (mkDISJ [
          mkBEXP (current (the_request_timer)) ge (n 10)
        ]).
  apply theo_rules_disj. reflexivity.
Defined.

Definition REQ004_tg : EXP.
Proof.
  apply (mkCONJ [
          REQ004_tg_disj1
          ; REQ004_tg_disj2
        ]).
Defined.

Definition REQ004_asgmt1 : ASGMT.
Proof.
  apply (mkASGMT (the_system_mode, (i 1))).
Defined.

Definition REQ004_asgmt2 : ASGMT.
Proof.
  apply (mkASGMT (the_coffee_machine_output, (i 1))).
Defined.

Definition REQ004_asgmts : ASGMTS.
Proof.
  apply (mkASGMTS [
          REQ004_asgmt1
          ; REQ004_asgmt2
        ]).
  apply theo_rules_asgmts. reflexivity.
Defined.

Definition REQ002_sg_disj1 : DISJ.
Proof.
  apply (mkDISJ [
          mkBEXP (previous (the_coffee_request_button)) ne (b true)
        ]).
  apply theo_rules_disj. reflexivity.
Defined.

Definition REQ002_sg_disj2 : DISJ.
Proof.
  apply (mkDISJ [
          mkBEXP (current (the_coffee_request_button)) eq (b true)
        ]).
  apply theo_rules_disj. reflexivity.
Defined.

Definition REQ002_sg_disj3 : DISJ.
Proof.
  apply (mkDISJ [
          mkBEXP (previous (the_coin_sensor)) eq (b false)
        ]).
  apply theo_rules_disj. reflexivity.
Defined.

Definition REQ002_sg_disj4 : DISJ.
Proof.
  apply (mkDISJ [
          mkBEXP (current (the_coin_sensor)) eq (b false)
        ]).
  apply theo_rules_disj. reflexivity.
Defined.

Definition REQ002_sg_disj5 : DISJ.
Proof.
  apply (mkDISJ [
          mkBEXP (current (the_system_mode)) eq (i 0)
        ]).
  apply theo_rules_disj. reflexivity.
Defined.

Definition REQ002_sg : EXP.
Proof.
  apply (mkCONJ [
          REQ002_sg_disj1
          ; REQ002_sg_disj2
          ; REQ002_sg_disj3
          ; REQ002_sg_disj4
          ; REQ002_sg_disj5
        ]).
Defined.

Definition REQ002_tg_disj1 : DISJ.
Proof.
  apply (mkDISJ [
          mkBEXP (current (the_request_timer)) le (n 30)
        ]).
  apply theo_rules_disj. reflexivity.
Defined.

Definition REQ002_tg : EXP.
Proof.
  apply (mkCONJ [
          REQ002_tg_disj1
        ]).
Defined.

Definition REQ002_asgmt1 : ASGMT.
Proof.
  apply (mkASGMT (the_request_timer, (n 0))).
Defined.

Definition REQ002_asgmt2 : ASGMT.
Proof.
  apply (mkASGMT (the_system_mode, (i 3))).
Defined.

Definition REQ002_asgmts : ASGMTS.
Proof.
  apply (mkASGMTS [
          REQ002_asgmt1
          ; REQ002_asgmt2
        ]).
  apply theo_rules_asgmts. reflexivity.
Defined.

Definition the_coffee_machine_system : FUNCTION.
Proof.
  apply (mkFUNCTION [
          (REQ001_sg, REQ001_tg, REQ001_asgmts, "REQ001")
          ; (REQ003_sg, REQ003_tg, REQ003_asgmts, "REQ003")
          ; (REQ005_sg, REQ005_tg, REQ005_asgmts, "REQ005")
          ; (REQ004_sg, REQ004_tg, REQ004_asgmts, "REQ004")
          ; (REQ002_sg, REQ002_tg, REQ002_asgmts, "REQ002")
        ]).
  apply theo_rules_function. reflexivity.
Defined.

Definition vm_functions : DFRS_FUNCTIONS.
Proof.
  apply (mkDFRS_FUNCTIONS [
          the_coffee_machine_system
        ]).
  apply theo_rules_dfrs_functions. reflexivity.
Defined.

(*============ VM: S_DFRS ============*)
Definition VM_s_dfrs : s_DFRS.
Proof.
  apply (mkS_DFRS vm_variables vm_s0 vm_functions).
  apply theo_rules_s_dfrs. reflexivity.
Defined.
(*============ VM: S_DFRS ============*)

Local Close Scope string.
