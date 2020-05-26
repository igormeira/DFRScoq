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

Definition the_reset_button : VNAME.
Proof.
  apply (mkVNAME "the_reset_button").
  apply theo_rules_vname. reflexivity.
Defined.

Definition the_blockage_button : VNAME.
Proof.
  apply (mkVNAME "the_blockage_button").
  apply theo_rules_vname. reflexivity.
Defined.

Definition the_water_pressure : VNAME.
Proof.
  apply (mkVNAME "the_water_pressure").
  apply theo_rules_vname. reflexivity.
Defined.

Definition npp_I : SVARS.
Proof.
  apply (mkSVARS [
              (the_reset_button, Tbool)
              ; (the_blockage_button, Tbool)
              ; (the_water_pressure, Tint)
        ]).
  apply theo_rules_svars. reflexivity.
Defined.

Definition the_safety_injection_mode : VNAME.
Proof.
  apply (mkVNAME "the_safety_injection_mode").
  apply theo_rules_vname. reflexivity.
Defined.

Definition the_overridden_mode : VNAME.
Proof.
  apply (mkVNAME "the_overridden_mode").
  apply theo_rules_vname. reflexivity.
Defined.

Definition the_pressure_mode : VNAME.
Proof.
  apply (mkVNAME "the_pressure_mode").
  apply theo_rules_vname. reflexivity.
Defined.

Definition npp_O : SVARS.
Proof.
  apply (mkSVARS [
              (the_safety_injection_mode, Tint)
              ; (the_overridden_mode, Tbool)
              ; (the_pressure_mode, Tint)
        ]).
  apply theo_rules_svars. reflexivity.
Defined.

Definition npp_T : STIMERS.
Proof.
  apply (mkSTIMERS [
        ]).
  apply theo_rules_stimers. reflexivity.
Defined.

Definition npp_gcvar := ("gc", Tnat).

Definition npp_variables : DFRS_VARIABLES.
Proof.
  apply (mkDFRS_VARIABLES npp_I npp_O npp_T npp_gcvar).
  apply theo_rules_dfrs_variables. reflexivity.
Defined.

(*============ INITIAL STATE ============*)

Definition npp_state : STATE.
Proof.
  apply (mkSTATE [
              ("the_reset_button", (b false, b false))
              ; ("the_blockage_button", (b false, b false))
              ; ("the_water_pressure", (i 0, i 0))
              ; ("the_safety_injection_mode", (i 1, i 1))
              ; ("the_overridden_mode", (b false, b false))
              ; ("the_pressure_mode", (i 1, i 1))
              ; ("gc", (n 0, n 0))
        ]).
  apply theo_rules_state. reflexivity.
Defined.

Definition npp_s0 : DFRS_INITIAL_STATE.
Proof.
  apply (mkDFRS_INITIAL_STATE npp_state).
Defined.

(*============ FUNCTIONS ============*)

Definition REQ004_sg_disj1 : DISJ.
Proof.
  apply (mkDISJ [
          mkBEXP (current (the_pressure_mode)) eq (i 0)
        ]).
  apply theo_rules_disj. reflexivity.
Defined.

Definition REQ004_sg_disj2 : DISJ.
Proof.
  apply (mkDISJ [
          mkBEXP (previous (the_water_pressure)) ge (i 10)
        ]).
  apply theo_rules_disj. reflexivity.
Defined.

Definition REQ004_sg_disj3 : DISJ.
Proof.
  apply (mkDISJ [
          mkBEXP (current (the_water_pressure)) lt (i 10)
        ]).
  apply theo_rules_disj. reflexivity.
Defined.

Definition REQ004_sg : EXP.
Proof.
  apply (mkCONJ [
          REQ004_sg_disj1
          ; REQ004_sg_disj2
          ; REQ004_sg_disj3
        ]).
Defined.

Definition REQ004_tg : EXP.
Proof.
  apply (mkCONJ [
        ]).
Defined.

Definition REQ004_asgmt1 : ASGMT.
Proof.
  apply (mkASGMT (the_pressure_mode, (i 2))).
Defined.

Definition REQ004_asgmts : ASGMTS.
Proof.
  apply (mkASGMTS [
          REQ004_asgmt1
        ]).
  apply theo_rules_asgmts. reflexivity.
Defined.

Definition REQ006_sg_disj1 : DISJ.
Proof.
  apply (mkDISJ [
          mkBEXP (current (the_pressure_mode)) ne (i 0)
        ]).
  apply theo_rules_disj. reflexivity.
Defined.

Definition REQ006_sg_disj2 : DISJ.
Proof.
  apply (mkDISJ [
          mkBEXP (previous (the_reset_button)) ne (b true)
        ]).
  apply theo_rules_disj. reflexivity.
Defined.

Definition REQ006_sg_disj3 : DISJ.
Proof.
  apply (mkDISJ [
          mkBEXP (current (the_reset_button)) eq (b true)
        ]).
  apply theo_rules_disj. reflexivity.
Defined.

Definition REQ006_sg : EXP.
Proof.
  apply (mkCONJ [
          REQ006_sg_disj1
          ; REQ006_sg_disj2
          ; REQ006_sg_disj3
        ]).
Defined.

Definition REQ006_tg : EXP.
Proof.
  apply (mkCONJ [
        ]).
Defined.

Definition REQ006_asgmt1 : ASGMT.
Proof.
  apply (mkASGMT (the_overridden_mode, (b false))).
Defined.

Definition REQ006_asgmts : ASGMTS.
Proof.
  apply (mkASGMTS [
          REQ006_asgmt1
        ]).
  apply theo_rules_asgmts. reflexivity.
Defined.

Definition REQ011_sg_disj1 : DISJ.
Proof.
  apply (mkDISJ [
          mkBEXP (current (the_pressure_mode)) eq (i 0)
          ; mkBEXP (current (the_pressure_mode)) eq (i 2)
        ]).
  apply theo_rules_disj. reflexivity.
Defined.

Definition REQ011_sg : EXP.
Proof.
  apply (mkCONJ [
          REQ011_sg_disj1
        ]).
Defined.

Definition REQ011_tg : EXP.
Proof.
  apply (mkCONJ [
        ]).
Defined.

Definition REQ011_asgmt1 : ASGMT.
Proof.
  apply (mkASGMT (the_safety_injection_mode, (i 0))).
Defined.

Definition REQ011_asgmts : ASGMTS.
Proof.
  apply (mkASGMTS [
          REQ011_asgmt1
        ]).
  apply theo_rules_asgmts. reflexivity.
Defined.

Definition REQ009_sg_disj1 : DISJ.
Proof.
  apply (mkDISJ [
          mkBEXP (current (the_overridden_mode)) eq (b true)
        ]).
  apply theo_rules_disj. reflexivity.
Defined.

Definition REQ009_sg_disj2 : DISJ.
Proof.
  apply (mkDISJ [
          mkBEXP (current (the_pressure_mode)) eq (i 1)
        ]).
  apply theo_rules_disj. reflexivity.
Defined.

Definition REQ009_sg : EXP.
Proof.
  apply (mkCONJ [
          REQ009_sg_disj1
          ; REQ009_sg_disj2
        ]).
Defined.

Definition REQ009_tg : EXP.
Proof.
  apply (mkCONJ [
        ]).
Defined.

Definition REQ009_asgmt1 : ASGMT.
Proof.
  apply (mkASGMT (the_safety_injection_mode, (i 0))).
Defined.

Definition REQ009_asgmts : ASGMTS.
Proof.
  apply (mkASGMTS [
          REQ009_asgmt1
        ]).
  apply theo_rules_asgmts. reflexivity.
Defined.

Definition REQ003_sg_disj1 : DISJ.
Proof.
  apply (mkDISJ [
          mkBEXP (current (the_pressure_mode)) eq (i 2)
        ]).
  apply theo_rules_disj. reflexivity.
Defined.

Definition REQ003_sg_disj2 : DISJ.
Proof.
  apply (mkDISJ [
          mkBEXP (previous (the_water_pressure)) ge (i 9)
        ]).
  apply theo_rules_disj. reflexivity.
Defined.

Definition REQ003_sg_disj3 : DISJ.
Proof.
  apply (mkDISJ [
          mkBEXP (current (the_water_pressure)) lt (i 9)
        ]).
  apply theo_rules_disj. reflexivity.
Defined.

Definition REQ003_sg : EXP.
Proof.
  apply (mkCONJ [
          REQ003_sg_disj1
          ; REQ003_sg_disj2
          ; REQ003_sg_disj3
        ]).
Defined.

Definition REQ003_tg : EXP.
Proof.
  apply (mkCONJ [
        ]).
Defined.

Definition REQ003_asgmt1 : ASGMT.
Proof.
  apply (mkASGMT (the_pressure_mode, (i 1))).
Defined.

Definition REQ003_asgmts : ASGMTS.
Proof.
  apply (mkASGMTS [
          REQ003_asgmt1
        ]).
  apply theo_rules_asgmts. reflexivity.
Defined.

Definition REQ008_sg_disj1 : DISJ.
Proof.
  apply (mkDISJ [
          mkBEXP (previous (the_pressure_mode)) eq (i 0)
        ]).
  apply theo_rules_disj. reflexivity.
Defined.

Definition REQ008_sg_disj2 : DISJ.
Proof.
  apply (mkDISJ [
          mkBEXP (current (the_pressure_mode)) ne (i 0)
        ]).
  apply theo_rules_disj. reflexivity.
Defined.

Definition REQ008_sg : EXP.
Proof.
  apply (mkCONJ [
          REQ008_sg_disj1
          ; REQ008_sg_disj2
        ]).
Defined.

Definition REQ008_tg : EXP.
Proof.
  apply (mkCONJ [
        ]).
Defined.

Definition REQ008_asgmt1 : ASGMT.
Proof.
  apply (mkASGMT (the_overridden_mode, (b false))).
Defined.

Definition REQ008_asgmts : ASGMTS.
Proof.
  apply (mkASGMTS [
          REQ008_asgmt1
        ]).
  apply theo_rules_asgmts. reflexivity.
Defined.

Definition REQ002_sg_disj1 : DISJ.
Proof.
  apply (mkDISJ [
          mkBEXP (current (the_pressure_mode)) eq (i 2)
        ]).
  apply theo_rules_disj. reflexivity.
Defined.

Definition REQ002_sg_disj2 : DISJ.
Proof.
  apply (mkDISJ [
          mkBEXP (previous (the_water_pressure)) lt (i 10)
        ]).
  apply theo_rules_disj. reflexivity.
Defined.

Definition REQ002_sg_disj3 : DISJ.
Proof.
  apply (mkDISJ [
          mkBEXP (current (the_water_pressure)) ge (i 10)
        ]).
  apply theo_rules_disj. reflexivity.
Defined.

Definition REQ002_sg : EXP.
Proof.
  apply (mkCONJ [
          REQ002_sg_disj1
          ; REQ002_sg_disj2
          ; REQ002_sg_disj3
        ]).
Defined.

Definition REQ002_tg : EXP.
Proof.
  apply (mkCONJ [
        ]).
Defined.

Definition REQ002_asgmt1 : ASGMT.
Proof.
  apply (mkASGMT (the_pressure_mode, (i 0))).
Defined.

Definition REQ002_asgmts : ASGMTS.
Proof.
  apply (mkASGMTS [
          REQ002_asgmt1
        ]).
  apply theo_rules_asgmts. reflexivity.
Defined.

Definition REQ007_sg_disj1 : DISJ.
Proof.
  apply (mkDISJ [
          mkBEXP (previous (the_pressure_mode)) ne (i 0)
        ]).
  apply theo_rules_disj. reflexivity.
Defined.

Definition REQ007_sg_disj2 : DISJ.
Proof.
  apply (mkDISJ [
          mkBEXP (current (the_pressure_mode)) eq (i 0)
        ]).
  apply theo_rules_disj. reflexivity.
Defined.

Definition REQ007_sg : EXP.
Proof.
  apply (mkCONJ [
          REQ007_sg_disj1
          ; REQ007_sg_disj2
        ]).
Defined.

Definition REQ007_tg : EXP.
Proof.
  apply (mkCONJ [
        ]).
Defined.

Definition REQ007_asgmt1 : ASGMT.
Proof.
  apply (mkASGMT (the_overridden_mode, (b false))).
Defined.

Definition REQ007_asgmts : ASGMTS.
Proof.
  apply (mkASGMTS [
          REQ007_asgmt1
        ]).
  apply theo_rules_asgmts. reflexivity.
Defined.

Definition REQ001_sg_disj1 : DISJ.
Proof.
  apply (mkDISJ [
          mkBEXP (current (the_pressure_mode)) eq (i 1)
        ]).
  apply theo_rules_disj. reflexivity.
Defined.

Definition REQ001_sg_disj2 : DISJ.
Proof.
  apply (mkDISJ [
          mkBEXP (previous (the_water_pressure)) lt (i 9)
        ]).
  apply theo_rules_disj. reflexivity.
Defined.

Definition REQ001_sg_disj3 : DISJ.
Proof.
  apply (mkDISJ [
          mkBEXP (current (the_water_pressure)) ge (i 9)
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
  apply (mkASGMT (the_pressure_mode, (i 2))).
Defined.

Definition REQ001_asgmts : ASGMTS.
Proof.
  apply (mkASGMTS [
          REQ001_asgmt1
        ]).
  apply theo_rules_asgmts. reflexivity.
Defined.

Definition REQ005_sg_disj1 : DISJ.
Proof.
  apply (mkDISJ [
          mkBEXP (current (the_pressure_mode)) ne (i 0)
        ]).
  apply theo_rules_disj. reflexivity.
Defined.

Definition REQ005_sg_disj2 : DISJ.
Proof.
  apply (mkDISJ [
          mkBEXP (current (the_reset_button)) ne (b true)
        ]).
  apply theo_rules_disj. reflexivity.
Defined.

Definition REQ005_sg_disj3 : DISJ.
Proof.
  apply (mkDISJ [
          mkBEXP (previous (the_blockage_button)) ne (b true)
        ]).
  apply theo_rules_disj. reflexivity.
Defined.

Definition REQ005_sg_disj4 : DISJ.
Proof.
  apply (mkDISJ [
          mkBEXP (current (the_blockage_button)) eq (b true)
        ]).
  apply theo_rules_disj. reflexivity.
Defined.

Definition REQ005_sg : EXP.
Proof.
  apply (mkCONJ [
          REQ005_sg_disj1
          ; REQ005_sg_disj2
          ; REQ005_sg_disj3
          ; REQ005_sg_disj4
        ]).
Defined.

Definition REQ005_tg : EXP.
Proof.
  apply (mkCONJ [
        ]).
Defined.

Definition REQ005_asgmt1 : ASGMT.
Proof.
  apply (mkASGMT (the_overridden_mode, (b true))).
Defined.

Definition REQ005_asgmts : ASGMTS.
Proof.
  apply (mkASGMTS [
          REQ005_asgmt1
        ]).
  apply theo_rules_asgmts. reflexivity.
Defined.

Definition REQ010_sg_disj1 : DISJ.
Proof.
  apply (mkDISJ [
          mkBEXP (current (the_overridden_mode)) eq (b false)
        ]).
  apply theo_rules_disj. reflexivity.
Defined.

Definition REQ010_sg_disj2 : DISJ.
Proof.
  apply (mkDISJ [
          mkBEXP (current (the_pressure_mode)) eq (i 1)
        ]).
  apply theo_rules_disj. reflexivity.
Defined.

Definition REQ010_sg : EXP.
Proof.
  apply (mkCONJ [
          REQ010_sg_disj1
          ; REQ010_sg_disj2
        ]).
Defined.

Definition REQ010_tg : EXP.
Proof.
  apply (mkCONJ [
        ]).
Defined.

Definition REQ010_asgmt1 : ASGMT.
Proof.
  apply (mkASGMT (the_safety_injection_mode, (i 1))).
Defined.

Definition REQ010_asgmts : ASGMTS.
Proof.
  apply (mkASGMTS [
          REQ010_asgmt1
        ]).
  apply theo_rules_asgmts. reflexivity.
Defined.

Definition the_safety_injection_system : FUNCTION.
Proof.
  apply (mkFUNCTION [
          (REQ004_sg, REQ004_tg, REQ004_asgmts, "REQ004")
          ; (REQ006_sg, REQ006_tg, REQ006_asgmts, "REQ006")
          ; (REQ011_sg, REQ011_tg, REQ011_asgmts, "REQ011")
          ; (REQ009_sg, REQ009_tg, REQ009_asgmts, "REQ009")
          ; (REQ003_sg, REQ003_tg, REQ003_asgmts, "REQ003")
          ; (REQ008_sg, REQ008_tg, REQ008_asgmts, "REQ008")
          ; (REQ002_sg, REQ002_tg, REQ002_asgmts, "REQ002")
          ; (REQ007_sg, REQ007_tg, REQ007_asgmts, "REQ007")
          ; (REQ001_sg, REQ001_tg, REQ001_asgmts, "REQ001")
          ; (REQ005_sg, REQ005_tg, REQ005_asgmts, "REQ005")
          ; (REQ010_sg, REQ010_tg, REQ010_asgmts, "REQ010")
        ]).
  apply theo_rules_function. reflexivity.
Defined.

Definition npp_functions : DFRS_FUNCTIONS.
Proof.
  apply (mkDFRS_FUNCTIONS [
          the_safety_injection_system
        ]).
  apply theo_rules_dfrs_functions. reflexivity.
Defined.

(*============ NPP: S_DFRS ============*)
Definition npp_s_dfrs : s_DFRS.
Proof.
  apply (mkS_DFRS npp_variables npp_s0 npp_functions).
  apply theo_rules_s_dfrs. reflexivity.
Defined.
(*============ NPP: S_DFRS ============*)

Local Close Scope string.
