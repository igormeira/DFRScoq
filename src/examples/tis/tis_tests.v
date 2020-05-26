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

Definition the_voltage : VNAME.
Proof.
  apply (mkVNAME "the_voltage").
  apply theo_rules_vname. reflexivity.
Defined.

Definition the_turn_indicator_lever : VNAME.
Proof.
  apply (mkVNAME "the_turn_indicator_lever").
  apply theo_rules_vname. reflexivity.
Defined.

Definition the_emergency_flashing : VNAME.
Proof.
  apply (mkVNAME "the_emergency_flashing").
  apply theo_rules_vname. reflexivity.
Defined.

Definition tis_I : SVARS.
Proof.
  apply (mkSVARS [
              (the_voltage, Tint)
              ; (the_turn_indicator_lever, Tint)
              ; (the_emergency_flashing, Tint)
        ]).
  apply theo_rules_svars. reflexivity.
Defined.

Definition the_indication_lights : VNAME.
Proof.
  apply (mkVNAME "the_indication_lights").
  apply theo_rules_vname. reflexivity.
Defined.

Definition the_flashing_mode : VNAME.
Proof.
  apply (mkVNAME "the_flashing_mode").
  apply theo_rules_vname. reflexivity.
Defined.

Definition tis_O : SVARS.
Proof.
  apply (mkSVARS [
              (the_indication_lights, Tint)
              ; (the_flashing_mode, Tint)
        ]).
  apply theo_rules_svars. reflexivity.
Defined.

Definition the_flashing_timer : VNAME.
Proof.
  apply (mkVNAME "the_flashing_timer").
  apply theo_rules_vname. reflexivity.
Defined.

Definition tis_T : STIMERS.
Proof.
  apply (mkSTIMERS [
              (the_flashing_timer, Tnat)
        ]).
  apply theo_rules_stimers. reflexivity.
Defined.

Definition tis_gcvar := ("gc", Tnat).

Definition tis_variables : DFRS_VARIABLES.
Proof.
  apply (mkDFRS_VARIABLES tis_I tis_O tis_T tis_gcvar).
  apply theo_rules_dfrs_variables. reflexivity.
Defined.

(*============ INITIAL STATE ============*)

Definition tis_state : STATE.
Proof.
  apply (mkSTATE [
              ("the_voltage", (i 0, i 0))
              ; ("the_turn_indicator_lever", (i 0, i 0))
              ; ("the_emergency_flashing", (i 0, i 0))
              ; ("the_indication_lights", (i 2, i 2))
              ; ("the_flashing_mode", (i 2, i 2))
              ; ("the_flashing_timer", (n 0, n 0))
              ; ("gc", (n 0, n 0))
        ]).
  apply theo_rules_state. reflexivity.
Defined.

Definition tis_s0 : DFRS_INITIAL_STATE.
Proof.
  apply (mkDFRS_INITIAL_STATE tis_state).
Defined.

(*============ FUNCTIONS ============*)

Definition REQ015_sg_disj1 : DISJ.
Proof.
  apply (mkDISJ [
          mkBEXP (current (the_flashing_mode)) ne (i 0)
        ]).
  apply theo_rules_disj. reflexivity.
Defined.

Definition REQ015_sg_disj2 : DISJ.
Proof.
  apply (mkDISJ [
          mkBEXP (previous (the_turn_indicator_lever)) ne (i 0)
        ]).
  apply theo_rules_disj. reflexivity.
Defined.

Definition REQ015_sg_disj3 : DISJ.
Proof.
  apply (mkDISJ [
          mkBEXP (current (the_turn_indicator_lever)) eq (i 0)
        ]).
  apply theo_rules_disj. reflexivity.
Defined.

Definition REQ015_sg_disj4 : DISJ.
Proof.
  apply (mkDISJ [
          mkBEXP (previous (the_emergency_flashing)) eq (i 1)
        ]).
  apply theo_rules_disj. reflexivity.
Defined.

Definition REQ015_sg_disj5 : DISJ.
Proof.
  apply (mkDISJ [
          mkBEXP (current (the_emergency_flashing)) eq (i 1)
        ]).
  apply theo_rules_disj. reflexivity.
Defined.

Definition REQ015_sg : EXP.
Proof.
  apply (mkCONJ [
          REQ015_sg_disj1
          ; REQ015_sg_disj2
          ; REQ015_sg_disj3
          ; REQ015_sg_disj4
          ; REQ015_sg_disj5
        ]).
Defined.

Definition REQ015_tg : EXP.
Proof.
  apply (mkCONJ [
        ]).
Defined.

Definition REQ015_asgmt1 : ASGMT.
Proof.
  apply (mkASGMT (the_flashing_mode, (i 0))).
Defined.

Definition REQ015_asgmt2 : ASGMT.
Proof.
  apply (mkASGMT (the_flashing_timer, (n 0))).
Defined.

Definition REQ015_asgmts : ASGMTS.
Proof.
  apply (mkASGMTS [
          REQ015_asgmt1
          ; REQ015_asgmt2
        ]).
  apply theo_rules_asgmts. reflexivity.
Defined.

Definition REQ013_sg_disj1 : DISJ.
Proof.
  apply (mkDISJ [
          mkBEXP (previous (the_turn_indicator_lever)) ne (i 1)
        ]).
  apply theo_rules_disj. reflexivity.
Defined.

Definition REQ013_sg_disj2 : DISJ.
Proof.
  apply (mkDISJ [
          mkBEXP (current (the_turn_indicator_lever)) eq (i 1)
        ]).
  apply theo_rules_disj. reflexivity.
Defined.

Definition REQ013_sg_disj3 : DISJ.
Proof.
  apply (mkDISJ [
          mkBEXP (previous (the_emergency_flashing)) eq (i 1)
        ]).
  apply theo_rules_disj. reflexivity.
Defined.

Definition REQ013_sg_disj4 : DISJ.
Proof.
  apply (mkDISJ [
          mkBEXP (current (the_emergency_flashing)) eq (i 1)
        ]).
  apply theo_rules_disj. reflexivity.
Defined.

Definition REQ013_sg : EXP.
Proof.
  apply (mkCONJ [
          REQ013_sg_disj1
          ; REQ013_sg_disj2
          ; REQ013_sg_disj3
          ; REQ013_sg_disj4
        ]).
Defined.

Definition REQ013_tg : EXP.
Proof.
  apply (mkCONJ [
        ]).
Defined.

Definition REQ013_asgmt1 : ASGMT.
Proof.
  apply (mkASGMT (the_flashing_mode, (i 1))).
Defined.

Definition REQ013_asgmt2 : ASGMT.
Proof.
  apply (mkASGMT (the_flashing_timer, (n 0))).
Defined.

Definition REQ013_asgmts : ASGMTS.
Proof.
  apply (mkASGMTS [
          REQ013_asgmt1
          ; REQ013_asgmt2
        ]).
  apply theo_rules_asgmts. reflexivity.
Defined.

Definition REQ014_sg_disj1 : DISJ.
Proof.
  apply (mkDISJ [
          mkBEXP (previous (the_turn_indicator_lever)) ne (i 2)
        ]).
  apply theo_rules_disj. reflexivity.
Defined.

Definition REQ014_sg_disj2 : DISJ.
Proof.
  apply (mkDISJ [
          mkBEXP (current (the_turn_indicator_lever)) eq (i 2)
        ]).
  apply theo_rules_disj. reflexivity.
Defined.

Definition REQ014_sg_disj3 : DISJ.
Proof.
  apply (mkDISJ [
          mkBEXP (previous (the_emergency_flashing)) eq (i 1)
        ]).
  apply theo_rules_disj. reflexivity.
Defined.

Definition REQ014_sg_disj4 : DISJ.
Proof.
  apply (mkDISJ [
          mkBEXP (current (the_emergency_flashing)) eq (i 1)
        ]).
  apply theo_rules_disj. reflexivity.
Defined.

Definition REQ014_sg : EXP.
Proof.
  apply (mkCONJ [
          REQ014_sg_disj1
          ; REQ014_sg_disj2
          ; REQ014_sg_disj3
          ; REQ014_sg_disj4
        ]).
Defined.

Definition REQ014_tg : EXP.
Proof.
  apply (mkCONJ [
        ]).
Defined.

Definition REQ014_asgmt1 : ASGMT.
Proof.
  apply (mkASGMT (the_flashing_mode, (i 3))).
Defined.

Definition REQ014_asgmt2 : ASGMT.
Proof.
  apply (mkASGMT (the_flashing_timer, (n 0))).
Defined.

Definition REQ014_asgmts : ASGMTS.
Proof.
  apply (mkASGMTS [
          REQ014_asgmt1
          ; REQ014_asgmt2
        ]).
  apply theo_rules_asgmts. reflexivity.
Defined.

Definition REQ016_sg_disj1 : DISJ.
Proof.
  apply (mkDISJ [
          mkBEXP (current (the_flashing_mode)) ne (i 1)
        ]).
  apply theo_rules_disj. reflexivity.
Defined.

Definition REQ016_sg_disj2 : DISJ.
Proof.
  apply (mkDISJ [
          mkBEXP (previous (the_turn_indicator_lever)) eq (i 1)
        ]).
  apply theo_rules_disj. reflexivity.
Defined.

Definition REQ016_sg_disj3 : DISJ.
Proof.
  apply (mkDISJ [
          mkBEXP (current (the_turn_indicator_lever)) eq (i 1)
        ]).
  apply theo_rules_disj. reflexivity.
Defined.

Definition REQ016_sg_disj4 : DISJ.
Proof.
  apply (mkDISJ [
          mkBEXP (previous (the_emergency_flashing)) ne (i 0)
        ]).
  apply theo_rules_disj. reflexivity.
Defined.

Definition REQ016_sg_disj5 : DISJ.
Proof.
  apply (mkDISJ [
          mkBEXP (current (the_emergency_flashing)) eq (i 0)
        ]).
  apply theo_rules_disj. reflexivity.
Defined.

Definition REQ016_sg : EXP.
Proof.
  apply (mkCONJ [
          REQ016_sg_disj1
          ; REQ016_sg_disj2
          ; REQ016_sg_disj3
          ; REQ016_sg_disj4
          ; REQ016_sg_disj5
        ]).
Defined.

Definition REQ016_tg : EXP.
Proof.
  apply (mkCONJ [
        ]).
Defined.

Definition REQ016_asgmt1 : ASGMT.
Proof.
  apply (mkASGMT (the_flashing_mode, (i 1))).
Defined.

Definition REQ016_asgmt2 : ASGMT.
Proof.
  apply (mkASGMT (the_flashing_timer, (n 0))).
Defined.

Definition REQ016_asgmts : ASGMTS.
Proof.
  apply (mkASGMTS [
          REQ016_asgmt1
          ; REQ016_asgmt2
        ]).
  apply theo_rules_asgmts. reflexivity.
Defined.

Definition REQ011_sg_disj1 : DISJ.
Proof.
  apply (mkDISJ [
          mkBEXP (current (the_emergency_flashing)) eq (i 0)
        ]).
  apply theo_rules_disj. reflexivity.
Defined.

Definition REQ011_sg_disj2 : DISJ.
Proof.
  apply (mkDISJ [
          mkBEXP (previous (the_turn_indicator_lever)) ne (i 2)
        ]).
  apply theo_rules_disj. reflexivity.
Defined.

Definition REQ011_sg_disj3 : DISJ.
Proof.
  apply (mkDISJ [
          mkBEXP (current (the_turn_indicator_lever)) eq (i 2)
        ]).
  apply theo_rules_disj. reflexivity.
Defined.

Definition REQ011_sg : EXP.
Proof.
  apply (mkCONJ [
          REQ011_sg_disj1
          ; REQ011_sg_disj2
          ; REQ011_sg_disj3
        ]).
Defined.

Definition REQ011_tg : EXP.
Proof.
  apply (mkCONJ [
        ]).
Defined.

Definition REQ011_asgmt1 : ASGMT.
Proof.
  apply (mkASGMT (the_flashing_mode, (i 3))).
Defined.

Definition REQ011_asgmt2 : ASGMT.
Proof.
  apply (mkASGMT (the_flashing_timer, (n 0))).
Defined.

Definition REQ011_asgmts : ASGMTS.
Proof.
  apply (mkASGMTS [
          REQ011_asgmt1
          ; REQ011_asgmt2
        ]).
  apply theo_rules_asgmts. reflexivity.
Defined.

Definition REQ012_sg_disj1 : DISJ.
Proof.
  apply (mkDISJ [
          mkBEXP (previous (the_emergency_flashing)) ne (i 1)
        ]).
  apply theo_rules_disj. reflexivity.
Defined.

Definition REQ012_sg_disj2 : DISJ.
Proof.
  apply (mkDISJ [
          mkBEXP (current (the_emergency_flashing)) eq (i 1)
        ]).
  apply theo_rules_disj. reflexivity.
Defined.

Definition REQ012_sg : EXP.
Proof.
  apply (mkCONJ [
          REQ012_sg_disj1
          ; REQ012_sg_disj2
        ]).
Defined.

Definition REQ012_tg : EXP.
Proof.
  apply (mkCONJ [
        ]).
Defined.

Definition REQ012_asgmt1 : ASGMT.
Proof.
  apply (mkASGMT (the_flashing_mode, (i 0))).
Defined.

Definition REQ012_asgmt2 : ASGMT.
Proof.
  apply (mkASGMT (the_flashing_timer, (n 0))).
Defined.

Definition REQ012_asgmts : ASGMTS.
Proof.
  apply (mkASGMTS [
          REQ012_asgmt1
          ; REQ012_asgmt2
        ]).
  apply theo_rules_asgmts. reflexivity.
Defined.

Definition REQ010_sg_disj1 : DISJ.
Proof.
  apply (mkDISJ [
          mkBEXP (current (the_emergency_flashing)) eq (i 0)
        ]).
  apply theo_rules_disj. reflexivity.
Defined.

Definition REQ010_sg_disj2 : DISJ.
Proof.
  apply (mkDISJ [
          mkBEXP (previous (the_turn_indicator_lever)) ne (i 1)
        ]).
  apply theo_rules_disj. reflexivity.
Defined.

Definition REQ010_sg_disj3 : DISJ.
Proof.
  apply (mkDISJ [
          mkBEXP (current (the_turn_indicator_lever)) eq (i 1)
        ]).
  apply theo_rules_disj. reflexivity.
Defined.

Definition REQ010_sg : EXP.
Proof.
  apply (mkCONJ [
          REQ010_sg_disj1
          ; REQ010_sg_disj2
          ; REQ010_sg_disj3
        ]).
Defined.

Definition REQ010_tg : EXP.
Proof.
  apply (mkCONJ [
        ]).
Defined.

Definition REQ010_asgmt1 : ASGMT.
Proof.
  apply (mkASGMT (the_flashing_mode, (i 1))).
Defined.

Definition REQ010_asgmt2 : ASGMT.
Proof.
  apply (mkASGMT (the_flashing_timer, (n 0))).
Defined.

Definition REQ010_asgmts : ASGMTS.
Proof.
  apply (mkASGMTS [
          REQ010_asgmt1
          ; REQ010_asgmt2
        ]).
  apply theo_rules_asgmts. reflexivity.
Defined.

Definition REQ017_sg_disj1 : DISJ.
Proof.
  apply (mkDISJ [
          mkBEXP (current (the_flashing_mode)) ne (i 3)
        ]).
  apply theo_rules_disj. reflexivity.
Defined.

Definition REQ017_sg_disj2 : DISJ.
Proof.
  apply (mkDISJ [
          mkBEXP (previous (the_turn_indicator_lever)) eq (i 2)
        ]).
  apply theo_rules_disj. reflexivity.
Defined.

Definition REQ017_sg_disj3 : DISJ.
Proof.
  apply (mkDISJ [
          mkBEXP (current (the_turn_indicator_lever)) eq (i 2)
        ]).
  apply theo_rules_disj. reflexivity.
Defined.

Definition REQ017_sg_disj4 : DISJ.
Proof.
  apply (mkDISJ [
          mkBEXP (previous (the_emergency_flashing)) ne (i 0)
        ]).
  apply theo_rules_disj. reflexivity.
Defined.

Definition REQ017_sg_disj5 : DISJ.
Proof.
  apply (mkDISJ [
          mkBEXP (current (the_emergency_flashing)) eq (i 0)
        ]).
  apply theo_rules_disj. reflexivity.
Defined.

Definition REQ017_sg : EXP.
Proof.
  apply (mkCONJ [
          REQ017_sg_disj1
          ; REQ017_sg_disj2
          ; REQ017_sg_disj3
          ; REQ017_sg_disj4
          ; REQ017_sg_disj5
        ]).
Defined.

Definition REQ017_tg : EXP.
Proof.
  apply (mkCONJ [
        ]).
Defined.

Definition REQ017_asgmt1 : ASGMT.
Proof.
  apply (mkASGMT (the_flashing_mode, (i 3))).
Defined.

Definition REQ017_asgmt2 : ASGMT.
Proof.
  apply (mkASGMT (the_flashing_timer, (n 0))).
Defined.

Definition REQ017_asgmts : ASGMTS.
Proof.
  apply (mkASGMTS [
          REQ017_asgmt1
          ; REQ017_asgmt2
        ]).
  apply theo_rules_asgmts. reflexivity.
Defined.

Definition the_flashing_mode_component : FUNCTION.
Proof.
  apply (mkFUNCTION [
          (REQ015_sg, REQ015_tg, REQ015_asgmts, "REQ015")
          ; (REQ013_sg, REQ013_tg, REQ013_asgmts, "REQ013")
          ; (REQ014_sg, REQ014_tg, REQ014_asgmts, "REQ014")
          ; (REQ016_sg, REQ016_tg, REQ016_asgmts, "REQ016")
          ; (REQ011_sg, REQ011_tg, REQ011_asgmts, "REQ011")
          ; (REQ012_sg, REQ012_tg, REQ012_asgmts, "REQ012")
          ; (REQ010_sg, REQ010_tg, REQ010_asgmts, "REQ010")
          ; (REQ017_sg, REQ017_tg, REQ017_asgmts, "REQ017")
        ]).
  apply theo_rules_function. reflexivity.
Defined.

Definition REQ008_sg_disj1 : DISJ.
Proof.
  apply (mkDISJ [
          mkBEXP (current (the_flashing_mode)) eq (i 3)
        ]).
  apply theo_rules_disj. reflexivity.
Defined.

Definition REQ008_sg_disj2 : DISJ.
Proof.
  apply (mkDISJ [
          mkBEXP (current (the_indication_lights)) eq (i 2)
        ]).
  apply theo_rules_disj. reflexivity.
Defined.

Definition REQ008_sg_disj3 : DISJ.
Proof.
  apply (mkDISJ [
          mkBEXP (current (the_voltage)) gt (i 80)
        ]).
  apply theo_rules_disj. reflexivity.
Defined.

Definition REQ008_sg : EXP.
Proof.
  apply (mkCONJ [
          REQ008_sg_disj1
          ; REQ008_sg_disj2
          ; REQ008_sg_disj3
        ]).
Defined.

Definition REQ008_tg_disj1 : DISJ.
Proof.
  apply (mkDISJ [
          mkBEXP (current (the_flashing_timer)) ge (n 11)
        ]).
  apply theo_rules_disj. reflexivity.
Defined.

Definition REQ008_tg : EXP.
Proof.
  apply (mkCONJ [
          REQ008_tg_disj1
        ]).
Defined.

Definition REQ008_asgmt1 : ASGMT.
Proof.
  apply (mkASGMT (the_indication_lights, (i 3))).
Defined.

Definition REQ008_asgmt2 : ASGMT.
Proof.
  apply (mkASGMT (the_flashing_timer, (n 0))).
Defined.

Definition REQ008_asgmts : ASGMTS.
Proof.
  apply (mkASGMTS [
          REQ008_asgmt1
          ; REQ008_asgmt2
        ]).
  apply theo_rules_asgmts. reflexivity.
Defined.

Definition REQ009_sg_disj1 : DISJ.
Proof.
  apply (mkDISJ [
          mkBEXP (current (the_flashing_mode)) eq (i 0)
        ]).
  apply theo_rules_disj. reflexivity.
Defined.

Definition REQ009_sg_disj2 : DISJ.
Proof.
  apply (mkDISJ [
          mkBEXP (current (the_indication_lights)) eq (i 2)
        ]).
  apply theo_rules_disj. reflexivity.
Defined.

Definition REQ009_sg_disj3 : DISJ.
Proof.
  apply (mkDISJ [
          mkBEXP (current (the_voltage)) gt (i 80)
        ]).
  apply theo_rules_disj. reflexivity.
Defined.

Definition REQ009_sg : EXP.
Proof.
  apply (mkCONJ [
          REQ009_sg_disj1
          ; REQ009_sg_disj2
          ; REQ009_sg_disj3
        ]).
Defined.

Definition REQ009_tg_disj1 : DISJ.
Proof.
  apply (mkDISJ [
          mkBEXP (current (the_flashing_timer)) ge (n 11)
        ]).
  apply theo_rules_disj. reflexivity.
Defined.

Definition REQ009_tg : EXP.
Proof.
  apply (mkCONJ [
          REQ009_tg_disj1
        ]).
Defined.

Definition REQ009_asgmt1 : ASGMT.
Proof.
  apply (mkASGMT (the_indication_lights, (i 0))).
Defined.

Definition REQ009_asgmt2 : ASGMT.
Proof.
  apply (mkASGMT (the_flashing_timer, (n 0))).
Defined.

Definition REQ009_asgmts : ASGMTS.
Proof.
  apply (mkASGMTS [
          REQ009_asgmt1
          ; REQ009_asgmt2
        ]).
  apply theo_rules_asgmts. reflexivity.
Defined.

Definition REQ005_sg_disj1 : DISJ.
Proof.
  apply (mkDISJ [
          mkBEXP (current (the_flashing_mode)) eq (i 2)
        ]).
  apply theo_rules_disj. reflexivity.
Defined.

Definition REQ005_sg_disj2 : DISJ.
Proof.
  apply (mkDISJ [
          mkBEXP (current (the_voltage)) gt (i 80)
        ]).
  apply theo_rules_disj. reflexivity.
Defined.

Definition REQ005_sg : EXP.
Proof.
  apply (mkCONJ [
          REQ005_sg_disj1
          ; REQ005_sg_disj2
        ]).
Defined.

Definition REQ005_tg : EXP.
Proof.
  apply (mkCONJ [
        ]).
Defined.

Definition REQ005_asgmt1 : ASGMT.
Proof.
  apply (mkASGMT (the_indication_lights, (i 2))).
Defined.

Definition REQ005_asgmt2 : ASGMT.
Proof.
  apply (mkASGMT (the_flashing_timer, (n 0))).
Defined.

Definition REQ005_asgmts : ASGMTS.
Proof.
  apply (mkASGMTS [
          REQ005_asgmt1
          ; REQ005_asgmt2
        ]).
  apply theo_rules_asgmts. reflexivity.
Defined.

Definition REQ006_sg_disj1 : DISJ.
Proof.
  apply (mkDISJ [
          mkBEXP (current (the_indication_lights)) eq (i 3)
          ; mkBEXP (current (the_indication_lights)) eq (i 1)
        ]).
  apply theo_rules_disj. reflexivity.
Defined.

Definition REQ006_sg_disj2 : DISJ.
Proof.
  apply (mkDISJ [
          mkBEXP (current (the_voltage)) gt (i 80)
        ]).
  apply theo_rules_disj. reflexivity.
Defined.

Definition REQ006_sg : EXP.
Proof.
  apply (mkCONJ [
          REQ006_sg_disj1
          ; REQ006_sg_disj2
        ]).
Defined.

Definition REQ006_tg_disj1 : DISJ.
Proof.
  apply (mkDISJ [
          mkBEXP (current (the_flashing_timer)) ge (n 17)
        ]).
  apply theo_rules_disj. reflexivity.
Defined.

Definition REQ006_tg : EXP.
Proof.
  apply (mkCONJ [
          REQ006_tg_disj1
        ]).
Defined.

Definition REQ006_asgmt1 : ASGMT.
Proof.
  apply (mkASGMT (the_indication_lights, (i 2))).
Defined.

Definition REQ006_asgmt2 : ASGMT.
Proof.
  apply (mkASGMT (the_flashing_timer, (n 0))).
Defined.

Definition REQ006_asgmts : ASGMTS.
Proof.
  apply (mkASGMTS [
          REQ006_asgmt1
          ; REQ006_asgmt2
        ]).
  apply theo_rules_asgmts. reflexivity.
Defined.

Definition REQ003_sg_disj1 : DISJ.
Proof.
  apply (mkDISJ [
          mkBEXP (previous (the_flashing_mode)) ne (i 3)
          ; mkBEXP (previous (the_voltage)) le (i 80)
        ]).
  apply theo_rules_disj. reflexivity.
Defined.

Definition REQ003_sg_disj2 : DISJ.
Proof.
  apply (mkDISJ [
          mkBEXP (current (the_flashing_mode)) eq (i 3)
        ]).
  apply theo_rules_disj. reflexivity.
Defined.

Definition REQ003_sg_disj3 : DISJ.
Proof.
  apply (mkDISJ [
          mkBEXP (current (the_voltage)) gt (i 80)
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
  apply (mkASGMT (the_indication_lights, (i 3))).
Defined.

Definition REQ003_asgmt2 : ASGMT.
Proof.
  apply (mkASGMT (the_flashing_timer, (n 0))).
Defined.

Definition REQ003_asgmts : ASGMTS.
Proof.
  apply (mkASGMTS [
          REQ003_asgmt1
          ; REQ003_asgmt2
        ]).
  apply theo_rules_asgmts. reflexivity.
Defined.

Definition REQ007_sg_disj1 : DISJ.
Proof.
  apply (mkDISJ [
          mkBEXP (current (the_flashing_mode)) eq (i 1)
        ]).
  apply theo_rules_disj. reflexivity.
Defined.

Definition REQ007_sg_disj2 : DISJ.
Proof.
  apply (mkDISJ [
          mkBEXP (current (the_indication_lights)) eq (i 2)
        ]).
  apply theo_rules_disj. reflexivity.
Defined.

Definition REQ007_sg_disj3 : DISJ.
Proof.
  apply (mkDISJ [
          mkBEXP (current (the_voltage)) gt (i 80)
        ]).
  apply theo_rules_disj. reflexivity.
Defined.

Definition REQ007_sg : EXP.
Proof.
  apply (mkCONJ [
          REQ007_sg_disj1
          ; REQ007_sg_disj2
          ; REQ007_sg_disj3
        ]).
Defined.

Definition REQ007_tg_disj1 : DISJ.
Proof.
  apply (mkDISJ [
          mkBEXP (current (the_flashing_timer)) ge (n 11)
        ]).
  apply theo_rules_disj. reflexivity.
Defined.

Definition REQ007_tg : EXP.
Proof.
  apply (mkCONJ [
          REQ007_tg_disj1
        ]).
Defined.

Definition REQ007_asgmt1 : ASGMT.
Proof.
  apply (mkASGMT (the_indication_lights, (i 1))).
Defined.

Definition REQ007_asgmt2 : ASGMT.
Proof.
  apply (mkASGMT (the_flashing_timer, (n 0))).
Defined.

Definition REQ007_asgmts : ASGMTS.
Proof.
  apply (mkASGMTS [
          REQ007_asgmt1
          ; REQ007_asgmt2
        ]).
  apply theo_rules_asgmts. reflexivity.
Defined.

Definition REQ002_sg_disj1 : DISJ.
Proof.
  apply (mkDISJ [
          mkBEXP (previous (the_flashing_mode)) ne (i 1)
          ; mkBEXP (previous (the_voltage)) le (i 80)
        ]).
  apply theo_rules_disj. reflexivity.
Defined.

Definition REQ002_sg_disj2 : DISJ.
Proof.
  apply (mkDISJ [
          mkBEXP (current (the_flashing_mode)) eq (i 1)
        ]).
  apply theo_rules_disj. reflexivity.
Defined.

Definition REQ002_sg_disj3 : DISJ.
Proof.
  apply (mkDISJ [
          mkBEXP (current (the_voltage)) gt (i 80)
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
  apply (mkASGMT (the_indication_lights, (i 1))).
Defined.

Definition REQ002_asgmt2 : ASGMT.
Proof.
  apply (mkASGMT (the_flashing_timer, (n 0))).
Defined.

Definition REQ002_asgmts : ASGMTS.
Proof.
  apply (mkASGMTS [
          REQ002_asgmt1
          ; REQ002_asgmt2
        ]).
  apply theo_rules_asgmts. reflexivity.
Defined.

Definition REQ001_sg_disj1 : DISJ.
Proof.
  apply (mkDISJ [
          mkBEXP (previous (the_voltage)) gt (i 80)
        ]).
  apply theo_rules_disj. reflexivity.
Defined.

Definition REQ001_sg_disj2 : DISJ.
Proof.
  apply (mkDISJ [
          mkBEXP (current (the_voltage)) le (i 80)
        ]).
  apply theo_rules_disj. reflexivity.
Defined.

Definition REQ001_sg : EXP.
Proof.
  apply (mkCONJ [
          REQ001_sg_disj1
          ; REQ001_sg_disj2
        ]).
Defined.

Definition REQ001_tg : EXP.
Proof.
  apply (mkCONJ [
        ]).
Defined.

Definition REQ001_asgmt1 : ASGMT.
Proof.
  apply (mkASGMT (the_indication_lights, (i 2))).
Defined.

Definition REQ001_asgmt2 : ASGMT.
Proof.
  apply (mkASGMT (the_flashing_timer, (n 0))).
Defined.

Definition REQ001_asgmts : ASGMTS.
Proof.
  apply (mkASGMTS [
          REQ001_asgmt1
          ; REQ001_asgmt2
        ]).
  apply theo_rules_asgmts. reflexivity.
Defined.

Definition REQ004_sg_disj1 : DISJ.
Proof.
  apply (mkDISJ [
          mkBEXP (previous (the_flashing_mode)) ne (i 0)
          ; mkBEXP (previous (the_voltage)) le (i 80)
        ]).
  apply theo_rules_disj. reflexivity.
Defined.

Definition REQ004_sg_disj2 : DISJ.
Proof.
  apply (mkDISJ [
          mkBEXP (current (the_flashing_mode)) eq (i 0)
        ]).
  apply theo_rules_disj. reflexivity.
Defined.

Definition REQ004_sg_disj3 : DISJ.
Proof.
  apply (mkDISJ [
          mkBEXP (current (the_voltage)) gt (i 80)
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
  apply (mkASGMT (the_indication_lights, (i 0))).
Defined.

Definition REQ004_asgmt2 : ASGMT.
Proof.
  apply (mkASGMT (the_flashing_timer, (n 0))).
Defined.

Definition REQ004_asgmts : ASGMTS.
Proof.
  apply (mkASGMTS [
          REQ004_asgmt1
          ; REQ004_asgmt2
        ]).
  apply theo_rules_asgmts. reflexivity.
Defined.

Definition the_lights_controller_component : FUNCTION.
Proof.
  apply (mkFUNCTION [
          (REQ008_sg, REQ008_tg, REQ008_asgmts, "REQ008")
          ; (REQ009_sg, REQ009_tg, REQ009_asgmts, "REQ009")
          ; (REQ005_sg, REQ005_tg, REQ005_asgmts, "REQ005")
          ; (REQ006_sg, REQ006_tg, REQ006_asgmts, "REQ006")
          ; (REQ003_sg, REQ003_tg, REQ003_asgmts, "REQ003")
          ; (REQ007_sg, REQ007_tg, REQ007_asgmts, "REQ007")
          ; (REQ002_sg, REQ002_tg, REQ002_asgmts, "REQ002")
          ; (REQ001_sg, REQ001_tg, REQ001_asgmts, "REQ001")
          ; (REQ004_sg, REQ004_tg, REQ004_asgmts, "REQ004")
        ]).
  apply theo_rules_function. reflexivity.
Defined.

Definition tis_functions : DFRS_FUNCTIONS.
Proof.
  apply (mkDFRS_FUNCTIONS [
          the_flashing_mode_component
          ; the_lights_controller_component
        ]).
  apply theo_rules_dfrs_functions. reflexivity.
Defined.

(*============ TIS: S_DFRS ============*)
Definition tis_s_dfrs : s_DFRS.
Proof.
  apply (mkS_DFRS tis_variables tis_s0 tis_functions).
  apply theo_rules_s_dfrs. reflexivity.
Defined.
(*============ TIS: S_DFRS ============*)

Local Close Scope string.
