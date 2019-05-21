Require Import trans_rel.
Require Import trans_rel_fun_rules.

(* DFRS_TRANSITION_RELATION *)
Theorem theo_rules_dfrs_trans_rel :
  forall (tr : TRANSREL),
    ind_rules_dfrs_trans_rel tr
    <-> fun_rules_dfrs_trans_rel tr = true.
Proof. Admitted.