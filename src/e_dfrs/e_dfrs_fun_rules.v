Require Import Coq.Lists.List.
Import ListNotations.
Require Import Bool.

Require Import util.
Require Import fun_util.
Require Import variables.
Require Import state.
Require Import states.
Require Import trans_rel_fun_rules.
Require Import e_dfrs.

Fixpoint bis_valid_states (states : list STATE) (f : list (NAME * TYPE)) :
  bool :=
  match states with
  | []     => true
  | h :: t => if bwell_typed_state h f
              then bis_valid_states t f
              else false
  end.

Fixpoint bis_valid_trans (trans : list TRANS) (sts : list STATE) 
  (I O T : list (VNAME * TYPE)) (gcvar : (NAME * TYPE)) : bool :=
  match trans with
  | []     => true
  | h :: t => bin_list (fst (fst h.(STS))) sts
              (fun (s1 s2 : STATE) =>
                  beq_state s1 s2)
              &&
              bin_list (snd h.(STS)) sts
              (fun (s1 s2 : STATE) =>
                  beq_state s1 s2)
              &&
              bwell_typed_transition (snd (fst h.(STS))) I O T gcvar
              &&
              (if branFun (snd (fst h.(STS)))
               then beq_state
                    (nextState (fst3 h.(STS)) T
                      (match (functionTransition (snd (fst h.(STS)))) with
                       | Some a => fst a
                       | None   => default_asgmts
                       end))
                    (snd h.(STS))
               else bis_valid_trans t sts I O T gcvar)
              &&
              (if branDel (snd (fst h.(STS)))
               then (if branDiscrete (snd (fst h.(STS)))
                     then (if beq_state_elements
                              (update_gc
                                (nextState (fst3 h.(STS)) T
                                  (match (delayTransition (snd3 h.(STS))) with
                                   | Some a => snd a
                                   | None   => default_asgmts
                                   end)).(state)
                                ((fst3 h.(STS)).(state))
                                (match (delayTransition (snd3 h.(STS))) with
                                   | Some a => fst a
                                   | None   => discrete 0
                                   end))
                              (snd h.(STS)).(state)
                              (* UPDATE GC *)
                           then bis_valid_trans t sts I O T gcvar
                           else false
                          )
                     else bis_valid_trans t sts I O T gcvar
                    )
               else bis_valid_trans t sts I O T gcvar
              )
  end.

Definition fun_rules_e_dfrs (vars : DFRS_VARIABLES) (sts : DFRS_STATES)
  (tr : DFRS_TRANSITION_RELATION) : bool :=
  let
    IO := List.app vars.(I).(svars) vars.(O).(svars)
  in
  let
    OT := List.app vars.(O).(svars) vars.(T).(stimers)
  in
  let
    IOT := List.app IO vars.(T).(stimers)
  in
  let
    IOTgcvar := List.app ([vars.(gcvar)])
                          (map (fun x : (VNAME * TYPE) 
                            => ((fst x).(vname), snd x)) IOT)
  in
    bis_valid_states sts.(States).(states) IOTgcvar
    &&
    bis_valid_trans tr.(TR).(transrel) sts.(States).(states)
      vars.(I).(svars) vars.(O).(svars) vars.(T).(stimers) vars.(gcvar).