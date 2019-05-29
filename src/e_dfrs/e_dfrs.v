Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.

Require Import util.
Require Import fun_util.
Require Import variables.
Require Import functions.
Require Import states.
Require Import trans_rel.
Require Import trans_rel_fun_rules.

Require Import functions_fun_ind_equiv.
Require Import states_fun_ind_equiv.

Local Open Scope string.

Definition default_vname : VNAME.
Proof.
  apply (mkVNAME "default").
  unfold ind_rules_vname. unfold not.
  intro H. inversion H.
Defined.

Definition default_asgmt : ASGMT.
Proof.
  apply (mkASGMT (default_vname, (n 0))).
Defined.

Definition default_asgmts : ASGMTS.
Proof.
  apply (mkASGMTS [default_asgmt]).
  apply theo_rules_asgmts. reflexivity.
Defined.

Fixpoint get_gc (l : list (NAME * (VALUE * VALUE))) : 
  option (NAME * (VALUE * VALUE)) :=
  match l with
  | []     => None
  | h :: t => if bstring_dec (fst h) ("gc")
              then Some h
              else get_gc t
  end.

Fixpoint get_asgmt_value (n : NAME) (A : list ASGMT) : option VALUE :=
  match A with
  | []     => None
  | h :: t => if bstring_dec (fst h.(asgmt)).(vname) (n)
              then Some (snd h.(asgmt))
              else get_asgmt_value n t
  end.

Fixpoint update_state_values (ls : list (NAME * (VALUE * VALUE))) 
  (S : STATE) (domT domA : list NAME) (A : ASGMTS) : 
  list (NAME * (VALUE * VALUE)) :=
  match ls with
  | []     => []
  | h :: t => let
                name := fst h
              in
              let
                v1 := fst(snd h)
              in
              let
                v2 := snd(snd h)
              in
              let
                gcName := get_gc S.(state)
              in
                if bin_list name domA
                   (fun (v v' : NAME)
                    => bstring_dec v v')
                then
                      if bin_list name domT
                         (fun (v v' : NAME)
                          => bstring_dec v v')
                      then (match gcName with
                            | Some e => (name, (v1, (snd(snd e)))) ::
                                        update_state_values t S domT domA A
                            | None   => (name, (v1, v2)) ::
                                        update_state_values t S domT domA A
                            end)
                      else (match (get_asgmt_value name A.(asgmts)) with
                            | Some v => (name, (v2, v)) ::
                                        update_state_values t S domT domA A
                            | None   => (name, (v1, v2)) ::
                                        update_state_values t S domT domA A
                            end)
                else (name, (v1, v2)) :: update_state_values t S domT domA A
    end.

(** nextState *)
Theorem state_valid :
  forall (s : list (NAME * (VALUE * VALUE))), 
    is_function
    (map (fun var : (NAME * (VALUE * VALUE)) => fst var) s)
    string_dec.
Admitted.

Definition nextState (S : STATE) (T : list (VNAME * TYPE)) (A : ASGMTS)  : 
  STATE :=
  let
    domT := map (fun x : (VNAME * TYPE) => (fst x).(vname)) T
  in
    let
      domA := map (fun x : ASGMT => (fst x.(asgmt)).(vname)) A.(asgmts)
    in
      mkSTATE (update_state_values S.(state) S domT domA A) 
              (state_valid (update_state_values S.(state) S domT domA A)).

(** e_DFRS *)
Fixpoint update_gc (st trans1 : list (NAME * (VALUE * VALUE)))
  (d : DELAY) : list (NAME * (VALUE * VALUE)) :=
  let
    gc := get_gc trans1
  in
  match st with
  | []     => []
  | h :: t => if (bstring_dec (fst h) "gc")
              then (match gc with
                    | Some x => (fst x, ((snd (snd x)), 
                                 (match (snd (snd x)) with
                                  | n v => n (v + (delayValue d))
                                  | _   => (snd (snd x))
                                  end))) ::
                                  update_gc t trans1 d
                    | None   => h :: update_gc t trans1 d
                    end)
              else h :: update_gc t trans1 d
  end.

Fixpoint is_valid_states (states : list STATE) (f : list (NAME * TYPE)) :
  Prop :=
  match states with
  | []     => True
  | h :: t => well_typed_state h f /\ is_valid_states t f
  end.

Fixpoint is_valid_trans (trans : list TRANS) (sts : list STATE) 
  (I O T : list (VNAME * TYPE)) (gcvar : (NAME * TYPE)) : Prop :=
  match trans with
  | []     => True
  | h :: t => in_list (fst (fst h.(STS))) sts
              (fun (s1 s2 : STATE) =>
                  eq_state s1 s2)
              /\
              in_list (snd h.(STS)) sts
              (fun (s1 s2 : STATE) =>
                  eq_state s1 s2)
              /\
              well_typed_transition (snd (fst h.(STS))) I O T gcvar
              /\
              ((ranFun (snd (fst h.(STS)))
                /\ eq_state
                    (nextState (fst3 h.(STS)) T
                      (match (functionTransition (snd (fst h.(STS)))) with
                       | Some a => fst a
                       | None   => default_asgmts
                       end))
                    (snd h.(STS)))
               \/
               is_valid_trans t sts I O T gcvar)
              /\
              ((ranDel (snd (fst h.(STS)))
               /\((ranDiscrete (snd (fst h.(STS)))
                   /\((eq_state_elements
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
                        (snd h.(STS)).(state))
                        (* UPDATE GC *)
                     /\ is_valid_trans t sts I O T gcvar)
                    )
                  \/ is_valid_trans t sts I O T gcvar))
               \/ is_valid_trans t sts I O T gcvar)
  end.

Definition ind_rules_e_dfrs (vars : DFRS_VARIABLES) (sts : DFRS_STATES)
  (tr : DFRS_TRANSITION_RELATION) : Prop :=
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
    is_valid_states sts.(States).(states) IOTgcvar
    /\
    is_valid_trans tr.(TR).(transrel) sts.(States).(states)
      vars.(I).(svars) vars.(O).(svars) vars.(T).(stimers) vars.(gcvar).

Record e_DFRS : Set := mkE_DFRS {
  e_dfrs_variables              : DFRS_VARIABLES;
  e_dfrs_states                 : DFRS_STATES;
  e_dfrs_transition_relation    : DFRS_TRANSITION_RELATION;
  rules_e_dfrs                  : ind_rules_e_dfrs e_dfrs_variables
                                                   e_dfrs_states
                                                   e_dfrs_transition_relation
}.

Local Close Scope string.