Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Require Import Bool.

Require Import util.
Require Import variables.
Require Import functions.
Require Import functions_fun_rules.
Require Import trans_rel.
Require Import states.
Require Import s_dfrs.
Require Import e_dfrs.

Definition ranB (v : VALUE) : bool :=
  match v with
  | b _ => true
  | _   => false
  end.

Definition ranI (v : VALUE) : bool :=
  match v with
  | i _ => true
  | _   => false
  end.

Definition ranN (v : VALUE) : bool :=
  match v with
  | n _ => true
  | _   => false
  end.

Definition ble_value (t1 t2 : VALUE) : bool :=
  match t1,t2 with
  | i t1, i t2 => Z.leb t1 t2
  | n t1, n t2 => Nat.leb t1 t2
  | _, _ => false
  end.

Definition blt_value (t1 t2 : VALUE) : bool :=
  match t1,t2 with
  | i t1, i t2 => Z.ltb t1 t2
  | n t1, n t2 => Nat.ltb t1 t2
  | _, _ => false
  end.

Definition bne_value (t1 t2 : VALUE) : bool :=
  match t1,t2 with
  | b t1, b t2 => negb (eqb t1 t2)
  | i t1, i t2 => negb (Z.leb t1 t2)
  | n t1, n t2 => negb (Nat.leb t1 t2)
  | _, _ => false
  end.

Definition bgt_value (t1 t2 : VALUE) : bool :=
  match t1,t2 with
  | i t1, i t2 => Z.gtb t1 t2
  | n t1, n t2 => negb (Nat.leb t1 t2)
  | _, _ => false
  end.

Definition bge_value (t1 t2 : VALUE) : bool :=
  match t1,t2 with
  | i t1, i t2 => Z.geb t1 t2
  | n t1, n t2 => negb (Nat.ltb t1 t2)
  | _, _ => false
  end.

Fixpoint union_lists {X : Type} (ll : list (list X)) : list X :=
  match ll with
  | []     => []
  | h :: t => List.app h (union_lists t)
  end.

Fixpoint gen_possible_asgmts (v : VNAME) (l : list VALUE)  : list ASGMT :=
  match l with
  | []     => []
  | h :: t => mkASGMT (v, h) :: gen_possible_asgmts v t
  end.

Fixpoint possible_asgmts (ll : list (VNAME * list VALUE)) : list (list ASGMT) :=
  match ll with
  | []     => []
  | h :: t => (gen_possible_asgmts (fst h) (snd h))
                     :: possible_asgmts t
  end.

Definition add_possible_assignment (a : ASGMT) (ll : list (list ASGMT)) : list (list ASGMT) :=
  map (fun (l : list ASGMT) => a :: l) ll.

Fixpoint add_possible_assignments (l : list ASGMT) (ll : list (list ASGMT)) : list (list ASGMT) :=
  match l with
  | []      => []
  | h :: tl => add_possible_assignment h ll
               ++ add_possible_assignments tl ll
  end.

Fixpoint gen_asgmts_combination (ll1 ll2 : list (list ASGMT)) : list (list ASGMT) :=
  match ll1 with
  | []      => [[]]
  | h :: tl => add_possible_assignments h (gen_asgmts_combination tl ll2)
  end.

(** static_bexps_true *)
Fixpoint static_bexps_true (l : list (NAME * VALUE)) (be : BEXP) : bool :=
  match l with
  | []      => true
  | f :: fs => (if bstring_dec (fst f) (var_name be).(vname)
                then (if ranB (snd f)
                      then beq_value (snd f) be.(literal)
                      else (if ranI (snd f) || ranN (snd f)
                            then match be.(op) with
                                 | le => ble_value (snd f) be.(literal)
                                 | lt => blt_value (snd f) be.(literal)
                                 | eq => beq_value (snd f) be.(literal)
                                 | ne => bne_value (snd f) be.(literal)
                                 | gt => bgt_value (snd f) be.(literal)
                                 | ge => bge_value (snd f) be.(literal)
                                 end
                            else false))
               else static_bexps_true fs be)
              &&
               static_bexps_true fs be
  end.

Definition minus_value (v1 v2 : VALUE) : VALUE :=
  match v1, v2 with
  | n n1, n n2 => (n (n1 - n2))
  | i i1, i i2 => (i (i1 - i2))
  | _   , _    => v1
  end.

(** timed_bexps_true *)
Fixpoint timed_bexps_true (l : list (NAME * VALUE)) (be : BEXP) 
  (gc : (NAME * (VALUE * VALUE))) : bool :=
  match l with
  | []      => true
  | f :: fs => (if bstring_dec (fst f) (var_name be).(vname)
                then
                  (if ranN (snd f)
                  then (match be.(op) with
                        | le => ble_value (minus_value (snd (snd gc)) 
                                                       (snd f)) be.(literal)
                        | lt => blt_value (minus_value (snd (snd gc)) 
                                                       (snd f)) be.(literal)
                        | eq => beq_value (minus_value (snd (snd gc))
                                                       (snd f)) be.(literal)
                        | ne => bne_value (minus_value (snd (snd gc))
                                                       (snd f)) be.(literal)
                        | gt => bgt_value (minus_value (snd (snd gc))
                                                       (snd f)) be.(literal)
                        | ge => bge_value (minus_value (snd (snd gc))
                                                       (snd f)) be.(literal)
                        end)
                  else false)
                else timed_bexps_true fs be gc)
               &&
                timed_bexps_true fs be gc
  end.

(** static_guards_true *)
Fixpoint values_in_static_bexps_true (be : list BEXP) (s : STATE) : bool :=
  match be with
  | []     => true
  | h :: t => if (match h.(v) with
                  | current _  => static_bexps_true (current_values s) h
                  | previous _ => static_bexps_true (previous_values s) h
                  end)
              then values_in_static_bexps_true t s
              else false
  end.

Definition static_guards_true (s : STATE) (sGuard : EXP)
  (IO T : list (VNAME * TYPE)) : bool :=
  let
    bexps := union_lists (map (fun d : DISJ => d.(disjs)) sGuard.(conjs))
  in
  (bvar_consistent_exp sGuard IO T) && (values_in_static_bexps_true bexps s).

(** timed_guards_true *)
Fixpoint values_in_timed_bexps_true (be : list BEXP) (s : STATE) 
  (gc : option (NAME * (VALUE * VALUE))) : bool :=
  match be with
  | []     => true
  | h :: t => if (match h.(v) with
                  | current _  => (match gc with
                                   | Some e => timed_bexps_true 
                                                (current_values s) h e
                                   | None   => false
                                   end)
                  | previous _ => (match gc with
                                   | Some e => timed_bexps_true 
                                                (previous_values s) h e
                                   | None   => false
                                   end)
                  end)
              then values_in_timed_bexps_true t s gc
              else false
  end.

Definition timed_guards_true (s : STATE) (tGuard : EXP) 
  (T : list (VNAME * TYPE)) : bool :=
  let
    bexps := union_lists (map (fun d : DISJ => d.(disjs)) tGuard.(conjs))
  in
  let
    gc := get_gc s.(state)
  in
  (bvar_consistent_exp tGuard T T) && (values_in_timed_bexps_true bexps s gc).

(** is_stable *)
Fixpoint is_stable_entry (s : STATE) (IO T : list (VNAME * TYPE)) 
  (le : list (EXP * EXP * ASGMTS * REQUIREMENT)) : bool :=
  match le with
  | []     => true
  | h :: t => if (negb (static_guards_true s (fst3 (fst h)) IO T))
                 ||
                  (negb (timed_guards_true s (snd3 (fst h)) T))
                 ||
                  beq_state s
                           (nextState s T (trd3 (fst h)))
               then is_stable_entry s IO T t
               else false
  end.

Definition is_stable (s : STATE) (IO T : list (VNAME * TYPE))
  (F : list (list FUNCTION)) : bool :=
  let
    entries := union_lists 
                (map (fun f : FUNCTION => f.(function)) (union_lists F))
  in
   is_stable_entry s IO T entries.

(** genTransitions *)
Theorem asgmts_valid :
  forall (l : list ASGMT), 
    (0 < (length l))
    /\ is_function l 
          (fun (asgmt1 asgmt2 : ASGMT)
                => string_dec
                     (fst asgmt1.(asgmt)).(vname)
                     (fst asgmt2.(asgmt)).(vname)).
Admitted.

Fixpoint make_trans_del (s : STATE) (I T : list (VNAME * TYPE))
  (a : list (list ASGMT)) : list TRANS :=
  match a with
  | []     => []
  | h :: t => let
                nextSt := nextState s T (mkASGMTS h (asgmts_valid h))
              in
              let
                delay := discrete 1
              in
              (mkTRANS (s, (del (delay, mkASGMTS h (asgmts_valid h))), 
                        mkSTATE (update_gc nextSt.(state) 
                                           nextSt.(state) delay)
                                (state_valid (update_gc nextSt.(state) 
                                                        nextSt.(state) delay))))
              :: make_trans_del s I T t
  end.

Fixpoint make_trans_func (s : STATE) (IO T : list (VNAME * TYPE))
  (le : list (EXP * EXP * ASGMTS * REQUIREMENT)) : list TRANS :=
  match le with
  | []     => []
  | h :: t => if static_guards_true s (fst3 (fst h)) IO T
                &&
                 timed_guards_true s (snd3 (fst h)) T
              then (mkTRANS (s, (func (trd3 (fst h), snd h)),
                            nextState s T (trd3 (fst h))))
                   :: make_trans_func s IO T t
              else make_trans_func s IO T t
  end.

Definition genTransitions (s : STATE) (I O T : list (VNAME * TYPE)) 
  (F : list (list FUNCTION)) (possibilities : list (VNAME * list VALUE)) 
  : TRANSREL :=
  let
    entries := union_lists 
                (map (fun f : FUNCTION => f.(function)) (union_lists F))
  in
  let
    combinations := gen_asgmts_combination
                      (possible_asgmts possibilities) [[]]
  in
    if is_stable s (List.app I O) T F
    then mkTRANSREL (make_trans_del s I T combinations)
    else mkTRANSREL (make_trans_func s (I ++ O) T entries).

Fixpoint bin_state_list (v : list (NAME * (VALUE * VALUE))) 
  (l : list STATE) (comp : list (NAME * (VALUE * VALUE)) -> 
  list (NAME * (VALUE * VALUE)) -> bool) : bool :=
  match l with
  | []      => false
  | h :: tl => if comp v h.(state) then true
               else bin_state_list v tl comp
  end.

Fixpoint get_list_states (l : list TRANS) (visited : list STATE) : list STATE :=
  match l with
  | []     => []
  | h :: t => if bin_state_list (trd3 h.(STS)).(state) visited beq_state_elements
              then get_list_states t visited
              else trd3 h.(STS) :: get_list_states t visited
  end.

(* buildTR *)
Fixpoint buildTR (toVisit visited : list STATE) (I Out T : list (VNAME * TYPE))
  (F : list (list FUNCTION)) (possibilities : list (VNAME * list VALUE))
  (num : nat) : list TRANS :=
  match toVisit, num with
  | []    , _  => []
  | _ :: _, 0    => []
  | h :: t, S n' => let
                      tr1 := genTransitions h I Out T F possibilities
                    in
                      if bin_state_list h.(state) visited beq_state_elements
                      then buildTR t visited I Out T F possibilities n'
                      else tr1.(transrel) ++ 
                           buildTR
                            (t ++ (get_list_states tr1.(transrel) 
                                    (h :: visited)))
                            (h :: visited) I Out T F possibilities n'
  end.

Definition call_buildTR (toVisit visited : list STATE) 
  (I Out T : list (VNAME * TYPE)) (F : list (list FUNCTION)) (limiter : nat)
  (possibilities : list (VNAME * list VALUE)) : list TRANS :=
  let
    numTR := limiter
  in
    buildTR toVisit visited I Out T F possibilities numTR.

(* S to E *)

(* TODO: REVIEW *)
Fixpoint removeDuplicateStates (l : list STATE) : list STATE :=
  match l with
  | []     => []
  | h :: t => if bin_state_list h.(state) t beq_state_elements
              then removeDuplicateStates t
              else h :: removeDuplicateStates t
  end.

Theorem variables_valid :
  forall (I O : SVARS) (T : STIMERS) (gcvar : (NAME * TYPE)),
    ind_rules_dfrs_variables I O T gcvar.
Admitted.

Theorem states_valid :
  forall (l : list STATE),
    ind_rules_states l.
Admitted.

Theorem dfrs_states_valid :
  forall (s : STATE) (ss : STATES),
    ind_rules_dfrs_states s ss.
Admitted.

Theorem dfrs_trans_rel_valid :
  forall (tr : TRANSREL),
    ind_rules_dfrs_trans_rel tr.
Admitted.

Theorem e_dfrs_valid :
  forall (vars : DFRS_VARIABLES) (sts : DFRS_STATES) (tr : DFRS_TRANSITION_RELATION),
    ind_rules_e_dfrs vars sts tr.
Admitted.

(* TODO: TRANSREL could have loops? *)
Definition expandedDFRS (sdfrs : s_DFRS) (limiter : nat)
  (possibilities : list (VNAME * list VALUE)) : e_DFRS :=
  let
    TR := mkTRANSREL 
          (call_buildTR [sdfrs.(s_dfrs_initial_state).(s0)] 
           [] 
           sdfrs.(s_dfrs_variables).(I).(svars) 
           sdfrs.(s_dfrs_variables).(O).(svars) 
           sdfrs.(s_dfrs_variables).(T).(stimers)
           [sdfrs.(s_dfrs_functions).(F)]
           limiter possibilities)
  in
  let
    states := removeDuplicateStates (
              (get_list_states TR.(transrel) []) ++
              [sdfrs.(s_dfrs_initial_state).(s0)])
  in
  let
    dfrs_variables := (mkDFRS_VARIABLES sdfrs.(s_dfrs_variables).(I)
                                        sdfrs.(s_dfrs_variables).(O)
                                        sdfrs.(s_dfrs_variables).(T)
                                        sdfrs.(s_dfrs_variables).(gcvar)
                                        (variables_valid 
                                          sdfrs.(s_dfrs_variables).(I)
                                          sdfrs.(s_dfrs_variables).(O)
                                          sdfrs.(s_dfrs_variables).(T)
                                          sdfrs.(s_dfrs_variables).(gcvar)))
  in
  let
    dfrs_states := (mkDFRSSTATES 
                      (mkSTATES states (states_valid states))
                      sdfrs.(s_dfrs_initial_state).(s0)
                      (dfrs_states_valid
                        sdfrs.(s_dfrs_initial_state).(s0)
                        (mkSTATES states (states_valid states))))
  in
  let
    dfrs_tr := (mkDFRSTRANSITIONREL 
                (mkTRANSREL TR.(transrel))
                (dfrs_trans_rel_valid
                  (mkTRANSREL TR.(transrel))))
  in
    mkE_DFRS
      dfrs_variables (* Variables *)
      dfrs_states (* States *)
      dfrs_tr (* TRs *)
      (e_dfrs_valid dfrs_variables dfrs_states dfrs_tr).


