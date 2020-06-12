Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Require Import Bool.

From QuickChick Require Import QuickChick.
Import QcDefaultNotation. 
Import QcNotation. 

Open Scope qc_scope.

Import GenLow GenHigh.
(* Suppress some annoying warnings: *)
Set Warnings "-extraction-opaque-accessed,-extraction".

Require Export ExtLib.Structures.Monads.
Export MonadNotation.

Require Import fun_util.
Require Import functions_fun_ind_equiv.
Require Import s_dfrs.
Require Import trans_rel_fun_rules.
Require Import e_dfrs.
Require Import s2e_dfrs_fun_rules.

Require Import vm_tests.
Require Import npp_tests.
Require Import tis_tests.

Open Scope monad_scope.

Local Open Scope string.
(*=============== NAT ================*)

Fixpoint string_of_nat_aux (time n : nat) (acc : string) : string :=
  let d := match n mod 10 with
           | 0 => "0" | 1 => "1" | 2 => "2" | 3 => "3" | 4 => "4" | 5 => "5"
           | 6 => "6" | 7 => "7" | 8 => "8" | _ => "9"
           end in
  let acc' := d ++ acc in
  match time with
    | 0 => acc'
    | S time' =>
      match n / 10 with
        | 0 => acc'
        | n' => string_of_nat_aux time' n' acc'
      end
  end.

Definition string_of_nat (n : nat) : string :=
  string_of_nat_aux n n "".

Instance showNat : Show nat :=
  {
    show := string_of_nat
  }.

(*=============== END NAT ================*)

(*=============== INT ================*)
Local Open Scope Z_scope.

Fixpoint string_of_int_aux (time : nat) (i : Z) (acc : string) : string :=
  let d := match Zmod i 10 with
           | 0 => "0" | 1 => "1" | 2 => "2" | 3 => "3" | 4 => "4" | 5 => "5"
           | 6 => "6" | 7 => "7" | 8 => "8" | _ => "9"
           end in
  let acc' := d ++ acc in
  match time with
    | S time' => match Z.div i 10 with
                   | Z0  => acc'
                   | i' => string_of_int_aux time' i' acc'
                 end
    | O       => acc'
  end.

Definition string_of_int (i : Z) : string :=
  string_of_int_aux (Z.to_nat i) i "".

Local Close Scope Z_scope.

Instance showInt : Show Z :=
  {
    show := string_of_int
  }.

(*=============== END INT ================*)

(*=============== BOOL ================*)

Definition string_of_bool (b : bool) : string :=
  match b with
  | true  => "true"
  | false => "false"
  end.

Instance showBool : Show bool :=
  {
    show := string_of_bool
  }.

(*=============== END BOOL ================*)

(*=============== VALUE ================*)

Definition string_of_value (v : VALUE) :=
  match v with
  | b v' => "b " ++ show v'
  | i v' => "i " ++ show v'
  | n v' => "n " ++ show v'
  end.

Instance showValeu : Show VALUE :=
  {
    show := string_of_value
  }.

(*=============== END VALUE ================*)

(*=============== STATE ================*)

Fixpoint string_of_state_aux (l : list (NAME*(VALUE*VALUE))) (acc : string)
  : string :=
  match l with
  | []     => acc ++ "]"
  | h :: t => let
                item := "(" ++ show (fst h) ++ ", " ++ 
                          "(" ++ show (fst (snd h)) ++ ", " ++ 
                                 show (snd (snd h)) ++ ")); "
              in
                string_of_state_aux t (acc ++ item)
  end.

Definition string_of_state (s : STATE) :=
  string_of_state_aux s.(state) "[".

Instance showState : Show STATE :=
  {
    show := string_of_state
  }.

(*=============== END STATE ================*)

(*=============== ASGMTS ================*)

Definition beq_asgmt (a1 a2 : ASGMT) : bool :=
  (bstring_dec (fst a1.(asgmt)).(vname) (fst a2.(asgmt)).(vname))
  &&
  (beq_value (snd a1.(asgmt)) (snd a2.(asgmt))).

Fixpoint beq_asgmts (l1 l2 : list ASGMT) : bool :=
  match l1, l2 with
  | []      , []       => true
  | []      , _        => false
  | _       , []       => false
  | h1 :: t1, h2 :: t2 => if beq_asgmt h1 h2
                          then beq_asgmts t1 t2
                          else false
  end.

Definition string_of_asgmt (a : ASGMT) : string :=
  "(" ++ ((fst a.(asgmt)).(vname)) ++ ", " 
      ++ show (snd a.(asgmt)) ++ ")".

Instance showAsgmt : Show ASGMT :=
  {
    show := string_of_asgmt
  }.

Fixpoint string_of_asgmts_aux (l : list ASGMT) (acc : string) : string :=
  match l with
  | []     => acc ++ "]"
  | h :: t => let
                item := show h
              in
                match t with
                | [] => string_of_asgmts_aux t (acc ++ item)
                | _  => string_of_asgmts_aux t (acc ++ item ++ "; ")
                end
  end.

Definition string_of_asgmts (a : ASGMTS) : string :=
  string_of_asgmts_aux a.(asgmts) "[".

Instance showAsgmts : Show ASGMTS :=
  {
    show := string_of_asgmts
  }.

(*=============== END ASGMTS ================*)

(*=============== TRANSREL ================*)

Definition beq_trans_label (t1 t2 : TRANS_LABEL) : bool :=
  match t1, t2 with
  | func f1, func f2 => beq_asgmts (fst f1).(asgmts) (fst f2).(asgmts)
                        &&
                        bstring_dec (snd f1) (snd f2)
  | del d1 , del d2  => beq_delay (fst d1) (fst d2)
                        &&
                        beq_asgmts (snd d1).(asgmts) (snd d2).(asgmts)
  | _      , _       => false
  end.

Definition string_of_delay (d : DELAY) : string :=
  match d with
  | discrete d' => "discrete " ++ show d'
  end.

Instance showDelay : Show DELAY :=
  {
    show := string_of_delay
  }.

Definition string_of_trans_label (tl : TRANS_LABEL) : string :=
  match tl with
  | func tl' => "func (" ++ show (fst tl') ++ ", " ++ (snd tl') ++ ")"
  | del tl'  => "del (" ++ show (fst tl') ++ ", " ++ show (snd tl') ++ ")"
  end.

Instance showTransLabel : Show TRANS_LABEL :=
  {
    show := string_of_trans_label
  }.

Definition string_of_trans (t : TRANS) : string :=
  "(" ++ show (fst3 t.(STS)) 
      ++ " - " ++ show (snd3 t.(STS)) 
      ++ " -> " ++ show (trd3 t.(STS)) ++ ")".

Instance showTrans : Show TRANS :=
  {
    show := string_of_trans
  }.

Fixpoint string_of_transrel_aux (l : list TRANS) (acc : string) : string :=
  match l with
  | []     => acc
  | h :: t => let
                item := show h ++ "; "
              in
                match t with
                | [] => string_of_transrel_aux t (acc)
                | _  => string_of_transrel_aux t (acc ++ item)
                end
  end.

Definition string_of_transrel (tr : TRANSREL) : string :=
  string_of_transrel_aux tr.(transrel) "".

Instance showTransrel : Show TRANSREL :=
  {
    show := string_of_transrel
  }.

Local Close Scope string.

(*=============== END TRANSREL ================*)

Fixpoint getStateLabels (s : STATE) (lt : list TRANS) : list TRANS_LABEL :=
  match lt with
  | []      => []
  | h :: tl => if beq_state s (fst3 h.(STS))
               then snd3 h.(STS) :: getStateLabels s tl
               else getStateLabels s tl
  end.

Fixpoint nextState (s : STATE) (tl : TRANS_LABEL) 
  (lt : list TRANS) : STATE :=
  match lt with
  | []      => s
  | h :: t => if beq_state s (fst3 h.(STS))
                 &&
                 beq_trans_label tl (snd3 h.(STS))
              then trd3 h.(STS)
              else nextState s tl t
  end.

(*=============== TRACE ================*)

Definition trace := list TRANS_LABEL.

Fixpoint possible_labels (st : STATE) (l : list TRANS) : list TRANS_LABEL :=
  match l with
  | []     => []
  | h :: t => if beq_state st (fst3 h.(STS))
              then (snd3 h.(STS)) :: possible_labels st t
              else possible_labels st t
  end.

Definition Asgmt_qc1 : ASGMT.
Proof.
  apply (mkASGMT (the_coin_sensor, (b false))).
Defined.

Definition Asgmt_qc2 : ASGMT.
Proof.
  apply (mkASGMT (the_coffee_request_button, (b false))).
Defined.

Definition Asgmts_qc : ASGMTS.
Proof.
  apply (mkASGMTS [Asgmt_qc1; Asgmt_qc2]).
  apply theo_rules_asgmts. reflexivity.
Defined.

Definition next_label (st : STATE) (l : list TRANS) : G TRANS_LABEL :=
  let
    p := (possible_labels st l)
  in
  let
    tl := (del (discrete 999, Asgmts_qc))
  in
    if (List.length l) =? 0
    then elements (hd tl p) (tl :: p)
    else elements (hd tl p) p.

Fixpoint genValidTrace (st : STATE) (dfrs : s_DFRS)
(possibilities : list (VNAME * list VALUE))
  (size : nat) : G trace :=
  match size with
  | 0       => ret []
  | S size' => let
                  tr := (genTransitions st 
                            dfrs.(s_dfrs_variables).(I).(svars)
                            dfrs.(s_dfrs_variables).(O).(svars)
                            dfrs.(s_dfrs_variables).(T).(stimers)
                            [dfrs.(s_dfrs_functions).(F)]
                            possibilities).(transrel)
               in
               freq [
                      (1, ret []) ;
                      (size, x  <- next_label st tr ;;
                             xs <- genValidTrace (nextState st x tr)
                                      dfrs possibilities size' ;;
                             ret (x :: xs))
                     ]
  end.

Fixpoint string_of_trace_aux (t : trace) (acc : string) : string :=
  match t with
  | []     => acc ++ "]"
  | h :: tl => let
                item := show h
              in
                match tl with
                | [] => string_of_trace_aux tl (acc ++ item)
                | _  => string_of_trace_aux tl (acc ++ item ++ "; ")
                end
  end.

Definition string_of_trace (t : trace) : string :=
  string_of_trace_aux t "[".

(*=============== END TRACE ================*)

Fixpoint in_list_rq (rq : REQUIREMENT) (l : list TRANS_LABEL) : bool :=
  match l with
  | []     => false
  | h :: t => match h with
              | func f' => if bstring_dec (snd f') rq
                           then true
                           else in_list_rq rq t
              | del _   => in_list_rq rq t
              end
  end.

(*=============== VM ================*)

Definition vm_initial_state := VM_state.

Definition vm_possibilities := [(the_coin_sensor, [b false; b true]);
                                (the_coffee_request_button, [b false; b true])].

(*=============== END VM ================*)

(*=============== NPP ================*)

Definition npp_initial_state := npp_state.

Definition npp_possibilities := [(the_reset_button, [b false; b true]);
                                 (the_blockage_button, [b false; b true]);
                                 (the_water_pressure, [i 0; i 1; i 8; i 9; i 10; i 11])].

(*=============== END VM TRACE ================*)

(*=============== TIS ================*)

Definition tis_initial_state := tis_state.

Definition tis_possibilities := [(the_voltage, [i 0; i 1; i 79;i 80; i 81; i 82]);
                                (the_turn_indicator_lever, [i 0; i 1; i 2; i 3]);
                                (the_emergency_flashing, [i 0; i 1; i 2])].

(*=============== END TIS ================*)

Inductive test_purpose_step : Type :=
  | any_values : test_purpose_step
  | match_values : list (NAME * VALUE) -> test_purpose_step.

Definition test_purpose := list test_purpose_step.

Fixpoint get_variable_value
  (s_values : list (NAME * VALUE)) (n : NAME) : option VALUE :=
  match s_values with
  | []            => None
  | (n',v) :: tl  => if bstring_dec n' n then Some v
                     else get_variable_value tl n
  end.

Fixpoint match_state_values_aux
  (s_values : list (NAME * VALUE))
  (values : list (NAME * VALUE)) : bool :=
  match values with
  | []              => true
  | (name,v) :: tl  => match get_variable_value s_values name with
                       | None     => false
                       | Some v'  => beq_value v v'
                       end
  end.

Definition match_state_values (s : STATE) (values : list (NAME * VALUE)) : bool :=
  let s_values := map (fun (x : (NAME * (VALUE * VALUE)))
                            => (fst x, snd (snd x))) s.(state) in
  match_state_values_aux s_values values.

Definition get_fst_asgmts (t : trace) : ASGMTS :=
  match t with
  | []      => default_asgmts
  | h :: tl => match h with
               | func (a,r) => a
               | del (d,a)  => a
               end
  end.
  
Fixpoint next_match_values (tp : test_purpose) : option (list (NAME * VALUE)) :=
  match tp with
  | []            => None
  | tp_h :: tp_tl => match tp_h with
                     | any_values          => next_match_values tp_tl
                     | match_values values => Some values
                     end
  end.
  
Fixpoint values_tl (tp : test_purpose) : test_purpose :=
  match tp with
  | []            => []
  | tp_h :: tp_tl => match tp_h with
                     | any_values     => values_tl tp_tl
                     | match_values _ => tp_tl
                     end
  end.

Fixpoint match_purpose_trace (sdfrs : s_DFRS) (s : STATE)
  (t : trace) (tp : test_purpose) (size : nat) : bool :=
  let T := sdfrs.(s_dfrs_variables).(T).(stimers) in
  let s' := e_dfrs.nextState s T (get_fst_asgmts t) in
  match tp,size with
  | [], _                  => true
  | _, 0                   => false
  | tp_h :: tp_tl, S size' =>
      match tp_h with
      | any_values          => 
          let next_values := next_match_values tp_tl in
          match next_values with
          | None        => true
          | Some values => if match_state_values s' values
                           then match_purpose_trace sdfrs s' (List.tl t) (values_tl tp_tl) size'
                           else match_purpose_trace sdfrs s' (List.tl t) tp size'
           end
      | match_values values => if match_state_values s' values
                               then match_purpose_trace sdfrs s' (List.tl t) tp_tl size'
                               else false
      end
  end.

Local Close Scope string.
