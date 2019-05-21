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
Require Import pc_tests.

Open Scope monad_scope.

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
  
Check elements.

(* TODO: elements x elems x elems_ *)
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

Definition initial_state := vm_state.

Definition vm_possibilities := [(the_coin_sensor, [b false; b true]);
                                (the_coffee_request_button, [b false; b true])].

(*=============== END VM ================*)

(*=============== NPP ================*)

Definition npp_initial_state := npp_state.

Definition npp_possibilities := [(the_reset_button, [b false; b true]);
                                 (the_blockage_button, [b false; b true]);
                                 (the_water_pressure, [i 0; i 10; i 9])].

(*=============== END VM TRACE ================*)

(*=============== PC ================*)

Definition pc_initial_state := pc_state.

Definition pc_possibilities := [(the_left_command, [b false; b true]);
                                (the_left_priority_button, [b false; b true]);
                                (the_right_command, [b false; b true]);
                                (the_right_priority_button, [b false; b true])].

(*=============== END PC ================*)

(*

(*=============== TRACE VM_REQ005 ================*)

Definition asgmt_coin_true : ASGMT.
Proof.
  apply (mkASGMT (the_coin_sensor, (b true))).
Defined.

Definition asgmt_coin_false : ASGMT.
Proof.
  apply (mkASGMT (the_coin_sensor, (b false))).
Defined.

Definition asgmt_coffee_true : ASGMT.
Proof.
  apply (mkASGMT (the_coffee_request_button, (b true))).
Defined.

Definition asgmt_coffee_false : ASGMT.
Proof.
  apply (mkASGMT (the_coffee_request_button, (b false))).
Defined.

Definition asgmts1 : ASGMTS.
Proof.
  apply (mkASGMTS [asgmt_coin_true ; asgmt_coffee_false]).
  apply theo_rules_asgmts. reflexivity.
Defined.

Definition asgmts2 : ASGMTS.
Proof.
  apply (mkASGMTS [asgmt_coin_false ; asgmt_coffee_true]).
  apply theo_rules_asgmts. reflexivity.
Defined.

Definition asgmts3 : ASGMTS.
Proof.
  apply (mkASGMTS [asgmt_coin_false ; asgmt_coffee_false]).
  apply theo_rules_asgmts. reflexivity.
Defined.

Definition del1 : TRANS_LABEL := del ((discrete 1), asgmts1).
Definition del2 : TRANS_LABEL := del ((discrete 1), asgmts2).
Definition del3 : TRANS_LABEL := del ((discrete 1), asgmts3).

Definition idle_del : STATE :=
  let
    tr := (genTransitions vm_s_dfrs.(s_dfrs_initial_state).(s0)
            vm_s_dfrs.(s_dfrs_variables).(I).(svars)
            vm_s_dfrs.(s_dfrs_variables).(O).(svars)
            vm_s_dfrs.(s_dfrs_variables).(T).(stimers)
            [vm_s_dfrs.(s_dfrs_functions).(F)]
            vm_possibilities).(transrel)
  in
    nextState vm_s_dfrs.(s_dfrs_initial_state).(s0) del1 tr.

(* Compute (show idle_del). *)

Definition dummy_trans : TRANS := mkTRANS (idle_del, del1, idle_del).

Definition choice : STATE :=
  let
    tr := (genTransitions idle_del
            vm_s_dfrs.(s_dfrs_variables).(I).(svars)
            vm_s_dfrs.(s_dfrs_variables).(O).(svars)
            vm_s_dfrs.(s_dfrs_variables).(T).(stimers)
            [vm_s_dfrs.(s_dfrs_functions).(F)]
            vm_possibilities).(transrel)
  in
  let
    fun_label := snd3 (hd dummy_trans tr).(STS)
  in    
    nextState idle_del fun_label tr.

(* Compute (show choice). *)

Fixpoint advance_time (s : STATE) (n : nat) : STATE :=
  match n with
  | 0     => s
  | S n'  => 
        let
          tr := (genTransitions s
                  vm_s_dfrs.(s_dfrs_variables).(I).(svars)
                  vm_s_dfrs.(s_dfrs_variables).(O).(svars)
                  vm_s_dfrs.(s_dfrs_variables).(T).(stimers)
                  [vm_s_dfrs.(s_dfrs_functions).(F)]
                  vm_possibilities).(transrel)
        in
          advance_time (nextState s del3 tr) n'
  end.

Definition choice_del : STATE := advance_time choice 30.

(* Compute (show choice_del). *)

Definition choice_del' : STATE :=
  let
    tr := (genTransitions choice_del
            vm_s_dfrs.(s_dfrs_variables).(I).(svars)
            vm_s_dfrs.(s_dfrs_variables).(O).(svars)
            vm_s_dfrs.(s_dfrs_variables).(T).(stimers)
            [vm_s_dfrs.(s_dfrs_functions).(F)]
            vm_possibilities).(transrel)
  in
    nextState choice_del del2 tr.

(* Compute (show choice_del'). *)

Definition strong : STATE :=
  let
    tr := (genTransitions choice_del'
            vm_s_dfrs.(s_dfrs_variables).(I).(svars)
            vm_s_dfrs.(s_dfrs_variables).(O).(svars)
            vm_s_dfrs.(s_dfrs_variables).(T).(stimers)
            [vm_s_dfrs.(s_dfrs_functions).(F)]
            vm_possibilities).(transrel)
  in
  let
    fun_label := snd3 (hd dummy_trans tr).(STS)
  in    
    nextState choice_del' fun_label tr.

(* Compute (show strong). *)

Definition strong_del : STATE := advance_time strong 30.

(* Compute (show strong_del). *)

(* Compute ((genTransitions strong_del
            vm_s_dfrs.(s_dfrs_variables).(I).(svars)
            vm_s_dfrs.(s_dfrs_variables).(O).(svars)
            vm_s_dfrs.(s_dfrs_variables).(T).(stimers)
            [vm_s_dfrs.(s_dfrs_functions).(F)]
            vm_possibilities).(transrel)). *)

Definition produce_strong : STATE :=
  let
    tr := (genTransitions strong_del
            vm_s_dfrs.(s_dfrs_variables).(I).(svars)
            vm_s_dfrs.(s_dfrs_variables).(O).(svars)
            vm_s_dfrs.(s_dfrs_variables).(T).(stimers)
            [vm_s_dfrs.(s_dfrs_functions).(F)]
            vm_possibilities).(transrel)
  in
  let
    fun_label := snd3 (hd dummy_trans tr).(STS)
  in    
    nextState strong_del fun_label tr.

(* Compute (show produce_strong). *)

(* TODO: refletir sobre modificar o genValidTrace para
  ao gerar um trace que cont\u00e9m o label do requisito de interesse
  j\u00e1 parar de gerar traces. Contudo, ao gerar v\u00e1rios contraexemplos
  para um certo requisito, pode ser que tenhamos um trace
  onde o label de interesse ocorra mais de uma vez. *)

(* TODO: timeout, tentar com nova abordagem
QuickChick (forAll (genValidTrace
                    (initial_state)
                    (trans 10000) 
                    5000) 
                   test_exist_func5).
*)


*)


