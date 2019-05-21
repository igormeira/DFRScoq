Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.

Require Import functions.
Require Import variables.
Require Import variables_fun_rules.
Require Import state.
Require Import state_fun_rules.
Require Import fun_util.

(* EXPRESSION *)
Definition bis_valid_op (op : OP) (v : VALUE) : bool :=
  match op with
  | le | lt | gt | ge => match v with
                         | b _ => false
                         | _   => true
                         end
  | _                 => true
  end.

Definition fun_rules_disj (lb : list BEXP) : bool :=
  0 <? length lb.
  
Definition bvar_consistent_be (be : BEXP)
  (f T : list (VNAME * TYPE)) : bool :=
    let n := var_name be in
    let value := be.(literal) in
    let op := be.(op) in
    let dom_f := map (fun x => fst x) f in
    let dom_T := map (fun x => fst x) T in
    let var := find_var_declaration n f in
      bin_list n dom_f bcomp_vname
      && match var with
         | None   => false
         | Some p => bis_valid_value value (snd p)
         end
      && bis_valid_op op value
      && if bin_list n dom_T bcomp_vname
         then match be.(v) with
              | current _ => true
              | _         => false
              end
         else true.
         
Definition bvar_consistent_dis (dis : DISJ)
  (f T : list (VNAME * TYPE)) : bool :=
    fold_left andb
      (map (fun be => bvar_consistent_be be f T)
           dis.(disjs))
      true.

Definition bvar_consistent_conj (con : CONJ)
  (f T : list (VNAME * TYPE)) : bool :=
    fold_left andb
      (map (fun dis => bvar_consistent_dis dis f T)
           con.(conjs))
      true.

Definition bvar_consistent_exp (exp : EXP)
  (f T : list (VNAME * TYPE)) : bool :=
    bvar_consistent_conj exp f T.

(* ASSIGNMENT *)
Definition fun_rules_asgmts (l : list ASGMT) : bool :=
  (0 <? (length l))
  && bis_function l 
        (fun (asgmt1 asgmt2 : ASGMT)
              => bstring_dec
                   (fst asgmt1.(asgmt)).(vname)
                   (fst asgmt2.(asgmt)).(vname)).

Fixpoint bis_valid_asgmts_names (la : list ASGMT)
  (ln : list VNAME) : bool :=
    match la with
    | [] => true
    | h :: t =>
        bin_list h ln
          (fun a v => bcomp_vname (fst a.(asgmt)) v)
        && bis_valid_asgmts_names t ln
    end.

Definition bwell_typed_asgmts (a : ASGMTS)
  (f : list (VNAME * TYPE)) : bool :=
    bis_valid_asgmts_names a.(asgmts)
                          (map (fun x => fst x) f)
    && fold_left andb
        (map (fun a => let var :=
                          find_var_declaration
                            (fst a.(asgmt)) f
                       in match var with
                          | None   => false
                          | Some p =>
                              bis_valid_value 
                                (snd a.(asgmt))
                                (snd p)
                       end) a.(asgmts))
         true.

(* FUNCTION *)
Definition fun_rules_function
  (l : list (EXP * EXP * ASGMTS * REQUIREMENT) )
  : bool :=
    fold_left andb
      (map
        (fun entry => 
          let sGuard := (fst (fst (fst entry))) in
          let tGuard := (snd (fst (fst entry))) in
            0 <? List.length
                  (sGuard.(conjs) ++ tGuard.(conjs)))
        l) true.

Definition fun_rules_dfrs_functions
  (lf : list FUNCTION) : bool :=
    0 <? (List.length lf).