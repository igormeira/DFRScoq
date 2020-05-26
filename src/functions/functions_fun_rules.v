Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.

Require Import functions.
Require Import variables.
Require Import variables_fun_rules.
Require Import states.
Require Import states_fun_rules.
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
         
Fixpoint bvar_consistent_dis
(disjs : list BEXP) (f T : list (VNAME * TYPE)) : bool :=
  match disjs with
  | []      => true
  | h :: tl => bvar_consistent_be h f T
               && bvar_consistent_dis tl f T
  end.

Fixpoint bvar_consistent_conj (conjs : list DISJ)
  (f T : list (VNAME * TYPE)) : bool :=
  match conjs with
  | []      => true
  | h :: tl => bvar_consistent_dis h.(disjs) f T
               && bvar_consistent_conj tl f T
  end.

Definition bvar_consistent_exp (exp : EXP)
  (f T : list (VNAME * TYPE)) : bool :=
    bvar_consistent_conj exp.(conjs) f T.

(* ASSIGNMENT *)
Definition fun_rules_asgmts (l : list ASGMT) : bool :=
  (0 <? (length l))
  && bis_function l 
        (fun (asgmt1 asgmt2 : ASGMT)
              => bstring_dec
                   (fst asgmt1.(asgmt)).(vname)
                   (fst asgmt2.(asgmt)).(vname)).

Fixpoint bis_valid_asgmts_names 
  (la : list ASGMT) (ln : list VNAME) : bool :=
    match la with
    | [] => true
    | h :: t =>
        bin_list h ln
          (fun a v => bcomp_vname (fst a.(asgmt)) v)
        && bis_valid_asgmts_names t ln
    end.

Fixpoint bwell_typed_asgmts 
  (la : list ASGMT) (f : list (VNAME * TYPE)) : bool :=
    bis_valid_asgmts_names la (map (fun x => fst x) f)
    && 
    (
      match la with
      | []      => true
      | h :: tl => (let 
                      var := find_var_declaration (fst h.(asgmt)) f
                    in 
                     match var with
                     | None   => false
                     | Some p =>
                         bis_valid_value 
                           (snd h.(asgmt))
                           (snd p)
                     end
                   ) && bwell_typed_asgmts tl f
      end
    ).

(* FUNCTION *)
Fixpoint fun_rules_function
  (l : list (EXP * EXP * ASGMTS * REQUIREMENT) ) : bool :=
    match l with
    | []      => true
    | h :: tl => (
                  let
                    sGuard := (fst (fst (fst h)))
                  in
                  let
                    tGuard := (snd (fst (fst h)))
                  in
                  0 <? List.length
                  (sGuard.(conjs) ++ tGuard.(conjs))
                 ) && fun_rules_function tl
    end.

Definition fun_rules_dfrs_functions
  (lf : list FUNCTION) : bool :=
    0 <? (List.length lf).