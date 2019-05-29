Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.

Require Import variables.
Require Import variables_fun_rules.
Require Import states.
Require Import util.
Require Import fun_util.

(* EXPRESSION *)
Inductive VAR : Type :=
  | current  : VNAME -> VAR
  | previous : VNAME -> VAR.

Inductive OP : Type :=
  | le : OP
  | lt : OP
  | eq : OP
  | ne : OP
  | gt : OP
  | ge : OP.
  
Definition is_valid_op (op : OP) (v : VALUE) : Prop :=
  match op with
  | le | lt | gt | ge => match v with
                         | b _ => False
                         | _   => True
                         end
  | _                 => True
  end.

Record BEXP : Set := mkBEXP {
  v : VAR ;
  op : OP ;
  literal : VALUE
}.

Definition ind_rules_disj (lb : list BEXP) : Prop :=
  0 < length lb.

Record DISJ : Set := mkDISJ {
  disjs : list BEXP
  
  ; rules_disj : ind_rules_disj disjs
}.

Record CONJ : Set := mkCONJ {
  conjs : list DISJ
}.

Definition EXP := CONJ.

Definition var_name (be : BEXP) : VNAME :=
  match be.(v) with
  | current vn  => vn
  | previous vn => vn
  end.
  
Fixpoint find_var_declaration (v : VNAME)
  (l : list (VNAME * TYPE)) : option (VNAME * TYPE) :=
    match l with
    | []     => None
    | h :: t => if bstring_dec (fst h).(vname)
                                v.(vname)
                then Some h
                else find_var_declaration v t
    end.

Definition var_consistent_be (be : BEXP)
  (f T : list (VNAME * TYPE)) : Prop :=
    let n := var_name be in
    let value := be.(literal) in
    let op := be.(op) in
    let dom_f := map (fun x => fst x) f in
    let dom_T := map (fun x => fst x) T in
    let var := find_var_declaration n f in
      in_list n dom_f comp_vname
      /\ match var with
         | None   => False
         | Some p => is_valid_value value (snd p)
         end
      /\ is_valid_op op value
      /\ if bin_list n dom_T bcomp_vname
         then match be.(v) with
              | current _ => True
              | _         => False
              end
         else True.
         
Definition var_consistent_dis (dis : DISJ)
  (f T : list (VNAME * TYPE)) : Prop :=
    fold_left and
      (map (fun be => var_consistent_be be f T)
           dis.(disjs))
      True.

Definition var_consistent_conj (con : CONJ)
  (f T : list (VNAME * TYPE)) : Prop :=
    fold_left and
      (map (fun dis => var_consistent_dis dis f T)
           con.(conjs))
      True.

Definition var_consistent_exp (exp : EXP)
  (f T : list (VNAME * TYPE)) : Prop :=
    var_consistent_conj exp f T.

(* ASSIGNMENT *)
Record ASGMT : Set := mkASGMT {
  asgmt : VNAME * VALUE
}.

Definition ind_rules_asgmts (l : list ASGMT) : Prop :=
  (0 < (length l))
  /\ is_function l 
        (fun (asgmt1 asgmt2 : ASGMT)
              => string_dec
                   (fst asgmt1.(asgmt)).(vname)
                   (fst asgmt2.(asgmt)).(vname)).

Record ASGMTS : Set := mkASGMTS {
  asgmts : list ASGMT
  
  ; rules_asgmts : ind_rules_asgmts asgmts
}.

Fixpoint is_valid_asgmts_names (la : list ASGMT)
  (ln : list VNAME) : Prop :=
    match la with
    | [] => True
    | h :: t =>
        in_list h ln
          (fun a v => comp_vname (fst a.(asgmt)) v)
        /\ is_valid_asgmts_names t ln
    end.

Definition well_typed_asgmts (a : ASGMTS)
  (f : list (VNAME * TYPE)) : Prop :=
    is_valid_asgmts_names a.(asgmts)
                          (map (fun x => fst x) f)
    /\ fold_left and
        (map (fun a => let var :=
                          find_var_declaration
                            (fst a.(asgmt)) f
                       in match var with
                          | None   => False
                          | Some p =>
                              is_valid_value 
                                (snd a.(asgmt))
                                (snd p)
                       end) a.(asgmts))
         True.

(* FUNCTION *)
Definition REQUIREMENT := string.

Definition ind_rules_function
  (l : list (EXP * EXP * ASGMTS * REQUIREMENT) )
  : Prop :=
    fold_left and
      (map
        (fun entry => 
          let sGuard := (fst (fst (fst entry))) in
          let tGuard := (snd (fst (fst entry))) in
            0 < List.length
                  (sGuard.(conjs) ++ tGuard.(conjs)))
        l) True.

Record FUNCTION : Set := mkFUNCTION {
  function : list (EXP * EXP * ASGMTS * REQUIREMENT) ;
  
  rules_function : ind_rules_function function
}.

Definition ind_rules_dfrs_functions
  (lf : list FUNCTION) : Prop :=
    0 < (List.length lf).

Record DFRS_FUNCTIONS : Set := mkDFRS_FUNCTIONS {
  F : list FUNCTION
  
  ; rules_dfrs_functions : ind_rules_dfrs_functions F
}.