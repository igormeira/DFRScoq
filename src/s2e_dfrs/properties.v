Require Import Coq.Lists.List.
Import ListNotations.

Require Import states.
Require Import trans_rel.
Require Import s_dfrs.
Require Import e_dfrs.
Require Import s2e_dfrs_fun_rules.

Fixpoint reached_func_state (sdfrs : s_DFRS) (s : STATE) (trace : list TRANS_LABEL) : STATE :=
  match trace with
  | []      => s
  | h :: tl => let T := sdfrs.(s_dfrs_variables).(T) in
               match h with
               | func (a, req) => reached_func_state sdfrs
                                    (nextState s T.(stimers) a) tl
               | del _         => s
               end
  end.
  
Inductive ind_func_trace : s_DFRS -> STATE -> list TRANS_LABEL -> Prop :=
  | func_traces_empty :
    forall (sdfrs : s_DFRS) (s : STATE),
      let I   := sdfrs.(s_dfrs_variables).(I).(svars) in
      let O   := sdfrs.(s_dfrs_variables).(O).(svars) in
      let T   := sdfrs.(s_dfrs_variables).(T).(stimers) in
      let IOT := List.app (List.app I O) T in
      let All := List.app ([sdfrs.(s_dfrs_variables).(gcvar)])
                          (map (fun x : (VNAME * TYPE) 
                            => ((fst x).(vname), snd x)) IOT) in
      let F := sdfrs.(s_dfrs_functions).(F) in      
        well_typed_state s All /\
        (is_stable s (List.app I O) T [F]) = false
        -> ind_func_trace sdfrs s []
  | func_traces_step :
    forall (sdfrs : s_DFRS) (s : STATE) (t : list TRANS_LABEL),
      let I := sdfrs.(s_dfrs_variables).(I).(svars) in
      let O := sdfrs.(s_dfrs_variables).(O).(svars) in
      let T := sdfrs.(s_dfrs_variables).(T).(stimers) in
      let IOT := List.app (List.app I O) T in
      let All := List.app ([sdfrs.(s_dfrs_variables).(gcvar)])
                          (map (fun x : (VNAME * TYPE) 
                            => ((fst x).(vname), snd x)) IOT) in
      let F := sdfrs.(s_dfrs_functions).(F) in
      let entries := union_lists
                      (map (fun f : FUNCTION => f.(function)) (union_lists [F])) in
        well_typed_state s All /\
        (is_stable s (List.app I O) T [F]) = false
        /\ ind_func_trace sdfrs s t
        -> forall (s' : STATE), s' = reached_func_state sdfrs s t
           /\ (is_stable s' (List.app I O) T [F]) = false
           -> let L := map (fun (t : TRANS) => snd3 t.(STS))
                           (make_trans_func s' (I ++ O) T entries) in
              forall (l : TRANS_LABEL), In l L -> ind_func_trace sdfrs s (t ++ [l]).

Definition deterministic (sdfrs: s_DFRS) : Prop :=
  let I := sdfrs.(s_dfrs_variables).(I).(svars) in
  let O := sdfrs.(s_dfrs_variables).(O).(svars) in
  let T := sdfrs.(s_dfrs_variables).(T).(stimers) in
  let F := sdfrs.(s_dfrs_functions).(F) in
  forall (s : STATE) (t1 t2 : list TRANS_LABEL),
    let s1 := reached_func_state sdfrs s t1 in
    let s2 := reached_func_state sdfrs s t2 in
    ind_func_trace sdfrs s t1 /\ ind_func_trace sdfrs s t2 /\
    (is_stable s1 (List.app I O) T [F]) = true /\
    (is_stable s2 (List.app I O) T [F]) = true
    -> s1 = s2.
    
Fixpoint visited_func_states (sdfrs : s_DFRS) (s : STATE) (trace : list TRANS_LABEL) : list STATE :=
  match trace with
  | []      => []
  | h :: tl => let T := sdfrs.(s_dfrs_variables).(T) in
               match h with
               | func (a, req) => s ::
                                  visited_func_states sdfrs
                                    (nextState s T.(stimers) a) tl
               | del _         => []
               end
  end.

Fixpoint count_occ_states (l : list STATE) (s : STATE) : nat :=
  match l with
  | [] => 0
  | s' :: tl => let n := count_occ_states tl s in
                if beq_state s s' then S n else n
  end.

Definition no_time_lock (sdfrs : s_DFRS) : Prop :=
  forall (s : STATE) (t : list TRANS_LABEL),
    let S := visited_func_states sdfrs s t in
    ind_func_trace sdfrs s t -> count_occ_states S s = 1.