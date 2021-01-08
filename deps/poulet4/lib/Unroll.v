Require Import Syntax.
Require Import Monads.Monad.
Require Import Monads.Option.
Require Import Step.
Require Import String.
Require Import Strings.String.

Open Scope list_scope.
Open Scope string_scope.


Section Unroll.
  Context (tags_t: Type).
  Context (tags_dummy: tags_t).

  (* Allocate a fresh name. For now, add a prime to the end of it. *)
  (* TODO make this sound *)
  Definition fresh_name (old: P4String tags_t) := 
    let 'MkP4String _ tag name := old in 
      MkP4String _ tag (name ++ "'").

  (* lift string equality to the P4String wrapper *)
  Definition P4Str_eqb (l: P4String tags_t) (r: P4String tags_t) : bool := 
    match (l, r) with 
    | (MkP4String _ _ l', MkP4String _ _ r') => eqb l' r'
    end.

  (* Given a transition, return a list of outgoing labels *)
  Definition label_of_trans (trans: ParserTransition tags_t) : list (P4String tags_t) :=
    match trans with 
    | ParserDirect _ _ x => x :: nil
    | ParserSelect _ _ _ cases => List.map (fun '(MkParserCase _ _ _ x) => x) cases
    end.

  (* Given a list of labels and a list of states, return a sublist of states corresponding to the labels *)
  Definition labels_to_states (labs: list (P4String tags_t)) (states: list (ParserState tags_t)) : list (ParserState tags_t) :=
    let l2st := fun '(MkP4String _ _ lab) => 
      match lookup_state _ states lab with
      | Some x => x :: nil
      | None => nil
      end in
    List.concat (List.map l2st labs).


  (* Given a set of visited labels and a start label, return a list of reachable labels
  from the start *)
  (* TODO: it should be the case that if fuel = | states |, then all reachable states are included in the result list *)
  (* TODO: to be more precise, this needs NoDup mixed in *)
  Fixpoint reachable_states (fuel: nat) (reached: list (P4String tags_t)) (start: P4String tags_t) (states: list (ParserState tags_t)) : list (P4String tags_t) :=
    (*   *)
    let 'MkP4String _ _ name := start in 
    match fuel, lookup_state _ states name with
    | 0, Some _ 
    | 0, None   => reached
    | S _, None => reached
    | S fuel', Some (MkParserState _ _ start_name _ trans) => 
      let outgoing_labels := label_of_trans trans in 
      let new_label := fun lab => negb (List.existsb (P4Str_eqb lab) reached) in
      let new_labels := (List.filter new_label outgoing_labels) in
        match new_labels with
        | nil => reached
        | _ => List.flat_map (fun start' => reachable_states fuel' (reached ++ new_labels) start' states) new_labels
        end

    end.

  Definition select_name (x: P4String tags_t) (old: P4String tags_t) (new: P4String tags_t):= 
    if P4Str_eqb x old then new else x.

  (* Given a parser, as well as an old name and new name, replace all transitions
  in parser that use the old name, to use the new name *)
  Definition rename_edge (p: ValueObject tags_t) (old: P4String tags_t) (new: P4String tags_t) : @option_monad (ValueObject tags_t) := 

    let rename_case := fun case => 
      let 'MkParserCase _ _ matches next := case in 
      MkParserCase tags_t tags_dummy matches (select_name next old new) 
    in
    let rename_transition := fun trans => 
      match trans with 
      | ParserDirect _ _ name => ParserDirect tags_t tags_dummy (select_name name old new)
      | ParserSelect _ _ exprs cases => ParserSelect tags_t tags_dummy exprs (List.map rename_case cases)
      end
    in
    let rename_state := fun '(MkParserState _ _ name stmts trans) =>
      MkParserState tags_t tags_dummy name stmts (rename_transition trans)
    in
    match p with
    | ValObjParser _ scope params locals states => 
      mret (ValObjParser _ scope params locals (List.map rename_state states))
    | _ => None
    end.

  (* Given a parser and an old/new pair of names, replace and substitute all states with the old name  *)
  Definition rename_state_name (p: ValueObject tags_t) (old: P4String tags_t) (new: P4String tags_t) : @option_monad (ValueObject tags_t) := 
    let rename_st_name := fun '(MkParserState _ _ name ss trans) => 
      MkParserState _ tags_dummy (select_name name old new) ss trans
    in
    match p with
    | ValObjParser _ scope params locals states => 
      mret (ValObjParser _ scope params locals (List.map rename_st_name states))
    | _ => None
    end.

  (* Definition rename_all_states  *)

  (* Definition replace_state (states : list (ParserState tags_t)) (name: P4String tags_t) (new: P4String tags_t) :=
    let relevant_states, old_states := List.partition (fun '(MkParserState _ _ n _ _) => P4Str_eqb n name) states in *)


  Definition up_state (acc: option (ValueObject tags_t)) (name : P4String tags_t) : option (ValueObject tags_t) :=
    match acc with
    | Some p => 
      let new_name := fresh_name name in
      let* p' := rename_state_name p name new_name in 
        rename_edge p' name new_name
    | None => None
    end. 
  
  (* Given a start state for a loop, duplicate it and give fresh names to all duplicated states *)
  Definition rename_loop (p: (ValueObject tags_t)) (loop_head: ParserState tags_t) : @option_monad (ValueObject tags_t) :=
    match p with
    | ValObjParser _ scope params locals states =>
      let 'MkParserState _ _ name _ _ := loop_head in
      let new_state_names := reachable_states (List.length states) nil name states in
        List.fold_left up_state new_state_names (Some p)
    | _ => mret p
    end.

 

  

  Definition unroll_loop (p: ValueObject tags_t) (loop_head: ParserState tags_t) : ValueObject tags_t :=
    let 'MkParserState _ _ name _ _ := loop_head in  
    let new_p := rename_edge p name (fresh_name name) in 
    match (new_p, rename_loop p loop_head, p) with
      | (Some p', Some (ValObjParser _ scope params locals states'), ValObjParser _ _ _ _ states) => 
        ValObjParser _ scope params locals (states ++ states')
      | _ => p (* maybe this case should be an error instead?*)
    end.
        
End Unroll.