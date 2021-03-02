Require Import Syntax.
Require Import Monads.Monad.
Require Import Monads.Option.
Require Import Step.
Require Import Strings.String.
Require Import P4String.

Open Scope list_scope.
Open Scope string_scope.


Section Unroll.
  Context (tags_t: Type).
  Context (tags_dummy: tags_t).

  Notation P4String := (P4String.t tags_t).

  Definition builtin_state_name (x: P4String) : bool :=
    orb (eqb x.(P4String.str) StringConstants.accept)
        (eqb x.(P4String.str) StringConstants.reject).

  (* Allocate a fresh name. For now, add a prime to the end of it. *)
  (* TODO make this sound *)
  Definition fresh_name (old: P4String) :=
    if builtin_state_name old then old else
    {| P4String.tags := tags_dummy;
       P4String.str := old.(P4String.str) ++ "'" |}
  .

  (* Given a transition, return a list of outgoing labels *)
  Definition label_of_trans (trans: ParserTransition) : list P4String :=
    match trans with
    | ParserDirect _ x => x :: nil
    | ParserSelect _ _ cases => List.map (fun '(MkParserCase _ _ x) => x) cases
    end.

  (* Given a list of labels and a list of states, return a sublist of states corresponding to the labels *)
  Definition labels_to_states (labs: list P4String) (states: list ParserState) : list ParserState :=
    let l2st := fun lab =>
      match lookup_state _ states lab with
      | Some x => x :: nil
      | None => nil
      end in
    List.concat (List.map l2st labs).

  Fixpoint nodup' (l : list P4String) : list P4String :=
    match l with
    | nil => nil
    | x :: xs => if (List.existsb (equivb x) xs) then nodup' xs else x :: nodup' xs
    end.

  (* Given a set of visited labels and a start label, return a list of reachable labels
  from the start *)
  (* TODO: it should be the case that if fuel = | states |, then all reachable states are included in the result list *)
  Fixpoint reachable_states (fuel: nat) (reached: list P4String) (start: P4String) (states: list ParserState) : list P4String :=
    (*   *)
    match fuel, lookup_state _ states start with
    | 0, Some _
    | 0, None   => reached
    | S _, None => reached
    | S fuel', Some (MkParserState _ start_name _ trans) =>
      let outgoing_labels := label_of_trans trans in
      let new_label := fun lab => negb (List.existsb (equivb lab) reached) in
      let new_labels := nodup' (List.filter new_label outgoing_labels) in
        match new_labels with
        | nil => reached
        | _ => nodup' (List.flat_map (fun start' => reachable_states fuel' (nodup' (reached ++ new_labels)) start' states) new_labels)
        end

    end.

  Definition select_name (x: P4String) (old: P4String) (new: P4String):=
    if equivb x old then new else x.

  Definition rename_case (old: P4String) (new: P4String) (case: ParserCase) : ParserCase :=
    let 'MkParserCase _ matches next := case in
    MkParserCase tags_dummy matches (select_name next old new).

  Definition rename_transition (old: P4String) (new: P4String) (trans: ParserTransition) :=
    match trans with
    | ParserDirect _ name => ParserDirect tags_dummy (select_name name old new)
    | ParserSelect _ exprs cases => ParserSelect tags_dummy exprs (List.map (rename_case old new) cases)
    end.

  Definition rename_state (old: P4String) (new: P4String) (state: ParserState) :=
    let 'MkParserState _ name stmts trans := state in
      MkParserState tags_dummy name stmts (rename_transition old new trans).

  (* Given a parser, as well as an old name and new name, replace all transitions
  in parser that use the old name, to use the new name *)
  Definition rename_edge (p: ValueObject) (old: P4String) (new: P4String) : @option_monad ValueObject :=
    match p with
    | ValObjParser scope constructor_params params locals states =>
      mret (ValObjParser scope constructor_params params locals (List.map (rename_state old new) states))
    | _ => None
    end.

  (* Given a parser and an old/new pair of names, replace and substitute all states with the old name  *)
  Definition rename_state_name (p: ValueObject) (old: P4String) (new: P4String) : @option_monad ValueObject :=
    let rename_st_name := fun '(MkParserState _ name ss trans) =>
      MkParserState tags_dummy (select_name name old new) ss trans
    in
    match p with
    | ValObjParser scope constructor_params params locals states =>
      mret (ValObjParser scope constructor_params params locals (List.map rename_st_name states))
    | _ => None
    end.

  Definition up_state (acc: option ValueObject) (name : P4String) : option ValueObject :=
    match acc with
    | Some p =>
      let new_name := fresh_name name in
      let* p' := rename_state_name p name new_name in
        rename_edge p' name new_name
    | None => None
    end.

  Definition in_list (l: list P4String) (x: P4String) : bool := List.existsb (equivb x) l.

  (* Given a start state for a loop, duplicate it and give fresh names to all duplicated states.
    return a tuple of stale state names and new states. *)
  Definition rename_loop (p: ValueObject) (loop_head: ParserState) : option (list P4String * list ParserState) :=
    match p return option (list P4String * list ParserState) with
    | ValObjParser scope constructor_params params locals states =>
      let 'MkParserState tags_dummy name _ _ := loop_head in
      let new_state_names := reachable_states (List.length states) nil name states in
      let stale_state_check := fun st =>
        let 'MkParserState _ name' _ _ := st in
        in_list new_state_names name'
      in
      let new_parser := List.fold_left up_state new_state_names (Some (ValObjParser scope constructor_params params locals (List.filter stale_state_check states))) in
      match new_parser return option (list P4String * list ParserState) with
      | Some (ValObjParser _ _ _ _ ss') => Some (new_state_names, ss')
      | _ => Some (nil, nil)
      end
    | _ => Some (nil, nil)
    end.

  Definition update_stale_name (old: P4String) (new: P4String) (acc: list ParserState) (stale: P4String) : list ParserState :=
    List.map (rename_state old new) acc.

  Definition rename_stale_states (states: list ParserState) (stales: list P4String) (old: P4String) (new: P4String) : list ParserState :=
    let stale_state_check := fun st =>
        let 'MkParserState _ name' _ _ := st in
        in_list stales name'
      in
    let (stale_states, ok_states) := List.partition stale_state_check states in

    ok_states ++ List.fold_left (update_stale_name old new) stales stale_states.


  Definition unroll_loop (p: ValueObject) (loop_head: ParserState) : ValueObject :=
    let 'MkParserState _ name _ _ := loop_head in
    let new_name := fresh_name name in
    match (rename_loop p loop_head, p) with
      | (Some (stale_names, states'), ValObjParser scope constructor_params params locals states) =>
        let unrolled_states := rename_stale_states states stale_names name new_name in
          ValObjParser scope constructor_params params locals ( unrolled_states ++ states')
      | _ => p (* maybe this case should be an error instead?*)
    end.

End Unroll.
