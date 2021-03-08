Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Syntax.
Require Import Eval.
Require Import Environment.Environment.
Require Import Monads.Monad.
Require Import Monads.State.

Open Scope monad.
Open Scope string_scope.

Section Step.
  Context (tags_t: Type).
  Context (tags_dummy: tags_t).
  Notation P4String := (P4String.t tags_t).
  Notation Statement := (@Statement tags_t).
  Notation Block := (@Block tags_t).
  Notation ParserState := (@ParserState tags_t).
  Notation ParserCase := (@ParserCase tags_t).
  Notation ParserTransition := (@ParserTransition tags_t).
  Notation Value := (@Value tags_t).
  Notation ValueObject := (@ValueObject tags_t).
  Notation accept := ({|P4String.tags:=tags_dummy;
                        P4String.str:=StringConstants.accept|}).
  Notation reject := ({|P4String.tags:=tags_dummy;
                        P4String.str:=StringConstants.reject|}).


  Definition states_to_block (ss: list Statement) : Block :=
    List.fold_right BlockCons (BlockEmpty tags_dummy) ss.

  Fixpoint lookup_state (states: list ParserState) (name: P4String) : option ParserState :=
    match states with
    | List.nil => None
    | s :: states' =>
      let 'MkParserState _ s_name _ _ := s in
      if P4String.equivb name s_name
      then Some s
      else lookup_state states' name
    end.

  Definition step (p: ValueObject) (start: P4String) : env_monad tags_t P4String :=
    match p with
    | ValObjParser env _ params locals states =>
      match lookup_state states start with
      | Some nxt =>
        let 'MkParserState _ _ statements transition := nxt in
        let blk := StatBlock (states_to_block statements) in
        let* _ := eval_statement _ tags_dummy (MkStatement tags_dummy blk Typed.StmUnit) in
        eval_transition tags_t tags_dummy transition
      | None =>
        state_fail (AssertError "State not found.")
      end
    | _ => state_fail (AssertError "Value provided for stepping is not a parser.")
    end.

  (* TODO: formalize progress with respect to a header, such that if the parser
  always makes forward progress then there exists a fuel value for which
  the parser either rejects or accepts (or errors, but not due to lack of fuel)
   *)
  Fixpoint step_trans (p: ValueObject) (fuel: nat) (start: P4String) : env_monad tags_t unit :=
    match fuel with
    | 0   => state_fail (AssertError "Ran out of fuel.")
    | S x => let* state' := step p start in
            if P4String.equivb state' accept
            then mret tt
            else if P4String.equivb state' reject
            then state_fail Reject
            else step_trans p x state'
    end.

End Step.
