Require Import Coq.Lists.List.
Require Import Syntax.
Require Import Eval.
Require Import Environment.
Require Import Monads.Monad.
Require Import Monads.State.
Require Import CamlString.

Open Scope monad.

Section Step.
  Context (tags_t: Type).
  Context (tags_dummy: tags_t).

  Definition states_to_block (ss: list (Statement tags_t)) : Block tags_t :=
    List.fold_right (BlockCons _) (BlockEmpty _ tags_dummy) ss.

  Fixpoint lookup_state (states: list (ParserState tags_t)) (name: caml_string) : option (ParserState tags_t) := 
    match states with
    | List.nil => None
    | s :: states' =>
      let 'MkParserState _ _ (MkP4String _ _ s_name) _ _ := s in
      if caml_string_eqb name s_name
      then Some s
      else lookup_state states' name
    end.

  Definition step (p: (ValueObject tags_t)) (start: caml_string) : env_monad tags_t caml_string := 
    match p with
    | ValObjParser _ env params locals states =>
      match lookup_state states start with
      | Some nxt => 
        let 'MkParserState _ _ _ statements transition := nxt in
        let blk := StatBlock _ (states_to_block statements) in
        let* _ := eval_statement _ tags_dummy (MkStatement _ tags_dummy blk Typed.StmUnit) in
        eval_transition tags_t tags_dummy transition
      | None =>
        state_fail Internal
      end
    | _ => state_fail Internal
    end.

  (* TODO: formalize progress with respect to a header, such that if the parser 
  always makes forward progress then there exists a fuel value for which
  the parser either rejects or accepts (or errors, but not due to lack of fuel) 
   *)
  Fixpoint step_trans (p: ValueObject tags_t) (fuel: nat) (start: caml_string) : env_monad tags_t unit := 
    match fuel with 
    | 0   => state_fail Internal (* TODO: add a separate exception for out of fuel? *)
    | S x => let* state' := step p start in 
            if caml_string_eqb state' StrConstants.accept
            then mret tt
            else if caml_string_eqb state' StrConstants.reject
            then state_fail Reject
            else step_trans p x state'
    end.

End Step.
