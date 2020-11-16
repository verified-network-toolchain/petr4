Require Import Syntax.
Require Import Eval.
Require Import Environment.
Require Import Monads.Monad.
Require Import Monads.State.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.

Open Scope monad.
(* Open Scope list_scope. *)

(* Open Scope string_scope. *)

Section Step.
  Context `{tags_inst: Tags}.
  Definition states_to_block (ss: list Statement) : Block :=
    List.fold_right BlockCons (BlockEmpty tags_dummy nil) ss.

  Fixpoint lookup_state (states: list ParserState) (name: string) : option ParserState := 
    match states with
    | List.nil => None
    | s :: states' =>
      let 'MkParserState _ _  s_name _ _ := s in
      if String.eqb name (snd s_name)
      then Some s
      else lookup_state states' name
    end.


  Definition step (p: ValueParser) (start: string) : env_monad string := 
    let 'MkValueParser env params cparams locals states := p in
    match lookup_state states start with
    | Some nxt => 
      let 'MkParserState _ _ _ statements transition := nxt in
      let blk := StatBlock (states_to_block statements) in
      let* _ := eval_statement (MkStatement tags_dummy blk Typed.StmUnit) in
      eval_transition transition
    | None =>
      state_fail Internal
    end.

  (* TODO: formalize progress with respect to a header, such that if the parser 
  always makes forward progress then there exists a fuel value for which
  the parser either rejects or accepts (or errors, but not due to lack of fuel) 
   *)
  Fixpoint step_trans (p: ValueParser) (fuel: nat) (start: string) : env_monad unit := 
    match fuel with 
    | 0   => state_fail Internal (* TODO: add a separate exception for out of fuel? *)
    | S x => let* state' := step p start in 
            match state' with
            | "accept"    => mret tt
            | "reject"    => state_fail Reject
            | name    => step_trans p x name
            end
    end. 
  
End Step.
