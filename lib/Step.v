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

Definition states_to_block (ss: list statement) : block := List.fold_right BlockCons BlockEmpty ss.

Fixpoint lookup_state (states: list State.state) (name: string) : option State.state := 
  match states with
  | List.nil => None
  | s :: states' => if String.eqb name (State.name s) then Some s else lookup_state states' name
  end.


Definition step (p: Parser.parser) (start: string) : env_monad string := 
  match lookup_state (Parser.states p) start with
  | Some nxt => 
    let* _ := evalStatement (BlockStatement (states_to_block (State.statements nxt))) in
      evalTransition (State.transition nxt)
  | None     => state_fail Internal
  end.

(* TODO: formalize progress with respect to a header, such that if the parser 
  always makes forward progress then there exists a fuel value for which
  the parser either rejects or accepts (or errors, but not due to lack of fuel) 
*)
Fixpoint step_trans (p: Parser.parser) (fuel: nat) (start: string) : env_monad unit := 
  match fuel with 
  | 0   => state_fail Internal (* TODO: add a separate exception for out of fuel? *)
  | S x => let* state' := step p start in 
    match state' with
    | "accept"    => mret tt
    | "reject"    => state_fail Reject
    | name    => step_trans p x name
    end
  end. 
  