Require Import Strings.String.
Require Import Coq.Bool.Bool.
Require Import Coq.ZArith.BinInt.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Program.Program.
Require Import Typed.
Require Import Syntax.
Require Import P4Int.

Section Target.

Context {tags_t: Type}.
Notation ident := (P4String.t tags_t).
Notation path := (list ident).
Notation Val := (@ValueBase tags_t).

(* We want to share the notation of External between P4light and P4cub, so later we need to
  have a parameter `ActionRef`, while `Match` is just shared. *)
(* Because the entries can refer to constructor parameters, we need to refer the arguments as expressions. *)
(* Maybe we can just use the definition in Syntax.v. *)

Context {Expression : Type}.

Inductive action_ref :=
  mk_action_ref (action : ident) (args : list (option Expression)).

Inductive table_entry :=
  (* TODO replace Expression in Match with Val. *)
  mk_table_entry (matches : list (@Match tags_t)) (action : action_ref).

Class ExternSem := {
  extern_state : Type;
  extern_empty : extern_state;
  (* Allocation should be a function; calling may be fine as a relation. *)
  alloc_extern : extern_state -> ident (* class *) -> list (@P4Type tags_t) -> path -> list Val -> extern_state;
  exec_extern : extern_state -> ident (* class *) -> ident (* method *) -> path -> list Val -> extern_state -> list Val -> option Val -> Prop;
  extern_get_entries : extern_state -> path -> list table_entry;
  extern_match : list (Val * ident (* match_kind *)) -> list table_entry -> option action_ref (* action *)
}.

Class Target := {
  extern_sem : ExternSem;
  exec_prog : (path -> extern_state -> list Val -> extern_state -> list Val -> Prop) -> Prop
}.

End Target.