Require Import Strings.String.
Require Import Coq.Bool.Bool.
Require Import Coq.ZArith.BinInt.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Program.Program.
Require Import Typed.
Require Import Syntax.
Require Import P4Int.
Require Import Target.
Require Import Maps.
Import ListNotations.

Section V1Model.

Context {tags_t: Type}.
Context {Expression: Type}.
Notation ident := (P4String.t tags_t).
Notation path := (list ident).
Notation Val := (@ValueBase tags_t).
Notation table_entry := (@table_entry tags_t Expression).
Notation action_ref := (@action_ref tags_t Expression).

Inductive register := mk_register {
  reg_size : Z;
  reg_content : list bool
}.

Definition new_register (size : Z) :=
  mk_register size (repeat false (Z.to_nat size)).

Definition extern_state := @PathMap.t tags_t register.

Definition extern_empty : extern_state := PathMap.empty.

Axiom dummy_tag : tags_t.
Definition register_string : ident := {| P4String.tags := dummy_tag; P4String.str := "register" |}.

Definition alloc_extern (s : extern_state) (class : ident) (p : path) (args : list Val) :=
  if P4String.equivb class register_string then
    match args with
    | [ValBaseInteger size]
    | [ValBaseBit _ size]
    | [ValBaseInt _ size] =>
        PathMap.set p (new_register size) s
    | _ => s
    end
  else
    s.

Axiom exec_extern : extern_state -> ident (* class *) -> ident (* method *) -> path -> list Val -> extern_state -> list Val -> option Val -> Prop.

Axiom extern_get_entries : extern_state -> path -> list table_entry.

Axiom extern_match : list (Val * ident) -> list table_entry -> option action_ref.

Instance V1ModelExternSem : ExternSem := Build_ExternSem
  extern_state
  extern_empty
  alloc_extern
  exec_extern
  extern_get_entries
  extern_match.

Axiom exec_prog : (path -> extern_state -> list Val -> extern_state -> list Val -> Prop) -> Prop.

Instance V1Model : Target := Build_Target _ exec_prog.

End V1Model.
