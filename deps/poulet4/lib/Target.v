Require Import Strings.String.
Require Import Coq.Bool.Bool.
Require Import Coq.ZArith.BinInt.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Program.Program.
Require Import Poulet4.Typed.
Require Import Poulet4.Syntax.
Require Import Poulet4.SyntaxUtil.
Require Import Poulet4.P4Int.
Require Import Poulet4.Maps.

Section Target.

Context {tags_t: Type}.
Notation ident := (P4String.t tags_t).
Notation path := (list ident).
Notation Val := (@ValueBase tags_t).
Notation signal := (@signal tags_t).

Fixpoint width_of_val (v: Val): nat :=
  let fix fields_width (fields: P4String.AList tags_t ValueBase) : nat :=
      match fields with
      | nil => O
      | (id, v) :: rest => width_of_val v + fields_width rest
      end in
  match v with
  | ValBaseNull => O
  | ValBaseBool _ => 1
  | ValBaseBit w _
  | ValBaseInt w _
  | ValBaseVarbit _ w _ => w
  | ValBaseStruct fields
  | ValBaseHeader fields _ => fields_width fields
  | ValBaseSenumField _ _ v => width_of_val v
  | _ => O
  end.

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
  exec_extern : extern_state -> ident (* class *) -> ident (* method *) -> path -> list (@P4Type tags_t) -> list Val -> extern_state -> list Val -> signal -> Prop;
  extern_get_entries : extern_state -> path -> list table_entry;
  extern_match : list (Val * ident (* match_kind *)) -> list table_entry -> option action_ref (* action *)
}.

Class SeparableExternSem := {
  extern_object : Type;
  (* extern_state := @IdentMap.t tags_t extern_object; *)
  (* extern_empty : extern_state := IdentMap.empty; *)
  (* Allocation should be a function; calling may be fine as a relation. *)
  ses_alloc_extern : ident (* class *) -> list (@P4Type tags_t) -> list Val -> extern_object;
  ses_exec_extern : ident (* class *) -> ident (* method *) -> extern_object -> list (@P4Type tags_t) -> list Val -> extern_object -> list Val -> signal -> Prop;
  (* ses_extern_get_entries : extern_state -> path -> list table_entry; *)
  ses_extern_match : list (Val * ident (* match_kind *)) -> list table_entry -> option action_ref (* action *)
}.

Section ExternSemOfSeparableExternSem.
Context (ses : SeparableExternSem).

Definition extern_state' : Type := @PathMap.t tags_t extern_object * @PathMap.t tags_t (list table_entry).

Inductive exec_extern' : extern_state' -> ident (* class *) -> ident (* method *) -> path -> list (@P4Type tags_t) -> list Val -> extern_state' -> list Val -> signal -> Prop :=
  | exec_extern_intro : forall s class method targs p args s' args' vret obj obj',
      PathMap.get p (fst s) = Some obj ->
      ses_exec_extern class method obj targs args obj' args' vret ->
      (PathMap.set p obj' (fst s), snd s) = s' ->
      exec_extern' s class method p targs args s' args' vret.

Definition extern_get_entries' (s : extern_state') p :=
  match PathMap.get p (snd s) with
  | Some entries => entries
  | None => nil
  end.

Definition ExternSemOfSeparableExternSem := {|
  extern_state := extern_state';
  extern_empty := (PathMap.empty, PathMap.empty);
  alloc_extern := (fun s class type_params p args =>
                    (PathMap.set p (ses_alloc_extern class type_params args) (fst s), snd s));
  exec_extern := exec_extern';
  extern_get_entries := extern_get_entries';
  extern_match := ses_extern_match
|}.
End ExternSemOfSeparableExternSem.

Coercion ExternSemOfSeparableExternSem : SeparableExternSem >-> ExternSem.

Class Target := {
  extern_sem :> ExternSem;
  exec_prog : (path -> extern_state -> list Val -> extern_state -> list Val -> signal-> Prop) ->
      extern_state -> list bool -> extern_state -> list bool -> Prop
}.

End Target.
