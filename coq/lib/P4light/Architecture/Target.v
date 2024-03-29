Require Import Strings.String.
Require Import Coq.Bool.Bool.
Require Import Coq.ZArith.BinInt.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Program.Program.
Require Import Poulet4.P4light.Syntax.Syntax.
Require Import Poulet4.P4light.Syntax.Value.
From Poulet4.P4light.Syntax Require Import Typed SyntaxUtil P4Int.
From Poulet4.Utils Require Import Maps AList.

Module Exn.
  Import ListNotations.
  Open Scope string_scope.
  Inductive t :=
  | GlobalVarsNotInState (var : list string)
  | LocNotFoundInState (var : Locator) (msg: string)
  | TypeNameNotFound (type_name: string)
  | NameNotFoundInIEnv (name: string)
  | NameNotFoundInClassEnv (name: string)
  | Other (msg: string)
  .

  (* [path_to_string p] produces a human-readable string for p. *)
  Fixpoint path_to_string (path : list string) :=
    match path with
    | []     => "<empty path>"
    | [n]    => n
    | n :: p => n ++ "." ++ path_to_string p
    end.

  (* [loc_to_string e] is a human-readable string for loc *)
  Definition loc_to_string (loc: Locator) :=
    match loc with
    | LGlobal path   => "<global: " ++ path_to_string path ++ ">"
    | LInstance path => "<instance: " ++ path_to_string path ++ ">"
    end.
  
  (* [to_string e] is a sentence describing the error e *)
  Definition to_string e :=
    match e with
    | GlobalVarsNotInState p =>
        "Tried to find the "
          ++ "global variable "
          ++ loc_to_string (LGlobal p)
          ++ " in a Semantics.state. "
          ++ "Global variables are stored in the genv."
    | LocNotFoundInState l msg =>
        "Couldn't find " ++ loc_to_string l ++ " in a Semantics.state. " ++ msg
    | TypeNameNotFound t =>
        "Couldn't find the type name " ++ t ++ " in a genv_typ."
    | NameNotFoundInIEnv name =>
        "Couldn't find the name " ++ name ++ " in an ienv (instantiation env)."
    | NameNotFoundInClassEnv name =>
        "Couldn't find the name " ++ name ++ " in a cenv (class env)."
    | Other s =>
        s ++ " (You may want to break this error out into its "
          ++ "own variant in Semantics.Exn.t instead of using Exn.Other)"
    end.
End Exn.

Section Target.

Context {tags_t: Type}.
Notation ident := string.
Notation path := (list ident).
Notation Val := (@ValueBase bool).

Fixpoint width_of_val (v: Val): N :=
  let fix fields_width (fields: StringAList ValueBase) : N :=
      match fields with
      | nil => N.of_nat O
      | (id, v) :: rest => (width_of_val v + fields_width rest)%N
      end in
  match v with
  | ValBaseNull => N.of_nat O
  | ValBaseBool _ => 1
  | ValBaseBit bits
  | ValBaseInt bits
  | ValBaseVarbit _ bits => Z.to_N (Zlength bits)
  | ValBaseTuple vs => List.fold_right N.add (0)%N (List.map width_of_val vs)
  | ValBaseStruct fields
  | ValBaseHeader fields _ => fields_width fields
  | ValBaseSenumField _ v => width_of_val v
  | _ => N.of_nat O
  end.

(* We want to share the notation of External between P4light and P4cub, so later we need to
  have a parameter `ActionRef`, while `Match` is just shared. *)
(* Because the entries can refer to constructor parameters, we need to refer the arguments as expressions. *)
(* Maybe we can just use the definition in Syntax.v. *)

Context {Expression : Type}.

Inductive action_ref :=
  mk_action_ref (action : ident) (args : list (option Expression)).

Inductive table_entry :=
  mk_table_entry (matches : list ValueSet) (action : action_ref).

Definition table_entry_valset : Type :=  ValueSet * action_ref.

Class ExternSem := {
  extern_env_object : Type;
  extern_env := PathMap.t extern_env_object;
  extern_object : Type;
  extern_state := PathMap.t extern_object;
  AbsMet := extern_state -> list Val -> extern_state -> list Val -> signal -> Prop;
  (* Allocation should be a function; calling may be fine as a relation. *)
  construct_extern : extern_env -> extern_state -> ident (* class *) -> list (@P4Type tags_t) -> path
      -> list (path + Val) -> (extern_env * extern_state);
  extern_set_abstract_method : extern_env -> path -> AbsMet -> extern_env;
  exec_extern : extern_env -> extern_state -> ident (* class *) -> ident (* method *) -> path
      -> list (@P4Type tags_t) -> list Val -> extern_state -> list Val -> signal -> Prop;
  (* runnable version of exec_extern *)
  interp_extern : extern_env -> extern_state -> ident (* class *) -> ident (* method *) -> path
      -> list (@P4Type tags_t) -> list Val -> Result.result Exn.t (extern_state * list Val * signal);
  interp_extern_safe :
    forall env st class method this targs args st' retvs sig,
      interp_extern env st class method this targs args = Result.Ok (st', retvs, sig) ->
      exec_extern env st class method this targs args st' retvs sig;
  extern_get_entries : extern_state -> path -> list table_entry;
  extern_set_entries : extern_state -> path -> list table_entry -> extern_state;
  extern_match : list (Val * ident (* match_kind *)) -> list table_entry_valset -> option action_ref (* action *)
}.

Class SeparableExternSem := {
  ses_extern_object : Type;
  (* extern_state := @IdentMap.t tags_t extern_object; *)
  (* extern_empty : extern_state := IdentMap.empty; *)
  (* Allocation should be a function; calling may be fine as a relation. *)
  ses_alloc_extern : ident (* class *) -> list (@P4Type tags_t) -> list Val -> ses_extern_object;
  ses_exec_extern : ident (* class *) -> ident (* method *) -> ses_extern_object -> list (@P4Type tags_t) -> list Val -> ses_extern_object -> list Val -> signal -> Prop;
  (* ses_extern_get_entries : extern_state -> path -> list table_entry; *)
  ses_extern_match : list (Val * ident (* match_kind *)) -> list table_entry_valset -> option action_ref (* action *)
}.

(* Section ExternSemOfSeparableExternSem.
Context (ses : SeparableExternSem).

(* Definition extern_state' : Type := @PathMap.t tags_t ses_extern_object * @PathMap.t tags_t (list table_entry).

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
  extern_object := ses_extern_object;
  extern_empty := (PathMap.empty, PathMap.empty);
  alloc_extern := (fun s class type_params p args =>
                    (PathMap.set p (ses_alloc_extern class type_params args) (fst s), snd s));
  exec_extern := exec_extern';
  extern_get_entries := extern_get_entries';
  extern_match := ses_extern_match
|}. *)
End ExternSemOfSeparableExternSem. *)

(* Coercion ExternSemOfSeparableExternSem : SeparableExternSem >-> ExternSem. *)

Class Target := {
  extern_sem :> ExternSem;
    target_main_name: string;
    exec_prog : list (@P4Type tags_t) ->
                (path -> extern_state -> list Val -> extern_state -> list Val -> signal -> Prop) ->
                extern_state ->
                list bool ->
                extern_state ->
                list bool ->
                Prop;
    interp_prog : list (@P4Type tags_t) ->
                  (path -> extern_state -> list Val -> Result.result Exn.t (extern_state * list Val * signal)) ->
      extern_state -> Z -> list bool -> Result.result Exn.t (extern_state * Z * list bool);
}.

End Target.
