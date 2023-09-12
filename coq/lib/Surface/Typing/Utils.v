From Coq Require Import Lists.List
     NArith.NArith
     Strings.String
     ZArith.ZArith.

(* From Coq Require Import Numbers.BinNums Classes.EquivDec. *)
From Poulet4 Require Import Utils.AList
     Monads.Option
     Utils.AListUtil
     (* Monads.Result *)
     Surface.Syntax.Syntax
     Surface.Typing.CheckerEnv
     P4light.Syntax.Info
     P4light.Syntax.P4Int
     P4light.Semantics.Semantics.

From Poulet4.P4light.Syntax Require P4String.

Import Result ResultNotations.
(*initially have none for types when you parse from p4 to surface ir. *)

Section Utils.

  (* Context {tags_t: Type}. *)
  Notation P4String := (P4String.t Info).
  Notation P4Int := (P4Int.t Info).
  Notation Val := (@ValueBase bool).

  (*dummy function definition for now. TODO: fill in.*)
  Definition compile_time_eval (env: checkerEnvs) (exp: expression) : option Val :=
    match exp with
    | _ => Some ValBaseNull
    end.

  Definition compile_time_known (env: checkerEnvs) (exp: expression) : bool :=
    match compile_time_eval env exp with
    | Some _ => true
    | _      => false
    end.


  Definition is_numeric (env: checkerEnvs) (exp: expression) (type: typ) : bool :=
    match type with
    | TypInt _ _   => true
    | TypBit _ _   => true
    | TypInteger _ => compile_time_known env exp
    | _            => false
    end.

  Definition is_bool (type: typ) : bool :=
    match type with
    | TypBool _ => true
    | _         => false
    end.

  Definition is_fixed_width_int (type: typ) : bool :=
    match type with
    | TypInt _ _ => true
    | TypBit _ _ => true
    | _          => false
    end.

  Definition is_integer (type: typ) : bool :=
    match type with
    | TypInteger _ => true
    | _            => false
    end.

  Definition is_type_error (type: typ) : bool :=
    match type with
    | TypError _ => true
    | _          => false
    end.

  (*dummy function definition. fill in later. TODO.*)
  (*the nitty gritty converting between types.*)
  (* Definition to_nat (val: Val) : nat := 0. *)

  (*dummy function definition. fill in later. TODO.*)
  (*pairs of types that allow explicit cast return true. otherwise it returns false.*)
  (*@parisa, finalize this for the p4 spec pr of casting.*)
  Definition explicit_cast (env:checkerEnvs) (typ1 typ2: typ) : bool :=
    false.

  (*dummy function definition. fill in later. TODO.*)
  (*looks up type variable type in environment env and return its type if it finds it.
    otherwise, it returns error.*)
  Definition lookup_type (type: P4String) (env: checkerEnvs) : result Exn.t typ :=
    error (Exn.Other "fill out later.").

  (*dummy function definition. fill in later. TODO.*)
  (*looks up variable var in environment env and if it finds it, it returns the pair (typ, dir), otherwise returns an error.*)
  Definition lookup_var (var: P4String) (env: checkerEnvs) : result Exn.t (typ * direction) :=
    error (Exn.Other "fill out later.").

  (*dummy function definition. fill in later. TODO.*)
  (*returns: error.mem *)
  Definition append_error (mem: P4String) : P4String :=
    mem.

  (*dummy function definition. fill in later. TODO.*)
  (*returns: typ.mem *)
  Definition append_type (typ: P4String) (mem: P4String) : P4String :=
    mem.

End Utils.

