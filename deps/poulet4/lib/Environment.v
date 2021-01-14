Require Import Coq.Lists.List.
Require Import Coq.FSets.FMapList.
Require Import Coq.Structures.OrderedTypeEx.

Require Import Monads.Monad.
Require Import Monads.Option.
Require Import Monads.State.

Require String.
Require Import Syntax.

Open Scope monad.

Module Import MNat := FMapList.Make(Nat_as_OT).
Module Import MStr := FMapList.Make(String.StringOT).

Inductive exception :=
| PacketTooShort
| Reject
| Exit
| Internal
| AssertError (error_msg: String.t).

Section Environment.

  Context (tags_t: Type).
  Context (tags_dummy: tags_t).

  Definition loc := nat.
  Definition scope := MStr.t loc.
  Definition stack := list scope.
  Definition heap := MNat.t (@Value tags_t).

  Record environment := MkEnvironment {
    env_fresh: loc;
    env_stack: stack;
    env_heap: heap;
  }.

  Definition env_monad := @state_monad environment exception.

  Definition lift_option {A : Type} (x: option A) : env_monad A :=
    fun env => 
      match x with
      | Some it => mret it env
      | None => (inr Internal, env)
      end.

  Fixpoint stack_lookup' (key: String.t) (st: stack) : option loc :=
    match st with
    | nil => None
    | top :: rest =>
      match MStr.find key top with
      | None => stack_lookup' key rest
      | Some l => Some l
      end
    end.

  Definition stack_lookup (key: String.t) : env_monad loc :=
    fun env =>
      match stack_lookup' key (env_stack env) with
      | None => state_fail Internal env
      | Some l => mret l env
      end.

  Definition stack_insert' (key: String.t) (l: loc) (st: stack) : option stack :=
    match st with
    | nil => None
    | top :: rest =>
      match MStr.find key top with
      | None => Some ((MStr.add key l top) :: rest)
      | Some _ => None
      end
    end.

  Definition stack_insert (key: String.t) (l: loc) : env_monad unit :=
    fun env =>
      match stack_insert' key l (env_stack env) with
      | None => state_fail Internal env
      | Some st => mret tt {|
          env_fresh := env_fresh env;
          env_stack := st;
          env_heap := env_heap env;
        |}
      end.

  Definition stack_push : env_monad unit :=
    fun env => mret tt {|
      env_fresh := env_fresh env;
      env_stack := MStr.empty _ :: (env_stack env);
      env_heap := env_heap env;
    |}.

  Definition stack_pop : env_monad unit :=
    fun env =>
      match env_stack env with
      | nil => state_fail Internal env
      | _ :: rest => mret tt {|
          env_fresh := env_fresh env;
          env_stack := rest;
          env_heap := env_heap env;
        |}
      end.

  (* TODO handle name resolution properly *)
  Definition str_of_name_warning_not_safe (t: @Typed.name tags_t) : String.t :=
    match t with 
    | Typed.BareName s
    | Typed.QualifiedName _ s => s.(P4String.str)
    end.

  Definition heap_lookup (l: loc) : env_monad (@Value tags_t) :=
    fun env =>
      match MNat.find l (env_heap env) with
      | None => state_fail Internal env
      | Some val => mret val env
      end.

  Definition heap_update (l: loc) (v: @Value tags_t) : env_monad unit :=
    fun env => mret tt {|
      env_fresh := env_fresh env;
      env_stack := env_stack env;
      env_heap := MNat.add l v (env_heap env);
    |}.

  Definition heap_insert (v: @Value tags_t) : env_monad loc :=
    fun env =>
      let l := env_fresh env in
      mret l {|
        env_fresh := S l;
        env_stack := env_stack env;
        env_heap := MNat.add l v (env_heap env);
      |}.

  Definition env_insert (name: String.t) (v: @Value tags_t) : env_monad unit :=
    let* l := heap_insert v in
    stack_insert name l.

  Definition env_lookup (lvalue: @ValueLvalue tags_t) : env_monad (@Value tags_t).
  Admitted.

  Definition env_update (lvalue: @ValueLvalue tags_t) (value: @Value tags_t) : env_monad unit.
  Admitted.

  Definition toss_value (original: env_monad (@Value tags_t)) : env_monad unit :=
    fun env =>
      match original env with
      | (inl result, env') => mret tt env'
      | (inr exc, env') => state_fail exc env'
      end.

  Definition dummy_value (original: env_monad unit) : env_monad (@Value tags_t) :=
    fun env =>
      match original env with
      | (inl tt, env') => mret (ValBase ValBaseNull) env'
      | (inr exc, env') => state_fail exc env'
      end.

End Environment.

