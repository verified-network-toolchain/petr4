Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.FSets.FMapList.
Require Import Coq.Structures.OrderedTypeEx.

Require Import Monads.Monad.
Require Import Monads.Option.
Require Import Monads.State.

Require Import Value.

Open Scope string_scope.
Open Scope monad.

Module Import MStr := FMapList.Make(String_as_OT).

Inductive exception :=
| PacketTooShort
| Reject
| Exit
| Internal.

Definition scope := MStr.t value.
Definition environment := list scope.

Definition env_monad := @state_monad environment exception.

Definition map_env (f : environment -> environment) : env_monad unit :=
  fun env => mret tt (f env).

Definition lift_env_fn (f : environment -> option environment) : env_monad unit :=
  fun env =>
    match f env with
    | Some env' => mret tt env'
    | None => state_fail Internal env
    end.

Definition lift_env_lookup_fn (f: environment -> option value) : env_monad value :=
  fun env =>
    match f env with
    | Some res => mret res env
    | None => state_fail Internal env
    end.

Definition lift_option {A : Type} (x: option A) : env_monad A := fun env => 
  match x with
  | Some it => mret it env
  | None => (inr Internal, env)
  end.

Definition update_scope (key: string) (val: value) (bindings: scope) : option scope :=
  MStr.find key bindings;;
  mret (MStr.add key val (MStr.remove key bindings)).

Definition insert_scope (key: string) (val: value) (bindings: scope) : option scope :=
  MStr.find key bindings;;
  mret (MStr.add key val bindings).

Definition find_scope (key: string) (bindings: scope) : option value :=
  MStr.find key bindings.

Definition push_scope (env: environment) :=
  MStr.empty _ :: env.

Definition pop_scope (env: environment) : option environment :=
  match env with
  | _ :: rest => Some rest
  | nil => None
  end.

Fixpoint update_environment' (key: string) (val: value) (env: environment) : option environment :=
  match env with
  | inner :: rest =>
    if MStr.find key inner
    then let* inner' := update_scope key val inner in
         mret (inner' :: rest)
    else let* rest' := update_environment' key val rest in
         mret (inner :: rest')
  | nil => None
  end.

Definition update_environment (key: string) (val: value) : env_monad unit :=
  lift_env_fn (update_environment' key val).

Definition insert_environment' (key: string) (val: value) (env: environment) : option environment :=
  match env with
  | inner :: rest =>
    let* inner' := insert_scope key val inner in
    mret (inner' :: rest)
  | nil => None
  end.

Definition insert_environment (key: string) (val: value) : env_monad unit :=
  lift_env_fn (insert_environment' key val).
  
Fixpoint find_environment' (key: string) (env: environment) : option value :=
  match env with
  | inner :: rest =>
    match MStr.find key inner with
    | Some v => Some v
    | None => find_environment' key rest
    end
  | nil => None
  end.

Definition find_environment (key: string) : env_monad value :=
  lift_env_lookup_fn (find_environment' key).

Fixpoint find_lvalue' (lval: lvalue) (env: environment) : option value :=
  match lval with
  | LValName var =>
    find_environment' var env
  | LValMember lval' member =>
    let* val := find_lvalue' lval' env in
    match val with
    | ValRecord map =>
      Raw.find member map
    | _ => None
    end
  end.

Definition find_lvalue (lval: lvalue) : env_monad value :=
  lift_env_lookup_fn (find_lvalue' lval).

Fixpoint update_lvalue' (lval: lvalue) (val: value) (env: environment) : option environment :=
  match lval with
  | LValName var =>
    update_environment' var val env
  | LValMember lval' member =>
    let* obj := find_lvalue' lval' env in
    let* obj' := update_member obj member val in
    update_lvalue' lval' obj' env
  end.

Definition update_lvalue (lval: lvalue) (val: value) : env_monad unit :=
  lift_env_fn (update_lvalue' lval val).

Definition toss_value (original: env_monad value) : env_monad unit :=
  fun env =>
    match original env with
    | (inl result, env') => mret tt env'
    | (inr exc, env') => state_fail exc env'
    end.

Definition dummy_value (original: env_monad unit) : env_monad value :=
  fun env =>
    match original env with
    | (inl tt, env') => mret ValVoid env'
    | (inr exc, env') => state_fail exc env'
    end.
