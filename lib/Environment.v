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
| Reject
| Exit
| Internal.

Definition scope := MStr.t value.
Definition environment := list scope.

Definition env_monad := @state_monad environment exception.

Definition mapEnv (f : environment -> environment) : env_monad unit :=
  fun env => mret tt (f env).

Definition liftEnvFn (f : environment -> option environment) : env_monad unit :=
  fun env =>
    match f env with
    | Some env' => mret tt env'
    | None => state_fail Internal env
    end.

Definition liftEnvLookupFn (f: environment -> option value) : env_monad value :=
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

Definition updateScope (key: string) (val: value) (bindings: scope) : option scope :=
  MStr.find key bindings;;
  mret (MStr.add key val (MStr.remove key bindings)).

Definition insertScope (key: string) (val: value) (bindings: scope) : option scope :=
  MStr.find key bindings;;
  mret (MStr.add key val bindings).

Definition findScope (key: string) (bindings: scope) : option value :=
  MStr.find key bindings.

Definition pushScope (env: environment) :=
  MStr.empty _ :: env.

Definition popScope (env: environment) : option environment :=
  match env with
  | _ :: rest => Some rest
  | nil => None
  end.

Fixpoint updateEnvironment' (key: string) (val: value) (env: environment) : option environment :=
  match env with
  | inner :: rest =>
    if MStr.find key inner
    then let* inner' := updateScope key val inner in
         mret (inner' :: rest)
    else let* rest' := updateEnvironment' key val rest in
         mret (inner :: rest')
  | nil => None
  end.

Definition updateEnvironment (key: string) (val: value) : env_monad unit :=
  liftEnvFn (updateEnvironment' key val).

Definition insertEnvironment' (key: string) (val: value) (env: environment) : option environment :=
  match env with
  | inner :: rest =>
    let* inner' := insertScope key val inner in
    mret (inner' :: rest)
  | nil => None
  end.

Definition insertEnvironment (key: string) (val: value) : env_monad unit :=
  liftEnvFn (insertEnvironment' key val).
  
Fixpoint findEnvironment' (key: string) (env: environment) : option value :=
  match env with
  | inner :: rest =>
    match MStr.find key inner with
    | Some v => Some v
    | None => findEnvironment' key rest
    end
  | nil => None
  end.

Definition findEnvironment (key: string) : env_monad value :=
  liftEnvLookupFn (findEnvironment' key).

Fixpoint findLvalue' (lval: lvalue) (env: environment) : option value :=
  match lval with
  | LValName var =>
    findEnvironment' var env
  | LValMember lval' member =>
    let* val := findLvalue' lval' env in
    match val with
    | ValRecord map =>
      Raw.find member map
    | _ => None
    end
  end.

Definition findLvalue (lval: lvalue) : env_monad value :=
  liftEnvLookupFn (findLvalue' lval).

Fixpoint updateLvalue' (lval: lvalue) (val: value) (env: environment) : option environment :=
  match lval with
  | LValName var =>
    updateEnvironment' var val env
  | LValMember lval' member =>
    let* obj := findLvalue' lval' env in
    let* obj' := updateMember obj member val in
    updateLvalue' lval' obj' env
  end.

Definition updateLvalue (lval: lvalue) (val: value) : env_monad unit :=
  liftEnvFn (updateLvalue' lval val).

Definition tossValue (original: env_monad value) : env_monad unit :=
  fun env =>
    match original env with
    | (inl result, env') => mret tt env'
    | (inr exc, env') => state_fail exc env'
    end.

Definition dummyValue (original: env_monad unit) : env_monad value :=
  fun env =>
    match original env with
    | (inl tt, env') => mret ValVoid env'
    | (inr exc, env') => state_fail exc env'
    end.
