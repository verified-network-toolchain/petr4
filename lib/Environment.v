Require Import String.
Require Import Coq.Lists.List.
Require Import Coq.FSets.FMapList.
Require Import Coq.Structures.OrderedTypeEx.
Require Import Value.

Require Import Monads.Monad.
Require Import Monads.Option.
Require Import Monads.State.

Open Scope string_scope.
Open Scope monad.

Module Import MStr := FMapList.Make(String_as_OT).

Inductive exception :=
| Reject
| Exit
| Internal.

Definition scope := MStr.t value.
Definition environment := list scope.

Definition env_monad := state_monad environment exception.
Definition env_fail {A: Type} := state_fail environment exception A.

Definition updateScope (key: string) (val: value) (bindings: scope) : option scope :=
  MStr.find key bindings;;
  mret (MStr.add key val (MStr.remove key bindings)).

Definition insertScope (key: string) (val: value) (bindings: scope) : option scope :=
  MStr.find key bindings;;
  mret (MStr.add key val bindings).

Fixpoint updateEnvironment (key: string) (val: value) (env: environment) : option environment :=
  match env with
  | inner :: rest =>
    if MStr.find key inner
    then let* inner' := updateScope key val inner in
         mret (inner' :: rest)
    else let* rest' := updateEnvironment key val rest in
         mret (inner :: rest')
  | nil => None
  end.

Definition insertEnvironment (key: string) (val: value) (env: environment) : option environment :=
  match env with
  | inner :: rest =>
    let* inner' := insertScope key val inner in
    mret (inner' :: rest)
  | nil => None
  end.

Definition findScope (key: string) (bindings: scope) : option value :=
  MStr.find key bindings.
  
Fixpoint findEnvironment (key: string) (env: environment) : option value :=
  match env with
  | inner :: rest =>
    match MStr.find key inner with
    | Some v => Some v
    | None => findEnvironment key rest
    end
  | nil => None
  end.

Definition pushScope (env: environment) :=
  MStr.empty _ :: env.

Definition popScope (env: environment) : option environment :=
  match env with
  | _ :: rest => Some rest
  | nil => None
  end.

Fixpoint findLvalue (lval: lvalue) (env: environment) : option value :=
  match lval with
  | LValName var =>
    findEnvironment var env
  | LValMember lval' member =>
    let* val := findLvalue lval' env in
    match val with
    | ValRecord map =>
      Raw.find member map
    | _ => None
    end
  end.

Fixpoint assocUpdate {A: Type} (key: string) (val: A) (map: list (string * A)) : option (list (string * A)) :=
  match map with
  | (s, v) :: map' =>
    if String_as_OT.eq_dec s key
    then mret ((key, val) :: map')
    else let* map' := assocUpdate key val map' in
         mret ((s, v) :: map')
  | nil => None
  end.

Definition updateMember (obj: value) (member: string) (val: value) : option value :=
  match obj with
  | ValRecord map =>
    let* map' := assocUpdate member val map in
    mret (ValRecord map')
  | _ => None
  end.

Fixpoint updateLvalue (lval: lvalue) (val: value) (env: environment) : option environment :=
  match lval with
  | LValName var =>
    updateEnvironment var val env
  | LValMember lval' member =>
    let* obj := findLvalue lval' env in
    let* obj' := updateMember obj member val in
    updateLvalue lval' obj' env
  end.

Definition liftEnvFn (f : environment -> option environment) : env_monad unit :=
  fun env =>
    match f env with
    | Some env' => mret tt env'
    | None => env_fail Internal env
    end.

Definition liftEnvLookupFn (f: environment -> option value) : env_monad value :=
  fun env =>
    match f env with
    | Some res => mret res env
    | None => env_fail Internal env
    end.

Definition tossValue (original: env_monad value) : env_monad unit :=
  fun env =>
    match original env with
    | (inl result, env') => mret tt env'
    | (inr exc, env') => env_fail exc env'
    end.

Definition dummyValue (original: env_monad unit) : env_monad value :=
  fun env =>
    match original env with
    | (inl tt, env') => mret ValVoid env'
    | (inr exc, env') => env_fail exc env'
    end.

Definition lift_option (x: option value) : env_monad value := fun env => 
  match x with
  | Some it => mret it env
  | None => (inr Internal, env)
  end.
