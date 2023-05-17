Require Export Poulet4.Monads.Monad.
Require Poulet4.Monads.Result.

Open Scope monad.

Definition state_monad State Exception Result: Type :=
  State -> (Result + Exception) * State.

Definition state_return {State Exception Result: Type} (res: Result) : state_monad State Exception Result :=
  fun env => (inl res, env).

Definition state_fail {State Exception Result: Type} (exc: Exception) : state_monad State Exception Result :=
  fun env => (inr exc, env).

Definition error {State Exception Result} := @state_fail State Exception Result.

Definition get_state {State Exception : Type} : state_monad State Exception State :=
  fun env => (inl env, env).

Definition put_state {State Exception : Type} (env: State) : state_monad State Exception unit :=
  fun _ => (inl tt, env).

Definition with_state {State Exception : Type} (f: State -> State) : state_monad State Exception unit :=
  fun env => (inl tt, f env).


Definition state_bind
  {State Exception Result Result': Type}
  (c: @state_monad State Exception Result)
  (f: Result -> @state_monad State Exception Result')
  : @state_monad State Exception Result' :=
  fun env =>
    let (ret, env') := c env in
    match ret with
    | inl result => f result env'
    | inr exc => (inr exc, env')
    end.

Global Instance state_monad_inst {State Exception: Type} : Monad (@state_monad State Exception) :=
  { mret := @state_return State Exception;
    mbind := @state_bind State Exception
  }.

Definition run_with_state
  {State Exception Result : Type}
  (st: State)
  (act: @state_monad State Exception Result)
  : (Result + Exception) * State := act st.

Definition skip {State Exception: Type}: @state_monad State Exception unit := state_return tt.

Definition from_opt {State Exception Result}
           (r : option Result) (exc : Exception)
  : state_monad State Exception Result :=
  match r with
  | None => error exc
  | Some res => mret res
  end.

Definition from_result {State Exception Result}
           (r : Result.result Exception Result)
  : state_monad State Exception Result :=
  match r with
  | Result.Error e => error e
  | Result.Ok res => mret res
  end.


Global Hint Unfold state_bind run_with_state state_fail state_return : core.
Global Hint Extern 3 => unfold state_bind : core.
