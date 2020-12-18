Require Import Monads.Monad.

Open Scope monad.


Definition state_monad {State Exception Result: Type} :=
  State -> (Result + Exception) * State.

Definition state_return {State Exception Result: Type} (res: Result) : @state_monad State Exception Result :=
  fun env => (inl res, env).
  
Definition state_fail {State Exception Result: Type} (exc: Exception) : @state_monad State Exception Result :=
  fun env => (inr exc, env).

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
