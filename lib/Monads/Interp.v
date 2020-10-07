Require Import Monads.Monad.
Require Import Environment.

Open Scope monad.


Definition interp_monad (Carry Result Exception: Type) :=
  Carry -> (Result + Exception) * Carry.

Definition interp_return (A B E: Type) (b: B) : interp_monad A B E :=
  fun env => (b, env).Scheme new_scheme := Induction for _ Sort _
with _ := Induction for _ Sort _.


Definition interp_bind (A B C: Type) (c: interp_monad A C) (f: A -> interp_monad B C) : interp_monad B C :=
  fun env =>
    let (res, env') := c env in
    match res with
    | inl a => f a env'
    | inr exn => (inr exn, env')
    end.

Global Instance interp_monad_inst : Monad interp_monad :=
  { mret := interp_return;
    mbind := interp_bind
  }.