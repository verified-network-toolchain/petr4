Require Import Monads.Monad.

Open Scope monad.

Definition option_ret (A: Type) (a: A) := Some a.

Definition option_bind (A B: Type) (c: option A) (f: A -> option B) : option B :=
  match c with
  | Some a => f a
  | None => None
  end.

Global Instance option_monad_inst : Monad option :=
  { mret := option_ret;
    mbind := option_bind;
  }.
