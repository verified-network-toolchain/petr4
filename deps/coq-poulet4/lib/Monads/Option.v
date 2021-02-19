Require Import Monads.Monad.

Open Scope monad.
Open Scope list_scope.


Definition option_monad {Result: Type} :=
  option Result.

Definition option_ret (A: Type) (a: A) : option_monad := Some a.

Definition option_bind (A B: Type) (c: @option_monad A) (f: A -> @option_monad B) : option_monad :=
  match c with
  | Some a => f a
  | None => None
  end.

Global Instance option_monad_inst : Monad option :=
  { mret := option_ret;
    mbind := option_bind;
  }.

Definition option_fail {A : Type} : @option_monad A := None.

Fixpoint reduce_option {A : Type} (acts: list (option A)) (f : A -> A -> A) (base: A) : option A :=
  match acts with 
  | nil => Some base
  | None :: _ => None
  | Some x :: xs => reduce_option xs f (f x base)
  end.

Hint Unfold option_ret option_bind : core.