Require Import Poulet4.Monads.Monad.
Require Import Poulet4.Monads.State.
Require Import Poulet4.Monads.Option.

(* TODO: it seems like exc could be implicit but in practice, it needs to be manually instantiated *)
Definition lift_opt {Result State Exception : Type} (exc : Exception) (x: option_monad) : @state_monad State Exception Result :=
  fun env =>
    match x with
    | Some t => (inl t, env)
    | None => (inr exc, env)
    end.
