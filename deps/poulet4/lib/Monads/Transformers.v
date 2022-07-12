Require Export Poulet4.Monads.Monad Poulet4.Monads.ExceptionState.

(* TODO: it seems like exc could be implicit but in practice, it needs to be manually instantiated *)
Definition lift_opt {Result State Exception : Type} (exc : Exception) (x: option Result) : @state_monad State Exception Result :=
  fun env =>
    match x with
    | Some t => (inl t, env)
    | None => (inr exc, env)
    end.
