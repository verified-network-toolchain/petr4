(** [default (Some v) _] is [v], and [default None d] is [d] *)
Definition default {A : Type} (d : A) (o : option A) : A :=
  match o with
  | Some v => v
  | None => d
  end.
