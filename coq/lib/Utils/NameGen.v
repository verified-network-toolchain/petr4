From stdpp Require Import
     gmap
     stringmap.

Definition t : Type := stringmap unit.

Definition init : t := empty.

Definition observe (env: t) (x: string) : option t :=
  match env !! x with
  | Some _ => None
  | None => Some (<[x:=()]>env)
  end.

(* Like observe but allows duplicates *)
Definition observe_dup (env: t) (x: string) : option t :=
  Some (<[x:=()]>env).

Fixpoint observe_all (env: t) (xs: list string) : option t :=
  match xs with
  | [] => mret env
  | x :: xs =>
     env ← observe env x;
     observe_all env xs
  end.

Definition freshen (env: t) (x: string) : string * t :=
  let x' := fresh_string x env in
  (x', <[x':=()]>env).
