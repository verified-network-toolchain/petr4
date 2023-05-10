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

Definition freshen (env: t) (x: string) : string * t :=
  let x' := fresh_string x env in
  (x', <[x':=()]>env).
