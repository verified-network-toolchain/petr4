From stdpp Require Import
     base
     strings
     infinite.

Definition t : Type := list string.

Definition init : t := [].

Definition freshen (env: t) (x: string) : string * t :=
  let x' := fresh env in
  (x', x' :: env).
