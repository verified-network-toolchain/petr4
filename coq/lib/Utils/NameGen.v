From stdpp Require Import
     gmap
     stringmap.

Module NameGenParam.
  Section NameGenParam.
    Context {A: Type}.
    Definition t : Type := stringmap A.

    Definition init : t := empty.

    Definition observe (env: t) (x: string) (a: A) : option t :=
      match env !! x with
      | Some _ => None
      | None => Some (<[x:=a]>env)
      end.

    (* Like observe but allows duplicates *)
    Definition observe_dup (env: t) (x: string) (a: A) : option t :=
      Some (<[x:=a]>env).

    Fixpoint observe_all (env: t) (xs: list (string * A)) : option t :=
      match xs with
      | [] => mret env
      | (x, a) :: xs =>
          env ← observe env x a;
          observe_all env xs
      end.

    Definition freshen (env: t) (x: string) (a: A) : string * t :=
      let x' := fresh_string x env in
      (x', <[x':=a]>env).

  End NameGenParam.
  Arguments t : clear implicits.
End NameGenParam.

Definition t : Type := NameGenParam.t unit.

Definition init : t := NameGenParam.init.

  Definition observe (env: t) (x: string) : option t :=
    NameGenParam.observe env x ().

  (* Like observe but allows duplicates *)
  Definition observe_dup (env: t) (x: string) : option t :=
    NameGenParam.observe_dup env x ().

  Definition observe_all (env: t) (xs: list string) : option t :=
    NameGenParam.observe_all env (List.map (fun x => (x, ())) xs).

  Definition freshen (env: t) (x: string) : string * t :=
    NameGenParam.freshen env x ().
