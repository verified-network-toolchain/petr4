Require Import String List.
Require Export Poulet4.Monads.Monad.

Inductive result (Err A : Type) : Type :=
| Ok  : A -> result Err A
| Error : Err -> result Err A.
Arguments Ok {Err A}.
Arguments Error {Err A}.

Definition ok {Err A : Type} (x : A) : result Err A := Ok x.
Definition error {Err A : Type} (err : Err) : result Err A := Error err.

Definition is_ok {Err A : Type} (x : result Err A) : Prop :=
  match x with
  | Ok x => True
  | _ => False
  end.

Definition is_error {Err A: Type} (x : result Err A) : Prop :=
  match x with
  | Error x => True
  | _ => False
  end.

Definition bind {Err A B : Type} (r : result Err A)  (f : A -> result Err B) : result Err B :=
  match r with
  | Error err => Error err
  | Ok x => f x
  end.

Global Instance result_monad_inst (Err: Type) : Monad (result Err) :=
  { mret := fun _ v => ok v;
    mbind := fun _ _ c1 c2 => bind c1 c2 }.

Definition opt_bind {Err A B : Type} (r : option A) (err : Err) (f : A -> result Err B) : result Err B :=
  match r with
  | None => error err
  | Some x => f x
  end.

Definition from_opt {Err A} (r : option A) (err : Err) :=
  match r with
  | None => error err
  | Some a => ok a
  end.

Definition map {Err A B : Type} (f : A -> B)  (r : result Err A) : result Err B :=
  match r with
  | Error err => error err
  | Ok x => ok (f x)
  end.

Definition overwritebind {Err A B : Type} (r : result Err A) (err : Err) (f : A -> result Err B) : result Err B :=
  match r with
  | Error err => error err (* ++ " because: \n" ++ s)*)
  | Ok x  => f x
  end.

Definition rbindcomp {Err A B C : Type} (f : B -> C) (g : A -> result Err B) (a : A) : result Err C :=
  map f (g a).

Definition rcomp {Err A B C : Type} (f : B -> result Err C) (g : A -> result Err B) (a : A) : result Err C :=
  bind (g a) f.

Fixpoint rred_aux {Err A : Type} (os : list (result Err A)) (acc : result Err (list A)) : result Err (list A) :=
  match acc with
  | Error err => error err
  | Ok acc =>
    match os with
    | Error err :: _ => error err
    | Ok x :: os =>
      rred_aux os (ok (x :: acc))
    | _ => ok acc
    end
  end.

Definition rred {Err A : Type} (os : list (result Err A)) : result Err (list A) :=
  match rred_aux os (ok nil) with
  | Error err => error err
  | Ok xs => ok (List.rev' xs)
  end.

Definition res_snd {Err A B : Type} (p : A * result Err B) : result Err (A * B) :=
  match p with
  | (_, Error err) => error err
  | (a, Ok b) => ok (a, b)
  end.

Definition
  snd_res_map {Err A B C : Type}
  (f : B -> result Err C) '((x,y) : A * B) : result Err (A * C) :=
  map (pair x) (f y).

Module ResultNotations.
  Notation "'let+' p ':=' c1 'in' c2" := (map (fun p => c2) c1)
                                            (at level 61, p as pattern, c1 at next level, right associativity).

  Notation "'let*~' p ':=' c1 'else' str 'in' c2 " := (opt_bind c1 str (fun p => c2))
                                                        (at level 61, p as pattern, c1 at next level, right associativity).

  Notation "'let~' p ':=' c1 'over' str 'in' c2" := (overwritebind c1 str (fun p => c2))
                                                      (at level 61, p as pattern, c1 at next level, right associativity).

  Infix ">>=>" := rbindcomp (at level 80, right associativity).

  Infix ">=>" := rcomp (at level 80, right associativity).

  Infix "|=>" := map (at level 80, right associativity).

End ResultNotations.

Definition cons_res {Err A : Type} (hd_res : result Err A) (rlist : result Err (list A)) : result Err (list A) :=
  let* l := rlist in
  map (fun p => p :: l) hd_res.

Fixpoint commute_result_optlist {A : Type} (l : list (option (result string A))) : result string (list (option A)) :=
  match l with
  | nil => ok nil
  | o :: l =>
      let* l := commute_result_optlist l in
      match o with
      | None =>
          ok (None :: l)
      | Some a_res =>
          map (fun p => Some p :: l) a_res
      end
  end.
