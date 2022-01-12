Require Import Poulet4.Monads.Monad String List.

Module Result.
  Inductive result (A : Type) : Type :=
  | Ok  : A -> result A
  | Error : string -> result A.

  Definition ok {A : Type} (x : A) : result A := Ok A x.
  Definition error {A : Type} (s : string) : result A := Error A s.

  Definition is_ok {A : Type} (x : result A) : Prop :=
    match x with
    | Ok _ x => True
    | _ => False
    end.

  Definition is_error {A : Type} (x : result A) : Prop :=
    match x with
    | Error _ x => True
    | _ => False
    end.

  Definition bind {A B : Type} (r : result A)  (f : A -> result B) : result B :=
    match r with
    | Error _ s => Error B s
    | Ok _ x => f x
    end.

  Instance result_monad_inst : Monad result:=
    {
    mret := @ok;
    mbind := @bind
    }.

  Definition opt_bind {A B : Type} (r : option A) (str : string) (f : A -> result B) : result B :=
    match r with
    | None => error str
    | Some x => f x
    end.

  Definition map {A B : Type} (f : A ->  B)  (r : result A) : result B :=
    match r with
    | Error _ s => error s
    | Ok _ x => ok (f x)
    end.


  Definition overwritebind {A B : Type} (r : result A) (str : string) (f : A -> result B) : result B :=
    match r with
    | Error _ _ => error str
    | Ok _ x  => f x
    end.

  Definition rbindcomp {A B C : Type} (f : B -> C) (g : A -> result B) (a : A) : result C :=
    map f (g a).

  Definition rcomp {A B C : Type} (f : B -> result C) (g : A -> result B) (a : A) : result C :=
    bind (g a) f.

  Fixpoint rred {A : Type} (os : list (result A)) : result (list A) :=
    match os with
    | (Error _ s :: _) => error s
    | ((Ok _ x) :: os) =>
      map (cons x) (rred os)
    | _ => ok nil
    end.

  Definition res_snd { A B : Type } (p : A * result B ) : result (A * B) :=
    match p with
    | (_, Error _ s) => error s
    | (a, Ok _ b) => ok (a, b)
    end.

  Definition
    snd_res_map {A B C : Type}
    (f : B -> result C) '((x,y) : A * B) : result (A * C) :=
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

End Result.
