From Equations Require Import Equations.
Require Import Poulet4.Utils.VecUtil Poulet4.Utils.Util.FunUtil.
Import Vec.VectorNotations.

Section prod.
  Polymorphic Universes a b.
  Variables (A : Type@{a}) (B : Type@{b}).
  Polymorphic Variant prod : Type@{max(a,b)} := pair : A -> B -> prod.

  Polymorphic Definition fst '(pair a _ : prod) : A := a.
  Polymorphic Definition snd '(pair _ b : prod) : B := b.
End prod.

Arguments pair {A} {B}.
Arguments fst {A} {B}.
Arguments snd {A} {B}.

Set Warnings "-notation-overridden".
Notation "x * y" := (prod x y) : type_scope.
Notation "( x , y , .. , z )" := (pair .. (pair x y) .. z) : core_scope.

Section ProdN.
  Polymorphic Universe a.
  
  Polymorphic Inductive t : forall {n : nat}, Vec.t Type@{a} n -> Type@{a+1} :=
  | nil : t []%vector
  | cons : forall {A : Type@{a}} {n : nat} {v : Vec.t Type@{a} n},
      A -> t v -> t (A :: v)%vector.

  Polymorphic Derive Signature NoConfusion NoConfusionHom for t.
End ProdN.

Module ProdNNotations.
  Declare Scope prodn_scope.
  Delimit Scope prodn_scope with prodn.
  Notation "[ ]" := nil (format "[ ]") : prodn_scope.
  Notation "h :: t" := (cons h t) (at level 60, right associativity)
      : prodn_scope.
  Notation "[ x ]" := (x :: []) : prodn_scope.
  Notation "[ x ; y ; .. ; z ]"
    := (cons _ x _ (cons _ y _ .. (cons _ z _ (nil _)) ..)) : prodn_scope.
  (*Notation "v [@ p ]" := (nth v p) (at level 1, format "v [@ p ]") : prodn_scope.
  Infix "++" := append : prodn_scope.*)
End ProdNNotations.


Section ProdN.
  Import ProdNNotations.
  Open Scope prodn_scope.

  Polymorphic Universe a.
  
  Polymorphic Equations append : forall {m n : nat} {v1 : Vec.t Type@{a} m} {v2 : Vec.t Type@{a} n},
      t v1 -> t v2 -> t (v1 ++ v2)%vector := {
      append [] p2 := p2;
      append (a :: p1) p2 := a :: append p1 p2
    }.

  Polymorphic Equations nth : forall {n : nat} {v : Vec.t Type@{a} n} (i : Fin.t n),
      t v -> (v [@ i])%vector := {
      nth Fin.F1 (a :: _) := a;
      nth (Fin.FS i) (_ :: p) := nth i p
    }.

  Section fixed.
    Context {A : Type@{a}}.

    Polymorphic Equations hd : forall {n : nat} {v : Vec.t Type@{a} n},
        t (A :: v)%vector -> A := {
        hd (a :: _) := a
      }.

    Polymorphic Equations tl : forall {n : nat} {v : Vec.t Type@{a} n},
        t (A :: v)%vector -> t v := {
        tl (_ :: p) := p
      }.

    Polymorphic Equations rep : forall (n : nat) (a : A), t (vec_rep n A) := {
        rep O a := [];
        rep (S n) a := a :: rep n a
      }.

    Polymorphic Equations to_vec : forall {n : nat}, t (vec_rep n A) -> Vec.t A n := {
      to_vec (n:=O) [] := []%vector;
        to_vec (a :: p) := (a :: to_vec p)%vector;
      }.
    
    Polymorphic Equations of_vec : forall {n : nat}, Vec.t A n -> t (vec_rep n A) := {
        of_vec []%vector := [];
        of_vec (a :: v)%vector := a :: of_vec v
      }.

    Polymorphic Definition to_list {n : nat} : t (vec_rep n A) -> list A :=
      Vec.to_list ∘ to_vec.

    Polymorphic Definition of_list (l : list A) : t (vec_rep (length l) A) :=
      of_vec $ Vec.of_list l.
  End fixed.

  Section Map.
    Polymorphic Universe b.
    
    Polymorphic Equations map : forall {n : nat} {dom : Vec.t Type@{a} n} {ran : Vec.t Type@{b} n},
      t (Vec.map2 (fun A B : Type@{a} => A -> B) dom ran) ->
      t dom -> t ran := {
      map (dom:=[]%vector) (ran:=[]%vector) [] [] := [];
        map (f :: fp) (a :: p) := f a :: map fp p
      }.
  End Map.

  Section MapPoly.
    (**Polymorphic Universe b.*)
    
    Variable f : forall {A : Type@{a}} {B : Type@{a}}, A -> B.

    Polymorphic Equations map_poly : forall {n : nat} {v : Vec.t Type@{a} n},
        t v -> t v := {
        map_poly [] := [];
        map_poly (a :: p) := f a :: map_poly p
      }.
  End MapPoly.

  Section Zip.
    Polymorphic Universe b.

    Polymorphic Equations zip :
      forall {n : nat} {v1 : Vec.t Type@{a} n} {v2 : Vec.t Type@{b} n},
        t v1 -> t v2 -> t (Vec.map2 prod v1 v2) := {
        zip [] [] := [];
        zip (a :: p1) (b :: p2) := (a, b) :: zip p1 p2
      }.

    Polymorphic Equations unzip :
      forall {n : nat} {v1 : Vec.t Type@{a} n} {v2 : Vec.t Type@{b} n},
        t (Vec.map2 prod v1 v2) -> t v1 * t v2 := {
        unzip (v1:=[]%vector) (v2:=[]%vector) [] := ([], []);
        unzip (v1:=(_ :: _)%vector) (v2:=(_ :: _)%vector)
          ((a, b) :: p) :=
          let '(p1, p2) := unzip p in (a :: p1, b :: p2)
      }.
  End Zip.
End ProdN.
