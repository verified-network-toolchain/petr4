Require Export Poulet4.P4cub.Syntax.Syntax.
Require Coq.Vectors.Vector.
Module Vec := Coq.Vectors.Vector.
Import Vec.VectorNotations.
From Equations Require Import Equations.
Import Coq.NArith.BinNat.

Module VecEq.
  Derive Signature NoConfusion NoConfusionHom for Vec.t.
End VecEq.
  
Module HetVec.
  
  
  Section Hetero.
    Polymorphic Universe a b.
    Polymorphic Context {A : Type@{a}}.
    Polymorphic Variable B : A -> Type@{b}.
    Polymorphic Inductive t : forall {n : nat}, Vec.t A n -> Type@{b} :=
    | nil : t []%vector
    | cons {n : nat} {a : A} {v : Vec.t A n} :
      B a -> t v -> t (a :: v)%vector.
    Polymorphic Derive Signature NoConfusion NoConfusionHom for t.
  End Hetero.

  Arguments nil {A}%type_scope {B}%type_scope.
  Arguments cons {A}%type_scope {B}%type_scope {n}%nat_scope {a} {v}.
  
  Module HetVecNotations.
    Declare Scope het_vec_scope.
    Delimit Scope het_vec_scope with het_vec.
    Notation "[ ]" := nil (format "[ ]") : het_vec_scope.
    Notation "h :: t" := (cons h t) (at level 60, right associativity)
        : het_vec_scope.
    Notation "[ x ]" := (x :: [])%het_vec : het_vec_scope.
    Notation "[ x ; y ; .. ; z ]"
      := (cons _ x _ (cons _ y _ .. (cons _ z _ (nil _)) ..)) : het_vec_scope.
  End HetVecNotations.
  
  Section Hetero.
    Import HetVecNotations.
    Local Open Scope het_vec_scope.

    Polymorphic Universe a b.
    Polymorphic Context {A : Type@{a}}.
    Polymorphic Variable B : A -> Type@{b}.
    
    Polymorphic Equations hd :
      forall {n : nat} {a : A} {v : Vec.t A n},
        t B (a :: v)%vector -> B a :=
      hd (b :: _) := b.

    Polymorphic Equations tl :
      forall {n : nat} {a : A} {v : Vec.t A n},
        t B (a :: v)%vector -> t B v :=
      tl (_ :: r) := r.

    Polymorphic Equations append :
      forall {m n : nat} {v1 : Vec.t A m} {v2 : Vec.t A n},
        t B v1 -> t B v2 -> t B (v1 ++ v2)%vector := {
        append [] hv := hv;
        append (b :: r) hv := b :: append r hv }.

    Polymorphic Equations nth :
      forall {n : nat} (fn : Fin.t n) {v : Vec.t A n},
        t B v -> B (Vec.nth v fn) := {
        nth Fin.F1 (b :: _) := b;
        nth (Fin.FS fn) (_ :: r) := nth fn r }.

    Section Inject.
      Variable (f : forall a : A, B a).
    
      Polymorphic Equations inject :
        forall (l : list A), t B (Vec.of_list l) := {
          inject []%list      => [];
          inject (a :: r)%list => f a :: inject r
        }.
    End Inject.

    Section Map.
      Polymorphic Universe c.
      Polymorphic Context
        {C : A -> Type@{c}}.
      Polymorphic Variable f : forall {a : A}, B a -> C a.

      Polymorphic Equations map
        : forall {n : nat} {v : Vec.t A n}, t B v -> t C v := {
          map [ ]     := [ ];
          map (b :: r) := f b :: map r }.
    End Map.
  End Hetero.
  
  Module NotationsFun.
    Notation "v [@ p ]" := (nth v p) (at level 1, format "v [@ p ]") : het_vec_scope.
    Infix "++" := append : het_vec_scope.
  End NotationsFun.
End HetVec.

Section Denote.
  Variable (σ : nat -> Set).

  Fail Fixpoint denote_typ (t : Typ.t) : Set :=
    match t with
    | Typ.Bool => bool
    | Typ.Bit w => Fin.t (N.to_nat w)
    | Typ.Int _ => Z
    | Typ.Error => String.string
    | Typ.VarBit _ => N
    | Typ.Var n => σ n
    | Typ.Array n t => Vec.t (denote_typ t) (N.to_nat n)
    | Typ.Struct b ts =>
        if b then
          HetVec.t denote_typ (Typ.Bool :: Vec.of_list ts)%vector
        else
          HetVec.t denote_typ (Vec.of_list ts)
    end.
  
  Fail Equations denote_typ : Typ.t -> Set := {
      denote_typ Typ.Bool := bool;
      denote_typ (Typ.Bit w) := Fin.t (N.to_nat w);
      denote_typ (Typ.Int _) := Z;
      denote_typ Typ.Error := String.string;
      denote_typ (Typ.VarBit _) := N;
      denote_typ (Typ.Var n) := σ n;
      denote_typ (Typ.Array n t) := Vec.t (denote_typ t) (N.to_nat n);
      denote_typ (Typ.Struct b ts) :=
        if b then
          HetVec.t denote_typ (Typ.Bool :: Vec.of_list ts)%vector
        else
          HetVec.t denote_typ (Vec.of_list ts)
    }.
End Denote.
