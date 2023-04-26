From Equations Require Import Equations.
Require Import Poulet4.Utils.VecUtil Poulet4.Utils.Util.FunUtil.
Import Vec.VectorNotations.

Section VecMap.
  Polymorphic Universes a b.
  Polymorphic Context {A : Type@{a}} {B : Type@{b}}.
  Polymorphic Variable f : A -> B.

  Import Vec.VectorNotations.
  Local Open Scope vector_scope.

  Polymorphic Equations vec_map : forall {n}, Vec.t A n -> Vec.t B n := {
      vec_map [] := [];
      vec_map (a :: v) := f a :: vec_map v
    }.
End VecMap.

Section ProdN.
  Polymorphic Universe a.
  
  Polymorphic Inductive t : forall {n : nat}, Vec.t Type@{a} n -> Type@{a+1} :=
  | nil : t []%vector
  | cons : forall {A : Type@{a}} {n : nat} {v : Vec.t Type@{a} n},
      A -> t v -> t (A :: v)%vector.

  Polymorphic Derive Signature NoConfusion NoConfusionHom Subterm for t.
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

  Polymorphic Inductive each :
    forall {n : nat} {v : Vec.t Type@{a} n},
      t (Vec.map (fun A => A -> Prop) v) -> t v -> Prop :=
  | each_nil : each (v:=[]%vector) [] []
  | each_cons
      {A : Type@{a}} {n : nat} {v : Vec.t Type@{a} n} (a : A) (p : t v)
      (P : A -> Prop) (props : t (Vec.map (fun A => A -> Prop) v)) :
    P a -> each props p -> each (v:=A :: v)%vector (P :: props) (a :: p).

  Polymorphic Derive Signature for each.
  
  Section fixed.
    Polymorphic Context {A : Type@{a}}.

    Polymorphic Equations hd : forall {n : nat} {v : Vec.t Type@{a} n},
        t (A :: v)%vector -> A := {
        hd (a :: _) := a
      }.

    Polymorphic Equations tl : forall {n : nat} {v : Vec.t Type@{a} n},
        t (A :: v)%vector -> t v := {
        tl (_ :: p) := p
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

    Polymorphic Fixpoint rep (a : A) (n : nat) : t (vec_rep n A) :=
      match n with
      | O => []
      | S n => a :: rep a n
      end.

    Section RepParam.
      Polymorphic Universe b.
      Polymorphic Context {B : A -> Type@{b}} {a : A}.
      Polymorphic Variable (ba : B a).
      
      Polymorphic Fixpoint rep_param (n : nat) : ProdN.t (Vec.map B (vec_rep n a)) :=
        match n with
        | O => []
        | S n => ba :: rep_param n
        end.
    End RepParam.
  End fixed.
  
  Section MapUni.
    Polymorphic Context {A : Type@{a}}.
    Polymorphic Variable a : A.
    
    Polymorphic Universe b.

    Polymorphic Equations map_uni1 :
      forall {n : nat} {BS : Vec.t Type@{b} n},
        ProdN.t (Vec.map (fun B => A -> B -> B) BS) ->
        ProdN.t BS -> ProdN.t BS := {
          map_uni1 [] [] := [];
          map_uni1 (f :: fs) (b :: p) := f a b :: map_uni1 fs p
      }.

    Polymorphic Context {B : Type@{b}}.
    Polymorphic Variable b : B.

    Polymorphic Universe c.

    Polymorphic Equations map_uni2 :
      forall {n : nat} {CS : Vec.t Type@{c} n},
        ProdN.t (Vec.map (fun C => A -> B -> C -> C) CS) ->
        ProdN.t CS -> ProdN.t CS := {
        map_uni2 [] [] := [];
        map_uni2 (f :: fs) (c :: p) := f a b c :: map_uni2 fs p
      }.
  End MapUni.
  
  Section Map.
    Polymorphic Universe b.
    
    Polymorphic Equations map : forall {n : nat} {dom : Vec.t Type@{a} n} {ran : Vec.t Type@{b} n},
        t (Vec.map2 (fun (A : Type@{a}) (B : Type@{b}) => A -> B) dom ran) ->
        t dom -> t ran := {
        map (dom:=[]%vector) (ran:=[]%vector) [] [] := [];
        map (f :: fp) (a :: p) := f a :: map fp p
      }.
    
    (* Takes too long to build:
    Polymorphic Universe c.

    Set Equations Transparent.
    
    Polymorphic Equations map2 :
      forall {n : nat} {dom1 : Vec.t Type@{a} n} {dom2 : Vec.t Type@{b} n} {ran : Vec.t Type@{c} n},
      t (vec_map3 (fun (A : Type@{a}) (B : Type@{b}) (C : Type@{c}) => A -> B -> C) dom1 dom2 ran) ->
      t dom1 -> t dom2 -> t ran := {
        map2 (ran := []%vector) [] [] [] := [];
        map2 (ran := (_ :: _)%vector) (f :: fp) (a :: p1) (b :: p2) := f a b :: map2 fp p1 p2
      }.*)

    (*Section Map2.
      Polymorphic Universe c.

      Polymorphic Context {n : nat} {dom1 : Vec.t Type@{a} n} {dom2 : Vec.t Type@{b} n} {ran : Vec.t Type@{c} n}.
      Polymorphic Variables
                    (fs : t (vec_map3 (fun (A : Type@{a}) (B : Type@{b}) (C : Type@{c}) => A -> B -> C) dom1 dom2 ran))
                    (pa : t dom1) (pb : t dom2).

      Definition map2 : t ran :=
      
    End Map2.*)
  End Map.
End ProdN.

Section MapUni2Thm.
  Import Vec.VectorNotations.
  Import ProdNNotations.
  Open Scope prodn_scope.
  
  Polymorphic Universes a b c.
  Polymorphic Context {A : Type@{a}} {B : Type@{a}} {C : Type@{a}}.
  Polymorphic Variables (f : A -> B -> C -> C) (a : A) (b : B).
  
  Polymorphic Lemma to_vec_map_uni2 :
    forall {n} (p : ProdN.t (vec_rep n C)),
      to_vec
        (map_uni2 (CS:=vec_rep n C) a b
           (ProdN.rep_param f n) p)
      = Vec.map (f a b) (ProdN.to_vec p).
  Proof using.
    intros n p.
    funelim (to_vec p); cbn.
    - rewrite map_uni2_equation_1, to_vec_equation_1; reflexivity.
    - rewrite map_uni2_equation_2. do 2 rewrite to_vec_equation_2.
      cbn; f_equal; auto.
  Qed.
End MapUni2Thm.

Section eachForall.
  Import ProdNNotations.
  Open Scope prodn_scope.
  
  Polymorphic Universe a.
  Polymorphic Context {A : Type@{a}}.
  Polymorphic Variable P : A -> Prop.
  
  Local Hint Constructors each : core.
  
  Polymorphic Lemma Forall_each :
    forall {n : nat} (v : Vec.t A n),
      Vec.Forall P v ->
      each (rep_param P n) (of_vec v).
  Proof using.
    intros n v hv; depind hv; cbn; auto.
    rewrite of_vec_equation_2.
    auto.
  Qed.

  Local Hint Constructors Vec.Forall : core.
  
  Polymorphic Lemma each_Forall :
    forall {n : nat} (p : ProdN.t (vec_rep n A)),
      ProdN.each (ProdN.rep_param P n) p ->
      Vec.Forall P (to_vec p).
  Proof using.
    intro n; induction n as [| n ih];
      intros p hp; cbn in *; depelim hp.
    - rewrite to_vec_equation_1. constructor.
    - rewrite to_vec_equation_2. auto.
  Qed.
End eachForall.

Module ProdNZip.
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
  
  Section Zip.
    Import ProdNNotations.
    Open Scope prodn_scope.
    
    Polymorphic Universe a b.

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
End ProdNZip.
