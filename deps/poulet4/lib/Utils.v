Require Import Coq.Bool.Bvector.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.NArith.BinNatDef.
Require Import Coq.ZArith.BinIntDef.
Require Import Coq.PArith.BinPos.
Require Import Coq.Structures.OrderedTypeEx.

Require Import Poulet4.Monads.Monad.
Require Import Poulet4.Monads.Option.

Open Scope monad.

Fixpoint assoc_update {A: Type} (key: string) (val: A) (map: list (string * A)) : option (list (string * A)) :=
  match map with
  | (s, v) :: map' =>
    if String_as_OT.eq_dec s key
    then mret ((key, val) :: map')
    else let* map' := assoc_update key val map' in
         mret ((s, v) :: map')
  | nil => None
  end.

Fixpoint rotate_left_nat {A: Type} (elements: list A) (count: nat) (pad: A) : option (list A) :=
  match count with
  | 0 => Some elements
  | S count' =>
    match elements with
    | nil => None
    | header :: elements' =>
      rotate_left_nat (elements' ++ pad :: nil) count' pad
    end
  end.

Definition rotate_left_z {A: Type} (elements: list A) (count: Z) (pad: A) : option (list A) :=
  match count with
  | Zneg _ => None
  | Zpos count' => rotate_left_nat elements (Pos.to_nat count') pad
  | Z0 => rotate_left_nat elements 0 pad
  end.


Fixpoint rotate_right_nat {A: Type} (elements: list A) (count: nat) (pad: A) : option (list A) :=
  match count with
  | 0 => Some elements
  | S count' =>
    match elements  with
    | nil => None
    | header :: elements' =>
      rotate_right_nat (pad :: (removelast elements)) count' pad
    end
  end.

Definition rotate_right_z {A: Type} (elements: list A) (count: Z) (pad: A) : option (list A) :=
  match count with
  | Zneg _ => None
  | Zpos count' => rotate_right_nat elements (Pos.to_nat count') pad
  | Z0 => rotate_right_nat elements 0 pad
  end.

Definition list_slice_z {A: Type} (l: list A) (lo: Z) (hi: Z) : option (list A).
Admitted.

Fixpoint list_slice_nat {A: Type} (l: list A) (lo: nat) (hi: nat) : option (list A) :=
  match (lo, hi) with
  | (0, 0)          => Some nil
  | (S _, 0)        => None
  | (0, S hi')      =>
    match l with
    | nil     => None
    | x :: xs => option_map (fun t => x :: t) (list_slice_nat xs 0 hi')
    end
  | (S lo', S hi')  =>
    match l with
    | nil      => None
    | x :: xs => list_slice_nat xs lo' hi'
    end
  end.

Definition index_z_error {A} (xs: list A) (i: Z) : option A.
Admitted.

Fixpoint truncate_bits (bits: positive) (count: nat) : N :=
  match count with
  | 0 => N0
  | S count' =>
    match bits with
    | xH => Npos xH
    | xO bits' =>
      match truncate_bits bits' count' with
      | N0 => N0
      | Npos rest => Npos (xO rest)
      end
    | xI bits' =>
      match truncate_bits bits' count' with
      | N0 => Npos xH
      | Npos rest => Npos (xI rest)
      end
    end
  end
.

Fixpoint glue_msb (bits: positive) :=
  match bits with
  | xH => xI xH
  | xO bits' => xO (glue_msb bits')
  | xI bits' => xI (glue_msb bits')
  end
.

Definition cast_bits_unsigned (bits: Z) (wold wnew: nat) : Z :=
  if Nat.eqb wold wnew then
    (* No difference in width; pass along old value. *)
    bits
  else if Nat.leb wold wnew then
    (* Strict widening. *)
    match bits with
    | Z0
    | Zpos _ =>
      bits
    | Zneg bits' =>
      (* Sign bit becomes part of the regular bits. *)
      Zpos (glue_msb bits')
    end
  else
    (* Strict truncation, i.e., wnew < wold. We can safely
       truncate without caring about the sign bit, because
       that is always discarded. *)
    match bits with
    | Z0 => Z0
    | Zpos bits'
    | Zneg bits' =>
      match truncate_bits bits' wnew with
      | N0 => Z0
      | Npos bits'' =>
        Zpos bits''
      end
    end
.

Fixpoint bits_length_positive (bits: positive) : nat :=
  match bits with
  | xH => 1
  | xO bits'
  | xI bits' =>
    1 + bits_length_positive bits'
  end
.

Definition bits_length_Z (bits: Z) : nat :=
  match bits with
  | Z0 => 0
  | Zpos bits' => bits_length_positive bits'
  | Zneg bits' => 1 + bits_length_positive bits'
  end
.

(* Coq Bvectors are little-endian *)
Open Scope vector_scope.
Fixpoint of_bvector {w} (bits: Bvector w) : Z :=
  match bits with
  | [] => 0
  | (b :: bits') => Z.add (if b then 1 else 0) (Z.double (of_bvector bits'))
  end.
Close Scope vector_scope.

Section list_rec.
  Context
    {A: Type}
    (PA: A -> Type)
    (PAList: list A -> Type)
    (HAListNil: PAList nil)
    (HAListCons: forall (a : A) (l: list A),
                 PA a -> PAList l -> PAList (a :: l))
  .

  Variable (rec: forall a: A, PA a).

  Fixpoint list_rec (l: list A) : PAList l :=
    match l with
    | nil => HAListNil
    | f :: l' =>
      HAListCons f l' (rec f) (list_rec l')
    end
  .
End list_rec.

Section option_rec.
  Context
    {A: Type}
    (PA: A -> Type)
    (PAOption: option A -> Type)
    (PAOptionNone: PAOption None)
    (PAOptionSome: forall a: A, PA a -> PAOption (Some a))
  .

  Variable (rec: forall a: A, PA a).

  Definition option_rec (o: option A) : PAOption o :=
    match o with
    | None => PAOptionNone
    | Some a => PAOptionSome a (rec a)
    end
  .
End option_rec.

Section MapCombine.
  Variables U V : Type.
  
  Lemma combine_map_fst_snd : forall (l : list (U * V)),
      combine (map fst l) (map snd l) = l.
  Proof.
    intro l; induction l as [| [u v] l IHl];
      simpl; f_equal; auto.
  Qed.
  
  Lemma map_fst_combine : forall (us : list U) (vs : list V),
      List.length us = List.length vs ->
      map fst (combine us vs) = us.
  Proof.
    intro us; induction us as [| u us IHus];
      intros [| v vs] Hl; simpl in *;
        inversion Hl; subst; f_equal; auto.
  Qed.
  
  Lemma map_snd_combine : forall (us : list U) (vs : list V),
      List.length us = List.length vs ->
      map snd (combine us vs) = vs.
  Proof.
    intro us; induction us as [| u us IHus];
      intros [| v vs] Hl; simpl in *;
        inversion Hl; subst; f_equal; auto.
  Qed.
End MapCombine.

Section Forall.
  Variables (A B : Type) (R : A -> B -> Prop).
  
  Lemma Forall_exists_factor : forall l : list A,
      Forall (fun a => exists b, R a b) l <-> exists bs, Forall2 R l bs.
  Proof.
    intro l; split.
    - intro H; induction H; eauto.
      destruct H as [b HRb];
      destruct IHForall as [bs HRbs]; eauto.
    - intros [bs HRlbs].
      induction HRlbs; eauto.
  Qed.

  Lemma forall_Forall2 : forall (l : list A),
      (forall a, In a l -> forall b, R a b) ->
      forall bs, List.length l = List.length bs -> Forall2 R l bs.
  Proof.
    intro l;
      induction l as [| a l IHl];
      intros H [| b bs] Hbs; simpl in *; try discriminate; auto.
  Qed.

  Lemma Forall2_length : forall la lb,
      Forall2 R la lb -> List.length la = List.length lb.
  Proof.
    intros la lb H; induction H;
      simpl; f_equal; auto.
  Qed.

  Lemma Forall2_flip : forall la lb,
      Forall2 (fun b a => R a b) lb la <-> Forall2 R la lb.
  Proof.
    intros la lb; split; intros H;
      induction H; auto.
  Qed.
  
  Variable Q : A -> B -> Prop.
  
  Lemma Forall2_impl : forall la lb,
      Forall2 (fun a b => R a b -> Q a b) la lb ->
      Forall2 R la lb -> Forall2 Q la lb.
  Proof.
    intros la lb HRQ HR;
      induction HRQ; inversion HR; subst; auto.
  Qed.

  Lemma Forall2_conj : forall us vs,
      Forall2 (fun u v => R u v /\ Q u v) us vs <->
      Forall2 R us vs /\ Forall2 Q us vs.
  Proof.
    intros us vs; split.
    - intros H; induction H; simpl in *; intuition.
    - intros [HR HQ]; induction HR; inversion HQ;
        simpl in *; auto.
  Qed.
End Forall.

Section ForallMap.
  Variables (A B C : Type) (R : A -> B -> Prop).
  
  Lemma Forall2_map_l : forall (f : C -> A) lc lb,
      Forall2 (fun c b => R (f c) b) lc lb <-> Forall2 R (map f lc) lb.
  Proof.
    intros f lc lb; split; intros H.
    - induction H; simpl in *; auto.
    - remember (map f lc) as la eqn:Heqla;
        generalize dependent lc.
      induction H; intros [| ? ?] Heqla;
      simpl in *; inversion Heqla; subst; auto.
  Qed.
  
  Lemma Forall2_map_r : forall (f : C -> B) la lc,
      Forall2 (fun a c => R a (f c)) la lc <-> Forall2 R la (map f lc).
  Proof.
    intros f la lc; split; intros H.
    - induction H; simpl in *; auto.
    - remember (map f lc) as mflc eqn:Hmflc.
      generalize dependent lc.
      induction H; intros lc Hmflc.
      + symmetry in Hmflc; apply map_eq_nil in Hmflc; subst; auto.
      + destruct lc as [| c lc]; simpl in *;
          inversion Hmflc; subst; auto.
  Qed.
End ForallMap.

Lemma Forall2_map_both :
  forall (T U V W : Type) (R : V -> W -> Prop) (f : T -> V) (g : U -> W) ts us,
    Forall2 (fun t u => R (f t) (g u)) ts us <-> Forall2 R (map f ts) (map g us).
Proof.
  intros; rewrite <- Forall2_map_l, <- Forall2_map_r; reflexivity.
Qed.

Lemma reduce_inner_impl : forall (A : Type) (Q : Prop) (P R : A -> Prop),
    (forall a, P a -> Q -> R a) -> Q -> forall a, P a -> R a.
Proof.
  intuition.
Qed.

Lemma reduce_inner_impl_forall : forall (A : Type) (P Q R : A -> Prop),
    (forall a, P a -> Q a -> R a) -> (forall a, P a -> Q a) -> forall a, P a -> R a.
Proof.
  intuition.
Qed.

Lemma reduce_inner_impl_forall_impl : forall (A : Type) (P Q R S : A -> Prop),
    (forall a, S a -> Q a) -> (forall a, P a -> Q a -> R a) ->
    (forall a, P a -> S a) -> forall a, P a -> R a.
Proof.
  intuition.
Qed.


Lemma split_impl_conj : forall (A : Type) (P Q R : A -> Prop),
    (forall a, P a -> Q a /\ R a) <->
    (forall a, P a -> Q a) /\ forall a, P a -> R a.
Proof.
  firstorder.
Qed.

Lemma Forall2_Forall : forall (U : Type) (R : U -> U -> Prop) us,
    Forall2 R us us <-> Forall (fun u => R u u) us.
Proof.
  intros U R us; split;
    induction us as [| u us IHus];
    intros H; inversion H; subst; simpl in *; auto.
Qed.

Section MapMap.
  Variables (U V W X : Type)
            (f : U -> W) (g : V -> X).

  Lemma map_fst_map : forall (uvs : list (U * V)),
      map fst (map (fun '(u,v) => (f u, g v)) uvs) = map f (map fst uvs).
  Proof.
    intro uvs; induction uvs as [| [u v] uvs IHuvs];
      simpl in *; f_equal; auto.
  Qed.
  
  Lemma map_snd_map : forall (uvs : list (U * V)),
      map snd (map (fun '(u,v) => (f u, g v)) uvs) = map g (map snd uvs).
  Proof.
    intro uvs; induction uvs as [| [u v] uvs IHuvs];
      simpl in *; f_equal; auto.
  Qed.
End MapMap.
  
Lemma map_only_fst : forall (U V W : Type) (f : U -> V) (uws : list (U * W)),
    map (fun '(u,w) => (f u, w)) uws =
    let '(us,ws) := split uws in
    combine (map f us) ws.
Proof.
  intros U V W f uws;
    induction uws as [| [u w] uws IHuws];
    simpl in *; auto.
  destruct (split uws) as [us ws] eqn:Hequws;
    simpl in *; f_equal; auto.
Qed.

Lemma map_only_snd : forall (U V W : Type) (f : V -> W) (uvs : list (U * V)),
    map (fun '(u,v) => (u, f v)) uvs =
    let '(us,vs) := split uvs in
    combine us (map f vs).
Proof.
  intros U V W f uvs;
    induction uvs as [| [u v] uvs IHuvs];
    simpl in *; auto.
  destruct (split uvs) as [us vs] eqn:Hequws;
    simpl in *; f_equal; auto.
Qed.

Lemma Forall_fst : forall (U V : Type) (P : U -> Prop) (uvs : list (U * V)),
    Forall (fun '(u,_) => P u) uvs <-> Forall (fun uv => P (fst uv)) uvs.
Proof.
  intros U V P uvs; split; intro H;
    induction uvs as [| [u v] uvs IHuvs];
    inversion H; subst; simpl in *; auto.
Qed.

Lemma Forall_snd : forall (U V : Type) (P : V -> Prop) (uvs : list (U * V)),
    Forall (fun '(_,v) => P v) uvs <-> Forall (fun uv => P (snd uv)) uvs.
Proof.
  intros U V P uvs; split; intro H;
    induction uvs as [| [u v] uvs IHuvs];
    inversion H; subst; simpl in *; auto.
Qed.

Lemma Forall2_eq : forall (U : Type) (us vs : list U),
    Forall2 eq us vs <-> us = vs.
Proof.
  intros U us vs; split; intros H; subst.
  - induction H; subst; auto.
  - induction vs; auto.
Qed.

Lemma map_pat_both : forall (U V W : Type) (f : U -> V -> W) luv,
    map (fun '(u,v) => f u v) luv = map (fun uv => f (fst uv) (snd uv)) luv.
Proof.
  intros U V W f luv;
    induction luv as [| [u v] luv IHluv];
    simpl; f_equal; auto.
Qed.

Lemma Forall2_destr_pair_eq :
  forall {U V W : Type}
    (f : V -> option W)
    (luv : list (U * V)) (luw : list (U * W)),
    Forall2 (fun uv uw =>
               match f (snd uv) with
               | Some w => Some (fst uv, w)
               | None   => None
               end = Some uw) luv luw <->
    map fst luv = map fst luw /\
    Forall2 (fun v w => f v = Some w) (map snd luv) (map snd luw).
Proof.
  intros U V W f luv luw; split;
    generalize dependent luw;
    induction luv as [| [u v] luv IHluv];
    intros [| [u' w] luw]; simpl in *; intros H; auto.
  - inversion H.
  - inversion H.
  - inversion H; subst; clear H; simpl in *.
    destruct (f v) as [w' |] eqn:Heqfv; simpl in *;
      inversion H3; subst; clear H3.
    apply IHluv in H5 as [Hfst Hsnd];
      rewrite Hfst; split; auto.
  - destruct H as [H _]; inversion H.
  - destruct H as [H _]; inversion H.
  - destruct H as [Hfst Hsnd];
      inversion Hfst; inversion Hsnd; subst; clear Hfst Hsnd;
        constructor; simpl; auto.
    rewrite H4; auto.
Qed.
