From Coq Require Export NArith.BinNat Strings.String
     Lists.List micromega.Lia.
Require Export VST.zlist.sublist.
From Poulet4 Require Export P4light.Syntax.Typed
     P4light.Syntax.Syntax Monads.Option
     P4light.Syntax.ValueUtil
     Utils.ForallMap P4light.Semantics.Typing.Ok
     P4light.Semantics.Typing.IsTerm.
Export ListNotations.
Require Poulet4.P4light.Syntax.P4String
        Poulet4.Utils.AListUtil.

(** * Utility Definitions & Lemmas for Type System. *)

Section Util.
  Context {tags_t : Type}.
  Notation typ  := (@P4Type tags_t).
  Notation expr := (@Expression tags_t).
  
  Definition
    string_of_name (X : @Typed.name tags_t) : string :=
    match X with
    | BareName        {| P4String.str:=T |}
    | QualifiedName _ {| P4String.str:=T |} => T
    end.
  
  (** Evidence for a type being a numeric of a given width. *)
  Variant numeric_width (w : N) : typ -> Prop :=
  | numeric_width_bit : numeric_width w (TypBit w)
  | numeric_width_int : numeric_width w (TypInt w).
  
  (** Evidence for a type being numeric. *)
  Variant numeric : typ -> Prop :=
  | NumericFixed (w : N) τ :
      numeric_width w τ -> numeric τ
  | NumericArbitrary :
      numeric TypInteger.
  
  (** Evidence a unary operation is valid for a type. *)
  Variant unary_type : OpUni -> typ -> typ -> Prop :=
  | UTNot :
      unary_type Not TypBool TypBool
  | UTBitNot w τ :
      numeric_width w τ -> unary_type BitNot τ τ
  | UTUMinus τ :
      numeric τ -> unary_type UMinus τ τ.
  
  Lemma unary_type_eq : forall o t t', unary_type o t t' -> t = t'.
  Proof.
    intros ? ? ? H; inversion H; subst; auto.
  Qed.

  (** Types of terms that may be compared for equality. *)
  Inductive Eq_type : typ -> Prop :=
  | Eq_Error :
      Eq_type TypError
  | Eq_Enum E t mems :
      predop Eq_type t ->
      Eq_type (TypEnum E t mems)
  | Eq_Bool :
      Eq_type TypBool
  | Eq_Bit w :
      Eq_type (TypBit w)
  | Eq_Int w :
      Eq_type (TypInt w)
  | Eq_VarBit w :
      Eq_type (TypVarBit w)
  | Eq_Integer :
      Eq_type TypInteger
  | Eq_Struct xts :
      Forall (Eq_type ∘ snd) xts ->
      Eq_type (TypStruct xts)
  | Eq_Union xts :
      Forall (Eq_type ∘ snd) xts ->
      Eq_type (TypHeaderUnion xts)
  | Eq_Header xts :
      Forall (Eq_type ∘ snd) xts ->
      Eq_type (TypHeaderUnion xts)
  | Eq_Tuple ts :
      Forall Eq_type ts ->
      Eq_type (TypTuple ts)
  | Eq_Array t n :
      Eq_type t ->
      Eq_type (TypArray t n).
  
  (** Evidence a binary operation is valid for given types. *)
  Variant binary_type : OpBin -> typ -> typ -> typ -> Prop :=
  | BTPlusPlusBit w1 w2 t2 :
      numeric_width w2 t2 ->
      binary_type PlusPlus (TypBit w1) t2 (TypBit (w1 + w2)%N)
  | BTPlusPlusInt w1 w2 t2 :
      numeric_width w2 t2 ->
      binary_type PlusPlus (TypInt w1) t2 (TypInt (w1 + w2)%N)
  | BTShlBit t1 w2 :
      numeric t1 ->
      binary_type Shl t1 (TypBit w2) t1
  | BTShlInteger t1 :
      numeric t1 ->
      binary_type Shl t1 TypInteger t1
  | BTShrBit t1 w2 :
      numeric t1 ->
      binary_type Shr t1 (TypBit w2) t1
  | BTShrInteger t1 :
      numeric t1 ->
      binary_type Shr t1 TypInteger t1
  | BTEq t :
      Eq_type t ->
      binary_type Eq t t TypBool
  | BTNotEq t :
      Eq_type t ->
      binary_type NotEq t t TypBool
  | BTPlus t :
      numeric t ->
      binary_type Plus t t t
  | BTMinus t :
      numeric t ->
      binary_type Minus t t t
  | BTMul t :
      numeric t ->
      binary_type Mul t t t
  | BTDivBit w :
      binary_type Div (TypBit w) (TypBit w) (TypBit w)
  | BTDivInteger :
      binary_type Div TypInteger TypInteger TypInteger
  | BTModBit w :
      binary_type Mod (TypBit w) (TypBit w) (TypBit w)
  | BTModInteger :
      binary_type Mod TypInteger TypInteger TypInteger
  | BTLe t :
      numeric t ->
      binary_type Le t t TypBool
  | BTGe t :
      numeric t ->
      binary_type Ge t t TypBool
  | BTLt t :
      numeric t ->
      binary_type Lt t t TypBool
  | BTGt t :
      numeric t ->
      binary_type Gt t t TypBool
  | BTPlusSat w t :
      numeric_width w t ->
      binary_type PlusSat t t t
  | BTMinusSat w t :
      numeric_width w t ->
      binary_type MinusSat t t t
  | BTBitAnd w t :
      numeric_width w t ->
      binary_type BitAnd t t t
  | BTBitOr w t :
      numeric_width w t ->
      binary_type BitOr t t t
  | BTBitXor w t :
      numeric_width w t ->
      binary_type BitXor t t t
  | BTAnd :
      binary_type And TypBool TypBool TypBool
  | BTOr :
      binary_type Or TypBool TypBool TypBool.

  (** [cast_type τ₁ τ₂] is evidence
      a cast from [τ₁] to [τ₂] is allowed. *)
  Inductive cast_type : typ -> typ -> Prop :=
  | Cast_Bit_Bool :
    cast_type (TypBit 1) TypBool
  | Cast_Bool_Bit :
    cast_type TypBool (TypBit 1)
  | Cast_Int_Bit w :
    cast_type (TypInt w) (TypBit w)
  | Cast_Bit_Bit w₁ w₂ :
    cast_type (TypBit w₁) (TypBit w₂)
  | Cast_Integer_Bit w :
    cast_type TypInteger (TypBit w)
  | Cast_Senum_Bit E w members :
    cast_type (TypEnum E (Some (TypBit w)) members) (TypBit w)
  | Cast_Bit_Int w :
    cast_type (TypBit w) (TypInt w)
  | Cast_Integer_Int w :
    cast_type TypInteger (TypInt w)
  | Cast_Senum_Int E w members :
    cast_type (TypEnum E (Some (TypInt w)) members) (TypInt w)
  | Cast_NewType_Type X τ₁ τ₂ :
    cast_type τ₁ τ₂ ->
    cast_type (TypNewType X τ₁) τ₂
  | Cast_Bit_Senum w E members :
    cast_type (TypBit w) (TypEnum E (Some (TypBit w)) members)
  | Cast_Senum_Senum_Bit E₁ E₂ w members₁ members₂ :
    cast_type
      (TypEnum E₁ (Some (TypBit w)) members₁)
      (TypEnum E₂ (Some (TypBit w)) members₂)
  | Cast_Int_Senum w E members :
    cast_type (TypInt w) (TypEnum E (Some (TypInt w)) members)
  | Cast_Senum_Senum_Int E₁ E₂ w members₁ members₂ :
    cast_type
      (TypEnum E₁ (Some (TypInt w)) members₁)
      (TypEnum E₂ (Some (TypInt w)) members₂)
  | Cast_Tuple_Struct ts xts :
    AList.key_unique xts = true ->
    Forall2 (fun t xt => cast_type t (snd xt)) ts xts ->
    cast_type (TypTuple ts) (TypStruct xts)
  | Cast_Header_Struct xts yts :
    AList.key_unique xts = true ->
    AList.key_unique yts = true ->
    AList.all_values cast_type xts yts ->
    cast_type (TypHeader xts) (TypStruct yts)
  | Cast_Struct_Struct xts yts :
    AList.key_unique xts = true ->
    AList.key_unique yts = true ->
    AList.all_values cast_type xts yts ->
    cast_type (TypStruct xts) (TypStruct yts)
  | Cast_Tuple_Header ts xts :
    AList.key_unique xts = true ->
    Forall2 (fun t xt => cast_type t (snd xt)) ts xts ->
    cast_type (TypTuple ts) (TypHeader xts)
  | Cast_Header_Header xts yts :
    AList.key_unique xts = true ->
    AList.key_unique yts = true ->
    AList.all_values cast_type xts yts ->
    cast_type (TypHeader xts) (TypHeader yts)
  | Cast_Struct_Header xts yts :
    AList.key_unique xts = true ->
    AList.key_unique yts = true ->
    AList.all_values cast_type xts yts ->
    cast_type (TypStruct xts) (TypHeader yts)
  | Cast_Tuple_Tuple ts₁ ts₂ :
    Forall2 cast_type ts₁ ts₂ ->
    cast_type (TypTuple ts₁) (TypTuple ts₂).
  
  (** Types whose fields are accessable via [AList.v] functions. *)
  Variant member_type (ts : P4String.AList tags_t typ)
    : typ -> Prop :=
  | record_member_type :
      member_type ts (TypRecord ts)
  | struct_member_type :
      member_type ts (TypStruct ts)
  | header_member_type :
      member_type ts (TypHeader ts)
  | union_member_type :
      member_type ts (TypHeaderUnion ts).

  (** May syntactically appear as an l-expression. *)
  Inductive lexpr_ok : expr -> Prop :=
  | lexpr_name tag x loc t dir :
    match dir with
    | Directionless => False | _ => True
    end ->
    lexpr_ok (MkExpression tag (ExpName x loc) t dir)
  | lexpr_member tag e x t dir :
    P4String.str x <> "size"%string ->
    P4String.str x <> "lastIndex"%string ->
    lexpr_ok e ->
    lexpr_ok (MkExpression tag (ExpExpressionMember e x) t dir)
  | lexpr_slice tag e hi lo t dir :
    lexpr_ok e ->
    lexpr_ok (MkExpression tag (ExpBitStringAccess e lo hi) t dir)
  | lexpr_access tag e₁ e₂ t dir :
    lexpr_ok e₁ ->
    lexpr_ok (MkExpression tag (ExpArrayAccess e₁ e₂) t dir).

  (** "Normalizes" a type to those in a
      one-to-one correspondence with values
      as defined in [ValueTyping.v]. *)
  Fixpoint normᵗ (t : typ) : typ :=
    match t with
    | TypBool
    | TypString
    | TypInteger
    | TypInt _
    | TypBit _
    | TypVarBit _
    | TypError
    | TypMatchKind
    | TypVoid
    | TypTypeName _
    | TypExtern _
    | TypTable _   => t
    | TypArray t n => TypArray (normᵗ t) n
    | TypList  ts
    | TypTuple ts  => TypTuple (map normᵗ ts)
    | TypRecord ts
    | TypStruct ts => TypStruct (map (fun '(x,t) => (x, normᵗ t)) ts)
    | TypSet    t  => TypSet (normᵗ t)
    | TypHeader ts => TypHeader (map (fun '(x,t) => (x, normᵗ t)) ts)
    | TypHeaderUnion ts => TypHeaderUnion (map (fun '(x,t) => (x, normᵗ t)) ts)
    | TypEnum X t ms    => TypEnum X (option_map normᵗ t) ms
    | TypNewType _ t    => normᵗ t
    | TypControl ct             => TypControl (normᶜ ct)
    | TypParser  ct             => TypParser  (normᶜ ct)
    | TypFunction ft            => TypFunction (normᶠ ft)
    | TypAction cs ds           => TypAction (map normᵖ cs) (map normᵖ ds)
    | TypPackage Xs ws ps       => TypPackage Xs ws (map normᵖ ps)
    | TypSpecializedType t ts   => TypSpecializedType (normᵗ t) (map normᵗ ts)
    | TypConstructor Xs ws ps t => TypConstructor Xs ws (map normᵖ ps) (normᵗ t)
    end
  with normᶜ (ct : ControlType) : ControlType :=
         match ct with
         | MkControlType Xs ps => MkControlType Xs (map normᵖ ps)
         end
  with normᶠ (ft : FunctionType) : FunctionType :=
         match ft with
         | MkFunctionType Xs ps k t
           => MkFunctionType Xs (map normᵖ ps) k (normᵗ t)
         end
  with normᵖ (p : P4Parameter) : P4Parameter :=
         match p with
         | MkParameter b d t a x => MkParameter b d (normᵗ t) a x
         end.
End Util.

Ltac inv_numeric_width :=
  match goal with
  | H: numeric_width _ _ |- _ => inversion H; subst
  end.

Ltac inv_numeric :=
  match goal with
  | H: numeric _ |- _ => inversion H; subst; try inv_numeric_width
  end.

Section EqTypeInd.
  Variable tags_t : Type.
  Notation typ := (@P4Type tags_t).
  Variable P : typ -> Prop.

  Hypothesis HError : P TypError.
  Hypothesis HEnum : forall E t mems,
      predop Eq_type t ->
      predop P t ->
      P (TypEnum E t mems).
  Hypothesis HBool : P TypBool.
  Hypothesis HBit : forall w, P (TypBit w).
  Hypothesis HInt : forall w, P (TypInt w).
  Hypothesis HVarBit : forall w, P (TypVarBit w).
  Hypothesis HInteger : P TypInteger.
  Hypothesis HStruct : forall xts,
      Forall (Eq_type ∘ snd) xts ->
      Forall (P ∘ snd) xts ->
      P (TypStruct xts).
  Hypothesis HUnion : forall xts,
      Forall (Eq_type ∘ snd) xts ->
      Forall (P ∘ snd) xts ->
      P (TypHeaderUnion xts).
  Hypothesis HHeader : forall xts,
      Forall (Eq_type ∘ snd) xts ->
      Forall (P ∘ snd) xts ->
      P (TypHeaderUnion xts).
  Hypothesis HTuple : forall ts,
      Forall Eq_type ts ->
      Forall P ts ->
      P (TypTuple ts).
  Hypothesis HArray : forall t n,
      Eq_type t ->
      P t ->
      P (TypArray t n).

  Definition my_Eq_type_ind :
    forall t : typ, Eq_type t -> P t :=
    fix I t H :=
      let PI {t} (H: predop Eq_type t) : predop P t :=
          match H with
          | predop_none _     => predop_none _
          | predop_some _ _ H => predop_some _ _ (I _ H)
          end in
      let fix LI {ts} (H: Forall Eq_type ts) : Forall P ts :=
          match H with
          | Forall_nil _        => Forall_nil _
          | Forall_cons _ Hh Ht => Forall_cons _ (I _ Hh) (LI Ht)
          end in
      let fix ALI {xts} (H: Forall (Eq_type ∘ snd) xts)
          : Forall (P ∘ snd) xts :=
          match H with
          | Forall_nil _        => Forall_nil _
          | Forall_cons _ Hh Ht => Forall_cons _ (I _ Hh) (ALI Ht)
          end in
      match H with
      | Eq_Error        => HError
      | Eq_Enum E _ m H => HEnum E _ m H (PI H)
      | Eq_Bool         => HBool
      | Eq_Bit w        => HBit w
      | Eq_Int w        => HInt w
      | Eq_Integer      => HInteger
      | Eq_VarBit w     => HVarBit w
      | Eq_Array _ n H  => HArray _ n H (I _ H)
      | Eq_Struct _ H   => HStruct _ H (ALI H)
      | Eq_Header _ H   => HHeader _ H (ALI H)
      | Eq_Union  _ H   => HUnion  _ H (ALI H)
      | Eq_Tuple  _ H   => HTuple  _ H (LI H)
      end.
End EqTypeInd.

Section Cast_Type_ind.
  Variable tags_t : Type.
  Notation typ := (@P4Type tags_t).
  Variable P : typ -> typ -> Prop.
  Hypothesis ih_bit_bool : P (TypBit 1) TypBool.
  Hypothesis ih_bool_bit : P TypBool (TypBit 1).
  Hypothesis ih_int_bit : forall w, P (TypInt w) (TypBit w).
  Hypothesis ih_bit_bit : forall w₁ w₂, P (TypBit w₁) (TypBit w₂).
  Hypothesis ih_integer_bit : forall w, P TypInteger (TypBit w).
  Hypothesis ih_senum_bit : forall E w mems,
      P (TypEnum E (Some (TypBit w)) mems) (TypBit w).
  Hypothesis ih_bit_int : forall w, P (TypBit w) (TypInt w).
  Hypothesis ih_integer_int : forall w, P TypInteger (TypInt w).
  Hypothesis ih_senum_int : forall E w mems,
      P (TypEnum E (Some (TypInt w)) mems) (TypInt w).
  Hypothesis ih_newtype_type : forall X t1 t2,
      cast_type t1 t2 -> P t1 t2 -> P (TypNewType X t1) t2.
  Hypothesis ih_bit_senum : forall w E members,
      P (TypBit w) (TypEnum E (Some (TypBit w)) members).
  Hypothesis ih_senum_senum_bit : forall E₁ E₂ w members₁ members₂,
      P (TypEnum E₁ (Some (TypBit w)) members₁)
        (TypEnum E₂ (Some (TypBit w)) members₂).
  Hypothesis ih_int_senum : forall w E members,
      P (TypInt w) (TypEnum E (Some (TypInt w)) members).
  Hypothesis ih_senum_senum_int : forall E₁ E₂ w members₁ members₂,
      P (TypEnum E₁ (Some (TypInt w)) members₁)
        (TypEnum E₂ (Some (TypInt w)) members₂).
  Hypothesis ih_tuple_struct : forall ts xts,
      AList.key_unique xts = true ->
      Forall2 (fun t xt => cast_type t (snd xt)) ts xts ->
      Forall2 (fun t xt => P t (snd xt)) ts xts ->
      P (TypTuple ts) (TypStruct xts).
  Hypothesis ih_header_struct : forall xts yts,
      AList.key_unique xts = true ->
      AList.key_unique yts = true ->
      AList.all_values cast_type xts yts ->
      AList.all_values P xts yts ->
      P (TypHeader xts) (TypStruct yts).
  Hypothesis ih_struct_struct : forall xts yts,
      AList.key_unique xts = true ->
      AList.key_unique yts = true ->
      AList.all_values cast_type xts yts ->
      AList.all_values P xts yts ->
      P (TypStruct xts) (TypStruct yts).
  Hypothesis ih_tuple_header : forall ts xts,
      AList.key_unique xts = true ->
      Forall2 (fun t xt => cast_type t (snd xt)) ts xts ->
      Forall2 (fun t xt => P t (snd xt)) ts xts ->
      P (TypTuple ts) (TypHeader xts).
  Hypothesis ih_header_header : forall xts yts,
      AList.key_unique xts = true ->
      AList.key_unique yts = true ->
      AList.all_values cast_type xts yts ->
      AList.all_values P xts yts ->
      P (TypHeader xts) (TypHeader yts).
  Hypothesis ih_struct_header : forall xts yts,
      AList.key_unique xts = true ->
      AList.key_unique yts = true ->
      AList.all_values cast_type xts yts ->
      AList.all_values P xts yts ->
      P (TypStruct xts) (TypHeader yts).
  Hypothesis ih_tuple_tuple : forall ts1 ts2,
      Forall2 cast_type ts1 ts2 ->
      Forall2 P ts1 ts2 ->
      P (TypTuple ts1) (TypTuple ts2).

  Definition my_cast_type_ind : forall τ₁ τ₂ : typ,
      cast_type τ₁ τ₂ -> P τ₁ τ₂ :=
    fix cstind t1 t2 hc :=
      let fix lind {ts1 ts2}
            (hc : Forall2 cast_type ts1 ts2)
        : Forall2 P ts1 ts2 :=
        match hc with
        | Forall2_nil _ => Forall2_nil _
        | Forall2_cons _ _ h t =>
            Forall2_cons _ _ (cstind _ _ h) (lind t)
        end in
      let fix alind {xts yts}
            (hc : AList.all_values cast_type xts yts)
        : AList.all_values P xts yts :=
        match hc with
        | Forall2_nil _ => Forall2_nil _
        | Forall2_cons _ _ (conj hk h) t =>
            Forall2_cons _ _ (conj hk (cstind _ _ h)) (alind t)
        end in
      let fix to_alind {ts xts}
            (hc : Forall2 (fun t xt => cast_type t (snd xt)) ts xts)
        : Forall2 (fun t xt => P t (snd xt)) ts xts :=
        match hc with
        | Forall2_nil _ => Forall2_nil _
        | Forall2_cons _ _ h t =>
            Forall2_cons _ _ (cstind _ _ h) (to_alind t)
        end in
      match hc with
      | Cast_Bit_Bool => ih_bit_bool
      | Cast_Bool_Bit => ih_bool_bit
      | Cast_Int_Bit w => ih_int_bit w
      | Cast_Bit_Bit w1 w2 => ih_bit_bit w1 w2
      | Cast_Integer_Bit w => ih_integer_bit w
      | Cast_Senum_Bit E w mems => ih_senum_bit E w mems
      | Cast_Bit_Int w => ih_bit_int w
      | Cast_Integer_Int w => ih_integer_int w
      | Cast_Senum_Int E w mems => ih_senum_int E w mems
      | Cast_NewType_Type X _ _ h => ih_newtype_type X _ _ h (cstind _ _ h)
      | Cast_Bit_Senum E w mems => ih_bit_senum E w mems
      | Cast_Senum_Senum_Bit a b c d e => ih_senum_senum_bit a b c d e
      | Cast_Int_Senum E w mems => ih_int_senum E w mems
      | Cast_Senum_Senum_Int a b c d e => ih_senum_senum_int a b c d e
      | Cast_Tuple_Struct _ _ hk h =>
          ih_tuple_struct _ _ hk h (to_alind h)
      | Cast_Header_Struct _ _ hk1 hk2 h =>
          ih_header_struct _ _ hk1 hk2 h (alind h)
      | Cast_Struct_Struct _ _ hk1 hk2 h =>
          ih_struct_struct _ _ hk1 hk2 h (alind h)
      | Cast_Tuple_Header _ _ hk h =>
          ih_tuple_header _ _ hk h (to_alind h)
      | Cast_Header_Header _ _ hk1 hk2 h =>
          ih_header_header _ _ hk1 hk2 h (alind h)
      | Cast_Struct_Header _ _ hk1 hk2 h =>
          ih_struct_header _ _ hk1 hk2 h (alind h)
      | Cast_Tuple_Tuple _ _ h =>
          ih_tuple_tuple _ _ h (lind h)
      end.
End Cast_Type_ind.

Ltac some_inv :=
  match goal with
  | H: Some _ = Some _ |- _ => inversion H; subst; clear H
  end.

Ltac match_some_inv :=
  match goal with
  | H: match ?trm with Some _ => _ | None => _ end = Some _
    |- _ => destruct trm as [? |] eqn:? ; cbn in *;
          try discriminate
  end.

Ltac if_destruct :=
  match goal with
  | H: context [if ?t then _ else _] |- _
    => destruct t eqn:?; cbn in *; try discriminate; try some_inv
  | |- context [if ?t then _ else _]
    => destruct t eqn:?; cbn in *; try discriminate; try some_inv
  end.

Section Lemmas.
  Context {tags_t : Type}.
  Notation typ := (@P4Type tags_t).

  Local Hint Constructors binary_type : core.
  Local Hint Constructors numeric_width : core.
  Local Hint Constructors numeric : core.
  Local Hint Constructors Eq_type : core.
  Local Hint Constructors predop : core.

  Lemma Eq_type_normᵗ : forall t : typ,
      Eq_type t -> Eq_type (normᵗ t).
  Proof.
    intros t H; induction H using my_Eq_type_ind;
      cbn in *; try (constructor; rewrite Forall_forall in *; eauto).
    - inversion H0; subst; cbn in *; auto.
    - intros.
      apply in_map_iff in H1.
      destruct H1, x0; intuition.
      subst.
      firstorder.
    - intros.
      apply in_map_iff in H1.
      destruct H1, x0; intuition.
      subst.
      firstorder.
    - intros.
      apply in_map_iff in H1.
      destruct H1, x0; intuition.
      subst.
      firstorder.
    - intros.
      apply in_map_iff in H1.
      destruct H1; intuition.
      subst.
      firstorder.
    - now constructor.
  Qed.

  Local Hint Resolve Eq_type_normᵗ : core.

  Lemma numeric_width_normᵗ : forall w (t : typ),
      numeric_width w t -> numeric_width w (normᵗ t).
  Proof.
    intros w t H; inv_numeric_width; auto.
  Qed.

  Local Hint Resolve numeric_width_normᵗ : core.
  
  Lemma numeric_normᵗ : forall t : typ,
      numeric t -> numeric (normᵗ t).
  Proof.
    intros t H; inv_numeric; auto.
  Qed.

  Local Hint Resolve numeric_normᵗ : core.
  
  Lemma binary_type_normᵗ : forall o (r r1 r2 : typ),
      binary_type o r1 r2 r -> binary_type o (normᵗ r1) (normᵗ r2) (normᵗ r).
  Proof.
    intros o r r1 r2 Hbt; inversion Hbt; subst; cbn; eauto.
  Qed.

  Lemma is_expr_typ_list_uninit_sval_of_typ :
    forall (ts : list (typ)) b,
      Forall is_expr_typ ts ->
      Forall
        (fun t => [] ⊢ok t -> exists v,
             uninit_sval_of_typ b t = Some v) ts ->
      Forall (fun τ : P4Type => [] ⊢ok τ) ts ->
      exists vs, sequence (map (uninit_sval_of_typ b) ts) = Some vs.
  Proof.
    intros ts b Hts IHts Hokts.
    rewrite Forall_forall in IHts, Hokts.
    pose proof reduce_inner_impl_forall
         _ _ _ _ IHts Hokts as H; cbn in H.
    rewrite <- Forall_forall, Forall_exists_factor in H.
    destruct H as [vs Hvs].
    pose proof ForallMap.Forall2_map_l
         _ _ _
         (fun ov v => ov = Some v)
         (uninit_sval_of_typ b) ts vs as H; cbn in H.
    rewrite H in Hvs; clear H.
    rewrite Forall2_sequence_iff in Hvs; eauto.
  Qed.

  Local Open Scope monad_scope.
  
  Lemma is_expr_typ_alist_uninit_sval_of_typ :
    forall (xts : list (P4String.t tags_t * (typ))) b,
      Forall (fun xt => is_expr_typ (snd xt)) xts ->
      Forall
        (fun xt =>
           [] ⊢ok snd xt ->
           exists v, uninit_sval_of_typ b (snd xt) = Some v)
        xts ->
      Forall (fun xt => [] ⊢ok snd xt) xts ->
      exists xvs,
        sequence
          (List.map
             (fun '({| P4String.str := x |}, t) =>
                uninit_sval_of_typ b t >>| pair x)
             xts)
        = Some xvs.
  Proof.
    intros xts b Hxts IHxts Hok.
    rewrite Forall_forall in IHxts, Hok.
    pose proof reduce_inner_impl_forall
         _ _ _ _ IHxts Hok as H; cbn in H.
    rewrite <- Forall_forall, Forall_exists_factor in H.
    destruct H as [vs Hvs].
    pose proof ForallMap.Forall2_map_l
         _ _ _
         (fun ov v => ov = Some v)
         (fun xt => uninit_sval_of_typ b (snd xt))
         xts vs as H; cbn in H.
    rewrite H in Hvs; clear H.
    rewrite <- List.map_map, Forall2_sequence_iff in Hvs.
    exists (combine (map P4String.str (map fst xts)) vs).
    assert (Hmap:
              List.map
                (fun '({| P4String.str := x |}, t) =>
                   uninit_sval_of_typ b t >>| pair x)
                xts =
              List.map
                (fun '(x, t) => uninit_sval_of_typ b t >>| pair x)
                (List.map (fun '(x,t) => (P4String.str x, t)) xts)).
    { clear Hvs IHxts Hxts Hok vs.
      induction xts as [| [[i x] t] xts IHxts];
        cbn in *; try rewrite IHxts; auto. }
    rewrite Hmap; clear Hmap.
    unfold ">>|", ">>=".
    unfold option_monad_inst,
    option_bind, mret in *.
    repeat rewrite map_pat_both.
    clear Hok Hxts IHxts.
    generalize dependent vs.
    induction xts as [| [[i x] t] xts IHxts];
      intros [| v vs] Hvs; cbn in *; auto.
    - destruct (uninit_sval_of_typ b t) as [v |] eqn:Hv;
        cbn in *; try discriminate.
      destruct (sequence (map (uninit_sval_of_typ b) (map snd xts)))
        as [vs |] eqn:Hvs'; cbn in *; inversion Hvs.
    - destruct (uninit_sval_of_typ b t) as [v' |] eqn:Hv';
        cbn in *; try discriminate.
      destruct (sequence (map (uninit_sval_of_typ b) (map snd xts)))
        as [vs' |] eqn:Hvs'; cbn in *; inversion Hvs; subst.
      rewrite IHxts with vs; auto.
  Qed.

  Ltac apply_ind :=
    match goal with
    | H: ?Q, IH: (?Q -> exists v, _)
      |- _ => apply IH in H as [? Hv];
            rewrite Hv; clear Hv IH;
            eauto; assumption
    end.

  Local Hint Extern 0 => apply_ind : core.
  
  Lemma is_expr_typ_uninit_sval_of_typ : forall (t : typ) b,
    is_expr_typ t -> [] ⊢ok t ->
    exists v, uninit_sval_of_typ b t = Some v.
  Proof.
    intros t b Ht Hok;
      induction Ht as
        [ (* bool *)
        | (* string *)
        | (* integer *)
        | w (* int *)
        | w (* bit *)
        | w (* varbit *)
        | t n Ht IHt (* array *)
        | ts Hts IHts (* tuple *)
        | ts Hts IHts (* list *)
        | xts Uxts Hxts IHxts (* record *)
        | (* error *)
        | xts Uxts Hxts IHxts (* header *)
        | xts Uxts Hxts IHxts (* union *)
        | xts Uxts Hxts IHxts (* struct *)
        | X ms Hms       (* enum *)
        | X t ms Ht IHt (* senum *)
        | X (* name *)
        | X t Ht IHt (* newtype *)
        ] using my_is_expr_typ_ind;
      inversion Hok; subst; cbn in *;
        unfold option_monad_inst, option_bind in *;
        try contradiction; eauto.
    - assert (H0n: (0 <? n)%N = true) by (rewrite N.ltb_lt; lia).
      rewrite H0n; eauto.
    - eapply is_expr_typ_list_uninit_sval_of_typ
        in Hts as [vs Hvs]; eauto.
      unfold option_monad_inst,
      option_bind in Hvs; rewrite Hvs; eauto.
    - eapply is_expr_typ_list_uninit_sval_of_typ
        in Hts as [vs Hvs]; eauto.
      unfold option_monad_inst,
      option_bind in Hvs; rewrite Hvs; eauto.
    - eapply is_expr_typ_alist_uninit_sval_of_typ
        in Hxts as [xvs Hxvs]; eauto.
      unfold ">>|",">>=",mret, option_monad_inst,
      option_bind in Hxvs; rewrite Hxvs; eauto.
    - eapply is_expr_typ_alist_uninit_sval_of_typ
        in Hxts as [xvs Hxvs]; eauto.
      unfold ">>|",">>=",mret, option_monad_inst,
      option_bind in Hxvs; rewrite Hxvs; eauto.
    - eapply is_expr_typ_alist_uninit_sval_of_typ
        in Hxts as [xvs Hxvs]; eauto.
      unfold ">>|",">>=",mret, option_monad_inst, 
      option_bind in Hxvs; rewrite Hxvs; eauto.
    - eapply is_expr_typ_alist_uninit_sval_of_typ
        in Hxts as [xvs Hxvs]; eauto.
      unfold ">>|",">>=",mret, option_monad_inst, 
      option_bind in Hxvs; rewrite Hxvs; eauto.
    - destruct X as [d X];
        destruct ms as [| [i M] ms];
        simpl in *; try lia; eauto.
    - destruct X as [d X].
      inversion H0;
      subst; cbn in *; eauto; try lia; eauto.
  Qed.

  Definition normᵗ_idem_def (t : typ) := normᵗ (normᵗ t) = normᵗ t.
  Definition normᶜ_idem_def (t : @ControlType tags_t) := normᶜ (normᶜ t) = normᶜ t.
  Definition normᶠ_idem_def (t : @FunctionType tags_t) := normᶠ (normᶠ t) = normᶠ t.
  Definition normᵖ_idem_def (t : @P4Parameter tags_t) := normᵖ (normᵖ t) = normᵖ t.
  
  Definition normᵗ_idem_ind :=
    my_P4Type_ind
      _ normᵗ_idem_def normᶜ_idem_def
      normᶠ_idem_def normᵖ_idem_def.

  Ltac list_idem :=
    intros ts Hts; f_equal;
    apply map_ext_Forall in Hts;
    rewrite map_map; auto; assumption.
  
  Ltac alist_idem :=
    intros xts Hxts; f_equal;
    pose proof Forall_map
         snd
         (fun t => normᵗ (normᵗ t) = normᵗ t) xts
      as H; unfold Basics.compose in H;
    rewrite <- H in Hxts; clear H;
    apply map_ext_Forall in Hxts;
    repeat rewrite map_pat_combine;
    repeat rewrite map_fst_combine;
    repeat rewrite map_snd_combine;
    repeat rewrite map_length; auto;
    repeat rewrite map_id; rewrite map_map;
    f_equal; auto; assumption.
    
  Lemma normᵗ_idem : forall t, normᵗ_idem_def t.
  Proof.
    apply normᵗ_idem_ind;
      unfold normᵗ_idem_def,normᶜ_idem_def,
      normᶠ_idem_def,normᵖ_idem_def; cbn in *;
        try (intros; f_equal; eauto; assumption);
        try list_idem; try alist_idem; eauto.
    - intros X [t |] ms H; inversion H; subst; cbn; do 2 f_equal; auto.
    - intros ds cs Hds Hcs.
      apply map_ext_Forall in Hds, Hcs.
      repeat rewrite map_map; f_equal; auto.
    - intros Xs ws ps H.
      apply map_ext_Forall in H.
      repeat rewrite map_map; f_equal; auto.
    - intros t ts Hts Ht.
      apply map_ext_Forall in Hts;
        rewrite map_map; f_equal; auto.
    - intros Xs ws ps t Hps Ht.
      apply map_ext_Forall in Hps;
        rewrite map_map; f_equal; auto.
    - intros Xs ps Hps;
        apply map_ext_Forall in Hps;
        rewrite map_map; f_equal; auto.
    - intros Xs ps k t Hps Ht;
        apply map_ext_Forall in Hps;
        rewrite map_map; f_equal; auto.
  Qed.

  Local Hint Constructors is_expr_typ : core.

  Ltac bruh :=
    match goal with
    | |- forall t, ?ty = normᵗ t -> is_expr_typ t
      => apply (my_P4Type_ind
                 tags_t (fun t => ty = normᵗ t -> is_expr_typ t)
                 (fun _ => True) (fun _ => True) (fun _ => True)); cbn;
        try discriminate; auto
    end.

  Local Hint Extern 2 => bruh : core.
  Local Hint Resolve in_map : core.

  Ltac bruh_list :=
    intros ts' IHts' Hts';
    injection Hts' as ?; subst;
    constructor;
    rewrite Forall_forall in *; eauto.

  Local Hint Extern 0 => bruh_list : core.
  
  Ltac bruh_alist :=
    match goal with
    | Uxts: AList.key_unique _ = true
      |- _ => intros xts' IHxts' Hxts';
            injection Hxts' as ?; subst;
            epose proof AListUtil.key_unique_map_values (K := P4String.t tags_t) as Hmv;
            unfold AListUtil.map_values in Hmv;
            rewrite Hmv in Uxts; clear Hmv;
            constructor; auto;
            rewrite Forall_forall in *;
            intros [x t] Hxt; cbn in *;
            match goal with
            | H: List.In _ ?l,
                 IH: context [List.In _ (map ?g ?l)]
              |- _ => apply in_map with (f := g) in H as Hinmap; eauto
            end
    end.

  Local Hint Extern 0 => bruh_alist : core.
  
  Lemma is_expr_typ_normᵗ_impl : forall t : typ,
      is_expr_typ (normᵗ t) -> is_expr_typ t.
  Proof.
    intros t Ht.
    remember (normᵗ t) as normᵗt eqn:Heqt.
    generalize dependent t.
    induction Ht as
        [ (* bool *)
        | (* string *)
        | (* integer *)
        | w (* int *)
        | w (* bit *)
        | w (* varbit *)
        | t n Ht IHt (* array *)
        | ts Hts IHts (* tuple *)
        | ts Hts IHts (* list *)
        | xts Uxts Hxts IHxts (* record *)
        | (* error *)
        | xts Uxts Hxts IHxts (* header *)
        | xts Uxts Hxts IHxts (* union *)
        | xts Uxts Hxts IHxts (* struct *)
        | X ms Hms       (* enum *)
        | X t ms Ht IHt (* senum *)
        | X (* name *)
        | X t Ht IHt (* newtype *)
        ] using my_is_expr_typ_ind; auto 3; bruh.
    - intros ty w IHty H; inv H; auto.
    - intros Y t' l IHt' Ht'.
      injection Ht' as ? ? ?; subst.
      destruct t' as [t |]; cbn in *; try discriminate; auto.
    - intros Y t' l IHt' Ht'.
      injection Ht' as ? ? ?; subst.
      inversion IHt'; subst;
        cbn in *; try discriminate; auto.
      some_inv; auto.
  Qed.

  Definition uninit_sval_of_typ_norm_def (t : typ) :=
    forall b, uninit_sval_of_typ b (normᵗ t) = uninit_sval_of_typ b t.

  Definition uninit_sval_of_typ_norm_ind :=
    my_P4Type_ind
      _ uninit_sval_of_typ_norm_def
      (fun _ => True) (fun _ => True) (fun _ => True).

  Ltac list_uninit_norm :=
    intros ts Hts b;
    rewrite Forall_forall in Hts;
    specialize Hts with (b:=b);
    rewrite <- Forall_forall in Hts;
    apply map_ext_Forall in Hts;
    do 2 f_equal; rewrite map_map; auto; assumption.

  Ltac alist_uninit_norm :=
    intros xts Hxts b;
    rewrite Forall_forall in Hxts;
    specialize Hxts with (b:=b);
    rewrite <- Forall_forall in Hxts;
    apply map_ext_Forall in Hxts;
    do 2 f_equal;
    rewrite <- map_map with
        (g := uninit_sval_of_typ b) (f := snd) in Hxts;
    rewrite <- map_map with
        (g := uninit_sval_of_typ b) (f := fun xt => normᵗ (snd xt)) in Hxts;
    rewrite <- map_map with
        (g := normᵗ) (f := snd) in Hxts;
    rewrite map_pat_combine, map_id;
    unfold option_bind;
    induction xts as [| [[i x] t] xts IHxts];
    simpl in *; inversion Hxts; subst; f_equal; auto; assumption.
  
  Lemma uninit_sval_of_typ_norm : forall t,
      uninit_sval_of_typ_norm_def t.
  Proof.
    apply uninit_sval_of_typ_norm_ind;
      unfold uninit_sval_of_typ_norm_def; cbn;
        try (intros; f_equal; auto; assumption);
        try list_uninit_norm; try alist_uninit_norm; auto.
    - intros t n IH b.
      destruct (0 <? n)%N eqn:H0n; f_equal; auto.
    - intros [iX X] [t |] [| [iM M] ms] H b;
        inversion H; subst; simpl in *; f_equal; eauto.
  Qed.

  Local Hint Constructors member_type : core.
  
  Lemma member_type_normᵗ : forall ts (t : typ),
      member_type ts t ->
      member_type (map (fun '(x,t) => (x,normᵗ t)) ts) (normᵗ t).
  Proof.
    intros ts t H; inversion H; subst; cbn; auto.
  Qed.

  Local Hint Constructors cast_type : core.

  Lemma cast_type_normᵗ_same : forall τ₁ τ₂ : typ,
      cast_type τ₁ τ₂ -> normᵗ τ₂ = τ₂.
  Proof.
    intros t1 t2 h;
      induction h using my_cast_type_ind;
      cbn; auto; f_equal.
    - apply Forall2_only_r_Forall in H1.
      rewrite <- Forall_map with
        (P:=fun t => normᵗ t = t) (f:=snd) in H1.
      apply map_ext_Forall in H1.
      rewrite map_id in H1.
      rewrite map_pat_combine,map_id.
      rewrite H1. apply combine_map_fst_snd.
    - unfold AList.all_values in *.
      rewrite Forall2_conj in *.
      rewrite Forall2_map_both with (f:=fst) in *.
      rewrite Forall2_map_both with (f:=snd) in H1.
      destruct H1 as [h_fst_xts_yts _].
      destruct H2 as [_ ih].
      apply Forall2_only_r_Forall in ih.
      rewrite <- Forall_map with
        (P:=fun t => normᵗ t = t) (f:=snd) in ih.
      apply map_ext_Forall in ih.
      rewrite map_id in ih.
      rewrite map_pat_combine,map_id.
      rewrite ih. apply combine_map_fst_snd.
    - unfold AList.all_values in *.
      rewrite Forall2_conj in *.
      rewrite Forall2_map_both with (f:=fst) in *.
      rewrite Forall2_map_both with (f:=snd) in H1.
      destruct H1 as [h_fst_xts_yts _].
      destruct H2 as [_ ih].
      apply Forall2_only_r_Forall in ih.
      rewrite <- Forall_map with
        (P:=fun t => normᵗ t = t) (f:=snd) in ih.
      apply map_ext_Forall in ih.
      rewrite map_id in ih.
      rewrite map_pat_combine,map_id.
      rewrite ih. apply combine_map_fst_snd.
    - apply Forall2_only_r_Forall in H1.
      rewrite <- Forall_map with
        (P:=fun t => normᵗ t = t) (f:=snd) in H1.
      apply map_ext_Forall in H1.
      rewrite map_id in H1.
      rewrite map_pat_combine,map_id.
      rewrite H1. apply combine_map_fst_snd.
    - unfold AList.all_values in *.
      rewrite Forall2_conj in *.
      rewrite Forall2_map_both with (f:=fst) in *.
      rewrite Forall2_map_both with (f:=snd) in H1.
      destruct H1 as [h_fst_xts_yts _].
      destruct H2 as [_ ih].
      apply Forall2_only_r_Forall in ih.
      rewrite <- Forall_map with
        (P:=fun t => normᵗ t = t) (f:=snd) in ih.
      apply map_ext_Forall in ih.
      rewrite map_id in ih.
      rewrite map_pat_combine,map_id.
      rewrite ih. apply combine_map_fst_snd.
    - unfold AList.all_values in *.
      rewrite Forall2_conj in *.
      rewrite Forall2_map_both with (f:=fst) in *.
      rewrite Forall2_map_both with (f:=snd) in H1.
      destruct H1 as [h_fst_xts_yts _].
      destruct H2 as [_ ih].
      apply Forall2_only_r_Forall in ih.
      rewrite <- Forall_map with
        (P:=fun t => normᵗ t = t) (f:=snd) in ih.
      apply map_ext_Forall in ih.
      rewrite map_id in ih.
      rewrite map_pat_combine,map_id.
      rewrite ih. apply combine_map_fst_snd.
    - apply Forall2_only_r_Forall in H0.
      apply map_ext_Forall in H0.
      rewrite map_id in H0; assumption.
  Qed.
  
  Lemma cast_type_normᵗ : forall τ₁ τ₂ : typ,
      cast_type τ₁ τ₂ -> cast_type (normᵗ τ₁) (normᵗ τ₂).
  Proof.
    intros t1 t2 h; induction h using my_cast_type_ind;
      cbn; auto.
    - constructor.
      + pose proof @AListUtil.key_unique_map_values as h.
        unfold AListUtil.map_values in h; rewrite h; assumption.
      + rewrite Forall2_map_r, map_snd_map.
        rewrite Forall2_map_r with
          (R:=fun x y => cast_type (normᵗ x) (normᵗ y))
          (f:=snd) in H1.
        rewrite Forall2_map_both in H1; assumption.
    - pose proof @AListUtil.key_unique_map_values as h.
      unfold AListUtil.map_values in h.
      constructor; try (rewrite h; assumption).
      clear h.
      unfold AList.all_values in *.
      rewrite Forall2_conj in *; clear H1.
      destruct H2 as [hfst hsnd].
      rewrite Forall2_map_both in hsnd.
      do 2 rewrite <- map_map with (f:=snd) in hsnd.
      rewrite Forall2_map_both in hfst.
      rewrite Forall2_map_both.
      rewrite Forall2_eq in *.
      do 2 rewrite map_fst_map,map_id; split; auto.
      rewrite Forall2_map_both.
      do 2 rewrite map_snd_map; assumption.
    - pose proof @AListUtil.key_unique_map_values as h.
      unfold AListUtil.map_values in h.
      constructor; try (rewrite h; assumption).
      clear h.
      unfold AList.all_values in *.
      rewrite Forall2_conj in *; clear H1.
      destruct H2 as [hfst hsnd].
      rewrite Forall2_map_both in hsnd.
      do 2 rewrite <- map_map with (f:=snd) in hsnd.
      rewrite Forall2_map_both in hfst.
      rewrite Forall2_map_both.
      rewrite Forall2_eq in *.
      do 2 rewrite map_fst_map,map_id; split; auto.
      rewrite Forall2_map_both.
      do 2 rewrite map_snd_map; assumption.
    - constructor.
      + pose proof @AListUtil.key_unique_map_values as h.
        unfold AListUtil.map_values in h; rewrite h; assumption.
      + rewrite Forall2_map_r, map_snd_map.
        rewrite Forall2_map_r with
          (R:=fun x y => cast_type (normᵗ x) (normᵗ y))
          (f:=snd) in H1.
        rewrite Forall2_map_both in H1; assumption.
    - pose proof @AListUtil.key_unique_map_values as h.
      unfold AListUtil.map_values in h.
      constructor; try (rewrite h; assumption).
      clear h.
      unfold AList.all_values in *.
      rewrite Forall2_conj in *; clear H1.
      destruct H2 as [hfst hsnd].
      rewrite Forall2_map_both in hsnd.
      do 2 rewrite <- map_map with (f:=snd) in hsnd.
      rewrite Forall2_map_both in hfst.
      rewrite Forall2_map_both.
      rewrite Forall2_eq in *.
      do 2 rewrite map_fst_map,map_id; split; auto.
      rewrite Forall2_map_both.
      do 2 rewrite map_snd_map; assumption.
    - pose proof @AListUtil.key_unique_map_values as h.
      unfold AListUtil.map_values in h.
      constructor; try (rewrite h; assumption).
      clear h.
      unfold AList.all_values in *.
      rewrite Forall2_conj in *; clear H1.
      destruct H2 as [hfst hsnd].
      rewrite Forall2_map_both in hsnd.
      do 2 rewrite <- map_map with (f:=snd) in hsnd.
      rewrite Forall2_map_both in hfst.
      rewrite Forall2_map_both.
      rewrite Forall2_eq in *.
      do 2 rewrite map_fst_map,map_id; split; auto.
      rewrite Forall2_map_both.
      do 2 rewrite map_snd_map; assumption.
    - constructor. rewrite <- Forall2_map_both; assumption.
  Qed.
End Lemmas.
