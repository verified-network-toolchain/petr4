From Coq Require Export NArith.BinNat Strings.String Lists.List.
Require Export Poulet4.Typed Poulet4.Syntax.
Export ListNotations.
Require Poulet4.P4String Poulet4.P4cub.Util.EquivUtil.

Notation predopt    := (EquivUtil.predop).
Notation remove_str := (remove string_dec).
Notation remove_all := (fold_right remove_str).

Section Utils.
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
  
  (** Evidence a binary operation is valid for given types. *)
  Variant binary_type : OpBin -> typ -> typ -> typ -> Prop :=
  | BTPlusPlusBit w1 w2 t2 :
      numeric_width w2 t2 ->
      binary_type PlusPlus (TypBit w1) t2 (TypBit (w1 + w2)%N)
  | BTPlusPlusInt w1 w2 t2 :
      numeric_width w2 t2 ->
      binary_type PlusPlus (TypInt w1) t2 (TypInt (w1 + w2)%N)
  | BTShl w1 t1 t2 :
      numeric_width w1 t1 -> numeric t2 ->
      binary_type Shl t1 t2 t1
  | BTShrBit w1 w2 t1 :
      numeric_width w1 t1 ->
      binary_type Shr t1 (TypBit w2) t1
  | BTShlInteger w1 t1 :
      numeric_width w1 t1 ->
      binary_type Shr t1 TypInteger t1
  | BTShrInteger w1 t1 :
      numeric_width w1 t1 ->
      binary_type Shr t1 TypInteger t1
  | BTEq t :
      binary_type Eq t t TypBool
  | BTNotEq t :
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
  | BTDiv t :
      numeric t ->
      binary_type Div t t t
  | BTMod t :
      numeric t ->
      binary_type Mod t t t
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
  
  Inductive cast_type : typ -> typ -> Prop :=
  | CTBool w :
      cast_type (TypBit w) TypBool
  | CTBit t w :
      match t with
      | TypBool
      | TypBit _
      | TypInt _
      | TypInteger
      | TypEnum _ (Some (TypBit _)) _ => True
      | _ => False
      end ->
      cast_type t (TypBit w)
  | CTInt t w :
      match t with
      | TypBool
      | TypBit _
      | TypInt _
      | TypInteger
      | TypEnum _ (Some (TypInt _)) _ => True
      | _ => False
      end ->
      cast_type t (TypInt w)
  | CTEnum t1 t2 enum fields :
      match t1, t2 with
      | TypBit _, TypBit _
      | TypInt _, TypInt _
      | TypEnum _ (Some (TypBit _)) _, TypBit _
      | TypEnum _ (Some (TypInt _)) _, TypInt _ => True
      | _, _ => False
      end ->
      cast_type t1 (TypEnum enum (Some t2) fields)
  | CTNewType x t t' :
      cast_type t t' ->
      cast_type t (TypNewType x t')
  | CTStructOfTuple ts xts :
      Forall2 (fun t xt => cast_type t (snd xt)) ts xts ->
      cast_type (TypTuple ts) (TypStruct xts)
  | CTStructOfRecord xts xts' :
      AList.all_values cast_type xts xts' ->
      cast_type (TypRecord xts) (TypStruct xts')
  | CTHeaderOfTuple ts xts :
      Forall2 (fun t xt => cast_type t (snd xt)) ts xts ->
      cast_type (TypTuple ts) (TypHeader xts)
  | CTHeaderOfRecord xts xts' :
      AList.all_values cast_type xts xts' ->
      cast_type (TypRecord xts) (TypHeader xts')
  | CTTuple ts ts' :
      Forall2 cast_type ts ts' ->
      cast_type (TypTuple ts) (TypTuple ts').
  
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
  
  Inductive lexpr_ok : expr -> Prop :=
  | lexpr_name tag x loc t dir :
      lexpr_ok (MkExpression tag (ExpName x loc) t dir)
  | lexpr_member tag e x t dir :
      lexpr_ok e ->
      lexpr_ok (MkExpression tag (ExpExpressionMember e x) t dir)
  | lexpr_slice tag e hi lo t dir :
      lexpr_ok e ->
      lexpr_ok (MkExpression tag (ExpBitStringAccess e lo hi) t dir)
  | lexpr_access tag e₁ e₂ t dir :
      lexpr_ok e₁ ->
      lexpr_ok (MkExpression tag (ExpArrayAccess e₁ e₂) t dir).
End Utils.

Ltac inv_numeric_width :=
  match goal with
  | H: numeric_width _ _ |- _ => inversion H; subst
  end.

Ltac inv_numeric :=
  match goal with
  | H: numeric _ |- _ => inversion H; subst; try inv_numeric_width
  end.

Reserved Notation "Δ '⊢ok' τ" (at level 80, no associativity).

Inductive
  P4Type_ok
  {tags_t : Type} (Δ : list string) : @P4Type tags_t -> Prop :=
| bool_ok :
    Δ ⊢ok TypBool
| integer_ok :
    Δ ⊢ok TypInteger
| int_ok w :
    Δ ⊢ok TypInt w
| bit_ok w :
    Δ ⊢ok TypBit w
| varbit_ok w :
    Δ ⊢ok TypVarBit w
| array_ok τ n :
    Δ ⊢ok τ ->
    Δ ⊢ok TypArray τ n
| tuple_ok τs :
    Forall (fun τ => Δ ⊢ok τ) τs ->
    Δ ⊢ok TypTuple τs
| list_ok τs :
    Forall (fun τ => Δ ⊢ok τ) τs ->
    Δ ⊢ok TypList τs
| record_ok τs :
    Forall (fun xτ => Δ ⊢ok snd xτ) τs ->
    Δ ⊢ok TypRecord τs
| set_ok τ :
    Δ ⊢ok τ ->
    Δ ⊢ok TypSet τ
| error_ok :
    Δ ⊢ok TypError
| matchkind_ok :
    Δ ⊢ok TypMatchKind
| void_ok :
    Δ ⊢ok TypVoid
| header_ok τs :
    Forall (fun xτ => Δ ⊢ok snd xτ) τs ->
    Δ ⊢ok TypHeader τs
| union_ok τs :
    Forall (fun xτ => Δ ⊢ok snd xτ) τs ->
    Δ ⊢ok TypHeaderUnion τs
| struct_ok τs :
    Forall (fun xτ => Δ ⊢ok snd xτ) τs ->
    Δ ⊢ok TypStruct τs
| enum_ok X τ mems :
    predopt (fun τ => remove_str (P4String.str X) Δ ⊢ok τ) τ ->
    Δ ⊢ok TypEnum X τ mems
| typeName_ok X :
    List.In (P4String.str X) Δ ->
    Δ ⊢ok TypTypeName X
| newType_ok X τ :
    remove_str (P4String.str X) Δ ⊢ok τ ->
    Δ ⊢ok TypNewType X τ
| control_ok ct :
    ControlType_ok Δ ct ->
    Δ ⊢ok TypControl ct
| parser_ok pt :
    ControlType_ok Δ pt ->
    Δ ⊢ok TypParser pt
(* TODO: How should externs be handled? *)
| extern_ok X :
    Δ ⊢ok TypExtern X
(* TODO: how to handle wildcard params? *)
| package_ok Xs Ys params :
    Forall
      (fun p =>
         P4Parameter_ok
           (remove_all (map P4String.str Xs) Δ) p)
      params ->
    Δ ⊢ok TypPackage Xs Ys params
| specialized_ok τ τs :
    Forall (fun τ => Δ ⊢ok τ) τs ->
    Δ ⊢ok τ ->
    Δ ⊢ok TypSpecializedType τ τs
| constructor_ok Xs Ys params τ :
    Forall
      (fun p =>
         P4Parameter_ok (remove_all (map P4String.str Xs) Δ) p)
      params ->
    remove_all (map P4String.str Xs) Δ ⊢ok τ ->
    Δ ⊢ok TypConstructor Xs Ys params τ
where "Δ '⊢ok' τ" := (P4Type_ok Δ τ) : type_scope
with ControlType_ok {tags_t : Type} (Δ : list string) : ControlType -> Prop :=
| controlType_ok Xs params :
    Forall
      (fun p =>
         P4Parameter_ok
           (remove_all (map P4String.str Xs) Δ) p)
      params ->
    ControlType_ok Δ (MkControlType Xs params)
with FunctionType_ok {tags_t : Type} (Δ : list string) : FunctionType -> Prop :=
| functionType_ok Xs params k τ :
    Forall
      (fun p =>
         P4Parameter_ok (remove_all (map P4String.str Xs) Δ) p)
      params ->
    remove_all (map P4String.str Xs) Δ ⊢ok τ ->
    FunctionType_ok Δ (MkFunctionType Xs params k τ)
with P4Parameter_ok {tags_t : Type} (Δ : list string) : P4Parameter -> Prop :=
| parameter_ok b d τ n x :
    Δ ⊢ok τ ->
    P4Parameter_ok Δ (MkParameter b d τ n x).
