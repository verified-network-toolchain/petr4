From Coq Require Export NArith.BinNat Strings.String Lists.List micromega.Lia.
Require Export Poulet4.Typed Poulet4.Syntax Poulet4.ValueUtil.
Export ListNotations.
Require Poulet4.P4String Poulet4.P4cub.Util.EquivUtil.
Require Import Poulet4.Monads.Monad Poulet4.Monads.Option.

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

  (** Types of p4light expressions.
      Correlates to [uninit_sval_of_typ]. *)
  Inductive is_expr_typ : typ -> Prop :=
  | is_bool :
      is_expr_typ TypBool
  | is_string :
      is_expr_typ TypString
  | is_integer :
      is_expr_typ TypInteger
  | is_int w :
      is_expr_typ (TypInt w)
  | is_bit w :
      is_expr_typ (TypBit w)
  | is_varbit w :
      is_expr_typ (TypVarBit w)
  | is_array t n :
      is_expr_typ t ->
      is_expr_typ (TypArray t n)
  | is_tuple ts :
      Forall is_expr_typ ts ->
      is_expr_typ (TypTuple ts)
  | is_list ts :
      Forall is_expr_typ ts ->
      is_expr_typ (TypList ts)
  | is_record ts :
      Forall (fun t => is_expr_typ (snd t)) ts ->
      is_expr_typ (TypRecord ts)
  | is_error :
      is_expr_typ TypError
  | is_header ts :
      Forall (fun t => is_expr_typ (snd t)) ts ->
      is_expr_typ (TypHeader ts)
  | is_union ts :
      Forall (fun t => is_expr_typ (snd t)) ts ->
      is_expr_typ (TypHeaderUnion ts)
  | is_struct ts :
      Forall (fun t => is_expr_typ (snd t)) ts ->
      is_expr_typ (TypStruct ts)
  | is_enum X t mems :
      length mems > 0 ->
      predopt is_expr_typ t ->
      is_expr_typ (TypEnum X t mems)
  | is_name X :
      is_expr_typ (TypTypeName X)
  | is_newtype X t :
      is_expr_typ t ->
      is_expr_typ (TypNewType X t).
End Utils.

Section IsExprTypInd.
  Variables (tags_t : Type) (P : @P4Type tags_t -> Prop).
  
  Hypothesis HBool : P TypBool.
  Hypothesis HString : P TypString.
  Hypothesis HInteger : P TypInteger.
  Hypothesis HInt : forall w, P (TypInt w).
  Hypothesis HBit : forall w, P (TypBit w).
  Hypothesis HVarbit : forall w, P (TypVarBit w).
  Hypothesis HArray : forall t n,
      is_expr_typ t -> P t -> P (TypArray t n).
  Hypothesis HTuple : forall ts,
      Forall is_expr_typ ts ->
      Forall P ts ->
      P (TypTuple ts).
  Hypothesis HList : forall ts,
      Forall is_expr_typ ts ->
      Forall P ts ->
      P (TypList ts).
  Hypothesis HRecord : forall ts,
      Forall (fun t => is_expr_typ (snd t)) ts ->
      Forall (fun t => P (snd t)) ts ->
      P (TypRecord ts).
  Hypothesis HError : P TypError.
  Hypothesis HHeader : forall ts,
      Forall (fun t => is_expr_typ (snd t)) ts ->
      Forall (fun t => P (snd t)) ts ->
      P (TypHeader ts).
  Hypothesis HUnion : forall ts,
      Forall (fun t => is_expr_typ (snd t)) ts ->
      Forall (fun t => P (snd t)) ts ->
      P (TypHeaderUnion ts).
  Hypothesis HStruct : forall ts,
      Forall (fun t => is_expr_typ (snd t)) ts ->
      Forall (fun t => P (snd t)) ts ->
      P (TypStruct ts).
  Hypothesis HEnum : forall X t mems,
      length mems > 0 ->
      predopt is_expr_typ t ->
      predopt P t ->
      P (TypEnum X t mems).
  Hypothesis HName : forall X, P (TypTypeName X).
  Hypothesis HNewType : forall X t,
      is_expr_typ t -> P t -> P (TypNewType X t).

  Definition my_is_expr_typ_ind
    : forall (t : P4Type), is_expr_typ t -> P t :=
    fix I t H :=
      let fix L {ts} (H : Forall is_expr_typ ts)
          : Forall P ts :=
          match H with
          | Forall_nil _ => Forall_nil _
          | Forall_cons _ Hh Ht
            => Forall_cons _ (I _ Hh) (L Ht)
          end in
      let fix AL
              {ts : list (P4String.t tags_t * P4Type)}
              (H : Forall (fun t => is_expr_typ (snd t)) ts)
          : Forall (fun t => P (snd t)) ts :=
          match H with
          | Forall_nil _ => Forall_nil _
          | Forall_cons _ Hh Hts
            => Forall_cons _ (I _ Hh) (AL Hts)
          end in
      let PO
            {ot : option P4Type}
            (H : predopt is_expr_typ ot)
          : predopt P ot :=
          match H with
          | EquivUtil.predop_none _ => EquivUtil.predop_none _
          | EquivUtil.predop_some _ _ H
            => EquivUtil.predop_some _ _ (I _ H)
          end in
      match H with
      | is_bool          => HBool
      | is_string        => HString
      | is_integer       => HInteger
      | is_int w         => HInt w
      | is_bit w         => HBit w
      | is_varbit w      => HVarbit w
      | is_array _ n H   => HArray _ n H (I _ H)
      | is_tuple _ H     => HTuple _ H (L H)
      | is_list  _ H     => HList _ H (L H)
      | is_record _ H    => HRecord _ H (AL H)
      | is_error         => HError
      | is_header _ H    => HHeader _ H (AL H)
      | is_union  _ H    => HUnion  _ H (AL H)
      | is_struct _ H    => HStruct _ H (AL H)
      | is_name X        => HName X
      | is_newtype X _ H => HNewType X _ H (I _ H)
      | is_enum X _ _ Hm H  => HEnum X _ _ Hm H (PO H)
      end.
End IsExprTypInd.

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
    List.In (P4String.str X) Δ ->
    Δ ⊢ok TypExtern X
| function_ok ft :
    FunctionType_ok Δ ft ->
    Δ ⊢ok TypFunction ft
| action_ok ds cs :
    Forall (P4Parameter_ok Δ) ds ->
    Forall (P4Parameter_ok Δ) cs ->
    Δ ⊢ok TypAction ds cs
| table_ok X :
    List.In (P4String.str X) Δ ->
    Δ ⊢ok TypTable X
(* TODO: how to handle wildcard params? *)
| package_ok Xs Ys params :
    Forall
      (P4Parameter_ok
         (remove_all Δ (map P4String.str Xs)))
      params ->
    Δ ⊢ok TypPackage Xs Ys params
| specialized_ok τ τs :
    Forall (fun τ => Δ ⊢ok τ) τs ->
    Δ ⊢ok τ ->
    Δ ⊢ok TypSpecializedType τ τs
| constructor_ok Xs Ys params τ :
    Forall
      (P4Parameter_ok (remove_all Δ (map P4String.str Xs)))
      params ->
    remove_all Δ (map P4String.str Xs) ⊢ok τ ->
    Δ ⊢ok TypConstructor Xs Ys params τ
where "Δ '⊢ok' τ" := (P4Type_ok Δ τ) : type_scope
with ControlType_ok {tags_t : Type} (Δ : list string) : ControlType -> Prop :=
| controlType_ok Xs params :
    Forall
      (P4Parameter_ok
         (remove_all Δ (map P4String.str Xs)))
      params ->
    ControlType_ok Δ (MkControlType Xs params)
with FunctionType_ok {tags_t : Type} (Δ : list string) : FunctionType -> Prop :=
| functionType_ok Xs params k τ :
    Forall
      (P4Parameter_ok (remove_all Δ (map P4String.str Xs)))
      params ->
    remove_all Δ (map P4String.str Xs) ⊢ok τ ->
    FunctionType_ok Δ (MkFunctionType Xs params k τ)
with P4Parameter_ok {tags_t : Type} (Δ : list string) : P4Parameter -> Prop :=
| parameter_ok b d τ n x :
    Δ ⊢ok τ ->
    P4Parameter_ok Δ (MkParameter b d τ n x).

Section OkBoomerInd.
  Variables
    (tags_t : Type)
    (P : list string -> @P4Type tags_t -> Prop)
    (Q : list string -> @ControlType tags_t -> Prop)
    (R : list string -> @FunctionType tags_t -> Prop)
    (S : list string -> @P4Parameter tags_t -> Prop).

  Hypothesis HBool : forall Δ, P Δ TypBool.

  Hypothesis HInteger : forall Δ, P Δ TypInteger.

  Hypothesis HInt : forall Δ w, P Δ (TypInt w).

  Hypothesis HBit : forall Δ w, P Δ (TypBit w).

  Hypothesis HVarbit : forall Δ w, P Δ (TypVarBit w).

  Hypothesis HArray : forall Δ t n,
      Δ ⊢ok t -> P Δ t -> P Δ (TypArray t n).

  Hypothesis HTuple : forall Δ ts,
      Forall (fun t => Δ ⊢ok t) ts ->
      Forall (P Δ) ts ->
      P Δ (TypTuple ts).
  
  Hypothesis HList : forall Δ ts,
      Forall (fun t => Δ ⊢ok t) ts ->
      Forall (P Δ) ts ->
      P Δ (TypList ts).

  Hypothesis HRecord : forall Δ ts,
      Forall (fun t => Δ ⊢ok snd t) ts ->
      Forall (fun t => P Δ (snd t)) ts ->
      P Δ (TypRecord ts).

  Hypothesis HSet : forall Δ t,
      Δ ⊢ok t -> P Δ t -> P Δ (TypSet t).

  Hypothesis HError : forall Δ, P Δ TypError.

  Hypothesis HMatchKind : forall Δ, P Δ TypMatchKind.

  Hypothesis HVoid : forall Δ, P Δ TypVoid.

  Hypothesis HHeader : forall Δ ts,
      Forall (fun t => Δ ⊢ok snd t) ts ->
      Forall (fun t => P Δ (snd t)) ts ->
      P Δ (TypHeader ts).

  Hypothesis HUnion : forall Δ ts,
      Forall (fun t => Δ ⊢ok snd t) ts ->
      Forall (fun t => P Δ (snd t)) ts ->
      P Δ (TypHeaderUnion ts).

  Hypothesis HStruct : forall Δ ts,
      Forall (fun t => Δ ⊢ok snd t) ts ->
      Forall (fun t => P Δ (snd t)) ts ->
      P Δ (TypStruct ts).

  Hypothesis HEnum : forall Δ X t mems,
      predopt (fun τ => remove_str (P4String.str X) Δ ⊢ok τ) t ->
      predopt (P (remove_str (P4String.str X) Δ)) t ->
      P Δ (TypEnum X t mems).

  Hypothesis HName : forall Δ X,
      List.In (P4String.str X) Δ ->
      P Δ (TypTypeName X).

  Hypothesis HNewType : forall Δ X τ,
      remove_str (P4String.str X) Δ ⊢ok τ ->
      P (remove_str (P4String.str X) Δ) τ ->
      P Δ (TypNewType X τ).

  Hypothesis HControl : forall Δ ct,
      ControlType_ok Δ ct -> Q Δ ct -> P Δ (TypControl ct).

  Hypothesis HParser : forall Δ pt,
      ControlType_ok Δ pt -> Q Δ pt -> P Δ (TypParser pt).

  Hypothesis HExtern : forall Δ X,
      List.In (P4String.str X) Δ -> P Δ (TypExtern X).

  Hypothesis HFunction : forall Δ ft,
    FunctionType_ok Δ ft -> R Δ ft -> P Δ (TypFunction ft).

  Hypothesis HAction : forall Δ ds cs,
      Forall (P4Parameter_ok Δ) ds ->
      Forall (S Δ) ds ->
      Forall (P4Parameter_ok Δ) cs ->
      Forall (S Δ) cs ->
      P Δ (TypAction ds cs).

  Hypothesis HTable : forall Δ X,
      List.In (P4String.str X) Δ -> P Δ (TypTable X).
  
  Hypothesis HPackage : forall Δ Xs Ys params,
      Forall
        (P4Parameter_ok
           (remove_all Δ (map P4String.str Xs)))
        params ->
      Forall
        (S (remove_all Δ (map P4String.str Xs)))
        params ->
      P Δ (TypPackage Xs Ys params).

  Hypothesis HSpecialized : forall Δ τ τs,
      Forall (fun τ => Δ ⊢ok τ) τs ->
      Forall (P Δ) τs ->
      Δ ⊢ok τ -> P Δ τ ->
      P Δ (TypSpecializedType τ τs).

  Hypothesis HConstructor : forall Δ Xs Ys params τ,
      Forall
        (P4Parameter_ok (remove_all Δ (map P4String.str Xs)))
        params ->
      Forall (S (remove_all Δ (map P4String.str Xs)))
        params ->
      remove_all Δ (map P4String.str Xs) ⊢ok τ ->
      P (remove_all Δ (map P4String.str Xs)) τ ->
      P Δ (TypConstructor Xs Ys params τ).
  
  Hypothesis HControlType : forall Δ Xs params,
      Forall
        (P4Parameter_ok
           (remove_all Δ (map P4String.str Xs)))
        params ->
      Forall
        (S (remove_all Δ (map P4String.str Xs)))
        params ->
      Q Δ (MkControlType Xs params).
  
  Hypothesis HFunctionType : forall Δ Xs params k τ,
      Forall
        (P4Parameter_ok (remove_all Δ (map P4String.str Xs)))
        params ->
      Forall
        (S (remove_all Δ (map P4String.str Xs)))
        params ->
      remove_all Δ (map P4String.str Xs) ⊢ok τ ->
      P (remove_all Δ (map P4String.str Xs)) τ ->
      R Δ (MkFunctionType Xs params k τ).
  
  Hypothesis HP4Parameter : forall Δ b d τ n x,
      Δ ⊢ok τ -> P Δ τ ->
      S Δ (MkParameter b d τ n x).

  (** Custom induction principles for the [_ok] rules. *)
  Fixpoint
    my_P4Type_ok_ind
    Δ t (H : Δ ⊢ok t) {struct H} : P Δ t :=
    let fix my_P4Type_list_ok
            {Δ} {ts} (H : Forall (fun t => Δ ⊢ok t) ts) {struct H}
        : Forall (P Δ) ts :=
        match H with
        | Forall_nil _ => Forall_nil _
        | Forall_cons _ Hh Ht
          => Forall_cons
              _ (my_P4Type_ok_ind _ _ Hh)
              (my_P4Type_list_ok Ht)
        end in
    let fix my_P4Type_alist_ok
            {Δ} {ts} (H : Forall (fun t => Δ ⊢ok snd t) ts) {struct H}
        : Forall (fun t => P Δ (snd t)) ts :=
        match H with
        | Forall_nil _ => Forall_nil _
        | Forall_cons _ Hh Ht
          => Forall_cons
              _ (my_P4Type_ok_ind _ _ Hh)
              (my_P4Type_alist_ok Ht)
        end in
    let my_P4Type_predopt_ok
          {Δ} {t} (H: predopt (fun τ => Δ ⊢ok τ) t)
        : predopt (P Δ) t :=
        match H with
        | EquivUtil.predop_none _ => EquivUtil.predop_none _
        | EquivUtil.predop_some _ _ H
          => EquivUtil.predop_some _ _ (my_P4Type_ok_ind _ _ H)
        end in
    let fix my_P4Parameter_list_ok
            {Δ} {ps}
            (H : Forall (P4Parameter_ok Δ) ps)
        : Forall (S Δ) ps :=
        match H with
        | Forall_nil _ => Forall_nil _
        | Forall_cons _ Hh Ht
          => Forall_cons
              _ (my_P4Parameter_ok_ind _ _ Hh)
              (my_P4Parameter_list_ok Ht)
        end in
    match H with
    | bool_ok _ => HBool _
    | integer_ok _ => HInteger _
    | int_ok _ w => HInt _ w
    | bit_ok _ w => HBit _ w
    | varbit_ok _ w => HVarbit _ w
    | array_ok _ _ n H => HArray _ _ n H (my_P4Type_ok_ind _ _ H)
    | tuple_ok _ _ H => HTuple _ _ H (my_P4Type_list_ok H)
    | list_ok _ _ H => HList _ _ H (my_P4Type_list_ok H)
    | record_ok _ _ H => HRecord _ _ H (my_P4Type_alist_ok H)
    | set_ok _ _ H => HSet _ _ H (my_P4Type_ok_ind _ _ H)
    | error_ok _ => HError _
    | matchkind_ok _ => HMatchKind _
    | void_ok _ => HVoid _
    | header_ok _ _ H => HHeader _ _ H (my_P4Type_alist_ok H)
    | union_ok _ _ H => HUnion _ _ H (my_P4Type_alist_ok H)
    | struct_ok _ _ H => HStruct _ _ H (my_P4Type_alist_ok H)
    | enum_ok _ X _ mems H => HEnum _ X _ mems H (my_P4Type_predopt_ok H)
    | typeName_ok _ _ H => HName _ _ H
    | newType_ok _ _ _ H => HNewType _ _ _ H (my_P4Type_ok_ind _ _ H)
    | control_ok _ _ H => HControl _ _ H (my_ControlType_ok_ind _ _ H)
    | parser_ok _ _ H => HParser _ _ H (my_ControlType_ok_ind _ _ H)
    | extern_ok _ _ H => HExtern _ _ H
    | function_ok _ _ H
      => HFunction _ _ H (my_FunctionType_ok_ind _ _ H)
    | action_ok _ _ _ Hds Hcs
      => HAction
          _ _ _
          Hds (my_P4Parameter_list_ok Hds)
          Hcs (my_P4Parameter_list_ok Hcs)
    | table_ok _ _ H => HTable _ _ H
    | package_ok _ _ _ _ H => HPackage _ _ _ _ H (my_P4Parameter_list_ok H)
    | specialized_ok _ _ _ Hts Ht
      => HSpecialized
          _ _ _
          Hts (my_P4Type_list_ok Hts)
          Ht (my_P4Type_ok_ind _ _ Ht)
    | constructor_ok _ _ _ _ _ Hps Ht
      => HConstructor
          _ _ _ _ _
          Hps (my_P4Parameter_list_ok Hps)
          Ht (my_P4Type_ok_ind _ _ Ht)
    end
  with my_ControlType_ok_ind
         Δ ct (H : ControlType_ok Δ ct) : Q Δ ct :=
         let fix my_P4Parameter_list_ok
                 {Δ} {ps}
                 (H : Forall (P4Parameter_ok Δ) ps)
             : Forall (S Δ) ps :=
             match H with
             | Forall_nil _ => Forall_nil _
             | Forall_cons _ Hh Ht
               => Forall_cons
                   _ (my_P4Parameter_ok_ind _ _ Hh)
                   (my_P4Parameter_list_ok Ht)
             end in
         match H with
         | controlType_ok _ _ _ Hps
           => HControlType _ _ _ Hps (my_P4Parameter_list_ok Hps)
         end
  with my_FunctionType_ok_ind
         Δ ft (H : FunctionType_ok Δ ft) : R Δ ft :=
         let fix my_P4Parameter_list_ok
                 {Δ} {ps}
                 (H : Forall (P4Parameter_ok Δ) ps)
             : Forall (S Δ) ps :=
             match H with
             | Forall_nil _ => Forall_nil _
             | Forall_cons _ Hh Ht
               => Forall_cons
                   _ (my_P4Parameter_ok_ind _ _ Hh)
                   (my_P4Parameter_list_ok Ht)
             end in
         match H with
         | functionType_ok _ _ _ k _ Hps Hrt
           => HFunctionType
               _ _ _ k _
               Hps (my_P4Parameter_list_ok Hps)
               Hrt (my_P4Type_ok_ind _ _ Hrt)
         end
  with my_P4Parameter_ok_ind
         Δ p (H : P4Parameter_ok Δ p) : S Δ p :=
         match H with
         | parameter_ok _ b d _ n x H
           => HP4Parameter _ b d _ n x H (my_P4Type_ok_ind _ _ H)
         end.
End OkBoomerInd.

Section Lemmas.
  Context {tags_t : Type} {dummy : Sublist.Inhabitant tags_t}.

  Lemma is_expr_typ_list_uninit_sval_of_typ :
    forall (ts : list (@P4Type tags_t)) b,
      Forall is_expr_typ ts ->
      Forall
        (fun t => [] ⊢ok t -> exists v,
             uninit_sval_of_typ b t = Some v) ts ->
      Forall (fun τ : P4Type => [] ⊢ok τ) ts ->
      exists vs, sequence (map (uninit_sval_of_typ b) ts) = Some vs.
  Proof.
    intros ts b Hts IHts Hokts.
    rewrite Forall_forall in IHts, Hokts.
    pose proof Utils.reduce_inner_impl_forall
         _ _ _ _ IHts Hokts as H; cbn in H.
    rewrite <- Forall_forall, Utils.Forall_exists_factor in H.
    destruct H as [vs Hvs].
    pose proof Utils.Forall2_map_l
         _ _ _
         (fun ov v => ov = Some v)
         (uninit_sval_of_typ b) ts vs as H; cbn in H.
    rewrite H in Hvs; clear H.
    rewrite Forall2_sequence_iff in Hvs; eauto.
  Qed.

  Local Open Scope monad_scope.
  
  Lemma is_expr_typ_alist_uninit_sval_of_typ :
    forall (xts : list (P4String.t tags_t * (@P4Type tags_t))) b,
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
    pose proof Utils.reduce_inner_impl_forall
         _ _ _ _ IHxts Hok as H; cbn in H.
    rewrite <- Forall_forall, Utils.Forall_exists_factor in H.
    destruct H as [vs Hvs].
    pose proof Utils.Forall2_map_l
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
    unfold option_monad_inst, option_monad,
    option_bind, option_ret, mret in *.
    repeat rewrite Utils.map_pat_both.
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
  
  Lemma is_expr_typ_uninit_sval_of_typ : forall (t : @P4Type tags_t) b,
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
        | xts Hxts IHxts (* record *)
        | (* error *)
        | xts Hxts IHxts (* header *)
        | xts Hxts IHxts (* union *)
        | xts Hxts IHxts (* struct *)
        | X t ms Hms Ht IHt (* enum *)
        | X (* name *)
        | X t Ht IHt (* newtype *)
        ] using my_is_expr_typ_ind;
      inversion Hok; subst; cbn in *;
        unfold option_monad_inst, option_monad,
        option_bind, option_ret in *;
        try contradiction; eauto.
    - eapply is_expr_typ_list_uninit_sval_of_typ in Hts as [vs Hvs]; eauto.
      unfold option_monad_inst, option_monad,
      option_bind, option_ret in Hvs; rewrite Hvs; eauto.
    - eapply is_expr_typ_list_uninit_sval_of_typ in Hts as [vs Hvs]; eauto.
      unfold option_monad_inst, option_monad,
      option_bind, option_ret in Hvs; rewrite Hvs; eauto.
    - eapply is_expr_typ_alist_uninit_sval_of_typ in Hxts as [xvs Hxvs]; eauto.
      unfold ">>|",">>=",mret, option_monad_inst, option_monad,
      option_bind, option_ret in Hxvs; rewrite Hxvs; eauto.
    - eapply is_expr_typ_alist_uninit_sval_of_typ in Hxts as [xvs Hxvs]; eauto.
      unfold ">>|",">>=",mret, option_monad_inst, option_monad,
      option_bind, option_ret in Hxvs; rewrite Hxvs; eauto.
    - eapply is_expr_typ_alist_uninit_sval_of_typ in Hxts as [xvs Hxvs]; eauto.
      unfold ">>|",">>=",mret, option_monad_inst, option_monad,
      option_bind, option_ret in Hxvs; rewrite Hxvs; eauto.
    - eapply is_expr_typ_alist_uninit_sval_of_typ in Hxts as [xvs Hxvs]; eauto.
      unfold ">>|",">>=",mret, option_monad_inst, option_monad,
      option_bind, option_ret in Hxvs; rewrite Hxvs; eauto.
    - destruct t as [t |];
        inversion Ht; inversion IHt; inversion H0; subst; cbn in *; eauto.
      assert (Heqb: PeanoNat.Nat.eqb (length ms) 0 = false)
        by (rewrite PeanoNat.Nat.eqb_neq; lia).
      rewrite Heqb; eauto.
  Qed.
End Lemmas.
