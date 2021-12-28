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
      (P4Parameter_ok
         (remove_all (map P4String.str Xs) Δ))
      params ->
    Δ ⊢ok TypPackage Xs Ys params
| specialized_ok τ τs :
    Forall (fun τ => Δ ⊢ok τ) τs ->
    Δ ⊢ok τ ->
    Δ ⊢ok TypSpecializedType τ τs
| constructor_ok Xs Ys params τ :
    Forall
      (P4Parameter_ok (remove_all (map P4String.str Xs) Δ))
      params ->
    remove_all (map P4String.str Xs) Δ ⊢ok τ ->
    Δ ⊢ok TypConstructor Xs Ys params τ
where "Δ '⊢ok' τ" := (P4Type_ok Δ τ) : type_scope
with ControlType_ok {tags_t : Type} (Δ : list string) : ControlType -> Prop :=
| controlType_ok Xs params :
    Forall
      (P4Parameter_ok
         (remove_all (map P4String.str Xs) Δ))
      params ->
    ControlType_ok Δ (MkControlType Xs params)
with FunctionType_ok {tags_t : Type} (Δ : list string) : FunctionType -> Prop :=
| functionType_ok Xs params k τ :
    Forall
      (P4Parameter_ok (remove_all (map P4String.str Xs) Δ))
      params ->
    remove_all (map P4String.str Xs) Δ ⊢ok τ ->
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

  Hypothesis HExtern : forall Δ X, P Δ (TypExtern X).

  Hypothesis HPackage : forall Δ Xs Ys params,
      Forall
        (P4Parameter_ok
           (remove_all (map P4String.str Xs) Δ))
        params ->
      Forall
        (S (remove_all (map P4String.str Xs) Δ))
        params ->
      P Δ (TypPackage Xs Ys params).

  Hypothesis HSpecialized : forall Δ τ τs,
      Forall (fun τ => Δ ⊢ok τ) τs ->
      Forall (P Δ) τs ->
      Δ ⊢ok τ -> P Δ τ ->
      P Δ (TypSpecializedType τ τs).

  Hypothesis HConstructor : forall Δ Xs Ys params τ,
      Forall
        (P4Parameter_ok (remove_all (map P4String.str Xs) Δ))
        params ->
      Forall (S (remove_all (map P4String.str Xs) Δ))
        params ->
      remove_all (map P4String.str Xs) Δ ⊢ok τ ->
      P (remove_all (map P4String.str Xs) Δ) τ ->
      P Δ (TypConstructor Xs Ys params τ).
  
  Hypothesis HControlType : forall Δ Xs params,
      Forall
        (P4Parameter_ok
           (remove_all (map P4String.str Xs) Δ))
        params ->
      Forall
        (S (remove_all (map P4String.str Xs) Δ))
        params ->
      Q Δ (MkControlType Xs params).
  
  Hypothesis HFunctionType : forall Δ Xs params k τ,
      Forall
        (P4Parameter_ok (remove_all (map P4String.str Xs) Δ))
        params ->
      Forall
        (S (remove_all (map P4String.str Xs) Δ))
        params ->
      remove_all (map P4String.str Xs) Δ ⊢ok τ ->
      P (remove_all (map P4String.str Xs) Δ) τ ->
      R Δ (MkFunctionType Xs params k τ).
  
  Hypothesis HP4Parameter : forall Δ b d τ n x,
      Δ ⊢ok τ -> P Δ τ ->
      S Δ (MkParameter b d τ n x).

  (** Custom induction principles for the [_ok] rules. *)
  Fail Fixpoint
    my_P4Type_ok_ind
    Δ t (H : Δ ⊢ok t) {struct H} : P Δ t :=
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
    | extern_ok _ X => HExtern _ X
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
  with my_P4Type_list_ok
         {Δ} {ts} (H : Forall (fun t => Δ ⊢ok t) ts) {struct H}
       : Forall (P Δ) ts :=
         match H with
         | Forall_nil _ => Forall_nil _
         | Forall_cons _ Hh Ht
           => Forall_cons
               _ (my_P4Type_ok_ind _ _ Hh)
               (my_P4Type_list_ok Ht)
         end
  with my_P4Type_alist_ok
         {Δ} {ts} (H : Forall (fun t => Δ ⊢ok snd t) ts) {struct H}
       : Forall (fun t => P Δ (snd t)) ts :=
         match H with
         | Forall_nil _ => Forall_nil _
         | Forall_cons _ Hh Ht
           => Forall_cons
               _ (my_P4Type_ok_ind _ _ Hh)
               (my_P4Type_alist_ok Ht)
         end
  with my_P4Type_predopt_ok
         {Δ} {t} (H: predopt (fun τ => Δ ⊢ok τ) t) {struct H}
       : predopt (P Δ) t :=
         match H with
         | EquivUtil.predop_none _ => EquivUtil.predop_none _
         | EquivUtil.predop_some _ _ H
           => EquivUtil.predop_some _ _ (my_P4Type_ok_ind _ _ H)
         end
  with my_ControlType_ok_ind
         Δ ct (H : ControlType_ok Δ ct) : Q Δ ct :=
         match H with
         | controlType_ok _ _ _ Hps
           => HControlType _ _ _ Hps (my_P4Parameter_list_ok Hps)
         end
  with my_P4Parameter_ok_ind
         Δ p (H : P4Parameter_ok Δ p) : S Δ p :=
         match H with
         | parameter_ok _ b d _ n x H
           => HP4Parameter _ b d _ n x H (my_P4Type_ok_ind _ _ H)
         end
  with my_P4Parameter_list_ok
         {Δ} {ps}
         (H : Forall (P4Parameter_ok Δ) ps)
       : Forall (S Δ) ps :=
         match H with
         | Forall_nil _ => Forall_nil _
         | Forall_cons _ Hh Ht
           => Forall_cons
               _ (my_P4Parameter_ok_ind _ _ Hh)
               (my_P4Parameter_list_ok Ht)
         end.
End OkBoomerInd.

(** TODO: will be replaced by above. *)
Scheme my_P4Type_ok_ind       := Induction for P4Type_ok       Sort Prop
  with my_ControlType_ok_ind  := Induction for ControlType_ok  Sort Prop
  with my_FunctionType_ok_ind := Induction for FunctionType_ok Sort Prop
  with my_P4Parameter_ok_ind  := Induction for P4Parameter_ok  Sort Prop.
