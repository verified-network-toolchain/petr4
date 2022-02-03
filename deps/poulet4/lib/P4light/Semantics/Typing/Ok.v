From Coq Require Export Strings.String Lists.List.
From Poulet4 Require Export P4light.Syntax.Typed
     P4light.Syntax.Syntax Utils.Util.EquivUtil.
Export ListNotations.

(** * Ok Type Names In Context. *)

(** Utility definitions. *)

Notation remove_str := (remove string_dec).

Lemma remove_str_nil : forall s, remove_str s [] = [].
Proof.
  auto.
Qed.

Notation remove_all := (fold_right remove_str).

Lemma remove_all_nil : forall ss, remove_all [] ss = [].
Proof.
  intros ss; induction ss as [| s ss IHss];
    cbn in *; try rewrite IHss; auto.
Qed.

(** Ok types. *)
Reserved Notation "Δ '⊢ok' τ" (at level 80, no associativity).
(** Ok expressions. *)
Reserved Notation "Δ '⊢okᵉ' e" (at level 80, no associativity).
(** Ok pre-expressions. *)
Reserved Notation "Δ '⊢ok`ᵉ' e" (at level 80, no associativity).
(** Ok statements. *)
Reserved Notation "Δ '⊢okˢ' s" (at level 80, no associativity).
(** Ok pre-statements. *)
Reserved Notation "Δ '⊢ok`ˢ' s" (at level 80, no associativity).
(** Ok blocks. *)
Reserved Notation "Δ '⊢okᵇ' b" (at level 80, no associativity).

(** Free type variables bound by [Δ]. *)
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
    predop (fun τ => remove_str (P4String.str X) Δ ⊢ok τ) τ ->
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
| extern_ok X :
    Δ ⊢ok TypExtern X
| function_ok ft :
    FunctionType_ok Δ ft ->
    Δ ⊢ok TypFunction ft
| action_ok ds cs :
    Forall (P4Parameter_ok Δ) ds ->
    Forall (P4Parameter_ok Δ) cs ->
    Δ ⊢ok TypAction ds cs
| table_ok X :
    Δ ⊢ok TypTable X
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

Inductive Expression_ok
          {tags_t: Type} (Δ: list string)
  : @Expression tags_t -> Prop :=
  MkExpression_ok i e t d :
    Δ ⊢ok t ->
    Δ ⊢ok`ᵉ e ->
    Δ ⊢okᵉ MkExpression i e t d
where "Δ '⊢okᵉ' e" := (Expression_ok Δ e) : type_scope
with ExpressionPreT_ok
       {tags_t: Type} (Δ: list string)
     : @ExpressionPreT tags_t -> Prop :=
| ExpBool_ok b :
    Δ ⊢ok`ᵉ ExpBool b
| ExpInt_ok n :
    Δ ⊢ok`ᵉ ExpInt n
| ExpString_ok s :
    Δ ⊢ok`ᵉ ExpString s
| ExpName_ok x l :
    Δ ⊢ok`ᵉ ExpName x l
| ExpArrayAccess_ok e₁ e₂ :
    Δ ⊢okᵉ e₁ ->
    Δ ⊢okᵉ e₂ ->
    Δ ⊢ok`ᵉ ExpArrayAccess e₁ e₂
| ExpBitStringAccess_ok e lo hi :
    Δ ⊢okᵉ e ->
    Δ ⊢ok`ᵉ ExpBitStringAccess e lo hi
| ExpList_ok es :
    Forall (Expression_ok Δ) es ->
    Δ ⊢ok`ᵉ ExpList es
| ExpRecord_ok es :
    Forall (fun xe => Δ ⊢okᵉ snd xe) es ->
    Δ ⊢ok`ᵉ ExpRecord es
| ExpUnaryOp_ok o e :
    Δ ⊢okᵉ e ->
    Δ ⊢ok`ᵉ ExpUnaryOp o e
| ExpBinaryOp_ok o e₁ e₂ :
    Δ ⊢okᵉ e₁ ->
    Δ ⊢okᵉ e₂ ->
    Δ ⊢ok`ᵉ ExpBinaryOp o e₁ e₂
| ExpCast_ok t e :
    Δ ⊢ok t ->
    Δ ⊢okᵉ e ->
    Δ ⊢ok`ᵉ ExpCast t e
| ExpTypeMember_ok X x :
    List.In (P4String.str X) Δ ->
    Δ ⊢ok`ᵉ ExpTypeMember X x
| ExpErrorMember_ok X :
    Δ ⊢ok`ᵉ ExpErrorMember X
| ExpExpressionMember_ok e x :
    Δ ⊢okᵉ e ->
    Δ ⊢ok`ᵉ ExpExpressionMember e x
| ExpTernary_ok e₁ e₂ e₃ :
    Δ ⊢okᵉ e₁ ->
    Δ ⊢okᵉ e₂ ->
    Δ ⊢okᵉ e₃ ->
    Δ ⊢ok`ᵉ ExpTernary e₁ e₂ e₃
| ExpFunctionCall_ok e Xs es :
    Forall (predop (Expression_ok Δ)) es ->
    Δ ⊢okᵉ e ->
    Δ ⊢ok`ᵉ ExpFunctionCall e Xs es
| ExpNamelessInstantiation_ok t es :
    Δ ⊢ok t ->
    Forall (Expression_ok Δ) es ->
    Δ ⊢ok`ᵉ ExpNamelessInstantiation t es
| ExpDontCare_ok :
    Δ ⊢ok`ᵉ ExpDontCare
where "Δ '⊢ok`ᵉ' e" := (ExpressionPreT_ok Δ e) : type_scope.

Inductive Statement_ok
          {tags_t: Type} (Δ: list string)
  : @Statement tags_t -> Prop :=
  MkStatement_ok i s t :
    Δ ⊢ok`ˢ s ->
    Δ ⊢okˢ MkStatement i s t
where "Δ '⊢okˢ' s" := (Statement_ok Δ s) : type_scope
with StatementPreT_ok
       {tags_t: Type} (Δ: list string)
     : @StatementPreT tags_t -> Prop :=
| StatMethodCall_ok e ts es :
    Forall (predop (Expression_ok Δ)) es ->
    Δ ⊢okᵉ e ->
    Δ ⊢ok`ˢ StatMethodCall e ts es
| StatAssignment_ok e₁ e₂ :
    Δ ⊢okᵉ e₁ ->
    Δ ⊢okᵉ e₂ ->
    Δ ⊢ok`ˢ StatAssignment e₁ e₂
| StatDirectApplication_ok t t' es :
    Δ ⊢ok t ->
    Forall (predop (Expression_ok Δ)) es ->
    Δ ⊢ok`ˢ StatDirectApplication t t' es
| StatConditional_ok e s₁ s₂ :
    Δ ⊢okᵉ e ->
    Δ ⊢okˢ s₁ ->
    predop (Statement_ok Δ) s₂ ->
    Δ ⊢ok`ˢ StatConditional e s₁ s₂
| StatBlock_ok b :
    Δ ⊢okᵇ b ->
    Δ ⊢ok`ˢ StatBlock b
| StatExit_ok :
    Δ ⊢ok`ˢ StatExit
| StatEmpty_ok :
    Δ ⊢ok`ˢ StatEmpty
| StatReturn_ok e :
    predop (Expression_ok Δ) e ->
    Δ ⊢ok`ˢ StatReturn e
| StatSwitch_ok e ss :
    Δ ⊢okᵉ e ->
    Forall (SwitchCase_ok Δ) ss ->
    Δ ⊢ok`ˢ StatSwitch e ss
| StatConstant_ok t x e l :
    Δ ⊢ok t ->
    Δ ⊢okᵉ e ->
    Δ ⊢ok`ˢ StatConstant t x e l
| StatVariable_ok t x e l :
    Δ ⊢ok t ->
    predop (Expression_ok Δ) e ->
    Δ ⊢ok`ˢ StatVariable t x e l
| StatInstantiation_ok t es x init :
    Δ ⊢ok t ->
    Forall (Expression_ok Δ) es ->
    Forall (Initializer_ok Δ) init ->
    Δ ⊢ok`ˢ StatInstantiation t es x init
where "Δ '⊢ok`ˢ' s" := (StatementPreT_ok Δ s) : type_scope
with Block_ok
       {tags_t: Type} (Δ: list string)
     : @Block tags_t -> Prop :=
| BlockEmpty_ok i :
    Δ ⊢okᵇ BlockEmpty i
| BlockCons_ok s b :
    Δ ⊢okˢ s ->
    Δ ⊢okᵇ b ->
    Δ ⊢okᵇ BlockCons s b
where "Δ '⊢okᵇ' b" := (Block_ok Δ b) : type_scope
with SwitchCase_ok
       {tags_t: Type} (Δ: list string)
     : @StatementSwitchCase tags_t -> Prop :=
| SwCaseAction_ok i lbl b :
    Δ ⊢okᵇ b ->
    SwitchCase_ok Δ (StatSwCaseAction i lbl b)
| SwCaseFallThrough_ok i lbl :
    SwitchCase_ok Δ (StatSwCaseFallThrough i lbl)
with Initializer_ok
       {tags_t: Type} (Δ: list string)
     : @Initializer tags_t -> Prop :=
| InitFunction_ok i t x Xs ps b :
    Forall (P4Parameter_ok (remove_all Δ (map P4String.str Xs))) ps ->
    remove_all Δ (map P4String.str Xs) ⊢ok t ->
    remove_all Δ (map P4String.str Xs) ⊢okᵇ b ->
    Initializer_ok Δ (InitFunction i t x Xs ps b)
| InitInstantiation_ok i t es x init :
    Δ ⊢ok t ->
    Forall (Expression_ok Δ) es ->
    Forall (Initializer_ok Δ) init ->
    Initializer_ok Δ (InitInstantiation i t es x init).

(** Custom induction principles. *)
Section OkBoomerInd.
  Variable tags_t : Type.

  Section OkType.
    Variables
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
        predop (fun τ => remove_str (P4String.str X) Δ ⊢ok τ) t ->
        predop (P (remove_str (P4String.str X) Δ)) t ->
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
    
    Hypothesis HFunction : forall Δ ft,
        FunctionType_ok Δ ft -> R Δ ft -> P Δ (TypFunction ft).
    
    Hypothesis HAction : forall Δ ds cs,
        Forall (P4Parameter_ok Δ) ds ->
        Forall (S Δ) ds ->
        Forall (P4Parameter_ok Δ) cs ->
        Forall (S Δ) cs ->
        P Δ (TypAction ds cs).
    
    Hypothesis HTable : forall Δ X, P Δ (TypTable X).
    
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
      let my_P4Type_predop_ok
            {Δ} {t} (H: predop (fun τ => Δ ⊢ok τ) t)
          : predop (P Δ) t :=
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
      | enum_ok _ X _ mems H => HEnum _ X _ mems H (my_P4Type_predop_ok H)
      | typeName_ok _ _ H => HName _ _ H
      | newType_ok _ _ _ H => HNewType _ _ _ H (my_P4Type_ok_ind _ _ H)
      | control_ok _ _ H => HControl _ _ H (my_ControlType_ok_ind _ _ H)
      | parser_ok _ _ H => HParser _ _ H (my_ControlType_ok_ind _ _ H)
      | extern_ok _ X => HExtern _ X
      | function_ok _ _ H
        => HFunction _ _ H (my_FunctionType_ok_ind _ _ H)
      | action_ok _ _ _ Hds Hcs
        => HAction
            _ _ _
            Hds (my_P4Parameter_list_ok Hds)
            Hcs (my_P4Parameter_list_ok Hcs)
      | table_ok _ X => HTable _ X
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
  End OkType.

  Section OkExpr.
    (* TODO: induction principles for ok expressions. *)
  End OkExpr.

  Section OkStat.
    (* TODO: induction principles for ok statements. *)
  End OkStat.
End OkBoomerInd.
