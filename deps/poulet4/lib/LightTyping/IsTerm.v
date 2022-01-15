Require Export Poulet4.Typed Poulet4.Syntax
        NArith.BinNat Coq.Lists.List Poulet4.P4cub.Util.EquivUtil.
Export ListNotations.

(** * Well-formed P4light Terms. *)

Section Is.
  Context {tags_t : Type}.
  Notation typ := (@P4Type tags_t).
  Notation expr := (@Expression tags_t).
  Notation pre_expr := (@ExpressionPreT tags_t).
  
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
      0 < N.to_nat n ->
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
  | is_enum X mems :
      length mems > 0 ->
      is_expr_typ (TypEnum X None mems)
  | is_senum X t mems :
      is_expr_typ t ->
      is_expr_typ (TypEnum X (Some t) mems)
  | is_name X :
      is_expr_typ (TypTypeName X)
  | is_newtype X t :
      is_expr_typ t ->
      is_expr_typ (TypNewType X t).

  Inductive is_expr : expr -> Prop :=
    is_MkExpression i e t d :
      is_expr_typ t ->
      is_pre_expr e ->
      is_expr (MkExpression i e t d)
  with is_pre_expr : pre_expr -> Prop :=
  | is_ExpBool b :
      is_pre_expr (ExpBool b)
  | is_ExpInt z :
      is_pre_expr (ExpInt z)
  | is_ExpString s :
      is_pre_expr (ExpString s)
  | is_ExpName x l :
      is_pre_expr (ExpName x l)
  | is_ExpArrayAccess e1 e2 :
      is_expr e1 ->
      is_expr e2 ->
      is_pre_expr (ExpArrayAccess e1 e2)
  | is_ExpBitStringAccess e lo hi :
      is_expr e ->
      is_pre_expr (ExpBitStringAccess e lo hi)
  | is_ExpList es :
      Forall is_expr es ->
      is_pre_expr (ExpList es)
  | is_ExpRecord es :
      Forall (is_expr ∘ snd) es ->
      is_pre_expr (ExpRecord es)
  | is_ExpUnaryOp o e :
      is_expr e ->
      is_pre_expr (ExpUnaryOp o e)
  | is_ExpBinaryOp o e1 e2 :
      is_expr e1 ->
      is_expr e2 ->
      is_pre_expr (ExpBinaryOp o (e1,e2))
  | is_ExpCast t e :
      is_expr_typ t ->
      is_expr e ->
      is_pre_expr (ExpCast t e)
  | is_ExpTypeMember X x :
      is_pre_expr (ExpTypeMember X x)
  | is_ExpErrorMember x :
      is_pre_expr (ExpErrorMember x)
  | is_ExpExpressionMember e x :
      is_expr e ->
      is_pre_expr (ExpExpressionMember e x)
  | is_ExpTernary e1 e2 e3 :
      is_expr e1 ->
      is_expr e2 ->
      is_expr e3 ->
      is_pre_expr (ExpTernary e1 e2 e3).
End Is.

Section IsInd.
  Variable tags_t : Type.

  Section IsExprTypInd.
    Variable P : @P4Type tags_t -> Prop.
  
    Hypothesis HBool : P TypBool.
    Hypothesis HString : P TypString.
    Hypothesis HInteger : P TypInteger.
    Hypothesis HInt : forall w, P (TypInt w).
    Hypothesis HBit : forall w, P (TypBit w).
    Hypothesis HVarbit : forall w, P (TypVarBit w).
    Hypothesis HArray : forall t n,
        0 < N.to_nat n ->
        is_expr_typ t -> P t ->
        P (TypArray t n).
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
    Hypothesis HEnum : forall X mems,
        length mems > 0 ->
        P (TypEnum X None mems).
    Hypothesis HSenum : forall X t mems,
        is_expr_typ t ->
        P t -> P (TypEnum X (Some t) mems).
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
              (H : predop is_expr_typ ot)
            : predop P ot :=
            match H with
            | predop_none _ => predop_none _
            | predop_some _ _ H
              => predop_some _ _ (I _ H)
            end in
        match H with
        | is_bool          => HBool
        | is_string        => HString
        | is_integer       => HInteger
        | is_int w         => HInt w
        | is_bit w         => HBit w
        | is_varbit w      => HVarbit w
        | is_array _ _ n H => HArray _ _ n H (I _ H)
        | is_tuple _ H     => HTuple _ H (L H)
        | is_list  _ H     => HList _ H (L H)
        | is_record _ H    => HRecord _ H (AL H)
        | is_error         => HError
        | is_header _ H    => HHeader _ H (AL H)
        | is_union  _ H    => HUnion  _ H (AL H)
        | is_struct _ H    => HStruct _ H (AL H)
        | is_name X        => HName X
        | is_newtype X _ H => HNewType X _ H (I _ H)
        | is_enum X _   H  => HEnum X _ H
        | is_senum X _ ms H => HSenum X _ ms H (I _ H)
        end.
  End IsExprTypInd.

  Section IsExprInd.
    (* TODO. *)
  End IsExprInd.
End IsInd.
