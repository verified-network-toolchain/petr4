Require Import Coq.Numbers.BinNums.
Require Petr4.String.
Require Petr4.P4String.
Require Petr4.P4Int.
Require Import Coq.Classes.EquivDec.

Section Typed.
  Context (tags_t: Type).
  Notation P4String := (P4String.t tags_t).
  Notation P4Int := (P4Int.t tags_t).

  Inductive name :=
  | BareName (name: P4String)
  | QualifiedName (namespaces: list P4String) (name: P4String).

  Definition equivn (n1 n2 : name) : Prop :=
    match n1, n2 with
    | BareName x1, BareName x2                   => P4String.equiv x1 x2
    | QualifiedName xs1 x1, QualifiedName xs2 x2 =>
        P4String.equiv x1 x2 /\
        List.Forall2 (@P4String.equiv tags_t) xs1 xs2
    | _, _ => False
    end.

  Lemma equivn_reflexive : Reflexive equivn.
  Proof.
    intros [x | xs x]; simpl.
    - reflexivity.
    - split; try reflexivity.
      induction xs as [| h xs IHxs];
        constructor; auto. reflexivity.
  Qed.

  Lemma equivn_symmetric : Symmetric equivn.
  Proof.
    intros [x | xs x] [y | ys y] H; simpl in *; auto.
    - symmetry. assumption.
    - destruct H as [Hxy H]. split; try (symmetry; assumption).
      generalize dependent ys; induction xs as [| hx xs IHxs];
        intros [| hy ys] H; inversion H; clear H; subst; auto;
      constructor; auto. symmetry. assumption.
  Qed.

  Lemma equivn_transitive : Transitive equivn.
  Proof.
    intros [x | xs x] [y | ys y] [z | zs z] Hxy Hyz;
      simpl in *; auto; try contradiction.
    - transitivity y; auto.
    - destruct Hxy as [Hxy Hxys]; destruct Hyz as [Hyz Hyzs]; split.
      + transitivity y; auto.
      + clear x y z Hxy Hyz.
        generalize dependent zs; generalize dependent ys.
        induction xs as [| x xs IHxs];
          intros [| y ys] Hxy [| z zs] Hyz;
          inversion Hxy; clear Hxy;
            inversion Hyz; clear Hyz; subst; auto.
        constructor.
        * transitivity y; auto.
        * apply IHxs with ys; auto.
  Qed.

  Instance NameEquivalence : Equivalence equivn.
  Proof.
    constructor; [ apply equivn_reflexive
                 | apply equivn_symmetric
                 | apply equivn_transitive].
  Defined.

  Instance NameEqDec : EqDec name equivn.
  Proof.
    intros [x | xs x] [y | ys y];
      unfold equiv; unfold complement; simpl; auto.
    - pose proof equiv_dec x y; auto.
    - assert (H : {List.Forall2 (@P4String.equiv tags_t) xs ys} +
                  {~ List.Forall2 (@P4String.equiv tags_t) xs ys}).
      { clear x y; generalize dependent ys.
        induction xs as [| x xs IHxs]; intros [| y ys];
          try (right; intros H'; inversion H'; contradiction).
        - left; constructor.
        - pose proof equiv_dec x y as Hxy; specialize IHxs with ys;
            unfold equiv in *; unfold complement in *.
          destruct Hxy as [Hxy | Hxy]; destruct IHxs as [IH | IH];
            try (right; intros H'; inversion H'; contradiction).
          left. constructor; auto. }
      destruct (equiv_dec x y) as [Hxy | Hxy]; destruct H as [H | H];
        unfold equiv in *; unfold complement in *;
          try (right; intros [Hxy' H']; contradiction).
      left; auto.
  Defined.

  Inductive direction :=
  | In
  | Out
  | InOut
  | Directionless.

  Definition eq_dir (d1 d2: direction) :=
    match d1, d2 with
    | In, In
    | Out, Out
    | InOut, InOut
    | Directionless, Directionless => true
    | _, _ => false
    end.

  Inductive FunctionKind :=
  | FunParser
  | FunControl
  | FunExtern
  | FunTable
  | FunAction
  | FunFunction
  | FunBuiltin.

  Inductive P4Type :=
  | TypBool
  | TypString
  | TypInteger
  | TypInt (width: nat)
  | TypBit (width: nat)
  | TypVarBit (width: nat)
  | TypArray (typ: P4Type) (size: nat)
  | TypTuple (types: list P4Type)
  | TypList (types: list P4Type)
  | TypRecord (fields: list FieldType)
  | TypSet (elt_type: P4Type)
  | TypError
  | TypMatchKind
  | TypVoid
  | TypHeader (fields: list FieldType)
  | TypHeaderUnion (fields: list FieldType)
  | TypStruct (fields: list FieldType)
  | TypEnum (name: P4String) (typ: option P4Type) (members: list P4String)
  | TypTypeName (name: name)
  | TypNewType (name: P4String) (typ: P4Type)
  | TypControl (_: ControlType)
  | TypParser (_: ControlType)
  | TypExtern (extern_name: P4String)
  | TypFunction (fn: FunctionType)
  | TypAction (data_params: list P4Parameter) (ctrl_params: list P4Parameter)
  | TypTable (result_typ_name: P4String)
  | TypPackage (type_params: list P4String) (wildcard_params: list P4String)
               (parameters: list P4Parameter)
  | TypSpecializedType (base: P4Type) (args: list P4Type)
  | TypConstructor (type_params: list P4String) (wildcard_params: list P4String)
                   (parameters: list P4Parameter) (ret: P4Type)
  with FieldType :=
  | MkFieldType (name: P4String) (typ: P4Type)
  with ControlType :=
  | MkControlType (type_params: list P4String) (parameters: list P4Parameter)
  with FunctionType :=
  | MkFunctionType (type_params: list P4String) (parameters: list P4Parameter)
                   (kind: FunctionKind) (ret: P4Type)
  with P4Parameter :=
  | MkParameter (opt: bool) (direction: direction) (typ: P4Type) (default_arg_id: option nat) (variable: P4String).

  Inductive StmType :=
  | StmUnit
  | StmVoid.

  Inductive StmtContext :=
  | StmtCxFunction (ret: P4Type)
  | StmtCxAction
  | StmtCxParserState
  | StmtCxApplyBlock.

  Inductive DeclContext :=
  | DeclCxTopLevel
  | DeclCxNested
  | DeclCxStatement (_: StmtContext).

  Inductive ParamContextDeclaration :=
  | ParamCxDeclParser
  | ParamCxDeclControl
  | ParamCxDeclMethod
  | ParamCxDeclAction
  | ParamCxDeclFunction
  | ParamCxDeclPackage.

  Inductive ParamContext :=
  | ParamCxRuntime (_: ParamContextDeclaration)
  | ParamCxConstructor (_: ParamContextDeclaration).

  Inductive ExprContext :=
  | ExprCxParserState
  | ExprCxApplyBlock
  | ExprCxDeclLocals
  | ExprCxTableAction
  | ExprCxAction
  | ExprCxFunction
  | ExprCxConstant.

End Typed.
