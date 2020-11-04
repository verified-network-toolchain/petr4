Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Info.
Require Import Coq.extraction.Extraction.

Open Scope type_scope.

Definition info (A : Type) := Info * A.

Inductive P4Int_pre_t :=
| MkP4Int_pre_t (value: Z) (width_signed: option (nat * bool)).

(* P4Int = info (value [bigint] * (width [int] * signed) option) *)
Definition P4Int := info P4Int_pre_t.

Definition P4String := info string.

Inductive name :=
  | BareName : P4String -> name
  | QualifiedName (namespaces: list P4String) (name: P4String).

Inductive Op_pre_uni : Type :=
  | Not
  | BitNot
  | UMinus.
Definition Op_uni := info Op_pre_uni.

Inductive Op_pre_bin : Type :=
  | Plus
  | PlusSat
  | Minus
  | MinusSat
  | Mul
  | Div
  | Mod
  | Shl
  | Shr
  | Le
  | Ge
  | Lt
  | Gt
  | Eq
  | NotEq
  | BitAnd
  | BitXor
  | BitOr
  | PlusPlus
  | And
  | Or.
Definition Op_bin := info Op_pre_bin.

Inductive Direction_pre_t :=
  | In
  | Out
  | InOut.
Definition Direction := info Direction_pre_t.

Inductive KeyValue :=
  | MkKeyValue (info: Info) (key: P4String) (value: Expression)
with Type'_pre_t :=
  | Typ_Bool
  | Typ_Error
  | Typ_Integer
  | Typ_IntType : Expression -> Type'_pre_t
  | Typ_BitType : Expression -> Type'_pre_t
  | Typ_VarBit : Expression -> Type'_pre_t
  (* this could be a typename or a type variable. *)
  | Typ_TypeName : name -> Type'_pre_t
  (* SpecializedType : base -> args -> Type'_pre_t *)
  | Typ_SpecializedType (bese: Type') (args: list Type')
  (* HeaderStack : header_type -> header_size -> Type'_pre_t *)
  | Typ_HeaderStack (header: Type') (size: Expression)
  | Typ_Tuple : list Type' -> Type'_pre_t
  | Typ_String
  | Typ_Void
  | Typ_DontCare
with Type' :=
  | MkType' : info Type'_pre_t -> Type'
with Argument :=
  | Arg_Expression (info: Info) (value: Expression)
  (* Arg_KeyValue : key -> value -> Argument_pre_t *)
  | Arg_KeyValue (info: Info) (key: P4String) (value: Expression)
  | Arg_Missing (info: Info)
with Expression_pre_t :=
  | Exp_True
  | Exp_False
  | Exp_Int : P4Int -> Expression_pre_t
  | Exp_String : P4String -> Expression_pre_t
  | Exp_Name : name -> Expression_pre_t
  (* | ArrayAccess of
      { array: t;
        index: t } *)
  (* | BitStringAccess of
      { bits: t;
        lo: t;
        hi: t } *)
  (* | List of
      { values: t list } *)
  (* | Record of
      { entries: KeyValue.t list } *)
  | Exp_UnaryOp (op: Op_uni) (arg: Expression)
  | Exp_BinaryOp (op: Op_bin) (args: (Expression * Expression))
  (* | Cast of
      { typ: Type.t;
        expr: t } *)
  (* | TypeMember of
      { typ: name;
        name: P4String.t } *)
  (* | ErrorMember of P4String.t *)
  (* | ExpressionMember of
      { expr: t;
        name: P4String.t } *)
  (* | Ternary of
      { cond: t;
        tru: t;
        fls: t } *)
  (* FunctionCall func type_args args *)
  | Exp_FunctionCall (func: Expression) (type_args: list Type') (args: list Argument)
  (* | NamelessInstantiation of
      { typ: Type.t [@key "type"];
        args: Argument.t list } *)
  (* | Mask of
      { expr: t;
        mask: t } *)
  (* | Range of
      { lo: t;
        hi: t } *)
with Expression :=
  | MkExpression : info Expression_pre_t -> Expression.

Inductive Annotation_body :=
  | Anno_Empty (info: Info)
  | Anno_Unparsed : Info -> list P4String -> Annotation_body
  | Anno_Expression : Info -> list Expression -> Annotation_body
  | Anno_KeyValue : Info -> list KeyValue -> Annotation_body.
Inductive Annotation :=
  | MkAnnotation (info: Info) (name: P4String) (body: Annotation_body).
