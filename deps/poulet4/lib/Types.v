Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Info.
Require Import Coq.extraction.Extraction.

Open Scope type_scope.

Definition info (A : Type) := Info * A.

Inductive P4IntPreT :=
| MkP4IntPreT (value: Z) (width_signed: option (nat * bool)).

(* P4Int = info (value [bigint] * (width [int] * signed) option) *)
Definition P4Int := info P4IntPreT.

Definition P4String := info string.

Inductive name :=
  | BareName (_: P4String)
  | QualifiedName (namespaces: list P4String) (name: P4String).

Inductive OpPreUni : Type :=
  | Not
  | BitNot
  | UMinus.
Definition OpUni := info OpPreUni.

Inductive OpPreBin : Type :=
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
Definition OpBin := info OpPreBin.

Inductive DirectionPreT :=
  | In
  | Out
  | InOut.
Definition Direction := info DirectionPreT.

Inductive KeyValue :=
  | MkKeyValue (info: Info) (key: P4String) (value: Expression)
with P4TypePreT :=
  | TypBool
  | TypError
  | TypInteger
  | TypIntType (_: Expression)
  | TypBitType (_: Expression)
  | TypVarBit (_: Expression)
  (* this could be a typename or a type variable. *)
  | TypTypeName (_: name)
  (* SpecializedType : base -> args -> P4TypePreT *)
  | TypSpecializedType (bese: P4Type) (args: list P4Type)
  (* HeaderStack : header_type -> header_size -> P4TypePreT *)
  | TypHeaderStack (header: P4Type) (size: Expression)
  | TypTuple (_: list P4Type)
  | TypString
  | TypVoid
  | TypDontCare
with P4Type :=
  | MkP4Type (_: Info) (_: P4TypePreT)
with ArgumentPreT :=
  | ArgExpression (value: Expression)
  (* ArgKeyValue : key -> value -> ArgumentPreT *)
  | ArgKeyValue (key: P4String) (value: Expression)
  | ArgMissing
with Argument :=
  | MkArgument (_: Info) (_: ArgumentPreT)
with ExpressionPreT :=
  | ExpTrue
  | ExpFalse
  | ExpInt (_: P4Int)
  | ExpString (_: P4String)
  | ExpName (_: name)
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
  | ExpUnaryOp (op: OpUni) (arg: Expression)
  | ExpBinaryOp (op: OpBin) (args: (Expression * Expression))
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
  (* FunctionCall: func type_args args *)
  | ExpFunctionCall (func: Expression) (type_args: list P4Type) (args: list Argument)
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
  | MkExpression (_: Info) (_: ExpressionPreT).

Inductive AnnotationBody :=
  | AnnoEmpty
  | AnnoUnparsed (_: list P4String)
  | AnnoExpression (_: list Expression)
  | AnnoKeyValue (_: list KeyValue).
Inductive Annotation :=
  | MkAnnotation (info: Info) (name: P4String) (body: AnnotationBody).
