Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Info.
Require Types.

Definition P4String := Types.P4String.
Definition Annotation := Types.Annotation.

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

Inductive TableType :=
| MkTableType (result_typ_name: string).

Inductive FunctionKind :=
| FunParser
| FunControl
| FunExtern
| FunTable
| FunAction
| FunFunction
| FunBuiltin.


Inductive P4Parameter :=
(* MkParameter: annotations -> direction -> type -> variable ->
                  opt_value -> P4Parameter *)
| MkParameter (annotations: list Annotation) (direction: direction) (typ: P4Type)
              (variable: P4String) (opt_value: option Types.Expression)
with PackageType :=
(* MkPackageType : type_params -> wildcard_params -> parameters ->
                     PackageType *)
| MkPackageType (type_params: list string) (wildcard_params: list string)
                (parameters: list P4Parameter)
with ControlType :=
(* MkControlType : type_params -> parameters -> ControlType *)
| MkControlType (type_params: list string) (parameters: list P4Parameter)
with ExternMethodType :=
(* ExternMethodType : name -> type -> ExternMethodType *)
| MkExternMethodType (name: string) (typ: FunctionType)
with ExternType :=
(* MkExternType : type_params -> methods -> ExternType *)
| MkExternType (type_params: list string) (methods: list ExternMethodType)
with ArrayType :=
(* MkArrayType : type -> size [int] -> ArrayType *)
| MkArrayType (typ: P4Type) (size: Z)
with TupleType :=
| MkTupleType (types: list P4Type)
with NewType :=
| MkNewType (name: string) (typ: P4Type)
with RecordFieldType :=
| MkRecordFieldType (name: string) (typ: P4Type)
with RecordType :=
| MkRecordType (fields: list RecordFieldType)
with EnumType :=
(* MkEnumType : name -> type -> members -> EnumType *)
| MkEnumType (name: string) (typ: option P4Type) (members: list string)
with FunctionType :=
(* MkFunctionType : type_params -> parameters -> kind ->
                      return -> FunctionType *)
| MkFunctionType (type_params: list string) (parameters: list P4Parameter)
                 (kind: FunctionKind) (ret: P4Type)
with SpecializedType :=
(* MkSpecializedType : base -> args -> SpecializedType *)
| MkSpecializedType (base: P4Type) (args: list P4Type)
with ActionType :=
(* MkActionType : data_params -> ctrl_params -> ActionType *)
| MkActionType (data_params: list P4Parameter) (ctrl_params: list P4Parameter)
with ConstructorType :=
(* MkConstructorType : type_params -> wildcard_params -> parameters
                         return -> ConstructorType *)
| MkConstructorType (type_params: list string) (wildcard_params: list string)
                    (parameters: list P4Parameter) (ret: P4Type)
with P4Type :=
| TypBool
| TypString
| TypInteger
| TypInt (width: nat)
| TypBit (width: nat)
| TypVarBit (width: nat)
| TypArray (size: ArrayType)
| TypTuple (_: TupleType)
| TypList (_: TupleType)
| TypRecord (_: RecordType)
| TypSet (_: P4Type)
| TypError
| TypMatchKind
| TypTypeName (_: Types.name)
| TypNewType (_: NewType)
| TypVoid
| TypHeader (_: RecordType)
| TypHeaderUnion (_: RecordType)
| TypStruct (_: RecordType)
| TypEnum (_: EnumType)
| TypSpecializedType (_: SpecializedType)
| TypPackage (_: PackageType)
| TypControl (_: ControlType)
| TypParser (_: ControlType)
| TypExtern (_: ExternType)
| TypFunction (_: FunctionType)
| TypAction (_: ActionType)
| TypConstructor (_: ConstructorType)
| TypTable (_: TableType).

Inductive StmType :=
| StmUnit
| StmVoid.

Inductive StmtContext :=
| StmtCxFunction (_: P4Type)
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
