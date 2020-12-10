Require Import Coq.ZArith.ZArith.
Require Import Info.
Require String.

Inductive name :=
| BareName (name: String.t)
| QualifiedName (namespaces: list String.t) (name: String.t).

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
| TypArray (size: ArrayType)
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
| TypEnum (name: String.t) (typ: option P4Type) (members: list String.t)
| TypTypeName (name: name)
| TypNewType (name: String.t) (typ: P4Type)
| TypControl (type_params: list String.t) (parameters: list P4Parameter)
| TypParser (type_params: list String.t) (parameters: list P4Parameter)
| TypExtern (extern_name: String.t)
| TypFunction (fn: FunctionType)
| TypAction (data_params: list P4Parameter) (ctrl_params: list P4Parameter)
| TypTable (result_typ_name: String.t)
| TypPackage (type_params: list String.t) (wildcard_params: list String.t)
             (parameters: list P4Parameter)
| TypConstructor (type_params: list String.t) (wildcard_params: list String.t)
                 (parameters: list P4Parameter) (ret: P4Type)
with ArrayType :=
| MkArrayType (typ: P4Type) (size: Z)
with FieldType :=
| MkFieldType (name: String.t) (typ: P4Type)
with ControlType :=
| MkControlType (type_params: list String.t) (parameters: list P4Parameter)
with FunctionType :=
| MkFunctionType (type_params: list String.t) (parameters: list P4Parameter)
                 (kind: FunctionKind) (ret: P4Type)
with SpecializedType :=
| MkSpecializedType (base: P4Type) (args: list P4Type)
with P4Parameter :=
| MkParameter (opt: bool) (direction: direction) (typ: P4Type) (variable: String.t).

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
