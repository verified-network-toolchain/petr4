Require Import Coq.ZArith.ZArith.
Require Import CamlString.
Require Import Info.

Inductive name :=
| BareName (name: caml_string)
| QualifiedName (namespaces: list caml_string) (name: caml_string).

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
| TypArray (typ: P4Type) (size: Z)
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
| TypEnum (name: caml_string) (typ: option P4Type) (members: list caml_string)
| TypTypeName (name: name)
| TypNewType (name: caml_string) (typ: P4Type)
| TypControl (_: ControlType)
| TypParser (_: ControlType)
| TypExtern (extern_name: caml_string)
| TypFunction (fn: FunctionType)
| TypAction (data_params: list P4Parameter) (ctrl_params: list P4Parameter)
| TypTable (result_typ_name: caml_string)
| TypPackage (type_params: list caml_string) (wildcard_params: list caml_string)
             (parameters: list P4Parameter)
| TypSpecializedType (base: P4Type) (args: list P4Type)
| TypConstructor (type_params: list caml_string) (wildcard_params: list caml_string)
                 (parameters: list P4Parameter) (ret: P4Type)
with FieldType :=
| MkFieldType (name: caml_string) (typ: P4Type)
with ControlType :=
| MkControlType (type_params: list caml_string) (parameters: list P4Parameter)
with FunctionType :=
| MkFunctionType (type_params: list caml_string) (parameters: list P4Parameter)
                 (kind: FunctionKind) (ret: P4Type)
with P4Parameter :=
| MkParameter (opt: bool) (direction: direction) (typ: P4Type) (variable: caml_string).

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
