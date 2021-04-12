Require Import Coq.Numbers.BinNums.
Require Import Coq.Classes.EquivDec.

Require Poulet4.P4String.
Require Poulet4.P4Int.

Section Typed.
  Context {tags_t: Type}.
  Notation P4String := (P4String.t tags_t).
  Notation P4Int := (P4Int.t tags_t).

  Inductive name :=
  | BareName (name: P4String)
  | QualifiedName (namespaces: list P4String) (name: P4String).

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
  | TypRecord (fields: P4String.AList tags_t P4Type)
  | TypSet (elt_type: P4Type)
  | TypError
  | TypMatchKind
  | TypVoid
  | TypHeader (fields: P4String.AList tags_t P4Type)
  | TypHeaderUnion (fields: P4String.AList tags_t P4Type)
  | TypStruct (fields: P4String.AList tags_t P4Type)
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
