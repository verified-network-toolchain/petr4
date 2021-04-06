open P4String

type 'tags_t name =
| BareName of 'tags_t t
| QualifiedName of 'tags_t t list * 'tags_t t

val name_rect :
  ('a1 t -> 'a2) -> ('a1 t list -> 'a1 t -> 'a2) -> 'a1 name -> 'a2

val name_rec :
  ('a1 t -> 'a2) -> ('a1 t list -> 'a1 t -> 'a2) -> 'a1 name -> 'a2

type direction =
| In
| Out
| InOut
| Directionless

val direction_rect : 'a1 -> 'a1 -> 'a1 -> 'a1 -> direction -> 'a1

val direction_rec : 'a1 -> 'a1 -> 'a1 -> 'a1 -> direction -> 'a1

val eq_dir : direction -> direction -> bool

type coq_FunctionKind =
| FunParser
| FunControl
| FunExtern
| FunTable
| FunAction
| FunFunction
| FunBuiltin

val coq_FunctionKind_rect :
  'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> coq_FunctionKind -> 'a1

val coq_FunctionKind_rec :
  'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> coq_FunctionKind -> 'a1

type 'tags_t coq_P4Type =
| TypBool
| TypString
| TypInteger
| TypInt of int
| TypBit of int
| TypVarBit of int
| TypArray of 'tags_t coq_P4Type * int
| TypTuple of 'tags_t coq_P4Type list
| TypList of 'tags_t coq_P4Type list
| TypRecord of 'tags_t coq_FieldType list
| TypSet of 'tags_t coq_P4Type
| TypError
| TypMatchKind
| TypVoid
| TypHeader of 'tags_t coq_FieldType list
| TypHeaderUnion of 'tags_t coq_FieldType list
| TypStruct of 'tags_t coq_FieldType list
| TypEnum of 'tags_t t * 'tags_t coq_P4Type option * 'tags_t t list
| TypTypeName of 'tags_t name
| TypNewType of 'tags_t t * 'tags_t coq_P4Type
| TypControl of 'tags_t coq_ControlType
| TypParser of 'tags_t coq_ControlType
| TypExtern of 'tags_t t
| TypFunction of 'tags_t coq_FunctionType
| TypAction of 'tags_t coq_P4Parameter list * 'tags_t coq_P4Parameter list
| TypTable of 'tags_t t
| TypPackage of 'tags_t t list * 'tags_t t list * 'tags_t coq_P4Parameter list
| TypSpecializedType of 'tags_t coq_P4Type * 'tags_t coq_P4Type list
| TypConstructor of 'tags_t t list * 'tags_t t list
   * 'tags_t coq_P4Parameter list * 'tags_t coq_P4Type
and 'tags_t coq_FieldType =
| MkFieldType of 'tags_t t * 'tags_t coq_P4Type
and 'tags_t coq_ControlType =
| MkControlType of 'tags_t t list * 'tags_t coq_P4Parameter list
and 'tags_t coq_FunctionType =
| MkFunctionType of 'tags_t t list * 'tags_t coq_P4Parameter list
   * coq_FunctionKind * 'tags_t coq_P4Type
and 'tags_t coq_P4Parameter =
| MkParameter of bool * direction * 'tags_t coq_P4Type * int option
   * 'tags_t t

val coq_P4Type_rect :
  'a2 -> 'a2 -> 'a2 -> (int -> 'a2) -> (int -> 'a2) -> (int -> 'a2) -> ('a1
  coq_P4Type -> 'a2 -> int -> 'a2) -> ('a1 coq_P4Type list -> 'a2) -> ('a1
  coq_P4Type list -> 'a2) -> ('a1 coq_FieldType list -> 'a2) -> ('a1
  coq_P4Type -> 'a2 -> 'a2) -> 'a2 -> 'a2 -> 'a2 -> ('a1 coq_FieldType list
  -> 'a2) -> ('a1 coq_FieldType list -> 'a2) -> ('a1 coq_FieldType list ->
  'a2) -> ('a1 t -> 'a1 coq_P4Type option -> 'a1 t list -> 'a2) -> ('a1 name
  -> 'a2) -> ('a1 t -> 'a1 coq_P4Type -> 'a2 -> 'a2) -> ('a1 coq_ControlType
  -> 'a2) -> ('a1 coq_ControlType -> 'a2) -> ('a1 t -> 'a2) -> ('a1
  coq_FunctionType -> 'a2) -> ('a1 coq_P4Parameter list -> 'a1
  coq_P4Parameter list -> 'a2) -> ('a1 t -> 'a2) -> ('a1 t list -> 'a1 t list
  -> 'a1 coq_P4Parameter list -> 'a2) -> ('a1 coq_P4Type -> 'a2 -> 'a1
  coq_P4Type list -> 'a2) -> ('a1 t list -> 'a1 t list -> 'a1 coq_P4Parameter
  list -> 'a1 coq_P4Type -> 'a2 -> 'a2) -> 'a1 coq_P4Type -> 'a2

val coq_P4Type_rec :
  'a2 -> 'a2 -> 'a2 -> (int -> 'a2) -> (int -> 'a2) -> (int -> 'a2) -> ('a1
  coq_P4Type -> 'a2 -> int -> 'a2) -> ('a1 coq_P4Type list -> 'a2) -> ('a1
  coq_P4Type list -> 'a2) -> ('a1 coq_FieldType list -> 'a2) -> ('a1
  coq_P4Type -> 'a2 -> 'a2) -> 'a2 -> 'a2 -> 'a2 -> ('a1 coq_FieldType list
  -> 'a2) -> ('a1 coq_FieldType list -> 'a2) -> ('a1 coq_FieldType list ->
  'a2) -> ('a1 t -> 'a1 coq_P4Type option -> 'a1 t list -> 'a2) -> ('a1 name
  -> 'a2) -> ('a1 t -> 'a1 coq_P4Type -> 'a2 -> 'a2) -> ('a1 coq_ControlType
  -> 'a2) -> ('a1 coq_ControlType -> 'a2) -> ('a1 t -> 'a2) -> ('a1
  coq_FunctionType -> 'a2) -> ('a1 coq_P4Parameter list -> 'a1
  coq_P4Parameter list -> 'a2) -> ('a1 t -> 'a2) -> ('a1 t list -> 'a1 t list
  -> 'a1 coq_P4Parameter list -> 'a2) -> ('a1 coq_P4Type -> 'a2 -> 'a1
  coq_P4Type list -> 'a2) -> ('a1 t list -> 'a1 t list -> 'a1 coq_P4Parameter
  list -> 'a1 coq_P4Type -> 'a2 -> 'a2) -> 'a1 coq_P4Type -> 'a2

val coq_FieldType_rect :
  ('a1 t -> 'a1 coq_P4Type -> 'a2) -> 'a1 coq_FieldType -> 'a2

val coq_FieldType_rec :
  ('a1 t -> 'a1 coq_P4Type -> 'a2) -> 'a1 coq_FieldType -> 'a2

val coq_ControlType_rect :
  ('a1 t list -> 'a1 coq_P4Parameter list -> 'a2) -> 'a1 coq_ControlType ->
  'a2

val coq_ControlType_rec :
  ('a1 t list -> 'a1 coq_P4Parameter list -> 'a2) -> 'a1 coq_ControlType ->
  'a2

val coq_FunctionType_rect :
  ('a1 t list -> 'a1 coq_P4Parameter list -> coq_FunctionKind -> 'a1
  coq_P4Type -> 'a2) -> 'a1 coq_FunctionType -> 'a2

val coq_FunctionType_rec :
  ('a1 t list -> 'a1 coq_P4Parameter list -> coq_FunctionKind -> 'a1
  coq_P4Type -> 'a2) -> 'a1 coq_FunctionType -> 'a2

val coq_P4Parameter_rect :
  (bool -> direction -> 'a1 coq_P4Type -> int option -> 'a1 t -> 'a2) -> 'a1
  coq_P4Parameter -> 'a2

val coq_P4Parameter_rec :
  (bool -> direction -> 'a1 coq_P4Type -> int option -> 'a1 t -> 'a2) -> 'a1
  coq_P4Parameter -> 'a2

type coq_StmType =
| StmUnit
| StmVoid

val coq_StmType_rect : 'a1 -> 'a1 -> coq_StmType -> 'a1

val coq_StmType_rec : 'a1 -> 'a1 -> coq_StmType -> 'a1

type 'tags_t coq_StmtContext =
| StmtCxFunction of 'tags_t coq_P4Type
| StmtCxAction
| StmtCxParserState
| StmtCxApplyBlock

val coq_StmtContext_rect :
  ('a1 coq_P4Type -> 'a2) -> 'a2 -> 'a2 -> 'a2 -> 'a1 coq_StmtContext -> 'a2

val coq_StmtContext_rec :
  ('a1 coq_P4Type -> 'a2) -> 'a2 -> 'a2 -> 'a2 -> 'a1 coq_StmtContext -> 'a2

type 'tags_t coq_DeclContext =
| DeclCxTopLevel
| DeclCxNested
| DeclCxStatement of 'tags_t coq_StmtContext

val coq_DeclContext_rect :
  'a2 -> 'a2 -> ('a1 coq_StmtContext -> 'a2) -> 'a1 coq_DeclContext -> 'a2

val coq_DeclContext_rec :
  'a2 -> 'a2 -> ('a1 coq_StmtContext -> 'a2) -> 'a1 coq_DeclContext -> 'a2

type coq_ParamContextDeclaration =
| ParamCxDeclParser
| ParamCxDeclControl
| ParamCxDeclMethod
| ParamCxDeclAction
| ParamCxDeclFunction
| ParamCxDeclPackage

val coq_ParamContextDeclaration_rect :
  'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> coq_ParamContextDeclaration -> 'a1

val coq_ParamContextDeclaration_rec :
  'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> coq_ParamContextDeclaration -> 'a1

type coq_ParamContext =
| ParamCxRuntime of coq_ParamContextDeclaration
| ParamCxConstructor of coq_ParamContextDeclaration

val coq_ParamContext_rect :
  (coq_ParamContextDeclaration -> 'a1) -> (coq_ParamContextDeclaration ->
  'a1) -> coq_ParamContext -> 'a1

val coq_ParamContext_rec :
  (coq_ParamContextDeclaration -> 'a1) -> (coq_ParamContextDeclaration ->
  'a1) -> coq_ParamContext -> 'a1

type coq_ExprContext =
| ExprCxParserState
| ExprCxApplyBlock
| ExprCxDeclLocals
| ExprCxTableAction
| ExprCxAction
| ExprCxFunction
| ExprCxConstant

val coq_ExprContext_rect :
  'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> coq_ExprContext -> 'a1

val coq_ExprContext_rec :
  'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> coq_ExprContext -> 'a1
