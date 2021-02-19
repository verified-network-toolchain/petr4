open P4String

type 'tags_t name =
| BareName of 'tags_t t
| QualifiedName of 'tags_t t list * 'tags_t t

(** val name_rect :
    ('a1 t -> 'a2) -> ('a1 t list -> 'a1 t -> 'a2) -> 'a1 name -> 'a2 **)

let name_rect f f0 = function
| BareName x -> f x
| QualifiedName (x, x0) -> f0 x x0

(** val name_rec :
    ('a1 t -> 'a2) -> ('a1 t list -> 'a1 t -> 'a2) -> 'a1 name -> 'a2 **)

let name_rec f f0 = function
| BareName x -> f x
| QualifiedName (x, x0) -> f0 x x0

type direction =
| In
| Out
| InOut
| Directionless

(** val direction_rect : 'a1 -> 'a1 -> 'a1 -> 'a1 -> direction -> 'a1 **)

let direction_rect f f0 f1 f2 = function
| In -> f
| Out -> f0
| InOut -> f1
| Directionless -> f2

(** val direction_rec : 'a1 -> 'a1 -> 'a1 -> 'a1 -> direction -> 'a1 **)

let direction_rec f f0 f1 f2 = function
| In -> f
| Out -> f0
| InOut -> f1
| Directionless -> f2

(** val eq_dir : direction -> direction -> bool **)

let eq_dir d1 d2 =
  match d1 with
  | In -> (match d2 with
           | In -> true
           | _ -> false)
  | Out -> (match d2 with
            | Out -> true
            | _ -> false)
  | InOut -> (match d2 with
              | InOut -> true
              | _ -> false)
  | Directionless -> (match d2 with
                      | Directionless -> true
                      | _ -> false)

type coq_FunctionKind =
| FunParser
| FunControl
| FunExtern
| FunTable
| FunAction
| FunFunction
| FunBuiltin

(** val coq_FunctionKind_rect :
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> coq_FunctionKind -> 'a1 **)

let coq_FunctionKind_rect f f0 f1 f2 f3 f4 f5 = function
| FunParser -> f
| FunControl -> f0
| FunExtern -> f1
| FunTable -> f2
| FunAction -> f3
| FunFunction -> f4
| FunBuiltin -> f5

(** val coq_FunctionKind_rec :
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> coq_FunctionKind -> 'a1 **)

let coq_FunctionKind_rec f f0 f1 f2 f3 f4 f5 = function
| FunParser -> f
| FunControl -> f0
| FunExtern -> f1
| FunTable -> f2
| FunAction -> f3
| FunFunction -> f4
| FunBuiltin -> f5

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

(** val coq_P4Type_rect :
    'a2 -> 'a2 -> 'a2 -> (int -> 'a2) -> (int -> 'a2) -> (int -> 'a2) -> ('a1
    coq_P4Type -> 'a2 -> int -> 'a2) -> ('a1 coq_P4Type list -> 'a2) -> ('a1
    coq_P4Type list -> 'a2) -> ('a1 coq_FieldType list -> 'a2) -> ('a1
    coq_P4Type -> 'a2 -> 'a2) -> 'a2 -> 'a2 -> 'a2 -> ('a1 coq_FieldType list
    -> 'a2) -> ('a1 coq_FieldType list -> 'a2) -> ('a1 coq_FieldType list ->
    'a2) -> ('a1 t -> 'a1 coq_P4Type option -> 'a1 t list -> 'a2) -> ('a1
    name -> 'a2) -> ('a1 t -> 'a1 coq_P4Type -> 'a2 -> 'a2) -> ('a1
    coq_ControlType -> 'a2) -> ('a1 coq_ControlType -> 'a2) -> ('a1 t -> 'a2)
    -> ('a1 coq_FunctionType -> 'a2) -> ('a1 coq_P4Parameter list -> 'a1
    coq_P4Parameter list -> 'a2) -> ('a1 t -> 'a2) -> ('a1 t list -> 'a1 t
    list -> 'a1 coq_P4Parameter list -> 'a2) -> ('a1 coq_P4Type -> 'a2 -> 'a1
    coq_P4Type list -> 'a2) -> ('a1 t list -> 'a1 t list -> 'a1
    coq_P4Parameter list -> 'a1 coq_P4Type -> 'a2 -> 'a2) -> 'a1 coq_P4Type
    -> 'a2 **)

let rec coq_P4Type_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 = function
| TypBool -> f
| TypString -> f0
| TypInteger -> f1
| TypInt width -> f2 width
| TypBit width -> f3 width
| TypVarBit width -> f4 width
| TypArray (typ, size) ->
  f5 typ
    (coq_P4Type_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
      f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 typ) size
| TypTuple types -> f6 types
| TypList types -> f7 types
| TypRecord fields -> f8 fields
| TypSet elt_type ->
  f9 elt_type
    (coq_P4Type_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
      f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 elt_type)
| TypError -> f10
| TypMatchKind -> f11
| TypVoid -> f12
| TypHeader fields -> f13 fields
| TypHeaderUnion fields -> f14 fields
| TypStruct fields -> f15 fields
| TypEnum (name0, typ, members) -> f16 name0 typ members
| TypTypeName name0 -> f17 name0
| TypNewType (name0, typ) ->
  f18 name0 typ
    (coq_P4Type_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
      f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 typ)
| TypControl c -> f19 c
| TypParser c -> f20 c
| TypExtern extern_name -> f21 extern_name
| TypFunction fn -> f22 fn
| TypAction (data_params, ctrl_params) -> f23 data_params ctrl_params
| TypTable result_typ_name -> f24 result_typ_name
| TypPackage (type_params, wildcard_params, parameters) ->
  f25 type_params wildcard_params parameters
| TypSpecializedType (base, args) ->
  f26 base
    (coq_P4Type_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
      f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 base) args
| TypConstructor (type_params, wildcard_params, parameters, ret) ->
  f27 type_params wildcard_params parameters ret
    (coq_P4Type_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
      f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 ret)

(** val coq_P4Type_rec :
    'a2 -> 'a2 -> 'a2 -> (int -> 'a2) -> (int -> 'a2) -> (int -> 'a2) -> ('a1
    coq_P4Type -> 'a2 -> int -> 'a2) -> ('a1 coq_P4Type list -> 'a2) -> ('a1
    coq_P4Type list -> 'a2) -> ('a1 coq_FieldType list -> 'a2) -> ('a1
    coq_P4Type -> 'a2 -> 'a2) -> 'a2 -> 'a2 -> 'a2 -> ('a1 coq_FieldType list
    -> 'a2) -> ('a1 coq_FieldType list -> 'a2) -> ('a1 coq_FieldType list ->
    'a2) -> ('a1 t -> 'a1 coq_P4Type option -> 'a1 t list -> 'a2) -> ('a1
    name -> 'a2) -> ('a1 t -> 'a1 coq_P4Type -> 'a2 -> 'a2) -> ('a1
    coq_ControlType -> 'a2) -> ('a1 coq_ControlType -> 'a2) -> ('a1 t -> 'a2)
    -> ('a1 coq_FunctionType -> 'a2) -> ('a1 coq_P4Parameter list -> 'a1
    coq_P4Parameter list -> 'a2) -> ('a1 t -> 'a2) -> ('a1 t list -> 'a1 t
    list -> 'a1 coq_P4Parameter list -> 'a2) -> ('a1 coq_P4Type -> 'a2 -> 'a1
    coq_P4Type list -> 'a2) -> ('a1 t list -> 'a1 t list -> 'a1
    coq_P4Parameter list -> 'a1 coq_P4Type -> 'a2 -> 'a2) -> 'a1 coq_P4Type
    -> 'a2 **)

let rec coq_P4Type_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 = function
| TypBool -> f
| TypString -> f0
| TypInteger -> f1
| TypInt width -> f2 width
| TypBit width -> f3 width
| TypVarBit width -> f4 width
| TypArray (typ, size) ->
  f5 typ
    (coq_P4Type_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
      f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 typ) size
| TypTuple types -> f6 types
| TypList types -> f7 types
| TypRecord fields -> f8 fields
| TypSet elt_type ->
  f9 elt_type
    (coq_P4Type_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
      f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 elt_type)
| TypError -> f10
| TypMatchKind -> f11
| TypVoid -> f12
| TypHeader fields -> f13 fields
| TypHeaderUnion fields -> f14 fields
| TypStruct fields -> f15 fields
| TypEnum (name0, typ, members) -> f16 name0 typ members
| TypTypeName name0 -> f17 name0
| TypNewType (name0, typ) ->
  f18 name0 typ
    (coq_P4Type_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
      f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 typ)
| TypControl c -> f19 c
| TypParser c -> f20 c
| TypExtern extern_name -> f21 extern_name
| TypFunction fn -> f22 fn
| TypAction (data_params, ctrl_params) -> f23 data_params ctrl_params
| TypTable result_typ_name -> f24 result_typ_name
| TypPackage (type_params, wildcard_params, parameters) ->
  f25 type_params wildcard_params parameters
| TypSpecializedType (base, args) ->
  f26 base
    (coq_P4Type_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
      f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 base) args
| TypConstructor (type_params, wildcard_params, parameters, ret) ->
  f27 type_params wildcard_params parameters ret
    (coq_P4Type_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
      f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 ret)

(** val coq_FieldType_rect :
    ('a1 t -> 'a1 coq_P4Type -> 'a2) -> 'a1 coq_FieldType -> 'a2 **)

let coq_FieldType_rect f = function
| MkFieldType (x, x0) -> f x x0

(** val coq_FieldType_rec :
    ('a1 t -> 'a1 coq_P4Type -> 'a2) -> 'a1 coq_FieldType -> 'a2 **)

let coq_FieldType_rec f = function
| MkFieldType (x, x0) -> f x x0

(** val coq_ControlType_rect :
    ('a1 t list -> 'a1 coq_P4Parameter list -> 'a2) -> 'a1 coq_ControlType ->
    'a2 **)

let coq_ControlType_rect f = function
| MkControlType (x, x0) -> f x x0

(** val coq_ControlType_rec :
    ('a1 t list -> 'a1 coq_P4Parameter list -> 'a2) -> 'a1 coq_ControlType ->
    'a2 **)

let coq_ControlType_rec f = function
| MkControlType (x, x0) -> f x x0

(** val coq_FunctionType_rect :
    ('a1 t list -> 'a1 coq_P4Parameter list -> coq_FunctionKind -> 'a1
    coq_P4Type -> 'a2) -> 'a1 coq_FunctionType -> 'a2 **)

let coq_FunctionType_rect f = function
| MkFunctionType (x, x0, x1, x2) -> f x x0 x1 x2

(** val coq_FunctionType_rec :
    ('a1 t list -> 'a1 coq_P4Parameter list -> coq_FunctionKind -> 'a1
    coq_P4Type -> 'a2) -> 'a1 coq_FunctionType -> 'a2 **)

let coq_FunctionType_rec f = function
| MkFunctionType (x, x0, x1, x2) -> f x x0 x1 x2

(** val coq_P4Parameter_rect :
    (bool -> direction -> 'a1 coq_P4Type -> int option -> 'a1 t -> 'a2) ->
    'a1 coq_P4Parameter -> 'a2 **)

let coq_P4Parameter_rect f = function
| MkParameter (x, x0, x1, x2, x3) -> f x x0 x1 x2 x3

(** val coq_P4Parameter_rec :
    (bool -> direction -> 'a1 coq_P4Type -> int option -> 'a1 t -> 'a2) ->
    'a1 coq_P4Parameter -> 'a2 **)

let coq_P4Parameter_rec f = function
| MkParameter (x, x0, x1, x2, x3) -> f x x0 x1 x2 x3

type coq_StmType =
| StmUnit
| StmVoid

(** val coq_StmType_rect : 'a1 -> 'a1 -> coq_StmType -> 'a1 **)

let coq_StmType_rect f f0 = function
| StmUnit -> f
| StmVoid -> f0

(** val coq_StmType_rec : 'a1 -> 'a1 -> coq_StmType -> 'a1 **)

let coq_StmType_rec f f0 = function
| StmUnit -> f
| StmVoid -> f0

type 'tags_t coq_StmtContext =
| StmtCxFunction of 'tags_t coq_P4Type
| StmtCxAction
| StmtCxParserState
| StmtCxApplyBlock

(** val coq_StmtContext_rect :
    ('a1 coq_P4Type -> 'a2) -> 'a2 -> 'a2 -> 'a2 -> 'a1 coq_StmtContext -> 'a2 **)

let coq_StmtContext_rect f f0 f1 f2 = function
| StmtCxFunction x -> f x
| StmtCxAction -> f0
| StmtCxParserState -> f1
| StmtCxApplyBlock -> f2

(** val coq_StmtContext_rec :
    ('a1 coq_P4Type -> 'a2) -> 'a2 -> 'a2 -> 'a2 -> 'a1 coq_StmtContext -> 'a2 **)

let coq_StmtContext_rec f f0 f1 f2 = function
| StmtCxFunction x -> f x
| StmtCxAction -> f0
| StmtCxParserState -> f1
| StmtCxApplyBlock -> f2

type 'tags_t coq_DeclContext =
| DeclCxTopLevel
| DeclCxNested
| DeclCxStatement of 'tags_t coq_StmtContext

(** val coq_DeclContext_rect :
    'a2 -> 'a2 -> ('a1 coq_StmtContext -> 'a2) -> 'a1 coq_DeclContext -> 'a2 **)

let coq_DeclContext_rect f f0 f1 = function
| DeclCxTopLevel -> f
| DeclCxNested -> f0
| DeclCxStatement x -> f1 x

(** val coq_DeclContext_rec :
    'a2 -> 'a2 -> ('a1 coq_StmtContext -> 'a2) -> 'a1 coq_DeclContext -> 'a2 **)

let coq_DeclContext_rec f f0 f1 = function
| DeclCxTopLevel -> f
| DeclCxNested -> f0
| DeclCxStatement x -> f1 x

type coq_ParamContextDeclaration =
| ParamCxDeclParser
| ParamCxDeclControl
| ParamCxDeclMethod
| ParamCxDeclAction
| ParamCxDeclFunction
| ParamCxDeclPackage

(** val coq_ParamContextDeclaration_rect :
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> coq_ParamContextDeclaration ->
    'a1 **)

let coq_ParamContextDeclaration_rect f f0 f1 f2 f3 f4 = function
| ParamCxDeclParser -> f
| ParamCxDeclControl -> f0
| ParamCxDeclMethod -> f1
| ParamCxDeclAction -> f2
| ParamCxDeclFunction -> f3
| ParamCxDeclPackage -> f4

(** val coq_ParamContextDeclaration_rec :
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> coq_ParamContextDeclaration ->
    'a1 **)

let coq_ParamContextDeclaration_rec f f0 f1 f2 f3 f4 = function
| ParamCxDeclParser -> f
| ParamCxDeclControl -> f0
| ParamCxDeclMethod -> f1
| ParamCxDeclAction -> f2
| ParamCxDeclFunction -> f3
| ParamCxDeclPackage -> f4

type coq_ParamContext =
| ParamCxRuntime of coq_ParamContextDeclaration
| ParamCxConstructor of coq_ParamContextDeclaration

(** val coq_ParamContext_rect :
    (coq_ParamContextDeclaration -> 'a1) -> (coq_ParamContextDeclaration ->
    'a1) -> coq_ParamContext -> 'a1 **)

let coq_ParamContext_rect f f0 = function
| ParamCxRuntime x -> f x
| ParamCxConstructor x -> f0 x

(** val coq_ParamContext_rec :
    (coq_ParamContextDeclaration -> 'a1) -> (coq_ParamContextDeclaration ->
    'a1) -> coq_ParamContext -> 'a1 **)

let coq_ParamContext_rec f f0 = function
| ParamCxRuntime x -> f x
| ParamCxConstructor x -> f0 x

type coq_ExprContext =
| ExprCxParserState
| ExprCxApplyBlock
| ExprCxDeclLocals
| ExprCxTableAction
| ExprCxAction
| ExprCxFunction
| ExprCxConstant

(** val coq_ExprContext_rect :
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> coq_ExprContext -> 'a1 **)

let coq_ExprContext_rect f f0 f1 f2 f3 f4 f5 = function
| ExprCxParserState -> f
| ExprCxApplyBlock -> f0
| ExprCxDeclLocals -> f1
| ExprCxTableAction -> f2
| ExprCxAction -> f3
| ExprCxFunction -> f4
| ExprCxConstant -> f5

(** val coq_ExprContext_rec :
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> coq_ExprContext -> 'a1 **)

let coq_ExprContext_rec f f0 f1 f2 f3 f4 f5 = function
| ExprCxParserState -> f
| ExprCxApplyBlock -> f0
| ExprCxDeclLocals -> f1
| ExprCxTableAction -> f2
| ExprCxAction -> f3
| ExprCxFunction -> f4
| ExprCxConstant -> f5
