open Datatypes
open P4Int
open P4String
open Typed
open Utils

type 'tags_t coq_MethodPrototype =
| ProtoConstructor of 'tags_t * 'tags_t t * 'tags_t coq_P4Parameter list
| ProtoAbstractMethod of 'tags_t * 'tags_t coq_P4Type * 'tags_t t
   * 'tags_t t list * 'tags_t coq_P4Parameter list
| ProtoMethod of 'tags_t * 'tags_t coq_P4Type * 'tags_t t * 'tags_t t list
   * 'tags_t coq_P4Parameter list

val coq_MethodPrototype_rect :
  ('a1 -> 'a1 t -> 'a1 coq_P4Parameter list -> 'a2) -> ('a1 -> 'a1 coq_P4Type
  -> 'a1 t -> 'a1 t list -> 'a1 coq_P4Parameter list -> 'a2) -> ('a1 -> 'a1
  coq_P4Type -> 'a1 t -> 'a1 t list -> 'a1 coq_P4Parameter list -> 'a2) ->
  'a1 coq_MethodPrototype -> 'a2

val coq_MethodPrototype_rec :
  ('a1 -> 'a1 t -> 'a1 coq_P4Parameter list -> 'a2) -> ('a1 -> 'a1 coq_P4Type
  -> 'a1 t -> 'a1 t list -> 'a1 coq_P4Parameter list -> 'a2) -> ('a1 -> 'a1
  coq_P4Type -> 'a1 t -> 'a1 t list -> 'a1 coq_P4Parameter list -> 'a2) ->
  'a1 coq_MethodPrototype -> 'a2

type coq_OpUni =
| Not
| BitNot
| UMinus

val coq_OpUni_rect : 'a1 -> 'a1 -> 'a1 -> coq_OpUni -> 'a1

val coq_OpUni_rec : 'a1 -> 'a1 -> 'a1 -> coq_OpUni -> 'a1

type coq_OpBin =
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
| Or

val coq_OpBin_rect :
  'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
  -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
  coq_OpBin -> 'a1

val coq_OpBin_rec :
  'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
  -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
  coq_OpBin -> 'a1

type 'tags_t coq_KeyValue =
| MkKeyValue of 'tags_t * 'tags_t t * 'tags_t coq_Expression
and 'tags_t coq_ExpressionPreT =
| ExpBool of bool
| ExpInt of 'tags_t P4Int.t
| ExpString of 'tags_t t
| ExpName of 'tags_t name
| ExpArrayAccess of 'tags_t coq_Expression * 'tags_t coq_Expression
| ExpBitStringAccess of 'tags_t coq_Expression * Bigint.t * Bigint.t
| ExpList of 'tags_t coq_Expression list
| ExpRecord of 'tags_t coq_KeyValue list
| ExpUnaryOp of coq_OpUni * 'tags_t coq_Expression
| ExpBinaryOp of coq_OpBin * ('tags_t coq_Expression * 'tags_t coq_Expression)
| ExpCast of 'tags_t coq_P4Type * 'tags_t coq_Expression
| ExpTypeMember of 'tags_t name * 'tags_t t
| ExpErrorMember of 'tags_t t
| ExpExpressionMember of 'tags_t coq_Expression * 'tags_t t
| ExpTernary of 'tags_t coq_Expression * 'tags_t coq_Expression
   * 'tags_t coq_Expression
| ExpFunctionCall of 'tags_t coq_Expression * 'tags_t coq_P4Type list
   * 'tags_t coq_Expression option list
| ExpNamelessInstantiation of 'tags_t coq_P4Type * 'tags_t coq_Expression list
| ExpDontCare
| ExpMask of 'tags_t coq_Expression * 'tags_t coq_Expression
| ExpRange of 'tags_t coq_Expression * 'tags_t coq_Expression
and 'tags_t coq_Expression =
| MkExpression of 'tags_t * 'tags_t coq_ExpressionPreT * 'tags_t coq_P4Type
   * direction

val coq_KeyValue_rect :
  ('a1 -> 'a1 t -> 'a1 coq_Expression -> 'a2) -> 'a1 coq_KeyValue -> 'a2

val coq_KeyValue_rec :
  ('a1 -> 'a1 t -> 'a1 coq_Expression -> 'a2) -> 'a1 coq_KeyValue -> 'a2

val coq_ExpressionPreT_rect :
  (bool -> 'a2) -> ('a1 P4Int.t -> 'a2) -> ('a1 t -> 'a2) -> ('a1 name ->
  'a2) -> ('a1 coq_Expression -> 'a1 coq_Expression -> 'a2) -> ('a1
  coq_Expression -> Bigint.t -> Bigint.t -> 'a2) -> ('a1 coq_Expression list
  -> 'a2) -> ('a1 coq_KeyValue list -> 'a2) -> (coq_OpUni -> 'a1
  coq_Expression -> 'a2) -> (coq_OpBin -> ('a1 coq_Expression * 'a1
  coq_Expression) -> 'a2) -> ('a1 coq_P4Type -> 'a1 coq_Expression -> 'a2) ->
  ('a1 name -> 'a1 t -> 'a2) -> ('a1 t -> 'a2) -> ('a1 coq_Expression -> 'a1
  t -> 'a2) -> ('a1 coq_Expression -> 'a1 coq_Expression -> 'a1
  coq_Expression -> 'a2) -> ('a1 coq_Expression -> 'a1 coq_P4Type list -> 'a1
  coq_Expression option list -> 'a2) -> ('a1 coq_P4Type -> 'a1 coq_Expression
  list -> 'a2) -> 'a2 -> ('a1 coq_Expression -> 'a1 coq_Expression -> 'a2) ->
  ('a1 coq_Expression -> 'a1 coq_Expression -> 'a2) -> 'a1 coq_ExpressionPreT
  -> 'a2

val coq_ExpressionPreT_rec :
  (bool -> 'a2) -> ('a1 P4Int.t -> 'a2) -> ('a1 t -> 'a2) -> ('a1 name ->
  'a2) -> ('a1 coq_Expression -> 'a1 coq_Expression -> 'a2) -> ('a1
  coq_Expression -> Bigint.t -> Bigint.t -> 'a2) -> ('a1 coq_Expression list
  -> 'a2) -> ('a1 coq_KeyValue list -> 'a2) -> (coq_OpUni -> 'a1
  coq_Expression -> 'a2) -> (coq_OpBin -> ('a1 coq_Expression * 'a1
  coq_Expression) -> 'a2) -> ('a1 coq_P4Type -> 'a1 coq_Expression -> 'a2) ->
  ('a1 name -> 'a1 t -> 'a2) -> ('a1 t -> 'a2) -> ('a1 coq_Expression -> 'a1
  t -> 'a2) -> ('a1 coq_Expression -> 'a1 coq_Expression -> 'a1
  coq_Expression -> 'a2) -> ('a1 coq_Expression -> 'a1 coq_P4Type list -> 'a1
  coq_Expression option list -> 'a2) -> ('a1 coq_P4Type -> 'a1 coq_Expression
  list -> 'a2) -> 'a2 -> ('a1 coq_Expression -> 'a1 coq_Expression -> 'a2) ->
  ('a1 coq_Expression -> 'a1 coq_Expression -> 'a2) -> 'a1 coq_ExpressionPreT
  -> 'a2

val coq_Expression_rect :
  ('a1 -> 'a1 coq_ExpressionPreT -> 'a1 coq_P4Type -> direction -> 'a2) ->
  'a1 coq_Expression -> 'a2

val coq_Expression_rec :
  ('a1 -> 'a1 coq_ExpressionPreT -> 'a1 coq_P4Type -> direction -> 'a2) ->
  'a1 coq_Expression -> 'a2

type 'tags_t coq_MatchPreT =
| MatchDontCare
| MatchExpression of 'tags_t coq_Expression

val coq_MatchPreT_rect :
  'a2 -> ('a1 coq_Expression -> 'a2) -> 'a1 coq_MatchPreT -> 'a2

val coq_MatchPreT_rec :
  'a2 -> ('a1 coq_Expression -> 'a2) -> 'a1 coq_MatchPreT -> 'a2

type 'tags_t coq_Match =
| MkMatch of 'tags_t * 'tags_t coq_MatchPreT * 'tags_t coq_P4Type

val coq_Match_rect :
  ('a1 -> 'a1 coq_MatchPreT -> 'a1 coq_P4Type -> 'a2) -> 'a1 coq_Match -> 'a2

val coq_Match_rec :
  ('a1 -> 'a1 coq_MatchPreT -> 'a1 coq_P4Type -> 'a2) -> 'a1 coq_Match -> 'a2

type 'tags_t coq_TablePreActionRef =
| MkTablePreActionRef of 'tags_t name * 'tags_t coq_Expression option list

val coq_TablePreActionRef_rect :
  ('a1 name -> 'a1 coq_Expression option list -> 'a2) -> 'a1
  coq_TablePreActionRef -> 'a2

val coq_TablePreActionRef_rec :
  ('a1 name -> 'a1 coq_Expression option list -> 'a2) -> 'a1
  coq_TablePreActionRef -> 'a2

type 'tags_t coq_TableActionRef =
| MkTableActionRef of 'tags_t * 'tags_t coq_TablePreActionRef
   * 'tags_t coq_P4Type

val coq_TableActionRef_rect :
  ('a1 -> 'a1 coq_TablePreActionRef -> 'a1 coq_P4Type -> 'a2) -> 'a1
  coq_TableActionRef -> 'a2

val coq_TableActionRef_rec :
  ('a1 -> 'a1 coq_TablePreActionRef -> 'a1 coq_P4Type -> 'a2) -> 'a1
  coq_TableActionRef -> 'a2

type 'tags_t coq_TableKey =
| MkTableKey of 'tags_t * 'tags_t coq_Expression * 'tags_t t

val coq_TableKey_rect :
  ('a1 -> 'a1 coq_Expression -> 'a1 t -> 'a2) -> 'a1 coq_TableKey -> 'a2

val coq_TableKey_rec :
  ('a1 -> 'a1 coq_Expression -> 'a1 t -> 'a2) -> 'a1 coq_TableKey -> 'a2

type 'tags_t coq_TableEntry =
| MkTableEntry of 'tags_t * 'tags_t coq_Match list
   * 'tags_t coq_TableActionRef

val coq_TableEntry_rect :
  ('a1 -> 'a1 coq_Match list -> 'a1 coq_TableActionRef -> 'a2) -> 'a1
  coq_TableEntry -> 'a2

val coq_TableEntry_rec :
  ('a1 -> 'a1 coq_Match list -> 'a1 coq_TableActionRef -> 'a2) -> 'a1
  coq_TableEntry -> 'a2

type 'tags_t coq_TableProperty =
| MkTableProperty of 'tags_t * bool * 'tags_t t * 'tags_t coq_Expression

val coq_TableProperty_rect :
  ('a1 -> bool -> 'a1 t -> 'a1 coq_Expression -> 'a2) -> 'a1
  coq_TableProperty -> 'a2

val coq_TableProperty_rec :
  ('a1 -> bool -> 'a1 t -> 'a1 coq_Expression -> 'a2) -> 'a1
  coq_TableProperty -> 'a2

type 'tags_t coq_ValueBase =
| ValBaseNull
| ValBaseBool of bool
| ValBaseInteger of Bigint.t
| ValBaseBit of int * Bigint.t
| ValBaseInt of int * Bigint.t
| ValBaseVarbit of int * int * Bigint.t
| ValBaseString of 'tags_t t
| ValBaseTuple of 'tags_t coq_ValueBase list
| ValBaseRecord of ('tags_t, 'tags_t coq_ValueBase) coq_AList
| ValBaseSet of 'tags_t coq_ValueSet
| ValBaseError of 'tags_t t
| ValBaseMatchKind of 'tags_t t
| ValBaseStruct of ('tags_t, 'tags_t coq_ValueBase) coq_AList
| ValBaseHeader of ('tags_t, 'tags_t coq_ValueBase) coq_AList * bool
| ValBaseUnion of ('tags_t, 'tags_t coq_ValueBase) coq_AList
| ValBaseStack of 'tags_t coq_ValueBase list * int * int
| ValBaseEnumField of 'tags_t t * 'tags_t t
| ValBaseSenumField of 'tags_t t * 'tags_t t * 'tags_t coq_ValueBase
| ValBaseSenum of ('tags_t, 'tags_t coq_ValueBase) coq_AList
and 'tags_t coq_ValueSet =
| ValSetSingleton of int * Bigint.t
| ValSetUniversal
| ValSetMask of 'tags_t coq_ValueBase * 'tags_t coq_ValueBase
| ValSetRange of 'tags_t coq_ValueBase * 'tags_t coq_ValueBase
| ValSetProd of 'tags_t coq_ValueSet list
| ValSetLpm of 'tags_t coq_ValueBase * int * 'tags_t coq_ValueBase
| ValSetValueSet of 'tags_t coq_ValueBase * 'tags_t coq_Match list list
   * 'tags_t coq_ValueSet list

val coq_ValueBase_rect :
  'a2 -> (bool -> 'a2) -> (Bigint.t -> 'a2) -> (int -> Bigint.t -> 'a2) ->
  (int -> Bigint.t -> 'a2) -> (int -> int -> Bigint.t -> 'a2) -> ('a1 t ->
  'a2) -> ('a1 coq_ValueBase list -> 'a2) -> (('a1, 'a1 coq_ValueBase)
  coq_AList -> 'a2) -> ('a1 coq_ValueSet -> 'a2) -> ('a1 t -> 'a2) -> ('a1 t
  -> 'a2) -> (('a1, 'a1 coq_ValueBase) coq_AList -> 'a2) -> (('a1, 'a1
  coq_ValueBase) coq_AList -> bool -> 'a2) -> (('a1, 'a1 coq_ValueBase)
  coq_AList -> 'a2) -> ('a1 coq_ValueBase list -> int -> int -> 'a2) -> ('a1
  t -> 'a1 t -> 'a2) -> ('a1 t -> 'a1 t -> 'a1 coq_ValueBase -> 'a2 -> 'a2)
  -> (('a1, 'a1 coq_ValueBase) coq_AList -> 'a2) -> 'a1 coq_ValueBase -> 'a2

val coq_ValueBase_rec :
  'a2 -> (bool -> 'a2) -> (Bigint.t -> 'a2) -> (int -> Bigint.t -> 'a2) ->
  (int -> Bigint.t -> 'a2) -> (int -> int -> Bigint.t -> 'a2) -> ('a1 t ->
  'a2) -> ('a1 coq_ValueBase list -> 'a2) -> (('a1, 'a1 coq_ValueBase)
  coq_AList -> 'a2) -> ('a1 coq_ValueSet -> 'a2) -> ('a1 t -> 'a2) -> ('a1 t
  -> 'a2) -> (('a1, 'a1 coq_ValueBase) coq_AList -> 'a2) -> (('a1, 'a1
  coq_ValueBase) coq_AList -> bool -> 'a2) -> (('a1, 'a1 coq_ValueBase)
  coq_AList -> 'a2) -> ('a1 coq_ValueBase list -> int -> int -> 'a2) -> ('a1
  t -> 'a1 t -> 'a2) -> ('a1 t -> 'a1 t -> 'a1 coq_ValueBase -> 'a2 -> 'a2)
  -> (('a1, 'a1 coq_ValueBase) coq_AList -> 'a2) -> 'a1 coq_ValueBase -> 'a2

val coq_ValueSet_rect :
  (int -> Bigint.t -> 'a2) -> 'a2 -> ('a1 coq_ValueBase -> 'a1 coq_ValueBase
  -> 'a2) -> ('a1 coq_ValueBase -> 'a1 coq_ValueBase -> 'a2) -> ('a1
  coq_ValueSet list -> 'a2) -> ('a1 coq_ValueBase -> int -> 'a1 coq_ValueBase
  -> 'a2) -> ('a1 coq_ValueBase -> 'a1 coq_Match list list -> 'a1
  coq_ValueSet list -> 'a2) -> 'a1 coq_ValueSet -> 'a2

val coq_ValueSet_rec :
  (int -> Bigint.t -> 'a2) -> 'a2 -> ('a1 coq_ValueBase -> 'a1 coq_ValueBase
  -> 'a2) -> ('a1 coq_ValueBase -> 'a1 coq_ValueBase -> 'a2) -> ('a1
  coq_ValueSet list -> 'a2) -> ('a1 coq_ValueBase -> int -> 'a1 coq_ValueBase
  -> 'a2) -> ('a1 coq_ValueBase -> 'a1 coq_Match list list -> 'a1
  coq_ValueSet list -> 'a2) -> 'a1 coq_ValueSet -> 'a2

type 'tags_t coq_StatementSwitchLabel =
| StatSwLabDefault of 'tags_t
| StatSwLabName of 'tags_t * 'tags_t t

val coq_StatementSwitchLabel_rect :
  ('a1 -> 'a2) -> ('a1 -> 'a1 t -> 'a2) -> 'a1 coq_StatementSwitchLabel -> 'a2

val coq_StatementSwitchLabel_rec :
  ('a1 -> 'a2) -> ('a1 -> 'a1 t -> 'a2) -> 'a1 coq_StatementSwitchLabel -> 'a2

type 'tags_t coq_StatementSwitchCase =
| StatSwCaseAction of 'tags_t * 'tags_t coq_StatementSwitchLabel
   * 'tags_t coq_Block
| StatSwCaseFallThrough of 'tags_t * 'tags_t coq_StatementSwitchLabel
and 'tags_t coq_StatementPreT =
| StatMethodCall of 'tags_t coq_Expression * 'tags_t coq_P4Type list
   * 'tags_t coq_Expression option list
| StatAssignment of 'tags_t coq_Expression * 'tags_t coq_Expression
| StatDirectApplication of 'tags_t coq_P4Type * 'tags_t coq_Expression list
| StatConditional of 'tags_t coq_Expression * 'tags_t coq_Statement
   * 'tags_t coq_Statement option
| StatBlock of 'tags_t coq_Block
| StatExit
| StatEmpty
| StatReturn of 'tags_t coq_Expression option
| StatSwitch of 'tags_t coq_Expression * 'tags_t coq_StatementSwitchCase list
| StatConstant of 'tags_t coq_P4Type * 'tags_t t * 'tags_t coq_ValueBase
| StatVariable of 'tags_t coq_P4Type * 'tags_t t
   * 'tags_t coq_Expression option
| StatInstantiation of 'tags_t coq_P4Type * 'tags_t coq_Expression list
   * 'tags_t t * 'tags_t coq_Block option
and 'tags_t coq_Statement =
| MkStatement of 'tags_t * 'tags_t coq_StatementPreT * coq_StmType
and 'tags_t coq_Block =
| BlockEmpty of 'tags_t
| BlockCons of 'tags_t coq_Statement * 'tags_t coq_Block

val coq_StatementSwitchCase_rect :
  ('a1 -> 'a1 coq_StatementSwitchLabel -> 'a1 coq_Block -> 'a2) -> ('a1 ->
  'a1 coq_StatementSwitchLabel -> 'a2) -> 'a1 coq_StatementSwitchCase -> 'a2

val coq_StatementSwitchCase_rec :
  ('a1 -> 'a1 coq_StatementSwitchLabel -> 'a1 coq_Block -> 'a2) -> ('a1 ->
  'a1 coq_StatementSwitchLabel -> 'a2) -> 'a1 coq_StatementSwitchCase -> 'a2

val coq_StatementPreT_rect :
  ('a1 coq_Expression -> 'a1 coq_P4Type list -> 'a1 coq_Expression option
  list -> 'a2) -> ('a1 coq_Expression -> 'a1 coq_Expression -> 'a2) -> ('a1
  coq_P4Type -> 'a1 coq_Expression list -> 'a2) -> ('a1 coq_Expression -> 'a1
  coq_Statement -> 'a1 coq_Statement option -> 'a2) -> ('a1 coq_Block -> 'a2)
  -> 'a2 -> 'a2 -> ('a1 coq_Expression option -> 'a2) -> ('a1 coq_Expression
  -> 'a1 coq_StatementSwitchCase list -> 'a2) -> ('a1 coq_P4Type -> 'a1 t ->
  'a1 coq_ValueBase -> 'a2) -> ('a1 coq_P4Type -> 'a1 t -> 'a1 coq_Expression
  option -> 'a2) -> ('a1 coq_P4Type -> 'a1 coq_Expression list -> 'a1 t ->
  'a1 coq_Block option -> 'a2) -> 'a1 coq_StatementPreT -> 'a2

val coq_StatementPreT_rec :
  ('a1 coq_Expression -> 'a1 coq_P4Type list -> 'a1 coq_Expression option
  list -> 'a2) -> ('a1 coq_Expression -> 'a1 coq_Expression -> 'a2) -> ('a1
  coq_P4Type -> 'a1 coq_Expression list -> 'a2) -> ('a1 coq_Expression -> 'a1
  coq_Statement -> 'a1 coq_Statement option -> 'a2) -> ('a1 coq_Block -> 'a2)
  -> 'a2 -> 'a2 -> ('a1 coq_Expression option -> 'a2) -> ('a1 coq_Expression
  -> 'a1 coq_StatementSwitchCase list -> 'a2) -> ('a1 coq_P4Type -> 'a1 t ->
  'a1 coq_ValueBase -> 'a2) -> ('a1 coq_P4Type -> 'a1 t -> 'a1 coq_Expression
  option -> 'a2) -> ('a1 coq_P4Type -> 'a1 coq_Expression list -> 'a1 t ->
  'a1 coq_Block option -> 'a2) -> 'a1 coq_StatementPreT -> 'a2

val coq_Statement_rect :
  ('a1 -> 'a1 coq_StatementPreT -> coq_StmType -> 'a2) -> 'a1 coq_Statement
  -> 'a2

val coq_Statement_rec :
  ('a1 -> 'a1 coq_StatementPreT -> coq_StmType -> 'a2) -> 'a1 coq_Statement
  -> 'a2

val coq_Block_rect :
  ('a1 -> 'a2) -> ('a1 coq_Statement -> 'a1 coq_Block -> 'a2 -> 'a2) -> 'a1
  coq_Block -> 'a2

val coq_Block_rec :
  ('a1 -> 'a2) -> ('a1 coq_Statement -> 'a1 coq_Block -> 'a2 -> 'a2) -> 'a1
  coq_Block -> 'a2

val statement_rec :
  ('a1 -> 'a1 coq_StatementSwitchLabel -> 'a1 coq_Block -> 'a7 -> 'a2) ->
  ('a1 -> 'a1 coq_StatementSwitchLabel -> 'a2) -> 'a3 -> ('a1
  coq_StatementSwitchCase -> 'a1 coq_StatementSwitchCase list -> 'a2 -> 'a3
  -> 'a3) -> ('a1 coq_Expression -> 'a1 coq_P4Type list -> 'a1 coq_Expression
  option list -> 'a4) -> ('a1 coq_Expression -> 'a1 coq_Expression -> 'a4) ->
  ('a1 coq_P4Type -> 'a1 coq_Expression list -> 'a4) -> ('a1 coq_Expression
  -> 'a1 coq_Statement -> 'a1 coq_Statement option -> 'a5 -> 'a6 -> 'a4) ->
  ('a1 coq_Block -> 'a7 -> 'a4) -> 'a4 -> 'a4 -> ('a1 coq_Expression option
  -> 'a4) -> ('a1 coq_Expression -> 'a1 coq_StatementSwitchCase list -> 'a3
  -> 'a4) -> ('a1 coq_P4Type -> 'a1 t -> 'a1 coq_ValueBase -> 'a4) -> ('a1
  coq_P4Type -> 'a1 t -> 'a1 coq_Expression option -> 'a4) -> ('a1 coq_P4Type
  -> 'a1 coq_Expression list -> 'a1 t -> 'a1 coq_Block option -> 'a8 -> 'a4)
  -> ('a1 -> 'a1 coq_StatementPreT -> coq_StmType -> 'a4 -> 'a5) -> 'a6 ->
  ('a1 coq_Statement -> 'a5 -> 'a6) -> ('a1 -> 'a7) -> ('a1 coq_Statement ->
  'a1 coq_Block -> 'a5 -> 'a7 -> 'a7) -> 'a8 -> ('a1 coq_Block -> 'a7 -> 'a8)
  -> 'a1 coq_Statement -> 'a5

val statement_pre_t_rec :
  ('a1 -> 'a1 coq_StatementSwitchLabel -> 'a1 coq_Block -> 'a7 -> 'a2) ->
  ('a1 -> 'a1 coq_StatementSwitchLabel -> 'a2) -> 'a3 -> ('a1
  coq_StatementSwitchCase -> 'a1 coq_StatementSwitchCase list -> 'a2 -> 'a3
  -> 'a3) -> ('a1 coq_Expression -> 'a1 coq_P4Type list -> 'a1 coq_Expression
  option list -> 'a4) -> ('a1 coq_Expression -> 'a1 coq_Expression -> 'a4) ->
  ('a1 coq_P4Type -> 'a1 coq_Expression list -> 'a4) -> ('a1 coq_Expression
  -> 'a1 coq_Statement -> 'a1 coq_Statement option -> 'a5 -> 'a6 -> 'a4) ->
  ('a1 coq_Block -> 'a7 -> 'a4) -> 'a4 -> 'a4 -> ('a1 coq_Expression option
  -> 'a4) -> ('a1 coq_Expression -> 'a1 coq_StatementSwitchCase list -> 'a3
  -> 'a4) -> ('a1 coq_P4Type -> 'a1 t -> 'a1 coq_ValueBase -> 'a4) -> ('a1
  coq_P4Type -> 'a1 t -> 'a1 coq_Expression option -> 'a4) -> ('a1 coq_P4Type
  -> 'a1 coq_Expression list -> 'a1 t -> 'a1 coq_Block option -> 'a8 -> 'a4)
  -> ('a1 -> 'a1 coq_StatementPreT -> coq_StmType -> 'a4 -> 'a5) -> 'a6 ->
  ('a1 coq_Statement -> 'a5 -> 'a6) -> ('a1 -> 'a7) -> ('a1 coq_Statement ->
  'a1 coq_Block -> 'a5 -> 'a7 -> 'a7) -> 'a8 -> ('a1 coq_Block -> 'a7 -> 'a8)
  -> 'a1 coq_StatementPreT -> 'a4

val statement_switch_case_rec :
  ('a1 -> 'a1 coq_StatementSwitchLabel -> 'a1 coq_Block -> 'a7 -> 'a2) ->
  ('a1 -> 'a1 coq_StatementSwitchLabel -> 'a2) -> 'a3 -> ('a1
  coq_StatementSwitchCase -> 'a1 coq_StatementSwitchCase list -> 'a2 -> 'a3
  -> 'a3) -> ('a1 coq_Expression -> 'a1 coq_P4Type list -> 'a1 coq_Expression
  option list -> 'a4) -> ('a1 coq_Expression -> 'a1 coq_Expression -> 'a4) ->
  ('a1 coq_P4Type -> 'a1 coq_Expression list -> 'a4) -> ('a1 coq_Expression
  -> 'a1 coq_Statement -> 'a1 coq_Statement option -> 'a5 -> 'a6 -> 'a4) ->
  ('a1 coq_Block -> 'a7 -> 'a4) -> 'a4 -> 'a4 -> ('a1 coq_Expression option
  -> 'a4) -> ('a1 coq_Expression -> 'a1 coq_StatementSwitchCase list -> 'a3
  -> 'a4) -> ('a1 coq_P4Type -> 'a1 t -> 'a1 coq_ValueBase -> 'a4) -> ('a1
  coq_P4Type -> 'a1 t -> 'a1 coq_Expression option -> 'a4) -> ('a1 coq_P4Type
  -> 'a1 coq_Expression list -> 'a1 t -> 'a1 coq_Block option -> 'a8 -> 'a4)
  -> ('a1 -> 'a1 coq_StatementPreT -> coq_StmType -> 'a4 -> 'a5) -> 'a6 ->
  ('a1 coq_Statement -> 'a5 -> 'a6) -> ('a1 -> 'a7) -> ('a1 coq_Statement ->
  'a1 coq_Block -> 'a5 -> 'a7 -> 'a7) -> 'a8 -> ('a1 coq_Block -> 'a7 -> 'a8)
  -> 'a1 coq_StatementSwitchCase -> 'a2

val block_rec :
  ('a1 -> 'a1 coq_StatementSwitchLabel -> 'a1 coq_Block -> 'a7 -> 'a2) ->
  ('a1 -> 'a1 coq_StatementSwitchLabel -> 'a2) -> 'a3 -> ('a1
  coq_StatementSwitchCase -> 'a1 coq_StatementSwitchCase list -> 'a2 -> 'a3
  -> 'a3) -> ('a1 coq_Expression -> 'a1 coq_P4Type list -> 'a1 coq_Expression
  option list -> 'a4) -> ('a1 coq_Expression -> 'a1 coq_Expression -> 'a4) ->
  ('a1 coq_P4Type -> 'a1 coq_Expression list -> 'a4) -> ('a1 coq_Expression
  -> 'a1 coq_Statement -> 'a1 coq_Statement option -> 'a5 -> 'a6 -> 'a4) ->
  ('a1 coq_Block -> 'a7 -> 'a4) -> 'a4 -> 'a4 -> ('a1 coq_Expression option
  -> 'a4) -> ('a1 coq_Expression -> 'a1 coq_StatementSwitchCase list -> 'a3
  -> 'a4) -> ('a1 coq_P4Type -> 'a1 t -> 'a1 coq_ValueBase -> 'a4) -> ('a1
  coq_P4Type -> 'a1 t -> 'a1 coq_Expression option -> 'a4) -> ('a1 coq_P4Type
  -> 'a1 coq_Expression list -> 'a1 t -> 'a1 coq_Block option -> 'a8 -> 'a4)
  -> ('a1 -> 'a1 coq_StatementPreT -> coq_StmType -> 'a4 -> 'a5) -> 'a6 ->
  ('a1 coq_Statement -> 'a5 -> 'a6) -> ('a1 -> 'a7) -> ('a1 coq_Statement ->
  'a1 coq_Block -> 'a5 -> 'a7 -> 'a7) -> 'a8 -> ('a1 coq_Block -> 'a7 -> 'a8)
  -> 'a1 coq_Block -> 'a7

type 'tags_t coq_ParserCase =
| MkParserCase of 'tags_t * 'tags_t coq_Match list * 'tags_t t

val coq_ParserCase_rect :
  ('a1 -> 'a1 coq_Match list -> 'a1 t -> 'a2) -> 'a1 coq_ParserCase -> 'a2

val coq_ParserCase_rec :
  ('a1 -> 'a1 coq_Match list -> 'a1 t -> 'a2) -> 'a1 coq_ParserCase -> 'a2

type 'tags_t coq_ParserTransition =
| ParserDirect of 'tags_t * 'tags_t t
| ParserSelect of 'tags_t * 'tags_t coq_Expression list
   * 'tags_t coq_ParserCase list

val coq_ParserTransition_rect :
  ('a1 -> 'a1 t -> 'a2) -> ('a1 -> 'a1 coq_Expression list -> 'a1
  coq_ParserCase list -> 'a2) -> 'a1 coq_ParserTransition -> 'a2

val coq_ParserTransition_rec :
  ('a1 -> 'a1 t -> 'a2) -> ('a1 -> 'a1 coq_Expression list -> 'a1
  coq_ParserCase list -> 'a2) -> 'a1 coq_ParserTransition -> 'a2

type 'tags_t coq_ParserState =
| MkParserState of 'tags_t * 'tags_t t * 'tags_t coq_Statement list
   * 'tags_t coq_ParserTransition

val coq_ParserState_rect :
  ('a1 -> 'a1 t -> 'a1 coq_Statement list -> 'a1 coq_ParserTransition -> 'a2)
  -> 'a1 coq_ParserState -> 'a2

val coq_ParserState_rec :
  ('a1 -> 'a1 t -> 'a1 coq_Statement list -> 'a1 coq_ParserTransition -> 'a2)
  -> 'a1 coq_ParserState -> 'a2

type 'tags_t coq_DeclarationField =
| MkDeclarationField of 'tags_t * 'tags_t coq_P4Type * 'tags_t t

val coq_DeclarationField_rect :
  ('a1 -> 'a1 coq_P4Type -> 'a1 t -> 'a2) -> 'a1 coq_DeclarationField -> 'a2

val coq_DeclarationField_rec :
  ('a1 -> 'a1 coq_P4Type -> 'a1 t -> 'a2) -> 'a1 coq_DeclarationField -> 'a2

type 'tags_t coq_Declaration =
| DeclConstant of 'tags_t * 'tags_t coq_P4Type * 'tags_t t
   * 'tags_t coq_ValueBase
| DeclInstantiation of 'tags_t * 'tags_t coq_P4Type
   * 'tags_t coq_Expression list * 'tags_t t * 'tags_t coq_Block option
| DeclParser of 'tags_t * 'tags_t t * 'tags_t t list
   * 'tags_t coq_P4Parameter list * 'tags_t coq_P4Parameter list
   * 'tags_t coq_Declaration list * 'tags_t coq_ParserState list
| DeclControl of 'tags_t * 'tags_t t * 'tags_t t list
   * 'tags_t coq_P4Parameter list * 'tags_t coq_P4Parameter list
   * 'tags_t coq_Declaration list * 'tags_t coq_Block
| DeclFunction of 'tags_t * 'tags_t coq_P4Type * 'tags_t t * 'tags_t t list
   * 'tags_t coq_P4Parameter list * 'tags_t coq_Block
| DeclExternFunction of 'tags_t * 'tags_t coq_P4Type * 'tags_t t
   * 'tags_t t list * 'tags_t coq_P4Parameter list
| DeclVariable of 'tags_t * 'tags_t coq_P4Type * 'tags_t t
   * 'tags_t coq_Expression option
| DeclValueSet of 'tags_t * 'tags_t coq_P4Type * 'tags_t coq_Expression
   * 'tags_t t
| DeclAction of 'tags_t * 'tags_t t * 'tags_t coq_P4Parameter list
   * 'tags_t coq_P4Parameter list * 'tags_t coq_Block
| DeclTable of 'tags_t * 'tags_t t * 'tags_t coq_TableKey list
   * 'tags_t coq_TableActionRef list * 'tags_t coq_TableEntry list option
   * 'tags_t coq_TableActionRef option * 'tags_t P4Int.t option
   * 'tags_t coq_TableProperty list
| DeclHeader of 'tags_t * 'tags_t t * 'tags_t coq_DeclarationField list
| DeclHeaderUnion of 'tags_t * 'tags_t t * 'tags_t coq_DeclarationField list
| DeclStruct of 'tags_t * 'tags_t t * 'tags_t coq_DeclarationField list
| DeclError of 'tags_t * 'tags_t t list
| DeclMatchKind of 'tags_t * 'tags_t t list
| DeclEnum of 'tags_t * 'tags_t t * 'tags_t t list
| DeclSerializableEnum of 'tags_t * 'tags_t coq_P4Type * 'tags_t t
   * ('tags_t, 'tags_t coq_Expression) coq_AList
| DeclExternObject of 'tags_t * 'tags_t t * 'tags_t t list
   * 'tags_t coq_MethodPrototype list
| DeclTypeDef of 'tags_t * 'tags_t t
   * ('tags_t coq_P4Type, 'tags_t coq_Declaration) sum
| DeclNewType of 'tags_t * 'tags_t t
   * ('tags_t coq_P4Type, 'tags_t coq_Declaration) sum
| DeclControlType of 'tags_t * 'tags_t t * 'tags_t t list
   * 'tags_t coq_P4Parameter list
| DeclParserType of 'tags_t * 'tags_t t * 'tags_t t list
   * 'tags_t coq_P4Parameter list
| DeclPackageType of 'tags_t * 'tags_t t * 'tags_t t list
   * 'tags_t coq_P4Parameter list

val coq_Declaration_rect :
  ('a1 -> 'a1 coq_P4Type -> 'a1 t -> 'a1 coq_ValueBase -> 'a2) -> ('a1 -> 'a1
  coq_P4Type -> 'a1 coq_Expression list -> 'a1 t -> 'a1 coq_Block option ->
  'a2) -> ('a1 -> 'a1 t -> 'a1 t list -> 'a1 coq_P4Parameter list -> 'a1
  coq_P4Parameter list -> 'a1 coq_Declaration list -> 'a1 coq_ParserState
  list -> 'a2) -> ('a1 -> 'a1 t -> 'a1 t list -> 'a1 coq_P4Parameter list ->
  'a1 coq_P4Parameter list -> 'a1 coq_Declaration list -> 'a1 coq_Block ->
  'a2) -> ('a1 -> 'a1 coq_P4Type -> 'a1 t -> 'a1 t list -> 'a1
  coq_P4Parameter list -> 'a1 coq_Block -> 'a2) -> ('a1 -> 'a1 coq_P4Type ->
  'a1 t -> 'a1 t list -> 'a1 coq_P4Parameter list -> 'a2) -> ('a1 -> 'a1
  coq_P4Type -> 'a1 t -> 'a1 coq_Expression option -> 'a2) -> ('a1 -> 'a1
  coq_P4Type -> 'a1 coq_Expression -> 'a1 t -> 'a2) -> ('a1 -> 'a1 t -> 'a1
  coq_P4Parameter list -> 'a1 coq_P4Parameter list -> 'a1 coq_Block -> 'a2)
  -> ('a1 -> 'a1 t -> 'a1 coq_TableKey list -> 'a1 coq_TableActionRef list ->
  'a1 coq_TableEntry list option -> 'a1 coq_TableActionRef option -> 'a1
  P4Int.t option -> 'a1 coq_TableProperty list -> 'a2) -> ('a1 -> 'a1 t ->
  'a1 coq_DeclarationField list -> 'a2) -> ('a1 -> 'a1 t -> 'a1
  coq_DeclarationField list -> 'a2) -> ('a1 -> 'a1 t -> 'a1
  coq_DeclarationField list -> 'a2) -> ('a1 -> 'a1 t list -> 'a2) -> ('a1 ->
  'a1 t list -> 'a2) -> ('a1 -> 'a1 t -> 'a1 t list -> 'a2) -> ('a1 -> 'a1
  coq_P4Type -> 'a1 t -> ('a1, 'a1 coq_Expression) coq_AList -> 'a2) -> ('a1
  -> 'a1 t -> 'a1 t list -> 'a1 coq_MethodPrototype list -> 'a2) -> ('a1 ->
  'a1 t -> ('a1 coq_P4Type, 'a1 coq_Declaration) sum -> 'a2) -> ('a1 -> 'a1 t
  -> ('a1 coq_P4Type, 'a1 coq_Declaration) sum -> 'a2) -> ('a1 -> 'a1 t ->
  'a1 t list -> 'a1 coq_P4Parameter list -> 'a2) -> ('a1 -> 'a1 t -> 'a1 t
  list -> 'a1 coq_P4Parameter list -> 'a2) -> ('a1 -> 'a1 t -> 'a1 t list ->
  'a1 coq_P4Parameter list -> 'a2) -> 'a1 coq_Declaration -> 'a2

val coq_Declaration_rec :
  ('a1 -> 'a1 coq_P4Type -> 'a1 t -> 'a1 coq_ValueBase -> 'a2) -> ('a1 -> 'a1
  coq_P4Type -> 'a1 coq_Expression list -> 'a1 t -> 'a1 coq_Block option ->
  'a2) -> ('a1 -> 'a1 t -> 'a1 t list -> 'a1 coq_P4Parameter list -> 'a1
  coq_P4Parameter list -> 'a1 coq_Declaration list -> 'a1 coq_ParserState
  list -> 'a2) -> ('a1 -> 'a1 t -> 'a1 t list -> 'a1 coq_P4Parameter list ->
  'a1 coq_P4Parameter list -> 'a1 coq_Declaration list -> 'a1 coq_Block ->
  'a2) -> ('a1 -> 'a1 coq_P4Type -> 'a1 t -> 'a1 t list -> 'a1
  coq_P4Parameter list -> 'a1 coq_Block -> 'a2) -> ('a1 -> 'a1 coq_P4Type ->
  'a1 t -> 'a1 t list -> 'a1 coq_P4Parameter list -> 'a2) -> ('a1 -> 'a1
  coq_P4Type -> 'a1 t -> 'a1 coq_Expression option -> 'a2) -> ('a1 -> 'a1
  coq_P4Type -> 'a1 coq_Expression -> 'a1 t -> 'a2) -> ('a1 -> 'a1 t -> 'a1
  coq_P4Parameter list -> 'a1 coq_P4Parameter list -> 'a1 coq_Block -> 'a2)
  -> ('a1 -> 'a1 t -> 'a1 coq_TableKey list -> 'a1 coq_TableActionRef list ->
  'a1 coq_TableEntry list option -> 'a1 coq_TableActionRef option -> 'a1
  P4Int.t option -> 'a1 coq_TableProperty list -> 'a2) -> ('a1 -> 'a1 t ->
  'a1 coq_DeclarationField list -> 'a2) -> ('a1 -> 'a1 t -> 'a1
  coq_DeclarationField list -> 'a2) -> ('a1 -> 'a1 t -> 'a1
  coq_DeclarationField list -> 'a2) -> ('a1 -> 'a1 t list -> 'a2) -> ('a1 ->
  'a1 t list -> 'a2) -> ('a1 -> 'a1 t -> 'a1 t list -> 'a2) -> ('a1 -> 'a1
  coq_P4Type -> 'a1 t -> ('a1, 'a1 coq_Expression) coq_AList -> 'a2) -> ('a1
  -> 'a1 t -> 'a1 t list -> 'a1 coq_MethodPrototype list -> 'a2) -> ('a1 ->
  'a1 t -> ('a1 coq_P4Type, 'a1 coq_Declaration) sum -> 'a2) -> ('a1 -> 'a1 t
  -> ('a1 coq_P4Type, 'a1 coq_Declaration) sum -> 'a2) -> ('a1 -> 'a1 t ->
  'a1 t list -> 'a1 coq_P4Parameter list -> 'a2) -> ('a1 -> 'a1 t -> 'a1 t
  list -> 'a1 coq_P4Parameter list -> 'a2) -> ('a1 -> 'a1 t -> 'a1 t list ->
  'a1 coq_P4Parameter list -> 'a2) -> 'a1 coq_Declaration -> 'a2

type 'tags_t coq_ValueLoc = 'tags_t t

type 'tags_t coq_ValueTable =
| MkValTable of 'tags_t t * 'tags_t coq_TableKey list
   * 'tags_t coq_TableActionRef list * 'tags_t coq_TableActionRef
   * 'tags_t coq_TableEntry list

val coq_ValueTable_rect :
  ('a1 t -> 'a1 coq_TableKey list -> 'a1 coq_TableActionRef list -> 'a1
  coq_TableActionRef -> 'a1 coq_TableEntry list -> 'a2) -> 'a1 coq_ValueTable
  -> 'a2

val coq_ValueTable_rec :
  ('a1 t -> 'a1 coq_TableKey list -> 'a1 coq_TableActionRef list -> 'a1
  coq_TableActionRef -> 'a1 coq_TableEntry list -> 'a2) -> 'a1 coq_ValueTable
  -> 'a2

type ('tags_t, 'binding) coq_Env_env = ('tags_t, 'binding) coq_AList list

type 'tags_t coq_Env_EvalEnv =
| MkEnv_EvalEnv of ('tags_t, 'tags_t coq_ValueLoc) coq_Env_env
   * ('tags_t, 'tags_t coq_P4Type) coq_Env_env * 'tags_t t

val coq_Env_EvalEnv_rect :
  (('a1, 'a1 coq_ValueLoc) coq_Env_env -> ('a1, 'a1 coq_P4Type) coq_Env_env
  -> 'a1 t -> 'a2) -> 'a1 coq_Env_EvalEnv -> 'a2

val coq_Env_EvalEnv_rec :
  (('a1, 'a1 coq_ValueLoc) coq_Env_env -> ('a1, 'a1 coq_P4Type) coq_Env_env
  -> 'a1 t -> 'a2) -> 'a1 coq_Env_EvalEnv -> 'a2

type 'tags_t coq_ExternMethod = { name : 'tags_t t;
                                  typ : 'tags_t coq_FunctionType }

val name : 'a1 coq_ExternMethod -> 'a1 t

val typ : 'a1 coq_ExternMethod -> 'a1 coq_FunctionType

type 'tags_t coq_ExternMethods = { type_params : 'tags_t t list;
                                   methods : 'tags_t coq_ExternMethod list }

val type_params : 'a1 coq_ExternMethods -> 'a1 t list

val methods : 'a1 coq_ExternMethods -> 'a1 coq_ExternMethod list

type 'tags_t coq_ValuePreLvalue =
| ValLeftName of 'tags_t name
| ValLeftMember of 'tags_t coq_ValueLvalue * 'tags_t t
| ValLeftBitAccess of 'tags_t coq_ValueLvalue * int * int
| ValLeftArrayAccess of 'tags_t coq_ValueLvalue * int
and 'tags_t coq_ValueLvalue =
| MkValueLvalue of 'tags_t coq_ValuePreLvalue * 'tags_t coq_P4Type

val coq_ValuePreLvalue_rect :
  ('a1 name -> 'a2) -> ('a1 coq_ValueLvalue -> 'a1 t -> 'a2) -> ('a1
  coq_ValueLvalue -> int -> int -> 'a2) -> ('a1 coq_ValueLvalue -> int ->
  'a2) -> 'a1 coq_ValuePreLvalue -> 'a2

val coq_ValuePreLvalue_rec :
  ('a1 name -> 'a2) -> ('a1 coq_ValueLvalue -> 'a1 t -> 'a2) -> ('a1
  coq_ValueLvalue -> int -> int -> 'a2) -> ('a1 coq_ValueLvalue -> int ->
  'a2) -> 'a1 coq_ValuePreLvalue -> 'a2

val coq_ValueLvalue_rect :
  ('a1 coq_ValuePreLvalue -> 'a1 coq_P4Type -> 'a2) -> 'a1 coq_ValueLvalue ->
  'a2

val coq_ValueLvalue_rec :
  ('a1 coq_ValuePreLvalue -> 'a1 coq_P4Type -> 'a2) -> 'a1 coq_ValueLvalue ->
  'a2

type 'tags_t coq_ValueFunctionImplementation =
| ValFuncImplUser of 'tags_t coq_Env_EvalEnv * 'tags_t coq_Block
| ValFuncImplExtern of 'tags_t t * ('tags_t coq_ValueLoc * 'tags_t t) option
| ValFuncImplBuiltin of 'tags_t t * 'tags_t coq_ValueLvalue

val coq_ValueFunctionImplementation_rect :
  ('a1 coq_Env_EvalEnv -> 'a1 coq_Block -> 'a2) -> ('a1 t -> ('a1
  coq_ValueLoc * 'a1 t) option -> 'a2) -> ('a1 t -> 'a1 coq_ValueLvalue ->
  'a2) -> 'a1 coq_ValueFunctionImplementation -> 'a2

val coq_ValueFunctionImplementation_rec :
  ('a1 coq_Env_EvalEnv -> 'a1 coq_Block -> 'a2) -> ('a1 t -> ('a1
  coq_ValueLoc * 'a1 t) option -> 'a2) -> ('a1 t -> 'a1 coq_ValueLvalue ->
  'a2) -> 'a1 coq_ValueFunctionImplementation -> 'a2

type 'tags_t coq_ValueObject =
| ValObjParser of 'tags_t coq_Env_EvalEnv * 'tags_t coq_P4Parameter list
   * 'tags_t coq_P4Parameter list * 'tags_t coq_Declaration list
   * 'tags_t coq_ParserState list
| ValObjTable of 'tags_t coq_ValueTable
| ValObjControl of 'tags_t coq_Env_EvalEnv * 'tags_t coq_P4Parameter list
   * 'tags_t coq_P4Parameter list * 'tags_t coq_Declaration list
   * 'tags_t coq_Block
| ValObjPackage of ('tags_t, 'tags_t coq_ValueLoc) coq_AList
| ValObjRuntime of 'tags_t coq_ValueLoc * 'tags_t t
| ValObjFun of 'tags_t coq_P4Parameter list
   * 'tags_t coq_ValueFunctionImplementation
| ValObjAction of 'tags_t coq_Env_EvalEnv * 'tags_t coq_P4Parameter list
   * 'tags_t coq_Block
| ValObjPacket of bool list

val coq_ValueObject_rect :
  ('a1 coq_Env_EvalEnv -> 'a1 coq_P4Parameter list -> 'a1 coq_P4Parameter
  list -> 'a1 coq_Declaration list -> 'a1 coq_ParserState list -> 'a2) ->
  ('a1 coq_ValueTable -> 'a2) -> ('a1 coq_Env_EvalEnv -> 'a1 coq_P4Parameter
  list -> 'a1 coq_P4Parameter list -> 'a1 coq_Declaration list -> 'a1
  coq_Block -> 'a2) -> (('a1, 'a1 coq_ValueLoc) coq_AList -> 'a2) -> ('a1
  coq_ValueLoc -> 'a1 t -> 'a2) -> ('a1 coq_P4Parameter list -> 'a1
  coq_ValueFunctionImplementation -> 'a2) -> ('a1 coq_Env_EvalEnv -> 'a1
  coq_P4Parameter list -> 'a1 coq_Block -> 'a2) -> (bool list -> 'a2) -> 'a1
  coq_ValueObject -> 'a2

val coq_ValueObject_rec :
  ('a1 coq_Env_EvalEnv -> 'a1 coq_P4Parameter list -> 'a1 coq_P4Parameter
  list -> 'a1 coq_Declaration list -> 'a1 coq_ParserState list -> 'a2) ->
  ('a1 coq_ValueTable -> 'a2) -> ('a1 coq_Env_EvalEnv -> 'a1 coq_P4Parameter
  list -> 'a1 coq_P4Parameter list -> 'a1 coq_Declaration list -> 'a1
  coq_Block -> 'a2) -> (('a1, 'a1 coq_ValueLoc) coq_AList -> 'a2) -> ('a1
  coq_ValueLoc -> 'a1 t -> 'a2) -> ('a1 coq_P4Parameter list -> 'a1
  coq_ValueFunctionImplementation -> 'a2) -> ('a1 coq_Env_EvalEnv -> 'a1
  coq_P4Parameter list -> 'a1 coq_Block -> 'a2) -> (bool list -> 'a2) -> 'a1
  coq_ValueObject -> 'a2

type 'tags_t coq_ValueConstructor =
| ValConsParser of 'tags_t coq_Env_EvalEnv * 'tags_t coq_P4Parameter list
   * 'tags_t coq_P4Parameter list * 'tags_t coq_Declaration list
   * 'tags_t coq_ParserState list
| ValConsTable of 'tags_t coq_ValueTable
| ValConsControl of 'tags_t coq_Env_EvalEnv * 'tags_t coq_P4Parameter list
   * 'tags_t coq_P4Parameter list * 'tags_t coq_Declaration list
   * 'tags_t coq_Block
| ValConsPackage of 'tags_t coq_P4Parameter list
   * ('tags_t, 'tags_t coq_ValueLoc) coq_AList
| ValConsExternObj of ('tags_t, 'tags_t coq_P4Parameter list) coq_AList

val coq_ValueConstructor_rect :
  ('a1 coq_Env_EvalEnv -> 'a1 coq_P4Parameter list -> 'a1 coq_P4Parameter
  list -> 'a1 coq_Declaration list -> 'a1 coq_ParserState list -> 'a2) ->
  ('a1 coq_ValueTable -> 'a2) -> ('a1 coq_Env_EvalEnv -> 'a1 coq_P4Parameter
  list -> 'a1 coq_P4Parameter list -> 'a1 coq_Declaration list -> 'a1
  coq_Block -> 'a2) -> ('a1 coq_P4Parameter list -> ('a1, 'a1 coq_ValueLoc)
  coq_AList -> 'a2) -> (('a1, 'a1 coq_P4Parameter list) coq_AList -> 'a2) ->
  'a1 coq_ValueConstructor -> 'a2

val coq_ValueConstructor_rec :
  ('a1 coq_Env_EvalEnv -> 'a1 coq_P4Parameter list -> 'a1 coq_P4Parameter
  list -> 'a1 coq_Declaration list -> 'a1 coq_ParserState list -> 'a2) ->
  ('a1 coq_ValueTable -> 'a2) -> ('a1 coq_Env_EvalEnv -> 'a1 coq_P4Parameter
  list -> 'a1 coq_P4Parameter list -> 'a1 coq_Declaration list -> 'a1
  coq_Block -> 'a2) -> ('a1 coq_P4Parameter list -> ('a1, 'a1 coq_ValueLoc)
  coq_AList -> 'a2) -> (('a1, 'a1 coq_P4Parameter list) coq_AList -> 'a2) ->
  'a1 coq_ValueConstructor -> 'a2

type 'tags_t coq_Value =
| ValBase of 'tags_t coq_ValueBase
| ValObj of 'tags_t coq_ValueObject
| ValCons of 'tags_t coq_ValueConstructor

val coq_Value_rect :
  ('a1 coq_ValueBase -> 'a2) -> ('a1 coq_ValueObject -> 'a2) -> ('a1
  coq_ValueConstructor -> 'a2) -> 'a1 coq_Value -> 'a2

val coq_Value_rec :
  ('a1 coq_ValueBase -> 'a2) -> ('a1 coq_ValueObject -> 'a2) -> ('a1
  coq_ValueConstructor -> 'a2) -> 'a1 coq_Value -> 'a2

type 'tags_t program =
  'tags_t coq_Declaration list
  (* singleton inductive, whose constructor was Program *)

val program_rect : ('a1 coq_Declaration list -> 'a2) -> 'a1 program -> 'a2

val program_rec : ('a1 coq_Declaration list -> 'a2) -> 'a1 program -> 'a2
