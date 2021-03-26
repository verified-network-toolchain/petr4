open Datatypes
open List
open P4String
open Syntax
open Typed

val to_digit : Bigint.t -> char

val to_N_aux : int -> Bigint.t -> string -> string

val coq_N_to_string : Bigint.t -> string

val add1 : Bigint.t -> Bigint.t

val coq_N_to_tempvar : 'a1 -> Bigint.t -> 'a1 t

val transform_ept :
  'a1 -> Bigint.t -> 'a1 coq_ExpressionPreT -> 'a1 -> 'a1 coq_P4Type ->
  direction -> (('a1 t * 'a1 coq_Expression) list * 'a1
  coq_Expression) * Bigint.t

val transform_exp :
  'a1 -> Bigint.t -> 'a1 coq_Expression -> (('a1 t * 'a1 coq_Expression)
  list * 'a1 coq_Expression) * Bigint.t

val transform_keyvalue :
  'a1 -> Bigint.t -> 'a1 coq_KeyValue -> (('a1 t * 'a1 coq_Expression)
  list * 'a1 coq_KeyValue) * Bigint.t

val transform_Expr :
  'a1 -> Bigint.t -> 'a1 coq_Expression -> (('a1 t * 'a1 coq_Expression)
  list * 'a1 coq_Expression) * Bigint.t

val expr_to_stmt :
  'a1 -> coq_StmType -> ('a1 t * 'a1 coq_Expression) -> 'a1 coq_Statement

val to_StmtList :
  'a1 -> coq_StmType -> ('a1 t * 'a1 coq_Expression) list -> 'a1
  coq_Statement list

val transform_list :
  (Bigint.t -> 'a1 -> ('a2 list * 'a3) * Bigint.t) -> Bigint.t -> 'a1 list ->
  ('a2 list * 'a3 list) * Bigint.t

val transform_exprs :
  'a1 -> Bigint.t -> 'a1 coq_Expression list -> (('a1 t * 'a1 coq_Expression)
  list * 'a1 coq_Expression list) * Bigint.t

val prepend_to_block :
  'a1 coq_Statement list -> 'a1 coq_Block -> 'a1 coq_Block

val transform_exp_stmt :
  'a1 -> Bigint.t -> 'a1 coq_Expression -> ('a1 coq_Statement list * 'a1
  coq_Expression) * Bigint.t

val transform_Expr_stmt :
  'a1 -> Bigint.t -> 'a1 coq_Expression -> ('a1 coq_Statement list * 'a1
  coq_Expression) * Bigint.t

val transform_list_stmt :
  'a1 -> Bigint.t -> 'a1 coq_Expression list -> ('a1 coq_Statement list * 'a1
  coq_Expression list) * Bigint.t

val transform_stmtpt :
  'a1 -> Bigint.t -> 'a1 -> 'a1 coq_StatementPreT -> coq_StmType -> 'a1
  coq_Statement list * Bigint.t

val transform_stmt :
  'a1 -> Bigint.t -> 'a1 coq_Statement -> 'a1 coq_Statement list * Bigint.t

val transform_blk :
  'a1 -> Bigint.t -> 'a1 coq_Block -> 'a1 coq_Block * Bigint.t

val transform_ssc :
  'a1 -> Bigint.t -> 'a1 coq_StatementSwitchCase -> 'a1
  coq_StatementSwitchCase * Bigint.t

val expr_to_decl : 'a1 -> ('a1 t * 'a1 coq_Expression) -> 'a1 coq_Declaration

val transform_list' :
  (Bigint.t -> 'a1 -> 'a1 list * Bigint.t) -> Bigint.t -> 'a1 list -> 'a1
  list * Bigint.t

val transform_match :
  'a1 -> Bigint.t -> 'a1 coq_Match -> ('a1 coq_Declaration list * 'a1
  coq_Match) * Bigint.t

val transform_psrcase :
  'a1 -> Bigint.t -> 'a1 coq_ParserCase -> ('a1 coq_Declaration list * 'a1
  coq_ParserCase) * Bigint.t

val transform_psrtrans :
  'a1 -> Bigint.t -> 'a1 coq_ParserTransition -> ('a1 coq_Declaration
  list * 'a1 coq_ParserTransition) * Bigint.t

val transform_psrst :
  'a1 -> Bigint.t -> 'a1 coq_ParserState -> ('a1 coq_Declaration list * 'a1
  coq_ParserState) * Bigint.t

val transform_tblkey :
  'a1 -> Bigint.t -> 'a1 coq_TableKey -> ('a1 coq_Declaration list * 'a1
  coq_TableKey) * Bigint.t

val transform_opt :
  'a1 -> Bigint.t -> 'a1 coq_Expression option -> (('a1 t * 'a1
  coq_Expression) list * 'a1 coq_Expression option) * Bigint.t

val transform_tpar :
  'a1 -> Bigint.t -> 'a1 coq_TablePreActionRef -> ('a1 coq_Declaration
  list * 'a1 coq_TablePreActionRef) * Bigint.t

val transform_tar :
  'a1 -> Bigint.t -> 'a1 coq_TableActionRef -> ('a1 coq_Declaration
  list * 'a1 coq_TableActionRef) * Bigint.t

val transform_tblenty :
  'a1 -> Bigint.t -> 'a1 coq_TableEntry -> ('a1 coq_Declaration list * 'a1
  coq_TableEntry) * Bigint.t

val transform_tblprop :
  'a1 -> Bigint.t -> 'a1 coq_TableProperty -> ('a1 coq_Declaration list * 'a1
  coq_TableProperty) * Bigint.t

val transform_membr :
  'a1 -> Bigint.t -> ('a1 t * 'a1 coq_Expression) -> ('a1 coq_Declaration
  list * ('a1 t * 'a1 coq_Expression)) * Bigint.t

val lastDecl : 'a1 -> 'a1 coq_Declaration list -> 'a1 coq_Declaration

val transform_decl :
  'a1 -> Bigint.t -> 'a1 coq_Declaration -> 'a1 coq_Declaration
  list * Bigint.t

val transform_prog : 'a1 -> 'a1 program -> 'a1 program
