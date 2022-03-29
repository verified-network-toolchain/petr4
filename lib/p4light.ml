open Sexplib.Conv

type direction = Poulet4.Typed.direction

type ('a, 'b) pre_AList = ('a, 'b) Poulet4.AList.coq_AList
type ('a, 'b) pre_AListString = ('a, 'b) Poulet4.P4String.coq_AList

type coq_FunctionKind = Poulet4.Typed.coq_FunctionKind
type coq_StmType = Poulet4.Typed.coq_StmType
type coq_ParamContextDeclaration = Poulet4.Typed.coq_ParamContextDeclaration
type coq_ParamContext = Poulet4.Typed.coq_ParamContext
type coq_ExprContext = Poulet4.Typed.coq_ExprContext
type 'a pre_P4Type = 'a Poulet4.Typed.coq_P4Type
type 'a pre_FunctionType = 'a Poulet4.Typed.coq_FunctionType
type 'a pre_ControlType = 'a Poulet4.Typed.coq_ControlType
type pre_P4Parameter = 'a Poulet4.Typed.coq_P4Parameter
type coq_P4Type = P4info.t pre_P4Type
type coq_FieldType = P4string.t * coq_P4Type
type coq_FunctionType = P4info.t pre_FunctionType
type coq_ControlType = P4info.t pre_ControlType
type coq_P4Parameter = P4info.t pre_P4Parameter

type 'a pre_StmtContext = 'a Poulet4.Typed.coq_StmtContext
type coq_StmtContext = P4info.t pre_StmtContext

type 'a pre_DeclContext = 'a Poulet4.Typed.coq_DeclContext
type coq_DeclContext = P4info.t pre_DeclContext

let eq_dir d1 d2 =
  match d1, d2 with
  | In, In
  | Out, Out
  | InOut, InOut
  | Directionless, Directionless -> true
  | _ -> false

let expr_ctxt_of_stmt_ctxt (s: coq_StmtContext) : coq_ExprContext =
  match s with
  | StmtCxFunction ret -> ExprCxFunction
  | StmtCxAction -> ExprCxAction
  | StmtCxParserState -> ExprCxParserState
  | StmtCxApplyBlock -> ExprCxApplyBlock
  | StmtCxMethod ret -> ExprCxMethod

let expr_ctxt_of_decl_ctxt (s: coq_DeclContext) : coq_ExprContext =
  match s with
   | DeclCxTopLevel -> ExprCxConstant
   | DeclCxNested -> ExprCxDeclLocals
   | DeclCxStatement c -> expr_ctxt_of_stmt_ctxt c

type 'a info = 'a Surface.info

type ('a, 'b) sum = ('a, 'b) Poulet4.Datatypes.sum
type 'a pre_MethodPrototype =
  'a Poulet4.Syntax.coq_MethodPrototype
type coq_MethodPrototype = P4info.t pre_MethodPrototype
type coq_OpUni = Poulet4.Syntax.coq_OpUni
type coq_OpBin = Poulet4.Syntax.coq_OpBin
type coq_Locator = Poulet4.Syntax.coq_Locator
let noLocator = LGlobal []
type 'a pre_ExpressionPreT =
  'a Poulet4.Syntax.coq_ExpressionPreT
type 'a pre_Expression =
  'a Poulet4.Syntax.coq_Expression
type coq_ExpressionPreT = P4info.t pre_ExpressionPreT
type coq_Expression = P4info.t pre_Expression
type 'a pre_MatchPreT =
  'a Poulet4.Syntax.coq_MatchPreT
type 'a pre_Match =
  'a Poulet4.Syntax.coq_Match
type 'a pre_TablePreActionRef =
  'a Poulet4.Syntax.coq_TablePreActionRef
type 'a pre_TableActionRef =
  'a Poulet4.Syntax.coq_TableActionRef
type 'a pre_TableKey =
  'a Poulet4.Syntax.coq_TableKey
type 'a pre_TableEntry =
  'a Poulet4.Syntax.coq_TableEntry
type 'a pre_TableProperty =
  'a Poulet4.Syntax.coq_TableProperty
type 'a pre_StatementSwitchLabel =
  'a Poulet4.Syntax.coq_StatementSwitchLabel
type 'a pre_StatementSwitchCase =
  'a Poulet4.Syntax.coq_StatementSwitchCase
type 'a pre_StatementPreT =
  'a Poulet4.Syntax.coq_StatementPreT
type 'a pre_Statement =
  'a Poulet4.Syntax.coq_Statement
type 'a pre_Block =
  'a Poulet4.Syntax.coq_Block
type 'a pre_Initializer =
  'a Poulet4.Syntax.coq_Initializer
type 'a pre_ParserCase =
  'a Poulet4.Syntax.coq_ParserCase
type 'a pre_ParserTransition =
  'a Poulet4.Syntax.coq_ParserTransition
type 'a pre_ParserState = 'a Poulet4.Syntax.coq_ParserState
type 'a pre_DeclarationField = 'a Poulet4.Syntax.coq_DeclarationField
type 'a pre_Declaration = 'a Poulet4.Syntax.coq_Declaration
type 'a pre_ExternMethod = 'a Poulet4.Syntax.coq_ExternMethod
type 'a pre_ExternMethods = 'a Poulet4.Syntax.coq_ExternMethods
type 'a pre_program = 'a Poulet4.Syntax.program
type coq_MatchPreT = P4info.t pre_MatchPreT
type coq_Match = P4info.t pre_Match
type coq_TablePreActionRef = P4info.t pre_TablePreActionRef
type coq_TableActionRef = P4info.t pre_TableActionRef
type coq_TableKey = P4info.t pre_TableKey
type coq_TableEntry = P4info.t pre_TableEntry
type coq_TableProperty = P4info.t pre_TableProperty

type coq_StatementSwitchLabel = P4info.t pre_StatementSwitchLabel
type coq_StatementSwitchCase = P4info.t pre_StatementSwitchCase
type coq_StatementPreT = P4info.t pre_StatementPreT
type coq_Statement = P4info.t pre_Statement
type coq_Block = P4info.t pre_Block
type coq_Initializer = P4info.t pre_Initializer
type coq_ParserCase = P4info.t pre_ParserCase
type coq_ParserTransition = P4info.t pre_ParserTransition
type coq_ParserState = P4info.t pre_ParserState
type coq_DeclarationField = P4info.t pre_DeclarationField
type coq_Declaration = P4info.t pre_Declaration
type coq_ExternMethod = P4info.t pre_ExternMethod
type coq_ExternMethods = P4info.t pre_ExternMethods
type 'a pre_Value = 'a Poulet4.ConstValue.coq_Value
type coq_Value = P4info.t pre_Value
type program = P4info.t pre_program

(* Everything below this comment is runtime data structures type not
 * program syntax.
 *)
type buf = Cstruct_sexp.t
type pkt = {
  emitted: buf;
  main: buf;
  in_size: int;
}
type loc = string
type entries = (Ast.qualified_name * (int option * Ast.match_ list * Ast.action * Ast.id option) list) list * (Ast.qualified_name * Ast.action list) list

type vsets = coq_Match list list

type ctrl = entries * vsets

type signal =
  | SContinue
  | SReturn of coq_Value
  | SExit
  | SReject of string
