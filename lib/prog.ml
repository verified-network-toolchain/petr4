type coq_MethodPrototype = Info.t Poulet4.Syntax.coq_MethodPrototype
type coq_OpUni = Poulet4.Syntax.coq_OpUni
type coq_OpBin = Poulet4.Syntax.coq_OpBin
type coq_KeyValue = Info.t Poulet4.Syntax.coq_KeyValue
and coq_ExpressionPreT = Info.t Poulet4.Syntax.coq_ExpressionPreT
and coq_Expression = Info.t Poulet4.Syntax.coq_Expression
type coq_MatchPreT = Info.t Poulet4.Syntax.coq_MatchPreT
type coq_Match = Info.t Poulet4.Syntax.coq_Match
type coq_TablePreActionRef = Info.t Poulet4.Syntax.coq_TablePreActionRef
type coq_TableActionRef = Info.t Poulet4.Syntax.coq_TableActionRef
type coq_TableKey = Info.t Poulet4.Syntax.coq_TableKey
type coq_TableEntry = Info.t Poulet4.Syntax.coq_TableEntry
type coq_TableProperty = Info.t Poulet4.Syntax.coq_TableProperty
type coq_ValueBase = Info.t Poulet4.Syntax.coq_ValueBase
and coq_ValueSet = Info.t Poulet4.Syntax.coq_ValueSet
type coq_StatementSwitchLabel = Info.t Poulet4.Syntax.coq_StatementSwitchLabel
type coq_StatementSwitchCase = Info.t Poulet4.Syntax.coq_StatementSwitchCase
and coq_StatementPreT = Info.t Poulet4.Syntax.coq_StatementPreT
and coq_Statement = Info.t Poulet4.Syntax.coq_Statement
and coq_Block = Info.t Poulet4.Syntax.coq_Block
type coq_ParserCase = Info.t Poulet4.Syntax.coq_ParserCase
type coq_ParserTransition = Info.t Poulet4.Syntax.coq_ParserTransition
type coq_ParserState = Info.t Poulet4.Syntax.coq_ParserState
type coq_DeclarationField = Info.t Poulet4.Syntax.coq_DeclarationField
type coq_Declaration = Info.t Poulet4.Syntax.coq_Declaration
type coq_ValueTable = Info.t Poulet4.Syntax.coq_ValueTable
type coq_Env_EvalEnv = Info.t Poulet4.Syntax.coq_Env_EvalEnv
type coq_ExternMethod = Info.t Poulet4.Syntax.coq_ExternMethod
type coq_ExternMethods = Info.t Poulet4.Syntax.coq_ExternMethods
type coq_ValuePreLvalue = Info.t Poulet4.Syntax.coq_ValuePreLvalue
and coq_ValueLvalue = Info.t Poulet4.Syntax.coq_ValueLvalue
type coq_ValueObject = Info.t Poulet4.Syntax.coq_ValueObject
type coq_ValueConstructor = Info.t Poulet4.Syntax.coq_ValueConstructor
type coq_Value = Info.t Poulet4.Syntax.coq_Value
type program = Info.t Poulet4.Syntax.program

(* Everything below this comment is runtime data structures and not
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
