open Sexplib.Conv

type direction = [%import:Poulet4.Typed.direction]
  [@@deriving sexp,show,yojson]

type ('a, 'b) pre_AList =
  [%import:('a, 'b) Poulet4.AList.coq_AList]
  [@@deriving sexp,show,yojson]
type ('a, 'b) pre_AListString =
  [%import:('a, 'b) Poulet4.P4String.coq_AList
    [@with t := P4string.pre_t; Poulet4.AList.coq_AList := pre_AList]]
  [@@deriving sexp,show,yojson]

type coq_FunctionKind = [%import:Poulet4.Typed.coq_FunctionKind]
  [@@deriving sexp,show,yojson]
type coq_StmType = [%import:Poulet4.Typed.coq_StmType]
  [@@deriving sexp,show,yojson]
type coq_ParamContextDeclaration = [%import:Poulet4.Typed.coq_ParamContextDeclaration]
  [@@deriving sexp,show,yojson]
type coq_ParamContext = [%import:Poulet4.Typed.coq_ParamContext]
  [@@deriving sexp,show,yojson]
type coq_ExprContext = [%import:Poulet4.Typed.coq_ExprContext]
  [@@deriving sexp,show,yojson]
type 'a pre_P4Type =
  [%import:'a Poulet4.Typed.coq_P4Type
    [@with name := P4name.pre_t;
           Bigint.t := Util.bigint;
           Poulet4.P4String.t := P4string.pre_t;
           coq_ControlType := pre_ControlType;
           coq_P4Parameter := pre_P4Parameter;
           coq_FunctionType := pre_FunctionType;
           Poulet4.P4String.coq_AList := pre_AListString]]
  [@@deriving sexp,show,yojson]
and 'a pre_FunctionType =
  [%import:'a Poulet4.Typed.coq_FunctionType
    [@with Poulet4.P4String.t := P4string.pre_t;
           coq_P4Parameter := pre_P4Parameter;
           coq_P4Type := pre_P4Type]]
  [@@deriving sexp,show,yojson]
and 'a pre_ControlType =
  [%import:'a Poulet4.Typed.coq_ControlType
          [@with Poulet4.P4String.t := P4string.pre_t;
           coq_P4Parameter := pre_P4Parameter;
           coq_P4Type := pre_P4Type]]
  [@@deriving sexp,show,yojson]
and 'a pre_P4Parameter =
  [%import:'a Poulet4.Typed.coq_P4Parameter
    [@with Poulet4.P4String.t := P4string.pre_t;
           Bigint.t := Util.bigint;
           coq_P4Type := pre_P4Type]]
  [@@deriving sexp,show,yojson]
type coq_P4Type = P4info.t pre_P4Type
[@@deriving sexp,show,yojson]
type coq_FieldType = P4string.t * coq_P4Type
[@@deriving sexp,show,yojson]
type coq_FunctionType = P4info.t pre_FunctionType
[@@deriving sexp,show,yojson]
type coq_ControlType = P4info.t pre_ControlType
[@@deriving sexp,show,yojson]
type coq_P4Parameter = P4info.t pre_P4Parameter
[@@deriving sexp,show,yojson]

type 'a pre_StmtContext =
  [%import:'a Poulet4.Typed.coq_StmtContext
    [@with coq_P4Type := pre_P4Type]]
  [@@deriving sexp,show,yojson]
type coq_StmtContext = P4info.t pre_StmtContext
  [@@deriving sexp,show,yojson]

type 'a pre_DeclContext =
  [%import:'a Poulet4.Typed.coq_DeclContext
          [@with coq_P4Type := pre_P4Type;
                 coq_StmtContext := pre_StmtContext]]
  [@@deriving sexp,show,yojson]
type coq_DeclContext = P4info.t pre_DeclContext
  [@@deriving sexp,show,yojson]

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

type ('a, 'b) sum = [%import:('a, 'b) Poulet4.Datatypes.sum]
  [@@deriving sexp,show,yojson]
type 'a pre_MethodPrototype =
  [%import:'a Poulet4.Syntax.coq_MethodPrototype
    [@with Poulet4.P4String.t := P4string.pre_t;
           Poulet4.Typed.coq_P4Type := pre_P4Type;
           Poulet4.Typed.coq_P4Parameter := pre_P4Parameter]]
  [@@deriving sexp,show,yojson]
type coq_MethodPrototype = P4info.t pre_MethodPrototype
  [@@deriving sexp,show,yojson]
type coq_OpUni = [%import:Poulet4.Syntax.coq_OpUni]
  [@@deriving sexp,show,yojson]
type coq_OpBin = [%import:Poulet4.Syntax.coq_OpBin]
  [@@deriving sexp,show,yojson]
type coq_Locator =
  [%import:Poulet4.Syntax.coq_Locator]
  [@@deriving sexp,show,yojson]
let noLocator = LGlobal []
type 'a pre_ExpressionPreT =
  [%import:'a Poulet4.Syntax.coq_ExpressionPreT
    [@with coq_Expression := pre_Expression;
      Bigint.t := Util.bigint;
      Poulet4.P4String.t := P4string.pre_t;
      Poulet4.P4String.coq_AList := pre_AListString;
      Poulet4.P4Int.t := P4int.pre_t;
      Poulet4.Typed.name := P4name.pre_t;
      Poulet4.Typed.coq_P4Type := pre_P4Type;
      Poulet4.Typed.direction := direction;
      coq_Locator := coq_Locator]]
  [@@deriving sexp,show,yojson]
and 'a pre_Expression =
  [%import:'a Poulet4.Syntax.coq_Expression
    [@with coq_ExpressionPreT := pre_ExpressionPreT;
      Poulet4.Typed.direction := direction;
      Poulet4.Typed.coq_P4Type := pre_P4Type]]
  [@@deriving sexp,show,yojson]
type coq_ExpressionPreT = P4info.t pre_ExpressionPreT
  [@@deriving sexp,show,yojson]
type coq_Expression = P4info.t pre_Expression
  [@@deriving sexp,show,yojson]
type 'a pre_MatchPreT =
  [%import:'a Poulet4.Syntax.coq_MatchPreT
             [@with coq_Expression := pre_Expression;
                    Poulet4.P4String.coq_AList := pre_AListString;
                    Poulet4.Typed.coq_P4Type := pre_P4Type]]
  [@@deriving sexp,show,yojson]
type 'a pre_Match =
  [%import:'a Poulet4.Syntax.coq_Match
    [@with coq_MatchPreT := pre_MatchPreT;
           Poulet4.Typed.coq_P4Type := pre_P4Type]]
  [@@deriving sexp,show,yojson]
type 'a pre_TablePreActionRef =
  [%import:'a Poulet4.Syntax.coq_TablePreActionRef
    [@with Poulet4.Typed.name := P4name.pre_t;
           coq_Expression := pre_Expression]]
  [@@deriving sexp,show,yojson]
type 'a pre_TableActionRef =
  [%import:'a Poulet4.Syntax.coq_TableActionRef
    [@with Poulet4.Typed.coq_P4Type := pre_P4Type;
           coq_TablePreActionRef := pre_TablePreActionRef]]
  [@@deriving sexp,show,yojson]
type 'a pre_TableKey =
  [%import:'a Poulet4.Syntax.coq_TableKey
    [@with coq_Expression := pre_Expression;
           Poulet4.P4String.t := P4string.pre_t]]
  [@@deriving sexp,show,yojson]
type 'a pre_TableEntry =
  [%import:'a Poulet4.Syntax.coq_TableEntry
    [@with coq_Match := pre_Match;
           coq_TableActionRef := pre_TableActionRef]]
  [@@deriving sexp,show,yojson]
type 'a pre_TableProperty =
  [%import:'a Poulet4.Syntax.coq_TableProperty
    [@with Poulet4.P4String.t := P4string.pre_t;
           coq_Expression := pre_Expression]]
  [@@deriving sexp,show,yojson]
type 'a pre_StatementSwitchLabel =
  [%import:'a Poulet4.Syntax.coq_StatementSwitchLabel
    [@with Poulet4.P4String.t := P4string.pre_t]]
  [@@deriving sexp,show,yojson]
type 'a pre_StatementSwitchCase =
  [%import:'a Poulet4.Syntax.coq_StatementSwitchCase
    [@with Poulet4.P4String.t := P4string.pre_t;
           coq_Statement := pre_Statement;
           coq_Expression := pre_Expression;
           coq_StatementSwitchLabel := pre_StatementSwitchLabel;
           coq_Block := pre_Block]]
  [@@deriving sexp,show,yojson]
and 'a pre_StatementPreT =
  [%import:'a Poulet4.Syntax.coq_StatementPreT
    [@with Poulet4.P4String.t := P4string.pre_t;
           coq_Initializer := pre_Initializer;
           Poulet4.Typed.coq_P4Type := pre_P4Type;
           coq_Locator := coq_Locator;
           coq_Statement := pre_Statement;
           coq_Expression := pre_Expression;
           coq_Block := pre_Block;
           coq_StatementSwitchCase := pre_StatementSwitchCase]]
  [@@deriving sexp,show,yojson]
and 'a pre_Statement =
  [%import:'a Poulet4.Syntax.coq_Statement
    [@with Poulet4.P4String.t := P4string.pre_t;
           Poulet4.Typed.coq_StmType := coq_StmType;
           coq_Initializer := pre_Initializer;
           coq_StatementPreT := pre_StatementPreT]]
  [@@deriving sexp,show,yojson]
and 'a pre_Block =
  [%import:'a Poulet4.Syntax.coq_Block
          [@with coq_Statement := pre_Statement]]
  [@@deriving sexp,show,yojson]
and 'a pre_Initializer =
  [%import:'a Poulet4.Syntax.coq_Initializer
          [@with Poulet4.P4String.t := P4string.pre_t;
                 Poulet4.Typed.coq_P4Type := pre_P4Type;
                 Poulet4.Typed.coq_P4Parameter := pre_P4Parameter;
                 coq_Expression := pre_Expression;
                 coq_Block := pre_Block;
                 coq_Initializer := pre_Initializer]]
  [@@deriving sexp,show,yojson]
type 'a pre_ParserCase =
  [%import:'a Poulet4.Syntax.coq_ParserCase
    [@with Poulet4.P4String.t := P4string.pre_t;
           coq_Match := pre_Match]]
  [@@deriving sexp,show,yojson]
type 'a pre_ParserTransition =
  [%import:'a Poulet4.Syntax.coq_ParserTransition
    [@with Poulet4.P4String.t := P4string.pre_t;
           coq_Expression := pre_Expression;
      coq_ParserCase := pre_ParserCase]]
  [@@deriving sexp,show,yojson]
type 'a pre_ParserState =
  [%import:'a Poulet4.Syntax.coq_ParserState
    [@with Poulet4.P4String.t := P4string.pre_t;
           coq_Statement := pre_Statement;
      coq_ParserTransition := pre_ParserTransition]]
  [@@deriving sexp,show,yojson]
type 'a pre_DeclarationField =
  [%import:'a Poulet4.Syntax.coq_DeclarationField
    [@with Poulet4.P4String.t := P4string.pre_t;
           Poulet4.Typed.coq_P4Type := pre_P4Type;
      coq_Match := pre_Match]]
  [@@deriving sexp,show,yojson]
type 'a pre_Declaration =
  [%import:'a Poulet4.Syntax.coq_Declaration
    [@with Poulet4.P4String.t := P4string.pre_t;
           Poulet4.Typed.coq_P4Type := pre_P4Type;
           Poulet4.Typed.coq_P4Parameter := pre_P4Parameter;
           Poulet4.Datatypes.sum := sum;
           Poulet4.P4Int.t := P4int.pre_t;
           Poulet4.P4String.coq_AList := pre_AListString;
           Bigint.t := Util.bigint;
           coq_Expression := pre_Expression;
           coq_Block := pre_Block;
           coq_ParserState := pre_ParserState;
           coq_TableKey := pre_TableKey;
           coq_TableActionRef := pre_TableActionRef;
           coq_TableEntry := pre_TableEntry;
           coq_TableProperty := pre_TableProperty;
           coq_DeclarationField := pre_DeclarationField;
           coq_MethodPrototype := pre_MethodPrototype;
           coq_Initializer := pre_Initializer]]
  [@@deriving sexp,show,yojson]
type 'a pre_ExternMethod =
  [%import:'a Poulet4.Syntax.coq_ExternMethod
    [@with Poulet4.P4String.t := P4string.pre_t;
           Poulet4.Typed.coq_FunctionType := pre_FunctionType]]
  [@@deriving sexp,show,yojson]
type 'a pre_ExternMethods =
  [%import:'a Poulet4.Syntax.coq_ExternMethods
    [@with coq_ExternMethod := pre_ExternMethod;
           Poulet4.P4String.t := P4string.pre_t]]
  [@@deriving sexp,show,yojson]
type 'a pre_program =
  [%import:'a Poulet4.Syntax.program
    [@with coq_Declaration := pre_Declaration]]
  [@@deriving sexp,show,yojson]
type coq_MatchPreT = P4info.t pre_MatchPreT
  [@@deriving sexp,show,yojson]
type coq_Match = P4info.t pre_Match
  [@@deriving sexp,show,yojson]
type coq_TablePreActionRef = P4info.t pre_TablePreActionRef
  [@@deriving sexp,show,yojson]
type coq_TableActionRef = P4info.t pre_TableActionRef
  [@@deriving sexp,show,yojson]
type coq_TableKey = P4info.t pre_TableKey
  [@@deriving sexp,show,yojson]
type coq_TableEntry = P4info.t pre_TableEntry
  [@@deriving sexp,show,yojson]
type coq_TableProperty = P4info.t pre_TableProperty
  [@@deriving sexp,show,yojson]

type coq_StatementSwitchLabel = P4info.t pre_StatementSwitchLabel
  [@@deriving sexp,show,yojson]
type coq_StatementSwitchCase = P4info.t pre_StatementSwitchCase
  [@@deriving sexp,show,yojson]
type coq_StatementPreT = P4info.t pre_StatementPreT
  [@@deriving sexp,show,yojson]
type coq_Statement = P4info.t pre_Statement
  [@@deriving sexp,show,yojson]
type coq_Block = P4info.t pre_Block
  [@@deriving sexp,show,yojson]
type coq_Initializer = P4info.t pre_Initializer
  [@@deriving sexp,show,yojson]
type coq_ParserCase = P4info.t pre_ParserCase
  [@@deriving sexp,show,yojson]
type coq_ParserTransition = P4info.t pre_ParserTransition
  [@@deriving sexp,show,yojson]
type coq_ParserState = P4info.t pre_ParserState
  [@@deriving sexp,show,yojson]
type coq_DeclarationField = P4info.t pre_DeclarationField
  [@@deriving sexp,show,yojson]
type coq_Declaration = P4info.t pre_Declaration
  [@@deriving sexp,show,yojson]
type coq_ExternMethod = P4info.t pre_ExternMethod
  [@@deriving sexp,show,yojson]
type coq_ExternMethods = P4info.t pre_ExternMethods
  [@@deriving sexp,show,yojson]
type 'a pre_Value =
  [%import:'a Poulet4.ConstValue.coq_Value
             [@with Poulet4.P4String.t := P4string.pre_t;
                    Bigint.t := Util.bigint;
                    Poulet4.P4String.coq_AList := pre_AListString]]
  [@@deriving sexp,show,yojson]
type coq_Value = P4info.t pre_Value
  [@@deriving sexp,show,yojson]
type program = P4info.t pre_program
  [@@deriving sexp,show,yojson]

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
