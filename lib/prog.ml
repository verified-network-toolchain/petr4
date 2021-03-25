open Sexplib.Conv
module T = Typed

type ('a, 'b) sum = [%import:('a, 'b) Poulet4.Datatypes.sum]
  [@@deriving sexp,show,yojson]
type ('a, 'b) pre_AList =
  [%import:('a, 'b) Poulet4.AList.coq_AList]
  [@@deriving sexp,show,yojson]
type ('a, 'b) pre_AListString =
  [%import:('a, 'b) Poulet4.P4String.coq_AList
    [@with t := P4string.pre_t; Poulet4.AList.coq_AList := pre_AList]]
  [@@deriving sexp,show,yojson]
type 'a pre_MethodPrototype =
  [%import:'a Poulet4.Syntax.coq_MethodPrototype
    [@with Poulet4.P4String.t := P4string.pre_t;
           Poulet4.Typed.coq_P4Type := T.pre_P4Type;
           Poulet4.Typed.coq_P4Parameter := T.pre_P4Parameter]]
  [@@deriving sexp,show,yojson]
type coq_MethodPrototype = Info.t pre_MethodPrototype
  [@@deriving sexp,show,yojson]
type coq_OpUni = [%import:Poulet4.Syntax.coq_OpUni]
  [@@deriving sexp,show,yojson]
type coq_OpBin = [%import:Poulet4.Syntax.coq_OpBin]
  [@@deriving sexp,show,yojson]
type 'a pre_KeyValue =
  [%import:'a Poulet4.Syntax.coq_KeyValue
    [@with Bigint.t := Util.bigint;
           Poulet4.P4String.t := P4string.pre_t;
           coq_Expression := pre_Expression]]
  [@@deriving sexp,show,yojson]
and 'a pre_ExpressionPreT =
  [%import:'a Poulet4.Syntax.coq_ExpressionPreT
    [@with coq_Expression := pre_Expression;
      Bigint.t := Util.bigint;
      Poulet4.P4String.t := P4string.pre_t;
      Poulet4.P4Int.t := P4int.pre_t;
      Poulet4.Typed.name := P4name.pre_t;
      Poulet4.Typed.coq_P4Type := T.pre_P4Type;
      Poulet4.Typed.direction := T.direction;
      coq_KeyValue := pre_KeyValue]]
  [@@deriving sexp,show,yojson]
and 'a pre_Expression =
  [%import:'a Poulet4.Syntax.coq_Expression
    [@with coq_ExpressionPreT := pre_ExpressionPreT;
      Poulet4.Typed.direction := T.direction;
      Poulet4.Typed.coq_P4Type := T.pre_P4Type]]
  [@@deriving sexp,show,yojson]
type coq_KeyValue = Info.t pre_KeyValue
  [@@deriving sexp,show,yojson]
type coq_ExpressionPreT = Info.t pre_ExpressionPreT
  [@@deriving sexp,show,yojson]
type coq_Expression = Info.t pre_Expression
  [@@deriving sexp,show,yojson]
type 'a pre_MatchPreT =
  [%import:'a Poulet4.Syntax.coq_MatchPreT
    [@with coq_Expression := pre_Expression]]
  [@@deriving sexp,show,yojson]
type 'a pre_Match =
  [%import:'a Poulet4.Syntax.coq_Match
    [@with coq_MatchPreT := pre_MatchPreT;
           Poulet4.Typed.coq_P4Type := T.pre_P4Type]]
  [@@deriving sexp,show,yojson]
type 'a pre_TablePreActionRef =
  [%import:'a Poulet4.Syntax.coq_TablePreActionRef
    [@with Poulet4.Typed.name := P4name.pre_t;
           coq_Expression := pre_Expression]]
  [@@deriving sexp,show,yojson]
type 'a pre_TableActionRef =
  [%import:'a Poulet4.Syntax.coq_TableActionRef
    [@with Poulet4.Typed.coq_P4Type := T.pre_P4Type;
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
type 'a pre_ValueBase =
  [%import:'a Poulet4.Syntax.coq_ValueBase
    [@with Bigint.t := Util.bigint;
           Poulet4.P4String.t := P4string.pre_t;
           Poulet4.P4String.coq_AList := pre_AListString;
           coq_ValueSet := pre_ValueSet]]
  [@@deriving sexp,show,yojson]
and 'a pre_ValueSet =
  [%import:'a Poulet4.Syntax.coq_ValueSet
    [@with Bigint.t := Util.bigint;
           coq_ValueBase := pre_ValueBase;
           coq_Match := pre_Match;
           Poulet4.P4String.coq_AList := pre_AListString]]
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
           Poulet4.Typed.coq_P4Type := T.pre_P4Type;
           coq_Statement := pre_Statement;
           coq_Expression := pre_Expression;
           coq_Block := pre_Block;
           coq_StatementSwitchCase := pre_StatementSwitchCase;
           coq_ValueBase := pre_ValueBase]]
  [@@deriving sexp,show,yojson]
and 'a pre_Statement =
  [%import:'a Poulet4.Syntax.coq_Statement
    [@with Poulet4.P4String.t := P4string.pre_t;
           Poulet4.Typed.coq_StmType := T.coq_StmType;
           coq_StatementPreT := pre_StatementPreT]]
  [@@deriving sexp,show,yojson]
and 'a pre_Block =
  [%import:'a Poulet4.Syntax.coq_Block
          [@with coq_Statement := pre_Statement]]
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
           Poulet4.Typed.coq_P4Type := T.pre_P4Type;
      coq_Match := pre_Match]]
  [@@deriving sexp,show,yojson]
type 'a pre_Declaration =
  [%import:'a Poulet4.Syntax.coq_Declaration
    [@with Poulet4.P4String.t := P4string.pre_t;
           Poulet4.Typed.coq_P4Type := T.pre_P4Type;
           Poulet4.Typed.coq_P4Parameter := T.pre_P4Parameter;
           Poulet4.Datatypes.sum := sum;
           Poulet4.P4Int.t := P4int.pre_t;
           Poulet4.P4String.coq_AList := pre_AListString;
           coq_ValueBase := pre_ValueBase;
           coq_Expression := pre_Expression;
           coq_Block := pre_Block;
           coq_ParserState := pre_ParserState;
           coq_TableKey := pre_TableKey;
           coq_TableActionRef := pre_TableActionRef;
           coq_TableEntry := pre_TableEntry;
           coq_TableProperty := pre_TableProperty;
           coq_DeclarationField := pre_DeclarationField;
           coq_MethodPrototype := pre_MethodPrototype]]
  [@@deriving sexp,show,yojson]
type 'a pre_ValueTable =
  [%import:'a Poulet4.Syntax.coq_ValueTable
    [@with Poulet4.P4String.t := P4string.pre_t;
           coq_TableKey := pre_TableKey;
           coq_TableActionRef := pre_TableActionRef;
           coq_TableEntry := pre_TableEntry]]
  [@@deriving sexp,show,yojson]
type ('tags_t, 'binding) coq_Env_env =
  [%import:('a, 'binding) Poulet4.Syntax.coq_Env_env
    [@with Poulet4.P4String.t := P4string.pre_t;
           Poulet4.P4String.coq_AList := pre_AListString]]
  [@@deriving sexp,show,yojson]
type 'a coq_ValueLoc =
  [%import:'a Poulet4.Syntax.coq_ValueLoc
    [@with Poulet4.P4String.t := P4string.pre_t]]
  [@@deriving sexp,show,yojson]
type 'a pre_Env_EvalEnv =
  [%import:'a Poulet4.Syntax.coq_Env_EvalEnv
    [@with coq_Env_env := coq_Env_env;
           coq_ValueLoc := coq_ValueLoc;
           Poulet4.P4String.t := P4string.pre_t;
           Poulet4.Typed.coq_P4Type := T.pre_P4Type]]
  [@@deriving sexp,show,yojson]
type 'a pre_ExternMethod =
  [%import:'a Poulet4.Syntax.coq_ExternMethod
    [@with Poulet4.P4String.t := P4string.pre_t;
           Poulet4.Typed.coq_FunctionType := T.pre_FunctionType]]
  [@@deriving sexp,show,yojson]
type 'a pre_ExternMethods =
  [%import:'a Poulet4.Syntax.coq_ExternMethods
    [@with coq_ExternMethod := pre_ExternMethod;
           Poulet4.P4String.t := P4string.pre_t]]
  [@@deriving sexp,show,yojson]
type 'a pre_ValuePreLvalue =
  [%import:'a Poulet4.Syntax.coq_ValuePreLvalue
    [@with Poulet4.P4String.t := P4string.pre_t;
           Poulet4.Typed.name := P4name.pre_t;
           Poulet4.Typed.coq_P4Type := T.pre_P4Type;
           coq_ValueLvalue := pre_ValueLvalue]]
  [@@deriving sexp,show,yojson]
and 'a pre_ValueLvalue =
  [%import:'a Poulet4.Syntax.coq_ValueLvalue
    [@with Poulet4.Typed.coq_P4Type := T.pre_P4Type;
           coq_ValuePreLvalue := pre_ValuePreLvalue]]
  [@@deriving sexp,show,yojson]
type 'a pre_ValueFunctionImplementation =
  [%import:'a Poulet4.Syntax.coq_ValueFunctionImplementation
    [@with coq_Env_EvalEnv := pre_Env_EvalEnv;
           coq_ValueLvalue := pre_ValueLvalue;
           Poulet4.P4String.t := P4string.pre_t;
           coq_Block := pre_Block]]
  [@@deriving sexp,show,yojson]
type 'a pre_ValueObject =
  [%import:'a Poulet4.Syntax.coq_ValueObject
    [@with Poulet4.Typed.coq_P4Parameter := T.pre_P4Parameter;
           Poulet4.P4String.t := P4string.pre_t;
           Poulet4.P4String.coq_AList := pre_AListString;
           coq_Env_EvalEnv := pre_Env_EvalEnv;
           coq_Declaration := pre_Declaration;
           coq_ParserState := pre_ParserState;
           coq_ValueTable := pre_ValueTable;
           coq_Block := pre_Block;
           coq_ValueFunctionImplementation := pre_ValueFunctionImplementation;
           coq_ValueLvalue := pre_ValueLvalue]]
  [@@deriving sexp,show,yojson]
type 'a pre_ValueConstructor =
  [%import:'a Poulet4.Syntax.coq_ValueConstructor
    [@with Poulet4.Typed.coq_P4Parameter := T.pre_P4Parameter;
           Poulet4.P4String.t := P4string.pre_t;
           Poulet4.P4String.coq_AList := pre_AListString;
           coq_Env_EvalEnv := pre_Env_EvalEnv;
           coq_Declaration := pre_Declaration;
           coq_ParserState := pre_ParserState;
           coq_ValueTable := pre_ValueTable;
           coq_Block := pre_Block]]
  [@@deriving sexp,show,yojson]
type 'a pre_Value =
  [%import:'a Poulet4.Syntax.coq_Value
    [@with coq_ValueBase := pre_ValueBase;
           coq_ValueLvalue := pre_ValueLvalue;
           coq_ValueObject := pre_ValueObject;
           coq_ValueConstructor := pre_ValueConstructor]]
  [@@deriving sexp,show,yojson]
type 'a pre_program =
  [%import:'a Poulet4.Syntax.program
    [@with coq_Declaration := pre_Declaration]]
  [@@deriving sexp,show,yojson]
type coq_MatchPreT = Info.t pre_MatchPreT
  [@@deriving sexp,show,yojson]
type coq_Match = Info.t pre_Match
  [@@deriving sexp,show,yojson]
type coq_TablePreActionRef = Info.t pre_TablePreActionRef
  [@@deriving sexp,show,yojson]
type coq_TableActionRef = Info.t pre_TableActionRef
  [@@deriving sexp,show,yojson]
type coq_TableKey = Info.t pre_TableKey
  [@@deriving sexp,show,yojson]
type coq_TableEntry = Info.t pre_TableEntry
  [@@deriving sexp,show,yojson]
type coq_TableProperty = Info.t pre_TableProperty
  [@@deriving sexp,show,yojson]

type coq_ValueBase = Info.t pre_ValueBase
  [@@deriving sexp,show,yojson]
type coq_ValueSet = Info.t pre_ValueSet
  [@@deriving sexp,show,yojson]
type coq_StatementSwitchLabel = Info.t pre_StatementSwitchLabel
  [@@deriving sexp,show,yojson]
type coq_StatementSwitchCase = Info.t pre_StatementSwitchCase
  [@@deriving sexp,show,yojson]
type coq_StatementPreT = Info.t pre_StatementPreT
  [@@deriving sexp,show,yojson]
type coq_Statement = Info.t pre_Statement
  [@@deriving sexp,show,yojson]
type coq_Block = Info.t pre_Block
  [@@deriving sexp,show,yojson]
type coq_ParserCase = Info.t pre_ParserCase
  [@@deriving sexp,show,yojson]
type coq_ParserTransition = Info.t pre_ParserTransition
  [@@deriving sexp,show,yojson]
type coq_ParserState = Info.t pre_ParserState
  [@@deriving sexp,show,yojson]
type coq_DeclarationField = Info.t pre_DeclarationField
  [@@deriving sexp,show,yojson]
type coq_Declaration = Info.t pre_Declaration
  [@@deriving sexp,show,yojson]
type coq_ValueTable = Info.t pre_ValueTable
  [@@deriving sexp,show,yojson]
type coq_Env_EvalEnv = Info.t pre_Env_EvalEnv
  [@@deriving sexp,show,yojson]
type coq_ExternMethod = Info.t pre_ExternMethod
  [@@deriving sexp,show,yojson]
type coq_ExternMethods = Info.t pre_ExternMethods
  [@@deriving sexp,show,yojson]
type coq_ValuePreLvalue = Info.t pre_ValuePreLvalue
  [@@deriving sexp,show,yojson]
type coq_ValueLvalue = Info.t pre_ValueLvalue
  [@@deriving sexp,show,yojson]
type coq_ValueFunctionImplementation = Info.t pre_ValueFunctionImplementation
  [@@deriving sexp,show,yojson]
type coq_ValueObject = Info.t pre_ValueObject
  [@@deriving sexp,show,yojson]
type coq_ValueConstructor = Info.t pre_ValueConstructor
  [@@deriving sexp,show,yojson]
type coq_Value = Info.t pre_Value
  [@@deriving sexp,show,yojson]
type program = Info.t pre_program
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
