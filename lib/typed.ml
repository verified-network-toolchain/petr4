open Sexplib.Conv
type direction = [%import:Poulet4.Typed.direction]
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
           Poulet4.P4String.t := P4string.pre_t;
           coq_ControlType := pre_ControlType;
           coq_P4Parameter := pre_P4Parameter;
           coq_FunctionType := pre_FunctionType;
           coq_FieldType := pre_FieldType]]
  [@@deriving sexp,show,yojson]
and 'a pre_FieldType =
  [%import:'a Poulet4.Typed.coq_FieldType
    [@with Poulet4.P4String.t := P4string.pre_t;
           coq_P4Type := pre_P4Type]]
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
and pre_P4Parameter =
  [%import:'a Poulet4.Typed.coq_P4Parameter
    [@with Poulet4.P4String.t := P4string.pre_t;
           coq_P4Type := pre_P4Type]]
  [@@deriving sexp,show,yojson]
type coq_P4Type = Info.t pre_P4Type
[@@deriving sexp,show,yojson]
type coq_FieldType = Info.t pre_FieldType
[@@deriving sexp,show,yojson]
type coq_FunctionType = Info.t pre_FunctionType
[@@deriving sexp,show,yojson]
type coq_ControlType = Info.t pre_ControlType
[@@deriving sexp,show,yojson]
type coq_P4Parameter = Info.t pre_P4Parameter
[@@deriving sexp,show,yojson]

type 'a pre_StmtContext =
  [%import:'a Poulet4.Typed.coq_StmtContext
    [@with coq_P4Type := pre_P4Type]]
  [@@deriving sexp,show,yojson]
type coq_StmtContext = Info.t pre_StmtContext
  [@@deriving sexp,show,yojson]

type 'a pre_DeclContext =
  [%import:'a Poulet4.Typed.coq_DeclContext
          [@with coq_P4Type := pre_P4Type;
                 coq_StmtContext := pre_StmtContext]]
  [@@deriving sexp,show,yojson]
type coq_DeclContext = Info.t pre_DeclContext
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

let expr_ctxt_of_decl_ctxt (s: coq_DeclContext) : coq_ExprContext =
  match s with
   | DeclCxTopLevel -> ExprCxConstant
   | DeclCxNested -> ExprCxDeclLocals
   | DeclCxStatement c -> expr_ctxt_of_stmt_ctxt c

type 'a info = 'a Types.info

module Annotation = Types.Annotation
