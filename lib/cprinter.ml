open Pp
open Pp.O
open Csyntax

let format_cname (name: cname) =
  text name

let rec format_ctyp (typ: ctyp) =
  match typ with
  | CVoid -> text "void"
  | CInt -> text "int"
  | CChar -> text "char"
  | CUInt -> text "unsigned int"
  | CBool -> text "bool"
  | CStruct name -> text "struct " ++ format_cname name
  | CPtr typ -> text "(" ++ format_ctyp typ ++ text "*)"

let rec format_cdecl (decl: cdecl) =
  match decl with
  | CStruct (name, fields) ->
    text "struct " ++ format_cname name ++ text " {"
    ++ concat_map ~sep:(text ";\n") ~f:format_cfield fields
    ++ text "}"
  | CFun (ret, name, params, body) ->
    format_ctyp ret
    ++ space
    ++ format_cname name
    ++ format_cparams params
    ++ text "\n{"
    ++ format_cstmts body
    ++ text "}"

and format_cfield ((CField (typ, name)): cfield) =
  format_ctyp typ ++ space ++ format_cname name

and format_cparam ((CParam (typ, name)): cparam) =
  format_ctyp typ ++ space ++ format_cname name

and format_cparams (params: cparam list) =
  concat_map ~sep:(text ", ") ~f:format_cparam params

and format_cstmt (stmt: cstmt) =
  match stmt with
  | CRet expr ->
    text "return " ++ format_cexpr expr
  | CSeq (e1, e2) ->
    format_cstmt e1 ++ text ";\n" ++ format_cstmt e2
  | CIf (cond, true_branch, false_branch) ->
    text "if (" ++ format_cexpr cond ++ text ") {\n"
    ++ format_cstmt true_branch
    ++ text "\n} else {\n"
    ++ format_cstmt false_branch
  | CAssign (lval, rval) ->
    format_cexpr lval ++ text " = " ++ format_cexpr rval
  | CVarInit (typ, var, rval) ->
    format_ctyp typ
    ++ space
    ++ format_cname var
    ++ text " = "
    ++ format_cexpr rval

and format_cstmts (stmts: cstmt list) =
  concat_map ~sep:(text ";\n") ~f:format_cstmt stmts

and format_cexpr (expr: cexpr) =
  match expr with
  | CIntLit i ->
    string_of_int i |> text
  | CStrLit s ->
    text "\"" ++ text (String.escaped s) ++ text "\""
  | CVar name ->
    format_cname name
  | CDeref exp ->
    text "(*" ++ format_cexpr exp ++ text ")"
  | CAddrOf exp ->
    text "(&" ++ format_cexpr exp ++ text ")"
  | CMember (exp, field) ->
    text "(" ++ format_cexpr exp ++ text ")." ++ format_cname field
  | CCall (func, args) ->
    format_cname func
    ++ text "("
    ++ concat_map ~sep:(text ", ") ~f:format_cexpr args
    ++ text ")"
