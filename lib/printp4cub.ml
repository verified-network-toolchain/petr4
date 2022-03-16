open Format
open Poulet4.AST
(* open Poulet4.P4Field *)
(***********************************************
              P4cub.ml -> Sexp
 ***********************************************)
let print_bool p b = 
    let s = 
    match b with 
    | true -> "true"
    | false -> "false"
  in fprintf p "%s" s

let print_bigint p n =
  fprintf p "%s" (Bignum.to_string_accurate (Bignum.of_bigint n))

let print_list ?(sep="") f p l =
  let print_item b x =
    if b then fprintf p "%s " sep;
    f p x ;
    true in
  ignore (List.fold_left print_item false l)

let print_string_string_field p (f: (string, string) F.f) =
  fprintf p "@[:%s = %s @]" (fst f) (snd f)


let print_string_string_fields p (f: (string, string) F.fs ) =
  if (List.length f <> 0) then
    fprintf p "<%a>" (print_list ~sep:"," print_string_string_field) f
  else ()  


let print_type p (t:Expr.t) = 
  match t with 
  | Expr.TBool -> fprintf p "%s" " (TBool) "
  | _ -> fprintf p "(%s)" "unimplemented"

let print_expr p (e: 'a Expr.e) = 
  match e with 
  | Expr.EBool (b, _) -> fprintf p "(Ebool %a)" print_bool b
  | _ -> fprintf p "(%s)" "unimplemented"

let print_stmt p (s: 'a Stmt.s) =
  match s with
  | Stmt.SSkip (_) -> fprintf p "(%s)" "unimplemented"
  | _ -> fprintf p "(%s)" "unimplemented"
 

let print_parser_state p (s: Parser.state) = 
  match s with 
  | Parser.STStart -> fprintf p "%s" "(STStart)"
  | Parser.STAccept -> fprintf p "%s" "(STAccept)"
  | Parser.STReject -> fprintf p "%s" "(STReject)"
  | Parser.STName (name) -> fprintf p "(STName %s)" name

let print_parser_expr p (e: 'a Parser.e) = 
  match e with 
  | Parser.PGoto (s,_) -> fprintf p "(Ebool %a)" print_parser_state s
  | _ -> fprintf p "(%s)" "unimplemented"

let print_parser_state_block p (st: 'a Parser.state_block) = 
  fprintf p "(Stateblock \n 
              (stmt %a) \n
              (trans %a) \n
              )"
  print_stmt st.stmt 
  print_parser_expr st.trans


let print_tp_decl p (d: 'a TopDecl.d) = 
  match d with 
  | TPParser (name, constructors, fields, params, state, states,_) ->
    fprintf p "(%s)" "unimplemented"
  | _ -> fprintf p "(%s)" "unimplemented"