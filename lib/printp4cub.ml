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

let print_uop p u = 
  let s = 
  match u with
  | Expr.Not -> "Not"
  | Expr.BitNot -> "BitNot"
  | Expr.UMinus -> "UMinus"
  | Expr.IsValid -> "IsValid"
  | Expr.SetValid -> "SetValid"
  | Expr.SetInValid -> "SetInValid"
  | Expr.NextIndex -> "NextIndex"
  | Expr.Size -> "Size"
  in
fprintf p "%s" s

let print_bop p b = 
 let s = 
  match b with
  | Expr.Plus -> "Plus"
  | Expr.PlusSat -> "PlusSat"
  | Expr.Minus -> "Minus"
  | Expr.MinusSat -> "MinusSat"
  | Expr.Times -> "Times"
  | Expr.Shl -> "Shl"
  | Expr.Shr -> "Shr"
  | Expr.Le -> "Le"
  | Expr.Ge -> "Ge"
  | Expr.Lt -> "Lt"
  | Expr.Gt -> "Gt"
  | Expr.Eq -> "Eq"
  | Expr.NotEq -> "NotEq"
  | Expr.BitAnd -> "BitAnd"
  | Expr.BitXor -> "BitXor"
  | Expr.BitOr -> "BitOr"
  | Expr.PlusPlus -> "PlusPlus"
  | Expr.And -> "And"
  | Expr.Or -> "Or"
  in
  fprintf p "%s" s

let print_matchkind p m = 
  let s = 
  match m with
  | Expr.MKExact -> "MKExact"
  | Expr.MKTernary -> "MKTernary"
  | Expr.MKLpm -> "MKLpm"
  in
fprintf p "%s" s

let print_list ?(sep="") f p l =
  let print_item b x =
    if b then fprintf p "%s@ " sep;
    f p x ;
    true in
  ignore (List.fold_left print_item false l)

let print_string p s =
  fprintf p "%s" s

let print_field print1 print2 p (f: ('a, 'b) F.f)  = 
  fprintf p "@[%a = %a@]" 
    print1 (fst f)
    print2 (snd f)

let print_fields print1 print2 p (f : ('a, 'b) F.fs) = 
   if (List.length f <> 0) then
    fprintf p "<%a>" (print_list ~sep:"," (print_field print1 print2)) f
  else ()

let print_string_string_field p (f: (string, string) F.f) =
  print_field print_string print_string p f 


let print_string_string_fields p (f: (string, string) F.fs ) =
  if (List.length f <> 0) then
    fprintf p "<%a>" (print_list ~sep:"," print_string_string_field) f
  else ()  




let rec print_type p (t:Expr.t) = 
  match t with 
  | Expr.TBool -> fprintf p "%s" "TBool"
  | Expr.TBit i -> fprintf p "TBit: @[%a@]" print_bigint i 
  | Expr.TInt i -> fprintf p "TInt: @[%a@]" print_bigint i 
  | Expr.TError -> fprintf p "%s" "TError" 
  | Expr.TTuple lt -> fprintf p "TTuple <%a>" (print_list ~sep:"*" print_type) lt
  | Expr.TStruct ts -> fprintf p "TStruct <%a>" (print_fields print_string print_type) ts  
  | Expr.THeader th -> fprintf p "THeader <%a>" (print_fields print_string print_type) th  
  | Expr.THeaderStack (ths, l) -> fprintf p "THeaderStack <%a> [%a]" 
                                  (print_fields print_string print_type) ths
                                  print_bigint l  

  | Expr.TVar n -> fprintf p "Tvar %s" n 

let rec print_expr p (e: 'a Expr.e) = 
  match e with 
  | Expr.EBool (b, _) -> fprintf p "EBool %a" print_bool b
  | Expr.EBit (w, i, _) -> fprintf p "EBit <%a> %a" print_bigint w print_bigint i
  | Expr.EInt (w, i, _) -> fprintf p "EInt <%a> %a" print_bigint w print_bigint i
  | Expr.EVar (typ, x, _) -> fprintf p "EVar : <%a> %a" print_type typ print_string x
  | Expr.ESlice (e', l, r , _) -> fprintf p "ESlice : <%a>[%a : %a]"
                                print_expr e'
                                print_bigint l
                                print_bigint r

  | Expr.ECast (typ, e', _) -> fprintf p "ECast <%a> %a" 
                                print_type typ
                                print_expr e'
  | Expr.EUop (typ, u, e', _) -> fprintf p "EUop <%a> %a @[%a @]"
                                  print_type typ
                                  print_uop u
                                  print_expr e'
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