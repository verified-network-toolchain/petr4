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

let my_print_int p z = fprintf p "%s" (Int.to_string z)

let print_bigint p n =
  fprintf p "%s" (Bignum.to_string_accurate (Bignum.of_bigint n))

let print_option printa p (o: ('a option)) = 
  match o with
  | None -> fprintf p "Option<%s>" "None"
  | Some a -> fprintf p "Option<%a>" printa a
let print_uop p u = 
  let s = 
  match u with
  | Expr.Not -> "Not"
  | Expr.BitNot -> "BitNot"
  | Expr.UMinus -> "UMinus"
  | Expr.IsValid -> "IsValid"
  | Expr.SetValidity true -> "SetValid"
  | Expr.SetValidity false -> "SetInValid"
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

let print_paramarg printa printb p (ab : ('a,'b) paramarg) = 
  match ab with
  | PAIn a -> fprintf p "PAIn <%a>" printa a
  | PAOut b -> fprintf p "PAOut <%a>" printb b
  | PAInOut b -> fprintf p "PAInOut <%a>" printb b

let print_list ?(sep="") f p l =
  let print_item b x =
    if b then fprintf p "%s@ " sep;
    f p x ;
    true in
  ignore (List.fold_left print_item false l)

let print_string p s =
  fprintf p "%s" s

let print_field print1 print2 p (f: 'a * 'b) = 
  fprintf p "@[%a = %a@]" 
    print1 (fst f)
    print2 (snd f)

let print_fields print1 print2 p (f : ('a * 'b) list) =
   if (List.length f <> 0) then
    fprintf p "<%a>" (print_list ~sep:"," (print_field print1 print2)) f
  else ()


let print_arrow printk printa printb p (ar: ('k,'a,'b) arrow) =
  fprintf p "@[paramargs: <%a>, rtrns: <%a>@]"
    (print_fields printk (print_paramarg printa printb)) ar.paramargs
    (print_option printb) ar.rtrns 


let print_string_string_field =
  print_field print_string print_string


let print_string_string_fields p (f: (string * string) list) =
  if (List.length f <> 0) then
    fprintf p "<%a>" (print_list ~sep:"," print_string_string_field) f
  else ()  




let rec print_type p (t:Expr.t) = 
  match t with
  | Expr.TBool -> fprintf p "%s" "TBool"
  | Expr.TBit i -> fprintf p "TBit: @[%a@]" print_bigint i 
  | Expr.TInt i -> fprintf p "TInt: @[%a@]" print_bigint i 
  | Expr.TError -> fprintf p "%s" "TError" 
  | Expr.TStruct (false,lt) -> fprintf p "TStruct <%a>" (print_list ~sep:"*" print_type) lt
  | Expr.TStruct (true,lt) -> fprintf p "THeader <%a>" (print_list ~sep:"*" print_type) lt
  | Expr.TArray (l, t) -> fprintf p "THeaderStack <%a> [%a]" 
                                  print_type t
                                  print_bigint l  
  | Expr.TVar n -> fprintf p "TVar <%a>" my_print_int n

let print_params p (pa: Expr.params) = 
  print_fields print_string (print_paramarg print_type print_type) p pa

let print_arrowT = print_arrow print_string print_type print_type

let print_ct p = 
  function
  | TopDecl.ControlInstType (fs, pa) ->
    fprintf p "CTControl <extern: %a> (%a)"
      (print_list print_string) fs
      print_params pa
  | TopDecl.ParserInstType (fs, pa) ->
    fprintf p "CTParser <extern: %a> (%a)"
      (print_list print_string) fs
      print_params pa
  | TopDecl.PackageInstType  -> 
    fprintf p "CTPackage"
  | TopDecl.ExternInstType s ->
    fprintf p "CTExtern %a"
      print_string s

let print_constructor_params = 
  print_fields print_string print_ct

let rec print_expr p =
  function
  | Expr.Bool b -> fprintf p "EBool %a" print_bool b
  | Expr.Bit (w, i) -> fprintf p "EBit <%a> %a" print_bigint w print_bigint i
  | Expr.Int (w, i) -> fprintf p "EInt <%a> %a" print_bigint w print_bigint i
  | Expr.Var (typ, x, n) ->
    fprintf p "EVar : <%a> %a %a" print_type typ print_string x
    my_print_int n
  | Expr.Slice (l, r , e) -> fprintf p "ESlice : <%a>[%a : %a]"
                                print_expr e
                                print_bigint l
                                print_bigint r

  | Expr.Cast (typ, e') -> fprintf p "ECast <%a> %a" 
                                print_type typ
                                print_expr e'
  | Expr.Uop (typ, u, e') -> fprintf p "EUop <%a> %a @[%a @]"
                                  print_type typ
                                  print_uop u
                                  print_expr e'

  | Expr.Bop (typ, b, e1, e2) -> 
        fprintf p "EBop <%a> %a (@[%a@] @[%a@])"
        print_type typ
        print_bop b
        print_expr e1 
        print_expr e2
  
  | Expr.Lists (Expr.Coq_lists_struct,fs) ->
        fprintf p "EStruct @[%a@]"
        (print_list ~sep:"," print_expr) fs
  | Expr.Lists (Expr.Coq_lists_header b, fs) ->
        fprintf p "EHeader <Valid: %a> @[%a@]"
        print_bool b
        (print_list ~sep:"," print_expr) fs
  | Expr.Member (typ, m, a) ->
        fprintf p "EMember <%a> @[%a@].%a"
        print_type typ
        print_expr a 
        my_print_int m
  | Expr.Error err ->
        fprintf p "Error @[%a@]"
        print_string err
  | Expr.Lists (Expr.Coq_lists_array t, el) ->
        fprintf p "EArray <%a> @[%a@]"
        print_type t
        (print_list ~sep:"," (print_expr)) el 
  | Expr.Index (t, e1, e2) ->
        fprintf p "EIndex <%a> @[%a.@[%a@] @]"
        print_type t
        print_expr e1
        print_expr e2


let print_args p (a : Expr.args) =
  (print_list ~sep:"," (print_paramarg print_expr print_expr)) p a

let print_constructor_args p (c : TopDecl.constructor_args) =
  (print_list ~sep:"," print_string) p c

let print_sum print1 print2 p (s: ('a,'b) Poulet4.Datatypes.sum) = 
  match s with 
  | Poulet4.Datatypes.Coq_inl a -> print1 p a
  | Poulet4.Datatypes.Coq_inr b -> print2 p b

let print_parser_state_label p (s: Parser.state_label) = 
  match s with
  | Parser.Start -> fprintf p "%s" "(STStart)"
  | Parser.Accept -> fprintf p "%s" "(STAccept)"
  | Parser.Reject -> fprintf p "%s" "(STReject)"
  | Parser.Name name -> fprintf p "(STName %a)" my_print_int name

let rec print_pat p (pat: Parser.pat) = 
  match pat with
  | Parser.Wild -> fprintf p "Wild"
  | Parser.Mask (p1,p2) -> 
      fprintf p "Mask(%a, %a)"
      print_pat p1
      print_pat p2
  | Parser.Range (p1,p2) ->
      fprintf p "Range(%a, %a)"
      print_pat p1
      print_pat p2
  | Parser.Bit (w,v) ->
      fprintf p "Bit<%a> (%a)"
      print_bigint w
      print_bigint v
  | Parser.Int (w,v) ->
      fprintf p "Int<%a> (%a)"
      print_bigint w
      print_bigint v
  | Parser.Lists pl ->
      fprintf p "Tuple@[%a@]"
      (print_list print_pat) pl


let print_parser_expr p (e: Parser.trns) = 
  match e with 
  | Parser.Direct s -> fprintf p "PGoto (%a)" print_parser_state_label s
  | Parser.Select (e, st, fs) -> 
    fprintf p "PSelect (discriminate := %a, default := %a, cases = %a) "
    print_expr e
    print_parser_state_label st
    (print_fields print_pat print_parser_state_label) fs

let rec print_stmt p =
  function
  | Stmt.Transition t ->
    fprintf p "Transition %a" print_parser_expr t
  | Stmt.Skip -> fprintf p "SSkip"
  | Stmt.Var (x, sum, s) -> 
    fprintf p "SVardecl @[Name: %a@] @[Init: %a@]) %a@"
    print_string x
    (print_sum print_type print_expr) sum
    print_stmt s
  | Stmt.Assign (e1, e2) ->
    fprintf p "SAssign @[%a := %a@]"
    print_expr e1
    print_expr e2
  | Stmt.Conditional (e,s1,s2) ->
    fprintf p "SConditional @[if (%a) then (%a) else (%a)@]" 
    print_expr e
    print_stmt s1
    print_stmt s2
  | Stmt.Seq (s1,s2) ->
    fprintf p "SSeq @[%a \n %a@]"
    print_stmt s1 
    print_stmt s2
  | Stmt.Call (Stmt.Method (name, meth, tl, e), args) ->
    fprintf p "SExternMethodCall %s.%s <%a>(%a) %a"
    name
    meth
    ((print_list ~sep:"," print_type)) tl
    print_args args
    (print_option print_expr) e
  
  | Stmt.Call (Stmt.Funct (s, tl, e), args) ->
    fprintf p "SFunCall %s<%a>(%a) %a"
    s
    ((print_list ~sep:"," print_type)) tl
    print_args args
    (print_option print_expr) e
  
  | Stmt.Call (Stmt.Action (s, ctrl_args), data_args) ->
    fprintf p "SActCall %s(%a)(%a)"
    s
    (print_list ~sep:"," print_expr) ctrl_args
    print_args data_args

  | Stmt.Return eo ->
    fprintf p "SReturn %a"
    (print_option print_expr) eo

  | Stmt.Exit ->
    fprintf p "SExit"

  | Stmt.Invoke s ->
    fprintf p "SInvoke %s" s

  | Stmt.Apply (s, fs, arg) ->
    fprintf p "SApply @[%s, Ext_args = %a, args = %a@]"
    s
    (print_list ~sep:"," print_string) fs
    print_args arg

let print_control_d p (d : Control.d) =
  match d with
  | Control.Var (x,te) ->
    fprintf p "CDVardecl @[Name: %a@] @[Init: %a@])"
    print_string x
    (print_sum print_type print_expr) te
  | Control.Action (s, ctrl_params, data_params, st) ->
    fprintf p "CDAction %s(%a)(%a){%a}"
    s
    (print_fields print_string print_type) ctrl_params
    print_params data_params
    print_stmt st
  | Control.Table (s, key, ss) ->
    fprintf p "CDTable %s (%a) %a"
    s
    (print_fields print_expr print_string) key
    (print_fields print_string print_args) ss

let print_tp_decl p (d: TopDecl.d) =
  match d with 
  | TopDecl.Instantiate (constructor_name, instance_name, type_args, cargs, es) ->
    fprintf p "@[Instantiate \n (constructor_name = %a) \n (instance_name = %a)
    \n (type_args = %a) \n (cargs = %a) (%a) @]"
    print_string constructor_name
    print_string instance_name
    (print_list print_type) type_args
    print_constructor_args cargs
    (print_list ~sep:"," print_expr) es
  | TopDecl.Extern (extern_name, type_params, cparams, eparams, methods) ->
    fprintf p "@[Extern \n (extern_name = %a) \n (type_params = %a) \n
    (cparams = %a) (%a) \n (methods = %a) @]" 
    print_string extern_name
    my_print_int type_params
    print_constructor_params cparams
    (print_list ~sep:"," print_type) eparams
    (print_fields print_string 
      (fun p ((tparams,eparams),arr) ->
      fprintf p "<%a>(%a)(%a)"
        my_print_int tparams
        (print_list ~sep:"," print_string) eparams
        print_arrowT arr
      )
    ) methods

  | TopDecl.Control (control_name, cparams, ts, eparams, params, body, apply_blk) ->
    fprintf p "@[Control \n (control_name = %a) \n (cparams = %a)
              \n (%a) \n (eparams = %a)
              \n (params = %a) \n (body = %a) \n (apply_blk = %a)@] "
    print_string control_name
    print_constructor_params cparams
    (print_list ~sep:"," print_type) ts
    print_string_string_fields eparams
    print_params params
    (print_list ~sep:";" print_control_d) body 
    print_stmt apply_blk

  | TopDecl.Parser (name, constructors, ts, fields, params, state, states) ->
    fprintf p "@[Parser \n (name = %a) \n (cparams = %a)
              \n (%a) \n (eparams = %a)
              \n (params = %a) \n (start = %a) \n (states = %a)@] "
    print_string name
    print_constructor_params constructors
    (print_list ~sep:"," print_type) ts
    print_string_string_fields fields
    print_params params
    print_stmt state
    (print_list ~sep:";" print_stmt) states
  
  | TopDecl.Funct (function_name, type_params, signature, body) ->
    fprintf p "@[Function \n (function_name = %a) \n (type_params = %a) \n
      (signature = %a) \n (body = %a) @]"
    print_string function_name
    my_print_int type_params
    print_arrowT signature
    print_stmt body

let print_prog p = fprintf p "%a" (print_list ~sep:"," print_tp_decl)
