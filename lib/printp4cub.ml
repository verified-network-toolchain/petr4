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
let print_una p u = 
  let s = 
  match u with
  | Una.Not -> "Not"
  | Una.BitNot -> "BitNot"
  | Una.Minus -> "UMinus"
  | Una.IsValid -> "IsValid"
  | Una.SetValidity true -> "SetValid"
  | Una.SetValidity false -> "SetInValid"
  in
fprintf p "%s" s

let print_bin p b = 
 let s = 
  match b with
  | Bin.Plus -> "Plus"
  | Bin.PlusSat -> "PlusSat"
  | Bin.Minus -> "Minus"
  | Bin.MinusSat -> "MinusSat"
  | Bin.Times -> "Times"
  | Bin.Shl -> "Shl"
  | Bin.Shr -> "Shr"
  | Bin.Le -> "Le"
  | Bin.Ge -> "Ge"
  | Bin.Lt -> "Lt"
  | Bin.Gt -> "Gt"
  | Bin.Eq -> "Eq"
  | Bin.NotEq -> "NotEq"
  | Bin.BitAnd -> "BitAnd"
  | Bin.BitXor -> "BitXor"
  | Bin.BitOr -> "BitOr"
  | Bin.PlusPlus -> "PlusPlus"
  | Bin.And -> "And"
  | Bin.Or -> "Or"
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




let rec print_type p (t:Typ.t) = 
  match t with
  | Typ.Bool -> fprintf p "%s" "TBool"
  | Typ.Bit i -> fprintf p "TBit: @[%a@]" print_bigint i 
  | Typ.Int i -> fprintf p "TInt: @[%a@]" print_bigint i
  | Typ.VarBit i -> fprintf p "TVarBit: @[%a@]" print_bigint i 
  | Typ.Error -> fprintf p "%s" "TError" 
  | Typ.Struct (false,lt) -> fprintf p "TStruct <%a>" (print_list ~sep:"*" print_type) lt
  | Typ.Struct (true,lt) -> fprintf p "THeader <%a>" (print_list ~sep:"*" print_type) lt
  | Typ.Array (l, t) -> fprintf p "THeaderStack <%a> [%a]" 
                                  print_type t
                                  print_bigint l  
  | Typ.Var n -> fprintf p "TVar <%a>" my_print_int n

let print_params p (pa: Typ.params) = 
  print_fields print_string (print_paramarg print_type print_type) p pa

let print_arrowT = print_arrow print_string print_type print_type

let print_ct p = 
  function
  | InstTyp.Ctr (Cnstr.Control, fs, pa) ->
    fprintf p "CTControl <extern: %a> (%a)"
      (print_list print_string) fs
      print_params pa
  | InstTyp.Ctr (Cnstr.Parser, fs, pa) ->
    fprintf p "CTParser <extern: %a> (%a)"
      (print_list print_string) fs
      print_params pa
  | InstTyp.Package  -> 
    fprintf p "CTPackage"
  | InstTyp.Extern s ->
    fprintf p "CTExtern %a"
      print_string s

let print_constructor_params = 
  print_fields print_string print_ct

let rec print_exp p =
  function
  | Exp.Bool b -> fprintf p "EBool %a" print_bool b
  | Exp.Bit (w, i) -> fprintf p "EBit <%a> %a" print_bigint w print_bigint i
  | Exp.Int (w, i) -> fprintf p "EInt <%a> %a" print_bigint w print_bigint i
  | Exp.VarBit (mw, w, i) -> fprintf p "EVarBit <%a> %a %a" print_bigint mw  print_bigint w print_bigint i
  | Exp.Var (typ, x, n) ->
    fprintf p "EVar : <%a> %a %a" print_type typ print_string x
    my_print_int n
  | Exp.Slice (l, r , e) -> fprintf p "ESlice : <%a>[%a : %a]"
                                print_exp e
                                print_bigint l
                                print_bigint r

  | Exp.Cast (typ, e') -> fprintf p "ECast <%a> %a" 
                                print_type typ
                                print_exp e'
  | Exp.Uop (typ, u, e') -> fprintf p "EUna <%a> %a @[%a @]"
                                  print_type typ
                                  print_una u
                                  print_exp e'

  | Exp.Bop (typ, b, e1, e2) -> 
        fprintf p "EBop <%a> %a (@[%a@] @[%a@])"
        print_type typ
        print_bin b
        print_exp e1 
        print_exp e2
  
  | Exp.Lists (Lst.Struct,fs) ->
        fprintf p "EStruct @[%a@]"
        (print_list ~sep:"," print_exp) fs
  | Exp.Lists (Lst.Header b, fs) ->
        fprintf p "EHeader <Valid: %a> @[%a@]"
        print_bool b
        (print_list ~sep:"," print_exp) fs
  | Exp.Member (typ, m, a) ->
        fprintf p "EMember <%a> @[%a@].%a"
        print_type typ
        print_exp a 
        my_print_int m
  | Exp.Error err ->
        fprintf p "Error @[%a@]"
        print_string err
  | Exp.Lists (Lst.Array t, el) ->
        fprintf p "EArray <%a> @[%a@]"
        print_type t
        (print_list ~sep:"," (print_exp)) el 
  | Exp.Index (t, e1, e2) ->
        fprintf p "EIndex <%a> @[%a.@[%a@] @]"
        print_type t
        print_exp e1
        print_exp e2


let print_args p (a : Exp.args) =
  (print_list ~sep:"," (print_paramarg print_exp print_exp)) p a

let print_constructor_args p (c : Top.constructor_args) =
  (print_list ~sep:"," print_string) p c

let print_sum print1 print2 p (s: ('a,'b) Poulet4.Datatypes.sum) = 
  match s with 
  | Poulet4.Datatypes.Coq_inl a -> print1 p a
  | Poulet4.Datatypes.Coq_inr b -> print2 p b

let print_parser_state_label p (s: Lbl.t) = 
  match s with
  | Lbl.Start -> fprintf p "%s" "(STStart)"
  | Lbl.Accept -> fprintf p "%s" "(STAccept)"
  | Lbl.Reject -> fprintf p "%s" "(STReject)"
  | Lbl.Name name -> fprintf p "(STName %a)" my_print_int name

let rec print_pat p (pat: Pat.t) = 
  match pat with
  | Pat.Wild -> fprintf p "Wild"
  | Pat.Mask (p1,p2) -> 
      fprintf p "Mask(%a, %a)"
      print_pat p1
      print_pat p2
  | Pat.Range (p1,p2) ->
      fprintf p "Range(%a, %a)"
      print_pat p1
      print_pat p2
  | Pat.Bit (w,v) ->
      fprintf p "Bit<%a> (%a)"
      print_bigint w
      print_bigint v
  | Pat.Int (w,v) ->
      fprintf p "Int<%a> (%a)"
      print_bigint w
      print_bigint v
  | Pat.Lists pl ->
      fprintf p "Tuple@[%a@]"
      (print_list print_pat) pl


let print_parser_exp p (e: Trns.t) = 
  match e with 
  | Trns.Direct s -> fprintf p "PGoto (%a)" print_parser_state_label s
  | Trns.Select (e, st, fs) -> 
    fprintf p "PSelect (discriminate := %a, default := %a, cases = %a) "
    print_exp e
    print_parser_state_label st
    (print_fields print_pat print_parser_state_label) fs

let rec print_stm p =
  function
  | Stm.Trans t ->
    fprintf p "Transition %a" print_parser_exp t
  | Stm.Skip -> fprintf p "SSkip"
  | Stm.LetIn (x, sum, s) -> 
    fprintf p "SVardecl @[Name: %a@] @[Init: %a@]) %a@"
    print_string x
    (print_sum print_type print_exp) sum
    print_stm s
  | Stm.Asgn (e1, e2) ->
    fprintf p "SAssign @[%a := %a@]"
    print_exp e1
    print_exp e2
  | Stm.Cond (e,s1,s2) ->
    fprintf p "SConditional @[if (%a) then (%a) else (%a)@]" 
    print_exp e
    print_stm s1
    print_stm s2
  | Stm.Seq (s1,s2) ->
    fprintf p "SSeq @[%a \n %a@]"
    print_stm s1 
    print_stm s2
  | Stm.App (Call.Method (name, meth, tl, e), args) ->
    fprintf p "SExternMethodCall %s.%s <%a>(%a) %a"
    name
    meth
    ((print_list ~sep:"," print_type)) tl
    print_args args
    (print_option print_exp) e
  
  | Stm.App (Call.Funct (s, tl, e), args) ->
    fprintf p "SFunCall %s<%a>(%a) %a"
    s
    ((print_list ~sep:"," print_type)) tl
    print_args args
    (print_option print_exp) e
  
  | Stm.App (Call.Action (s, ctrl_args), data_args) ->
    fprintf p "SActCall %s(%a)(%a)"
    s
    (print_list ~sep:"," print_exp) ctrl_args
    print_args data_args

  | Stm.Ret eo ->
    fprintf p "SReturn %a"
    (print_option print_exp) eo

  | Stm.Exit ->
    fprintf p "SExit"

  | Stm.Invoke (eo, s) ->
    fprintf p "SInvoke %a %s" (print_option print_exp) eo s

  | Stm.App (Call.Inst (s, fs), arg) ->
    fprintf p "SApply @[%s, Ext_args = %a, args = %a@]"
    s
    (print_list ~sep:"," print_string) fs
    print_args arg

let print_control_d p (d : Ctrl.t) =
  match d with
  | Ctrl.Var (x,te) ->
    fprintf p "CDVardecl @[Name: %a@] @[Init: %a@])"
    print_string x
    (print_sum print_type print_exp) te
  | Ctrl.Action (s, ctrl_params, data_params, st) ->
    fprintf p "CDAction %s(%a)(%a){%a}"
    s
    (print_fields print_string print_type) ctrl_params
    print_params data_params
    print_stm st
  | Ctrl.Table (s, key, ss, def) ->
    fprintf p "CDTable %s (%a) %a %a"
    s
    (print_fields print_exp print_string) key
    (print_fields print_string print_args) ss
    (print_option (fun p (a, es) -> fprintf p "(%s , %a)" a (print_list print_exp) es)) def

let print_tp_decl p (d: Top.t) =
  match d with 
  | Top.Instantiate (constructor_name, instance_name, type_args, cargs, es) ->
    fprintf p "@[Instantiate \n (constructor_name = %a) \n (instance_name = %a)
    \n (type_args = %a) \n (cargs = %a) (%a) @]"
    print_string constructor_name
    print_string instance_name
    (print_list print_type) type_args
    print_constructor_args cargs
    (print_list ~sep:"," print_exp) es
  | Top.Extern (extern_name, type_params, cparams, eparams, methods) ->
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

  | Top.Control (control_name, cparams, ts, eparams, params, body, apply_blk) ->
    fprintf p "@[Control \n (control_name = %a) \n (cparams = %a)
              \n (%a) \n (eparams = %a)
              \n (params = %a) \n (body = %a) \n (apply_blk = %a)@] "
    print_string control_name
    print_constructor_params cparams
    (print_list ~sep:"," print_type) ts
    print_string_string_fields eparams
    print_params params
    (print_list ~sep:";" print_control_d) body 
    print_stm apply_blk

  | Top.Parser (name, constructors, ts, fields, params, state, states) ->
    fprintf p "@[Parser \n (name = %a) \n (cparams = %a)
              \n (%a) \n (eparams = %a)
              \n (params = %a) \n (start = %a) \n (states = %a)@] "
    print_string name
    print_constructor_params constructors
    (print_list ~sep:"," print_type) ts
    print_string_string_fields fields
    print_params params
    print_stm state
    (print_list ~sep:";" print_stm) states
  
  | Top.Funct (function_name, type_params, signature, body) ->
    fprintf p "@[Function \n (function_name = %a) \n (type_params = %a) \n
      (signature = %a) \n (body = %a) @]"
    print_string function_name
    my_print_int type_params
    print_arrowT signature
    print_stm body

let print_prog p = fprintf p "%a" (print_list ~sep:"," print_tp_decl)
