open Poulet4.Syntax
open Poulet4.Typed
open P4light
open Format

(****************************************************
  Pruning the AST with the guarantee that 
  the same P4 program will printed by printp4.ml.
 ****************************************************)

(***********************************************
              P4light.ml -> Type.ml
 ***********************************************)

let print_bool p b =
  let s =
    match b with
    | true -> "true"
    | false -> "false"
  in fprintf p "%s" s

let print_string p s =
  fprintf p "%s" s

let print_pair f1 f2 p (a, b) =
  fprintf p "( @[<hov 0>%a,@ %a )@]" f1 a f2 b

let print_triplet f1 f2 f3 p (a, b, c) =
  fprintf p "( @[<hov 0>%a,@ %a,@ %a )@]" f1 a f2 b f3 c

let print_option f p a =
  match a with
  | Some a -> fprintf p "(@[<hov 0>Some@ %a)@]" f a
  | None -> fprintf p "@[<hov 0>None@]"

let rec print_list_aux f p l =
  match l with
  | [] -> ()
  | hd :: tl ->
      fprintf p ";@ %a%a" f hd (print_list_aux f) tl

let print_list f p l =
  match l with
  | [] -> fprintf p "[]"
  | hd :: tl ->
      fprintf p "[@[<hov 0>%a%a]@]" f hd (print_list_aux f) tl

(* print_info prints a unit now, because we do not have info in Coq in this version. *)
let print_info p info =
  fprintf p "noinfo"

let print_coq_string p s =
  fprintf p "\"%s\"" s

let print_coq_strings =
  print_list print_coq_string

let p4string p (s : P4string.t) =
  fprintf p "(to_p4str %a)@]" 
      print_coq_string s.str

let p4strings =
  print_list p4string

let print_int p n =
  fprintf p "%s" (Bignum.to_string_accurate (Bignum.of_bigint n))

let print_bigint p n =
  fprintf p "(Bigint.of_int %s)" (Bignum.to_string_accurate (Bignum.of_bigint n))

let print_bignat = print_bigint

let p4int p (n : P4int.t) =
  fprintf p "{ @[<hov 0> tags = %a;@ value = %a;@ width_signed = %a }@]"
      print_info n.tags
      print_bigint n.value
      (print_option (print_pair print_bignat print_bool)) n.width_signed

let print_direction p (dir: direction) =
  let s =
    match dir with
    | In -> "In"
    | Out -> "Out"
    | InOut -> "InOut"
    | Directionless -> "Directionless"
  in fprintf p "%s" s

let print_name p (name : P4name.t) =
  match name with
  | BareName s ->
      fprintf p "(@[<hov 0>gen_p4name@ %a)@]"
          print_coq_string s.str
  | QualifiedName (namespaces, s) ->
      fprintf p "(@[<hov 4>QualifiedName@ (%a,@ %a))@]"
          p4strings namespaces
          p4string s

let print_function_kind p (func_kind: coq_FunctionKind) =
  let s =
    match func_kind with
    | FunParser -> "FunParser"
    | FunControl -> "FunControl"
    | FunExtern -> "FunExtern"
    | FunTable -> "FunTable"
    | FunAction -> "FunAction"
    | FunFunction -> "FunFunction"
    | FunBuiltin -> "FunBuiltin"
  in fprintf p "%s" s

let rec printable_type (typ : coq_P4Type) : bool =
  match typ with 
  | TypBool
  | TypString
  | TypInteger
  | TypInt _
  | TypBit _
  | TypVarBit _
  | TypArray _
  | TypTuple _ 
  | TypError
  | TypMatchKind
  | TypVoid
  | TypTypeName _ -> true
  | TypSpecializedType (base, args) ->
      List.for_all printable_type args
  | _ -> false

let print_no_type p _ = fprintf p "notype"

let rec print_type p (typ : coq_P4Type) =
  match typ with
  | TypBool ->
      fprintf p "@[<hov 0>TypBool@]"
  | TypString ->
      fprintf p "@[<hov 0>TypString@]"
  | TypInteger ->
      fprintf p "@[<hov 0>TypInteger@]"
  | TypInt width ->
      fprintf p "(@[<hov 0>TypInt@ %a)@]"
          print_bignat width
  | TypBit width ->
      fprintf p "(@[<hov 0>TypBit@ %a)@]"
          print_bignat width
  | TypVarBit width ->
      fprintf p "(@[<hov 0>TypVarBit@ %a)@]"
          print_bignat width
  | TypArray (typ, size) ->
      fprintf p "(@[<hov 4>TypArray@ (%a,@ %a))@]"
          print_type typ
          print_bignat size
  | TypTuple typs ->
      fprintf p "(@[<hov 0>TypTuple@ %a)@]"
          (print_list print_type) typs
  | TypList typs ->
      print_no_type p ()
  | TypRecord fields ->
      print_no_type p ()
  | TypSet elem_typ ->
      print_no_type p ()
  | TypError ->
      fprintf p "@[<hov 0>TypError@]"
  | TypMatchKind ->
      fprintf p "@[<hov 0>TypMatchKind@]"
  | TypVoid ->
      fprintf p "@[<hov 0>TypVoid@]"
  | TypHeader fields ->
      print_no_type p ()
  | TypHeaderUnion fields ->
      print_no_type p ()
  | TypStruct fields ->
      print_no_type p ()
  | TypEnum (s, typ, members) ->
      print_no_type p ()
  | TypTypeName name ->
      fprintf p "(@[<hov 0>TypTypeName@ %a)@]"
          p4string name
  | TypNewType (s, typ) ->
      print_no_type p ()
  | TypControl ctrl ->
      print_no_type p ()
  | TypParser ctrl ->
      print_no_type p ()
  | TypExtern s ->
      print_no_type p ()
  | TypFunction func ->
      print_no_type p ()
  | TypAction (data_params, ctrl_params) ->
      print_no_type p ()
  | TypTable s ->
      print_no_type p ()
  | TypPackage (typ_params, wildcard_params, params) ->
      print_no_type p ()
  | TypSpecializedType (base, args) ->
      if List.for_all printable_type args
      then fprintf p "(@[<hov 4>TypSpecializedType@ (%a,@ %a))@]"
              print_type base
              (print_list print_type) args
      else fprintf p "(@[<hov 4>TypSpecializedType@ (%a,@ []))@]"
              print_type base
  | TypConstructor (typ_params, wildcard_params, params, ret_type) ->
      print_no_type p ()
and print_param p (param: coq_P4Parameter) =
  match param with
  | MkParameter (false, direction, typ, _, variable) ->
      fprintf p "(@[<hov 4>gen_p4param@ %a@ %a@ %a)@]"
          print_direction direction
          print_type typ
          print_coq_string variable.str
  | MkParameter (opt, direction, typ, default_arg_id, variable) ->
      fprintf p "(@[<hov 4>MkParameter@ (%a,@ %a,@ %a,@ %a,@ %a))@]"
          print_bool opt
          print_direction direction
          print_type typ
          (print_option print_bigint) default_arg_id
          p4string variable

let rec extract_params (params: coq_P4Parameter list) =
  match params with 
  | MkParameter (false, direction, typ, _, variable) :: tl ->
      (direction, typ, variable.str) :: extract_params tl
  | _ -> []

let print_types =
  print_list print_type

let print_params =
  print_list print_param

let print_stmt_type p (typ : coq_StmType) =
  let s =
    match typ with
    | StmUnit ->  "StmUnit"
    | StmVoid -> "StmVoid"
  in fprintf p "%s" s

(* **********************************************
              Syntax.ml -> Syntax.ml
 ********************************************** *)

let print_method_prototype p (proto: coq_MethodPrototype) =
  match proto with
  | ProtoConstructor (info, s, params) ->
      fprintf p "(@[<hov 4>ProtoConstructor@ (%a,@ %a,@ %a))@]"
          print_info info
          p4string s
          print_params params
  | ProtoAbstractMethod (info, ret_typ, s, typ_params, params)->
      fprintf p "(@[<hov 4>ProtoAbstractMethod@ (%a,@ %a,@ %a,@ %a,@ %a))@]"
          print_info info
          print_type ret_typ
          p4string s
          p4strings typ_params
          print_params params
  | ProtoMethod (info, ret_typ, s, typ_params, params) ->
      fprintf p "(@[<hov 4>ProtoMethod@ (%a,@ %a,@ %a,@ %a,@ %a))@]"
          print_info info
          print_type ret_typ
          p4string s
          p4strings typ_params
          print_params params

let print_op_uni p (op: coq_OpUni) =
  let s =
    match op with
    | Not -> "Not"
    | BitNot -> "BitNot"
    | UMinus -> "UMinus"
  in fprintf p "%s" s

let print_op_bin p (op: coq_OpBin) =
  let s =
    match op with
    | Plus -> "Plus"
    | PlusSat -> "PlusSat"
    | Minus -> "Minus"
    | MinusSat -> "MinusSat"
    | Mul -> "Mul"
    | Div -> "Div"
    | Mod -> "Mod"
    | Shl -> "Shl"
    | Shr -> "Shr"
    | Le -> "Le"
    | Ge -> "Ge"
    | Lt -> "Lt"
    | Gt -> "Gt"
    | Eq -> "Eq"
    | NotEq -> "NotEq"
    | BitAnd -> "BitAnd"
    | BitXor -> "BitXor"
    | BitOr -> "BitOr"
    | PlusPlus -> "PlusPlus"
    | And -> "And"
    | Or -> "Or"
  in fprintf p "%s" s

let print_no_locator p () =
  fprintf p "noloc"

let print_locator p (loc: coq_Locator) =
  match loc with
  | LGlobal [] ->
      fprintf p "noloc"
  | LGlobal path ->
      fprintf p "(@[<hov 4>LGlobal@ %a)@]" (* TODO formatting *)
          print_coq_strings path
  | LInstance path ->
      fprintf p "(@[<hov 4>LInstance@ %a)@]" (* TODO formatting *)
          print_coq_strings path

let extract_names (e: coq_Expression) : string list = 
  let rec extract_names' e =
    match e with 
    | MkExpression (_, ExpExpressionMember(e', s),_,_) ->
        s.str :: (extract_names' e')
    | MkExpression (_, ExpName( BareName s, _),_,_) ->
        [s.str]
    | _ -> [] 
  in 
  List.rev (extract_names' e)

let rec print_expr p (expr : coq_Expression) =
  match expr with
  | MkExpression (info, pre_expr, typ, dir) ->
    (match pre_expr with
    | ExpInt { value = v; width_signed = Some (w, false); _ } ->
        fprintf p "(@[<hov 4>gen_p4expint@ %a@ %a)@]"
          print_int v
          print_int w
    | ExpCast (TypBit w, MkExpression (_, ExpInt { value = v; width_signed = None; _ }, _, _)) ->
        fprintf p "(@[<hov 4>gen_p4expint@ %a@ %a)@]"
          print_int v
          print_int w
    | ExpName _ | ExpExpressionMember _ ->
      let ss = extract_names expr in
      if ss = [] then
        fprintf p "(@[<hov 4>gen_p4expr@ %a)@]"
            print_pre_expr pre_expr
      else 
        if List.hd ss = "ig_md" then 
          fprintf p "(@[<hov 0>gen_p4meta@ %a)@]"
              print_coq_strings (List.tl ss)
        else if List.hd ss = "ig_intr_md" then 
          fprintf p "(@[<hov 0>gen_p4intr_meta@ %a)@]"
              print_coq_strings (List.tl ss)
        else
          fprintf p "(@[<hov 0>gen_p4expname@ %a)@]"
              print_coq_strings ss
    | _ ->
      fprintf p "(@[<hov 4>gen_p4expr@ %a)@]"
          print_pre_expr pre_expr)
and print_pre_expr p (pre_expr : coq_ExpressionPreT) =
  match pre_expr with
  | ExpBool b ->
      fprintf p "(@[<hov 0>ExpBool@ %a)@]"
          print_bool b
  | ExpInt n ->
      fprintf p "(@[<hov 0>ExpInt@ %a)@]"
          p4int n
  | ExpString s ->
      fprintf p "(@[<hov 0>ExpString@ %a)@]"
          p4string s
  | ExpName (name, loc) ->
      fprintf p "(@[<hov 0>ExpName@ (%a,@ %a))@]"
          print_name name
          print_no_locator ()
  | ExpArrayAccess (array, index) ->
      fprintf p "(@[<hov 4>ExpArrayAccess@ (%a,@ %a))@]"
          print_expr array
          print_expr index
  | ExpBitStringAccess (bits, lo, hi) ->
      fprintf p "(@[<hov 4>ExpBitStringAccess@ (%a,@ %a,@ %a))@]"
          print_expr bits
          print_bignat lo
          print_bignat hi
  | ExpList exprs ->
      fprintf p "(@[<hov 0>ExpList@ %a)@]"
          (print_list print_expr) exprs
  | ExpRecord kvs ->
      fprintf p "(@[<hov 0>ExpRecord@ %a)@]"
          (print_list print_keyvalue) kvs
  | ExpUnaryOp (op_uni, expr) ->
      fprintf p "(@[<hov 4>ExpUnaryOp@ (%a,@ %a))@]"
          print_op_uni op_uni
          print_expr expr
  | ExpBinaryOp (op_bin, e1, e2) ->
      fprintf p "(@[<hov 4>ExpBinaryOp@ (%a,@ %a,@ %a))@]"
          print_op_bin op_bin
          print_expr e1 
          print_expr e2
  | ExpCast (typ, expr) ->
      if printable_type typ
      then fprintf p "(@[<hov 4>ExpCast@ (%a,@ %a))@]"
              print_type typ
              print_expr expr
      else let MkExpression (info, pre_expr, typ, dir) = expr in 
              print_pre_expr p pre_expr
  | ExpTypeMember (name, s)->
      fprintf p "(@[<hov 4>ExpTypeMember@ (%a,@ %a))@]"
        p4string name
          p4string s
  | ExpErrorMember s ->
      fprintf p "(@[<hov 0>ExpErrorMember@ %a)@]"
          p4string s
  | ExpExpressionMember (expr, s) ->
      fprintf p "(@[<hov 4>ExpExpressionMember@ (%a,@ %a))@]"
          print_expr expr
          p4string s
  | ExpTernary (cond, tru, fls) ->
      fprintf p "(@[<hov 4>ExpTernary@ (%a,@ %a,@ %a))@]"
          print_expr cond
          print_expr tru
          print_expr fls
  | ExpFunctionCall (func, arg_types, args) ->
      if List.for_all printable_type arg_types
      then fprintf p "(@[<hov 4>ExpFunctionCall@ (%a,@ %a,@ %a))@]"
              print_expr func
              print_types arg_types
              (print_list (print_option print_expr)) args
      else fprintf p "(@[<hov 4>ExpFunctionCall@ (%a,@ [],@ %a))@]"
              print_expr func
              (print_list (print_option print_expr)) args
  | ExpNamelessInstantiation (typ, args) ->
      fprintf p "(@[<hov 4>ExpNamelessInstantiation@ (%a,@ %a))@]"
          print_type typ
          (print_list print_expr) args
  | ExpDontCare ->
    fprintf p "@[<hov 0>ExpDontCare@]"
and print_keyvalue p kv =
  match kv with
  | (key, value) ->
      fprintf p "(@[<hov 4>(%a@, %a)@]"
          p4string key
          print_expr value

let print_exprs =
  print_list print_expr

let print_pre_match p (m: coq_MatchPreT) =
  match m with
  | MatchDontCare ->
      fprintf p "@[<hov 0>MatchDontCare@]"
  | MatchMask (expr, mask) ->
     fprintf p "(@[<hov 0>MatchMask@ (%a,@ %a))@]"
       print_expr expr
       print_expr mask
  | MatchRange (lo, hi) ->
     fprintf p "(@[<hov 0>MatchRange@ (%a,@ %a))@]"
       print_expr lo
       print_expr hi
  | MatchCast (typ, expr) ->
     fprintf p "(@[<hov 0>MatchCast@ (%a,@ %a))@]"
        print_no_type ()
        print_expr expr

let print_match p (m: coq_Match) =
  match m with
  | MkMatch (info, expr, typ) ->
      fprintf p "(@[<hov 4>gen_p4match@ %a)@]"
          print_pre_match expr

let print_pre_matches =
  print_list print_pre_match

let print_matches =
  print_list print_match

let print_table_pre_action_ref p (action: coq_TablePreActionRef) =
  match action with
  | MkTablePreActionRef (name, args) ->
      fprintf p "(@[<hov 4>MkTablePreActionRef@ (%a,@ %a))@]"
          print_name name
          (print_list (print_option print_expr)) args

let print_table_action_ref p (action: coq_TableActionRef) =
  match action with
  | MkTableActionRef ( _
                      , MkTablePreActionRef (QualifiedName ([], { str="NoAction"; _ }), [])
                      , notype ) ->
      fprintf p "@[<hov 4>p4actref_noaction@]"
  | MkTableActionRef (info, MkTablePreActionRef (BareName s, []), typ) ->
      fprintf p "(@[<hov 4>gen_p4actref_na@ %a)@]"
          print_coq_string s.str
  | MkTableActionRef (info, action, typ) ->
      fprintf p "(@[<hov 4>MkTableActionRef@ (%a,@ %a,@ %a))@]"
          print_info info
          print_table_pre_action_ref action
          print_no_type ()

let print_table_actions =
  print_list print_table_action_ref

let print_table_key p (key: coq_TableKey) =
  match key with
  | MkTableKey (info, key, match_kind) ->
      fprintf p "(@[<hov 4>MkTableKey@ (%a,@ %a,@ %a))@]"
          print_info info
          print_expr key
          p4string match_kind

let print_table_keys =
  print_list print_table_key

let print_table_entry p (entry: coq_TableEntry) =
  match entry with
  | MkTableEntry (_, matches, 
      MkTableActionRef (_, MkTablePreActionRef (BareName s, []), typ)) ->
      let prems = List.map (fun m -> let MkMatch (_, prem, _) = m in prem) matches in 
        fprintf p "(@[<hov 4>gen_p4entry_na@ %a@ %a)@]"
            print_pre_matches prems
            print_coq_string s.str
  | MkTableEntry (info, matches, action) ->
      fprintf p "(@[<hov 4>MkTableEntry@ (%a,@ %a,@ %a))@]"
          print_info info
          print_matches matches
          print_table_action_ref action

let print_table_entries =
  print_list print_table_entry

let print_table_property p (property: coq_TableProperty) =
  match property with
  | MkTableProperty (info, const, s, expr) ->
      fprintf p "(@[<hov 4>MkTableProperty@ (%a,@ %a,@ %a,@ %a))@]"
          print_info info
          print_bool const
          p4string s
          print_expr expr

let print_stmt_switch_label p (label: coq_StatementSwitchLabel) =
  match label with
  | StatSwLabDefault info ->
      fprintf p "(@[<hov 0>StatSwLabDefault@ %a)@]"
          print_info info
  | StatSwLabName (info, s) ->
      fprintf p "(@[<hov 4>StatSwLabName@ (%a,@ %a))@]"
          print_info info
          p4string s

let block_to_pre_stmts (b: coq_Block) : coq_StatementPreT list =
  let rec block_to_pre_stmts' b agg =
    match b with
    | BlockEmpty info ->
        agg
    | BlockCons (MkStatement(_, pre_s, _), b') ->
          pre_s :: (block_to_pre_stmts' b' agg) 
  in 
  block_to_pre_stmts' b []
let rec print_stmt_switch_case p (case: coq_StatementSwitchCase) =
  match case with
  | StatSwCaseAction (info, label, code) ->
      fprintf p "(@[<hov 4>StatSwCaseAction@ (%a,@ %a,@ %a))@]"
          print_info info
          print_stmt_switch_label label
          print_block code
  | StatSwCaseFallThrough (info, label) ->
      fprintf p "(@[<hov 4>StatSwCaseFallThrough@ (%a,@ %a))@]"
          print_info info
          print_stmt_switch_label label
and print_pre_stmt p (pre_stmt: coq_StatementPreT) =
  match pre_stmt with
  | StatMethodCall (func, arg_types, args) ->
      let fun_str = extract_names func in
      let arg_str = List.map 
                      (fun arg ->
                        match arg with 
                        | None -> [] 
                        | Some arg' -> extract_names arg') args in
      ( match fun_str, (List.mem [] arg_str) with 
        | [fun_str' ; "apply"], false -> 
            if arg_str = [] then 
            fprintf p "(@[<hov 0>gen_p4tbl_call@ %a)@]"
              print_coq_string fun_str'
            else 
            fprintf p "(@[<hov 0>gen_p4tbl_call@ ~args:%a@ %a)@]"
              (print_list print_coq_strings) arg_str
              print_coq_string fun_str'
        | _, _ ->
          if List.for_all printable_type arg_types
          then fprintf p "(@[<hov 4>StatMethodCall@ (%a,@ %a,@ %a))@]"
                  print_expr func
                  print_types arg_types
                  (print_list (print_option print_expr)) args
          else fprintf p "(@[<hov 4>StatMethodCall@ (%a,@ [],@ %a))@]"
                  print_expr func
                  (print_list (print_option print_expr)) args )
  | StatAssignment (lhs, rhs) ->
      fprintf p "(@[<hov 4>StatAssignment@ (%a,@ %a))@]"
          print_expr lhs
          print_expr rhs
  | StatDirectApplication (typ, func_typ, args) ->
      fprintf p "(@[<hov 4>StatDirectApplication@ (%a,@ %a,@ %a))@]"
          print_type typ
          print_type func_typ
          (print_list (print_option print_expr)) args
  | StatConditional (cond, tru, fls) ->
      fprintf p "(@[<hov 4>StatConditional@ (%a,@ %a,@ %a))@]"
          print_expr cond
          print_stmt tru
          (print_option print_stmt) fls
  | StatBlock block ->
      fprintf p "(@[<hov 0>StatBlock@ %a)@]"
          print_block block
  | StatExit ->
      fprintf p "@[<hov 0>StatExit@]"
  | StatEmpty ->
      fprintf p "@[<hov 0>StatEmpty@]"
  | StatReturn expr ->
      fprintf p "(@[<hov 0>StatReturn@ %a)@]"
          (print_option print_expr) expr
  | StatSwitch (expr, cases) ->
      fprintf p "(@[<hov 4>StatSwitch@ (%a,@ %a))@]"
          print_expr expr
          (print_list print_stmt_switch_case) cases
  | StatConstant (typ, s, value, loc) ->
      fprintf p "(@[<hov 4>StatConstant@ (%a,@ %a,@ %a,@ %a))@]"
          print_type typ
          p4string s
          print_expr value
          print_no_locator ()
  | StatVariable (typ, s, init, loc) ->
      fprintf p "(@[<hov 4>StatVariable@ (%a,@ %a,@ %a,@ %a))@]"
          print_type typ
          p4string s
          (print_option print_expr) init
          print_no_locator ()
  | StatInstantiation (typ, args, s, init) ->
      fprintf p "(@[<hov 4>StatInstantiation@ (%a,@ %a,@ %a,@ %a))@]"
          print_type typ
          print_exprs args
          p4string s
          (print_list print_init) init
and print_stmt p (stmt : coq_Statement) =
  match stmt with
  | MkStatement (info, pre_stmt, typ) ->
      fprintf p "(@[<hov 4>gen_p4stmt@ %a)@]"
          print_pre_stmt pre_stmt
and print_block p (block : coq_Block) =
  let pre_stmts = block_to_pre_stmts block in 
  fprintf p "(@[<hov 0>prestmt_list_to_block@ %a)@]"
          (print_list print_pre_stmt) pre_stmts
and print_init p (init : coq_Initializer) =
    match init with
    | InitFunction (info, ret, name, t_params, params, body) ->
        fprintf p "(@[<hov 4>InitFunction@ (%a,@ %a,@ %a,@ %a,@ %a,@ %a))@]"
            print_info info
            print_type ret
            p4string name
            (print_list p4string) t_params
            print_params params
            print_block body
    | InitInstantiation (info, typ, args, name, init) ->
        fprintf p "(@[<hov 4>InitInstantiation@ (%a,@ %a,@ %a,@ %a,@ %a))@]"
            print_info info
            print_type typ
            print_exprs args
            p4string name
            (print_list print_init) init


let print_stmts =
  print_list print_stmt

let print_parser_case p (case: coq_ParserCase) =
  match case with
  | MkParserCase (info, matches, next) ->
      fprintf p "(@[<hov 4>MkParserCase@ (%a,@ %a,@ %a))@]"
          print_info info
          print_matches matches
          p4string next

let print_parser_transition p (transition: coq_ParserTransition) =
  match transition with
  | ParserDirect (info, next) ->
      fprintf p "(@[<hov 4>ParserDirect@ (%a,@ %a))@]"
          print_info info
          p4string next
  | ParserSelect (info, exprs, cases) ->
      fprintf p "(@[<hov 4>ParserSelect@ (%a,@ %a,@ %a))@]"
          print_info info
          print_exprs exprs
          (print_list print_parser_case) cases


let print_parser_state p (state: coq_ParserState) =
  match state with
  | MkParserState (info, s, stmts, transition) ->
      fprintf p "(@[<hov 4>MkParserState@ (%a,@ %a,@ %a,@ %a))@]"
          print_info info
          p4string s
          print_stmts stmts
          print_parser_transition transition

let print_parser_states =
  print_list print_parser_state

let print_sum_type_left f p l =
  fprintf p "(@[<hov 0>Coq_inl %a)@]" f l

let print_sum_type_right f p r =
  fprintf p "(@[<hov 0>Coq_inr %a)@]" f r

let print_decl_field p (decl_field : coq_DeclarationField) =
  match decl_field with
  | MkDeclarationField (info, typ, name) ->
      fprintf p "(@[<hov 4>MkDeclarationField@ (%a,@ %a,@ %a))@]"
          print_info info
          print_type typ
          p4string name

let gen_format_string decl_name content =
  match decl_name with
  | Some decl_name ->
      ("@[<hov 4>let %s = " ^^ content ^^ ";;@]@ @ ", decl_name)
  | None ->
      ("(@[<hov 4>%s" ^^ content ^^ ")@]", "")

let rec print_decl ?(pruned=false) (decl_name : string option) p (decl : coq_Declaration) =
  (* let print_dummy_decl decl_name p =
    fprintf p "Axiom %s : @Declaration unit.@ @ " decl_name
  in  *)
  match pruned, decl with
  | _, DeclConstant (info, typ, name, value) ->
      let (f_str, decl_name) =
        (gen_format_string decl_name "DeclConstant@ (%a,@ %a,@ %a,@ %a)")
      in
      fprintf p f_str
          decl_name
          print_info info
          print_type typ
          p4string name
          print_expr value
  | _, DeclInstantiation (info, typ, args, name, init) ->
      let (f_str, decl_name) =
        (gen_format_string decl_name "DeclInstantiation@ (%a,@ %a,@ %a,@ %a,@ %a)")
      in
      fprintf p f_str
          decl_name
          print_info info
          print_type typ
          print_exprs args
          p4string name
          (print_list (print_decl None)) init
  | _, DeclParser (info, name, type_params, params, constructor_params, locals, states) ->
      let (f_str, decl_name) =
        (gen_format_string decl_name "DeclParser@ (%a,@ %a,@ %a,@ %a,@ %a,@ %a,@ %a)")
      in
      fprintf p f_str
          decl_name
          print_info info
          p4string name
          p4strings type_params
          print_params params
          print_params constructor_params
          (print_list (print_decl None)) locals
          print_parser_states states
  | false, DeclControl (_, name, [], params, [], locals, apply) ->
      let params_triplets = extract_params params in
      if params_triplets = [] 
      then
        print_decl ~pruned:true decl_name p decl
      else 
        let (f_str, decl_name) =
          (gen_format_string decl_name "gen_p4ctrl@ %a@ %a@ %a@ %a")
        in
      let pre_stmts = block_to_pre_stmts apply in 
        fprintf p f_str
            decl_name
            print_coq_string name.str
            (print_list (print_triplet 
                print_direction print_type print_coq_string)) params_triplets
            (print_list (print_decl None)) locals
            (print_list print_pre_stmt) pre_stmts
  | _, DeclControl (info, name, type_params, params, constructor_params, locals, apply) ->
      let (f_str, decl_name) =
        (gen_format_string decl_name "DeclControl@ (%a,@ %a,@ %a,@ %a,@ %a,@ %a,@ %a)")
      in
      fprintf p f_str
          decl_name
          print_info info
          p4string name
          p4strings type_params
          print_params params
          print_params constructor_params
          (print_list (print_decl None)) locals
          print_block apply
  | _, DeclFunction (info, ret_type, name, type_params, params, body) ->
      let (f_str, decl_name) =
        (gen_format_string decl_name "DeclFunction@ (%a,@ %a,@ %a,@ %a,@ %a,@ %a)")
      in
      fprintf p f_str
          decl_name
          print_info info
          print_type ret_type
          p4string name
          p4strings type_params
          print_params params
          print_block body
  | _, DeclExternFunction (info, ret_type, name, type_params, params) ->
      let (f_str, decl_name) =
        (gen_format_string decl_name "DeclExternFunction@ (%a,@ %a,@ %a,@ %a,@ %a)")
      in
      fprintf p f_str
          decl_name
          print_info info
          print_type ret_type
          p4string name
          p4strings type_params
          print_params params
  | _, DeclVariable (info, typ, name, init) ->
      let (f_str, decl_name) =
        (gen_format_string decl_name "DeclVariable@ (%a,@ %a,@ %a,@ %a)")
      in fprintf p f_str
          decl_name
          print_info info
          print_type typ
          p4string name
          (print_option print_expr) init
  | _, DeclValueSet (info, typ, size, name) ->
      let (f_str, decl_name) =
        (gen_format_string decl_name "DeclValueSet@ (%a,@ %a,@ %a,@ %a)")
      in fprintf p f_str
          decl_name
          print_info info
          print_type typ
          print_bignat size
          p4string name
  | _, DeclAction (_, name, [], [], body) -> 
    let (f_str, decl_name) =
        (gen_format_string decl_name "gen_p4act@ %a@ %a")
      in
      let pre_stmts = block_to_pre_stmts body in 
      fprintf p f_str
          decl_name
          print_coq_string name.str
          (print_list print_pre_stmt) pre_stmts
  | _, DeclAction (info, name, data_params, ctrl_params, body) ->
      let (f_str, decl_name) =
        (gen_format_string decl_name "DeclAction@ (%a,@ %a,@ %a,@ %a,@ %a)")
      in
      fprintf p f_str
          decl_name
          print_info info
          p4string name
          print_params data_params
          print_params ctrl_params
          print_block body
  | false, DeclTable ( _, name, [], 
      [ MkTableActionRef (_, MkTablePreActionRef (BareName aname, []), _) ]
      , _
      , Some (MkTableActionRef (_, MkTablePreActionRef (BareName aname', []), _))
      , _
      , [] ) ->
      if aname.str = aname'.str
      then
        let (f_str, decl_name) =
        (gen_format_string decl_name "gen_p4tbl@ %a@ %a")
        in
        fprintf p f_str
            decl_name
            print_coq_string name.str
            print_coq_string aname.str
      else 
        print_decl ~pruned:true decl_name p decl
  | _, DeclTable (info, name, keys, actions, entries,
              default_action, size, custom_properties) ->
      let (f_str, decl_name) =
        (gen_format_string decl_name "DeclTable@ (%a,@ %a,@ %a,@ %a,@ %a,@ %a,@ %a,@ %a)")
      in
      fprintf p f_str
          decl_name
          print_info info
          p4string name
          print_table_keys keys
          print_table_actions actions
          (print_option print_table_entries) entries
          (print_option print_table_action_ref) default_action
          (print_option print_bignat) size
          (print_list print_table_property) custom_properties
  | _, DeclHeader (info, name, fields) ->
      let (f_str, decl_name) =
        (gen_format_string decl_name "DeclHeader@ (%a,@ %a,@ %a)")
      in
      fprintf p f_str
          decl_name
          print_info info
          p4string name
          (print_list print_decl_field) fields
  | _, DeclHeaderUnion (info, name, fields) ->
      let (f_str, decl_name) =
        (gen_format_string decl_name "DeclHeaderUnion@ (%a,@ %a,@ %a)")
      in
      fprintf p f_str
          decl_name
          print_info info
          p4string name
          (print_list print_decl_field) fields
  | _, DeclStruct (info, name, fields) ->
      let (f_str, decl_name) =
        (gen_format_string decl_name "DeclStruct@ (%a,@ %a,@ %a)")
      in
      fprintf p f_str
          decl_name
          print_info info
          p4string name
          (print_list print_decl_field) fields
  | _, DeclError (info, members) ->
      let (f_str, decl_name) =
        (gen_format_string decl_name "DeclError@ (%a,@ %a)")
      in
      fprintf p f_str
          decl_name
          print_info info
          p4strings members
  | _, DeclMatchKind (info, members) ->
      let (f_str, decl_name) =
        (gen_format_string decl_name "DeclMatchKind@ (%a,@ %a)")
      in
      fprintf p f_str
          decl_name
          print_info info
          p4strings members
  | _, DeclEnum (info, name, members) ->
      let (f_str, decl_name) =
        (gen_format_string decl_name "DeclEnum@ (%a,@ %a,@ %a)")
      in
      fprintf p f_str
          decl_name
          print_info info
          p4string name
          p4strings members
  | _, DeclSerializableEnum (info, typ, name, members) ->
      let (f_str, decl_name) =
        (gen_format_string decl_name "DeclSerializableEnum@ (%a,@ %a,@ %a,@ %a)")
      in
      fprintf p f_str
          decl_name
          print_info info
          print_type typ
          p4string name
          (print_list (print_pair p4string print_expr)) members
  | _, DeclExternObject (info, name, type_params, methods) ->
      let (f_str, decl_name) =
        (gen_format_string decl_name "DeclExternObject@ (%a,@ %a,@ %a,@ %a)")
      in
      fprintf p f_str
          decl_name
          print_info info
          p4string name
          p4strings type_params
          (print_list print_method_prototype) methods
  | _, DeclTypeDef (info, name, typ_or_decl) ->
    begin
      match typ_or_decl with
      | Coq_inl typ ->
        ( match typ with 
          | TypBit n -> 
              let (f_str, decl_name) =
                (gen_format_string decl_name "gen_p4decltypedef@ %a@ %a")
              in
              fprintf p f_str
                  decl_name
                  print_coq_string name.str
                  (print_int) n
           | _ -> 
              let (f_str, decl_name) =
                (gen_format_string decl_name "DeclTypeDef@ (%a,@ %a,@ %a)")
              in
              fprintf p f_str
                  decl_name
                  print_info info
                  p4string name
                  (print_sum_type_left print_type) typ)
      | Coq_inr decl ->
        let (f_str, decl_name) =
          (gen_format_string decl_name "DeclTypeDef@ (%a,@ %a,@ %a)")
        in
        fprintf p f_str
            decl_name
            print_info info
            p4string name
            (print_sum_type_right (print_decl None)) decl
    end
  | _, DeclNewType (info, name, typ_or_decl) ->
    begin
      match typ_or_decl with
      | Coq_inl typ ->
        let (f_str, decl_name) =
          (gen_format_string decl_name "DeclNewType@ (%a,@ %a,@ %a)")
        in
        fprintf p f_str
            decl_name
            print_info info
            p4string name
            (print_sum_type_left print_type) typ
      | Coq_inr decl ->
        let (f_str, decl_name) =
          (gen_format_string decl_name "DeclNewType@ (%a,@ %a,@ %a)")
        in
        fprintf p f_str
            decl_name
            print_info info
            p4string name
            (print_sum_type_right (print_decl None)) decl
    end
  | _, DeclControlType (info, name, type_params, params) ->
      let (f_str, decl_name) =
        (gen_format_string decl_name "DeclControlType@ (%a,@ %a,@ %a,@ %a)")
      in
      fprintf p f_str
          decl_name
          print_info info
            p4string name
            p4strings type_params
            print_params params
  | _, DeclParserType (info, name, type_params, params) ->
      let (f_str, decl_name) =
        (gen_format_string decl_name "DeclParserType@ (%a,@ %a,@ %a,@ %a)")
      in
      fprintf p f_str
          decl_name
          print_info info
            p4string name
            p4strings type_params
            print_params params
  | _, DeclPackageType (info, name, type_params, params) ->
      let (f_str, decl_name) =
        (gen_format_string decl_name "DeclPackageType@ (%a,@ %a,@ %a,@ %a)")
      in
      fprintf p f_str
          decl_name
          print_info info
            p4string name
            p4strings type_params
            print_params params

let print_decls =
  print_list (print_decl None)

let gen_decl_name =
  let cnt = ref 0 in
  fun (existing: string list) ->
    cnt := !cnt + 1;
    while List.mem ("decl" ^ string_of_int !cnt) existing do
      cnt := !cnt + 1;
    done;
    "decl'" ^ string_of_int !cnt

let get_decl_name (decl: coq_Declaration): string option =
  match decl with
    | DeclFunction (_, _, name, _, params, _)
    | DeclExternFunction (_, _, name, _, params) ->
      let param_names =
        List.fold_left
          (fun accum p -> let MkParameter (_,_,_,_,name) = p
                          in accum ^ "'" ^ name.str) "" params
      in Some (name.str ^ param_names)
    | DeclConstant (_, _, name, _)
    | DeclInstantiation (_, _, _, name, _)
    | DeclParser (_, name, _, _, _, _, _)
    | DeclControl (_, name, _, _, _, _, _)
    | DeclVariable (_, _, name, _)
    | DeclValueSet (_, _, _, name)
    | DeclAction (_, name, _, _, _)
    | DeclTable (_, name, _, _, _, _, _, _)
    | DeclHeader (_, name, _)
    | DeclHeaderUnion (_, name, _)
    | DeclStruct (_, name, _)
    | DeclEnum (_, name, _)
    | DeclSerializableEnum (_, _, name, _)
    | DeclExternObject (_, name, _, _)
    | DeclTypeDef (_, name, _)
    | DeclNewType (_, name, _)
    | DeclControlType (_, name, _, _)
    | DeclParserType (_, name, _, _)
    | DeclPackageType (_, name, _, _) -> Some ("decl'" ^ name.str)
    | DeclError (_, _)
    | DeclMatchKind (_, _) -> None

let collect_decl_names (program : P4light.program): string list =
  List.filter_map Fun.id (List.map get_decl_name program)

let print_top_decl p (existing: string list) (decl : coq_Declaration): string =
  let decl_name =
    match get_decl_name decl with
    | Some name -> name
    | None -> gen_decl_name existing
  in
    print_decl (Some decl_name) p decl;
    decl_name

let print_value_loc =
  p4string

let print_env_env print_binding =
  print_list (print_list (print_pair p4string print_binding))

let print_header p =
  fprintf p "open Petr4@ ";
  fprintf p "open P4light@ ";
  fprintf p "open Prunefunc@ "

let print_program p (program : P4light.program) =
  fprintf p "@[<v 0>";
  print_header p;
  let existing = collect_decl_names program in
  let decl_names = List.map (print_top_decl p existing) program in
  let prog_name = Some "prog : program" in
  let (f_str, prog_name) = (gen_format_string prog_name "@ %a")
  in fprintf p f_str
        prog_name
        (print_list print_string) decl_names;
  fprintf p "@]@."
