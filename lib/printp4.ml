open Typed
open Prog
open Format

(***********************************************
              Typed.ml -> Type.v
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

let print_option f p a =
  match a with
  | Some a -> f p a
  | None -> ()

let print_list ?(sep="") f p l =
  let print_item b x =
    if b then fprintf p "%s@ " sep;
    f p x ;
    true in
  ignore (List.fold_left print_item false l)

(* print_info prints a unit now, because we do not have info in Coq in this version. *)
let print_info p info =
  fprintf p "NoInfo"

let p4string p (s : P4string.t) =
  fprintf p "{| @[<hov 0>stags := %a;@ str := \"%s\" |}@]" print_info s.tags s.str

let p4strings =
  print_list p4string

let print_type_params p (type_params: P4string.t list) =
  if (List.length type_params <> 0) then
    fprintf p "<%a>" (print_list ~sep:"," p4string) type_params
  else ()
let print_nat p n =
  fprintf p "%d" n

let print_bigint p n =
  fprintf p "%s" (Bignum.to_string_accurate (Bignum.of_bigint n))

let print_bignat p n =
  fprintf p "%s%%N" (Bignum.to_string_accurate (Bignum.of_bigint n))

let p4int p (n : P4int.t) =
  fprintf p "{| @[<hov 0>itags := %a;@ value := %a;@ width_signed := %a |}@]" 
      print_info n.tags 
      print_bigint n.value
      (print_option (print_pair print_bignat print_bool)) n.width_signed

let print_direction p (dir: direction) =
  let s = 
    match dir with
    | In -> "in " 
    | Out -> "out "
    | InOut -> "inout "
    | Directionless -> ""
  in fprintf p "%s" s

let print_name p (name : Info.t Poulet4.Typed.name) =
  match name with
  | BareName s ->
      fprintf p "(@[<hov 0>BareName@ %a)@]" p4string s
  | QualifiedName (namespaces, s) -> 
      fprintf p "(@[<hov 4>QualifiedName@ %a@ %a)@]" 
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
          print_bigint width
  | TypBit width ->
      fprintf p "(@[<hov 0>TypBit@ %a)@]"
          print_bigint width
  | TypVarBit width ->
      fprintf p "(@[<hov 0>TypVarBit@ %a)@]"
          print_bigint width
  | TypArray (typ, size) ->
      fprintf p "(@[<hov 4>TypArray@ %a@ %a)@]"
          print_type typ
          print_bigint size
  | TypTuple typs ->
      fprintf p "(@[<hov 0>TypTuple@ %a)@]"
          (print_list print_type) typs
  | TypList typs ->
      fprintf p "(@[<hov 0>TypList@ %a)@]"
          (print_list print_type) typs
  | TypRecord fields ->
      fprintf p "(@[<hov 0>TypRecord@ %a)@]"
          (print_list print_field_type) fields
  | TypSet elem_typ ->
      fprintf p "(@[<hov 0>TypSet@ %a)@]"
          print_type elem_typ
  | TypError ->
      fprintf p "@[<hov 0>TypError@]"
  | TypMatchKind ->
      fprintf p "@[<hov 0>TypMatchKind@]"
  | TypVoid ->
      fprintf p "@[<hov 0>TypVoid@]"
  | TypHeader fields ->
      fprintf p "(@[<hov 0>TypHeader@ %a)@]"
          (print_list print_field_type) fields
  | TypHeaderUnion fields ->
      fprintf p "(@[<hov 0>TypHeaderUnion@ %a)@]"
          (print_list print_field_type) fields
  | TypStruct fields ->
      fprintf p "(@[<hov 0>TypStruct@ %a)@]"
          (print_list print_field_type) fields
  | TypEnum (s, typ, members) ->
      fprintf p "(@[<hov 4>TypEnum@ %a@ %a@ %a)@]"
          p4string s
          (print_option print_type) typ
          p4strings members
  | TypTypeName name ->
      fprintf p "(@[<hov 0>TypTypeName@ %a)@]"
          print_name name
  | TypNewType (s, typ) ->
      fprintf p "(@[<hov 4>TypNewType@ %a@ %a)@]"
          p4string s
          print_type typ
  | TypControl ctrl ->
      fprintf p "(@[<hov 0>TypControl@ %a)@]"
          print_control_type ctrl
  | TypParser ctrl ->
      fprintf p "(@[<hov 0>TypParser@ %a)@]"
          print_control_type ctrl
  | TypExtern s ->
      fprintf p "(@[<hov 0>TypExtern@ %a)@]"
          p4string s
  | TypFunction func ->
      fprintf p "(@[<hov 0>TypFunction@ %a)@]"
          print_function_type func
  | TypAction (data_params, ctrl_params) ->
      fprintf p "(@[<hov 4>TypAction@ %a@ %a)@]"
          (print_list print_param) data_params
          (print_list print_param) ctrl_params
  | TypTable s ->
      fprintf p "(@[<hov 0>TypTable@ %a)@]"
          p4string s
  | TypPackage (type_params, wildcard_params, params) ->
      fprintf p "(@[<hov 4>TypPackage@ %a@ %a@ %a)@]"
          print_type_params type_params
          print_type_params wildcard_params
          (print_list print_param) params
  | TypSpecializedType (base, args) ->
      fprintf p "(@[<hov 4>TypSpecializedType@ %a@ %a)@]"
          print_type base
          (print_list print_type) args
  | TypConstructor (type_params, wildcard_params, params, ret_type) ->
      fprintf p "(@[<hov 4>TypConstructor@ %a@ %a@ %a@ %a)@]"
          print_type_params type_params
          print_type_params wildcard_params
          (print_list print_param) params
          print_type ret_type
and print_field_type p (field: coq_FieldType) =
  print_pair p4string print_type p field
and print_control_type p (ctrl: coq_ControlType) =
  match ctrl with
  | MkControlType (type_params, params) ->
      fprintf p "(@[<hov 4>MkControlType@ %a@ %a)@]"
          print_type_params type_params
          (print_list print_param) params
and print_function_type p (func: coq_FunctionType) =
  match func with 
  | MkFunctionType (type_params, params, func_kind, ret_typ) ->
      fprintf p "(@[<hov 4>MkFunctionType@ %a@ %a@ %a@ %a)@]"
          print_type_params type_params
          (print_list print_param) params
          print_function_kind func_kind
          print_type ret_typ
and print_param p (param: coq_P4Parameter) =
  match param with
  | MkParameter (opt, direction, typ, default_arg_id, variable) ->
      fprintf p "[<h>";
      if opt
      then fprintf p "%@optional ";
      fprintf p "%a%a %a%a)@]"
          print_direction direction
          print_type typ
          p4string variable
          (print_option (fun p v -> fprintf p " = %a" print_bigint v)) default_arg_id

let print_types =
  print_list print_type

let print_params p (params: coq_P4Parameter list) =
  fprintf p "@[<hov 0>%a@]" (print_list ~sep:"," print_param) params

let print_cstr_params p (params: coq_P4Parameter list) =
  if (List.length params <> 0)
  then fprintf p "@,(@[<hov 0>%a@])" (print_list ~sep:"," print_param) params
  else ()

let print_stmt_type p (typ : coq_StmType) =
  let s =
    match typ with
    | StmUnit ->  "StmUnit"
    | StmVoid -> "StmVoid"
  in fprintf p "%s" s

(* **********************************************
              Syntax.ml -> Syntax.v
 ********************************************** *)

let print_method_prototype p (proto: coq_MethodPrototype) =
  match proto with
  | ProtoConstructor (info, s, params) ->
      fprintf p "@[<h>%a(%a);@]"
          p4string s
          print_params params
  | ProtoAbstractMethod (info, ret_typ, s, type_params, params)-> 
      fprintf p "@[<h>abstract %a %a%a(%a);@]" 
          print_type ret_typ
          p4string s
          print_type_params type_params
          print_params params
  | ProtoMethod (info, ret_typ, s, type_params, params) -> 
      fprintf p "@[<h>%a %a%a(%a);@]"
          print_type ret_typ
          p4string s
          print_type_params type_params
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

let print_locator p (loc: coq_Locator) =
  match loc with
  | LGlobal [] ->
      fprintf p "NoLocator"
  | LGlobal path ->
      fprintf p "(@[<hov 4>LGlobal@ %a)@]" (* TODO formatting *)
          p4strings path
  | LInstance path ->
      fprintf p "(@[<hov 4>LInstance@ %a)@]" (* TODO formatting *)
          p4strings path

let rec print_expr p (expr : coq_Expression) =
  match expr with
  | MkExpression (info, pre_expr, typ, dir) ->
      fprintf p "(@[<hov 4>MkExpression@ %a@ %a@ %a@ %a)@]"
          print_info info
          print_pre_expr pre_expr
          print_type typ
          print_direction dir
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
      fprintf p "(@[<hov 0>ExpName@ %a@ %a)@]" 
          print_name name
          print_locator loc
  | ExpArrayAccess (array, index) ->
      fprintf p "(@[<hov 4>ExpArrayAccess@ %a@ %a)@]"
          print_expr array
          print_expr index
  | ExpBitStringAccess (bits, lo, hi) ->
      fprintf p "(@[<hov 4>ExpBitStringAccess@ %a@ %a@ %a)@]"
          print_expr bits
          print_bigint lo
          print_bigint hi
  | ExpList exprs ->
      fprintf p "(@[<hov 0>ExpList@ %a)@]"
          (print_list print_expr) exprs
  | ExpRecord kvs ->
      fprintf p "(@[<hov 0>ExpRecord@ %a)@]"
          (print_list print_keyvalue) kvs
  | ExpUnaryOp (op_uni, expr) ->
      fprintf p "(@[<hov 4>ExpUnaryOp@ %a@ %a)@]"
          print_op_uni op_uni
          print_expr expr
  | ExpBinaryOp (op_bin, expr_pair) ->
      fprintf p "(@[<hov 4>ExpBinaryOp@ %a@ %a)@]"
          print_op_bin op_bin
          (print_pair print_expr print_expr) expr_pair
  | ExpCast (typ, expr) ->
      fprintf p "(@[<hov 4>ExpCast@ %a@ %a)@]"
          print_type typ
          print_expr expr
  | ExpTypeMember (name, s)->
      fprintf p "(@[<hov 4>ExpTypeMember@ %a@ %a)@]"
          print_name name
          p4string s
  | ExpErrorMember s ->
      fprintf p "(@[<hov 0>ExpErrorMember@ %a)@]" 
          p4string s
  | ExpExpressionMember (expr, s) ->
      fprintf p "(@[<hov 4>ExpExpressionMember@ %a@ %a)@]"
          print_expr expr
          p4string s
  | ExpTernary (cond, tru, fls) ->
      fprintf p "(@[<hov 4>ExpTernary@ %a@ %a@ %a)@]"
          print_expr cond
          print_expr tru
          print_expr fls
  | ExpFunctionCall (func, arg_types, args) ->
      fprintf p "(@[<hov 4>ExpFunctionCall@ %a@ %a@ %a)@]"
          print_expr func
          print_types arg_types
          print_args args
  | ExpNamelessInstantiation (typ, args) ->
      fprintf p "(@[<hov 4>ExpNamelessInstantiation@ %a@ %a)@]"
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
and print_args p (args: (coq_Expression option) list) = 
  let print_arg p arg = 
    match arg with
    | None -> print_pre_expr p ExpDontCare
    | Some expr -> print_expr p expr
  in fprintf p "@[<hov 0>%a@]" (print_list ~sep:"," print_arg) args

let print_exprs =
  print_list print_expr

let print_match p (m: coq_Match) =
  match m with
  | MkMatch (info, expr, typ) ->
      match expr with
      | MatchDontCare -> 
          fprintf p "@[<h>_@]"
      | MatchMask (expr, mask) ->
        fprintf p "@[<h>%a &&& %a@]"
          print_expr expr
          print_expr mask
      | MatchRange (lo, hi) ->
        fprintf p "@[<h>%a .. %a@]"
          print_expr lo
          print_expr hi
      | MatchCast (typ, expr) ->
          print_expr p expr

let print_matches p (matches: coq_Match list)=
  fprintf p "@[<hov 0>%a@]" (print_list ~sep:"," print_match) matches

let print_table_action_ref p (action: coq_TableActionRef) =
  match action with
  | MkTableActionRef (info, action, typ) ->
      match action with
      | MkTablePreActionRef (name, []) ->
          fprintf p "(@[<h>%a;@]"
              print_name name
      | MkTablePreActionRef (name, args) ->
          fprintf p "(@[<h>%a(%a);@]"
              print_name name
              print_args args

let print_table_actions p (actions: coq_TableActionRef list)=
  if (List.length actions <> 0)
  then fprintf p "@[<v 4>actions = {@,%a@]@,}@,"
          (print_list print_table_action_ref) actions
  else fprintf p "@[<h>actions = { }@]@,"

let print_table_default_action p (action: coq_TableActionRef)=
  fprintf p "@[<h>default_action = %a;@]@,"
      print_table_action_ref action

let print_table_key p (key: coq_TableKey) =
  match key with
  | MkTableKey (info, key, match_kind) ->
      fprintf p "@[<h>%a : %a;@]"
          print_expr key
          p4string match_kind

let print_table_keys p (keys: coq_TableKey list) =
  if (List.length keys <> 0) then
    fprintf p "@[<v 4>key = {@,%a@]@,}@,"
        (print_list print_table_key) keys

let print_table_entry p (entry: coq_TableEntry) =
  match entry with
  | MkTableEntry (info, matches, action) ->
      fprintf p "(@[<h>(%a) : %a;@]"
          print_matches matches
          print_table_action_ref action

let print_table_entries p (entries: coq_TableEntry list)= 
  if (List.length entries <> 0) then
    fprintf p "@[<v 4>const entries = {@,%a@]@,}@,"
        (print_list print_table_entry) entries

let print_table_size p size = 
  fprintf p "@[<h>size = %a;@]@,"
      print_bigint size

let print_table_property p (property: coq_TableProperty) =
  match property with
  | MkTableProperty (info, const, s, expr) ->
      fprintf p "@[<h>%s%a = %a;@]@,"
          (if const then "const " else "")
          p4string s
          print_expr expr

let print_stmt_switch_label p (label: coq_StatementSwitchLabel) =
  match label with
  | StatSwLabDefault info -> 
      fprintf p "(@[<hov 0>StatSwLabDefault@ %a)@]"
          print_info info
  | StatSwLabName (info, s) ->
      fprintf p "(@[<hov 4>StatSwLabName@ %a@ %a)@]"
          print_info info
          p4string s

let rec print_stmt_switch_case p (case: coq_StatementSwitchCase) =
  match case with
  | StatSwCaseAction (info, label, code) ->
      fprintf p "(@[<hov 4>StatSwCaseAction@ %a@ %a@ %a)@]" 
          print_info info
          print_stmt_switch_label label
          print_block code
  | StatSwCaseFallThrough (info, label) ->
      fprintf p "(@[<hov 4>StatSwCaseFallThrough@ %a@ %a)@]" 
          print_info info
          print_stmt_switch_label label
and print_pre_stmt p (pre_stmt: coq_StatementPreT) =
  match pre_stmt with
  | StatMethodCall (func, arg_types, args) ->
      fprintf p "(@[<hov 4>StatMethodCall@ %a@ %a@ %a)@]"
          print_expr func
          print_types arg_types
          print_args args
  | StatAssignment (lhs, rhs) ->
      fprintf p "(@[<hov 4>StatAssignment@ %a@ %a)@]"
          print_expr lhs
          print_expr rhs
  | StatDirectApplication (typ, args) ->
      fprintf p "(@[<hov 4>StatDirectApplication@ %a@ %a)@]"
          print_type typ
          print_exprs args
  | StatConditional (cond, tru, fls) ->
      fprintf p "(@[<hov 4>StatConditional@ %a@ %a@ %a)@]"
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
      fprintf p "(@[<hov 4>StatSwitch@ %a@ %a)@]"
          print_expr expr
          (print_list print_stmt_switch_case) cases
  | StatConstant (typ, s, value, loc) ->
      fprintf p "(@[<hov 4>StatConstant@ %a@ %a@ %a@ %a)@]"
          print_type typ
          p4string s
          print_expr value
          print_locator loc
  | StatVariable (typ, s, init, loc) ->
      fprintf p "(@[<hov 4>StatVariable@ %a@ %a@ %a@ %a)@]"
          print_type typ
          p4string s
          (print_option print_expr) init
          print_locator loc
  | StatInstantiation (typ, args, s, init) ->
      fprintf p "(@[<hov 4>StatInstantiation@ %a@ %a@ %a@ %a)@]"
          print_type typ
          print_exprs args
          p4string s
          (print_list print_init) init
and print_stmt p (stmt : coq_Statement) =
  match stmt with
  | MkStatement (info, pre_stmt, typ) ->
      fprintf p "(@[<hov 4>MkStatement@ %a@ %a@ %a)@]"
          print_info info
          print_pre_stmt pre_stmt
          print_stmt_type typ
and print_block p (block : coq_Block) =
  let print_block_aux p (block : coq_Block)=
    match block with 
    | BlockEmpty info -> 
        fprintf p ""
    | BlockCons (stmt, block) ->
       fprintf p "@,%a%a"
          print_stmt stmt
          print_block block in
  match block with
  | BlockEmpty _ -> fprintf p "{ }"
  | BlockCons _ -> fprintf p "{%a@]@,}" print_block_aux block

and print_init p (init : coq_Initializer) =
    match init with
    | InitFunction (info, ret, name, t_params, params, body) ->
        fprintf p "(@[<hov 4>InitFunction@ %a@ %a@ %a@ %a@ %a@ %a)@]"
            print_info info
            print_type ret
            p4string name
            (print_list p4string) t_params
            print_params params
            print_block body
    | InitInstantiation (info, typ, args, name, init) ->
        fprintf p "(@[<hov 4>InitInstantiation@ %a@ %a@ %a@ %a@ %a)@]"
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
      fprintf p "(@[<hov 4>MkParserCase@ %a@ %a@ %a)@]"
          print_info info
          print_matches matches
          p4string next
  
let print_parser_transition p (transition: coq_ParserTransition) =
  match transition with
  | ParserDirect (info, next) ->
      fprintf p "(@[<hov 4>ParserDirect@ %a@ %a)@]"
          print_info info
          p4string next
  | ParserSelect (info, exprs, cases) ->
      fprintf p "(@[<hov 4>ParserSelect@ %a@ %a@ %a)@]"
          print_info info
          print_exprs exprs
          (print_list print_parser_case) cases


let print_parser_state p (state: coq_ParserState) =
  match state with
  | MkParserState (info, s, stmts, transition) ->
      fprintf p "(@[<hov 4>MkParserState@ %a@ %a@ %a@ %a)@]"
          print_info info
          p4string s
          print_stmts stmts
          print_parser_transition transition

let print_parser_states =
  print_list print_parser_state

let print_sum_type_left f p l= 
  fprintf p "(@[<hov 0>inl %a)@]" f l

let print_sum_type_right f p r = 
  fprintf p "(@[<hov 0>inr %a)@]" f r

let print_decl_field p (decl_field : coq_DeclarationField) =
  match decl_field with
  | MkDeclarationField (info, typ, name) ->
      fprintf p "(@[<h>%a@ %a;@]"
          print_type typ
          p4string name

let print_decl_fields p (decl_fields : coq_DeclarationField list) =
  if (List.length decl_fields <> 0)
  then fprintf p "{@,%a@]@,}" (print_list print_decl_field) decl_fields
  else fprintf p "{ }"

let rec print_decl p (decl : coq_Declaration) =
  match decl with
  | DeclConstant (info, typ, name, value) ->
    fprintf p "@[<hov 4>const %a %a =@ %a;@]"
        print_type typ
        p4string name
        print_expr value
  | DeclInstantiation (info, typ, args, name, []) ->
      fprintf p "@[<h>%a(%a) %a;@]"
          print_type typ
          print_exprs args
          p4string name
  | DeclInstantiation (info, typ, args, name, init) ->
      fprintf p "@[<v 4>%a(%a) %a = {@,%a@]@,};"
          print_type typ
          print_exprs args
          p4string name
          (print_list print_decl) init
  | DeclParser (info, name, type_params, params, constructor_params, locals, states) ->
      fprintf p "@[<v 4>parser %a%a@[<v 0>(%a)%a@] {@,"
          p4string name
          print_type_params type_params
          print_params params
          print_cstr_params constructor_params;
      if (List.length locals <> 0) then
        fprintf p "%a@," (print_list print_decl) locals;
      fprintf p "%a@]@,}" print_parser_states states
  | DeclControl (info, name, type_params, params, constructor_params, locals, apply) ->
      fprintf p "@[<v 4>control %a%a@[<v 0>(%a)%a@] {@,"
          p4string name
          print_type_params type_params
          print_params params
          print_params constructor_params;
      if (List.length locals <> 0) then
        fprintf p "%a@," (print_list print_decl) locals;
      fprintf p "@[<v 4>apply %a@]@,}" print_block apply
  | DeclFunction (info, ret_type, name, type_params, params, body) ->
      fprintf p "@[<v 4>%a %a%a(%a) %a"
          print_type ret_type
          p4string name
          print_type_params type_params
          print_params params
          print_block body
  | DeclExternFunction (info, ret_type, name, type_params, params) ->
      fprintf p "@[<h>extern %a %a%a(%a);@]"
          print_type ret_type
          p4string name
          print_type_params type_params
          print_params params
  | DeclVariable (info, typ, name, init) ->
      fprintf p "@[<hov 4>%a %a%a;@]"
          print_type typ
          p4string name
          (print_option (fun p e -> fprintf p " = %a" print_expr e)) init
  | DeclValueSet (info, typ, size, name) ->
      fprintf p "@[<h>value_set<%a>(%a) %a;@]"
          print_type typ
          print_bigint size
          p4string name
  | DeclAction (info, name, data_params, ctrl_params, body) ->
      fprintf p "@[<4>action %a(%a) %a"
          p4string name
          print_params (data_params @ ctrl_params)
          print_block body
  | DeclTable (info, name, keys, actions, entries, 
              default_action, size, custom_properties) ->
      fprintf p "@[<v 4>table %a {@,%a%a%a%a%a%a@]@,}"
          p4string name
          print_table_keys keys
          print_table_actions actions
          (print_option print_table_entries) entries
          (print_option print_table_default_action) default_action
          (print_option print_table_size) size
          (print_list print_table_property) custom_properties
  | DeclHeader (info, name, fields) ->
      fprintf p "@[<v 4>header %a %a"
          p4string name
          print_decl_fields fields
  | DeclHeaderUnion (info, name, fields) ->
      fprintf p "@[<v 4>header_union %a %a"
          p4string name
          print_decl_fields fields
  | DeclStruct (info, name, fields) ->
      fprintf p "@[<v 4>struct %a %a"
          p4string name
          print_decl_fields fields
  | DeclError (info, []) ->
      fprintf p "@[<h>error { }@]"
  | DeclError (info, members) ->
      fprintf p "@[<v 4>error {@,%a@]@,}"
          (print_list ~sep:"," p4string) members
  | DeclMatchKind (info, []) ->
     fprintf p "@[<h>match_kind { }@]"
  | DeclMatchKind (info, members) ->
     fprintf p "@[<v 4>match_kind {@,%a@]@,}"
          (print_list ~sep:"," p4string) members
  | DeclEnum (info, name, []) ->
      fprintf p "@[<h>enum %a { }@]"
          p4string name
  | DeclEnum (info, name, members) ->
      fprintf p "@[<v 4>enum %a {@,%a@]@,}"
          p4string name
          (print_list ~sep:"," p4string) members
  | DeclSerializableEnum (info, typ, name, []) ->
      fprintf p "@[<h>enum %a %a { }@]"
          print_type typ
          p4string name
  | DeclSerializableEnum (info, typ, name, members) ->
      let print_member p (field, init) =
        Format.fprintf p "@[<h>%a = %a@]"
          p4string field
          print_expr init in
      fprintf p "@[<v 4>enum %a %a {@,%a@]@,}"
          print_type typ
          p4string name
          (print_list ~sep:"," print_member) members
  | DeclExternObject (info, name, type_params, methods) ->
      fprintf p "@[<v 4>extern %a%a {@,%a@]@,}"
          p4string name
          print_type_params type_params
          (print_list print_method_prototype) methods
  | DeclTypeDef (info, name, typ_or_decl) ->
    begin
      match typ_or_decl with
      | Coq_inl typ ->
        fprintf p "@[<h>typedef %a %a;@]"
            print_type typ
            p4string name
      | Coq_inr decl ->
        fprintf p "@[<h>typedef %a %a;@]"
            print_decl decl
            p4string name
    end
  | DeclNewType (info, name, typ_or_decl) ->
    begin
      match typ_or_decl with
      | Coq_inl typ ->
        fprintf p "@[<h>type %a %a;@]"
            print_type typ
            p4string name
      | Coq_inr decl ->
        fprintf p "@[<h>type %a %a;@]"
            print_decl decl
            p4string name
    end
  | DeclControlType (info, name, type_params, params) ->
      fprintf p "@[<hov 4>control %a%a@ (%a);@]"
          p4string name
          print_type_params type_params
          print_params params
  | DeclParserType (info, name, type_params, params) ->
      fprintf p "@[<hov 4>parser %a%a@ (%a);@]"
          p4string name
          print_type_params type_params
          print_params params
  | DeclPackageType (info, name, type_params, params) ->
      fprintf p "@[<hov 4>package %a%a@ (%a);@]"
          p4string name
          print_type_params type_params
          print_params params

let print_decls =
  print_list print_decl

let print_header p imports =
  let _ = List.map (fprintf p "#include \"%s\"@,") imports in ()

let print_program p (imports : string list) (program : Prog.program) =
  fprintf p "@[<v 0>";
  print_header p imports;
  print_decls p program;
  fprintf p "@]@."
