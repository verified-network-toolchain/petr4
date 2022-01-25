open P4light
open Format

(***********************************************
              P4light.ml -> Type.v
 ***********************************************)

let print_bool p b =
  let s = 
    match b with
    | true -> "true"
    | false -> "false"
  in fprintf p "%s" s

let print_string p s =
  fprintf p "%s" s

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

let p4string p (s : P4string.t) =
  fprintf p "%s" s.str

let name_dot_prefix p (l: P4string.t list)=
  if List.length l == 0 then
    fprintf p "."
  else
    let f (elem: P4string.t) = 
      fprintf p "%s." elem.str in
    List.iter f l

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
  match n.width_signed with 
  | None ->
      fprintf p "%a" print_bigint n.value
  | Some (width, sign) ->
      let sign = if sign then "s" else "w" in 
      fprintf p "%a%s%a" 
          print_bigint width
          sign
          print_bigint n.value

let print_direction p (dir: direction) =
  let s = 
    match dir with
    | In -> "in " 
    | Out -> "out "
    | InOut -> "inout "
    | Directionless -> ""
  in fprintf p "%s" s

let print_name p (name : P4name.t) =
  match name with
  | BareName s ->
      fprintf p "%s" s.str
  | QualifiedName (namespaces, s) -> 
      fprintf p "%a%s" 
          name_dot_prefix namespaces
          s.str

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

let rec print_type p (typ : coq_P4Type) =
  match typ with
  | TypBool -> 
      fprintf p "bool"
  | TypString ->
      fprintf p "string"
  | TypInteger ->
      fprintf p "int"
  | TypInt width ->
      fprintf p "@[<h>int<%a>@]"
          print_bigint width
  | TypBit width ->
      fprintf p "@[<h>bit<%a>@]"
          print_bigint width
  | TypVarBit width ->
      fprintf p "@[<h>varbit<%a>@]"
          print_bigint width
  | TypArray (typ, size) -> 
      fprintf p "@[<h>%a[%a]@]"
          print_type typ
          print_bigint size
  | TypTuple typs ->
      fprintf p "@[<h>tuple%a@]"
          print_type_args typs
  | TypList typs ->
      failwith "unimplemented: print_type TypList"
  | TypRecord fields ->
      failwith "unimplemented: print_type TypRecord"
  | TypSet elem_typ ->
      failwith "unimplemented: print_type TypSet"
  | TypError ->
      fprintf p "error"
  | TypMatchKind ->
      fprintf p "match_kind"
  | TypVoid ->
      fprintf p "void"
  | TypHeader fields ->
      failwith "unimplemented: print_type TypHeader"
  | TypHeaderUnion fields ->
      failwith "unimplemented: print_type TypHeaderUnion"
  | TypStruct fields ->
      failwith "unimplemented: print_type TypStruct"
  | TypEnum (s, typ, members) ->
      failwith "unimplemented: print_type TypEnum"
  | TypTypeName name ->
      fprintf p "@[<h>%a@]" print_string name.str
  | TypNewType (s, typ) ->
      failwith "unimplemented: print_type TypNewType"
  | TypControl ctrl ->
      failwith "unimplemented: print_type TypControl"
  | TypParser ctrl ->
      failwith "unimplemented: print_type TypParser"
  | TypExtern s ->
      failwith "unimplemented: print_type TypExtern"
  | TypFunction func ->
      failwith "unimplemented: print_type TypFunction"
  | TypAction (data_params, ctrl_params) ->
      failwith "unimplemented: print_type TypAction"
  | TypTable s ->
      failwith "unimplemented: print_type TypTable"
  | TypPackage (type_params, wildcard_params, params) ->
      failwith "unimplemented: print_type TypPackage"
  | TypSpecializedType (base, args) ->
      if List.for_all printable_type args
      then fprintf p "@[<h>%a%a@]" 
                print_type base 
                print_type_args args
      else fprintf p "@[<h>%a@]" 
                print_type base
  | TypConstructor (type_params, wildcard_params, params, ret_type) ->
      failwith "unimplemented: print_type TypConstructor"
and print_param p (param: coq_P4Parameter) =
  match param with
  | MkParameter (opt, direction, typ, default_arg_id, variable) ->
      fprintf p "@[<h>";
      if opt
      then fprintf p "%@optional ";
      fprintf p "%a%a %a@]"
          print_direction direction
          print_type typ
          p4string variable
          (* (print_option (fun p v -> fprintf p " = %a" print_bigint v)) default_arg_id *)
and print_type_args p l =
  if List.length l <> 0
  then fprintf p "<%a>" (print_list ~sep:"," print_type) l
  else ()

let print_params p (params: coq_P4Parameter list) =
  fprintf p "@[<hv 0>%a@]" (print_list ~sep:"," print_param) params

let print_cstr_params p (params: coq_P4Parameter list) =
  if (List.length params <> 0)
  then fprintf p "(@[<hv 0>%a@])" (print_list ~sep:"," print_param) params
  else ()

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
    | Not -> "!"
    | BitNot -> "~"
    | UMinus -> "-"
  in fprintf p "%s" s

let print_op_bin p (op: coq_OpBin) =
  let s =
    match op with 
    | Plus -> "+"
    | PlusSat -> "|+|"
    | Minus -> "-"
    | MinusSat -> "|-|"
    | Mul -> "*"
    | Div -> "/"
    | Mod -> "%"
    | Shl -> "<<"
    | Shr -> ">>"
    | Le -> "<="
    | Ge -> ">="
    | Lt -> "<"
    | Gt -> ">"
    | Eq -> "=="
    | NotEq -> "!="
    | BitAnd -> "&"
    | BitXor -> "^"
    | BitOr -> "!"
    | PlusPlus -> "++"
    | And -> "&&"
    | Or -> "||"
  in fprintf p "%s" s

let rec print_expr p (expr : coq_Expression) =
  match expr with
  | MkExpression (info, pre_expr, typ, dir) ->
      fprintf p "@[<hov 4>%a@]" print_pre_expr pre_expr
and print_pre_expr p (pre_expr : coq_ExpressionPreT) =
  match pre_expr with
  | ExpBool b ->
      fprintf p "@[<h>%a@]" print_bool b
  | ExpInt n ->
      fprintf p "@[<h>%a@]" p4int n
  | ExpString s ->
      fprintf p "@[<h>\"%s\"@]" s.str
  | ExpName (name, loc) ->
      fprintf p "@[<h>%a@]" print_name name
  | ExpArrayAccess (array, index) ->
      fprintf p "@[<h>%a[%a]@]"
          print_expr array
          print_expr index
  | ExpBitStringAccess (bits, lo, hi) ->
      fprintf p "@[<h>%a[%a:%a]@]"
          print_expr bits
          print_bigint lo
          print_bigint hi
  | ExpList exprs ->
      fprintf p "{@[<hv 0>%a@]}"
          (print_list ~sep:"," print_expr) exprs
  | ExpRecord kvs ->
      fprintf p "{@[<hv 0>%a@]}"
          (print_list ~sep:"," print_keyvalue) kvs
  | ExpUnaryOp (op_uni, expr) ->
      fprintf p "@[<h>(%a %a)@]"
          print_op_uni op_uni
          print_expr expr
  | ExpBinaryOp (op_bin, expr_pair) ->
      fprintf p "@[<h>(%a %a %a)@]"
          print_expr (fst expr_pair)
          print_op_bin op_bin
          print_expr (snd expr_pair)
  | ExpCast (typ, expr) ->
      if printable_type typ
      then fprintf p "@[<h>(%a)%a@]" 
                print_type typ 
                print_expr expr 
      else fprintf p "@[<h>%a@]" print_expr expr
  | ExpTypeMember (name, s)->
      fprintf p "@[<h>%a.%s@]"
          p4string name s.str
  | ExpErrorMember s ->
      fprintf p "@[<h>error.%s@]" s.str
  | ExpExpressionMember (expr, s) ->
      fprintf p "@[<h>%a.%s@]"
          print_expr expr s.str
  | ExpTernary (cond, tru, fls) ->
      fprintf p "(@[<hv>%a ?@ %a :@ %a@])"
          print_expr cond
          print_expr tru
          print_expr fls
  | ExpFunctionCall (func, arg_types, args) ->
      if List.for_all printable_type arg_types
      then fprintf p "@[<hov 0>%a%a(%a)@]" 
                print_expr func 
                print_type_args arg_types
                print_args args 
      else fprintf p "@[<hov 0>%a(%a)@]"
                print_expr func
                print_args args
  | ExpNamelessInstantiation (typ, args) ->
      fprintf p "@[<h>%a(%a)@]"
          print_type typ
          (print_list ~sep:"," print_expr) args
  | ExpDontCare ->
      fprintf p "_"
and print_keyvalue p kv =
  match kv with
  | (key, value) ->
      fprintf p "@[<h>%a = %a@]"
          p4string key
          print_expr value
and print_args p (args: (coq_Expression option) list) = 
  let print_arg p arg = 
    match arg with
    | None -> print_pre_expr p ExpDontCare
    | Some expr -> print_expr p expr
  in fprintf p "@[<hv 0>%a@]" (print_list ~sep:"," print_arg) args

let print_exprs =
  print_list ~sep:"," print_expr

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
  fprintf p "@[<hv 0>%a@]" (print_list ~sep:"," print_match) matches

let print_table_action_ref p (action: coq_TableActionRef) =
  match action with
  | MkTableActionRef (info, action, typ) ->
      match action with
      | MkTablePreActionRef (name, []) ->
          fprintf p "@[<h>%a();@]"
              print_name name
      | MkTablePreActionRef (name, args) ->
          fprintf p "@[<h>%a(%a);@]"
              print_name name
              print_args args

let print_table_actions p (actions: coq_TableActionRef list)=
  if (List.length actions <> 0)
  then fprintf p "@[<v 4>actions = {@,%a@]@,}"
          (print_list print_table_action_ref) actions
  else fprintf p "@[<h>actions = { }@]"

let print_table_default_action p (action: coq_TableActionRef)=
  fprintf p "@[<h>default_action = %a@]"
      print_table_action_ref action

let print_table_key p (key: coq_TableKey) =
  match key with
  | MkTableKey (info, key, match_kind) ->
      fprintf p "@[<h>%a : %a;@]"
          print_expr key
          p4string match_kind

let print_table_keys p (keys: coq_TableKey list) =
  if (List.length keys <> 0) then
    fprintf p "@[<v 4>key = {@,%a@]@,}"
        (print_list print_table_key) keys

let print_table_entry p (entry: coq_TableEntry) =
  match entry with
  | MkTableEntry (info, matches, action) ->
      if List.length matches <= 1
      then 
        fprintf p "@[<h>%a : %a@]"
            print_matches matches
            print_table_action_ref action
      else
        fprintf p "@[<h>(%a) : %a@]"
            print_matches matches
            print_table_action_ref action

let print_table_entries p (entries: coq_TableEntry list)= 
  if (List.length entries <> 0) then
    fprintf p "@[<v 4>const entries = {@,%a@]@,}"
        (print_list print_table_entry) entries

let print_table_size p size = 
  fprintf p "@[<h>size = %a;@]"
      print_bigint size

let print_table_property p (property: coq_TableProperty) =
  match property with
  | MkTableProperty (info, const, s, expr) ->
      fprintf p "@[<h>%s%a = %a;@]@,"
          (if const then "const " else "")
          p4string s
          print_expr expr

type block_type = SwitchCase | OtherBlock

let print_stmt_switch_label p (label: coq_StatementSwitchLabel) =
  match label with
  | StatSwLabDefault info -> 
      fprintf p "default"
  | StatSwLabName (info, s) ->
      fprintf p "%s" s.str

let rec print_stmt_switch_case p (case: coq_StatementSwitchCase) =
  match case with
  | StatSwCaseAction (info, label, code) ->
      fprintf p "@[<h>%a : %a@]" 
          print_stmt_switch_label label
          print_block (SwitchCase, code)
  | StatSwCaseFallThrough (info, label) ->
      fprintf p "@[<h>%a:@]" 
          print_stmt_switch_label label
and print_pre_stmt p (pre_stmt: coq_StatementPreT) =
  match pre_stmt with
  | StatMethodCall (func, arg_types, args) ->
      if List.for_all printable_type arg_types
      then fprintf p "@[<h>%a%a(%a);@]"
                print_expr func
                print_type_args arg_types
                print_args args
      else fprintf p "@[<h>%a(%a);@]"
                print_expr func
                print_args args
  | StatAssignment (lhs, rhs) ->
      fprintf p "@[<hov 4>%a =@ %a;@]"
          print_expr lhs
          print_expr rhs
  | StatDirectApplication (typ, func_typ, args) ->
      fprintf p "@[<h>%a.apply(%a);@]"
          print_type typ
          print_args args
  | StatConditional (cond, tru, None) ->
      (match tru with 
      | MkStatement (_, (StatBlock _),_) ->
          fprintf p "@[<v 0>if (%a)@,%a@]"
              print_expr cond
              print_stmt tru
      | _ -> 
          fprintf p "@[<v 0>@[<v 4>if (%a)@,%a@]@,@]"
              print_expr cond
              print_stmt tru)
  | StatConditional (cond, tru, Some fls) ->
      (match tru with 
      | MkStatement (_, (StatBlock _),_) ->
          fprintf p "@[<v 0>if (%a)@,%a@]"
              print_expr cond
              print_stmt tru
      | _ -> 
          fprintf p "@[<v 0>@[<v 4>if (%a)@,%a@]@,@]"
              print_expr cond
              print_stmt tru);
      (match fls with 
      | MkStatement (_, (StatBlock _),_) ->
          fprintf p "@[<v 0>else@,%a@]"
              print_stmt fls
      | _ -> 
          fprintf p "@[<v 4>else@,%a@]"
              print_stmt fls);
  | StatBlock block ->
      fprintf p "@[<v 0>@[<v 4>%a"
          print_block (OtherBlock, block)
  | StatExit -> 
      fprintf p "@[<h>exit;@]"
  | StatEmpty -> 
      fprintf p "@[<h>;@]"
  | StatReturn None ->
      fprintf p "@[<h>return;@]"
  | StatReturn (Some expr) ->
      fprintf p "@[<h>return %a;@]"
          print_expr expr
  | StatSwitch (expr, cases) -> 
      fprintf p "@[<v 0>@[<v 4>switch (%a) {@,%a@]@,}@]"
          print_expr expr
          (print_list print_stmt_switch_case) cases
  | StatConstant (typ, s, value, loc) ->
      fprintf p "@[<hov 4>const %a %s =@ %a;@]"
          print_type typ
          s.str
          print_expr value
  | StatVariable (typ, s, None, loc) ->
      fprintf p "@[<h>%a %s;@]"
          print_type typ
          s.str
  | StatVariable (typ, s, Some init, loc) ->
      fprintf p "@[<hov 4>%a %s =@ %a;@]"
          print_type typ
          s.str
          print_expr init
  | StatInstantiation (typ, args, s, []) ->
      fprintf p "@[<h>%a(%a) %a;@]"
          print_type typ
          print_exprs args
          p4string s
  | StatInstantiation (typ, args, s, init) ->
      fprintf p "@[<v 0>@[<v 4>%a(%a) %s = {%a@]@,};@]"
          print_type typ
          print_exprs args
          s.str
          (print_list print_init) init
and print_stmt p (stmt : coq_Statement) =
  match stmt with
  | MkStatement (info, pre_stmt, typ) ->
      fprintf p "@[<hov 4>%a@]"
          print_pre_stmt pre_stmt 
and print_block p ((btype, block) : block_type * coq_Block)  =
  let rec print_block_aux p (block : coq_Block)=
    match block with 
    | BlockEmpty info -> 
        fprintf p ""
    | BlockCons (stmt, block) ->
      fprintf p "@,%a%a"
          print_stmt stmt
          print_block_aux block in
  match btype with 
  | SwitchCase ->
      (match block with
      | BlockEmpty _ -> 
            fprintf p "{ }"
      | BlockCons (stmt, rest) -> 
            fprintf p "@[<v 2>{ %a%a }@]" 
                      print_stmt stmt 
                      print_block_aux rest)
  | OtherBlock ->
      (match block with
      | BlockEmpty _ -> 
            fprintf p "{ }@]@]"
      | BlockCons _ -> 
            fprintf p "{%a@]@,}@]" print_block_aux block )
and print_init p (init : coq_Initializer) =
    match init with
    | InitFunction (info, ret, name, t_params, params, body) ->
        fprintf p "@[<v 0>@[<v 4>%a %s%a(%a) %a"
            print_type ret
            name.str
            print_type_params t_params
            print_params params
            print_block (OtherBlock, body)
    | InitInstantiation (info, typ, args, name, init) ->
        fprintf p "@[<v 0>@[<v 4>%a(%a) %s = {%a@]@,};@]"
            print_type typ
            print_exprs args
            name.str
            (print_list print_init) init

let print_parser_case p (case: coq_ParserCase) =
  match case with
  | MkParserCase (info, matches, next) ->
      fprintf p "@[<h>%a : %a;@]"
          print_matches matches
          p4string next
  
let print_parser_transition p (transition: coq_ParserTransition) =
  match transition with
  | ParserDirect (info, next) ->
      fprintf p "@[<h>transition@ %a;@]"
          p4string next
  | ParserSelect (info, exprs, cases) ->
      fprintf p "@[<v 4>transition select(%a) {@,%a@]@,}"
          print_exprs exprs
          (print_list print_parser_case) cases

let print_parser_state p (state: coq_ParserState) =
  let rec print_state_aux p (stmts : coq_Statement list)=
    match stmts with 
    | [] -> 
        fprintf p ""
    | stmt :: rest ->
       fprintf p "@,%a%a"
          print_stmt stmt
          print_state_aux rest in
  match state with
  | MkParserState (info, s, stmts, transition) ->
      fprintf p "@[<v 4>state %a {%a@,%a@]@,}"
          p4string s
          print_state_aux stmts
          print_parser_transition transition

let print_parser_states =
  print_list print_parser_state

let print_decl_field p (decl_field : coq_DeclarationField) =
  match decl_field with
  | MkDeclarationField (info, typ, name) ->
      fprintf p "@[<h>%a %a;@]"
          print_type typ
          p4string name

let print_decl_fields p (decl_fields : coq_DeclarationField list) =
  if (List.length decl_fields <> 0)
  then fprintf p "{@,%a@]@,}@]" (print_list print_decl_field) decl_fields
  else fprintf p "{ }@]@]"

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
      fprintf p "@[<v 0>@[<v 4>%a(%a) %a = {@,%a@]@,};@]"
          print_type typ
          print_exprs args
          p4string name
          (print_list print_decl) init
  | DeclParser (info, name, type_params, params, constructor_params, locals, states) ->
      fprintf p "@[<v 0>@[<v 4>parser %a%a@[<hov 0>(%a)@ %a@] {@,"
          p4string name
          print_type_params type_params
          print_params params
          print_cstr_params constructor_params;
      (if (List.length locals <> 0) then
        fprintf p "%a" (print_list print_decl) locals;
        fprintf p "@,");
      fprintf p "%a@]@,}@]" print_parser_states states
  | DeclControl (info, name, type_params, params, constructor_params, locals, apply) ->
      fprintf p "@[<v 0>@[<v 4>control %a%a@[<hov 0>(%a)@ %a@] {@,"
          p4string name
          print_type_params type_params
          print_params params
          print_cstr_params constructor_params;
      (if (List.length locals <> 0) then
        fprintf p "%a" (print_list print_decl) locals;
        fprintf p "@,");
      fprintf p "@[<v 0>@[<v 4>apply %a@]@,}@]" print_block (OtherBlock, apply)
  | DeclFunction (info, ret_type, name, type_params, params, body) ->
      fprintf p "@[<v 0>@[<v 4>%a %a%a(%a) %a"
          print_type ret_type
          p4string name
          print_type_params type_params
          print_params params
          print_block (OtherBlock, body)
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
          (print_option (fun p e -> fprintf p " =@ %a" print_expr e)) init
  | DeclValueSet (info, typ, size, name) ->
      fprintf p "@[<h>value_set<%a>(%a) %a;@]"
          print_type typ
          print_bigint size
          p4string name
  | DeclAction (info, name, data_params, ctrl_params, body) ->
      fprintf p "@[<v 0>@[<v 4>action %a(%a) %a"
          p4string name
          print_params (data_params @ ctrl_params)
          print_block (OtherBlock, body)
  | DeclTable (info, name, keys, actions, entries, 
              default_action, size, custom_properties) ->
      fprintf p "@[<v 4>table %a {@,%a@,%a@,%a@,%a@,%a"
          p4string name
          print_table_keys keys
          print_table_actions actions
          (print_option print_table_entries) entries
          (print_option print_table_default_action) default_action
          (print_option print_table_size) size;
      (if (List.length custom_properties) <> 0
      then 
        (fprintf p "@,";
        fprintf p "%a@]@,}" (print_list print_table_property) custom_properties)
      else 
        fprintf p "@]@,}" )
  | DeclHeader (info, name, fields) ->
      fprintf p "@[<v 0>@[<v 4>header %a %a"
          p4string name
          print_decl_fields fields
  | DeclHeaderUnion (info, name, fields) ->
      fprintf p "@[<v 0>@[<v 4>header_union %a %a"
          p4string name
          print_decl_fields fields
  | DeclStruct (info, name, fields) ->
      fprintf p "@[<v 0>@[<v 4>struct %a %a"
          p4string name
          print_decl_fields fields
  | DeclError (info, []) ->
      fprintf p "@[<h>error { }@]"
  | DeclError (info, members) ->
      fprintf p "@[<v 0>@[<v 4>error {@,%a@]@,}@]"
          (print_list ~sep:"," p4string) members
  | DeclMatchKind (info, []) ->
     fprintf p "@[<h>match_kind { }@]"
  | DeclMatchKind (info, members) ->
     fprintf p "@[<v 0>@[<v 4>match_kind {@,%a@]@,}@]"
          (print_list ~sep:"," p4string) members
  | DeclEnum (info, name, []) ->
      fprintf p "@[<h>enum %a { }@]"
          p4string name
  | DeclEnum (info, name, members) ->
      fprintf p "@[<v 0>@[<v 4>enum %a {@,%a@]@,}@]"
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
      fprintf p "@[<v 0>@[<v 4>enum %a %a {@,%a@]@,}@]"
          print_type typ
          p4string name
          (print_list ~sep:"," print_member) members
  | DeclExternObject (info, name, type_params, methods) ->
      fprintf p "@[<v 0>@[<v 4>extern %a%a {@,%a@]@,}@]"
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

let print_program p (imports : string list) (program : P4light.program) =
  fprintf p "@[<v 0>";
  print_header p imports;
  let _, sub_program = List.fold_right 
                    (fun decl (counter, agg) -> 
                      if counter < 20 then (counter + 1, decl :: agg) else (counter, agg) ) program (0, []) in
  print_decls p sub_program;
  fprintf p "@]@."
