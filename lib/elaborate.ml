open Core_kernel
open Util
open Surface
open Checker_env

let subst_vars_name env type_name =
  begin match Checker_env.resolve_type_name_opt type_name env with
  | Some (TypTypeName v) -> P4name.BareName v
  | Some _ -> failwith "unexpected type value during elaboration"
  | None -> type_name
  end

let rec subst_vars_type env typ =
  let open Surface.Type in
  fst typ,
  match snd typ with
  | TypeName name ->
     TypeName (subst_vars_name env name)
  | SpecializedType { base; args } ->
     let base = subst_vars_type env base in
     let args = List.map ~f:(subst_vars_type env) args in
     SpecializedType { base; args }
  | HeaderStack { header; size } ->
     HeaderStack { header = subst_vars_type env header; size }
  | Tuple types ->
     Tuple (List.map ~f:(subst_vars_type env) types)
  | other -> other

let subst_vars_argument env arg = arg

let subst_vars_arguments env args =
  List.map ~f:(subst_vars_argument env) args

let rec subst_vars_expression env expr =
  let open Surface.Expression in
  let go = subst_vars_expression env in
  let go_l = List.map ~f:go in
  fst expr,
  match snd expr with
  | ArrayAccess { array; index } ->
     ArrayAccess { array = go array; index = go index }
  | BitStringAccess { bits; lo; hi } ->
     BitStringAccess { bits = go bits; lo = go lo; hi = go hi }
  | List { values } ->
     List { values = go_l values }
  | UnaryOp { op; arg } ->
     UnaryOp { op; arg = go arg }
  | BinaryOp { op; args = (x, y) } ->
     BinaryOp { op; args = (go x, go y) }
  | Cast { typ; expr } ->
     Cast { typ = subst_vars_type env typ; expr = go expr }
  | TypeMember { typ; name } ->
     TypeMember { typ = subst_vars_name env typ; name = name }
  | ExpressionMember { expr; name } ->
     ExpressionMember { expr = go expr; name = name }
  | Ternary { cond; tru; fls } ->
     Ternary { cond = go cond; tru = go tru; fls = go fls }
  | FunctionCall { func; type_args; args } ->
     FunctionCall { func = go func;
                    type_args = List.map ~f:(subst_vars_type env) type_args;
                    args = subst_vars_arguments env args }
  | NamelessInstantiation { typ; args } ->
     NamelessInstantiation { typ = subst_vars_type env typ;
                             args = subst_vars_arguments env args }
  | Mask { expr; mask } ->
     Mask { expr = go expr; mask = go mask }
  | Range { lo; hi } ->
     Range { lo = go lo; hi = go hi }
  | e -> e

let rec subst_vars_statement env stmt =
  let open Surface.Statement in
  fst stmt,
  match snd stmt with
  | MethodCall { func; type_args; args } ->
     MethodCall { func = subst_vars_expression env func;
                  type_args = List.map ~f:(subst_vars_type env) type_args;
                  args = subst_vars_arguments env args }
  | Assignment { lhs; rhs } ->
     Assignment { lhs = subst_vars_expression env lhs;
                  rhs = subst_vars_expression env rhs }
  | DirectApplication { typ; args } ->
     DirectApplication { typ = subst_vars_type env typ;
                         args = subst_vars_arguments env args }
  | Conditional { cond; tru; fls } ->
     Conditional { cond = subst_vars_expression env cond;
                   tru = subst_vars_statement env tru;
                   fls = option_map (subst_vars_statement env) fls }
  | BlockStatement { block } ->
     BlockStatement { block = subst_vars_block env block }
  | Exit -> Exit
  | EmptyStatement -> EmptyStatement
  | Return { expr } ->
     Return { expr = option_map (subst_vars_expression env) expr }
  | Switch { expr; cases } ->
     Switch { expr = subst_vars_expression env expr;
              cases = subst_vars_cases env cases }
  | DeclarationStatement { decl } ->
     DeclarationStatement { decl = subst_vars_stmt_declaration env decl }

and subst_vars_case env case =
  let open Surface.Statement in
  fst case,
  match snd case with
  | Action { label; code } ->
     Action { label = label; code = subst_vars_block env code }
  | FallThrough { label } ->
     FallThrough { label }

and subst_vars_cases env cases =
  List.map ~f:(subst_vars_case env) cases

and subst_vars_block env block =
  let open Surface.Block in
  let { annotations; statements } = snd block in
  fst block, { annotations; statements = List.map ~f:(subst_vars_statement env) statements }

and subst_vars_stmt_declaration env decl =
  let open Surface.Declaration in
  fst decl,
  match snd decl with
  | Instantiation { annotations; typ; args; name; init } ->
     Instantiation { annotations = annotations;
                     typ = subst_vars_type env typ;
                     args = subst_vars_arguments env args;
                     name = name;
                     init = option_map (subst_vars_block env) init }
  | Constant { annotations; typ; name; value } ->
     Constant { annotations = annotations;
                typ = subst_vars_type env typ;
                name = name;
                value = subst_vars_expression env value }
  | Variable  { annotations; typ; name; init } ->
     Variable { annotations = annotations;
                typ = subst_vars_type env typ;
                name = name;
                init = option_map (subst_vars_expression env) init }
  | _ -> raise_s [%message "declaration is not allowed as a statement"
                     ~decl:(decl: Surface.Declaration.t)]

let subst_vars_param env param =
  let open Surface.Parameter in
  let { annotations; direction; typ; variable; opt_value } = snd param in
  let typ = subst_vars_type env typ in
  let opt_value = Util.option_map (subst_vars_expression env) opt_value in
  fst param, { annotations; direction; typ; variable; opt_value }

let subst_vars_params env params =
  List.map ~f:(subst_vars_param env) params

let freshen_param env param =
  let param' = Renamer.freshen_p4string (renamer env) param in
  Checker_env.insert_type
    ~shadow:true (BareName param) (TypTypeName param') env, param'

let check_shadowing params =
  let param_compare (p1: P4string.t) (p2: P4string.t) = String.compare p1.str p2.str in
  match List.find_a_dup ~compare:param_compare params with
  | Some _ -> failwith "parameter shadowed?"
  | None -> ()

let rec freshen_params env params =
  check_shadowing params;
  match params with
  | [] -> env, []
  | param :: params ->
     let env, param = freshen_param env param in
     let env, params = freshen_params env params in
     env, param :: params

let elab_method env m =
  let open Surface.MethodPrototype in
  fst m,
  match snd m with
  | Constructor { annotations; name; params } ->
     let params = subst_vars_params env params in
     Constructor { annotations; name; params }
  | Method { annotations; return; name; type_params; params } ->
     let env, type_params = freshen_params env type_params in
     let return = subst_vars_type env return in
     let params = subst_vars_params env params in
     Method { annotations; return; name; type_params; params }
  | AbstractMethod { annotations; return; name; type_params; params } ->
     let env, type_params = freshen_params env type_params in
     let return = subst_vars_type env return in
     let params = subst_vars_params env params in
     AbstractMethod { annotations; return; name; type_params; params }

let elab_methods env ms =
  List.map ~f:(elab_method env) ms

let elab_decl env decl =
  let open Declaration in
  fst decl,
  match snd decl with
  | Function { return; name; type_params; params; body } ->

     let env, type_params = freshen_params env type_params in
     let return = subst_vars_type env return in
     let params = subst_vars_params env params in
     let body = subst_vars_block env body in
     Function { return; name; type_params; params; body }

  | ExternFunction { annotations; return; name; type_params; params } ->
     let env, type_params = freshen_params env type_params in
     let return = subst_vars_type env return in
     let params = subst_vars_params env params in
     ExternFunction { annotations; return; name; type_params; params }

  | ExternObject { annotations; name; type_params; methods } ->
     let env, type_params = freshen_params env type_params in
     let methods = elab_methods env methods in
     ExternObject { annotations; name; type_params; methods }

  | ControlType { annotations; name; type_params; params } ->
     let env, type_params = freshen_params env type_params in
     let params = subst_vars_params env params in
     ControlType { annotations; name; type_params; params }

  | ParserType { annotations; name; type_params; params } ->
     let env, type_params = freshen_params env type_params in
     let params = subst_vars_params env params in
     ParserType { annotations; name; type_params; params }

  | PackageType { annotations; name; type_params; params } ->
     let env, type_params = freshen_params env type_params in
     let params = subst_vars_params env params in
     PackageType { annotations; name; type_params; params }

  | d -> d

let rec elab_decls' env decls =
  match decls with
  | decl :: decls ->
     let decl = elab_decl env decl in
     decl :: elab_decls' env decls
  | [] -> []

let elab_decls env decls =
  (* add decl names to renamer first, because they are _free_ and
     cannot be changed, unlike bound type variable names! *)
  let observe_decl_name d =
    match Declaration.name_opt d with
    | Some name -> Renamer.observe_name (renamer env) name.str
    | None -> ()
  in
  List.iter ~f:observe_decl_name decls;
  elab_decls' env decls

let elab (P4lightram decls) =
  let env = Checker_env.empty_t () in
  P4lightram (elab_decls env decls), env.renamer
