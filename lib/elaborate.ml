(* adds type variable at various places. check with Ryan. *)
open Core
open Util
open Poulet4.Typed
open Surface
open Checker_env

let subst_vars_name env type_name =
  begin match Checker_env.resolve_type_name_opt type_name env with
  | Some (TypTypeName v) -> BareName v
  | Some _ -> failwith "unexpected type value during elaboration"
  | None -> type_name
  end

let rec subst_vars_type env typ =
  let open Surface.Type in
  match typ with
  | TypeName {tags; name} ->
     TypeName {tags; name=subst_vars_name env name}
  | SpecializedType { tags; base; args } ->
     let base = subst_vars_type env base in
     let args = List.map ~f:(subst_vars_type env) args in
     SpecializedType { tags; base; args }
  | HeaderStack { tags; header; size } ->
     HeaderStack { tags; header = subst_vars_type env header; size }
  | Tuple {tags; xs} ->
     Tuple {tags; xs=List.map ~f:(subst_vars_type env) xs}
  | other -> other

let subst_vars_argument env arg = arg

let subst_vars_arguments env args =
  List.map ~f:(subst_vars_argument env) args

let rec subst_vars_expression env expr =
  let open Surface.Expression in
  let go = subst_vars_expression env in
  let go_l = List.map ~f:go in
  match expr with
  | ArrayAccess { tags; array; index } ->
     ArrayAccess { tags; array = go array; index = go index }
  | BitStringAccess { tags; bits; lo; hi } ->
     BitStringAccess { tags; bits = go bits; lo = go lo; hi = go hi }
  | List { tags; values } ->
     List { tags; values = go_l values }
  | UnaryOp { tags; op; arg } ->
     UnaryOp { tags; op; arg = go arg }
  | BinaryOp { tags; op; args = (x, y) } ->
     BinaryOp { tags; op; args = (go x, go y) }
  | Cast { tags; typ; expr } ->
     Cast { tags; typ = subst_vars_type env typ; expr = go expr }
  | TypeMember { tags; typ; name } ->
     TypeMember { tags; typ = subst_vars_name env typ; name = name }
  | ExpressionMember { tags; expr; name } ->
     ExpressionMember { tags; expr = go expr; name = name }
  | Ternary { tags; cond; tru; fls } ->
     Ternary { tags; cond = go cond; tru = go tru; fls = go fls }
  | FunctionCall { tags; func; type_args; args } ->
     FunctionCall { tags;
                    func = go func;
                    type_args = List.map ~f:(subst_vars_type env) type_args;
                    args = subst_vars_arguments env args }
  | NamelessInstantiation { tags; typ; args } ->
     NamelessInstantiation { tags; 
                             typ = subst_vars_type env typ;
                             args = subst_vars_arguments env args }
  | Mask { tags; expr; mask } ->
     Mask { tags; expr = go expr; mask = go mask }
  | Range { tags; lo; hi } ->
     Range { tags; lo = go lo; hi = go hi }
  | e -> e

let rec subst_vars_statement env stmt =
  let open Surface.Statement in
  match stmt with
  | MethodCall { tags; func; type_args; args } ->
     MethodCall { tags;
                  func = subst_vars_expression env func;
                  type_args = List.map ~f:(subst_vars_type env) type_args;
                  args = subst_vars_arguments env args }
  | Assignment { tags; lhs; rhs } ->
     Assignment { tags; 
                  lhs = subst_vars_expression env lhs;
                  rhs = subst_vars_expression env rhs }
  | DirectApplication { tags; typ; args } ->
     DirectApplication { tags;
                         typ = subst_vars_type env typ;
                         args = subst_vars_arguments env args }
  | Conditional { tags; cond; tru; fls } ->
     Conditional { tags;
                   cond = subst_vars_expression env cond;
                   tru = subst_vars_statement env tru;
                   fls = option_map (subst_vars_statement env) fls }
  | BlockStatement { tags; block } ->
     BlockStatement { tags; block = subst_vars_block env block }
  | Exit {tags} -> Exit {tags}
  | EmptyStatement {tags} -> EmptyStatement {tags}
  | Return { tags; expr } ->
     Return { tags; expr = option_map (subst_vars_expression env) expr }
  | Switch { tags; expr; cases } ->
     Switch { tags; 
              expr = subst_vars_expression env expr;
              cases = subst_vars_cases env cases }
  | DeclarationStatement { tags; decl } ->
     DeclarationStatement { tags;
                            decl = subst_vars_stmt_declaration env decl }

and subst_vars_case env case =
  let open Surface.Statement in
  match case with
  | Action { tags; label; code } ->
     Action { tags; label = label; code = subst_vars_block env code }
  | FallThrough { tags; label } ->
     FallThrough { tags; label }

and subst_vars_cases env cases =
  List.map ~f:(subst_vars_case env) cases

and subst_vars_block env block =
  let open Surface.Block in
  let { tags; annotations; statements } = block in
    { tags; annotations; statements = List.map ~f:(subst_vars_statement env) statements }

and subst_vars_stmt_declaration env decl =
  let open Surface.Declaration in
  match decl with
  | Instantiation { tags; annotations; typ; args; name; init } ->
     Instantiation { tags;
                     annotations = annotations;
                     typ = subst_vars_type env typ;
                     args = subst_vars_arguments env args;
                     name = name;
                     init = option_map (subst_vars_block env) init }
  | Constant { tags; annotations; typ; name; value } ->
     Constant { tags;
                annotations = annotations;
                typ = subst_vars_type env typ;
                name = name;
                value = subst_vars_expression env value }
  | Variable  { tags; annotations; typ; name; init } ->
     Variable { tags;
                annotations = annotations;
                typ = subst_vars_type env typ;
                name = name;
                init = option_map (subst_vars_expression env) init }
  | _ -> failwith "declaration is not allowed as a statement"
         (* decl: Surface.Declaration.t *)

let subst_vars_param env param =
  let open Surface.Parameter in
  let { tags; annotations; direction; typ; variable; opt_value } = param in
  let typ = subst_vars_type env typ in
  let opt_value = Util.option_map (subst_vars_expression env) opt_value in
    { tags; annotations; direction; typ; variable; opt_value }

let subst_vars_params env params =
  List.map ~f:(subst_vars_param env) params

let freshen_param env param =
  let param' = Renamer.freshen_p4string (renamer env) param in
  Checker_env.insert_type
    ~shadow:true (BareName param) (TypTypeName param') env, param'

let check_shadowing (params: P4string.t list) =
  let param_compare (p1: P4string.t) (p2: P4string.t) =
    String.compare p1.str p2.str in
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
  match m with
  | Constructor { tags; annotations; name; params } ->
     let params = subst_vars_params env params in
     Constructor { tags; annotations; name; params }
  | Method { tags; annotations; return; name; type_params; params } ->
     let env, type_params = freshen_params env type_params in
     let return = subst_vars_type env return in
     let params = subst_vars_params env params in
     Method { tags; annotations; return; name; type_params; params }
  | AbstractMethod { tags; annotations; return; name; type_params; params } ->
     let env, type_params = freshen_params env type_params in
     let return = subst_vars_type env return in
     let params = subst_vars_params env params in
     AbstractMethod { tags; annotations; return; name; type_params; params }

let elab_methods env ms =
  List.map ~f:(elab_method env) ms

let elab_decl env decl =
  let open Declaration in
  match decl with
  | Function { tags; return; name; type_params; params; body } ->

     let env, type_params = freshen_params env type_params in
     let return = subst_vars_type env return in
     let params = subst_vars_params env params in
     let body = subst_vars_block env body in
     Function { tags; return; name; type_params; params; body }

  | ExternFunction { tags; annotations; return; name; type_params; params } ->
     let env, type_params = freshen_params env type_params in
     let return = subst_vars_type env return in
     let params = subst_vars_params env params in
     ExternFunction { tags; annotations; return; name; type_params; params }

  | ExternObject { tags; annotations; name; type_params; methods } ->
     let env, type_params = freshen_params env type_params in
     let methods = elab_methods env methods in
     ExternObject { tags; annotations; name; type_params; methods }

  | ControlType { tags; annotations; name; type_params; params } ->
     let env, type_params = freshen_params env type_params in
     let params = subst_vars_params env params in
     ControlType { tags; annotations; name; type_params; params }

  | ParserType { tags; annotations; name; type_params; params } ->
     let env, type_params = freshen_params env type_params in
     let params = subst_vars_params env params in
     ParserType { tags; annotations; name; type_params; params }

  | PackageType { tags; annotations; name; type_params; params } ->
     let env, type_params = freshen_params env type_params in
     let params = subst_vars_params env params in
     PackageType { tags; annotations; name; type_params; params }

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

let elab (Program decls) =
  let env = Checker_env.empty_t () in
  Program (elab_decls env decls), env.renamer
