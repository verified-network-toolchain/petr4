(* adds type variable at various places. check with Ryan. *)

module I = Info
open Core
open Prog.Env
open Util
open Types
module Info = I

let subst_vars_name env type_name =
  begin match CheckerEnv.resolve_type_name_opt type_name env with
  | Some (TypeName v) -> v
  | Some _ -> failwith "unexpected type value during elaboration"
  | None -> type_name
  end

let rec subst_vars_type env typ =
  let open Types.Type in
  (* fst typ, *)
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
  let open Types.Expression in
  let go = subst_vars_expression env in
  let go_l = List.map ~f:go in
  (* fst expr, *)
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
  let open Types.Statement in
  (* fst stmt, *)
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
  let open Types.Statement in
  (* fst case, *)
  match case with
  | Action { tags; label; code } ->
     Action { tags; label = label; code = subst_vars_block env code }
  | FallThrough { tags; label } ->
     FallThrough { tags; label }

and subst_vars_cases env cases =
  List.map ~f:(subst_vars_case env) cases

and subst_vars_block env block =
  let open Types.Block in
  let { tags; annotations; statements } = block in
    { tags; annotations; statements = List.map ~f:(subst_vars_statement env) statements }

and subst_vars_stmt_declaration env decl =
  let open Types.Declaration in
  (* fst decl, *)
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
  | _ -> raise_s [%message "declaration is not allowed as a statement"
                     ~decl:(decl: Types.Declaration.t)]

let subst_vars_param env param =
  let open Types.Parameter in
  let { tags; annotations; direction; typ; variable; opt_value } = param in
  let typ = subst_vars_type env typ in
  let opt_value = Util.option_map (subst_vars_expression env) opt_value in
    { tags; annotations; direction; typ; variable; opt_value }

let subst_vars_params env params =
  List.map ~f:(subst_vars_param env) params

let freshen_param env param =
  let param' = Renamer.freshen_name (CheckerEnv.renamer env) param in
  CheckerEnv.insert_type ~shadowing:true (BareName {tags=Info.dummy; name={tags=Info.dummy; string=param}}) (TypeName (BareName {tags=Info.dummy; name={tags=Info.dummy; string=param'}})) env, param'

let check_shadowing (params: P4String.t list) =
  (* let open Types.P4String in *)
  let param_compare p1 p2 = String.compare p1.P4String.string p2.P4String.string in
  match List.find_a_dup ~compare:param_compare params with
  | Some _ -> failwith "parameter shadowed?"
  | None -> ()

let rec freshen_params env (params: P4String.t list) =
  check_shadowing params;
  match params with
  | [] -> env, []
  | {P4String.tags; P4String.string=param} :: params ->
     (* let pre_param = param.string in *)
     let env, pre_param = freshen_param env param in
     let env, params = freshen_params env params in
     env, {P4String.tags; P4String.string=pre_param} :: params

let elab_method env m =
  let open Types.MethodPrototype in
  (* fst m, *)
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
  (* fst decl, *)
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
    | Some {P4String.tags; P4String.string=name} -> Renamer.observe_name (CheckerEnv.renamer env) name
    | None -> ()
  in
  List.iter ~f:observe_decl_name decls;
  elab_decls' env decls

let elab (Program decls) =
  let env = CheckerEnv.empty_t () in
  Program (elab_decls env decls), CheckerEnv.renamer env
