open Core
open Util
open Types

module Renamer = struct
  type state = { counter : int;
                 seen : string list }
  type t = state ref

  let create () = ref { counter = 0; seen = [] }

  let seen_name st name =
    List.mem ~equal:(=) !st.seen name

  let observe_name st name =
    if seen_name st name
    then ()
    else st := { !st with seen = name :: !st.seen }

  let incr st =
    st := {!st with counter = !st.counter + 1}

  let rec gen_name st name =
    let { counter = i; _ } = !st in
    let new_name = Printf.sprintf "%s%d" name i in
    incr st;
    if seen_name st new_name
    then gen_name st name
    else new_name

  let freshen_name st name =
    let new_name =
      if seen_name st name
      then gen_name st name
      else name
    in
    observe_name st new_name;
    new_name

end

let rec subst_vars_type env typ =
  let open Types.Type in
  fst typ,
  match snd typ with
  | TypeName name ->
     let name_info, nm = name in
     begin match Env.resolve_type_name_opt nm env with
     | Some (TypeName v) -> (TypeName (name_info, v))
     | Some _ -> failwith "unexpected type value during elaboration"
     | None -> TypeName name
     end
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
  let open Types.Expression in
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
     TypeMember { typ = subst_vars_type env typ; name = name }
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
  let open Types.Statement in
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
  let open Types.Statement in
  fst case,
  match snd case with
  | Action { label; code } ->
     Action { label = label; code = subst_vars_block env code }
  | FallThrough { label } -> 
     FallThrough { label }

and subst_vars_cases env cases =
  List.map ~f:(subst_vars_case env) cases
  
and subst_vars_block env block =
  let open Types.Block in
  let { annotations; statements } = snd block in
  fst block, { annotations; statements = List.map ~f:(subst_vars_statement env) statements }

and subst_vars_stmt_declaration env decl =
  let open Types.Declaration in
  fst decl,
  match snd decl with
  | Instantiation { annotations; typ; args; name } ->
     Instantiation { annotations = annotations;
                     typ = subst_vars_type env typ;
                     args = subst_vars_arguments env args;
                     name = name }
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
                     ~decl:(decl: Types.Declaration.t)]

let subst_vars_param env param =
  let open Types.Parameter in
  let { annotations; direction; typ; variable; opt_value } = snd param in
  let typ = subst_vars_type env typ in
  let opt_value = Util.option_map (subst_vars_expression env) opt_value in
  fst param, { annotations; direction; typ; variable; opt_value }

let subst_vars_params env params =
  List.map ~f:(subst_vars_param env) params

let freshen_param env gen param = 
  let param' = Renamer.freshen_name gen param in
  Env.insert_type param (TypeName param') env, param'

let rec freshen_params env gen params =
  match params with
  | [] -> env, []
  | param :: params ->
     let info, pre_param = param in
     let env, pre_param = freshen_param env gen pre_param in
     let env, params = freshen_params env gen params in
     env, (info, pre_param) :: params

let elab_method env gen m =
  let open Types.MethodPrototype in
  fst m,
  match snd m with
  | Constructor { annotations; name; params } ->
     let params = subst_vars_params env params in
     Constructor { annotations; name; params }
  | Method { annotations; return; name; type_params; params } ->
     let env, type_params = freshen_params env gen type_params in
     let return = subst_vars_type env return in
     let params = subst_vars_params env params in
     Method { annotations; return; name; type_params; params }

let elab_methods env gen ms =
  List.map ~f:(elab_method env gen) ms

let elab_decl env gen decl =
  let open Declaration in
  fst decl,
  match snd decl with
  | Function { return; name; type_params; params; body } ->

     let env, type_params = freshen_params env gen type_params in
     let return = subst_vars_type env return in
     let params = subst_vars_params env params in
     let body = subst_vars_block env body in
     Function { return; name; type_params; params; body }

  | ExternFunction { annotations; return; name; type_params; params } ->
     let env, type_params = freshen_params env gen type_params in
     let return = subst_vars_type env return in
     let params = subst_vars_params env params in
     ExternFunction { annotations; return; name; type_params; params }

  | ExternObject { annotations; name; type_params; methods } ->
     let env, type_params = freshen_params env gen type_params in
     let methods = elab_methods env gen methods in
     ExternObject { annotations; name; type_params; methods }

  | ControlType { annotations; name; type_params; params } ->
     let env, type_params = freshen_params env gen type_params in
     let params = subst_vars_params env params in
     ControlType { annotations; name; type_params; params }

  | ParserType { annotations; name; type_params; params } ->
     let env, type_params = freshen_params env gen type_params in
     let params = subst_vars_params env params in
     ParserType { annotations; name; type_params; params }

  | PackageType { annotations; name; type_params; params } ->
     let env, type_params = freshen_params env gen type_params in
     let params = subst_vars_params env params in
     PackageType { annotations; name; type_params; params }

  | d -> d

let rec elab_decls env gen decls =
  match decls with
  | decl :: decls ->
     let decl = elab_decl env gen decl in
     let env = Env.insert_decl decl env in
     decl :: elab_decls env gen decls
  | [] -> []

let elab (Program decls) =
  let gen = Renamer.create () in
  let env = Env.empty_checker_env in
  Program (elab_decls env gen decls)
