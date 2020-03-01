open Types
open Typed
open Util
open Env
(* hack *)
module Petr4Error = Error
module Petr4Info = Info
open Core
open Petr4Error
module Error = Petr4Error
module Info = Petr4Info

let find_decl_opt name decls =
  let ok decl =
    match Prog.Declaration.name_opt decl with
    | Some decl_name ->
       name = snd decl_name
    | None -> false
  in
  List.find ~f:ok decls

let find_decl name decls =
  let ok decl =
    name = snd (Prog.Declaration.name decl)
  in
  match List.find ~f:ok decls with
  | Some v -> v
  | None -> raise (UnboundName name)

let make_assert expected unwrap = fun info typ ->
  match unwrap typ with
  | Some v -> v
  | None -> raise_mismatch info expected typ

let assert_array = make_assert "array"
  begin function
  | Array array_typ -> Some array_typ
  | _ -> None
  end

let assert_bool = make_assert "bool"
  begin function
  | Bool -> Some Type.Bool
  | _ -> None
  end

let assert_bit = make_assert "unsigned int"
  begin function
  | Bit { width } -> Some (Type.Bit { width })
  | _ -> None
  end

(* numeric(t) <=> t = int \/ t = int<n> \/ t = bit<n> *)
let assert_numeric = make_assert "integer"
  begin function
  | Integer -> Some None
  | Int typ
  | Bit typ -> Some (Some typ)
  | _ -> None
  end

let rec is_lvalue (_, expr) =
  let open Types.Expression in
  match expr with
  | Name _
  | TopLevel _ -> true
  | ExpressionMember { expr = lvalue; _ }
  | ArrayAccess { array = lvalue; _ }
  | BitStringAccess { bits = lvalue; _ } ->
     is_lvalue lvalue
  | _ -> false

(* Evaluate the expression [expr] at compile time. Make sure to
 * typecheck the expression before trying to evaluate it! *)
let rec compile_time_eval_expr (env: CheckerEnv.t) (expr: Prog.Expression.t) : Value.value option =
  match (snd expr).expr with
  | Name (_, var) ->
     CheckerEnv.find_const_opt var env
  | True -> Some (Value.VBool true)
  | False -> Some (Value.VBool false)
  | String (_, str) -> Some (Value.VString str)
  | Int (_, i) ->
     begin match i.width_signed with
     | None ->
        Some (Value.VInteger i.value)
     | Some (width, signed) ->
        if signed
        then Some (Value.VInt { w = Bigint.of_int width; v = i.value })
        else Some (Value.VBit { w = Bigint.of_int width; v = i.value })
     end
  | UnaryOp { op; arg } -> failwith "unimplemented"
  | BinaryOp { op; args } -> failwith "unimplemented"
  | Cast { typ; expr } -> compile_time_eval_expr env expr
  | TypeMember {typ; name } -> failwith "unimplemented"
  | Ternary {cond; tru; fls } -> failwith "unimplemented"
  | _ -> None

let compile_time_eval_bigint env expr: Bigint.t =
  match compile_time_eval_expr env expr with
  | Some (Value.VInt { v; _})
  | Some (Value.VBit { v; _})
  | Some (Value.VInteger v) ->
     v
  | _ -> raise_s [%message "could not compute compile-time-known numerical value for expr"
                     ~expr:(expr: Prog.Expression.t)]

(* Evaluate the declaration [decl] at compile time, updating env.const
 * with any bindings made in the declaration.  Make sure to typecheck
 * [decl] before trying to evaluate it! *)
let compile_time_eval_decl (env: CheckerEnv.t) (decl: Prog.Declaration.t) : CheckerEnv.t =
  match snd decl with
  | Constant { name; value; _ } ->
     CheckerEnv.insert_const (snd name) value env
  | _ -> env

let get_type_params (t: Typed.Type.t) : string list =
  match t with
  | Package {type_params; _}
  | Control {type_params; _}
  | Parser {type_params; _}
  | Extern {type_params; _}
  | Function {type_params; _} ->
     type_params
  | _ ->
     []

let drop_type_params (t: Typed.Type.t) : Typed.Type.t =
  match t with
  | Package p ->
     Package {p with type_params = []}
  | Control c ->
     Control {c with type_params = []}
  | Parser p ->
     Parser {p with type_params = []}
  | Extern e ->
     Extern {e with type_params = []}
  | Function f ->
     Function {f with type_params = []}
  | t -> t

(* Eliminate all type references in typ and replace them with the type they
 * refer to. The result of saturation will contain no TypeName constructors
 * anywhere. It may contain TypeName constructors.
 *
 * Warning: this will loop forever if you give it an environment with circular
 * TypeName references.
 *)
let rec saturate_type (env: CheckerEnv.t) (typ: Typed.Type.t) : Typed.Type.t =
  let open Type in
  let saturate_field env (field: RecordType.field) =
    {field with typ = saturate_type env field.typ}
  in
  let saturate_rec env ({fields}: RecordType.t) : RecordType.t =
    {fields = List.map ~f:(saturate_field env) fields}
  in
  let saturate_construct_param env (param: ConstructParam.t) =
    {param with typ = saturate_type env param.typ}
  in
  let saturate_construct_params env (params: ConstructParam.t list) =
    List.map ~f:(saturate_construct_param env) params
  in
  let saturate_param env (param: Typed.Parameter.t) =
    {param with typ = saturate_type env param.typ}
  in
  let saturate_pkg env (pkg: PackageType.t) : PackageType.t =
    let env = CheckerEnv.insert_type_vars pkg.type_params env in
    {type_params = pkg.type_params;
     parameters = saturate_construct_params env pkg.parameters}
  in
  let saturate_ctrl env (ctrl: ControlType.t) : ControlType.t =
    let env = CheckerEnv.insert_type_vars ctrl.type_params env in
    {type_params = ctrl.type_params;
     parameters = List.map ~f:(saturate_param env) ctrl.parameters}
  in
  let rec saturate_extern env (extern: ExternType.t) : ExternType.t =
    let env = CheckerEnv.insert_type_vars extern.type_params env in
    { extern with
      methods = List.map ~f:(saturate_method env) extern.methods }
  and saturate_method env (m: ExternType.extern_method) =
    { m with typ = saturate_function env m.typ }
  and saturate_function env (fn: FunctionType.t) : FunctionType.t =
    let env = CheckerEnv.insert_type_vars fn.type_params env in
    {type_params = fn.type_params;
     parameters = List.map ~f:(saturate_param env) fn.parameters;
     return = saturate_type env fn.return}
  and saturate_action env (action: ActionType.t) : ActionType.t =
    { data_params = List.map ~f:(saturate_param env) action.data_params;
      ctrl_params = List.map ~f:(saturate_construct_param env) action.ctrl_params }
  in
  match typ with
  | TypeName t ->
     begin match CheckerEnv.resolve_type_name_opt t env with
     | None -> typ
     | Some (TypeName t') ->
        if t' = t
        then typ
        else saturate_type env (TypeName t')
     | Some typ' ->
        saturate_type env typ'
     end
  | TopLevelType typ ->
      saturate_type env (CheckerEnv.resolve_type_name_toplevel typ env)
  | Bool | String | Integer
  | Int _ | Bit _ | VarBit _
  | Error | MatchKind | Void
  | Table _ ->
      typ
  | Array arr ->
      Array {arr with typ = saturate_type env arr.typ}
  | Tuple {types} ->
      Tuple {types = List.map ~f:(saturate_type env) types}
  | List {types} ->
      List {types = List.map ~f:(saturate_type env) types}
  | Set typ ->
      Set (saturate_type env typ)
  | Header rec_typ ->
      Header (saturate_rec env rec_typ)
  | HeaderUnion rec_typ ->
      HeaderUnion (saturate_rec env rec_typ)
  | Struct rec_typ ->
      Struct (saturate_rec env rec_typ)
  | Enum enum ->
      Enum {enum with typ = option_map (saturate_type env) enum.typ}
  | SpecializedType spec ->
      SpecializedType {base = saturate_type env spec.base;
                       args = List.map ~f:(saturate_type env) spec.args}
  | Package pkg ->
      Package (saturate_pkg env pkg)
  | Control control ->
      Control (saturate_ctrl env control)
  | Parser control ->
      Parser (saturate_ctrl env control)
  | Extern extern ->
      Extern (saturate_extern env extern)
  | Function func ->
      Function (saturate_function env func)
  | Action action ->
    Action (saturate_action env action)

type var_constraint = string * Typed.Type.t option [@@deriving sexp]
type var_constraints = var_constraint list [@@deriving sexp]
type soln = var_constraints option [@@deriving sexp]

let empty_constraints unknowns : var_constraints =
  let empty_constraint var =
    (var, None)
  in
  List.map ~f:empty_constraint unknowns

let single_constraint vars var typ : var_constraints =
  let empty = empty_constraints vars in
  let update (v, emp) =
    if v = var
    then (v, Some typ)
    else (v, emp)
  in
  List.map ~f:update empty

(* This needs a real meet operator *)
let rec merge_constraints env xs ys =
  let fail () =
    raise_s [%message "could not merge constraint sets during type argument inference"
                ~xs:(xs: (string * Typed.Type.t option) list)
                ~ys:(ys: (string * Typed.Type.t option) list)]
  in
  let merge ((x_var, x_typ), (y_var, y_typ)) =
    match x_typ, y_typ with
    | None, _ -> y_var, y_typ
    | _, None -> x_var, x_typ
    | Some x_typ, Some y_typ ->
       if type_equality env x_typ y_typ
       then (x_var, Some x_typ)
       else fail ()
  in
  match List.zip xs ys with
  | Ok xys ->
     List.map ~f:merge xys
  | Unequal_lengths -> fail ()

and constraints_to_type_args _ (cs: var_constraints) : (string * Typed.Type.t) list =
  let constraint_to_type_arg (var, type_opt) =
    match type_opt with
    | Some t -> (var, t)
    | None -> raise_s [%message "could not solve for type argument" ~var]
  in
  List.map ~f:constraint_to_type_arg cs

and gen_all_constraints (env: CheckerEnv.t) unknowns params_args constraints =
  match params_args with
  | (param, Some arg) :: more ->
     let arg_type = type_expression env arg in
     let param_type = param.Parameter.typ in
     begin match solve_types env [] unknowns param_type arg_type with
     | Some arg_constraints ->
        let constraints = merge_constraints env constraints arg_constraints in
        gen_all_constraints env unknowns more constraints
     | None -> raise_s [%message "could not solve type equality t1 = t2"
                           ~t1:(reduce_type env param_type: Typed.Type.t)
                           ~t2:((snd arg_type).typ: Typed.Type.t)
                           ~env:(env: CheckerEnv.t)]
     end
  | (param_type, None) :: more ->
     gen_all_constraints env unknowns more constraints
  | [] ->
     constraints

and infer_type_arguments env ret type_params_args params_args constraints =
  let insert (env, args, unknowns) (type_var, type_arg) =
    match type_arg with
    | Some arg ->
       CheckerEnv.insert_type type_var arg env, (type_var, arg) :: args, unknowns
    | None ->
       CheckerEnv.insert_type_var type_var env, args, type_var :: unknowns
  in
  let env, params_args', unknowns = List.fold ~f:insert ~init:(env, [], []) type_params_args in
  let constraints =
    empty_constraints unknowns
    |> gen_all_constraints env unknowns params_args
  in
  params_args' @ constraints_to_type_args ret constraints

and merge_solutions env soln1 soln2 =
  match soln1, soln2 with
  | None, _
  | _, None -> None
  | Some constraints1, Some constraints2 ->
     Some (merge_constraints env constraints1 constraints2)

and solve_lists: 'a 'b.
                 CheckerEnv.t -> string list ->
                 f:('a * 'b -> soln) -> 'a list -> 'b list -> soln =
  fun env unknowns ~f xs ys ->
  zip_map_fold xs ys
    ~f:f
    ~merge:(merge_solutions env)
    ~init:(Some (empty_constraints unknowns))
  |> option_collapse

and solve_constructor_params_equality env equiv_vars unknowns ps1 ps2 =
  let open Typed.ConstructParam in
  let solve_params (p1, p2) =
    solve_types env equiv_vars unknowns p1.typ p2.typ
  in
  solve_lists env unknowns ps1 ps2 ~f:solve_params

and solve_record_type_equality env equiv_vars unknowns (rec1: RecordType.t) (rec2: RecordType.t) =
  let open RecordType in
  let solve_fields (f1, f2) =
    if f1.name = f2.name
    then solve_types env equiv_vars unknowns f1.typ f2.typ
    else None
  in
  let field_cmp f1 f2 =
    String.compare f1.name f2.name
  in
  let fields1 = List.sort ~compare:field_cmp rec1.fields in
  let fields2 = List.sort ~compare:field_cmp rec2.fields in
  solve_lists env unknowns fields1 fields2 ~f:solve_fields

and solve_enum_type_equality env equiv_vars unknowns enum1 enum2 =
  let open EnumType in
  let soln =
    match enum1.typ, enum2.typ with
    | Some typ1, Some typ2 ->
        solve_types env equiv_vars unknowns typ1 typ2
    | None, None -> Some (empty_constraints unknowns)
    | _, _ -> None
  in
  let mems1 = List.sort ~compare:String.compare enum1.members in
  let mems2 = List.sort ~compare:String.compare enum2.members in
  if mems1 = mems2
  then soln
  else None

and solve_package_type_equality env equiv_vars unknowns pkg1 pkg2 =
  let open PackageType in
  match List.zip pkg1.type_params pkg2.type_params with
  | Ok param_pairs ->
     let equiv_vars' = equiv_vars @ param_pairs in
     solve_constructor_params_equality env equiv_vars' unknowns pkg1.parameters pkg2.parameters
  | Unequal_lengths -> None

and solve_params_equality env equiv_vars unknowns ps1 ps2 =
  let open Parameter in
  let param_eq (p1, p2) =
    if p1.direction = p2.direction
    then solve_types env equiv_vars unknowns p1.typ p2.typ
    else None
  in
  solve_lists env unknowns ~f:param_eq ps1 ps2

and solve_control_type_equality env equiv_vars unknowns ctrl1 ctrl2 =
  let open ControlType in
  match List.zip ctrl1.type_params ctrl2.type_params with
  | Ok param_pairs ->
     let equiv_vars' = equiv_vars @ param_pairs in
     solve_params_equality env equiv_vars' unknowns ctrl1.parameters ctrl2.parameters
  | Unequal_lengths -> None

and solve_extern_type_equality env equiv_vars unknowns extern1 extern2 =
  let open Typed.ExternType in
  match List.zip extern1.type_params extern2.type_params with
  | Ok param_pairs ->
      let equiv_vars' = equiv_vars @ param_pairs in
      let method_cmp m1 m2 =
          String.compare m1.name m2.name
      in
      let solve_method_eq (m1, m2) =
        if m1.name = m2.name
        then solve_function_type_equality env equiv_vars' unknowns m1.typ m2.typ
        else None
      in
      let methods1 = List.sort ~compare:method_cmp extern1.methods in
      let methods2 = List.sort ~compare:method_cmp extern2.methods in
      solve_lists env unknowns ~f:solve_method_eq methods1 methods2
  | Unequal_lengths -> None

and solve_function_type_equality env equiv_vars unknowns func1 func2 =
  let open FunctionType in
  match List.zip func1.type_params func2.type_params with
  | Ok param_pairs ->
     let equiv_vars' = equiv_vars @ param_pairs in
     merge_solutions env (solve_types env equiv_vars' unknowns func1.return func2.return)
                         (solve_params_equality env equiv_vars' unknowns func1.parameters func2.parameters)
  | Unequal_lengths -> None

and solve_action_type_equality env equiv_vars unknowns action1 action2 =
  let open ActionType in
  merge_solutions env
    (solve_params_equality env equiv_vars unknowns action1.data_params action2.data_params)
    (solve_constructor_params_equality env equiv_vars unknowns action1.ctrl_params action2.ctrl_params)

and type_vars_equal_under env equiv_vars tv1 tv2 =
  match equiv_vars with
  | (a, b)::rest ->
      if tv1 = a || tv2 = b
      then tv1 = a && tv2 = b
      else type_vars_equal_under env rest tv1 tv2
  | [] ->
      tv1 = tv2

and reduce_type : CheckerEnv.t -> Typed.Type.t -> Typed.Type.t =
  fun env typ ->
  let typ = saturate_type env typ in
  match typ with
  | SpecializedType { base; args } ->
     let base = reduce_type env base in
     begin match get_type_params base with
     | [] -> begin match args with
             | [] -> base
             | _ -> typ (* stuck type application *)
             end
     | t_params ->
        let args = List.map ~f:(reduce_type env) args in
        begin match List.zip t_params args with
        | Ok pairs ->
           let base = drop_type_params base in
           reduce_type (CheckerEnv.insert_types pairs env) base
        | Unequal_lengths ->
           failwith "mismatch in # of type params and type args"
        end
     end
  | _ -> typ

(* [type_equality env t1 t2] is true if and only if expression type t1
 * is equivalent to expression type t2 under environment env.
 *  Alpha equivalent types are equal. *)
and type_equality env t1 t2 =
  match solve_types env [] [] t1 t2 with
  | Some solution -> true
  | None -> false

and solve_types (env: CheckerEnv.t)
                (equiv_vars: (string * string) list)
                (unknowns: string list)
                (t1:Type.t) (t2:Type.t)
    : soln =

  let t1' = reduce_type env (translate_type env [] t1) in
  let t2' = reduce_type env (translate_type env [] t2) in
  begin match t1', t2' with
    | TopLevelType _, _
    | _, TopLevelType _ ->
        failwith "TopLevelType in saturated type?"

    | SpecializedType _, _
    | _, SpecializedType _ ->
       raise_s [%message "Stuck specialized type?" ~t1:(t1': Typed.Type.t)
                                                   ~t2:(t2': Typed.Type.t)]
    | TypeName tv1, TypeName tv2 ->
        if type_vars_equal_under env equiv_vars tv1 tv2
        then Some (empty_constraints unknowns)
        else Some (single_constraint unknowns tv1 (TypeName tv2))

    | TypeName tv, typ ->
       if List.mem ~equal:(=) unknowns tv
       then Some (single_constraint unknowns tv typ)
       else None

    | Bool, Bool
    | String, String
    | Integer, Integer
    (* These false "equalities" should probably be handled by addding implicit
     * casts as described in sec. 8.9.2 of the p4-16 spec. *)
    | Integer, Int _
    | Int _, Integer
    | Integer, Bit _
    | Bit _, Integer
    | Error, Error
    | MatchKind, MatchKind
    | Void, Void ->
        Some (empty_constraints unknowns)

    | Bit { width = l}, Bit {width = r}
    | Int { width = l}, Int {width = r}
    | VarBit {width = l}, VarBit {width = r} ->
        if l = r
        then Some (empty_constraints unknowns)
        else None

    | Array {typ = lt; size = ls}, Array {typ = rt; size = rs} ->
       if ls = rs
       then solve_types env equiv_vars unknowns lt rt
       else None

    | Tuple {types = types1}, Tuple {types = types2} ->
       let solve_type_pair (t1, t2) =
         solve_types env equiv_vars unknowns t1 t2
       in
       solve_lists env unknowns ~f:solve_type_pair types1 types2

    | List {types = types1}, List {types = types2}
    | Tuple {types = types1}, List {types = types2} ->
       solve_types env equiv_vars unknowns
         (Tuple {types = types1}) (Tuple {types = types2})

    | Struct {fields}, List {types}
    | Header {fields}, List {types} ->
       let ok (struct_field, tuple_type: Typed.RecordType.field * Typed.Type.t) =
         solve_types env equiv_vars unknowns struct_field.typ tuple_type
       in
       solve_lists env unknowns ~f:ok fields types

    | Set ty1, Set ty2 ->
        solve_types env equiv_vars unknowns ty1 ty2

    | Header rec1, Header rec2
    | HeaderUnion rec1, HeaderUnion rec2
    | Struct rec1, Struct rec2 ->
        solve_record_type_equality env equiv_vars unknowns rec1 rec2

    | Enum enum1, Enum enum2 ->
        solve_enum_type_equality env equiv_vars unknowns enum1 enum2

    | Package pkg1, Package pkg2 ->
        solve_package_type_equality env equiv_vars unknowns pkg1 pkg2

    | Control ctrl1, Control ctrl2
    | Parser ctrl1, Parser ctrl2 ->
        solve_control_type_equality env equiv_vars unknowns ctrl1 ctrl2

    | Extern extern1, Extern extern2 ->
        solve_extern_type_equality env equiv_vars unknowns extern1 extern2

    | Action action1, Action action2 ->
        solve_action_type_equality env equiv_vars unknowns action1 action2

    | Function func1, Function func2 ->
        solve_function_type_equality env equiv_vars unknowns func1 func2

    | Table table1, Table table2 ->
       if table1.result_typ_name = table2.result_typ_name
       then Some (empty_constraints unknowns)
       else None

    (* We could replace this all with | _, _ -> false. I am writing it this way
     * because when I change Type.t I want Ocaml to warn me about missing match
     * cases. *)
    | Bool, _
    | String, _
    | Integer, _
    | Error, _
    | MatchKind, _
    | Void, _
    | Bit _, _
    | Int _, _
    | VarBit _, _
    | Array _, _
    | Tuple _, _
    | List _, _
    | Set _, _
    | Header _, _
    | HeaderUnion _, _
    | Struct _, _
    | Enum _, _
    | Control _, _
    | Parser _, _
    | Package _, _
    | Extern _, _
    | Action _, _
    | Function _, _
    | Table _, _ ->
      None
  end

(* Checks that a list of parameters is type equivalent.
 * True if equivalent, false otherwise.
 * Parameter names are ignored.
 * The order of parameters is significant. *)
and param_equality env p1s p2s =
  let open Parameter in
  let check_params = fun (par1,par2) ->
    if par1.direction <> par2.direction then false
    else type_equality env par1.typ par2.typ in
  eq_lists ~f:check_params p1s p2s

(* Checks that a list of constructor parameters is type equivalent.
 * True if equivalent, false otherwise.
 * Parameter names are ignored.
 * The order of parameters is significant. *)
and construct_param_equality env p1s p2s =
  let open ConstructParam in
  let check_params = fun (par1,par2) ->
    type_equality env par1.typ par2.typ in
  eq_lists ~f:check_params p1s p2s

and assert_same_type (env: CheckerEnv.t) info1 info2 (typ1: Type.t) (typ2: Type.t) =
  if type_equality env typ1 typ2
  then (typ1, typ2)
  else let info = Info.merge info1 info2 in
    raise_type_error info (Type_Difference (typ1, typ2))

and assert_type_equality env info (t1: Typed.Type.t) (t2: Typed.Type.t) : unit =
  let t1 = reduce_type env t1 in
  let t2 = reduce_type env t2 in
  if type_equality env t1 t2
  then ()
  else raise @@ Error.Type (info, Type_Difference (t1, t2))

and compile_time_known_expr (env: CheckerEnv.t) (expr: Prog.Expression.t) : bool =
  match compile_time_eval_expr env expr with
  | Some _ -> true
  | None -> false

and type_expression (env: CheckerEnv.t) (exp_info, exp: Expression.t)
    : Prog.Expression.t =
  let module E = Prog.Expression in
  let pre_expr : E.typed_t =
    match exp with
    | True ->
       { expr = E.True;
         typ = Bool;
         dir = Directionless }
    | False ->
       { expr = E.False;
         typ = Bool;
         dir = Directionless }
    | String s ->
       { expr = E.String s;
         typ = String;
         dir = Directionless }
    | Int i ->
       type_int i
    | Name name ->
       let typ, dir = CheckerEnv.find_type_of (snd name) env in
       { expr = E.Name name;
         typ = typ;
         dir = dir }
    | TopLevel name ->
       let typ, dir = CheckerEnv.find_type_of_toplevel (snd name) env in
       { expr = E.TopLevel name;
         typ = typ;
         dir = dir }
    | ArrayAccess { array; index } ->
       type_array_access env array index
    | BitStringAccess { bits; lo; hi } ->
       type_bit_string_access env bits lo hi
    | List { values } ->
       type_list env values
    | UnaryOp { op; arg } ->
       type_unary_op env op arg
    | BinaryOp { op; args } ->
       type_binary_op env op args
    | Cast { typ; expr } ->
       type_cast env typ expr
    | TypeMember { typ; name } ->
       type_type_member env typ name
    | ErrorMember name ->
       type_error_member env name
    | ExpressionMember { expr; name } ->
       type_expression_member env expr name
    | Ternary { cond; tru; fls } ->
       type_ternary env cond tru fls
    | FunctionCall { func; type_args; args } ->
       type_function_call env exp_info func type_args args
    | NamelessInstantiation { typ; args } ->
       type_nameless_instantiation env exp_info typ args
    | Mask { expr; mask } ->
       type_mask env expr mask
    | Range { lo; hi } ->
       type_range env lo hi
  in
  (exp_info, pre_expr)
  (*
  | FunctionCall { func; type_args; args } ->
     (type_function_call env exp_info func type_args args, Directionless)
  in
  (typ, dir, (Info.dummy, pre_exp))
   *)

and translate_direction (dir: Types.Direction.t option) : Typed.direction =
  match dir with
  | Some (_, In) -> In
  | Some (_, Out) -> Out
  | Some (_, InOut) -> InOut
  | None -> Directionless

and translate_type : CheckerEnv.t -> string list -> Types.Type.t -> Typed.Type.t =
  fun env vars typ ->
  let open Types.Type in
  let eval e =
    Eval.eval_expression (CheckerEnv.eval_env_of_t env) e
  in
  let get_int_from_bigint num =
    begin match Bigint.to_int num with
      | Some n -> n;
      | None -> failwith "numeric type parameter is too large"
    end in
  match snd typ with
  | Bool -> Bool
  | Error -> Error
  | Integer -> Integer
  | IntType e ->
    begin match snd (eval e) with
      | Value.VInt {v; _}
      | Value.VBit {v; _}
      | Value.VInteger v ->
         Int {width= get_int_from_bigint v}
      | _ -> failwith "int type param must evaluate to an int"
    end
  | BitType e ->
    begin match snd (eval e) with
      | Value.VInt {v; _}
      | Value.VBit {v; _}
      | Value.VInteger v ->
         Bit {width= get_int_from_bigint v}
      | _ -> failwith "bit type param must evaluate to an int"
    end
  | VarBit e ->
    begin match snd (eval e) with
      | Value.VInt {v; _}
      | Value.VBit {v; _}
      | Value.VInteger v ->
         VarBit {width= get_int_from_bigint v}
      | _ -> failwith "bit type param must evaluate to an int"
    end
  | TopLevelType ps -> TopLevelType (snd ps)
  | TypeName ps -> TypeName (snd ps)
  | SpecializedType {base; args} ->
      SpecializedType {base = (translate_type env vars base);
                       args = (List.map ~f:(translate_type env vars) args)}
  | HeaderStack {header=ht; size=e}
    -> let hdt = translate_type env vars ht in
    let len =
      begin match snd (eval e) with
      | Value.VInt {v; _}
      | Value.VBit {v; _}
      | Value.VInteger v ->
         get_int_from_bigint v
      | _ -> failwith "header stack size must be a number"
      end in
    Array {typ=hdt; size=len}
  | Tuple tlist ->
    Tuple {types = List.map ~f:(translate_type env vars) tlist}
  | Void -> Void
  | DontCare -> failwith "TODO: type inference"

and translate_type_opt (env: CheckerEnv.t) (vars : string list) (typ: Types.Type.t) : Typed.Type.t option =
  match snd typ with
  | DontCare -> None
  | _ -> Some (translate_type env vars typ)

(* Translates Types.Parameters to Typed.Parameters *)
and translate_parameters env vars params =
  let translate_parameter (info, param : Types.Parameter.t) : Typed.Parameter.t =
    { annotations = param.annotations;
      direction = translate_direction param.direction;
      typ = translate_type env vars param.typ;
      variable = param.variable }
  in
  List.map ~f:translate_parameter params

(* Translates Types.Parameters representing constructor parameters
 * to Typed.ConstructParams *)
and translate_construct_params env vars construct_params =
  let translate_parameter (info, param : Types.Parameter.t) : Typed.ConstructParam.t =
    if param.direction <> None
    then failwith "Constructor parameters must be directionless."
    else if List.length param.annotations > 0
    then failwith "Constructor parameters should not be annotated."
    else if param.opt_value <> None
    then failwith "Constructor parameters should not have an optional value."
    else { typ = translate_type env vars param.typ;
           name = snd param.variable }
  in
  List.map ~f:translate_parameter construct_params

and construct_param_as_param (construct_param: ConstructParam.t) : Parameter.t =
  { variable = Info.dummy, construct_param.name;
    typ = construct_param.typ;
    direction = Directionless;
    annotations = [] }
  
and control_param_as_param (control_param: ConstructParam.t) : Parameter.t =
  { variable = Info.dummy, control_param.name;
    typ = control_param.typ;
    direction = In;
    annotations = [] }
  
and expr_of_arg (arg: Argument.t): Expression.t option =
  match snd arg with
  | Missing -> None
  | KeyValue { value; _ }
  | Expression { value } -> Some value

(* Returns true if type typ is a well-formed type
*)
and is_well_formed_type env (typ: Typed.Type.t) : bool =
  match typ with

  (* Base types *)
  | Bool
  | String
  | Integer
  | Int _
  | Bit _
  | VarBit _
  | Error
  | MatchKind
  | Void -> true

  (* Recursive types *)
  | Array {typ=t; _} -> is_well_formed_type env t
  | Tuple {types= typs}
  | List {types= typs} -> List.for_all ~f:(is_well_formed_type env) typs
  | Set t -> is_well_formed_type env t
  | Enum {typ=maybe_typ; _} ->
    begin match maybe_typ with
    | None -> true
    | Some t ->  is_well_formed_type env t
    end
  | Header {fields=fields}
  | HeaderUnion {fields=fields}
  | Struct {fields=fields} ->
    let open RecordType in
    List.for_all ~f:(fun field -> field.typ |> is_well_formed_type env) fields
  | Action { data_params=dps; ctrl_params=cps } ->
    let res1 : bool = (are_param_types_well_formed env dps) in
    let res2 : bool = (are_construct_params_types_well_formed env cps) in
    res1 && res2

  (* Type names *)
  | TypeName name
  | Table {result_typ_name=name} ->
    begin match CheckerEnv.resolve_type_name_opt name env with
    | None -> false
    | Some _ -> true (* Unsure of what to do in this case *)
    end
  | TopLevelType name ->
    begin match CheckerEnv.resolve_type_name_toplevel_opt name env with
    | None -> false
    | Some _ -> true (* Unsure of what to do in this case *)
    end

  (* Polymorphic types *)
  | Function {type_params=tps; parameters=ps; return=rt} ->
    let env = CheckerEnv.insert_type_vars tps env in
    are_param_types_well_formed env ps && is_well_formed_type env rt
  | Extern {type_params=tps; methods=methods} ->
    let env = CheckerEnv.insert_type_vars tps env in
    let open ExternType in
    let folder (env,result) m =
      if is_well_formed_type env (Type.Function m.typ) then
      (CheckerEnv.insert_type_of m.name (Type.Function m.typ) env,result)
      else (env,false) in
    List.fold_left ~f:folder ~init:(env,true) methods |> snd
  | Parser {type_params=tps; parameters=ps}
  | Control {type_params=tps; parameters=ps} ->
    let env = CheckerEnv.insert_type_vars tps env in
    are_param_types_well_formed env ps
  | Package {type_params=tps; parameters=cps} ->
    let env = CheckerEnv.insert_type_vars tps env in
    are_construct_params_types_well_formed  env cps

  (* Type Application *)
  | SpecializedType {base=base_typ; args=typ_args} ->
    is_well_formed_type env base_typ
    && List.for_all ~f:(is_well_formed_type env) typ_args

and are_param_types_well_formed env (params:Parameter.t list) : bool =
  let open Parameter in
  let check param = is_well_formed_type env param.typ in
  List.for_all ~f:check params


and are_construct_params_types_well_formed env (construct_params:ConstructParam.t list) : bool =
  let open ConstructParam in
  let check param = is_well_formed_type env param.typ in
  List.for_all ~f:check construct_params


and type_int (val_info, value) : Prog.Expression.typed_t =
  let open P4Int in
  { expr = Int (val_info, value);
    dir = Directionless;
    typ = match value.width_signed with
          | None -> Type.Integer
          | Some (width, true) -> Type.Int { width }
          | Some (width, false) -> Type.Bit { width } }

(* Section 8.15
 * ------------
 *
 * Δ, T, Γ |- a : t[size]      Δ, T, Γ |- i : u, where numeric(u)
 * ----------------------------------------------------------
 *                Δ, T, Γ |- a[i] : t
 *
 * Some architectures may further require ctk(i).
 *)
and type_array_access env (array: Types.Expression.t) index : Prog.Expression.typed_t =
  let array_typed = type_expression env array in
  let array_typ = (snd array_typed).typ in
  let idx_typed = type_expression env index in
  let element_typ = (assert_array (info array) array_typ).typ in
  assert_numeric (info index) (snd idx_typed).typ |> ignore;
  { expr = ArrayAccess { array = array_typed; index = idx_typed };
    typ = element_typ;
    dir = (snd array_typed).dir }

and is_numeric (typ: Typed.Type.t) : bool =
  match typ with
  | Int _
  | Bit _
  | VarBit _
  | Integer -> true
  | _ -> false

(* Section 8.5
 * -----------
 *
 * Δ, T, Γ |- b : bit<n>
 * Δ, T, Γ |- l : t, where numeric(t)
 * Δ, T, Γ |- m : u, where numeric(u)
 * ctk(l) /\ 0 <= l < width
 * ctk(m) /\ l <= m < width
 * -------------------------------
 * Δ, T, Γ |- b[m:l] : bit<m - l>
 *)
and type_bit_string_access env bits lo hi : Prog.Expression.typed_t =
  let bits_typed = type_expression env bits in
  match (snd bits_typed).typ with
  | Bit { width } ->
     let lo_typed = type_expression env lo in
     let typ_lo = saturate_type env (snd lo_typed).typ in
     let hi_typed = type_expression env hi in
     let typ_hi = saturate_type env (snd hi_typed).typ in
     assert (is_numeric typ_lo);
     assert (is_numeric typ_hi);
     let val_lo = compile_time_eval_bigint env lo_typed in
     let val_hi = compile_time_eval_bigint env hi_typed in
     let big_width = Bigint.of_int width in
     (* Bounds checking *)
     assert (Bigint.(<=) Bigint.zero val_lo);
     assert (Bigint.(<) val_lo big_width);
     assert (Bigint.(<=) val_lo val_hi);
     assert (Bigint.(<) val_hi big_width);
     let diff = Bigint.(-) val_hi val_lo |> Bigint.to_int_exn |> (+) 1 in
     { expr = BitStringAccess { bits = bits_typed;
                                lo = val_lo;
                                hi = val_hi };
       typ = Bit { width = diff };
       dir = (snd bits_typed).dir }
  | typ ->
     raise_s [%message "expected bit type, got" ~typ:(typ: Typed.Type.t)]

(* Section 8.11
 * ------------
 *
 *      1 <= i <= n; Δ, T, Γ |- xi : ti
 * ------------------------------------------
 * Δ, T, Γ |- { x1, ..., xn } : (t1, ..., tn)
 *
 *)
and type_list env values : Prog.Expression.typed_t =
  let typed_exprs = List.map ~f:(type_expression env) values in
  let types = List.map ~f:(fun e -> (snd e).typ) typed_exprs in
  { expr = List { values = typed_exprs };
    typ = Type.List { types };
    dir = Directionless }

(* Sections 8.5-8.8
 * ----------------
 *
 * Logical Negation
 *
 * Δ, T, Γ |- e : bool
 * --------------------
 * Δ, T, Γ |- !e : bool
 *
 *
 * Bitwise Complement
 *
 * Δ, T, Γ |- e : bit<n>
 * --------------------
 * Δ, T, Γ |- ~e : bit<n>
 *
 *
 * Unary Minus
 *
 * Δ, T, Γ |- e : int
 * ------------------
 * Δ, T, Γ |- -e : int
 *
 *
 * Δ, T, Γ |- e : int<n>
 * ----------------------
 * Δ, T, Γ |- -e : int<n>
 *)
and type_unary_op env op arg =
  let arg_typed = type_expression env arg in
  let arg_typ = (snd arg_typed).typ in
  begin match snd op with
  | Not    -> assert_bool (info arg) arg_typ |> ignore
  | BitNot -> assert_bit (info arg) arg_typ |> ignore
  | UMinus -> assert_numeric (info arg) arg_typ |> ignore
  end;
  { expr = UnaryOp { op = op;
                     arg = arg_typed };
    typ = arg_typ;
    dir = (snd arg_typed).dir }

(* Sections 8.5-8.8
 *
 * Let eq_bop be in the set {==, !=}.
 *
 * Let bool_bop be in the set {&&, ||}.
 *
 * Let comp_bop be in the set {==, !=, <, >, <=, >=}.
 *
 * Let arith_bop be in the set {+, -, *}.
 *
 * Let sat_bop be in the set {|+|, |-|}
 *
 * Let bit_bop be in the set {&, |, ~, ^}
 *
 * Let shift be in the set {<<, >>}.
 *
 * Let div be in the set {%, /}.
 *
 * TODO(ryan): fix use of implicit cast here to remove it from
 * individual rules
 *
 * Equality operations:
 * Δ, T, Γ |- e1 : t1      Δ, T, Γ |- e2 : t2
 * t1 = t2 = t or t = implicit_cast(t1,t2)
 * ------------------------------------------------
 * Δ, T, Γ |- e1 bool_bop e2 : t
 *
 * Binary Boolean operations:
 * Δ, T, Γ |- e1 : bool       Δ, T, Γ |- e2 : bool
 * ------------------------------------------------
 * Δ, T, Γ |- e1 bool_bop e2 : bool
 *
 * Comparison operators:
 * Δ, T, Γ |- e1 : t1          numeric(t1)
 * Δ, T, Γ |- e2 : t2          numeric(t2)
 * implicit_cast(t1, t2)
 * ------------------------------------------------
 * Δ, T, Γ |- e1 comp_bop e2 : bool
 *
 * Division operations:
 * Δ, T, Γ |- e1 : int CTK      Δ, T, Γ |- e2 : int CTK
 * -----------------------------------------------------
 * Δ, T, Γ |- e1 div e2 : int
 *
 * Binary arithmetic operations:
 * Δ, T, Γ |- e1 : t1          numeric(t1)
 * Δ, T, Γ |- e2 : t2          numeric(t2)
 * ------------------------------------------------
 * Δ, T, Γ |- e1 arith_bop e2 : implicit_cast(t1, t2)
 *
 * Binary arithemetic operations with Saturating:
 * Δ, T, Γ |- e1 : t1          numeric(t1)
 * Δ, T, Γ |- e2 : t2          numeric(t2)
 * implicit_cast(t1, t2) = bit<w> or implicit_cast(t1, t2) = int<w>
 * -----------------------------------------------------------------
 * Δ, T, Γ |- e1 sat_bop e2 : implicit_cast(t1, t2)
 *
 * Binary bitwise operations:
 * Δ, T, Γ |- e1 : t1          numeric(t1)
 * Δ, T, Γ |- e2 : t2          numeric(t2)
 * implicit_cast(t1, t2) = bit<w>
 * ----------------------------------------
 * Δ, T, Γ |- e1 bit_bop e2 : bit<w>
 *
 * Shift operators:
 * Δ, T, Γ |- e1 : t1     numeric(t1)
 * Δ, T, Γ |- e2 : t2     t2 = int or t2 = bit<w>     e2 > 0
 * ----------------------------------------------------------
 * Δ, T, Γ |- e1 shift e2 : t1
 *
 * Bitwise concatentation:
* Δ, T, Γ |- e1 : t1          numeric(t1)
* Δ, T, Γ |- e2 : t2          numeric(t2)
* t1 = bit<w1> and implicit_cast(t1,t2) = bit<w1>, w2 = w1 or
* t2 = bit<w2> and implicit_cast(t1,t2) = bit<w2>, w1 = w2 or
* t1 = bit<w1> and t2 = bit<w2>
* -----------------------------------------------------------
* Δ, T, Γ |- e1 ++ e2 : bit<w1 + w2>
*
*)
and implicit_cast env l r : Typed.Type.t option * Typed.Type.t option =
  let open Prog.Expression in
  match (snd l).typ, (snd r).typ with
  | Bit { width }, Integer ->
     None, Some (Bit { width })
  | Integer, Bit { width } ->
     Some (Bit { width }), None
  | Int { width }, Integer ->
     None, Some (Int { width })
  | Integer, Int { width } ->
     Some (Int { width }), None
  | _, _ ->
     None, None

and coerce_binary_op_args env l r =
  (* Implicit integer casts as per section 8.9.2
   *
   * Let implicit_cast(t1,t2) be defined as follows to describe
   * p4's impliciting casting behavior on operands in binary expressions:
   *
   * implicit_cast(bit<w>, int CTK)   = bit<w>                 (cast RHS)
   * implicit_cast(int CTK, bit<w>)   = bit<w>                 (cast LHS)
   * implicit_cast(int<w>, int CTK)   = int<w>                 (cast RHS)
   * implicit_cast(int CTK, int<w>)   = int<w>                 (cast LHS)
   * implicit_cast(_, _)              = None                    (no cast)
   *
   *)
  let l_typed = type_expression env l in
  let r_typed = type_expression env r in
  let cast typ (expr_info, expr : Prog.Expression.t) : Prog.Expression.t =
    expr_info,
    { expr = Cast { typ = typ;
                    expr = (expr_info, expr) };
      typ = typ;
      dir = expr.dir }
  in
  let cast_opt = function
    | Some typ -> cast typ
    | None -> fun e -> e
  in
  let cast_type_l, cast_type_r = implicit_cast env l_typed r_typed in
  cast_opt cast_type_l l_typed, cast_opt cast_type_r r_typed

(* TODO: Checking if two values of this type be compared for equality
 * (==) or inequality (!=).
 *)
and type_has_equality_tests env (typ: Typed.Type.t) =
  match typ with
  | Bool
  | String
  | Integer
  | Int _
  | Bit _
  | VarBit _
  | Error
  | MatchKind
  | Void ->
     true
  | Array { typ; _ }
  | Set typ ->
     type_has_equality_tests env typ
  | Tuple { types }
  | List { types } ->
     List.for_all ~f:(type_has_equality_tests env) types
  | Header { fields }
  | HeaderUnion { fields }
  | Struct { fields } ->
     List.for_all ~f:(fun field -> type_has_equality_tests env field.typ) fields
  | Enum { typ; _ } ->
     begin match typ with
     | Some typ -> type_has_equality_tests env typ
     | None -> true
     end
  | TypeName name
  | TopLevelType name ->
     failwith "type name?"
  | _ ->
     false

and type_binary_op env (op_info, op) (l, r) : Prog.Expression.typed_t =
  let open Op in
  let open Typed.Type in
  let typed_l, typed_r = coerce_binary_op_args env l r in
  let l_typ = (snd typed_l).typ in
  let r_typ = (snd typed_r).typ in
  let dir =
    match (snd typed_l).dir, (snd typed_r).dir with
    | In, In -> In
    | _ -> Directionless
  in
  let typ =
    match op with
    | And | Or ->
       begin match l_typ, r_typ with
       | Bool, Bool -> Bool
       | Bool, r -> raise_mismatch (op_info) "Operand must be a bool" r
       | l, r -> raise_mismatch (op_info) "Operand must be a bool" l
       end
    (* Basic numeric operations are defined on both arbitrary and fixed-width integers *)
    | Plus | Minus | Mul ->
       begin match l_typ, r_typ with
       | Integer, Integer -> Integer
       | Bit { width = l }, Bit { width = r } when l = r -> Bit { width = l }
       | Int { width = l }, Int { width = r } when l = r -> Int { width = l }
       | _, _ -> failwith "this binop unimplemented" (* TODO: better error message here *)
       end
    | Eq | NotEq ->
       if type_equality env l_typ r_typ
       then if type_has_equality_tests env l_typ
            then Type.Bool
            else failwith "bad error message: type doesn't have equality tests (== and !=)"
       else raise_type_error op_info (Type_Difference (l_typ, r_typ))
    (* Saturating operators are only defined on finite-width signed or unsigned integers *)
    | PlusSat | MinusSat ->
       begin match l_typ, r_typ with
       | Bit { width = l }, Bit { width = r } when l = r ->
          Bit { width = l }
       | Int { width = l }, Int { width = r } when l = r ->
          Int { width = l }
       | Bit _, r | Int _, r ->
          raise_mismatch (op_info) "Operand must have type int<w> or bit<w>" r
       | l, r ->
          raise_mismatch (op_info) "Operand must have type int<w> or bit<w>" l
       end
    (* Bitwise operators are only defined on bitstrings of the same width *)
    | BitAnd | BitXor | BitOr ->
       begin match l_typ, r_typ with
       | Bit { width = l }, Bit { width = r } when l = r -> Bit { width = l }
       | Bit { width = _ }, _ -> raise_mismatch (info r) "unsigned int" r_typ
       | _, _ -> raise_mismatch (info l) "unsigned int" l_typ
       end
    (* Bitstring concatentation is defined on any two bitstrings *)
    | PlusPlus ->
       begin match l_typ, r_typ with
       | Bit { width = l }, Bit { width = r } -> Bit { width = l + r }
       | Bit { width = _ }, _ -> raise_mismatch (info r) "unsigned int" r_typ
       | _, _ -> raise_mismatch (info l) "unsigned int" l_typ
       end
    (* Comparison is defined on both arbitrary and fixed-width integers *)
    | Le | Ge | Lt | Gt ->
       begin match l_typ, r_typ with
       | Integer, Integer -> Bool
       | Bit { width = l }, Bit { width = r } when l = r -> Bool
       | Int { width = l }, Int { width = r } when l = r -> Bool
       | _, _ -> raise_type_error op_info (Type_Difference (l_typ, r_typ))
       end
    (* Division is only defined on compile-time known arbitrary-precision positive integers *)
    | Div | Mod ->
       begin match l_typ, r_typ with
       | Integer, Integer -> Integer (* TODO: must be compile-time-known? *)
       | Integer, _ -> raise_mismatch (info r) "arbitrary precision integer" r_typ
       | _, _ -> raise_mismatch (info l) "arbitrary precision integer" l_typ
       end
    (* Left and Right Shifts
     * Shift operators:
     * Δ, T, Γ |- e1 : t1     numeric(t1)
     * Δ, T, Γ |- e2 : t2     t2 = int or t2 = bit<w>     e2 > 0
     * ----------------------------------------------------------
     * Δ, T, Γ |- e1 shift e2 : t1
     * As of yet we assume that e2 > 0, but this must be updated.
     *)
    | Shl | Shr ->
       if is_numeric l_typ
       then match r_typ with
            |  Bit _ -> l_typ
            |  Integer -> l_typ (* TODO check the value of the rhs is non negative *)
            | _ -> failwith "Shift operands have improper types" (*TODO better error handling*)
       else failwith "can only shift numbers"
  in
  { expr = BinaryOp { op = (op_info, op); args = (typed_l, typed_r) };
    typ = typ;
    dir = dir }

and cast_ok original_type new_type =
  (* TODO *)
  match original_type, new_type with
  | _ -> true

(* Section 8.9 *)
and type_cast env typ expr : Prog.Expression.typed_t =
  let expr_typed = type_expression env expr in
  let expr_type = saturate_type env (snd expr_typed).typ in
  let new_type = translate_type env [] typ in
  if cast_ok expr_type (saturate_type env new_type)
  then { (snd expr_typed) with typ = new_type }
  else raise_s [%message "illegal explicit cast"
                   ~old_type:(expr_type: Typed.Type.t)
                   ~new_type:(new_type: Typed.Type.t)]

(* ? *)
and type_type_member env typ name : Prog.Expression.typed_t =
  let open Core in
  let typ = translate_type env [] typ in
  let full_typ = saturate_type env typ
  in
  let out_typ = 
    match full_typ with
    | Enum { typ = carrier; members } ->
       if List.mem ~equal:(fun x y -> x = y) members (snd name)
       then match carrier with
            | None -> typ
            | Some carrier -> carrier
       else raise_s [%message "enum has no such member"
                        ~enum:(full_typ: Typed.Type.t)
                        ~member:(snd name)]
    | _ -> raise_s [%message "type_type_member unimplemented"
                       ~typ:(full_typ: Typed.Type.t)
                       ~name:(snd name)]
  in
  { expr = TypeMember { typ = typ;
                        name = name };
    typ = out_typ;
    dir = Directionless }

(* Section 8.2
 * -----------
 *
 *       (e, error) ∈ T
 * --------------------------
 * Δ, T, Γ |- error.e : error
 *
 *)
and type_error_member env name : Prog.Expression.typed_t =
  let (e, _) = CheckerEnv.find_type_of ("error." ^ (snd name)) env in
  if e <> Type.Error then failwith "Error member not an error?";
  { expr = ErrorMember name;
    typ = Type.Error;
    dir = Directionless }

and header_methods typ =
  let fake_fields: RecordType.field list =
    [{name = "isValid";
      typ = Function {type_params = []; parameters = []; return = Bool}}]
  in
  match typ with
  | Type.Header { fields } -> fake_fields
  | _ -> []

and type_expression_member_builtin env info typ name : Typed.Type.t =
  let open Typed.Type in
  let fail () =
    raise_unfound_member info (snd name) in
  match typ with
  | Control { type_params = []; parameters = ps }
  | Parser { type_params = []; parameters = ps } ->
     begin match snd name with
     | "apply" ->
        Function { type_params = [];
                   parameters = ps;
                   return = Void }
     | _ -> fail ()
     end
  | Table { result_typ_name } ->
     begin match snd name with
     | "apply" ->
        Function { type_params = []; parameters = [];
                   return = TypeName result_typ_name }
     | _ -> fail ()
     end
  | Header { fields } ->
     begin match snd name with
     | "isValid" ->
        Function { type_params = []; parameters = []; return = Bool }
     | "setValid"
     | "setInvalid" ->
        Function { type_params = []; parameters = []; return = Void }
     | _ -> fail ()
     end
  | Array { typ; _ } ->
     let idx_typ = Bit { width = 32 } in
     begin match snd name with
     | "size"
     | "nextIndex"
     | "lastIndex" ->
        idx_typ
     | "next"
     | "last" ->
        typ
     | "push_front"
     | "pop_front" ->
        Function { type_params = [];
                   parameters = [{ variable = Info.dummy, "count";
                                   typ = Integer;
                                   direction = Directionless;
                                   annotations = [] }];
                   return = Void }
     | _ -> fail ()
     end
  | HeaderUnion { fields } ->
     begin match snd name with
     | "isValid" ->
        Function { type_params = []; parameters = []; return = Bool }
     | _ -> fail ()
     end
  | _ -> fail ()

(* Sections 6.6, 8.14 *)
and type_expression_member env expr name : Prog.Expression.typed_t =
  let typed_expr = type_expression env expr in
  let expr_typ = reduce_type env (snd typed_expr).typ in
  let open RecordType in
  let methods = header_methods (snd typed_expr).typ in
  let typ = 
    match expr_typ with
    | Header {fields=fs}
    | HeaderUnion {fields=fs}
    | Struct {fields=fs} ->
       let fs = fs @ methods in
       let matches f = f.name = snd name in
       begin match List.find ~f:matches fs with
       | Some field -> field.typ
       | None -> type_expression_member_builtin env (info expr) expr_typ name
       end
    | Extern {methods; _} ->
       let open ExternType in
       let matches m = m.name = snd name in
       begin match List.find ~f:matches methods with
       | Some m -> Type.Function m.typ
       | None -> type_expression_member_builtin env (info expr) expr_typ name
       end
    | _ -> type_expression_member_builtin env (info expr) expr_typ name
  in
  { expr = ExpressionMember { expr = typed_expr;
                              name = name };
    typ = typ;
    dir = Directionless }

(* Section 8.4.1
 * -------------
 *
 * Δ, T, Γ |- cond : bool    Δ, T, Γ |- tru : t    Δ, T, Γ |- fls : t;
 * -------------------------------------------------------------------
 *              Δ, T, Γ |- cond ? tru : fls : t
 *)
and type_ternary env cond tru fls : Prog.Expression.typed_t =
  let cond_typed = type_expression env cond in
  assert_bool (info cond) (snd cond_typed).typ |> ignore;
  let fls_typed = type_expression env fls in
  let tru_typed = type_expression env tru in
  assert_same_type env (info tru) (info fls) (snd tru_typed).typ (snd fls_typed).typ |> ignore;
  match (snd tru_typed).typ with
  | Type.Integer ->
     (* TODO this is allowed if cond is compile-time known *)
     failwith "Conditional expressions may not have arbitrary width integer type"
  | t ->
     { expr = Ternary { cond = cond_typed; tru = tru_typed; fls = fls_typed };
       typ = t;
       dir = Directionless }

and match_params_to_args call_site_info params args : (Prog.TypeParameter.t * Expression.t option) list =
  let rec get_mode mode (args: Types.Argument.pre_t list) =
    match mode, args with
    | None, Expression { value } :: args
    | Some `Positional, Expression { value } :: args ->
       get_mode (Some `Positional) args
    | None, Missing :: args
    | Some `Positional, Missing :: args ->
       get_mode (Some `Positional) args
    | None, KeyValue { key; value } :: args
    | Some `Named, KeyValue { key; value } :: args ->
       get_mode (Some `Named) args
    | m, [] -> m
    | _ -> raise_s [%message "mixed positional and named arguments at call site"
                       ~info:(call_site_info: Info.t)]
  in
  let args = List.map ~f:snd args in
  match get_mode None args with
  | None ->
     begin match params with
     | [] -> []
     | _ -> raise_s [%message "not enough arguments supplied" ~info:(call_site_info: Info.t)]
     end
  | Some `Positional ->
     match_positional_args_to_params call_site_info params args
  | Some `Named ->
     match_named_args_to_params call_site_info params args

and match_params_to_args' call_site_info params args : (Typed.Parameter.t * Expression.t option) list =
  let add_opt (param: Typed.Parameter.t) : Prog.TypeParameter.t =
    (Info.dummy, 
     { annotations = param.annotations;
       direction = param.direction; 
       typ = param.typ;
       variable = param.variable;
       opt_value = None })
  in
  let remove_opt ((_, param): Prog.TypeParameter.t) : Typed.Parameter.t =
    { annotations = param.annotations;
      direction = param.direction; 
      typ = param.typ;
      variable = param.variable }
  in
  let params' = List.map ~f:add_opt params in
  let pairs = match_params_to_args call_site_info params' args in
  List.map ~f:(fun (param, arg) -> remove_opt param, arg) pairs

and match_positional_args_to_params call_site_info params args =
  let open Types.Argument in
  match List.zip params args with
  | Ok matches ->
     let conv (param, arg) =
       match arg with
       | Expression { value } -> param, Some value
       | Missing -> param, None
       | _ -> failwith "expected positional argument"
     in
     List.map ~f:conv matches
  | Unequal_lengths ->
     raise_s [%message "wrong number of arguments provided at call site"
                 ~info:(call_site_info: Info.t)
                 ~args:(args : Types.Argument.pre_t list)]

     
and match_named_args_to_params call_site_info (params: Prog.TypeParameter.t list) args =
  let open Types.Argument in
  let open Prog.TypeParameter in
  match params with
  | p :: params ->
     let right_arg = function
       | KeyValue { key; value } ->
          if snd (snd p).variable = snd key
          then Some value
          else None
       | _ -> None
     in
     let maybe_arg_for_p, other_args =
       Util.find_map_and_drop ~f:right_arg args
     in
     begin match maybe_arg_for_p with
     | Some arg_for_p ->
        (p, Some arg_for_p) :: match_named_args_to_params call_site_info params other_args
     | None ->
        raise_s [%message "parameter has no matching argument"
                    ~call_site:(call_site_info: Info.t)
                    ~param:(p: Prog.TypeParameter.t)]
     end
  | [] ->
     match args with
     | [] -> []
     | a :: rest ->
        raise_s [%message "too many arguments supplied at call site"
                    ~info:(call_site_info: Info.t)
                    ~unused_args:(args : Types.Argument.pre_t list)]
     
and check_direction env dir expr expr_dir =
  match dir with
  | Directionless
  | In -> ()
  | Out
  | InOut ->
     if not @@ is_lvalue expr
     then raise_s [%message "expected l-value, got expr:" ~expr:(expr: Expression.t)];
     if expr_dir = In
     then raise_s [%message "in parameter passed as out parameter" ~expr:(expr: Expression.t)]

and find_extern_methods env func : (FunctionType.t list) option =
  match snd func with
  | Expression.ExpressionMember { expr; name } ->
     begin match reduce_type env @@ (snd (type_expression env expr)).typ with
     | Extern e ->
        let methods = List.filter ~f:(fun m -> m.name = snd name) e.methods in
        Some (List.map ~f:(fun m -> m.typ) methods)
     | _ -> None
     end
  | _ -> None

and resolve_extern_overload env method_types args =
  let works (method_type: FunctionType.t) =
    try match_params_to_args' Info.dummy method_type.parameters args |> ignore;
        true
    with _ -> false
  in
  Typed.Type.Function (List.find_exn ~f:works method_types)

(* Section 8.17: Typing Function Calls *)
and type_param_arg env call_info (param, expr: Typed.Parameter.t * Expression.t option) =
  match expr with
  | Some expr ->
     let info, typed_arg = type_expression env expr in
     check_direction env param.direction expr typed_arg.dir;
     assert_type_equality env call_info typed_arg.typ param.typ
  | None ->
     if param.direction <> Out
     then raise_s [%message "don't care argument (underscore) provided for non-out parameter"
                      ~call_site:(call_info: Info.t)
                      ~param:(snd param.variable)]

and type_function_call env call_info func type_args args : Prog.Expression.typed_t =
  let func_typed = type_expression env func in
  let func_type =
    match find_extern_methods env func with
    | Some method_types ->
       resolve_extern_overload env method_types args
    | None ->
       (snd func_typed).typ
  in
  let func_typed = (fst func_typed, { (snd func_typed) with typ = func_type }) in
  let type_params, params, return_type =
    match func_type with
    | Function { type_params; parameters; return } ->
       type_params, parameters, return
    | Action { data_params; ctrl_params } ->
       let params =
         data_params @ List.map ~f:control_param_as_param ctrl_params
       in
       [], params, Type.Void
    | _ ->
       raise_s [%message "don't know how to typecheck function call with function"
                   ~fn:(func: Types.Expression.t)
                   ~fn_type:(func_type: Typed.Type.t)]
  in
  let type_args = List.map ~f:(translate_type_opt env []) type_args in
  let params_args = match_params_to_args' (fst func) params args in
  let type_params_args =
    match List.zip type_params type_args with
    | Ok v -> v
    | Unequal_lengths ->
       match type_args with
       | [] -> List.map ~f:(fun v -> v, None) type_params
       | _ -> failwith "mismatch in type arguments"
  in
  let type_params_args =
    infer_type_arguments env return_type type_params_args params_args type_params_args
  in
  let env = CheckerEnv.insert_types type_params_args env in
  List.iter ~f:(type_param_arg env call_info) params_args;
  let out_type_args = List.map ~f:snd type_params_args in
  let out_args = List.map ~f:(fun (_, arg) -> option_map (type_expression env) arg)
                   params_args in
  let typ = saturate_type env return_type in
  let call = Prog.Expression.FunctionCall { func = func_typed;
                                            type_args = out_type_args;
                                            args = out_args }
  in
  { expr = call; typ = typ; dir = Directionless }

and prog_params_to_typed_params ps = failwith "unimplemented"

and select_constructor_params env info methods args =
  let matching_constructor (proto: Prog.MethodPrototype.t) =
    match snd proto with
    | Constructor { params; _ } ->
       let params' = prog_params_to_typed_params params in
       begin try
         let _ = match_params_to_args info params' args in
         true
         with _ -> false
       end
    | Method _ -> false
    | AbstractMethod _ -> false
  in
  match List.find ~f:matching_constructor methods with
  | Some (_, Constructor { params; _ }) ->
     let params' = prog_params_to_typed_params params in
     Some (match_params_to_args info params' args)
  | _ -> None

and get_decl_type_params (decl : Prog.Declaration.t) : P4String.t list =
  let open Prog.Declaration in
  match snd decl with
  | ExternObject { type_params; _ }
  | Parser { type_params; _ }
  | Control { type_params; _ } ->
     type_params
  | _ ->
     []

and get_decl_constructor_params env info (decl : Prog.Declaration.t) args =
  let open Prog.Declaration in
  let params_maybe_args =
    match snd decl with
    | Parser { constructor_params; _ }
    | Control { constructor_params; _ } ->
       Some (match_params_to_args info constructor_params args)
    | ExternObject { methods; _ } ->
       select_constructor_params env info methods args
    | _ ->
       None
  in
  let f (param, arg) = 
    match arg with
    | Some a -> (param, a)
    | None -> raise_s [%message "missing parameter?"
                          ~param:(param: Prog.TypeParameter.t)
                          ~call_site:(info: Info.t)]
  in
  option_map (List.map ~f) params_maybe_args

and type_constructor_invocation env info decl type_args args : Prog.Expression.t list * Typed.Type.t =
  let open Types.Declaration in
  let type_args = List.map ~f:(translate_type_opt env []) type_args in
  let type_params = List.map ~f:snd (get_decl_type_params decl) in
  let constructor_params = get_decl_constructor_params env info decl args in
  check_constructor_invocation env type_params constructor_params type_args args;
  let type_args = solve_constructor_invocation env type_params constructor_params type_args args in
  ignore type_args;
  failwith "unimplemented"

(* Section 14.1 *)
and type_nameless_instantiation env info typ args =
  let open Prog.Expression in
  match snd typ with
  | SpecializedType { base; args = type_args } ->
     begin match snd base with
     | TypeName (_, decl_name) ->
        let decl = CheckerEnv.find_decl decl_name env in
        let out_args, out_typ = type_constructor_invocation env info decl type_args args in
        let inst = NamelessInstantiation { typ = translate_type env [] typ;
                                           args = out_args }
        in
        { expr = inst;
          typ = out_typ;
          dir = Directionless }
     | _ ->
        raise_s [%message "don't know how to instantiate this type"
                    ~typ:(typ: Types.Type.t)]
     end
  | TypeName tn ->
     let typ = fst typ, Types.Type.SpecializedType { base = typ; args = [] } in
     type_nameless_instantiation env info typ args
  | _ ->
     raise_s [%message "don't know how to instantiate this type"
                 ~typ:(typ: Types.Type.t)]

(* Section 8.12.3 *)
and type_mask env expr mask : Prog.Expression.typed_t =
  let expr_typed = type_expression env expr in
  let mask_typed = type_expression env mask in
  let res_typ : Typed.Type.t =
    match (snd expr_typed).typ, (snd mask_typed).typ with
    | Bit { width }, Integer
    | Integer, Bit { width } ->
       Bit { width }
    | Integer, Integer ->
       Integer
    | l_typ, r_typ -> failwith "bad type for mask operation &&&"
  in
  { expr = Mask { expr = expr_typed; mask = mask_typed };
    typ = Type.Set res_typ;
    dir = Directionless }

(* Section 8.12.4 *)
and type_range env lo hi : Prog.Expression.typed_t =
  let lo_typed = type_expression env lo in
  let hi_typed = type_expression env hi in
  let typ : Typed.Type.t = 
    match (snd lo_typed).typ, (snd hi_typed).typ with
    | Bit { width = l }, Bit { width = r } when l = r ->
       Bit { width = l}
    | Int { width = l }, Int { width = r } when l = r ->
       Int { width = l }
    (* TODO: add pretty-printer and [to_string] for Typed module *)
    | Bit { width }, hi_typ ->
       raise_mismatch (info hi) ("bit<" ^ (string_of_int width) ^ ">") hi_typ
    | Int { width }, hi_typ ->
       raise_mismatch (info hi) ("int<" ^ (string_of_int width) ^ ">") hi_typ
    | lo_typ, _ -> raise_mismatch (Info.merge (info lo) (info hi)) "int or bit" lo_typ
  in
  { expr = Range { lo = lo_typed; hi = hi_typed };
    typ = Set typ;
    dir = Directionless }

and type_statement (env: CheckerEnv.t) (stm: Statement.t) : (Prog.Statement.t * CheckerEnv.t) =
  let open Prog.Statement in
  let typed_stm, env' =
    match snd stm with
    | MethodCall { func; type_args; args } ->
       type_method_call env (fst stm) func type_args args
    | Assignment { lhs; rhs } ->
       type_assignment env lhs rhs
    | DirectApplication { typ; args } ->
       type_direct_application env typ args
    | Conditional { cond; tru; fls } ->
       type_conditional env cond tru fls
    | BlockStatement { block } ->
       type_block_statement env block
    | Exit ->
       { stmt = Exit;
         typ = StmType.Void },
       env
    | EmptyStatement ->
       { stmt = EmptyStatement;
         typ = StmType.Unit },
       env
    | Return { expr } ->
       type_return env expr
    | Switch { expr; cases } ->
       type_switch env expr cases
    | DeclarationStatement { decl } ->
       type_declaration_statement env decl
  in
  ((fst stm, typed_stm), env')
  
(* Section 8.17 *)
and type_method_call env call_info func type_args args =
  let call_typed = type_function_call env call_info func type_args args in
  match call_typed.expr with
  | FunctionCall call ->
     { stmt = MethodCall 
                { func = call.func;
                  type_args = call.type_args;
                  args = call.args };
       typ = StmType.Unit },
     env
  | _ -> raise_s [%message "function call not typed as FunctionCall?"
                     ~typed_expr:(call_typed.expr : Prog.Expression.pre_t)]

(* Question: Can Assignment statement update env? *)
(* Typecheck LHS and RHS respectively and check if they have the same type. *)
(* Section 11.1
 *
 *          Δ, T, Γ |- e1 : t1
 *          Δ, T, Γ |- e2 : t2
 *                t1 = t2
 * ---------------------------------------------
 *    Δ, T, Γ |- e1 = e2 : Δ, T, Γ
 *)
and type_assignment env lhs rhs =
  let open Prog.Statement in
  let lhs_typed = type_expression env lhs in
  let rhs_typed = type_expression env rhs in
  ignore (assert_same_type env (info lhs) (info rhs)
            (snd lhs_typed).typ (snd rhs_typed).typ);
  { stmt = Assignment { lhs = lhs_typed; rhs = rhs_typed };
    typ = StmType.Unit },
  env

(* This belongs in an elaboration pass, really. - Ryan *)
and type_direct_application env typ args =
  let open Types.Expression in
  let instance = NamelessInstantiation { typ = typ; args = [] } in
  let apply = ExpressionMember { expr = Info.dummy, instance; name = (Info.dummy, "apply") } in
  let call = FunctionCall { func = Info.dummy, apply; type_args = []; args = args } in
  let call_typed = type_expression env (Info.dummy, call) in
  match (snd call_typed).expr with
  | FunctionCall call ->
     let args =
       List.map call.args
         ~f:(function
           | Some a -> a
           | None -> failwith "missing argument")
     in
     { stmt = DirectApplication { typ = translate_type env [] typ;
                                  args = args };
       typ = StmType.Unit },
     env
  | _ -> raise_s [%message "function call not typed as FunctionCall?"
                     ~typed_expr:((snd call_typed).expr : Prog.Expression.pre_t)]

(* Question: Can Conditional statement update env? *)
(* Section 11.6 The condition is required to be a Boolean
 *
 *          Δ, T, Γ |- e1 : bool
 *          Δ, T, Γ |- e2 : unit, Δ', T', Γ'
 * ---------------------------------------------
 *    Δ, T, Γ |- if e1 then e2 : Δ', T', Γ'
 *
 *
 *          Δ, T, Γ |- e1 : bool
 *          Δ, T, Γ |- e2 : unit, Δ', T', Γ'
 *          Δ, T, Γ |- e3 : unit, Δ', T', Γ'
 * ---------------------------------------------
 *    Δ, T, Γ |- if e1 then e2 else e3: Δ', T', Γ'
 *)
and type_conditional env cond tru fls =
  let open Prog.Statement in
  let expr_typed = type_expression env cond in
  assert_bool (info cond) (snd expr_typed).typ |> ignore;
  let type' stmt = fst (type_statement env stmt) in
  let tru_typed = type' tru in
  let tru_typ = (snd tru_typed).typ in
  let fls_typed = option_map type' fls in
  let stmt_out =
    Conditional { cond = expr_typed;
                  tru = tru_typed;
                  fls = fls_typed }
  in
  match fls_typed with
  | None ->
     { stmt = stmt_out; typ = tru_typ }, env
  | Some fls_typed ->
     let typ =
       match tru_typ, (snd fls_typed).typ with
       | StmType.Void, StmType.Void -> StmType.Void
       | StmType.Unit, _
       | _, StmType.Unit -> StmType.Unit
     in
     { stmt = stmt_out; typ = typ }, env

(* QUESTION: Why are we only allowing statements but not declarations *)
(* A block execuete a sequence of statements sequentially*)
and type_block_statement env block =
  let open Prog.Statement in
  let fold (prev_type, stmts, env) statement =
    (* Cannot have statements after a void statement *)
    match prev_type with
    | StmType.Void -> raise_internal_error "UnreachableBlock"
    | StmType.Unit ->
       let stmt_typed, env = type_statement env statement in
       ((snd stmt_typed).typ, stmt_typed::stmts, env)
  in
  let (typ, stmts, env) =
    List.fold_left ~f:fold ~init:(StmType.Unit, [], env) (snd block).statements
  in
  let block : Prog.Block.pre_t = 
    { annotations = (snd block).annotations;
      statements = List.rev stmts }
  in
  { stmt = BlockStatement { block = Info.dummy, block }; typ = typ }, env

(* Section 11.4
 * Can a return statement update the environment?
 *
 *          Δ, T, Γ |- e : t
 * ---------------------------------------------
 *    Δ, T, Γ |- return e: void ,Δ, T, Γ
 *)
and type_return env expr =
  let stmt : Prog.Statement.pre_t = 
    match expr with
    | None -> Return { expr = None }
    | Some e ->
       let e_typed = type_expression env e in
       Return { expr = Some e_typed }
  in
  { stmt = stmt; typ = StmType.Void }, env

(* Section 11.7 *)
and type_switch env expr cases =
  let open Types.Statement in
  let expr_typed = type_expression env expr in
  let action_name_typ = reduce_type env (snd expr_typed).typ in
  let label_checker label =
    match label with
    | Default ->
       Prog.Statement.Default
    | Name (name_info, name) ->
       CheckerEnv.find_type_of name env |> ignore;
       Prog.Statement.Name (name_info, name)
  in
  let case_checker (case_info, case) =
    match case with
    | Action { label = (label_info, label); code = block } ->
       let block_expr_typed, env = type_block_statement env block in
       let label_typed = label_checker label in
       let block_typed =
         match block_expr_typed.stmt with
         | BlockStatement { block } -> block
         | _ -> failwith "bug: expected block"
       in
       case_info,
       Prog.Statement.Action
         { label = (label_info, label_typed);
           code = block_typed }
    | FallThrough { label = (label_info, label)} ->
       let label_typed = label_checker label in
       case_info,
       Prog.Statement.FallThrough { label = (label_info, label_typed) }
  in
  match action_name_typ with
  | Enum _ -> 
     let cases = List.map ~f:case_checker cases in
     { stmt = Switch { expr = expr_typed;
                       cases = cases };
       typ = StmType.Unit }, env
  | _ -> failwith "Switch statement does not type check."

(* Section 10.3 *)
and type_declaration_statement env (decl: Declaration.t) : Prog.Statement.typed_t * CheckerEnv.t =
  let open Prog.Statement in
  match snd decl with
  | Constant _
  | Instantiation _
  | Variable _ ->
     let decl_typed, env' = type_declaration env decl in
     { stmt = DeclarationStatement { decl = decl_typed };
       typ = StmType.Unit },
     env'
  | _ -> raise_s [%message "declaration used as statement, but that's not allowed. Parser bug?" ~decl:(decl: Types.Declaration.t)]

and type_field env field =
  let Declaration.{ annotations = _; typ; name } = snd field in
  let name = snd name in
  let typ = translate_type env [] typ in
  RecordType.{ name; typ }

(* Section 10.1
 *
 *          Δ, T, Γ |- e : t' = t
 * ---------------------------------------------
 *    Δ, T, Γ |- const t x = e : Δ, T, Γ[x -> t]
 *)
and type_constant env decl_info typ name expr =
  let expected_typ = translate_type env [] typ in
  let typed_expr = type_expression env expr in
  assert_same_type env decl_info (fst expr)
    expected_typ (snd typed_expr).typ |> ignore;
  match compile_time_eval_expr env typed_expr with
  | Some value ->
     CheckerEnv.insert_dir_type_of (snd name) (snd typed_expr).typ In env
  | None ->
     failwith "expression not compile-time-known"

and insert_params (env: CheckerEnv.t) (params: Types.Parameter.t list) : CheckerEnv.t =
  let open Types.Parameter in
  let insert_param env (_, p) =
    let typ = translate_type env [] p.typ in
    let dir = translate_direction p.direction in
    CheckerEnv.insert_dir_type_of (snd p.variable) typ dir env
  in
  List.fold_left ~f:insert_param ~init:env params

(* Section 10.3 *)
and type_instantiation env info typ args name =
  let instance_type = type_nameless_instantiation env info typ args in
  CheckerEnv.insert_type_of (snd name) instance_type env

and check_constructor_invocation env type_params params type_args args =
  solve_constructor_invocation env type_params params type_args args |> ignore

and solve_constructor_invocation env type_params params_args type_args args: Typed.Type.t list =
  let type_params_args =
    match List.zip type_params type_args with
    | Ok v -> v
    | Unequal_lengths ->
       if type_args = []
       then List.map ~f:(fun v -> v, None) type_params
       else failwith "mismatch in type arguments"
  in
  let type_params_args =
    let inference_params_args =
      List.map params_args
        ~f:(fun (cons_param, arg) -> construct_param_as_param cons_param,
                                     expr_of_arg arg)
    in
    infer_type_arguments env Typed.Type.Void type_params_args inference_params_args []
  in
  let env = CheckerEnv.insert_types type_params_args env in
  let param_matches_arg (param, arg: Typed.ConstructParam.t * Types.Argument.t) =
    match snd arg with
    | Argument.Expression { value } ->
       let arg_type = type_expression env value in
       assert_type_equality env (fst arg) arg_type param.typ
    | KeyValue _ -> failwith "key-value argument passing unimplemented"
    | Missing -> failwith "missing argument??"
  in
  List.iter ~f:param_matches_arg params_args;
  List.map ~f:snd type_params_args

and type_select_case env state_names expr_types (_, case) : unit =
  let open Parser in
  let open Match in
  let open Typed.Type in
  let rec check' info match_type typ =
    match match_type with
    | Set element_type ->
       begin match element_type, typ with
       | Struct _, Struct _
       | Tuple _, Tuple _
       | List _, List _ ->
          assert_type_equality env info element_type typ
       | Tuple _, _
       | Struct _, _ ->
          assert_type_equality env info
            element_type
            (List { types = [typ] })
       | _, _ ->
          assert_type_equality env info element_type typ
       end
    | non_set_type ->
       check' info (Set non_set_type) typ
  in
  match List.zip expr_types case.matches with
  | Ok matches_and_types ->
    let check_match (typ, m) =
        match snd m with
        | Expression {expr} ->
           let match_type = reduce_type env @@ type_expression env expr in
           check' (fst m) match_type typ
        | Default
        | DontCare -> ()
    in
    List.iter ~f:check_match matches_and_types;
    let name = snd case.next in
    if List.mem ~equal:(=) state_names name
    then ()
    else raise @@ Env.UnboundName name
  | Unequal_lengths -> failwith "mismatch between types and number of matches"

and type_transition env state_names transition : unit =
  let open Parser in
  match snd transition with
  | Direct {next = (_, name')} ->
      if List.mem ~equal:(=) state_names name'
      then ()
      else raise @@ Env.UnboundName name'
  | Select {exprs; cases} ->
      let expr_types = List.map ~f:(type_expression env) exprs in
      List.iter ~f:(type_select_case env state_names expr_types) cases

and type_parser_state env state_names (state: Parser.state) : unit =
  let open Block in
  let block = {annotations = []; statements = (snd state).statements} in
  let (_, env') = type_block_statement env (fst state, block) in
  type_transition env' state_names (snd state).transition

and open_parser_scope env params constructor_params locals states =
  let open Parser in
  let env' = insert_params env constructor_params in
  let env' = List.fold_left ~f:type_declaration ~init:env' locals in
  let env' = insert_params env' params in
  let program_state_names = List.map ~f:(fun (_, state) -> snd state.name) states in
  (* TODO: check that no program_state_names overlap w/ standard ones
   * and that there is some "start" state *)

  let state_names = program_state_names @ ["accept"; "reject"] in
  (env', state_names)

(* Section 12.2 *)
and type_parser env name params constructor_params locals states =
  let (env', state_names) =
    open_parser_scope env params constructor_params locals states
  in
  let env' = type_declarations env' locals in
  List.iter ~f:(type_parser_state env' state_names) states;
  env

and open_control_scope env params constructor_params locals =
  (*TODO check that params and constructor params are well-formed *)
  let env' = insert_params env constructor_params in
  let env' = insert_params env' params in
  let env' = List.fold_left ~f:type_declaration ~init:env' locals in
  env'

(* Section 13 *)
and type_control env name type_params params constructor_params locals apply =
  if List.length type_params > 0
  then raise_s [%message "Control declarations cannot have type parameters" ~name:(snd name)]
  else
    let env' = open_control_scope env params constructor_params locals in
    let _ = type_block_statement env' apply in
    env

(* Section 9

 * Function Declaration:
 *
 *        Γ' = union over i Γ (xi -> di ti)
 *   forall k,  Δk, Tk, Γk' |- stk+1 : Δk+1, Tk+1, Γk+1'
 *     stk = return ek => Δk, Tk, Γk' |- ek : t' = tr
 * -------------------------------------------------------
 *    Δ, T, Γ |- tr fn<...Aj,...>(...di ti xi,...){...stk;...}
 *)
and type_function env return name type_params params body =
  let t_params = List.map ~f:snd type_params in
  let body_env = CheckerEnv.insert_type_vars t_params env in
  let p_fold = fun (acc,env:Parameter.t list * CheckerEnv.t) (p:Types.Parameter.t) ->
    begin let open Parameter in
    let p = snd p in
      let pd = begin match p.direction with
      | None -> In
      | Some d -> begin match snd d with
          | In -> In
          | Out -> Out
          | InOut -> InOut
      end
    end in
    let p_typ = p.typ |> translate_type env t_params in
    if is_well_formed_type env p_typ |> not
    then failwith "Parameter type is not well-formed" else
    let par = {name=p.variable |> snd;
              typ=p_typ;
              direction=pd} in
    let new_env =
      CheckerEnv.insert_dir_type_of (snd p.variable) par.typ par.direction env
    in
    par::acc, new_env end in
  let (ps,body_env) = List.fold_left ~f:p_fold ~init:([],body_env) params in
  let ps = List.rev ps in
  let rt = return |> translate_type env t_params in
  let sfold = fun (prev_type,envi:StmType.t*CheckerEnv.t) (stmt:Statement.t) ->
    begin match prev_type with
      | Void -> failwith "UnreachableBlock" (* do we want to do this? *)
      | Unit ->
        let (st,new_env) = type_statement envi stmt in
        begin match snd stmt with
          | Return {expr=eo} ->
            begin match eo with
              | None -> failwith "return expression must have an expression"
              | Some e ->
                 let te = type_expression envi e in
                 if not (type_equality envi rt te)
                 then failwith "body does not match return type"
                 else (st,new_env)
            end
          | _ -> (st,new_env)
        end
    end in
  let _ = List.fold_left ~f:sfold ~init:(StmType.Unit, body_env) (snd body).statements in
  let open FunctionType in
  let funtype = Type.Function {parameters=ps;
                 type_params= type_params |> List.map ~f:snd;
                 return= rt} in
  CheckerEnv.insert_type_of (snd name) funtype env

(* Section 7.2.9.1 *)
and type_extern_function env return name type_params params =
  let type_params = type_params |> List.map ~f:snd in
  let return = return |> translate_type env type_params in
  let params = translate_parameters env type_params params in
  let typ: Typed.FunctionType.t =
    { type_params = type_params;
      parameters = params;
      return = return }
  in
  CheckerEnv.insert_type_of (snd name) (Function typ) env

(* Section 10.2
 *
 *          Δ, T, Γ |- e : t' = t
 * ---------------------------------------------
 *    Δ, T, Γ |- t x = e : Δ, T, Γ[x -> t]
 *)
and type_variable env typ name init =
  let expected_typ = translate_type env [] typ in
  match init with
  | None ->
      CheckerEnv.insert_dir_type_of (snd name) expected_typ In env
  | Some value ->
     let initialized_typ = type_expression env value in
     let expr_typ, _ =
       assert_same_type env (fst value) (fst value) expected_typ initialized_typ in
    CheckerEnv.insert_dir_type_of (snd name) expr_typ In env

(* Section 12.11 *)
and type_value_set env typ size name =
  let element_type = translate_type env [] typ in
  CheckerEnv.insert_type_of (snd name) (Set element_type) env

(* Section 13.1 *)
and type_action env name params body =
 let p_fold = fun (((data_params,ctrl_params),env): (Typed.Parameter.t list * ConstructParam.t list) * CheckerEnv.t) (p:Types.Parameter.t) : ((Typed.Parameter.t list * ConstructParam.t list) * CheckerEnv.t) ->
    begin let p = snd p in
      let name = p.variable |> snd in
      let typ = p.typ |> translate_type env [] in
      if is_well_formed_type env typ |> not
      then failwith "Parameter type is not well-formed" else
      begin match p.direction with
        | None ->
          let open ConstructParam in
          let ctrl_par = {name=name; typ=typ} in
          let new_env = CheckerEnv.insert_type_of (snd p.variable) typ env in
          (data_params, ctrl_par::ctrl_params), new_env
        | Some d ->
          if ctrl_params <> []
          then failwith "Action parameters with direction must come before directionless parameters"
          else let d = begin match snd d with
            | In -> In
            | Out -> Out
            | InOut -> InOut end in
          let open Typed.Parameter in
          let par = {name=name; typ=typ; direction=d} in
          let new_env =
            CheckerEnv.insert_dir_type_of (snd p.variable) typ d env
          in
          (par::data_params, ctrl_params), new_env
      end
      end in
 let ((dps,cps),body_env) = List.fold_left ~f:p_fold ~init:(([],[]),env) params in
 let dps = List.rev dps in
 let cps = List.rev cps in
  let sfold = fun (prev_type,envi:StmType.t*CheckerEnv.t) (stmt:Statement.t) ->
    begin match prev_type with
    | Void -> failwith "UnreachableBlock" (* do we want to do this? *)
    | Unit -> let (st,new_env) = type_statement envi stmt in
      begin match snd stmt with
      | Switch _ -> failwith "Actions can not contain Switch Statements"
      | Return {expr=eo} ->
        begin match eo with
        | Some _ -> failwith "Return expressions in Actions must not contain expressions"
        | None -> (st,new_env)
        end
      | _ -> (st, new_env)
      end
    end
  in
  let _ = List.fold_left ~f:sfold ~init:(StmType.Unit, body_env) (snd body).statements in
  let open Typed.ActionType in
  let actionType = Type.Action {data_params=dps; ctrl_params=cps} in
  CheckerEnv.insert_type_of (snd name) actionType env

(* Section 13.2 *)
and type_table env name properties =
  type_table' env name None [] (List.map ~f:snd properties)

and type_keys env keys =
  let type_key (key: Types.Table.key) =
    let {key; match_kind; _}: Table.pre_key = snd key in
    match CheckerEnv.find_type_of_opt (snd match_kind) env with
    | Some (MatchKind, _) ->
       type_expression env key
    | _ ->
       raise_s [%message "invalid match_kind" ~match_kind:(snd match_kind)]
  in
  List.map ~f:type_key keys

and type_table_actions env key_types actions =
  let type_table_action (call_info, action: Table.action_ref) =
    match CheckerEnv.find_type_of_opt (snd action.name) env with
    | Some (Action action_decl, _) ->
       (* Below should fail if there are control plane arguments *)
       let params_args = match_params_to_args call_info action_decl.data_params action.args in
       let type_param_arg env (param, expr: Typed.Parameter.t * Expression.t option) =
         match expr with
         | Some expr ->
             let arg_typ, dir = type_expression env expr in
             check_direction env param.direction expr dir;
             assert_type_equality env call_info arg_typ param.typ
         | None ->
            if param.direction = In
            then raise_s [%message "don't care argument (underscore) provided for in parameter"
                             ~call_site:(call_info: Info.t) ~param:param.name]
       in
       List.iter ~f:(type_param_arg env) params_args;
       Type.Action action_decl
    | _ ->
       raise_s [%message "invalid action" ~action:(snd action.name)]
  in
  let action_typs = List.map ~f:type_table_action actions in
  (* Need to fail in the case of duplicate action names *)
  let action_names = List.map ~f:(fun (_, action: Table.action_ref) -> snd action.name) actions in
  List.zip_exn action_names action_typs

and type_table_entries env entries key_typs action_map =
  match key_typs with
  (* Should key types be in an option type? *)
  | None -> failwith "Keys need to have types"
  | Some key_typs ->
    let type_table_entry (_, entry: Table.entry) =
      let type_entry_key_vals (key_typ: Type.t) (_, key_match: Match.t) =
        match key_match with
        | Default -> failwith "Default unimplemented"
        | DontCare -> true
        | Expression {expr= exp} -> exp |> type_expression env |> type_equality env key_typ in
      let _ = List.map2 ~f:type_entry_key_vals key_typs entry.matches in
      let action = snd entry.action in
      match List.Assoc.find action_map ~equal:(=) (snd action.name) with
      | None -> failwith "Entry must call an action in the table."
      | Some (Type.Action {data_params=params; ctrl_params=_}) ->
        let check_arg (param:Parameter.t) (_, arg:Argument.t) =
          begin match arg with
          (* Direction handling probably is incorrect here. *)
          | Expression {value=exp} -> exp |> type_expression env |> type_equality env param.typ
          | _ -> failwith "Actions in entries only support positional arguments."
          end in
        let _ = List.map2 ~f:check_arg params action.args in true
      | _ -> failwith "Table actions must have action types." in
    List.for_all ~f:type_table_entry entries

and type_table' env name key_types action_map properties =
  match properties with
  | Key { keys } :: rest ->
     begin match key_types with
     | None -> type_table' env name (Some (type_keys env keys)) action_map rest
     | Some key_types -> raise_s [%message "multiple key properties in table?" ~name:(snd name)]
     end
  | Actions { actions } :: rest ->
     begin match key_types with
     | None ->
        begin match Util.find_and_drop ~f:(function Table.Key _ -> true | _ -> false) properties with
        | Some key_prop, other_props ->
           let props = key_prop :: other_props in
           type_table' env name None action_map props
        | None, props ->
           type_table' env name (Some []) action_map props
        end
     | Some kts ->
        let action_map = type_table_actions env kts actions in
        type_table' env name key_types action_map rest
     end
  | Entries { entries } :: rest ->
    if type_table_entries env entries key_types action_map
    then type_table' env name key_types action_map rest
    else failwith ""
  | Custom { name = (_, "default_action"); _ } :: rest ->
     type_table' env name key_types action_map rest
  | Custom { name = (_, "size"); _ } :: rest
  | Custom _ :: rest ->
     (* TODO *)
     type_table' env name key_types action_map rest
  | [] ->
    let open EnumType in
    let open RecordType in
    (* Aggregate table information. *)
    let action_names = List.map ~f:fst action_map in
    let action_enum_typ = Type.Enum {typ=None; members=action_names} in
    (* Populate environment with action_enum *)
    (* names of action list enums are "action_list_<<table name>>" *)
    let env = CheckerEnv.insert_type (name |> snd |> (^) "action_list_") action_enum_typ env in
    let hit_field = {name="hit"; typ=Type.Bool} in
    (* How to represent the type of an enum member *)
    let run_field = {name="action_run"; typ=action_enum_typ} in
    let apply_result_typ = Type.Struct {fields=[hit_field; run_field]} in
    (* names of table apply results are "apply_result_<<table name>>" *)
    let result_typ_name = name |> snd |> (^) "apply_result_" in
    let env = CheckerEnv.insert_type result_typ_name apply_result_typ env in
    let table_typ = Type.Table {result_typ_name=result_typ_name} in
    CheckerEnv.insert_type_of (snd name) table_typ env

(* Section 7.2.2 *)
and type_header env name fields =
  let fields = List.map ~f:(type_field env) fields in
  let header_typ = Type.Header { fields } in
  CheckerEnv.insert_type (snd name) header_typ env

(* Section 7.2.3 *)
and type_header_union env name fields =
  let open RecordType in
  let union_folder = fun acc -> fun field ->
    begin let open Types.Declaration in
      let {typ=ht; name=fn; _} = snd field in
      let ht = begin match snd ht with
        | TypeName tn -> snd tn
        | _ -> failwith "Header Union fields must be Headers"
      end in
      match CheckerEnv.resolve_type_name ht env with
      | Header _ -> {name = snd fn; typ=TypeName ht}::acc
      | _ -> failwith "Header Union field is undefined"
    end in
  let ufields = List.fold_left ~f:union_folder ~init:[] fields |> List.rev in
  let hu = Type.HeaderUnion {fields=ufields} in
  CheckerEnv.insert_type (snd name) hu env

(* Section 7.2.5 *)
and type_struct env name fields =
  let fields = List.map ~f:(type_field env) fields in
  let struct_typ = Type.Struct { fields } in
  CheckerEnv.insert_type (snd name) struct_typ env

(* Auxillary function for [type_error] and [type_match_kind],
 * which require unique names *)
and fold_unique members (_, member) =
  if List.mem ~equal:(=) members member then
    failwith "Name already bound"
  else
    member :: members

(* Section 7.1.2 *)
(* called by type_type_declaration *)
and type_error env members =
  let add_err env (_, e) =
    CheckerEnv.insert_type_of_toplevel ("error." ^ e) Type.Error env
  in
  List.fold_left ~f:add_err ~init:env members

(* Section 7.1.3 *)
and type_match_kind env members =
  let add_mk env (_, m) =
    CheckerEnv.insert_type_of_toplevel m Type.MatchKind env
  in
  List.fold_left ~f:add_mk ~init:env members

(* Section 7.2.1 *)
and type_enum env name members =
  let members' = List.map ~f:snd members in
  let enum_typ = Type.Enum { members = members'; typ = None } in
  CheckerEnv.insert_type (snd name) enum_typ env

(* Section 8.3 *)
and type_serializable_enum env typ name members =
  let typ = translate_type env [] typ in
  begin match typ with
    | Int _ | Bit _ ->
      let enum_member_folder = fun (acc_members : string list) ((name,exp):P4String.t * Expression.t) ->
        begin let name = snd name in
          let mem_typ = type_expression env exp in
          if type_equality env mem_typ typ then name::acc_members
          else failwith "The type of each enum member must conform to the underlying type."
        end in let members = List.fold_left ~f:enum_member_folder ~init:[] members in
        let open EnumType in
        let enum_typ = Type.Enum {typ=Some(typ); members=members} in
        CheckerEnv.insert_type (snd name) enum_typ env
    | _ -> failwith "The underlying type of a serializable enum must be a fixed-width integer."
  end

(* Section 7.2.9.2 *)
and type_extern_object env name type_params methods =
  let init_env = env in
  let type_params' = List.map ~f:snd type_params in
  let consume_method (constructors, methods) m =
    match snd m with
    | MethodPrototype.Constructor {name = cname; params; _} ->
        assert (snd cname = snd name);
        let params' = translate_construct_params env type_params' params in
        (params' :: constructors, methods)
    | MethodPrototype.Method {return; name; type_params; params; _}
    | MethodPrototype.AbstractMethod {return; name; type_params; params; _} ->
        let method_typ_params = List.map ~f:snd type_params in
        let all_typ_params = type_params' @ method_typ_params in
        let params' =
          translate_parameters env all_typ_params params
        in
        let m: ExternType.extern_method =
          { name = snd name;
            typ = { type_params = method_typ_params;
                    parameters = params';
                    return = translate_type env all_typ_params return } }
        in
        (constructors, m :: methods)
  in
  let (_, ms') = List.fold_left ~f:consume_method ~init:([], []) methods in
  let typ: ExternType.t =
    { type_params = type_params';
      methods = ms' }
  in
  let extern_typ = (Typed.Type.Extern typ) in
  if is_well_formed_type init_env extern_typ |> not
  then failwith "Extern type is not well-formed" else
  CheckerEnv.insert_type (snd name) extern_typ env

(* Section 7.3 *)
and type_type_def env (_, name) typ_or_decl =
  match typ_or_decl with
  | Left typ ->
      CheckerEnv.insert_type name (translate_type env [] typ) env
  | Right decl ->
      let env' = type_declaration env decl in
      let (_, decl_name) = Declaration.name decl in
      let decl_typ = CheckerEnv.resolve_type_name decl_name env' in
      CheckerEnv.insert_type name decl_typ env'

(* ? *)
and type_new_type env name typ_or_decl =
  (* Treating newtypes like typedefs for now even though this defeats the
   * purpose of newtypes *)
  type_type_def env name typ_or_decl

and check_params_wf env params =
  if not (are_param_types_well_formed env params)
  then raise_s [%message "Parameter types are  not well-formed"
                   ~ps:(params: Typed.Parameter.t list)]

and check_construct_params_wf env params =
  if not (are_construct_params_types_well_formed env params)
  then raise_s [%message "Parameter types are  not well-formed"
                   ~ps:(params: Typed.ConstructParam.t list)]


(* Section 7.2.11.2 *)
and type_control_type env name type_params params =
  let t_params = List.map ~f:snd type_params in
  let body_env = CheckerEnv.insert_type_vars t_params env in
  let ps = translate_parameters env t_params params in
  check_params_wf body_env ps;
  let tps = List.map ~f:snd type_params in
  let ctrl = Type.Control {type_params=tps; parameters=ps} in
  CheckerEnv.insert_type (snd name) ctrl env

(* Section 7.2.11 *)
and type_parser_type env name type_params params =
  let t_params = List.map ~f:snd type_params in
  let body_env = CheckerEnv.insert_type_vars t_params env in
  let ps = translate_parameters env t_params params in
  check_params_wf body_env ps;
  let tps = List.map ~f:snd type_params in
  let ctrl = Type.Parser {type_params=tps; parameters=ps} in
  CheckerEnv.insert_type (snd name) ctrl env

(* Section 7.2.12 *)
and type_package_type env name type_params params =
  let t_params = List.map ~f:snd type_params in
  let body_env = CheckerEnv.insert_type_vars t_params env in
  let ps = translate_construct_params env t_params params in
  check_construct_params_wf body_env ps;
  let tps = List.map ~f:snd type_params in
  let ctrl = Type.Package {type_params=tps; parameters=ps} in
  CheckerEnv.insert_type (snd name) ctrl env

and type_declaration (env: CheckerEnv.t) (decl: Types.Declaration.t) : Prog.Declaration.t * CheckerEnv.t =
  let (decl': Prog.Declaration.t), env =
    match snd decl with
    | Constant { annotations = _; typ; name; value } ->
      type_constant env (fst decl) typ name value
    | Instantiation { annotations = _; typ; args; name; init } ->
      (* TODO: type check init? *)
      type_instantiation env (fst decl) typ args name
    | Parser { annotations = _; name; type_params = _; params; constructor_params; locals; states } ->
      type_parser env name params constructor_params locals states
    | Control { annotations = _; name; type_params; params; constructor_params; locals; apply } ->
      type_control env name type_params params constructor_params locals apply
    | Function { return; name; type_params; params; body } ->
      type_function env return name type_params params body
    | ExternFunction { annotations = _; return; name; type_params; params } ->
      type_extern_function env return name type_params params
    | Variable { annotations = _; typ; name; init } ->
      type_variable env typ name init
    | ValueSet { annotations = _; typ; size; name } ->
      type_value_set env typ size name
    | Action { annotations = _; name; params; body } ->
      type_action env name params body
    | Table { annotations = _; name; properties } ->
      type_table env name properties
    | Header { annotations = _; name; fields } ->
      type_header env name fields
    | HeaderUnion { annotations = _; name; fields } ->
      type_header_union env name fields
    | Struct { annotations = _; name; fields } ->
      type_struct env name fields
    | Error { members } ->
      type_error env members
    | MatchKind { members } ->
      type_match_kind env members
    | Enum { annotations = _; name; members } ->
      type_enum env name members
    | SerializableEnum { annotations = _; typ; name; members } ->
      type_serializable_enum env typ name members
    | ExternObject { annotations = _; name; type_params; methods } ->
      type_extern_object env name type_params methods
    | TypeDef { annotations = _; name; typ_or_decl } ->
      type_type_def env name typ_or_decl
    | NewType { annotations = _; name; typ_or_decl } ->
      type_new_type env name typ_or_decl
    | ControlType { annotations = _; name; type_params; params } ->
      type_control_type env name type_params params
    | ParserType { annotations = _; name; type_params; params } ->
      type_parser_type env name type_params params
    | PackageType { annotations = _; name; type_params; params } ->
      type_package_type env name type_params params
  in
  let env = compile_time_eval_decl env decl' in
  decl', CheckerEnv.insert_decl decl' env

and type_declarations env decls =
  let f env decl = snd (type_declaration env decl) in
  List.fold_left ~f ~init:env decls

(* Entry point function for type checker *)
let check_program (program:Types.program) : CheckerEnv.t * Prog.program =
  let Program top_decls = program in
  let env = type_declarations CheckerEnv.empty_t top_decls in
  env, Prog.Program (CheckerEnv.all_decls env)
