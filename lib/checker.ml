open Types
open Typed
open Util
open Prog.Env
(* hack *)
module Petr4Error = Error
module Petr4Info = Info
open Core_kernel
open Petr4Error
module Error = Petr4Error
module Info = Petr4Info
let (=) = Stdlib.(=)
let (<>) = Stdlib.(<>)

module Eval = Eval.MakeInterpreter(V1model.V1Switch)

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

let assert_runtime_numeric = make_assert "bit<> or int<>"
  begin function
  | Int typ
  | Bit typ -> Some typ
  | _ -> None
  end


(* Checks if [t] is a specific p4 type as satisfied by [f] under [env] *)
let rec is_some_type
  env
  (f:Typed.Type.t -> bool)
  (t:Typed.Type.t) : bool =
  if f t then true else begin match t with
  | TypeName n ->
    let ty = CheckerEnv.resolve_type_name n env in
    if Typed.Type.eq ty t then false else is_some_type env f ty
  | NewType {typ=ty; name=s} -> is_some_type env f ty
  | SpecializedType {base=ty; _} -> is_some_type env f ty
  | _ -> false
  end

let is_package env (t:Typed.Type.t) : bool =
  is_some_type env
    begin function
    | Package _ -> true
    | _         -> false
    end t

let is_parser env (t:Typed.Type.t) : bool =
  is_some_type env
    begin function
    | Parser _ -> true
    | _        -> false
    end t

let is_control env (t:Typed.Type.t) : bool =
  is_some_type env
    begin function
    | Control _ -> true
    | _         -> false
    end t

let is_extern env (t:Typed.Type.t) : bool =
  is_some_type env
    begin function
    | Extern _ -> true
    | _         -> false
    end t

let is_function env (t:Typed.Type.t) : bool =
  is_some_type env
    begin function
    | Function _ -> true
    | _          -> false
    end t

let is_table env (t:Typed.Type.t) : bool =
  is_some_type env
    begin function
    | Table _ -> true
    | _         -> false
    end t

(* Ugly hack *)
let real_name_for_type_member env (typ_name: Types.name) name =
  begin match typ_name with
  | QualifiedName (qs, typ_name) ->
     let prefixed_name = snd typ_name ^ "." ^ (snd name) in
     QualifiedName (qs, (fst name, prefixed_name))
  | BareName typ_name ->
     let prefixed_name = snd typ_name ^ "." ^ (snd name) in
     BareName (fst name, prefixed_name)
  end

let rec min_size_in_bits' env (info: Info.t) (hdr_type: Typed.Type.t) : int =
  match saturate_type env hdr_type with
  | Bit { width } | Int { width } ->
     width
  | VarBit _ ->
     0
  | NewType { typ; _ }
  | Enum { typ = Some typ; _ } ->
     min_size_in_bits' env info typ
  | Struct { fields }
  | Header { fields } ->
     fields
     |> List.map ~f:(field_width_bits env info)
     |> List.fold ~init:0 ~f:(+)
  | HeaderUnion { fields } ->
     let min_field_size (field: RecordType.field) =
       min_size_in_bits' env info field.typ
     in
     fields
     |> List.map ~f:min_field_size
     |> List.fold ~init:0 ~f:min
  | Array { typ; size } ->
     size * min_size_in_bits' env info typ
  | _ -> raise_mismatch info "header or header union" hdr_type

and field_width_bits env info (field: Typed.RecordType.field) : int =
  min_size_in_bits' env info field.typ

and min_size_in_bits env (info: Info.t) (hdr_type: Typed.Type.t) : Bigint.t =
  Bigint.of_int (min_size_in_bits' env info hdr_type)

and min_size_in_bytes env info hdr_type =
  let bits = min_size_in_bits' env info hdr_type in
  Bigint.of_int ((bits + 7) asr 3)

(* Evaluate the expression [expr] at compile time. Make sure to
 * typecheck the expression before trying to evaluate it! *)
and compile_time_eval_expr (env: CheckerEnv.t) (expr: Prog.Expression.t) : Prog.Value.value option =
  match (snd expr).expr with
  | Name name ->
     CheckerEnv.find_const_opt name env
  | True -> Some (Prog.Value.VBool true)
  | False -> Some (Prog.Value.VBool false)
  | String (_, str) -> Some (Prog.Value.VString str)
  | Int (_, i) ->
     begin match i.width_signed with
     | None ->
        Some (Prog.Value.VInteger i.value)
     | Some (width, signed) ->
        if signed
        then Some (Prog.Value.VInt { w = Bigint.of_int width; v = i.value })
        else Some (Prog.Value.VBit { w = Bigint.of_int width; v = i.value })
     end
  | UnaryOp { op; arg } ->
     begin match compile_time_eval_expr env arg with
     | Some arg ->
        Some (Ops.interp_unary_op op arg)
     | None -> None
     end
  | BinaryOp { op; args = (l, r) } ->
     begin match compile_time_eval_expr env l,
                 compile_time_eval_expr env r with
     | Some l, Some r ->
        Some (Ops.interp_binary_op op l r)
     | _ -> None
     end
  | Cast { typ; expr } ->
     let expr_val = compile_time_eval_expr env expr in
     let type_lookup name = CheckerEnv.resolve_type_name name env in
     let val_lookup name = CheckerEnv.find_const name env in
     option_map (Ops.interp_cast ~type_lookup ~val_lookup typ) expr_val
  | List { values } ->
     begin match compile_time_eval_exprs env values with
     | Some vals -> Some (VTuple vals)
     | None -> None
     end
  | TypeMember{typ;name} ->
     let real_name = real_name_for_type_member env typ name in
     CheckerEnv.find_const_opt real_name env
  | ErrorMember t ->
     Some (VError (snd t))
  | Record { entries } ->
     let opt_entries =
       List.map ~f:(fun (_, {key; value}) ->
           match compile_time_eval_expr env value with
           | Some v -> Some (snd key, v)
           | None -> None)
         entries
     in
     begin match Util.list_option_flip opt_entries with
     | Some es -> Some (Prog.Value.VRecord es)
     | None -> None
     end
  | BitStringAccess{bits; hi; lo} ->
     begin match compile_time_eval_expr env bits with
     | Some (VInt {w; v})
     | Some (VBit {w; v}) ->
        let slice_width = Bigint.(hi - lo + one) in
        let slice_val = Bitstring.bitstring_slice v hi lo in
        Some (VBit {w = slice_width; v = slice_val})
     | _ -> None
     end
  | DontCare -> Some (VSet (SUniversal))
  | ExpressionMember {expr; name = (_, "size")} ->
     begin match saturate_type env (snd expr).typ with
     | Array {size; _} -> Some (VInteger (Bigint.of_int size))
     | _ -> None
     end
  | ExpressionMember {expr; name} ->
     begin match compile_time_eval_expr env expr with
     | Some (VStruct {fields})
     | Some (VHeader {fields; _})
     | Some (VUnion {fields}) ->
        fields
        |> List.find ~f:(fun (n, _) -> n = snd name)
        |> option_map snd
     | _ -> None
     end
  | FunctionCall { func; type_args = []; args = [] } ->
     begin match (snd func).expr with
     | ExpressionMember {expr; name = (_, "minSizeInBits")} ->
        let typ = saturate_type env (snd expr).typ in
        let size = min_size_in_bits env (fst expr) typ in
        Some (VInteger size)
     | ExpressionMember {expr; name = (_, "minSizeInBytes")} ->
        let typ = saturate_type env (snd expr).typ in
        let size = min_size_in_bytes env (fst expr) typ in
        Some (VInteger size)
     | _ -> None
     end
  | _ ->
     None

and compile_time_eval_exprs env exprs : Prog.Value.value list option =
  let options = List.map ~f:(compile_time_eval_expr env) exprs in
  Util.list_option_flip options

and bigint_of_value v =
  match v with
  | Prog.Value.VInt { v; _}
  | Prog.Value.VBit { v; _}
  | Prog.Value.VInteger v ->
     Some v
  | _ -> None

and compile_time_eval_bigint env expr: Bigint.t =
  match
    compile_time_eval_expr env expr
    |> option_map bigint_of_value
    |> option_collapse
  with
  | Some bigint ->
     bigint
  | None ->
     raise_s [%message "could not compute compile-time-known numerical value for expr"
                 ~expr:(expr: Prog.Expression.t)]

(* Evaluate the declaration [decl] at compile time, updating env.const
 * with any bindings made in the declaration.  Make sure to typecheck
 * [decl] before trying to evaluate it! *)
and compile_time_eval_decl (env: CheckerEnv.t) (decl: Prog.Declaration.t) : CheckerEnv.t =
  match snd decl with
  | Constant { name; value; _ } ->
     CheckerEnv.insert_const (BareName name) value env
  | _ -> env

and get_type_params (t: Typed.Type.t) : string list =
  match t with
  | Package {type_params; _}
  | Control {type_params; _}
  | Parser {type_params; _}
  | Function {type_params; _} ->
     type_params
  | _ ->
     []

and drop_type_params (t: Typed.Type.t) : Typed.Type.t =
  match t with
  | Package p ->
     Package {p with type_params = []}
  | Control c ->
     Control {c with type_params = []}
  | Parser p ->
     Parser {p with type_params = []}
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
and saturate_type (env: CheckerEnv.t) (typ: Typed.Type.t) : Typed.Type.t =
  let open Type in
  let saturate_field env (field: RecordType.field) =
    {field with typ = saturate_type env field.typ}
  in
  let saturate_rec env ({fields;} : RecordType.t) : RecordType.t =
    {fields = List.map ~f:(saturate_field env) fields;}
  in
  let saturate_param env (param: Typed.Parameter.t) =
    {param with typ = saturate_type env param.typ}
  in
  let saturate_params env params =
    List.map ~f:(saturate_param env) params
  in
  let saturate_pkg env (pkg: PackageType.t) : PackageType.t =
    let env = CheckerEnv.insert_type_vars pkg.type_params env in
    let env = CheckerEnv.insert_type_vars pkg.wildcard_params env in
    {pkg with parameters = saturate_params env pkg.parameters;}
  in
  let saturate_ctrl env (ctrl: ControlType.t) : ControlType.t =
    let env = CheckerEnv.insert_type_vars ctrl.type_params env in
    {type_params = ctrl.type_params;
     parameters = List.map ~f:(saturate_param env) ctrl.parameters}
  in
  let saturate_function env (fn: FunctionType.t) : FunctionType.t =
    let env = CheckerEnv.insert_type_vars fn.type_params env in
    {type_params = fn.type_params;
     parameters = List.map ~f:(saturate_param env) fn.parameters;
     kind = fn.kind;
     return = saturate_type env fn.return}
  and saturate_action env (action: ActionType.t) : ActionType.t =
    { data_params = List.map ~f:(saturate_param env) action.data_params;
      ctrl_params = List.map ~f:(saturate_param env) action.ctrl_params }
  and saturate_constructor env (ctor: ConstructorType.t) : ConstructorType.t =
    { type_params = ctor.type_params;
      wildcard_params = ctor.wildcard_params;
      parameters = List.map ~f:(saturate_param env) ctor.parameters;
      return = saturate_type env ctor.return }
  in
  match typ with
  | TypeName t ->
     begin match CheckerEnv.resolve_type_name_opt t env with
     | None -> typ
     | Some (TypeName t') ->
        if Types.name_eq t' t
        then typ
        else saturate_type env (TypeName t')
     | Some typ' ->
        saturate_type env typ'
     end
  | Bool | String | Integer
  | Int _ | Bit _ | VarBit _
  | Error | MatchKind | Void
  | NewType _
  | Table _ ->
      typ
  | Array arr ->
      Array {arr with typ = saturate_type env arr.typ}
  | Tuple {types} ->
      Tuple {types = List.map ~f:(saturate_type env) types}
  | List {types} ->
      List {types = List.map ~f:(saturate_type env) types}
  | Record rec_typ ->
      Record (saturate_rec env rec_typ)
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
      Extern extern
  | Function func ->
      Function (saturate_function env func)
  | Action action ->
    Action (saturate_action env action)
  | Constructor ctor ->
     Constructor (saturate_constructor env ctor)

and reduce_type (env: CheckerEnv.t) (typ: Typed.Type.t) : Typed.Type.t =
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

and reduce_to_underlying_type (env: CheckerEnv.t) (typ: Typed.Type.t) : Typed.Type.t =
  let typ = reduce_type env typ in
  match typ with
  | NewType {typ; _} -> reduce_to_underlying_type env typ
  | Enum {typ = Some typ; _} -> reduce_to_underlying_type env typ
  | _ -> typ

and reduce_enums_in_type (env: CheckerEnv.t) (typ: Typed.Type.t) : Typed.Type.t =
  let typ = reduce_type env typ in
  match typ with
  | Enum {typ = Some typ; _} -> reduce_enums_in_type env typ
  | _ -> typ

type var_constraint = string * Typed.Type.t option [@@deriving sexp]
type var_constraints = var_constraint list [@@deriving sexp]
type soln = var_constraints option [@@deriving sexp]

let empty_constraints unknowns : var_constraints =
  let empty_constraint var =
    (var, None)
  in
  List.map ~f:empty_constraint unknowns

let unknowns constraints =
  List.map ~f:fst constraints

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
       if type_equality env [] x_typ y_typ
       then (x_var, Some x_typ)
       else if cast_ok env x_typ y_typ
       then (x_var, Some y_typ)
       else if cast_ok env y_typ x_typ
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
    | None -> (var, Type.Void)
  in
  List.map ~f:constraint_to_type_arg cs

and gen_all_constraints (env: CheckerEnv.t) ctx unknowns params_args constraints =
  match params_args with
  | (param, Some arg) :: more ->
     let arg_typed = type_expression env ctx arg in
     let param_type = param.Typed.Parameter.typ in
     begin match solve_types env [] unknowns param_type (snd arg_typed).typ with
     | Some arg_constraints ->
        let constraints = merge_constraints env constraints arg_constraints in
        gen_all_constraints env ctx unknowns more constraints
     | None -> raise_s [%message "could not solve type equality t1 = t2"
                           ~t1:(param_type: Typed.Type.t)
                           ~t2:((snd arg_typed).typ: Typed.Type.t)
                           ~unknowns:(unknowns: string list)
                           ~env:(env: CheckerEnv.t)]
     end
  | (param_type, None) :: more ->
     gen_all_constraints env ctx unknowns more constraints
  | [] ->
     constraints

and infer_type_arguments env ctx ret type_params_args params_args constraints =
  let insert (env, args, unknowns) (type_var, type_arg) =
    match type_arg with
    | Some arg ->
       CheckerEnv.insert_type (BareName (Info.dummy, type_var)) arg env, args @ [(type_var, arg)], unknowns
    | None ->
       env, args, unknowns @ [type_var]
  in
  let env, params_args', unknowns = List.fold ~f:insert ~init:(env, [], []) type_params_args in
  let constraints =
    empty_constraints unknowns
    |> gen_all_constraints env ctx unknowns params_args
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
  |> option_map List.rev

and solve_record_type_equality env equiv_vars unknowns (rec1: RecordType.t) (rec2: RecordType.t) =
  let open RecordType in
  let solve_fields (f1, f2 : field * field) =
    if f1.name = f2.name
    then solve_types env equiv_vars unknowns f1.typ f2.typ
    else None
  in
  let field_cmp (f1 : field) (f2 : field) =
    String.compare f1.name f2.name
  in
  let fields1 = List.sort ~compare:field_cmp rec1.fields in
  let fields2 = List.sort ~compare:field_cmp rec2.fields in
  solve_lists env unknowns fields1 fields2 ~f:solve_fields

and solve_enum_type_equality env equiv_vars unknowns enum1 enum2 =
  let open EnumType in
  (* could also check structural equality just to be sure but I don't
     think that's necessary... - Ryan *)
  if enum1.name = enum2.name
  then Some (empty_constraints unknowns)
  else None

and solve_package_type_equality env equiv_vars unknowns pkg1 pkg2 =
  let open PackageType in
  match List.zip pkg1.type_params pkg2.type_params with
  | Ok param_pairs ->
     let equiv_vars' = equiv_vars @ param_pairs in
     solve_params_equality env equiv_vars' unknowns pkg1.parameters pkg2.parameters
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
    (solve_params_equality env equiv_vars unknowns action1.ctrl_params action2.ctrl_params)

and solve_constructor_type_equality env equiv_vars unknowns ctor1 ctor2 =
  let open ConstructorType in
  match List.zip ctor1.type_params ctor2.type_params with
  | Ok param_pairs ->
     let equiv_vars' = equiv_vars @ param_pairs in
     merge_solutions env (solve_types env equiv_vars' unknowns ctor1.return ctor2.return)
                         (solve_params_equality env equiv_vars' unknowns ctor1.parameters ctor2.parameters)
  | Unequal_lengths -> None


and type_vars_equal_under equiv_vars tv1 tv2 =
  match equiv_vars with
  | (a, b)::rest ->
      if tv1 = a || tv2 = b
      then tv1 = a && tv2 = b
      else type_vars_equal_under rest tv1 tv2
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
and solve_types ?(casts=true)
                (env: CheckerEnv.t)
                (equiv_vars: (string * string) list)
                (unknowns: string list)
                (t1: Typed.Type.t)
                (t2: Typed.Type.t)
  : soln =
  let ok ?(casts=true) (t1, t2) =
    solve_types ~casts env equiv_vars unknowns t1 t2
  in
  let t1 = reduce_type env t1 in
  let t2 = reduce_type env t2 in
  begin match t1, t2 with
    | TypeName (QualifiedName _), _
    | _, TypeName (QualifiedName _) ->
       failwith "Name in saturated type?"
    | SpecializedType { base = Extern { name = e1 };
                        args = type_args1 },
      SpecializedType { base = Extern { name = e2 };
                        args = type_args2 } ->
       if e1 = e2
       then solve_lists env unknowns ~f:(ok ~casts:false) type_args1 type_args2
       else None
    | SpecializedType _, _
    | _, SpecializedType _ ->
       raise_s [%message "Stuck specialized type?" ~t1:(t1: Typed.Type.t)
                                                   ~t2:(t2: Typed.Type.t)]
    | TypeName (BareName (_, tv1)), TypeName (BareName (i2, tv2)) ->
        if type_vars_equal_under equiv_vars tv1 tv2
        then Some (empty_constraints unknowns)
        else Some (single_constraint unknowns tv1 t2)
    | TypeName (BareName (_, tv)), typ ->
       if List.mem ~equal:(=) unknowns tv
       then Some (single_constraint unknowns tv typ)
       else None
    | NewType nt1, NewType nt2 ->
       if nt1.name = nt2.name
       then Some (empty_constraints unknowns)
       else None
    | Bool, Bool
    | String, String
    | Integer, Integer
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
    | List {types = types1}, List {types = types2}
    | Tuple {types = types1}, Tuple {types = types2} ->
       solve_lists env unknowns ~f:ok types1 types2
    | Record rec1, Record rec2
    | Header rec1, Header rec2
    | HeaderUnion rec1, HeaderUnion rec2
    | Struct rec1, Struct rec2 ->
       solve_record_type_equality env equiv_vars unknowns rec1 rec2
    | Set ty1, Set ty2 ->
        solve_types env equiv_vars unknowns ty1 ty2
    | Enum enum1, Enum enum2 ->
        solve_enum_type_equality env equiv_vars unknowns enum1 enum2
    | Package pkg1, Package pkg2 ->
        solve_package_type_equality env equiv_vars unknowns pkg1 pkg2
    | Control ctrl1, Control ctrl2
    | Parser ctrl1, Parser ctrl2 ->
        solve_control_type_equality env equiv_vars unknowns ctrl1 ctrl2
    | Extern extern1, Extern extern2 ->
       if extern1.name = extern2.name
       then Some (empty_constraints unknowns)
       else None
    | Action action1, Action action2 ->
        solve_action_type_equality env equiv_vars unknowns action1 action2
    | Function func1, Function func2 ->
        solve_function_type_equality env equiv_vars unknowns func1 func2
    | Constructor ctor1, Constructor ctor2 ->
        solve_constructor_type_equality env equiv_vars unknowns ctor1 ctor2
    | Table table1, Table table2 ->
       if table1.result_typ_name = table2.result_typ_name
       then Some (empty_constraints unknowns)
       else None
    | x, y when casts && cast_ok env x y ->
        Some (empty_constraints unknowns)
    | x, y when casts && cast_ok env y x ->
        Some (empty_constraints unknowns)
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
    | Record _, _
    | Set _, _
    | Header _, _
    | HeaderUnion _, _
    | NewType _, _
    | Struct _, _
    | Enum _, _
    | Control _, _
    | Parser _, _
    | Package _, _
    | Extern _, _
    | Action _, _
    | Function _, _
    | Constructor _, _
    | Table _, _ ->
      None
  end

and sort_fields fields =
  let open RecordType in
  let field_cmp (f1 : field) (f2 : field) =
    String.compare f1.name f2.name
  in
  List.sort ~compare:field_cmp fields

and sort_entries entries =
  let entry_cmp (_, e1: KeyValue.t) (_, e2: KeyValue.t) =
    String.compare (snd e1.key) (snd e2.key)
  in
  List.sort ~compare:entry_cmp entries

(* [type_equality env t1 t2] is true if and only if expression type t1
 * is equivalent to expression type t2 under environment env.
 *  Alpha equivalent types are equal. *)
and type_equality env equiv_vars t1 t2 : bool =
  solve_types ~casts:false env equiv_vars [] t1 t2 <> None

and assert_same_type (env: CheckerEnv.t) info1 info2 (typ1: Type.t) (typ2: Type.t) =
  if type_equality env [] typ1 typ2
  then (typ1, typ2)
  else let info = Info.merge info1 info2 in
    raise_type_error info (Type_Difference (typ1, typ2))

and assert_type_equality env info (t1: Typed.Type.t) (t2: Typed.Type.t) : unit =
  let t1 = reduce_type env t1 in
  let t2 = reduce_type env t2 in
  if type_equality env [] t1 t2
  then ()
  else raise @@ Error.Type (info, Type_Difference (t1, t2))

and compile_time_known_expr (env: CheckerEnv.t) (expr: Prog.Expression.t) : bool =
  match compile_time_eval_expr env expr with
  | Some _ -> true
  | None ->
     match reduce_type env (snd expr).typ with
     | SpecializedType { base = Extern _; _ }
     | Extern _
     | Package _
     | Control _
     | Parser _ -> true
     | _ -> false

and type_expression (env: CheckerEnv.t) (ctx: Typed.ExprContext.t) (exp_info, exp: Expression.t)
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
       let typ, dir = CheckerEnv.find_type_of name env in
       { expr = E.Name name;
         typ = typ;
         dir = dir }
    | ArrayAccess { array; index } ->
       type_array_access env ctx array index
    | BitStringAccess { bits; lo; hi } ->
       type_bit_string_access env ctx bits lo hi
    | List { values } ->
       type_list env ctx values
    | Record { entries } ->
       type_record env ctx entries
    | UnaryOp { op; arg } ->
       type_unary_op env ctx op arg
    | BinaryOp { op; args } ->
       type_binary_op env ctx op args
    | Cast { typ; expr } ->
       type_cast env ctx typ expr
    | TypeMember { typ; name } ->
       type_type_member env ctx typ name
    | ErrorMember name ->
       type_error_member env ctx name
    | ExpressionMember { expr; name } ->
       type_expression_member env ctx expr name
    | Ternary { cond; tru; fls } ->
       type_ternary env ctx cond tru fls
    | FunctionCall { func; type_args; args } ->
       type_function_call env ctx exp_info func type_args args
    | NamelessInstantiation { typ; args } ->
       type_nameless_instantiation env ctx exp_info typ args
    | Mask { expr; mask } ->
       type_mask env ctx expr mask
    | Range { lo; hi } ->
       type_range env ctx lo hi
  in
  (exp_info, pre_expr)

and add_cast env expr typ =
  let expr_casted: Prog.Expression.t =
    fst expr,
    {expr = Cast {typ = typ; expr = expr};
     typ = typ;
     dir = (snd expr).dir}
  in
  if cast_ok env (snd expr).typ typ
  then expr_casted
  else raise_s [%message "cannot cast" ~expr:(expr:Prog.Expression.t) ~typ:(typ: Typed.Type.t)]

and cast_if_needed env (expr: Prog.Expression.t) typ =
  if type_equality env [] (snd expr).typ typ
  then expr
  else match typ with
       | Set elt_typ -> add_cast env (cast_if_needed env expr elt_typ) typ
       | typ -> add_cast env expr typ

and cast_to_same_type (env: CheckerEnv.t) (ctx: Typed.ExprContext.t) (exp1: Expression.t) (exp2: Expression.t) =
  let exp1 = type_expression env ctx exp1 in
  let typ1 = (snd exp1).typ in
  let exp2 = type_expression env ctx exp2 in
  let typ2 = (snd exp2).typ in
  if type_equality env [] typ1 typ2
  then exp1, exp2
  else if cast_ok env typ1 typ2
  then add_cast env exp1 typ2, exp2
  else if cast_ok env typ2 typ1
  then exp1, add_cast env exp2 typ1
  else failwith "cannot cast types so that they agree"

and cast_expression (env: CheckerEnv.t) ctx (typ: Typed.Type.t) (exp_info, exp: Expression.t) =
  let module E = Prog.Expression in
  let typ = reduce_type env typ in
  match exp with
  | String _
  | Cast _ ->
     let exp_typed = type_expression env ctx (exp_info, exp) in
     assert_type_equality env exp_info typ (snd exp_typed).typ;
     exp_typed
  | True
  | False
  | Int _
  | Name _
  | ArrayAccess _
  | BitStringAccess _
  | UnaryOp _
  | TypeMember _
  | ErrorMember _
  | ExpressionMember _
  | FunctionCall _
  | NamelessInstantiation _
  | BinaryOp {op = (_, Op.Shl); args = _}
  | BinaryOp {op = (_, Op.Shr); args = _}
  | BinaryOp {op = (_, Op.PlusPlus); args = _} ->
     let exp_typed = type_expression env ctx (exp_info, exp) in
     cast_if_needed env exp_typed typ
  | List { values } ->
     let rec get_types (typ: Typed.Type.t) =
       match typ with
       | Tuple { types }
       | List { types } ->
          types
       | Header { fields }
       | Struct { fields } ->
          List.map ~f:(fun f -> f.typ) fields
       | Set t ->
          get_types t
       | _ -> [typ]
     in
     let types = get_types typ in
     let values_casted =
       List.zip_exn types values
       |> List.map ~f:(fun (t, v) -> cast_expression env ctx t v)
     in
     let exp_typed: E.t =
       exp_info,
       {expr = List {values = values_casted};
        typ = List {types};
        dir = Directionless}
     in
     cast_if_needed env exp_typed typ
  | Record { entries } ->
     let entries = sort_entries entries in
     let fields =
       match typ with
       | Record {fields}
       | Header {fields}
       | Struct {fields} ->
          sort_fields fields
       | _ -> failwith "can't cast record"
     in
     let cast_entry (field, entry: RecordType.field * KeyValue.t) : Prog.KeyValue.t =
       if field.name <> (snd (snd entry).key)
       then failwith "bad names";
       let value_typed: Prog.Expression.t =
         cast_expression env ctx field.typ (snd entry).value
       in
       fst entry,
       {key = (snd entry).key;
        value = value_typed}
     in
     let entries_casted =
       List.zip_exn fields entries
       |> List.map ~f:cast_entry
     in
     let exp_typed: E.t =
       exp_info,
       {expr = Record {entries = entries_casted};
        typ = Record {fields};
        dir = Directionless}
     in
     cast_if_needed env exp_typed typ
  | BinaryOp {op = (_, Op.Eq) as op; args = (left, right)}
  | BinaryOp {op = (_, Op.NotEq) as op; args = (left, right)}
  | BinaryOp {op = (_, Op.Lt) as op; args = (left, right)}
  | BinaryOp {op = (_, Op.Le) as op; args = (left, right)}
  | BinaryOp {op = (_, Op.Gt) as op; args = (left, right)}
  | BinaryOp {op = (_, Op.Ge) as op; args = (left, right)} ->
     let left_typed, right_typed = cast_to_same_type env ctx left right in
     let exp_typed = exp_info, check_binary_op env op left_typed right_typed in
     cast_if_needed env exp_typed typ
  | BinaryOp {op = (_, Op.Div) as op; args = (left, right)}
  | BinaryOp {op = (_, Op.Mod) as op; args = (left, right)} ->
     let exp_typed = exp_info, type_binary_op env ctx op (left, right) in
     cast_if_needed env exp_typed typ
  | BinaryOp {op; args = (left, right)} ->
     let left_typed = cast_expression env ctx typ left in
     let right_typed =
       if snd op <> Op.Shl && snd op <> Op.Shr
       then cast_expression env ctx typ right
       else type_expression env ctx right
     in
     exp_info, check_binary_op env op left_typed right_typed
  | Ternary { cond; tru; fls } ->
     let cond_typed = cast_expression env ctx Bool cond in
     let tru_typed = cast_expression env ctx typ tru in
     let fls_typed = cast_expression env ctx typ fls in
     exp_info,
     {expr = Ternary {cond = cond_typed; tru = tru_typed; fls = fls_typed};
      typ = typ;
      dir = Directionless}
  | Mask { expr; mask } ->
     let elt_width =
       match reduce_type env typ with
       | Set (Bit {width})
       | Set (NewType {typ = Bit {width}; _})
       | Set (Enum {typ = Some (Bit {width}); _}) ->
          width
       | _ -> failwith "must be a set of bit<w>"
     in
     let elt_type = Typed.Type.Bit {width = elt_width} in
     let expr_typed = cast_expression env ctx elt_type expr in
     let mask_typed = cast_expression env ctx elt_type mask in
     exp_info,
     {expr = Mask {expr = expr_typed; mask = mask_typed};
      typ = Set (elt_type);
      dir = Directionless}
  | Range { lo; hi } ->
     let elt_typ =
       match reduce_type env typ with
       | Set typ -> typ
       | _ -> failwith "must be a set"
     in
     let lo_typed = cast_expression env ctx elt_typ lo in
     let hi_typed = cast_expression env ctx elt_typ hi in
     exp_info,
     {expr = Range {lo = lo_typed; hi = hi_typed};
      typ = typ;
      dir = Directionless}

and translate_direction (dir: Types.Direction.t option) : Typed.direction =
  match dir with
  | Some (_, In) -> In
  | Some (_, Out) -> Out
  | Some (_, InOut) -> InOut
  | None -> Directionless

and eval_to_positive_int env info expr =
  let value =
    expr
    |> type_expression env Constant
    |> compile_time_eval_bigint env
    |> Bigint.to_int_exn
  in
  if value > 0
  then value
  else raise_s [%message "expected positive integer" ~info:(info: Info.t)]

and gen_wildcard env =
  Renamer.freshen_name (CheckerEnv.renamer env) "__wild"

and translate_type' ?(gen_wildcards=false) (env: CheckerEnv.t) (vars: string list) (typ: Types.Type.t) : Typed.Type.t * string list =
  let open Types.Type in
  let ret (t: Typed.Type.t) = t, [] in
  match snd typ with
  | Bool -> ret Bool
  | Error -> ret Error
  | Integer -> ret Integer
  | String -> ret String
  | IntType e -> ret @@ Int {width = eval_to_positive_int env (fst typ) e}
  | BitType e -> ret @@ Bit {width = eval_to_positive_int env (fst typ) e}
  | VarBit e -> ret @@ VarBit {width = eval_to_positive_int env (fst typ) e}
  | TypeName ps -> ret @@ TypeName ps
  | SpecializedType {base; args} ->
     let args, wildcards =
       args
       |> List.map ~f:(translate_type' ~gen_wildcards env vars)
       |> List.unzip
     in
     SpecializedType {base = translate_type env vars base; args},
     List.concat wildcards
  | HeaderStack {header=ht; size=e} ->
     let hdt = translate_type env vars ht in
     let len =
       e
       |> type_expression env Constant
       |> compile_time_eval_bigint env
       |> Bigint.to_int_exn in
     ret @@ Array {typ=hdt; size=len}
  | Tuple tlist ->
     ret @@ Tuple {types = List.map ~f:(translate_type env vars) tlist}
  | Void -> ret Void
  | DontCare ->
     let name = gen_wildcard env in
     TypeName (BareName (fst typ, name)), [name]

and translate_type (env: CheckerEnv.t) (vars: string list) (typ: Types.Type.t) : Typed.Type.t =
  fst (translate_type' env vars typ)

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
      opt_value = param.opt_value;
      variable = param.variable }
  in
  List.map ~f:translate_parameter params

and expr_of_arg (arg: Argument.t): Expression.t option =
  match snd arg with
  | Missing -> None
  | KeyValue { value; _ }
  | Expression { value } -> Some value

and field_cmp (f1: RecordType.field) (f2: RecordType.field) : int =
  String.compare f1.name f2.name

(* Returns true if type typ is a well-formed type *)
and is_well_formed_type env (typ: Typed.Type.t) : bool =
  match saturate_type env typ with
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
  | Array {typ; _} as arr_typ ->
     is_well_formed_type env typ &&
       is_valid_nested_type env arr_typ typ
  | Tuple {types}
  | List {types} ->
     List.for_all ~f:(is_well_formed_type env) types &&
       List.for_all ~f:(is_valid_nested_type env typ) types
  | Set typ ->
     is_well_formed_type env typ
  | Enum {typ; _} ->
    begin match typ with
    | None -> true
    | Some typ -> is_well_formed_type env typ
    end
  | Record {fields; _}
  | HeaderUnion {fields; _}
  | Struct {fields; _} ->
    let field_ok (field: RecordType.field) =
      is_well_formed_type env field.typ &&
        is_valid_nested_type env typ field.typ
    in
    List.for_all ~f:field_ok fields &&
      not (List.contains_dup ~compare:field_cmp fields)
  | Header {fields; _} ->
    let field_ok (field: RecordType.field) =
      is_well_formed_type env field.typ &&
        is_valid_nested_type ~in_header:true env typ field.typ
    in
    List.for_all ~f:field_ok fields &&
      not (List.contains_dup ~compare:field_cmp fields)
  | Action {data_params; ctrl_params} ->
    let res1 : bool = (are_param_types_well_formed env data_params) in
    let res2 : bool = (are_construct_params_types_well_formed env ctrl_params) in
    res1 && res2
  (* Type names *)
  | TypeName name ->
    CheckerEnv.resolve_type_name_opt name env <> None
  | Table {result_typ_name=name} ->
    CheckerEnv.resolve_type_name_opt (BareName (Info.dummy, name)) env <> None
  | NewType {name; typ} ->
    is_well_formed_type env typ
  (* Polymorphic types *)
  | Function {type_params=tps; parameters=ps; return=rt; _} ->
    let env = CheckerEnv.insert_type_vars tps env in
    are_param_types_well_formed env ps && is_well_formed_type env rt
  | Constructor {type_params=tps; wildcard_params=ws; parameters=ps; return=rt} ->
    let env = CheckerEnv.insert_type_vars tps env in
    are_construct_params_types_well_formed env ps && is_well_formed_type env rt
  | Extern {name} ->
    let open ExternMethods in 
    begin match CheckerEnv.find_extern_opt (BareName (Info.dummy, name)) env with
    | Some {type_params = []; _} -> true
    | _ -> false
    end
  | Parser {type_params=tps; parameters=ps;_}
  | Control {type_params=tps; parameters=ps;_} ->
    let env = CheckerEnv.insert_type_vars tps env in
    are_param_types_well_formed env ps
  | Package {type_params=tps; parameters=cps;_} ->
    let env = CheckerEnv.insert_type_vars tps env in
    are_construct_params_types_well_formed  env cps
  (* Type Application *)
  | SpecializedType {base=base_typ; args=typ_args} ->
    let base_typ = saturate_type env base_typ in
    begin match base_typ with
    | Extern {name} ->
      let open ExternMethods in
      let {type_params; methods} =
        CheckerEnv.find_extern (BareName (Info.dummy, name)) env
      in
      List.for_all ~f:(is_well_formed_type env) typ_args
      && List.length type_params = List.length typ_args
    | typ ->
      let type_params = get_type_params typ in
      is_well_formed_type env base_typ
      && List.for_all ~f:(is_well_formed_type env) typ_args
      && List.length type_params = List.length typ_args
    end

and are_param_types_well_formed env (params:Parameter.t list) : bool =
  let open Parameter in
  let check param = is_well_formed_type env param.typ in
  List.for_all ~f:check params

and are_construct_params_types_well_formed env (construct_params: Typed.Parameter.t list) : bool =
  let check (param: Typed.Parameter.t) : bool =
    param.direction = Directionless && is_well_formed_type env param.typ
  in
  List.for_all ~f:check construct_params

and ctx_of_kind (k: FunctionType.kind) : Typed.ParamContext.t =
  match k with
  | Parser -> Runtime Parser
  | Control -> Runtime Control
  | Extern -> Runtime Method
  | Table -> Runtime Control
  | Action -> Runtime Action
  | Function -> Runtime Function
  | Builtin -> Runtime Method

and is_valid_param_type env (ctx: Typed.ParamContext.t) (typ: Typed.Type.t) =
  let typ = reduce_to_underlying_type env typ in
  match ctx with
  | Constructor decl ->
     begin match typ, decl with
     | Package _, Package -> true
     | Package _, _ -> false
     | Parser _, Package
     | Parser _, Parser -> true
     | Parser _, _ -> false
     | Control _, Package
     | Control _, Control -> true
     | Control _, _ -> false
     | Extern _, Package
     | Extern _, Parser
     | Extern _, Control
     | Extern _, Method -> true
     | Extern _, _ -> false
     | Function _, _ -> false
     | Action _, _ -> false
     | Table _, _ -> false
     | Set _, _ -> false
     | _ -> true
     end
  | Runtime decl ->
     begin match typ, decl with
     | Package _, _ -> false
     | Parser _, _ -> false
     | Control _, _ -> false
     | Extern _, Parser
     | Extern _, Control
     | Extern _, Method -> true
     | Extern _, _ -> false
     | Table _, _ -> false
     | Set _, _ -> false
     | Action _, _ -> false
     | Function _, _ -> false
     | _ -> true
     end

and is_valid_param_type_kind env (kind: FunctionType.kind) (typ: Typed.Type.t) =
    let open ParamContext in
  match kind with
  | Parser -> is_valid_param_type env (Runtime Parser) typ
  | Control -> is_valid_param_type env (Runtime Control) typ
  | Extern -> is_valid_param_type env (Runtime Method) typ
  | Table -> false
  | Action -> is_valid_param_type env (Runtime Action) typ
  | Function -> is_valid_param_type env (Runtime Function) typ
  | Builtin -> is_valid_param_type env (Runtime Method) typ

and is_valid_nested_type ?(in_header=false) (env: CheckerEnv.t) (outer_type: Typed.Type.t) (inner_type: Typed.Type.t) =
  let inner_type = reduce_to_underlying_type env inner_type in
  match reduce_to_underlying_type env outer_type with
  | Header _ ->
     begin match inner_type with
     | Bit _
     | Int _
     | VarBit _
     | Bool
     | Enum {typ = Some _; _} ->
        true
     | Struct {fields} ->
        List.for_all fields
          ~f:(fun f -> is_valid_nested_type ~in_header:true env inner_type f.typ)
     | _ ->
        false
     end
  | HeaderUnion _ ->
     begin match inner_type with
     | Header _ -> true
     | _ -> false
     end
  | Struct _
  | List _
  | Tuple _ ->
     begin match inner_type with
     | TypeName _
     | Bit _
     | Int _
     | Enum _
     | Bool -> true
     | Struct {fields} ->
        not in_header ||
          List.for_all fields
            ~f:(fun f -> is_valid_nested_type ~in_header env inner_type f.typ)
     | Header _
     | VarBit _
     | Error
     | Array _
     | HeaderUnion _
     | Tuple _ ->
        not in_header
     | _ ->
        false
     end
  | Array _ ->
     begin match inner_type with
     | Header _ -> true
     | HeaderUnion _ -> true
     | _ -> false
     end
  | _ -> false

and is_compile_time_only_type env typ =
  match reduce_to_underlying_type env typ with
  | Integer
  | String -> true
  | _ -> false


and validate_param env ctx (typ: Typed.Type.t) dir info =
  if is_extern env typ && not (eq_dir dir Directionless)
  then raise_s [%message "Externs as parameters must be directionless"];
  if is_compile_time_only_type env typ && not (eq_dir dir Directionless)
  then raise_s [%message "parameters of this type must be directionless" ~typ:(typ: Typed.Type.t)];
  if not (is_well_formed_type env typ)
  then raise_s [%message "Parameter type is not well-formed" ~info:(info:Info.t) ~typ:(typ:Typed.Type.t)];
  if not (is_valid_param_type env ctx typ)
  then raise_s [%message "Type cannot be passed as a parameter" ~info:(info:Info.t)];

and type_param' ?(gen_wildcards=false) env (ctx: Typed.ParamContext.t) (param_info, param : Types.Parameter.t) : Typed.Parameter.t * string list =
  let typ, wildcards = translate_type' ~gen_wildcards env [] param.typ in
  let env = CheckerEnv.insert_type_vars wildcards env in
  let dir = translate_direction param.direction in
  validate_param env ctx typ dir param_info;
  let opt_value =
    match param.opt_value with
    | Some value ->
       if eq_dir dir Directionless || eq_dir dir In
       then Some value
       else raise_s [%message "Only directionless and in parameters may have default arguments" ~param_info:(param_info:Info.t)]
    | None -> None
  in
  { annotations = param.annotations;
    direction = translate_direction param.direction;
    typ = typ;
    variable = param.variable;
    opt_value = opt_value },
  wildcards

and type_param env ctx param =
  fst (type_param' env ctx param)

and type_params' ?(gen_wildcards=false) env ctx params =
  let params, wildcard_lists =
    params
    |> List.map ~f:(type_param' ~gen_wildcards env ctx)
    |> List.unzip
  in
  params, List.concat wildcard_lists

and type_params env ctx param =
  fst (type_params' env ctx param)

and type_constructor_param env decl_kind (param: Types.Parameter.t) : Typed.Parameter.t =
  if (snd param).direction <> None
  then raise_s [%message "Constructor parameters must be directionless"
                   ~param:(param: Types.Parameter.t)];
  type_param env (Constructor decl_kind) param

and type_constructor_params env ctx params =
  List.map ~f:(type_constructor_param env ctx) params

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
and type_array_access env ctx (array: Types.Expression.t) index : Prog.Expression.typed_t =
  let array_typed = type_expression env ctx array in
  let array_typ = (snd array_typed).typ in
  let idx_typed = type_expression env ctx index in
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
and type_bit_string_access env ctx bits lo hi : Prog.Expression.typed_t =
  let bits_typed = type_expression env ctx bits in
  match reduce_type env (snd bits_typed).typ with
  | Int { width }
  | Bit { width } ->
     let lo_typed = type_expression env Constant lo in
     let typ_lo = saturate_type env (snd lo_typed).typ in
     let hi_typed = type_expression env Constant hi in
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
     raise_s [%message "expected bit type, got"
                 ~expr:(bits: Types.Expression.t)
                 ~typ:(typ: Typed.Type.t)]

(* Section 8.11
 * ------------
 *
 *      1 <= i <= n; Δ, T, Γ |- xi : ti
 * ------------------------------------------
 * Δ, T, Γ |- { x1, ..., xn } : (t1, ..., tn)
 *
 *)
and type_list env ctx values : Prog.Expression.typed_t =
  let typed_exprs = List.map ~f:(type_expression env ctx) values in
  let types = List.map ~f:(fun e -> (snd e).typ) typed_exprs in
  { expr = List { values = typed_exprs };
    typ = Type.List { types };
    dir = Directionless }

and type_key_val env ctx ((info, entry): Types.KeyValue.t) : Prog.KeyValue.t =
  info,
  { key = entry.key;
    value = type_expression env ctx entry.value }

and type_record env ctx entries : Prog.Expression.typed_t =
  let entries_typed = List.map ~f:(type_key_val env ctx) entries in
  let rec_typed = Prog.Expression.Record { entries = entries_typed } in
  let kv_to_field (kv: Prog.KeyValue.t) : Typed.RecordType.field =
    { name = snd (snd kv).key; typ = (snd (snd kv).value).typ }
  in
  let fields = List.map ~f:kv_to_field entries_typed in
  { expr = rec_typed; typ = Record { fields; }; dir = Directionless }

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
and type_unary_op env ctx op arg =
  let arg_typed = type_expression env ctx arg in
  let arg_typ = (snd arg_typed).typ in
  begin match snd op with
  | Not    -> assert_bool (info arg) arg_typ |> ignore
  | BitNot -> assert_runtime_numeric (info arg) arg_typ |> ignore
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
  match saturate_type env (snd l).typ, saturate_type env (snd r).typ with
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

and coerce_binary_op_args env ctx op l r =
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
  let l_typed = type_expression env ctx l in
  let r_typed = type_expression env ctx r in
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
  if op <> Op.Shl && op <> Op.Shr && op <> Op.PlusPlus
  then cast_opt cast_type_l l_typed, cast_opt cast_type_r r_typed
  else l_typed, r_typed

(* TODO: Checking if two values of this type be compared for equality
 * (==) or inequality (!=).
 *)
and type_has_equality_tests env (typ: Typed.Type.t) =
  match reduce_type env typ with
  | Bool
  | String
  | Integer
  | Int _
  | Bit _
  | VarBit _
  | Error
  | MatchKind ->
     true
  | Array { typ; _ }
  | Set typ ->
     type_has_equality_tests env typ
  | List { types }
  | Tuple { types } ->
     List.for_all ~f:(type_has_equality_tests env) types
  | Header { fields; _ }
  | HeaderUnion { fields; _ }
  | Struct { fields; _ } ->
     List.for_all ~f:(fun field -> type_has_equality_tests env field.typ) fields
  | NewType { typ; _ } ->
     type_has_equality_tests env typ
  | Enum { typ; _ } ->
     begin match typ with
     | Some typ -> type_has_equality_tests env typ
     | None -> true
     end
  | TypeName name ->
     failwith "type name in saturated type?"
  | _ ->
     false

and is_nonnegative_numeric env (e: Prog.Expression.t) : bool =
  match (snd e).typ with
  | Integer ->
     let e_value = compile_time_eval_bigint env e in
     Bigint.(e_value >= zero)
  | Bit _ -> true
  | _ -> false

and is_positive_numeric env (e: Prog.Expression.t) : bool =
  match (snd e).typ with
  | Integer ->
     let e_value = compile_time_eval_bigint env e in
     Bigint.(e_value > zero)
  | Bit _ ->
     begin match compile_time_eval_expr env e with
     | None ->
        true (* XXX: bit<> values can be zero... *)
     | Some value ->
        match bigint_of_value value with
        | Some e_value -> Bigint.(e_value > zero)
        | None ->
           raise_s [%message "bit<> evaluated to non numerical value?"
                       ~expr:(e: Prog.Expression.t) ~value:(value: Prog.Value.value)]
     end
  | _ -> false

and check_div_args env left_arg right_arg =
  if is_nonnegative_numeric env left_arg && is_positive_numeric env right_arg
  then ()
  else raise_s [%message "arguments to division must be positive"
                   ~divisor:(right_arg:Prog.Expression.t)
                   ~dividend:(left_arg:Prog.Expression.t)];

and type_binary_op env ctx (op_info, op) (l, r) : Prog.Expression.typed_t =
  let typed_l, typed_r = coerce_binary_op_args env ctx op l r in
  check_binary_op env (op_info, op) typed_l typed_r

and check_binary_op env (op_info, op) typed_l typed_r : Prog.Expression.typed_t =
  let open Op in
  let open Prog.Expression in
  let open Typed.Type in
  let l_typ = reduce_enums_in_type env (snd typed_l).typ in
  let r_typ = reduce_enums_in_type env (snd typed_r).typ in
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
       | _, _ -> raise_s [%message "this binop unimplemented"
                             ~l_typ:(l_typ:Typed.Type.t)
                             ~r_typ:(r_typ:Typed.Type.t)]
       end
    | Eq | NotEq ->
       if type_equality env [] l_typ r_typ
       then if type_has_equality_tests env l_typ
            then Type.Bool
            else raise_s [%message "bad error message: type doesn't have equality tests (== and !=)"
                             ~l_typ:(l_typ:Typed.Type.t)
                             ~r_typ:(r_typ:Typed.Type.t)]
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
       | Int { width = l }, Int { width = r } when l = r -> Int { width = l }
       | Bit { width = _ }, _ -> raise_mismatch (info typed_r) "unsigned int" r_typ
       | _, _ -> raise_mismatch (info typed_l) "unsigned int" l_typ
       end
    (* Bitstring concatentation is defined on any two bitstrings *)
    | PlusPlus ->
       begin match l_typ, r_typ with
       | Bit { width = l }, Bit { width = r }
       | Bit { width = l }, Int { width = r } -> Bit { width = l + r }
       | Int { width = l }, Bit { width = r }
       | Int { width = l }, Int { width = r } -> Int { width = l + r }
       | Int { width = _ }, _
       | Bit { width = _ }, _ -> raise_mismatch (info typed_r) "bit<> or int<>" r_typ
       | _, _ -> raise_mismatch (info typed_l) "bit<> or int<>" l_typ
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
       | Integer, Integer ->
          check_div_args env typed_l typed_r;
          Integer
       | Bit { width = l_width }, Bit { width = r_width } when l_width = r_width ->
          check_div_args env typed_l typed_r;
          Bit { width = l_width }
       | Integer, _ -> raise_mismatch (info typed_r) "arbitrary precision integer" r_typ
       | _, _ -> raise_mismatch (info typed_l) "arbitrary precision integer" l_typ
       end
    | Shl | Shr ->
       begin match l_typ, is_nonnegative_numeric env typed_r with
       | Bit _, true
       | Int _, true -> l_typ
       | Integer, true ->
          if compile_time_known_expr env typed_r
          then l_typ
          else raise_s [%message "bad right hand argument to shift" ~typed_r:(typed_r: Prog.Expression.t)]
       | _, true -> raise_s [%message "bad left hand argument to shift" ~l_typ:(l_typ: Typed.Type.t)]
       | _ -> raise_s [%message "bad right hand argument to shift" ~typed_r:(typed_r: Prog.Expression.t)]
       end
  in
  { expr = BinaryOp { op = (op_info, op); args = (typed_l, typed_r) };
    typ = typ;
    dir = dir }

(* See section 8.9.2 "Explicit casts" *)
and cast_ok ?(explicit = false) env original_type new_type =
  let original_type = saturate_type env original_type in
  let new_type = saturate_type env new_type in
  let open Typed.Type in
  match original_type, new_type with
  | Set t1, Set t2 ->
     type_equality env [] t1 t2
  | t1, Set t2 ->
     not explicit &&
     type_equality env [] t1 t2
  | Bit { width = 1 }, Bool
  | Bool, Bit { width = 1 } ->
     explicit
  | Int {width = width1}, Bit {width = width2}
  | Bit {width = width1}, Int {width = width2} ->
     explicit && width1 = width2
  | Bit { width = width1 }, Bit { width = width2 }
  | Int { width = width1 }, Int { width = width2 } ->
     width1 = width2 || explicit
  | Integer, Bit { width = _ }
  | Integer, Int { width = _ } ->
     true
  | Enum { name; typ = Some t; members }, Enum {typ = Some t'; _}
  | Enum { name; typ = Some t; members }, t'
  | t', Enum { name; typ = Some t; members } ->
     type_equality env [] t t'
  | NewType { name = name1; typ = typ1 },
    NewType { name = name2; typ = typ2 } ->
     type_equality env [] typ1 new_type
     || type_equality env [] original_type typ2
  | NewType { name; typ }, t ->
     cast_ok ~explicit env typ t
  | t, NewType { name; typ } ->
     cast_ok ~explicit env t typ
  | List types1, Tuple types2 ->
     type_equality env [] (Tuple types1) (Tuple types2)
  | List types1, Header rec2
  | List types1, Struct rec2 ->
     let types2 = List.map ~f:(fun f -> f.typ) rec2.fields in
     casts_ok ~explicit env types1.types types2 ||
       type_equality env [] (Tuple types1) (Tuple {types = types2})
  | Record rec1, Header rec2
  | Record rec1, Struct rec2 ->
     let types1 = List.map ~f:(fun f -> f.typ) rec1.fields in
     let types2 = List.map ~f:(fun f -> f.typ) rec2.fields in
     casts_ok ~explicit env types1 types2 ||
       type_equality env [] (Record rec1) (Record rec2)
  | Header rec1, Header rec2
  | Struct rec1, Struct rec2 ->
     let types1 = List.map ~f:(fun f -> f.typ) rec1.fields in
     let types2 = List.map ~f:(fun f -> f.typ) rec2.fields in
     casts_ok ~explicit env types1 types2 ||
       type_equality env [] (Record rec1) (Record rec2)
  | _ -> not explicit && original_type = new_type

and casts_ok ?(explicit = false) env original_types new_types =
  match List.zip original_types new_types with
  | Ok pairs ->
     List.for_all pairs ~f:(fun (orig_typ, new_typ) ->
         cast_ok ~explicit env orig_typ new_typ)
  | Unequal_lengths ->
     false

(* Section 8.9 *)
and type_cast env ctx typ expr : Prog.Expression.typed_t =
  let expr_typed = type_expression env ctx expr in
  let expr_type = saturate_type env (snd expr_typed).typ in
  let new_type = translate_type env [] typ in
  let new_type_sat = saturate_type env new_type in
  if not (is_well_formed_type env new_type)
  then raise_s [%message "ill-formed type" ~typ:(new_type:Typed.Type.t)];
  if cast_ok ~explicit:true env expr_type new_type_sat
  then { dir = Directionless; typ = new_type; expr = Cast {typ = new_type; expr = expr_typed} }
  else raise_s [%message "illegal explicit cast"
                   ~old_type:(expr_type: Typed.Type.t)
                   ~new_type:(new_type_sat: Typed.Type.t)]

(* ? *)
and type_type_member env ctx typ name : Prog.Expression.typed_t =
   let real_name = real_name_for_type_member env typ name in
   let full_type, dir = CheckerEnv.find_type_of real_name env in
   { expr = TypeMember { typ;
                         name = name };
     typ = full_type;
     dir }

(* Section 8.2
 * -----------
 *
 *       (e, error) ∈ T
 * --------------------------
 * Δ, T, Γ |- error.e : error
 *
 *)
and type_error_member env ctx name : Prog.Expression.typed_t =
  let (e, _) = CheckerEnv.find_type_of (BareName (Info.dummy, "error." ^ (snd name))) env in
  if e <> Type.Error then failwith "Error member not an error?";
  { expr = ErrorMember name;
    typ = Type.Error;
    dir = Directionless }

and header_methods typ =
  let fake_fields: RecordType.field list =
    [{name = "isValid";
      typ = Function {type_params = []; parameters = []; kind = Builtin; return = Bool}}]
  in
  match typ with
  | Type.Header { fields; _ } -> fake_fields
  | _ -> []

and type_expression_member_builtin env (ctx: Typed.ExprContext.t) info typ name : Typed.Type.t =
  let open Typed.Type in
  let fail () =
    raise_unfound_member info (snd name) in
  match typ with
  | Array { typ; _ } ->
     let idx_typ = Bit { width = 32 } in
     begin match snd name with
     | "size"
     | "lastIndex" ->
        idx_typ
     | "next"
     | "last" ->
        begin match ctx with
        | ParserState ->
           typ
        | _ -> failwith "can only use .last or .next within a parser"
        end
     | _ -> fail ()
     end
  | _ -> fail ()

and type_expression_member_function_builtin env info typ name : Typed.Type.t option =
  let open Typed.Type in
  match typ with
  | Control { type_params = []; parameters = ps; _ } ->
     begin match snd name with
     | "apply" ->
        Some (Function { type_params = [];
                         parameters = ps;
                         kind = Control;
                         return = Void })
     | _ -> None
     end
  | Parser { type_params = []; parameters = ps; _ } ->
     begin match snd name with
     | "apply" ->
        Some (Function { type_params = [];
                         parameters = ps;
                         kind = Parser;
                         return = Void })
     | _ -> None
     end
  | Table { result_typ_name } ->
     begin match snd name with
     | "apply" ->
        Some (Function { type_params = [];
                         parameters = [];
                         kind = Table;
                         return = TypeName (BareName (Info.dummy, result_typ_name)) })
     | _ -> None
     end
  | Struct _ ->
     begin match snd name with
     | "minSizeInBits" ->
        Some (Function { type_params = []; kind = Builtin; parameters = []; return = Integer })
     | "minSizeInBytes" ->
        Some (Function { type_params = []; kind = Builtin; parameters = []; return = Integer })
     | _ -> None
     end
  | Header _ ->
     begin match snd name with
     | "isValid" ->
        Some (Function { type_params = []; kind = Builtin; parameters = []; return = Bool })
     | "setValid"
     | "setInvalid" ->
        Some (Function { type_params = []; kind = Builtin; parameters = []; return = Void })
     | "minSizeInBits" ->
        Some (Function { type_params = []; kind = Builtin; parameters = []; return = Integer })
     | "minSizeInBytes" ->
        Some (Function { type_params = []; kind = Builtin; parameters = []; return = Integer })
     | _ -> None
     end
  | Array { typ; _ } ->
     begin match snd name with
     | "minSizeInBits" ->
        Some (Function { type_params = []; kind = Builtin; parameters = []; return = Integer })
     | "minSizeInBytes" ->
        Some (Function { type_params = []; kind = Builtin; parameters = []; return = Integer })
     | "push_front"
     | "pop_front" ->
        let parameters: Typed.Parameter.t list =
          [{ variable = Info.dummy, "count";
             typ = Integer;
             direction = Directionless;
             opt_value = None;
             annotations = [] }]
        in
        Some (Function { type_params = []; kind = Builtin; parameters; return = Void })
     | _ -> None
     end
  | HeaderUnion _ ->
     begin match snd name with
     | "isValid" ->
        Some (Function { type_params = []; parameters = []; kind = Builtin; return = Bool })
     | "minSizeInBits" ->
        Some (Function { type_params = []; parameters = []; kind = Builtin; return = Integer })
     | "minSizeInBytes" ->
        Some (Function { type_params = []; parameters = []; kind = Builtin; return = Integer })
     | _ -> None
     end
  | _ -> None

(* Sections 6.6, 8.14 *)
and type_expression_member env ctx expr name : Prog.Expression.typed_t =
  let typed_expr = type_expression env ctx expr in
  let expr_typ = reduce_type env (snd typed_expr).typ in
  let open RecordType in
  let methods = header_methods (snd typed_expr).typ in
  let rec find_type (expr_typ: Typed.Type.t) =
    match expr_typ with
    | Header {fields=fs;_}
    | HeaderUnion {fields=fs;_}
    | Struct {fields=fs;_} ->
       let fs = fs @ methods in
       let matches (f : field) = f.name = snd name in
       begin match List.find ~f:matches fs with
       | Some field -> field.typ
       | None -> type_expression_member_builtin env ctx (info expr) expr_typ name
       end
    | SpecializedType { base = Extern { name = extern_name }; args } ->
       begin match CheckerEnv.find_extern_opt (BareName (Info.dummy, extern_name)) env with
       | Some { type_params; methods } ->
          let extended_env = CheckerEnv.insert_types (List.zip_exn type_params args) env in
          let open ExternMethods in
          let matches m = m.name = snd name in
          begin match List.find ~f:matches methods with
          | Some m -> reduce_type extended_env (Type.Function m.typ)
          | None -> type_expression_member_builtin env ctx (info expr) expr_typ name
          end
       | None -> raise_s [%message "methods not found for extern" ~extern_name]
       end
    | Extern { name = extern_name } ->
       find_type (SpecializedType { base = Extern { name = extern_name }; args = [] })
    | _ -> type_expression_member_builtin env ctx (info expr) expr_typ name
  in
  let typ = find_type expr_typ in
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
and type_ternary env ctx cond tru fls : Prog.Expression.typed_t =
  let cond_typed = type_expression env ctx cond in
  assert_bool (info cond) (snd cond_typed).typ |> ignore;
  let fls_typed = type_expression env ctx fls in
  let tru_typed = type_expression env ctx tru in
  assert_same_type env (info tru) (info fls) (snd tru_typed).typ (snd fls_typed).typ |> ignore;
  match (snd tru_typed).typ with
  | Type.Integer ->
     (* TODO this is allowed if cond is compile-time known *)
     failwith "Conditional expressions may not have arbitrary width integer type"
  | t ->
     { expr = Ternary { cond = cond_typed; tru = tru_typed; fls = fls_typed };
       typ = t;
       dir = Directionless }

and match_params_to_args call_site_info params args : (Typed.Parameter.t * Expression.t option) list =
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
     match_positional_args_to_params call_site_info params args
  | Some `Positional ->
     match_positional_args_to_params call_site_info params args
  | Some `Named ->
     match_named_args_to_params call_site_info params args

and match_positional_args_to_params call_site_info params args =
  let conv param arg =
    let open Types.Argument in
    match arg with
    | Expression { value } -> param, Some value
    | Missing -> param, None
    | _ -> failwith "expected positional argument"
  in
  let rec go (params: Typed.Parameter.t list) (args: Types.Argument.pre_t list) =
    match params, args with
    | param :: params, arg :: args ->
       conv param arg :: go params args
    | param :: params, [] ->
       begin match param.opt_value with
       | Some expr -> conv param (Expression {value = expr}) :: go params args
       | None ->
          if Parameter.is_optional param
          then conv param Missing :: go params args
          else raise_s [%message "missing argument for parameter"
                           ~info:(call_site_info: Info.t)
                           ~param:(param: Typed.Parameter.t)]
       end
    | [], arg :: args ->
       raise_s [%message "too many arguments"
                   ~info:(call_site_info: Info.t)]
    | [], [] -> []
  in
  go params args

and match_named_args_to_params call_site_info (params: Typed.Parameter.t list) args =
  let open Types.Argument in
  let open Typed.Parameter in
  match params with
  | p :: params ->
     let right_arg = function
       | KeyValue { key; value } ->
          if snd p.variable = snd key
          then Some value
          else None
       | _ -> None
     in
     let maybe_arg_for_p, other_args =
       Util.find_map_and_drop ~f:right_arg args
     in
     begin match maybe_arg_for_p, p.opt_value with
     | Some arg_for_p, _
     | None, Some arg_for_p ->
        (p, Some arg_for_p) :: match_named_args_to_params call_site_info params other_args
     | None, None ->
        if is_optional p
        then (p, None) :: match_named_args_to_params call_site_info params other_args
        else raise_s [%message "parameter has no matching argument"
                         ~call_site:(call_site_info: Info.t)
                         ~param:(p: Typed.Parameter.t)]
     end
  | [] ->
     match args with
     | [] -> []
     | a :: rest ->
        raise_s [%message "too many arguments supplied at call site"
                    ~info:(call_site_info: Info.t)
                    ~unused_args:(args : Types.Argument.pre_t list)]

and is_lvalue env (expr_typed: Prog.Expression.t) =
  match (snd expr_typed).expr with
  | Name name ->
     let typ = reduce_type env (snd expr_typed).typ in
     let const = CheckerEnv.find_const_opt name env in
     begin match (snd expr_typed).dir, typ with
     | In, _
     | Directionless, _ -> false
     | _, Extern _ -> false
     | _, Integer -> false
     | _, String -> false
     | _ ->
        begin match const with
        | Some constant -> false
        | _ -> true
        end
     end
  | ExpressionMember { expr = lvalue; _ }
  | ArrayAccess { array = lvalue; _ }
  | BitStringAccess { bits = lvalue; _ } ->
     is_lvalue env lvalue
  | _ -> false

and check_direction env dir (arg_typed: Prog.Expression.t) =
  match dir with
  | Directionless -> ()
  | In ->
     begin match (snd arg_typed).typ with
     | Extern _ ->
        raise_s [%message "externs should always be directionless"]
     | _ -> ()
     end
  | Out
  | InOut ->
     if not @@ is_lvalue env arg_typed
     then raise_s [%message "expected l-value, got expr:" ~expr:(arg_typed: Prog.Expression.t)];
     if (snd arg_typed).dir = In
     then raise_s [%message "in parameter passed as out parameter" ~expr:(arg_typed: Prog.Expression.t)]

(* Section 8.17: Typing Function Calls *)
and cast_param_arg env ctx call_info (param, expr: Typed.Parameter.t * Expression.t option) =
  match expr with
  | Some expr ->
     let typed_arg = cast_expression env ctx param.typ expr in
     check_direction env param.direction typed_arg;
     param, Some typed_arg
  | None ->
     if param.direction <> Out && not (Parameter.is_optional param)
     then raise_s [%message "don't care argument (underscore) provided for non-out parameter"
                      ~call_site:(call_info: Info.t)
                      ~param:(snd param.variable)]
     else if param.typ = Type.Void
     then raise_s [%message "could not infer valid type for don't care argument"]
     else param, None

and call_ok (ctx: ExprContext.t) (fn_kind: Typed.FunctionType.kind) : bool =
  begin match ctx, fn_kind with
  | ParserState, Parser -> true
  | _, Parser -> false
  | ApplyBlock, Control -> true
  | _, Control -> false
  | Function, Extern -> false
  | _, Extern -> true
  | ApplyBlock, Table -> true
  | _, Table -> false
  | ApplyBlock, Action -> true
  | Action, Action -> true
  | TableAction, Action -> true
  | _, Action -> false
  | ParserState, Function -> true
  | ApplyBlock, Function -> true
  | Action, Function -> true
  | Function, Function -> true
  | DeclLocals, Function -> true
  | _, Function -> false
  | _, Builtin -> true
  end

and type_function_call env ctx call_info func type_args args : Prog.Expression.typed_t =
  let open Prog.Expression in
  let func_typed = resolve_function_overload env ctx func args in
  let func_type = (snd func_typed).typ in
  let type_params, params, kind, return_type =
    match func_type with
    | Function { type_params; parameters; kind; return } ->
       type_params, parameters, kind, return
    | Action { data_params; ctrl_params } ->
       let params = data_params @ ctrl_params in
       [], params, Action, Type.Void
    | _ ->
       raise_s [%message "don't know how to typecheck function call with function"
                   ~fn:(func: Types.Expression.t)
                   ~fn_type:(func_type: Typed.Type.t)]
  in
  let type_args = List.map ~f:(translate_type_opt env []) type_args in
  let params_args = match_params_to_args (fst func) params args in
  let type_params_args =
    match List.zip type_params type_args with
    | Ok v -> v
    | Unequal_lengths ->
       match type_args with
       | [] -> List.map ~f:(fun v -> v, None) type_params
       | _ -> failwith "mismatch in type arguments"
  in
  let type_params_args =
    infer_type_arguments env ctx return_type type_params_args params_args type_params_args
  in
  let env = CheckerEnv.insert_types type_params_args env in
  let subst_param_arg ((param:Typed.Parameter.t), arg) =
    let param = {param with typ = saturate_type env param.typ} in
    validate_param env (ctx_of_kind kind) param.typ param.direction call_info;
    param, arg
  in
  let params_args' = List.map params_args ~f:subst_param_arg in
  let typed_params_args = List.map ~f:(cast_param_arg env ctx call_info) params_args' in
  let out_type_args = List.map ~f:snd type_params_args in
  let out_args = List.map ~f:snd typed_params_args in
  let typ = saturate_type env return_type in
  let call = Prog.Expression.FunctionCall { func = func_typed;
                                            type_args = out_type_args;
                                            args = out_args }
  in
  if call_ok ctx kind
  then { expr = call; typ = typ; dir = Directionless }
  else raise_s [%message "call not allowed" ~call_info:(call_info: Info.t)
         ~ctx:(ctx: ExprContext.t)]

and select_constructor_params env info methods args =
  let matching_constructor (proto: Prog.MethodPrototype.t) =
    match snd proto with
    | Constructor { params; _ } ->
       begin try
         let _ = match_params_to_args info params args in
         true
         with _ -> false
       end
    | Method _ -> false
    | AbstractMethod _ -> false
  in
  match List.find ~f:matching_constructor methods with
  | Some (_, Constructor { params; _ }) ->
     Some (match_params_to_args info params args)
  | _ -> None

and get_decl_type_params (decl : Prog.Declaration.t) : P4String.t list =
  let open Prog.Declaration in
  match snd decl with
  | ExternObject { type_params; _ }
  | Parser { type_params; _ }
  | ParserType { type_params; _ }
  | Control { type_params; _ }
  | ControlType { type_params; _ }
  | PackageType { type_params; _ } ->
     type_params
  | _ ->
     []

and get_decl_constructor_params env info (decl : Prog.Declaration.t) args =
  let open Prog.Declaration in
  let params_maybe_args =
    match snd decl with
    | PackageType { params = constructor_params; _ }
    | Parser { constructor_params; _ }
    | Control { constructor_params; _ } ->
       Some (match_params_to_args info constructor_params args)
    | ExternObject { methods; _ } ->
       select_constructor_params env info methods args
    | _ ->
       None
  in
  match params_maybe_args with
  | Some ps -> ps
  | None ->
     raise_s [%message "type does not have constructor for these arguments"
                 ~typ:(decl: Prog.Declaration.t) ~args:(args: Argument.t list)]

and overload_param_count_ok (args: Argument.t list) (params: Typed.Parameter.t list) =
  match params, args with
  | param :: params, arg :: args ->
     overload_param_count_ok args params
  | param :: params, [] ->
     (Typed.Parameter.is_optional param || param.opt_value <> None)
     && overload_param_count_ok [] params
  | [], arg :: args ->
     false
  | [], [] ->
     true

and overload_param_names_ok (arg_names: string list) (params: Typed.Parameter.t list) =
  let param_has_arg (param: Typed.Parameter.t) =
    Typed.Parameter.is_optional param ||
    param.opt_value <> None ||
      List.exists arg_names
        ~f:(fun arg_name -> arg_name = snd param.variable)
  in
  let arg_has_param (arg_name: string) =
    List.exists params
      ~f:(fun param -> arg_name = snd param.variable)
  in
  List.for_all params ~f:param_has_arg && List.for_all arg_names ~f:arg_has_param

and resolve_constructor_overload_by ~f:(f: Typed.Parameter.t list -> bool) env type_name =
  let ok : Typed.Type.t -> bool =
    function
    | Constructor { parameters; _ } -> f parameters
    | _ -> false
  in
  let candidates = CheckerEnv.find_types_of type_name env in
  match
    candidates
    |> List.map ~f:fst
    |> List.find ~f:ok
  with
  | Some (Typed.Type.Constructor c) -> c
  | ctor -> raise_s [%message "bad constructor type or no matching constructor"
                     ~name:(type_name: Types.name)
                     ~ctor:(ctor:Typed.Type.t option)
                     ~candidates:(candidates:(Typed.Type.t * Typed.direction) list)]

and resolve_constructor_overload env type_name args : ConstructorType.t =
  let arg_name arg =
    match snd arg with
    | Argument.KeyValue {key; _} -> Some (snd key)
    | _ -> None
  in
  match list_option_flip (List.map ~f:arg_name args) with
  | Some arg_names ->
     resolve_constructor_overload_by ~f:(overload_param_names_ok arg_names) env type_name
  | None ->
     resolve_constructor_overload_by ~f:(overload_param_count_ok args) env type_name

and resolve_function_overload_by ~f env ctx func : Prog.Expression.t =
  let open Types.Expression in
  fst func,
  match snd func with
  | Name func_name ->
     let ok : Typed.Type.t -> bool =
       function
       | Function { parameters; _ } -> f parameters
       | _ -> false
     in
     begin match
       CheckerEnv.find_types_of func_name env
       |> List.map ~f:fst
       |> List.find ~f:ok
     with
     | Some typ -> { expr = Name func_name; typ; dir = Directionless }
     | _ -> snd @@ type_expression env ctx func
     end
  | ExpressionMember { expr; name } ->
     let expr_typed = type_expression env ctx expr in
     let prog_member = Prog.Expression.ExpressionMember { expr = expr_typed;
                                                          name = name }
     in
     let rec resolve_by_type typ : Prog.Expression.typed_t =
       begin match reduce_type env typ with
       | SpecializedType { base = Extern { name = extern_name }; args } ->
          let { expr; typ; dir }: Prog.Expression.typed_t =
            resolve_by_type (Extern {name = extern_name})
          in
          let { type_params; methods }: ExternMethods.t =
            CheckerEnv.find_extern (BareName (Info.dummy, extern_name)) env
          in 
          let env_with_args =
            CheckerEnv.insert_types (List.zip_exn type_params args) env
          in
          let typ = reduce_type env_with_args typ in
          {expr; typ; dir}
       | Extern { name = extern_name } ->
          let open ExternMethods in
          let { type_params; methods } = CheckerEnv.find_extern (BareName (Info.dummy, extern_name)) env in 
          let works meth =
            meth.name = snd name && f meth.typ.parameters
          in
          begin match List.find ~f:works methods with
          | Some p ->
             { expr = prog_member;
               typ = Function p.typ;
               dir = Directionless }
          | None -> failwith "couldn't find matching method"
          end
       | _ ->
          let typ = saturate_type env (snd expr_typed).typ in
          begin match type_expression_member_function_builtin env info typ name with
          | Some typ ->
             { expr = prog_member;
               typ;
               dir = Directionless }
          | None ->
             snd @@ type_expression env ctx func
          end
       end
     in
     resolve_by_type (snd expr_typed).typ
  | _ -> snd @@ type_expression env ctx func

and resolve_function_overload env ctx type_name args =
  let arg_name arg =
    match snd arg with
    | Argument.KeyValue {key; _} -> Some (snd key)
    | _ -> None
  in
  match list_option_flip (List.map ~f:arg_name args) with
  | Some arg_names ->
     resolve_function_overload_by ~f:(overload_param_names_ok arg_names) env ctx type_name
  | None ->
     resolve_function_overload_by ~f:(overload_param_count_ok args) env ctx type_name

and type_constructor_invocation env ctx info decl_name type_args args : Prog.Expression.t list * Typed.Type.t =
  let open Typed.ConstructorType in
  let type_args = List.map ~f:(translate_type_opt env []) type_args in
  let constructor_type = resolve_constructor_overload env decl_name args in
  let t_params = constructor_type.type_params in
  let w_params = constructor_type.wildcard_params in
  let params_args = match_params_to_args info constructor_type.parameters args in
  let type_params_args = infer_constructor_type_args env ctx t_params w_params params_args type_args in
  let env' = CheckerEnv.insert_types type_params_args env in
  let cast_arg (param, arg: Typed.Parameter.t * Types.Expression.t option) =
    match cast_param_arg env' ctx info (param, arg) with
    | _, Some e ->
       if compile_time_known_expr env e
       then Some e
       else raise_s [%message "constructor argument is not compile-time known" ~arg:(e: Prog.Expression.t)]
    | _, None ->
       if Parameter.is_optional param
       then None
       else failwith "missing constructor argument"
  in
  let args_typed =
    params_args
    |> List.filter_map ~f:cast_arg
  in
  let ret = saturate_type env' constructor_type.return in
  args_typed, ret

(* Section 14.1 *)
and type_nameless_instantiation env ctx info typ args =
  let open Prog.Expression in
  match snd typ with
  | SpecializedType { base; args = type_args } ->
     begin match snd base with
     | TypeName decl_name ->
        let out_args, out_typ = type_constructor_invocation env ctx info decl_name type_args args in
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
     type_nameless_instantiation env ctx info typ args
  | _ ->
     raise_s [%message "don't know how to instantiate this type"
                 ~typ:(typ: Types.Type.t)]

(* Section 8.12.3 *)
and type_mask env ctx expr mask : Prog.Expression.typed_t =
  let expr_typed = type_expression env ctx expr in
  let mask_typed = type_expression env ctx mask in
  let res_typ : Typed.Type.t =
    match (snd expr_typed).typ, (snd mask_typed).typ with
    | Bit { width = w1 }, Bit { width = w2 } when w1 = w2 ->
       Bit { width = w1 }
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
and type_range env ctx lo hi : Prog.Expression.typed_t =
  let lo_typed = type_expression env ctx lo in
  let hi_typed = type_expression env ctx hi in
  let typ : Typed.Type.t =
    match (snd lo_typed).typ, (snd hi_typed).typ with
    | Bit { width = l }, Bit { width = r } when l = r ->
       Bit { width = l}
    | Int { width = l }, Int { width = r } when l = r ->
       Int { width = l }
    | Integer, Integer -> Integer
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

and check_statement_legal_in (ctx: StmtContext.t) (stm: Statement.t) : unit =
  match ctx, snd stm with
  | Action, Switch _ ->
     raise_s [%message "branching statement not allowed in action"
                 ~stm:(stm: Statement.t)]
  | ParserState, Conditional _
  | ParserState, Switch _ ->
     raise_s [%message "branching statement not allowed in parser"
                 ~stm:(stm: Statement.t)]
  | _ -> ()

and type_statement (env: CheckerEnv.t) (ctx: StmtContext.t) (stm: Statement.t) : (Prog.Statement.t * CheckerEnv.t) =
  let open Prog.Statement in
  check_statement_legal_in ctx stm;
  let typed_stm, env' =
    match snd stm with
    | MethodCall { func; type_args; args } ->
       type_method_call env ctx (fst stm) func type_args args
    | Assignment { lhs; rhs } ->
       type_assignment env ctx lhs rhs
    | DirectApplication { typ; args } ->
       type_direct_application env ctx typ args
    | Conditional { cond; tru; fls } ->
       type_conditional env ctx cond tru fls
    | BlockStatement { block } ->
       type_block env ctx block
    | Exit ->
       { stmt = Exit;
         typ = StmType.Void },
       env
    | EmptyStatement ->
       { stmt = EmptyStatement;
         typ = StmType.Unit },
       env
    | Return { expr } ->
       type_return env ctx (fst stm) expr
    | Switch { expr; cases } ->
       type_switch env ctx (fst stm) expr cases
    | DeclarationStatement { decl } ->
       type_declaration_statement env ctx decl
  in
  ((fst stm, typed_stm), env')

(* Section 8.17 *)
and type_method_call env ctx call_info func type_args args =
  let expr_ctx = ExprContext.of_stmt_context ctx in
  let call_typed = type_function_call env expr_ctx call_info func type_args args in
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
and type_assignment env ctx lhs rhs =
  let open Prog.Statement in
  let expr_ctx = ExprContext.of_stmt_context ctx in
  let lhs_typed = type_expression env expr_ctx lhs in
  if not @@ is_lvalue env lhs_typed
  then raise_s [%message "Must be an lvalue"
                   ~lhs:(lhs:Types.Expression.t)]
  else
    let rhs_typed = cast_expression env expr_ctx (snd lhs_typed).typ rhs in
    ignore (assert_same_type env (info lhs) (info rhs)
              (snd lhs_typed).typ (snd rhs_typed).typ);
    { stmt = Assignment { lhs = lhs_typed; rhs = rhs_typed };
      typ = StmType.Unit },
    env

(* This belongs in an elaboration pass, really. - Ryan *)
and type_direct_application env ctx typ args =
  let open Types.Expression in
  let expr_ctx = ExprContext.of_stmt_context ctx in
  let instance = NamelessInstantiation { typ = typ; args = [] } in
  let apply = ExpressionMember { expr = Info.dummy, instance; name = (Info.dummy, "apply") } in
  let call = FunctionCall { func = Info.dummy, apply; type_args = []; args = args } in
  let call_typed = type_expression env expr_ctx (Info.dummy, call) in
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
and type_conditional env ctx cond tru fls =
  let open Prog.Statement in
  let expr_ctx = ExprContext.of_stmt_context ctx in
  let expr_typed = cast_expression env expr_ctx Bool cond in
  assert_bool (info cond) (snd expr_typed).typ |> ignore;
  let type' stmt = fst (type_statement env ctx stmt) in
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
     { stmt = stmt_out; typ = StmType.Unit }, env
  | Some fls_typed ->
     let typ =
       match tru_typ, (snd fls_typed).typ with
       | StmType.Void, StmType.Void -> StmType.Void
       | _ -> StmType.Unit
     in
     { stmt = stmt_out; typ = typ }, env

and type_statements env ctx statements =
  let open Prog.Statement in
  let fold (prev_type, stmts, env) statement =
    (* Cannot have statements after a void statement *)
    let stmt_typed, env = type_statement env ctx statement in
    let next_typ =
      match prev_type, (snd stmt_typed).typ with
      | _, StmType.Void
      | StmType.Void, _ -> StmType.Void
      | _ -> StmType.Unit
    in
    (next_typ, stmts @ [stmt_typed], env)
  in
  List.fold_left ~f:fold ~init:(StmType.Unit, [], env) statements

and type_block env ctx block =
  let (typ, stmts, env') = type_statements env ctx (snd block).statements in
  let block : Prog.Block.pre_t =
    { annotations = (snd block).annotations;
      statements = stmts }
  in
  { stmt = BlockStatement { block = Info.dummy, block }; typ = typ }, env

(* Section 11.4
 * Can a return statement update the environment?
 *
 *          Δ, T, Γ |- e : t
 * ---------------------------------------------
 *    Δ, T, Γ |- return e: void ,Δ, T, Γ
 *)
and type_return env ctx info expr =
  let expr_ctx = ExprContext.of_stmt_context ctx in
  let ret_typ =
    match ctx with
    | ApplyBlock
    | Action -> Typed.Type.Void
    | Function t -> t
    | ParserState -> failwith "return in parser state not allowed"
  in
  let (stmt, typ) : Prog.Statement.pre_t * Typed.Type.t =
    match expr with
    | None -> Return { expr = None }, Typed.Type.Void
    | Some e ->
       let e_typed = cast_expression env expr_ctx ret_typ e in
       Return { expr = Some e_typed }, (snd e_typed).typ
  in
  { stmt = stmt; typ = StmType.Void }, env

(* Section 11.7 *)
and type_switch env ctx info expr cases =
  let open Types.Statement in
  let expr_ctx = ExprContext.of_stmt_context ctx in
  if ctx <> ApplyBlock
  then raise_s [%message "switch statements not allowed in context"
                   ~ctx:(ctx: StmtContext.t)];
  let expr_typed = type_expression env expr_ctx expr in
  let action_name_typ =
    match reduce_type env (snd expr_typed).typ with
    | Enum e -> e
    | _ -> raise_mismatch info "table action enum" (snd expr_typed).typ
  in
  let lbl_seen cases_done lbl =
    let case_name_eq lbl ((_, case): Prog.Statement.switch_case) =
      match case with
      | Action { label; _ }
      | FallThrough { label } ->
         match snd label, lbl with
         | Default, Default -> true
         | Name (_, n1), Name (_, n2) ->
            n1 = n2
         | _ -> false
    in
    List.exists ~f:(case_name_eq lbl) cases_done
  in
  let label_checker cases_done (label: Types.Statement.switch_label) =
    if lbl_seen cases_done (snd label) then raise (Type ((fst label), Duplicate));
    if lbl_seen cases_done Default then raise (Type ((fst label), UnreachableBlock));
    match snd label with
    | Default ->
       fst label, Prog.Statement.Default
    | Name (info, name) ->
       if List.mem ~equal:(=) action_name_typ.members name
       then fst label, Prog.Statement.Name (info, name)
       else raise_unfound_member info name
  in
  let case_checker cases_done (case_info, case) =
    match case with
    | Action { label; code = block } ->
       let block_expr_typed, env = type_block env ctx block in
       let label_typed = label_checker cases_done label in
       let block_typed =
         match block_expr_typed.stmt with
         | BlockStatement { block } -> block
         | _ -> failwith "bug: expected block"
       in
       cases_done @ [case_info, Prog.Statement.Action { label = label_typed; code = block_typed }]
    | FallThrough { label } ->
       let label_typed = label_checker cases_done label in
       cases_done @ [case_info, Prog.Statement.FallThrough { label = label_typed }]
  in
  let cases = List.fold ~init:[] ~f:case_checker cases in
  { stmt = Switch { expr = expr_typed;
                    cases = cases };
    typ = StmType.Unit }, env

(* Section 10.3 *)
and type_declaration_statement env ctx (decl: Declaration.t) : Prog.Statement.typed_t * CheckerEnv.t =
  let open Prog.Statement in
  match snd decl with
  | Constant _
  | Instantiation _
  | Variable _ ->
     let decl_typed, env' = type_declaration env (DeclContext.Statement ctx) decl in
     { stmt = DeclarationStatement { decl = decl_typed };
       typ = StmType.Unit },
     env'
  | _ -> raise_s [%message "declaration used as statement, but that's not allowed. Parser bug?" ~decl:(decl: Types.Declaration.t)]

(* Section 10.1
 *
 *          Δ, T, Γ |- e : t' = t
 * ---------------------------------------------
 *    Δ, T, Γ |- const t x = e : Δ, T, Γ[x -> t]
 *)
and type_constant env ctx decl_info annotations typ name expr : Prog.Declaration.t * CheckerEnv.t =
  let expr_ctx = ExprContext.of_decl_context ctx in
  let expected_typ = translate_type env [] typ in
  let typed_expr = cast_expression env expr_ctx expected_typ expr in
  match compile_time_eval_expr env typed_expr with
  | Some value ->
     (decl_info, Constant { annotations; typ = expected_typ; name = name; value = value }),
     env
     |> CheckerEnv.insert_dir_type_of (BareName name) expected_typ Directionless
     |> CheckerEnv.insert_const (BareName name) value
  | None ->
     raise_s [%message "expression not compile-time-known"
                 ~expr:(typed_expr:Prog.Expression.t)]

and insert_params (env: CheckerEnv.t) (params: Types.Parameter.t list) : CheckerEnv.t =
  let open Types.Parameter in
  let insert_param env (_, p) =
    let typ = translate_type env [] p.typ in
    let dir = translate_direction p.direction in
    CheckerEnv.insert_dir_type_of (BareName p.variable) typ dir env
  in
  List.fold_left ~f:insert_param ~init:env params

(* Section 10.3 *)
and type_instantiation env ctx info annotations typ args name : Prog.Declaration.t * CheckerEnv.t =
  let expr_ctx = ExprContext.of_decl_context ctx in
  let instance_typed = type_nameless_instantiation env expr_ctx info typ args in
  let instance_type = instance_typed.typ in
  begin match instance_type, ctx with
  | Control _, DeclContext.TopLevel ->
     raise_s [%message "controls cannot be instantiated in the top level scope"]
  | Parser _, DeclContext.TopLevel ->
     raise_s [%message "parsers cannot be instantiated in the top level scope"]
  | _ -> ()
  end;
  match instance_typed.expr with
  | NamelessInstantiation { args; typ } ->
     (info,
      Instantiation
        { annotations = annotations;
          typ = typ;
          args = args;
          name = name;
          init = None }),
     CheckerEnv.insert_type_of (BareName name) instance_type env
  | _ -> failwith "BUG: expected NamelessInstantiation"

and infer_constructor_type_args env ctx type_params wildcard_params params_args type_args =
  let type_params_args =
    match List.zip type_params type_args with
    | Ok v -> v
    | Unequal_lengths ->
       if type_args = []
       then List.map ~f:(fun v -> v, None) type_params
       else failwith "mismatch in type arguments"
  in
  let full_params_args =
    type_params_args @ List.map ~f:(fun v -> v, None) wildcard_params
  in
  infer_type_arguments env ctx Typed.Type.Void full_params_args params_args []

(* Terrible hack - Ryan *)
and check_match_type_eq env info set_type element_type =
  let open Typed.Type in
  match set_type with
  | Set (Enum { typ = Some carrier; _ }) ->
     check_match_type_eq env info (Set carrier) element_type
  | _ ->
     match element_type with
     | Enum { typ = Some elt_carrier; _ } ->
        check_match_type_eq env info set_type elt_carrier
     | _ ->
        assert_type_equality env info set_type (Set element_type)

and check_match env ctx (info, m: Types.Match.t) (expected_type: Type.t) : Prog.Match.t =
  match m with
  | Default
  | DontCare ->
     let set = Type.Set expected_type in
     info, { expr = DontCare; typ = set }
  | Expression { expr } ->
     let expr_typed = cast_expression env ctx (Set expected_type) expr in
     let typ = (snd expr_typed).typ in
     check_match_type_eq env info typ expected_type;
     info, { expr = Expression {expr = expr_typed};
             typ = Type.Set typ }

and check_match_product env ctx (ms: Types.Match.t list) (expected_types: Type.t list) =
  match ms, expected_types with
  | [m], [t] ->
     [check_match env ctx m t]
  | [m], types ->
     [check_match env ctx m (List { types })]
  | ms, types ->
     List.map ~f:(fun (m, t) -> check_match env ctx m t) @@ List.zip_exn ms types

and type_select_case env ctx state_names expr_types ((case_info, case): Types.Parser.case) : Prog.Parser.case =
  let matches_typed = check_match_product env ctx case.matches expr_types in
  if List.mem ~equal:(=) state_names (snd case.next)
  then case_info, { matches = matches_typed; next = case.next }
  else raise_s [%message "state name unknown" ~name:(snd case.next: string)]

and type_transition env ctx state_names transition : Prog.Parser.transition =
  let open Parser in
  fst transition,
  match snd transition with
  | Direct {next = (name_info, name')} ->
      if List.mem ~equal:(=) state_names name'
      then Direct { next = (name_info, name') }
      else raise @@ Type (name_info, (Error.Unbound name'))
  | Select {exprs; cases} ->
      let exprs_typed = List.map ~f:(type_expression env ctx) exprs in
      let expr_types = List.map ~f:(fun (_, e) -> e.typ) exprs_typed in
      let cases_typed =
        List.map ~f:(type_select_case env ctx state_names expr_types) cases
      in
      Select { exprs = exprs_typed; cases = cases_typed }

and type_parser_state env state_names (state: Parser.state) : Prog.Parser.state =
  let (_, stmts_typed, env) = type_statements env ParserState (snd state).statements in
  let transition_typed = type_transition env ParserState state_names (snd state).transition in
  let pre_state : Prog.Parser.pre_state =
    { annotations = (snd state).annotations;
      statements = stmts_typed;
      transition = transition_typed;
      name = (snd state).name }
  in
  (fst state, pre_state)

and check_state_names names =
  match List.find_a_dup ~compare:String.compare names with
  | Some duplicated -> raise_s [%message "duplicate state name in parser" ~state:duplicated]
  | None ->
     if List.mem ~equal:(=) names "start"
     then ()
     else raise_s [%message "parser is missing start state"];

and open_parser_scope env ctx params constructor_params locals states =
  let open Parser in
  let constructor_params_typed = type_constructor_params env ctx constructor_params in
  let params_typed = type_params env (Runtime ctx) params in
  let env = insert_params env constructor_params in
  let env = insert_params env params in
  let locals_typed, env = type_declarations env DeclContext.Nested locals in
  let program_state_names = List.map ~f:(fun (_, state) -> snd state.name) states in
  (* TODO: check that no program_state_names overlap w/ standard ones
   * and that there is some "start" state *)
  let state_names = program_state_names @ ["accept"; "reject"] in
  check_state_names state_names;
  (env, state_names, constructor_params_typed, params_typed, locals_typed)

(* Section 12.2 *)
and type_parser env info name annotations params constructor_params locals states =
  let (env', state_names,
       constructor_params_typed, params_typed, locals_typed) =
    open_parser_scope env Parser params constructor_params locals states
  in
  let states_typed = List.map ~f:(type_parser_state env' state_names) states in
  let parser_typed : Prog.Declaration.pre_t =
    Parser { annotations;
             name;
             type_params = [];
             params = params_typed;
             constructor_params = constructor_params_typed;
             locals = locals_typed;
             states = states_typed }
  in
  let parser_typ : Typed.ControlType.t =
    { type_params = [];
      parameters = params_typed }
  in
  let ctor : Typed.ConstructorType.t =
    { type_params = [];
      wildcard_params = [];
      parameters = constructor_params_typed;
      return = Parser parser_typ }
  in
  let env = CheckerEnv.insert_type_of (BareName name) (Constructor ctor) env in
  (info, parser_typed), env

and open_control_scope env ctx params constructor_params locals =
  let params_typed = type_params env (Runtime ctx) params in
  let constructor_params_typed = type_constructor_params env ctx constructor_params in
  let env = insert_params env constructor_params in
  let env = insert_params env params in
  let locals_typed, env = type_declarations env DeclContext.Nested locals in
  env, params_typed, constructor_params_typed, locals_typed

(* Section 13 *)
and type_control env info name annotations type_params params constructor_params locals apply =
  if List.length type_params > 0
  then raise_s [%message "Control declarations cannot have type parameters" ~name:(snd name)]
  else
    let env', params_typed, constructor_params_typed, locals_typed =
      open_control_scope env Control params constructor_params locals
    in
    let block_typed, env'' = type_block env' ApplyBlock apply in
    let apply_typed =
      match block_typed.stmt with
      | BlockStatement { block } -> block
      | _ -> failwith "expected BlockStatement"
    in
    let control : Prog.Declaration.pre_t =
      Control { annotations = annotations;
                name = name;
                type_params = [];
                params = params_typed;
                constructor_params = constructor_params_typed;
                locals = locals_typed;
                apply = apply_typed }
    in
    let control_type =
      Typed.Type.Control { type_params = [];
                           parameters = params_typed }
    in
    let ctor : Typed.ConstructorType.t =
      { type_params = [];
        wildcard_params = [];
        parameters = constructor_params_typed;
        return = control_type }
    in
    let env' = CheckerEnv.insert_type_of (BareName name) (Constructor ctor) env in
    (info, control), env'

(* Section 9

 * Function Declaration:
 *
 *        Γ' = union over i Γ (xi -> di ti)
 *   forall k,  Δk, Tk, Γk' |- stk+1 : Δk+1, Tk+1, Γk+1'
 *     stk = return ek => Δk, Tk, Γk' |- ek : t' = tr
 * -------------------------------------------------------
 *    Δ, T, Γ |- tr fn<...Aj,...>(...di ti xi,...){...stk;...}
 *)
and type_function env (ctx: Typed.StmtContext.t) info return name type_params params body =
  let (paramctx: Typed.ParamContext.decl), (kind: Typed.FunctionType.kind) =
    match ctx with
    | Function _ -> Function, Function
    | Action -> Action, Action
    | _ -> failwith "bad context for function"
  in
  let t_params = List.map ~f:snd type_params in
  let body_env = CheckerEnv.insert_type_vars t_params env in
  let params_typed = List.map ~f:(type_param body_env (Runtime paramctx)) params in
  let return_type = return |> translate_type env t_params in
  let body_env = insert_params body_env params in
  let body_stmt_typed, _ = type_block body_env ctx body in
  let body_typed : Prog.Block.t =
    match body_stmt_typed, return_type with
    | { stmt = BlockStatement { block = blk }; _ }, Void
    | { stmt = BlockStatement { block = blk }; typ = StmType.Void }, _ ->
       blk
    | { stmt = BlockStatement { block = blk}; typ = StmType.Unit }, non_void ->
       raise_s [%message "function body does not return a value of the required type"
              ~body:(blk: Prog.Block.t)
              ~return_type:(return_type: Typed.Type.t)]
    | _ -> failwith "bug: expected BlockStatement"
  in
  let funtype =
    Type.Function { parameters = params_typed;
                    type_params = List.map ~f:snd type_params;
                    kind;
                    return = return_type } in
  let env = CheckerEnv.insert_type_of (BareName name) funtype env in
  let fn_typed : Prog.Declaration.pre_t =
    Function { return = return_type;
               name = name;
               type_params = type_params;
               params = params_typed;
               body = body_typed }
  in
  (info, fn_typed), env

(* Section 7.2.9.1 *)
and type_extern_function env info annotations return name type_params params =
  let t_params = type_params |> List.map ~f:snd in
  let return = return |> translate_type env t_params in
  let env' = CheckerEnv.insert_type_vars t_params env in
  let params_typed = List.map ~f:(type_param env' (Runtime Function)) params in
  let typ: Typed.FunctionType.t =
    { type_params = t_params;
      parameters = params_typed;
      kind = Extern;
      return = return }
  in
  let fn_typed : Prog.Declaration.pre_t =
    ExternFunction { annotations;
                     return;
                     type_params;
                     params = params_typed;
                     name = name }
  in
  (info, fn_typed), CheckerEnv.insert_type_of ~shadowing:true (BareName name) (Function typ) env

and is_variable_type env (typ: Typed.Type.t) =
  let typ = saturate_type env typ in
  match typ with
  | TypeName name -> true
  | NewType {typ; _} ->
     is_variable_type env typ
  | Bool
  | Int _
  | Bit _
  | VarBit _
  | Array _
  | Tuple _
  | Record _
  | Error
  | MatchKind
  | Header _
  | HeaderUnion _
  | Struct _
  | Enum _ ->
     true
  | String
  | Integer
  | List _
  | Set _
  | Void
  | SpecializedType _
  | Package _
  | Control _
  | Parser _
  | Extern _
  | Function _
  | Action _
  | Constructor _
  | Table _ ->
     false

(* Section 10.2
 *
 *          Δ, T, Γ |- e : t' = t
 * ---------------------------------------------
 *    Δ, T, Γ |- t x = e : Δ, T, Γ[x -> t]
 *)
and type_variable env ctx info annotations typ name init =
  let expr_ctx = ExprContext.of_decl_context ctx in
  let expected_typ = translate_type env [] typ in
  if not (is_variable_type env expected_typ)
  then raise_s [%message "Cannot declare variables of this type"
              ~typ:(expected_typ: Typed.Type.t)];
  if not (is_well_formed_type env expected_typ)
  then raise_s [%message "type is not well-formed" ~typ:(expected_typ:Typed.Type.t)];
  if ctx = DeclContext.TopLevel
  then raise_s [%message "variables cannot be declared at the top level"];
  let init_typed =
    match init with
    | None ->
       None
    | Some value ->
       let expected_typ = translate_type env [] typ in
       let typed_expr = cast_expression env expr_ctx expected_typ value in
       Some typed_expr
  in
  let var_typed : Prog.Declaration.pre_t =
    Variable { annotations;
               typ = expected_typ;
               name = name;
               init = init_typed }
  in
  let env = CheckerEnv.insert_dir_type_of (BareName name) expected_typ InOut env in
  (info, var_typed), env

(* Section 12.11 *)
and type_value_set env ctx info annotations typ size name =
  let element_type = translate_type env [] typ in
  let size_typed = type_expression env Constant size in
  let env = CheckerEnv.insert_type_of (BareName name) (Set element_type) env in
  let value_set : Prog.Declaration.pre_t =
    ValueSet { annotations;
               typ = element_type;
               name = name;
               size = size_typed }
  in
  (info, value_set), env

(* Section 13.1 *)
and type_action env info annotations name params body =
  let fn_typed, fn_env =
    type_function env Action info (Info.dummy, Types.Type.Void) name [] params body
  in
  let action_typed, action_type =
    match snd fn_typed with
    | Function { return; name; type_params; params; body } ->
       let data_params, ctrl_params =
         List.split_while params
           ~f:(fun p -> p.direction <> Directionless)
       in
       let check_ctrl p =
         let open Typed.Parameter in
         if p.direction <> Directionless
         then raise_s [%message "data parameter after a control parameter in action declaration"
                          ~data_param:(p: Typed.Parameter.t)
                          ~action_info:(info: Info.t)]
       in
       List.iter ~f:check_ctrl ctrl_params;
       let action_type : Typed.Type.t =
         Action { data_params = data_params;
                  ctrl_params = ctrl_params; }
       in
       let action =
         Prog.Declaration.Action { annotations; name; data_params; ctrl_params; body = body }
       in
       action, action_type
    | _ -> failwith "expected function declaration"
  in
  (info, action_typed),
  CheckerEnv.insert_type_of (BareName name) action_type env

(* Section 13.2 *)
and type_table env ctx info annotations name properties : Prog.Declaration.t * CheckerEnv.t =
  type_table' env ctx info annotations name None [] None None None (List.map ~f:snd properties)

and type_keys env ctx keys =
  let open Prog.Table in
  let expr_ctx = ExprContext.of_decl_context ctx in
  let type_key key =
    let {key; match_kind; annotations}: Table.pre_key = snd key in
    match CheckerEnv.find_type_of_opt (BareName match_kind) env with
    | Some (MatchKind, _) ->
       let expr_typed = type_expression env expr_ctx key in
       (fst key, { annotations; key = expr_typed; match_kind })
    | _ ->
       raise_s [%message "invalid match_kind" ~match_kind:(snd match_kind)]
  in
  List.map ~f:type_key keys

and type_table_actions env ctx key_types actions =
  let expr_ctx = ExprContext.of_decl_context ctx in
  let type_table_action (call_info, action: Table.action_ref) =
    let data_params =
      match CheckerEnv.find_type_of_opt action.name env with
      | Some (Action action_typ, _) ->
         action_typ.data_params
      | _ ->
         raise_s [%message "invalid action" ~action:(action.name: Types.name)]
    in
    (* Below should fail if there are control plane arguments *)
    let params_args = match_params_to_args call_info data_params action.args in
    let type_param_arg env (param, expr: Typed.Parameter.t * Expression.t option) =
      match expr with
      | Some expr ->
         let arg_typed = cast_expression env expr_ctx param.typ expr in
         check_direction env param.direction arg_typed;
         Some arg_typed
      | None ->
         match param.direction with
         | Out -> None
         | _ ->
            raise_s [%message "don't care argument (underscore) provided for non-out parameter"
                        ~call_site:(call_info: Info.t) ~param:(snd param.variable)]
    in
    let args_typed = List.map ~f:(type_param_arg env) params_args in
    let open Prog.Table in
    (call_info,
     { action =
         { annotations = action.annotations;
           name = action.name;
           args = args_typed };
       typ = fst @@ CheckerEnv.find_type_of action.name env })
  in
  let action_typs = List.map ~f:type_table_action actions in
  (* Need to fail in the case of duplicate action names *)
  let action_names = List.map ~f:(fun (_, action: Table.action_ref) -> action.name) actions in
  List.zip_exn action_names action_typs

and type_table_entries env ctx entries key_typs action_map =
  let open Prog.Table in
  let expr_ctx = ExprContext.of_decl_context ctx in
  let type_table_entry (entry_info, entry: Table.entry) : Prog.Table.entry =
    let matches_typed = check_match_product env expr_ctx entry.matches key_typs in
    match List.Assoc.find action_map ~equal:name_eq (snd entry.action).name with
    | None ->
       failwith "Entry must call an action in the table."
    | Some (action_info, { action; typ = Action { data_params; ctrl_params } }) ->
       let type_arg (param: Typed.Parameter.t) (arg_info, arg: Argument.t) =
         begin match arg with
         (* Direction handling probably is incorrect here. *)
         | Expression { value = exp } -> Some (cast_expression env expr_ctx param.typ exp)
         | _ -> failwith "Actions in entries only support positional arguments."
         end in
       let args_typed = List.map2_exn ~f:type_arg ctrl_params (snd entry.action).args in
       let action_ref_typed : Prog.Table.action_ref =
         action_info,
         { action =
             { annotations = (snd entry.action).annotations;
               name = (snd entry.action).name;
               args = args_typed };
           typ = Action { data_params; ctrl_params } }
       in
       let pre_entry : Prog.Table.pre_entry =
         { annotations = entry.annotations;
           matches = matches_typed;
           action = action_ref_typed }
       in
       (entry_info, pre_entry)
    | _ -> failwith "Table actions must have action types."
  in
  List.map ~f:type_table_entry entries

(* syntactic equality of expressions *)
and expr_eq env (expr1: Prog.Expression.t) (expr2: Prog.Expression.t) : bool =
  let key_val_eq (_, k1: Prog.KeyValue.t) (_, k2: Prog.KeyValue.t) : bool =
    k1.key = k2.key && expr_eq env k1.value k2.value
  in
  let e1 = (snd expr1).expr in
  let e2 = (snd expr2).expr in
  match e1, e2 with
  | True,  True
  | False, False
  | DontCare, DontCare -> true
  | Int (_,{value=v1; width_signed=w1}),
    Int (_,{value=v2; width_signed=w2})
    -> Bigint.equal v1 v2
       && [%compare.equal: ((int * bool) option)] w1 w2
  | String (_,s1), String (_,s2)
    -> String.equal s1 s2
  | Name n1, Name n2
    -> Types.name_eq n1 n2
  | ArrayAccess { array=a1; index=i1 },
    ArrayAccess { array=a2; index=i2 }
    -> expr_eq env a1 a2 && expr_eq env i1 i2
  | BitStringAccess { bits=b1; lo=l1; hi=h1 },
    BitStringAccess { bits=b2; lo=l2; hi=h2 }
    -> expr_eq env b1 b2 && Bigint.equal l1 l2 && Bigint.equal h1 h2
  | List { values=v1 }, List { values=v2 }
    -> List.equal (expr_eq env) v1 v2
  | Record { entries=kv1 }, Record { entries=kv2 }
    -> List.equal key_val_eq kv1 kv2
  | UnaryOp { op=o1; arg=e1 }, UnaryOp { op=o2; arg=e2 }
    -> Op.eq_uni o1 o2 && expr_eq env e1 e2
  | BinaryOp { op=b1; args=(l1,r1) }, BinaryOp { op=b2; args=(l2,r2) }
    -> Op.eq_bin b1 b2 && expr_eq env l1 l2 && expr_eq env r1 r2
  | Cast { typ=t1; expr=e1 }, Cast { typ=t2; expr=e2 }
    -> type_equality env [] t1 t2 && expr_eq env e1 e2
  | TypeMember { typ=n1; name=_,s1 },
    TypeMember { typ=n2; name=_,s2 }
    -> Types.name_eq n1 n2 && String.equal s1 s2
  | ErrorMember (_,s1), ErrorMember (_,s2)
    -> String.equal s1 s2
  | ExpressionMember { expr=e1; name=_,s1 },
    ExpressionMember { expr=e2; name=_,s2 }
    -> expr_eq env e1 e2 && String.equal s1 s2
  | Ternary { cond=c1; tru=t1; fls=f1 },
    Ternary { cond=c2; tru=t2; fls=f2 }
    -> expr_eq env c1 c2 && expr_eq env t1 t2 && expr_eq env f1 f2
  | FunctionCall { func=e1; type_args=t1; args=l1 },
    FunctionCall { func=e2; type_args=t2; args=l2 }
    -> expr_eq env e1 e2 &&
         List.equal Type.eq t1 t2 &&
           List.equal begin Util.eq_opt ~f:(expr_eq env) end l1 l2
  | NamelessInstantiation { typ=t1; args=e1 },
    NamelessInstantiation { typ=t2; args=e2 }
    -> Type.eq t1 t2 && List.equal (expr_eq env) e1 e2
  | Mask { expr=e1; mask=m1 }, Mask { expr=e2; mask=m2 }
    -> expr_eq env e1 e2 && expr_eq env m1 m2
  | Range { lo=l1; hi=h1 }, Range { lo=l2; hi=h2 }
    -> expr_eq env l1 l2 && expr_eq env h1 h2
  | _ -> false

and type_default_action
  env ctx (action_map : (Types.name * (Info.t * Prog.Table.typed_action_ref)) list)
  action_expr : Prog.Table.action_ref =
  let expr_ctx: Typed.ExprContext.t = TableAction in
  let action_expr_typed = type_expression env expr_ctx action_expr in
  match (snd action_expr_typed).expr with
  | FunctionCall { func = _, {expr = Name action_name; _}; type_args = []; args = args } ->
     begin match List.Assoc.find ~equal:name_eq action_map action_name with
     | None -> raise_s [%message "couldn't find default action in action_map"]
     | Some (_, {action={args=prop_args; _}; _}) ->
        (* compares the longest prefix that
         * the default args are equal to the property args, and then
         * the remainder of values must be compile-time known *)
         let len = List.length prop_args in
         let prefix,suffix = List.split_n args len in
         if List.equal
          begin Util.eq_opt ~f:(expr_eq env) end prop_args prefix
          && suffix
          |> List.filter_map ~f:(fun x -> x)
          |> List.for_all
            ~f:begin fun e ->
                match compile_time_eval_expr env e with
                | None -> raise_s
                  [%message "default action argument is not compile-time known"]
                (* is there a way to convert from values to expressions?
                 * this seems wasteful... *)
                | Some _ -> true
              end
         then
           fst action_expr,
               { action = { annotations = [];
                            name = action_name;
                            args = args };
                 typ = (snd action_expr_typed).typ }
         else raise_s [%message "default action's prefix of arguments do not match those of that in table actions property"]
    end
  | Name action_name ->
     if List.Assoc.mem ~equal:name_eq action_map action_name
     || List.Assoc.mem
      ~equal:name_eq
      begin List.map ~f:begin Tuple.T2.map_fst ~f:to_bare end action_map end action_name
     then fst action_expr,
          { action = { annotations = [];
                       name = action_name;
                       args = [] };
            typ = (snd action_expr_typed).typ }
     else failwith "couldn't find default action in action_map"
  | e ->
     failwith "couldn't type default action as functioncall"

and keys_actions_ok keys actions =
  match keys with
  | Some [] -> true
  | Some ks -> List.length actions > 0
  | None -> List.length actions > 0

and type_table' env ctx info annotations name key_types action_map entries_typed size default_typed properties =
  let open Types.Table in
  match properties with
  | Key { keys } :: rest ->
     begin match key_types with
     | None ->
        type_table' env ctx info annotations
          name
          (Some (type_keys env ctx keys))
          action_map
          entries_typed
          size
          default_typed
          rest
     | Some key_types ->
        raise_s [%message "multiple key properties in table?" ~name:(snd name)]
     end
  | Actions { actions } :: rest ->
     begin match key_types with
     | None ->
        begin match Util.find_and_drop ~f:(function Table.Key _ -> true | _ -> false) properties with
        | Some key_prop, other_props ->
           let props = key_prop :: other_props in
           type_table' env ctx info annotations
             name
             None
             action_map
             entries_typed
             size
             default_typed
             props
        | None, props ->
           type_table' env ctx info annotations
             name
             (Some [])
             action_map
             entries_typed
             size
             default_typed
             props
        end
     | Some kts ->
        let action_map = type_table_actions env ctx kts actions in
        type_table' env ctx info annotations
          name
          key_types
          action_map
          entries_typed
          size
          default_typed
          rest
     end
  | Entries { entries } :: rest ->
     begin match entries_typed with
     | Some _ -> failwith "multiple entries properties in table"
     | None ->
        begin match key_types with
        | Some keys_typed ->
           let key_types' = List.map ~f:(fun k -> (snd (snd k).key).typ) keys_typed in
           let entries_typed = type_table_entries env ctx entries key_types' action_map in
           type_table' env ctx info annotations name key_types action_map (Some entries_typed) size default_typed rest
        | None -> failwith "entries with no keys?"
        end
     end
  | Custom { name = (_, "default_action"); value; _ } :: rest ->
     begin match default_typed with
     | None ->
        let default_typed = type_default_action env ctx action_map value in
        type_table' env ctx info annotations
          name
          key_types
          action_map
          entries_typed
          size
          (Some default_typed)
          rest
     | Some _ -> failwith "multiple default_action properties in table"
     end
  | Custom { name = (_, "size"); value; _ } :: rest ->
     if size <> None then failwith "duplicated size properties?";
     let expr_ctx = ExprContext.of_decl_context ctx in
     let value_typed = type_expression env expr_ctx value in
     let _ = assert_numeric (fst value) (snd value_typed).typ in
     let size = compile_time_eval_expr env value_typed in
     begin match size with
     | Some (VInteger size) ->
        let size: P4Int.t =
          fst value, { value = size; width_signed = None }
        in
        type_table' env ctx info annotations
          name
          key_types
          action_map
          entries_typed
          (Some size)
          default_typed
          rest
     | _ ->
        type_table' env ctx info annotations
          name
          key_types
          action_map
          entries_typed
          None
          default_typed
          rest
     end
  | Custom _ :: rest ->
     (* TODO *)
     type_table' env ctx info annotations
       name
       key_types
       action_map
       entries_typed
       size
       default_typed
       rest
  | [] ->
    let open EnumType in
    let open RecordType in
    (* Aggregate table information. *)
    let action_names = action_map
      |> begin fun l ->
         if keys_actions_ok key_types l
         then l
         else raise_s [%message "Table must have a non-empty actions property"] end
      |> List.map ~f:fst
      |> List.map ~f:name_only in
    let action_enum_name = "action_list_" ^ snd name in
    let action_enum_typ =
      Type.Enum { name=action_enum_name;
                  typ=None;
                  members=action_names }
    in
    let key = match key_types with
      | Some ks -> ks
      | None -> failwith "no key property in table?"
    in
    (* Populate environment with action_enum *)
    (* names of action list enums are "action_list_<<table name>>" *)
    let env =
      CheckerEnv.insert_type (BareName (Info.dummy, action_enum_name))
                action_enum_typ env
    in
    let hit_field = {name="hit"; typ=Type.Bool} in
    let miss_field = {name="miss"; typ=Type.Bool} in
    (* How to represent the type of an enum member *)
    let run_field = {name="action_run"; typ=action_enum_typ} in
    let apply_result_typ = Type.Struct {fields=[hit_field; miss_field; run_field]; } in
    (* names of table apply results are "apply_result_<<table name>>" *)
    let result_typ_name = name |> snd |> (^) "apply_result_" in
    let env = CheckerEnv.insert_type (BareName (fst name, result_typ_name)) apply_result_typ env in
    let table_typ = Type.Table {result_typ_name=result_typ_name} in
    let table_typed : Prog.Declaration.pre_t =
      Table { annotations;
              name;
              key = key;
              actions = List.map ~f:snd action_map;
              entries = entries_typed;
              default_action = default_typed;
              size = size;
              custom_properties = [] }
    in
    let nm = BareName name in
    (info, table_typed), CheckerEnv.insert_type_of nm table_typ env

(* Section 7.2.2 *)
and type_header env info annotations name fields =
  let fields_typed, type_fields = List.unzip @@ List.map ~f:(type_field env) fields in
  let header_typ = Type.Header { fields = type_fields; } in
  if not (is_well_formed_type env header_typ)
  then raise_s [%message "bad header type" ~typ:(header_typ:Typed.Type.t)];
  let env = CheckerEnv.insert_type (BareName name) header_typ env in
  let header = Prog.Declaration.Header { annotations; name; fields = fields_typed } in
  (info, header), env

and type_field env (field_info, field) =
  let open Types.Declaration in
  let typ = saturate_type env (translate_type env [] field.typ) in
  let pre_field : Prog.Declaration.pre_field =
    { annotations = field.annotations; name = field.name; typ }
  in
  let pre_record_field : Typed.RecordType.field =
    { name = snd field.name; typ }
  in
  (field_info, pre_field), pre_record_field

and type_header_union_field env (field_info, field) =
  let open Types.Declaration in
  let typ = translate_type env [] field.typ in
  match saturate_type env typ with
  | Header _ ->
     type_field env (field_info, field)
  | _ -> raise_s [%message "header union fields must have header type"
                     ~field:((field_info, field): Types.Declaration.field)]

(* Section 7.2.3 *)
and type_header_union env info annotations name fields =
  let fields_typed, type_fields =
    List.unzip @@ List.map ~f:(type_header_union_field env) fields
  in
  let header_typ = Type.HeaderUnion { fields = type_fields; } in
  if not (is_well_formed_type env header_typ)
  then raise_s [%message "bad header type" ~typ:(header_typ:Typed.Type.t)];
  let env = CheckerEnv.insert_type (BareName name) header_typ env in
  let header = Prog.Declaration.HeaderUnion { annotations; name; fields = fields_typed } in
  (info, header), env

(* Section 7.2.5 *)
and type_struct env info annotations name fields =
  let fields_typed, type_fields = List.unzip @@ List.map ~f:(type_field env) fields in
  let struct_typ = Type.Struct { fields = type_fields; } in
  if not (is_well_formed_type env struct_typ)
  then raise_s [%message "bad struct type" ~name:(snd name) ~typ:(struct_typ:Typed.Type.t)];
  let env = CheckerEnv.insert_type (BareName name) struct_typ env in
  let struct_decl = Prog.Declaration.Struct { annotations; name; fields = fields_typed } in
  (info, struct_decl), env

(* Auxillary function for [type_error] and [type_match_kind],
 * which require unique names *)
and fold_unique members (_, member) =
  if List.mem ~equal:(=) members member then
    failwith "Name already bound"
  else
    member :: members

(* Section 7.1.2 *)
(* called by type_type_declaration *)
and type_error env info members =
  let add_err env (e_info, e) =
    let name = QualifiedName ([], (e_info, "error." ^ e)) in
    if CheckerEnv.find_type_of_opt name env <> None
    then raise_s [%message "error already declared" ~err:e];
    env
    |> CheckerEnv.insert_type_of name Type.Error
    |> CheckerEnv.insert_const name (VError e)
  in
  let env = List.fold_left ~f:add_err ~init:env members in
  (info, Prog.Declaration.Error { members }), env

(* Section 7.1.3 *)
and type_match_kind env info members =
  let add_mk env e =
    let name = QualifiedName ([], e) in
    if CheckerEnv.find_type_of_opt name env <> None
    then raise_s [%message "match_kind already declared" ~match_kind:(snd e)];
    env
    |> CheckerEnv.insert_type_of name Type.MatchKind
    |> CheckerEnv.insert_const name (VMatchKind (snd e))
  in
  let env = List.fold_left ~f:add_mk ~init:env members in
  (info, Prog.Declaration.MatchKind { members }), env

(* Section 7.2.1 *)
and type_enum env info annotations name members =
  let enum_typ =
    Type.Enum { name = snd name;
                members = List.map ~f:snd members;
                typ = None }
  in
  let add_member env (member_info, member) =
    let member_name = QualifiedName ([], (member_info, snd name ^ "." ^ member)) in
    env
    |> CheckerEnv.insert_type_of member_name enum_typ
    |> CheckerEnv.insert_const member_name
         (VEnumField { typ_name = snd name;
                       enum_name = member  })
  in
  let env = CheckerEnv.insert_type (QualifiedName ([], name)) enum_typ env in
  let env = List.fold_left ~f:add_member ~init:env members in
  (info, Prog.Declaration.Enum { annotations; name; members }), env

(* Section 8.3 *)
and type_serializable_enum env ctx info annotations underlying_type name members =
  let expr_ctx = ExprContext.of_decl_context ctx in
  let underlying_type =
    underlying_type
    |> translate_type env []
    |> saturate_type env
  in
  let underlying_type =
    match underlying_type with
    | Int _ | Bit _ -> underlying_type
    | _ -> raise_mismatch info "fixed width numeric type for enum" underlying_type
  in
  let member_names = List.map ~f:(fun member -> snd (fst member)) members in
  let enum_type: Typed.Type.t =
    Enum { name = snd name; typ = Some underlying_type; members = member_names }
  in
  let add_member (env, members_typed) ((member_info, member), expr) =
    let member_name = QualifiedName ([], (member_info, snd name ^ "." ^ member)) in
    let expr_typed = cast_expression env expr_ctx underlying_type expr in
    match compile_time_eval_expr env expr_typed with
    | Some value ->
       env
       |> CheckerEnv.insert_type_of member_name enum_type
       |> CheckerEnv.insert_const member_name
            (VEnumField { typ_name = snd name;
                          enum_name = member }),
       members_typed @ [ (member_info, member), expr_typed ]
    | None -> failwith "could not evaluate enum member"
  in
  let env = CheckerEnv.insert_type (QualifiedName ([], name)) enum_type env in
  let env, member_names = List.fold_left ~f:add_member ~init:(env, []) members in
  let enum_typed =
    Prog.Declaration.SerializableEnum { annotations; typ=enum_type; name; members = member_names } in
  (info, enum_typed), env

and type_extern_object env info annotations obj_name t_params methods =
  let type_params' = List.map ~f:snd t_params in
  let extern_type = Typed.Type.Extern { name = snd obj_name } in
  let extern_methods:  Typed.ExternMethods.t = { type_params = type_params'; methods = [] } in
  let env' = env
             |> CheckerEnv.insert_type_vars type_params'
             |> CheckerEnv.insert_type (BareName obj_name) extern_type
             |> CheckerEnv.insert_extern (BareName obj_name) extern_methods
  in
  let consume_method (constructors, methods) m =
    match snd m with
    | MethodPrototype.Constructor { annotations; name = cname; params } ->
       if snd cname <> snd obj_name then failwith "Constructor name and type name disagree";
       let params_typed = type_constructor_params env' Method params in
       let constructor_typed =
         Prog.MethodPrototype.Constructor { annotations;
                                            name = cname;
                                            params = params_typed }
       in
       ((fst m, constructor_typed) :: constructors, methods)
    | MethodPrototype.Method { annotations; return; name; type_params = t_params; params }
    | MethodPrototype.AbstractMethod { annotations; return; name; type_params = t_params; params } ->
       if snd name = snd obj_name
       then raise_s [%message "extern method must have different name from extern"
                        ~m:(m: MethodPrototype.t)];
       let method_type_params = List.map ~f:snd t_params in
       let env'' = CheckerEnv.insert_type_vars method_type_params env' in
       let params_typed = type_params env'' (Runtime Method) params in
       let return_typed = translate_type env'' [] return in
       let method_typed =
         match snd m with
         | Method _ ->
            Prog.MethodPrototype.Method
              { annotations;
                return = return_typed;
                name;
                type_params = t_params;
                params = params_typed }
         | AbstractMethod _ ->
            Prog.MethodPrototype.AbstractMethod
              { annotations;
                return = return_typed;
                name;
                type_params = t_params;
                params = params_typed }
         | _ -> failwith "bug"
       in
       (constructors, (fst m, method_typed) :: methods)
  in
  let (cs, ms) = List.fold_left ~f:consume_method ~init:([], []) methods in
  let extern_decl =
    Prog.Declaration.ExternObject
      { annotations;
        name = obj_name;
        type_params = t_params;
        methods = cs @ ms }
  in
  let extern_methods: Typed.ExternMethods.t =
    { type_params = List.map ~f:snd t_params;
      methods = List.map ~f:(method_prototype_to_extern_method obj_name) ms }
  in
  let extern_ctors =
    List.map cs ~f:(function
        | _, Prog.MethodPrototype.Constructor
              { annotations; name = cname; params = params_typed } ->
           let generic_args =
             List.map t_params
               ~f:(fun ty -> Type.TypeName (BareName ty))
           in
           Type.Constructor
             { type_params = type_params';
               wildcard_params = [];
               parameters = params_typed;
               return = SpecializedType { base = extern_type;
                                          args = generic_args } }
        | _ -> failwith "bug: expected constructor")
  in
  let env = CheckerEnv.insert_type ~shadowing:true (BareName obj_name) extern_type env in
  let env = CheckerEnv.insert_extern (BareName obj_name) extern_methods env in
  let env = List.fold extern_ctors ~init:env
              ~f:(fun env t -> CheckerEnv.insert_type_of ~shadowing:true (BareName obj_name) t env)
  in
  (info, extern_decl), env

and method_prototype_to_extern_method extern_name (m: Prog.MethodPrototype.t) : Typed.ExternMethods.extern_method =
    let open Typed.Type in
    let name, (fn : Typed.FunctionType.t) =
      match snd m with
      | Constructor { annotations; name; params } ->
          name,
          { type_params = [];
            return = TypeName (BareName extern_name);
            kind = Extern;
            parameters = params }
      | AbstractMethod { annotations; return; name; type_params; params }
      | Method { annotations; return; name; type_params; params } ->
          name,
          { type_params = List.map ~f:snd type_params;
            return = return;
            kind = Extern;
            parameters = params }
    in
    { name = snd name;
      typ = fn }

(* Section 7.3 *)
and type_type_def env ctx info annotations name typ_or_decl =
  match typ_or_decl with
  | Left typ ->
     let typ = translate_type env [] typ in
     let typedef_typed =
       Prog.Declaration.TypeDef
         { annotations;
           name;
           typ_or_decl = Left typ }
     in
     (info, typedef_typed), CheckerEnv.insert_type (BareName name) typ env
  | Right decl ->
     let decl_typed, env' = type_declaration env ctx decl in
     let (_, decl_name) = Declaration.name decl in
     let decl_typ = CheckerEnv.resolve_type_name (BareName (Info.dummy, decl_name)) env' in
     let typedef_typed =
       Prog.Declaration.TypeDef
         { annotations;
           name;
           typ_or_decl = Right decl_typed }
     in
     (info, typedef_typed), CheckerEnv.insert_type (BareName name) decl_typ env'

(* ? *)
and type_new_type env ctx info annotations name typ_or_decl =
  match typ_or_decl with
  | Left typ ->
     let typ = translate_type env [] typ in
     let typedef_typed =
       Prog.Declaration.TypeDef
         { annotations;
           name;
           typ_or_decl = Left typ }
     in
     let new_typ = Typed.Type.NewType { name = snd name; typ = typ } in
     (info, typedef_typed), CheckerEnv.insert_type (BareName name) new_typ env
  | Right decl ->
     let decl_typed, env' = type_declaration env ctx decl in
     let (_, decl_name) = Declaration.name decl in
     let decl_typ = CheckerEnv.resolve_type_name (BareName (Info.dummy, decl_name)) env' in
     let typedef_typed =
       Prog.Declaration.TypeDef
         { annotations;
           name;
           typ_or_decl = Right decl_typed }
     in
     let new_typ = Typed.Type.NewType { name = snd name; typ = decl_typ } in
     (info, typedef_typed), CheckerEnv.insert_type (BareName name) new_typ env'

(* Section 7.2.11.2 *)
and type_control_type env info annotations name t_params params =
  let simple_t_params = List.map ~f:snd t_params in
  let body_env = CheckerEnv.insert_type_vars simple_t_params env in
  let params_typed = type_params body_env (Runtime Control) params in
  let params_for_type = params_typed in
  let ctrl_decl =
    Prog.Declaration.ControlType
      { annotations;
        name;
        type_params = t_params;
        params = params_typed }
  in
  let ctrl_typ = Type.Control { type_params = simple_t_params;
                                parameters = params_for_type } in
  (info, ctrl_decl), CheckerEnv.insert_type (BareName name) ctrl_typ env

(* Section 7.2.11 *)
and type_parser_type env info annotations name t_params params =
  let simple_t_params = List.map ~f:snd t_params in
  let body_env = CheckerEnv.insert_type_vars simple_t_params env in
  let params_typed = type_params body_env (Runtime Parser) params in
  let parser_decl =
    Prog.Declaration.ParserType
      { annotations;
        name;
        type_params = t_params;
        params = params_typed }
  in
  let parser_typ = Type.Parser { type_params = simple_t_params;
                                 parameters = params_typed } in
  (info, parser_decl), CheckerEnv.insert_type (BareName name) parser_typ env

(* Section 7.2.12 *)
and type_package_type env info annotations name t_params params =
  let simple_t_params = List.map ~f:snd t_params in
  let body_env = CheckerEnv.insert_type_vars simple_t_params env in
  let params_typed, wildcard_params =
    type_params' ~gen_wildcards:true body_env (Constructor Package) params in
  let pkg_decl =
    Prog.Declaration.PackageType
      { annotations;
        name;
        type_params = t_params;
        params = params_typed }
  in
  let pkg_typ: Typed.PackageType.t =
    { type_params = simple_t_params;
      parameters = params_typed;
      wildcard_params }
  in
  let ret = Type.Package { pkg_typ with type_params = [] } in
  let ctor_typ =
    Type.Constructor { type_params = simple_t_params;
                       wildcard_params;
                       parameters = params_typed;
                       return = ret }
  in
  let env' =
    env
    |> CheckerEnv.insert_type_of ~shadowing:true (BareName name) ctor_typ
    |> CheckerEnv.insert_type ~shadowing:true (BareName name) (Type.Package pkg_typ)
  in
  (info, pkg_decl), env'

and check_param_shadowing params constructor_params =
  let open Types.Parameter in 
  let all_params = params @ constructor_params in
  let names = List.map ~f:(fun (_, p) -> snd p.variable) all_params in
  match List.find_a_dup ~compare:String.compare names with
  | Some dup -> raise_s [%message "duplicate parameter" ~dup]
  | None -> ()

and type_declaration (env: CheckerEnv.t) (ctx: DeclContext.t) (decl: Types.Declaration.t) : Prog.Declaration.t * CheckerEnv.t =
  match snd decl with
  | Constant { annotations; typ; name; value } ->
     type_constant env ctx (fst decl) annotations typ name value
  | Instantiation { annotations; typ; args; name; init } ->
     begin match init with
     | Some init -> failwith "initializer block in instantiation unsupported"
     | None -> type_instantiation env ctx (fst decl) annotations typ args name
     end
  | Parser { annotations; name; type_params = _; params; constructor_params; locals; states } ->
     check_param_shadowing params constructor_params;
     type_parser env (fst decl) name annotations params constructor_params locals states
  | Control { annotations; name; type_params; params; constructor_params; locals; apply } ->
     check_param_shadowing params constructor_params;
     type_control env (fst decl) name annotations type_params params constructor_params locals apply
  | Function { return; name; type_params; params; body } ->
     check_param_shadowing params [];
     let ctx: StmtContext.t = Function (translate_type env (List.map ~f:snd type_params) return) in
     type_function env ctx (fst decl) return name type_params params body
  | Action { annotations; name; params; body } ->
     check_param_shadowing params [];
     type_action env (fst decl) annotations name params body
  | ExternFunction { annotations; return; name; type_params; params } ->
     check_param_shadowing params [];
     type_extern_function env (fst decl) annotations return name type_params params
  | Variable { annotations; typ; name; init } ->
     type_variable env ctx (fst decl) annotations typ name init
  | ValueSet { annotations; typ; size; name } ->
     type_value_set env ctx (fst decl) annotations typ size name
  | Table { annotations; name; properties } ->
     type_table env ctx (fst decl) annotations name properties
  | Header { annotations; name; fields } ->
     type_header env (fst decl) annotations name fields
  | HeaderUnion { annotations; name; fields } ->
     type_header_union env (fst decl) annotations name fields
  | Struct { annotations; name; fields } ->
     type_struct env (fst decl) annotations name fields
  | Error { members } ->
     type_error env (fst decl) members
  | MatchKind { members } ->
     type_match_kind env (fst decl) members
  | Enum { annotations; name; members } ->
     type_enum env (fst decl) annotations name members
  | SerializableEnum { annotations; typ; name; members } ->
     type_serializable_enum env ctx (fst decl) annotations typ name members
  | ExternObject { annotations; name; type_params; methods } ->
     type_extern_object env (fst decl) annotations name type_params methods
  | TypeDef { annotations; name; typ_or_decl } ->
     type_type_def env ctx (fst decl) annotations name typ_or_decl
  | NewType { annotations; name; typ_or_decl } ->
     type_new_type env ctx (fst decl) annotations name typ_or_decl
  | ControlType { annotations; name; type_params; params } ->
     check_param_shadowing params [];
     type_control_type env (fst decl) annotations name type_params params
  | ParserType { annotations; name; type_params; params } ->
     check_param_shadowing params [];
     type_parser_type env (fst decl) annotations name type_params params
  | PackageType { annotations; name; type_params; params } ->
     check_param_shadowing params [];
     type_package_type env (fst decl) annotations name type_params params

and type_declarations env ctx decls =
  let f (decls_typed, env) decl =
    let decl_typed, env = type_declaration env ctx decl in
    decls_typed @ [decl_typed], env
  in
  let decls, env = List.fold_left ~f ~init:([], env) decls in
  decls, env

(* Entry point function for type checker *)
let check_program renamer (program:Types.program) : CheckerEnv.t * Prog.program =
  let Program top_decls = program in
  let initial_env = CheckerEnv.empty_with_renamer renamer in
  let prog, env = type_declarations initial_env DeclContext.TopLevel top_decls in
  env, Prog.Program prog
