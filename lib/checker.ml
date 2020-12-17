open Types
open Typed
open Util
open Checker_env

(* hack *)
module Petr4Error = Error
module Petr4Info = Info
open Core_kernel
open Petr4Error
module Error = Petr4Error
module Info = Petr4Info
let (=) = Stdlib.(=)
let (<>) = Stdlib.(<>)

let make_assert expected unwrap = fun info typ ->
  match unwrap typ with
  | Some v -> v
  | None -> raise_mismatch info expected typ

let binop_to_coq_binop (n: Op.pre_bin) : Prog.coq_OpBin =
  match n with
  | Op.Plus -> Plus
  | Op.PlusSat -> PlusSat
  | Op.Minus -> Minus
  | Op.MinusSat -> MinusSat
  | Op.Mul -> Mul
  | Op.Div -> Div
  | Op.Mod -> Mod
  | Op.Shl -> Shl
  | Op.Shr -> Shr
  | Op.Le -> Le
  | Op.Ge -> Ge
  | Op.Lt -> Lt
  | Op.Gt -> Gt
  | Op.Eq -> Eq
  | Op.NotEq -> NotEq
  | Op.BitAnd -> BitAnd
  | Op.BitXor -> BitXor
  | Op.BitOr -> BitOr
  | Op.PlusPlus -> PlusPlus
  | Op.And -> And
  | Op.Or -> Or

let uop_to_coq_uop (n: Op.pre_uni) : Prog.coq_OpUni =
  match n with
  | Op.Not -> Not
  | Op.BitNot -> BitNot
  | Op.UMinus -> UMinus

let info_of_expr (MkExpression (info, _, _, _): Prog.coq_Expression) = info

let preexpr_of_expr (MkExpression (_, exp, _, _): Prog.coq_Expression) = exp

let type_of_expr (MkExpression (_, _, typ, _): Prog.coq_Expression) = typ

let dir_of_expr (MkExpression (_, _, _, dir): Prog.coq_Expression) = dir

let info_of_stmt (MkStatement (info, _, _): Prog.coq_Statement) = info

let prestmt_of_stmt (MkStatement (_, stmt, _): Prog.coq_Statement) = stmt

let type_of_stmt (MkStatement (_, _, typ): Prog.coq_Statement) = typ

let opt_of_param (MkParameter (opt, _, _, _, _): Typed.coq_P4Parameter) = opt

let dir_of_param (MkParameter (_, dir, _, _, _): Typed.coq_P4Parameter) = dir

let type_of_param (MkParameter (_, _, typ, _, _): Typed.coq_P4Parameter) = typ

let default_arg_id_of_param (MkParameter (_, _, _, default_arg, _): Typed.coq_P4Parameter) = default_arg

let var_of_param (MkParameter (_, _, _, _, var): Typed.coq_P4Parameter) = var

let has_default_arg p =
  default_arg_id_of_param p <> None

let find_default_arg env (MkParameter (_, _, _, arg_id, _): Typed.coq_P4Parameter) =
  match arg_id with
  | Some arg_id -> Checker_env.find_default_arg arg_id env |> Some
  | None -> None

let is_optional (param: Types.Parameter.t) =
  let f ((_, a): Types.Annotation.t) =
    match snd a.body with
    | Empty -> String.equal a.name.str "optional"
    | _ -> false
  in
  List.exists ~f (snd param).annotations

let params_of_fn_type (MkFunctionType (_, parameters, _, _)) = parameters

let assert_array = make_assert "array"
    begin function
      | TypArray (typ, size) -> Some (typ, size)
      | _ -> None
    end

let assert_bool = make_assert "bool"
    begin function
      | TypBool -> Some Type.Bool
      | _ -> None
    end

let assert_bit = make_assert "unsigned int"
    begin function
      | TypBit width -> Some width
      | _ -> None
    end

(* numeric(t) <=> t = int \/ t = int<n> \/ t = bit<n> *)
let assert_numeric = make_assert "integer"
    begin function
      | TypInteger -> Some None
      | TypInt typ
      | TypBit typ -> Some (Some typ)
      | _ -> None
    end

let field_cmp (MkFieldType (name1, _)) (MkFieldType (name2, _)) =
  String.compare name1.str name2.str

let sort_fields = List.sort ~compare:field_cmp

(* Checks if [t] is a specific p4 type as satisfied by [f] under [env] *)
let rec is_extern (env: Checker_env.t) (typ: Typed.coq_P4Type) =
  match typ with
  | TypExtern _ -> true
  | TypTypeName n ->
    begin match Checker_env.resolve_type_name n env with
      | TypTypeName n' ->
        if P4name.name_eq n n'
        then false
        else is_extern env (TypTypeName n')
      | typ -> is_extern env typ
    end
  | TypNewType (s, typ) -> is_extern env typ
  | TypSpecializedType (typ, _) -> is_extern env typ
  | _ -> false

(* Ugly hack *)
let real_name_for_type_member env (typ_name: P4name.t) (name: P4string.t) : P4name.t =
  begin match typ_name with
    | QualifiedName (qs, typ_name) ->
      let prefixed_name = {name with str = typ_name.str ^ "." ^ name.str} in
      QualifiedName (qs, prefixed_name)
    | BareName typ_name ->
      let prefixed_name = {name with str = typ_name.str ^ "." ^ name.str} in
      BareName prefixed_name
  end

let rec min_size_in_bits' env (info: Info.t) (hdr_type: coq_P4Type) : int =
  match saturate_type env hdr_type with
  | TypBit width | TypInt width ->
    width
  | TypVarBit _ ->
    0
  | TypNewType (_, typ)
  | TypEnum (_, Some typ, _) ->
    min_size_in_bits' env info typ
  | TypStruct fields
  | TypHeader fields ->
    fields
    |> List.map ~f:(field_width_bits env info)
    |> List.fold ~init:0 ~f:(+)
  | TypHeaderUnion fields ->
    fields
    |> List.map ~f:(field_width_bits env info)
    |> List.fold ~init:0 ~f:min
  | TypArray (typ, size) ->
    (Obj.magic size) * min_size_in_bits' env info typ
  | _ -> raise_mismatch info "header or header union" hdr_type

and field_width_bits env info (MkFieldType (_, typ): coq_FieldType) : int =
  min_size_in_bits' env info typ

and min_size_in_bits env (info: Info.t) (hdr_type: coq_P4Type) : Bigint.t =
  Bigint.of_int (min_size_in_bits' env info hdr_type)

and min_size_in_bytes env info hdr_type =
  let bits = min_size_in_bits' env info hdr_type in
  Bigint.of_int ((bits + 7) asr 3)

(* Evaluate the expression [expr] at compile time. Make sure to
 * typecheck the expression before trying to evaluate it! *)
and compile_time_eval_expr (env: Checker_env.t) (expr: Prog.coq_Expression) : Prog.coq_ValueBase option =
  let MkExpression (tags, expr, typ, dir) = expr in
  match expr with
  | ExpName name ->
    begin match Checker_env.find_const_opt name env with
      | Some (ValBase b) -> Some b
      | _ -> None
    end
  | ExpBool b -> Some (ValBaseBool b)
  | ExpString str -> Some (ValBaseString str)
  | ExpInt i ->
    begin match i.width_signed with
      | None ->
        Some (ValBaseInteger i.value)
      | Some (width, signed) ->
        if signed
        then Some (ValBaseInt (width, i.value))
        else Some (ValBaseBit (width, i.value))
    end
  | ExpUnaryOp (op, arg) ->
    begin match compile_time_eval_expr env arg with
      | Some arg ->
        Some (Ops.interp_unary_op op arg)
      | None -> None
    end
  | ExpBinaryOp (op, (l, r)) ->
    begin match compile_time_eval_expr env l,
                compile_time_eval_expr env r with
    | Some l, Some r ->
      Some (Ops.interp_binary_op op l r)
    | _ -> None
    end
  | ExpCast (typ, expr) ->
    let expr_val = compile_time_eval_expr env expr in
    let type_lookup name = Checker_env.resolve_type_name name env in
    option_map (Ops.interp_cast ~type_lookup typ) expr_val
  | ExpList values ->
    begin match compile_time_eval_exprs env values with
      | Some vals -> Some (ValBaseTuple vals)
      | None -> None
    end
  | ExpTypeMember (typ, name) ->
    let real_name = real_name_for_type_member env typ name in
    begin match Checker_env.find_const_opt real_name env with
      | Some (ValBase b) -> Some b
      | _ -> None
    end
  | ExpErrorMember t ->
    Some (ValBaseError t)
  | ExpRecord entries ->
    let opt_entries =
      List.map ~f:(fun (MkKeyValue (_, key, value)) ->
          match compile_time_eval_expr env value with
          | Some v -> Some (key, v)
          | None -> None)
        entries
    in
    begin match Util.list_option_flip opt_entries with
      | Some es -> Some (ValBaseRecord es)
      | None -> None
    end
  | ExpBitStringAccess (bits, hi, lo) ->
    begin match compile_time_eval_expr env bits with
      | Some (ValBaseInt (w, v))
      | Some (ValBaseBit (w, v)) ->
        let slice_width = Bigint.(to_int_exn (hi - lo + one)) in
        let slice_val = Bitstring.bitstring_slice v hi lo in
        Some (ValBaseBit (slice_width, slice_val))
      | _ -> None
    end
  | ExpDontCare -> Some (ValBaseSet (ValSetUniversal))
  | ExpExpressionMember (expr, {str="size";_}) ->
    begin match saturate_type env (type_of_expr expr) with
      | TypArray (_, size) -> Some (ValBaseInteger (Bigint.of_int size))
      | _ -> None
    end
  | ExpExpressionMember (expr, name) ->
    begin match compile_time_eval_expr env expr with
      | Some (ValBaseStruct fields)
      | Some (ValBaseHeader (fields, _))
      | Some (ValBaseUnion fields) ->
        fields
        |> List.find ~f:(fun (n, _) -> P4string.eq n name)
        |> option_map snd
      | _ -> None
    end
  | ExpFunctionCall (func, [], args) ->
    let MkExpression (_, func, _, _) = func in
    begin match func with
      | ExpExpressionMember (expr, {str="minSizeInBits"; _}) ->
        let MkExpression (i, expr, typ, _) = expr in
        let typ = saturate_type env typ in
        let size = min_size_in_bits env i typ in
        Some (ValBaseInteger size)
      | ExpExpressionMember (expr, {str="minSizeInBytes"; _}) ->
        let MkExpression (i, expr, typ, _) = expr in
        let typ = saturate_type env typ in
        let size = min_size_in_bytes env i typ in
        Some (ValBaseInteger size)
      | _ -> None
    end
  | _ ->
    None

and compile_time_eval_exprs env exprs : Prog.coq_ValueBase list option =
  let options = List.map ~f:(compile_time_eval_expr env) exprs in
  Util.list_option_flip options

and bigint_of_value (v: Prog.coq_ValueBase) =
  match v with
  | ValBaseInt (_, v)
  | ValBaseBit (_, v)
  | ValBaseInteger v ->
    Some v
  | _ -> None

and compile_time_eval_bigint env expr: Bigint.t =
  match
    compile_time_eval_expr env expr
    |> option_map bigint_of_value
    |> option_collapse
  with
  | Some bigint -> bigint
  | None -> failwith "could not compute compile-time-known numerical value for expr"

(* Evaluate the declaration [decl] at compile time, updating env.const
 * with any bindings made in the declaration.  Make sure to typecheck
 * [decl] before trying to evaluate it! *)
and compile_time_eval_decl (env: Checker_env.t) (decl: Prog.coq_Declaration) : Checker_env.t =
  match decl with
  | DeclConstant (_, _, name, value) ->
    Checker_env.insert_const (BareName name) (ValBase value) env
  | _ -> env

and get_type_params (t: coq_P4Type) : P4string.t list =
  match t with
  | TypPackage (type_params, _, _)
  | TypControl (MkControlType (type_params, _))
  | TypParser (MkControlType (type_params, _))
  | TypFunction (MkFunctionType (type_params, _, _, _)) ->
    type_params
  | _ ->
    []

and drop_type_params (t: coq_P4Type) : coq_P4Type =
  match t with
  | TypPackage (_, wild_params, params) ->
    TypPackage ([], wild_params, params)
  | TypControl (MkControlType (_, params)) ->
    TypControl (MkControlType ([], params))
  | TypParser (MkControlType (_, params)) ->
    TypParser (MkControlType ([], params))
  | TypFunction (MkFunctionType (_, params, kind, ret)) ->
    TypFunction (MkFunctionType ([], params, kind, ret))
  | t -> t

(* Eliminate all type references in typ and replace them with the type they
 * refer to. The result of saturation will contain no TypeName constructors
 * anywhere. It may contain TypeName constructors.
 *
 * Warning: this will loop forever if you give it an environment with circular
 * TypeName references.
*)
and saturate_type (env: Checker_env.t) (typ: coq_P4Type) : coq_P4Type =
  let saturate_types env types =
    List.map ~f:(saturate_type env) types
  in
  let saturate_field env (MkFieldType (name, typ)) =
    MkFieldType (name, saturate_type env typ)
  in
  let saturate_rec env (fields: coq_FieldType list) : coq_FieldType list =
    List.map ~f:(saturate_field env) fields
  in
  let saturate_param env (MkParameter (opt, direction, typ, opt_arg_id, variable)) =
    MkParameter (opt, direction, saturate_type env typ, opt_arg_id, variable)
  in
  let saturate_params env params =
    List.map ~f:(saturate_param env) params
  in
  let saturate_ctrl env (MkControlType (type_params, params)) =
    let env = Checker_env.insert_type_vars type_params env in
    MkControlType (type_params, List.map ~f:(saturate_param env) params)
  in
  let saturate_function env (MkFunctionType (type_params, params, kind, ret)) =
    let env = Checker_env.insert_type_vars type_params env in
    MkFunctionType (type_params,
                    saturate_params env params,
                    kind,
                    saturate_type env ret)
  in
  match typ with
  | TypTypeName t ->
    begin match Checker_env.resolve_type_name_opt t env with
      | None -> typ
      | Some (TypTypeName t') ->
        if P4name.name_eq t' t
        then typ
        else saturate_type env (TypTypeName t')
      | Some typ' ->
        saturate_type env typ'
    end
  | TypBool | TypString | TypInteger
  | TypInt _ | TypBit _ | TypVarBit _
  | TypError | TypMatchKind | TypVoid
  | TypNewType _
  | TypTable _ ->
    typ
  | TypArray (typ, size) ->
    TypArray (saturate_type env typ, size)
  | TypTuple types ->
    TypTuple (saturate_types env types)
  | TypList types ->
    TypList (saturate_types env types)
  | TypRecord rec_typ ->
    TypRecord (saturate_rec env rec_typ)
  | TypSet typ ->
    TypSet (saturate_type env typ)
  | TypHeader rec_typ ->
    TypHeader (saturate_rec env rec_typ)
  | TypHeaderUnion rec_typ ->
    TypHeaderUnion (saturate_rec env rec_typ)
  | TypStruct rec_typ ->
    TypStruct (saturate_rec env rec_typ)
  | TypEnum (name, typ, members) ->
    TypEnum (name, option_map (saturate_type env) typ, members)
  | TypSpecializedType (base, args) ->
    TypSpecializedType (saturate_type env base,
                        saturate_types env args)
  | TypPackage (type_params, wildcard_params, params) ->
    let env = Checker_env.insert_type_vars type_params env in
    let env = Checker_env.insert_type_vars wildcard_params env in
    TypPackage (type_params,
                wildcard_params,
                saturate_params env params)
  | TypControl ctrl ->
    TypControl (saturate_ctrl env ctrl)
  | TypParser ctrl ->
    TypParser (saturate_ctrl env ctrl)
  | TypExtern extern ->
    TypExtern extern
  | TypFunction func ->
    TypFunction (saturate_function env func)
  | TypAction (data_params, ctrl_params) ->
    TypAction (saturate_params env data_params,
               saturate_params env ctrl_params)
  | TypConstructor (type_params, wildcard_params, params, ret) ->
    let env = Checker_env.insert_type_vars type_params env in
    TypConstructor (type_params,
                    wildcard_params,
                    saturate_params env params,
                    saturate_type env ret)
      
and reduce_type (env: Checker_env.t) (typ: coq_P4Type) : coq_P4Type =
  let typ = saturate_type env typ in
  match typ with
  | TypSpecializedType (base, args) ->
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
            reduce_type (Checker_env.insert_types pairs env) base
          | Unequal_lengths ->
            failwith "mismatch in # of type params and type args"
        end
    end
  | _ -> typ

and reduce_to_underlying_type (env: Checker_env.t) (typ: coq_P4Type) : coq_P4Type =
  let typ = reduce_type env typ in
  match typ with
  | TypNewType (_, typ) -> reduce_to_underlying_type env typ
  | TypEnum (_, Some typ, _) -> reduce_to_underlying_type env typ
  | _ -> typ

type var_constraint = P4string.t * coq_P4Type option
type var_constraints = var_constraint list
type soln = var_constraints option

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
    if P4string.eq v var
    then (v, Some typ)
    else (v, emp)
  in
  List.map ~f:update empty

(* This needs a real meet operator *)
let rec merge_constraints env xs ys =
  let fail () =
    failwith "could not merge constraint sets during type argument inference"
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

and constraints_to_type_args _ (cs: var_constraints) : (P4string.t * coq_P4Type) list =
  let constraint_to_type_arg (var, type_opt) =
    match type_opt with
    | Some t -> (var, t)
    | None -> (var, TypVoid)
  in
  List.map ~f:constraint_to_type_arg cs

and gen_all_constraints (env: Checker_env.t) ctx unknowns (params_args: (coq_P4Parameter * Expression.t option) list) constraints =
  match params_args with
  | (param, Some arg) :: more ->
    let arg_typed = type_expression env ctx arg in
    let MkExpression (_, _, expr_typ, _) = arg_typed in
    let MkParameter (_, _, param_type, _, _) = param in
    begin match solve_types env [] unknowns param_type expr_typ with
      | Some arg_constraints ->
        let constraints = merge_constraints env constraints arg_constraints in
        gen_all_constraints env ctx unknowns more constraints
      | None -> raise_s [%message "Could not solve type equality."
                         ~param:(reduce_type env param_type: coq_P4Type) ~arg_typ:(reduce_type env expr_typ: coq_P4Type)]
    end
  | (param_type, None) :: more ->
    gen_all_constraints env ctx unknowns more constraints
  | [] ->
    constraints

and infer_type_arguments env ctx ret type_params_args params_args constraints =
  let insert (env, args, unknowns) (type_var, type_arg) =
    match type_arg with
    | Some arg ->
      Checker_env.insert_type (BareName type_var) arg env, args @ [(type_var, arg)], unknowns
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
                   Checker_env.t -> P4string.t list ->
  f:('a * 'b -> soln) -> 'a list -> 'b list -> soln =
  fun env unknowns ~f xs ys ->
  zip_map_fold xs ys
    ~f:f
    ~merge:(merge_solutions env)
    ~init:(Some (empty_constraints unknowns))
  |> option_collapse
  |> option_map List.rev

and solve_record_type_equality env equiv_vars unknowns (rec1: coq_FieldType list) (rec2: coq_FieldType list) =
  let solve_fields (MkFieldType (name1, type1), MkFieldType (name2, type2)) =
    if P4string.eq name1 name2
    then solve_types env equiv_vars unknowns type1 type2
    else None
  in
  let fields1 = sort_fields rec1 in
  let fields2 = sort_fields rec2 in
  solve_lists env unknowns fields1 fields2 ~f:solve_fields

and solve_params_equality env equiv_vars unknowns ps1 ps2 =
  let param_eq (MkParameter (opt1, dir1, typ1, _, var1),
                MkParameter (opt2, dir2, typ2, _, var2)) =
    if eq_dir dir1 dir2
    then solve_types env equiv_vars unknowns typ1 typ2
    else None
  in
  solve_lists env unknowns ~f:param_eq ps1 ps2

and solve_control_type_equality env equiv_vars unknowns ctrl1 ctrl2 =
  let MkControlType (type_params1, params1) = ctrl1 in
  let MkControlType (type_params2, params2) = ctrl2 in
  match List.zip type_params1 type_params2 with
  | Ok param_pairs ->
    let equiv_vars' = equiv_vars @ param_pairs in
    solve_params_equality env equiv_vars' unknowns params1 params2
  | Unequal_lengths -> None

and solve_function_type_equality env equiv_vars unknowns func1 func2 =
  let MkFunctionType (type_params1, params1, kind1, ret1) = func1 in
  let MkFunctionType (type_params2, params2, kind2, ret2) = func2 in
  match List.zip type_params1 type_params2 with
  | Ok param_pairs ->
    let equiv_vars' = equiv_vars @ param_pairs in
    merge_solutions env (solve_types env equiv_vars' unknowns ret1 ret2)
      (solve_params_equality env equiv_vars' unknowns params1 params2)
  | Unequal_lengths -> None

and type_vars_equal_under equiv_vars tv1 tv2 =
  match equiv_vars with
  | (a, b) :: rest ->
    if P4string.eq tv1 a || P4string.eq tv2 b
    then P4string.eq tv1 a && P4string.eq tv2 b
    else type_vars_equal_under rest tv1 tv2
  | [] ->
    P4string.eq tv1 tv2

(* [type_equality env t1 t2] is true if and only if expression type t1
 * is equivalent to expression type t2 under environment env.
 *  Alpha equivalent types are equal. *)
and solve_types 
    ?(casts=true)
    (env: Checker_env.t)
    (equiv_vars: (P4string.t * P4string.t) list)
    (unknowns: P4string.t list)
    (type1: coq_P4Type)
    (type2: coq_P4Type)
  : soln =
  let t1 = reduce_type env type1 in
  let t2 = reduce_type env type2 in
  begin match t1, t2 with
    | TypTypeName (QualifiedName _), _
    | _, TypTypeName (QualifiedName _) ->
      failwith "Name in saturated type."
    | TypSpecializedType (TypExtern e1, args1),
      TypSpecializedType (TypExtern e2, args2) ->
      let ok (t1, t2) = solve_types env equiv_vars unknowns t1 t2 in
      if P4string.eq e1 e2
      then solve_lists env unknowns ~f:ok args1 args2
      else None
    | TypSpecializedType (base, args), _
    | _, TypSpecializedType (base, args) ->
      raise_s [%message "Stuck specialized type." ~t:(TypSpecializedType (base, args):coq_P4Type)]
    | TypTypeName (BareName tv1), TypTypeName (BareName tv2) ->
      if type_vars_equal_under equiv_vars tv1 tv2
      then Some (empty_constraints unknowns)
      else Some (single_constraint unknowns tv1 t2)
    | TypTypeName (BareName tv), typ ->
      if List.mem ~equal:P4string.eq unknowns tv
      then Some (single_constraint unknowns tv typ)
      else None
    | TypNewType (name1, typ1), TypNewType (name2, typ2) ->
      if P4string.eq name1 name2
      then solve_types ~casts env equiv_vars unknowns typ1 typ2
      else None
    | TypBool, TypBool
    | TypString, TypString
    | TypInteger, TypInteger
    | TypError, TypError
    | TypMatchKind, TypMatchKind
    | TypVoid, TypVoid ->
      Some (empty_constraints unknowns)
    | TypBit width1, TypBit width2
    | TypInt width1, TypInt width2
    | TypVarBit width1, TypVarBit width2 ->
      if width1 = width2
      then Some (empty_constraints unknowns)
      else None
    | TypArray (typ1, size1), TypArray (typ2, size2) ->
      if size1 = size2
      then solve_types env equiv_vars unknowns typ1 typ2
      else None
    | TypList types1, TypList types2
    | TypTuple types1, TypTuple types2 ->
      let ok (t1, t2) = solve_types env equiv_vars unknowns t1 t2 in
      solve_lists env unknowns ~f:ok types1 types2
    | TypRecord rec1, TypRecord rec2
    | TypHeader rec1, TypHeader rec2
    | TypHeaderUnion rec1, TypHeaderUnion rec2
    | TypStruct rec1, TypStruct rec2 ->
      solve_record_type_equality env equiv_vars unknowns rec1 rec2
    | TypSet ty1, TypSet ty2 ->
      solve_types env equiv_vars unknowns ty1 ty2
    | TypExtern name1, TypExtern name2
    | TypEnum (name1, _, _), TypEnum (name2, _, _) ->
      if P4string.eq name1 name2 then Some (empty_constraints unknowns) else None
    | TypPackage (type_params1, _, params1),
      TypPackage (type_params2, _, params2) ->
      begin match List.zip type_params1 type_params2 with
        | Ok param_pairs ->
          let equiv_vars' = equiv_vars @ param_pairs in
          solve_params_equality env equiv_vars' unknowns params1 params2
        | Unequal_lengths -> None
      end
    | TypControl ctrl1, TypControl ctrl2
    | TypParser ctrl1, TypParser ctrl2 ->
      solve_control_type_equality env equiv_vars unknowns ctrl1 ctrl2
    | TypAction (data1, ctrl1), TypAction (data2, ctrl2) ->
      merge_solutions env
        (solve_params_equality env equiv_vars unknowns data1 data2)
        (solve_params_equality env equiv_vars unknowns ctrl1 ctrl2)
    | TypFunction func1, TypFunction func2 ->
      solve_function_type_equality env equiv_vars unknowns func1 func2
    | TypConstructor (type_params1, wildcard_params1, params1, ret1),
      TypConstructor (type_params2, wildcard_params2, params2, ret2) ->
      begin match List.zip type_params1 type_params2 with
        | Ok param_pairs ->
          let equiv_vars' = equiv_vars @ param_pairs in
          merge_solutions env (solve_types env equiv_vars' unknowns ret1 ret2)
            (solve_params_equality env equiv_vars' unknowns params1 params2)
        | Unequal_lengths -> None
      end
    | TypTable res_name1, TypTable res_name2 ->
      if P4string.eq res_name1 res_name2
      then Some (empty_constraints unknowns)
      else None
    | x, y when casts && cast_ok env x y ->
      Some (empty_constraints unknowns)
    | x, y when casts && cast_ok env y x ->
      Some (empty_constraints unknowns)
    (* We could replace this all with | _, _ -> false. I am writing it this way
     * because when I change Type.t I want Ocaml to warn me about missing match
     * cases. *)
    | TypBool, _
    | TypString, _
    | TypInteger, _
    | TypError, _
    | TypMatchKind, _
    | TypVoid, _
    | TypBit _, _
    | TypInt _, _
    | TypVarBit _, _
    | TypArray _, _
    | TypTuple _, _
    | TypList _, _
    | TypRecord _, _
    | TypSet _, _
    | TypHeader _, _
    | TypHeaderUnion _, _
    | TypNewType _, _
    | TypStruct _, _
    | TypEnum _, _
    | TypControl _, _
    | TypParser _, _
    | TypPackage _, _
    | TypExtern _, _
    | TypAction _, _
    | TypFunction _, _
    | TypConstructor _, _
    | TypTable _, _ ->
       None
  end

and sort_entries entries =
  let entry_cmp (_, e1: KeyValue.t) (_, e2: KeyValue.t) =
    String.compare e1.key.str e2.key.str
  in
  List.sort ~compare:entry_cmp entries

(* [type_equality env t1 t2] is true if and only if expression type t1
 * is equivalent to expression type t2 under environment env.
 *  Alpha equivalent types are equal. *)
and type_equality env equiv_vars t1 t2 : bool =
  solve_types ~casts:false env equiv_vars [] t1 t2 <> None

and assert_same_type env info1 info2 typ1 typ2 =
  if type_equality env [] typ1 typ2
  then (typ1, typ2)
  else let info = Info.merge info1 info2 in
    raise_type_error info (Type_Difference (typ1, typ2))

and assert_type_equality env info typ1 typ2 : unit =
  let t1 = reduce_type env typ1 in
  let t2 = reduce_type env typ2 in
  if type_equality env [] t1 t2
  then ()
  else raise @@ Error.Type (info, Type_Difference (t1, t2))

and compile_time_known_expr (env: Checker_env.t) (expr: Prog.coq_Expression) : bool =
  match compile_time_eval_expr env expr with
  | Some _ -> true
  | None ->
    let MkExpression (_, _, typ, _) = expr in
    match reduce_type env typ with
    | TypSpecializedType (TypExtern _, _)
    | TypExtern _
    | TypPackage _
    | TypControl _
    | TypParser _ -> true
    | _ -> false

and type_expression (env: Checker_env.t) (ctx: Typed.coq_ExprContext) (exp_info, exp: Expression.t)
  : Prog.coq_Expression =
  let (pre_expr: Prog.coq_ExpressionPreT), typ, dir =
    match exp with
    | True ->
      (ExpBool true, TypBool, Directionless)
    | False ->
      (ExpBool false, TypBool, Directionless)
    | String str ->
      (ExpString str, TypString, Directionless)
    | Int i ->
      type_int i
    | Name name ->
      let typ, dir = Checker_env.find_type_of name env in
      ExpName name, typ, dir
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
      type_binary_op env ctx exp_info op args
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
  MkExpression (exp_info, pre_expr, typ, dir)

and add_cast env (expr: Prog.coq_Expression) new_typ : Prog.coq_Expression =
  let MkExpression (info, pre_expr, orig_typ, dir) = expr in
  if cast_ok env orig_typ new_typ
  then MkExpression (info, ExpCast (new_typ, expr), new_typ, dir)
  else failwith "Cannot cast."

and cast_if_needed env (expr: Prog.coq_Expression) typ : Prog.coq_Expression =
  let MkExpression (info, pre_expr, expr_typ, dir) = expr in
  if type_equality env [] expr_typ typ
  then expr
  else match typ with
    | TypSet elt_typ -> add_cast env (cast_if_needed env expr elt_typ) typ
    | typ -> add_cast env expr typ

and cast_to_same_type (env: Checker_env.t) (ctx: Typed.coq_ExprContext) (exp1: Expression.t) (exp2: Expression.t) =
  let exp1 = type_expression env ctx exp1 in
  let typ1 = type_of_expr exp1 in
  let exp2 = type_expression env ctx exp2 in
  let typ2 = type_of_expr exp2 in
  if type_equality env [] typ1 typ2
  then exp1, exp2
  else if cast_ok env typ1 typ2
  then add_cast env exp1 typ2, exp2
  else if cast_ok env typ2 typ1
  then exp1, add_cast env exp2 typ1
  else failwith "cannot cast types so that they agree"

and cast_expression (env: Checker_env.t) ctx (typ: coq_P4Type) (exp_info, exp: Expression.t) =
  let typ = reduce_type env typ in
  match exp with
  | String _
  | Cast _ ->
    let exp_typed = type_expression env ctx (exp_info, exp) in
    assert_type_equality env exp_info typ (type_of_expr exp_typed);
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
    let rec get_types (typ: coq_P4Type) =
      match typ with
      | TypTuple types
      | TypList types ->
        types
      | TypHeader fields
      | TypStruct fields ->
        List.map ~f:(fun (MkFieldType (_, typ)) -> typ) fields
      | TypSet t ->
        get_types t
      | _ -> [typ]
    in
    let types = get_types typ in
    let values_casted =
      List.zip_exn types values
      |> List.map ~f:(fun (t, v) -> cast_expression env ctx t v)
    in
    cast_if_needed env (MkExpression (exp_info, ExpList values_casted, TypList types, Directionless)) typ
  | Record { entries } ->
    let entries = sort_entries entries in
    let fields =
      match typ with
      | TypRecord fields
      | TypHeader fields
      | TypStruct fields ->
        sort_fields fields
      | _ -> failwith "can't cast record"
    in
    let cast_entry (field, entry: coq_FieldType * KeyValue.t) : Prog.coq_KeyValue =
      let MkFieldType (field_name, field_type) = field in
      if P4string.neq field_name (snd entry).key
      then failwith "bad names";
      let value_typed: Prog.coq_Expression =
        cast_expression env ctx field_type (snd entry).value
      in
      MkKeyValue (fst entry, (snd entry).key, value_typed)
    in
    let entries_casted =
      List.zip_exn fields entries
      |> List.map ~f:cast_entry
    in
    let exp_typed: Prog.coq_Expression =
      MkExpression (exp_info,
                    ExpRecord entries_casted,
                    TypRecord fields,
                    Directionless)
    in
    cast_if_needed env exp_typed typ
  | BinaryOp {op = (_, Op.Eq) as op; args = (left, right)}
  | BinaryOp {op = (_, Op.NotEq) as op; args = (left, right)}
  | BinaryOp {op = (_, Op.Lt) as op; args = (left, right)}
  | BinaryOp {op = (_, Op.Le) as op; args = (left, right)}
  | BinaryOp {op = (_, Op.Gt) as op; args = (left, right)}
  | BinaryOp {op = (_, Op.Ge) as op; args = (left, right)} ->
    let left_typed, right_typed = cast_to_same_type env ctx left right in
    let exp, exp_typ, dir = check_binary_op env exp_info op left_typed right_typed in
    let exp_typed: Prog.coq_Expression =
      MkExpression (exp_info, exp, exp_typ, dir)
    in
    cast_if_needed env exp_typed typ
  | BinaryOp {op = (_, Op.Div) as op; args = (left, right)}
  | BinaryOp {op = (_, Op.Mod) as op; args = (left, right)} ->
    let exp, exp_typ, dir = type_binary_op env ctx exp_info op (left, right) in
    let exp_typed: Prog.coq_Expression =
      MkExpression (exp_info, exp, exp_typ, dir)
    in
    cast_if_needed env exp_typed typ
  | BinaryOp {op; args = (left, right)} ->
    let left_typed = cast_expression env ctx typ left in
    let right_typed =
      if snd op <> Op.Shl && snd op <> Op.Shr
      then cast_expression env ctx typ right
      else type_expression env ctx right
    in
    let exp, exp_typ, dir = check_binary_op env exp_info op left_typed right_typed in
    MkExpression (exp_info, exp, exp_typ, dir)
  | Ternary { cond; tru; fls } ->
    let cond_typed = cast_expression env ctx TypBool cond in
    let tru_typed = cast_expression env ctx typ tru in
    let fls_typed = cast_expression env ctx typ fls in
    MkExpression (exp_info,
                  ExpTernary (cond_typed, tru_typed, fls_typed),
                  typ,
                  Directionless)
  | Mask { expr; mask } ->
    let elt_width =
      match reduce_type env typ with
      | TypSet (TypBit width)
      | TypSet (TypNewType (_, TypBit width))
      | TypSet (TypEnum (_, Some (TypBit width), _)) ->
        width
      | _ -> failwith "must be a set of bit<w>"
    in
    let elt_type = TypBit elt_width in
    let expr_typed = cast_expression env ctx elt_type expr in
    let mask_typed = cast_expression env ctx elt_type mask in
    MkExpression (exp_info,
                  ExpMask (expr_typed, mask_typed),
                  TypSet (elt_type),
                  Directionless)
  | Range { lo; hi } ->
    let elt_typ =
      match reduce_type env typ with
      | TypSet typ -> typ
      | _ -> failwith "must be a set"
    in
    let lo_typed = cast_expression env ctx elt_typ lo in
    let hi_typed = cast_expression env ctx elt_typ hi in
    MkExpression (exp_info, ExpRange (lo_typed, hi_typed), typ, Directionless)

and translate_direction (dir: Types.Direction.t option) : Typed.direction =
  match dir with
  | Some (_, In) -> In
  | Some (_, Out) -> Out
  | Some (_, InOut) -> InOut
  | None -> Directionless

and eval_to_positive_int env info expr =
  let value =
    expr
    |> type_expression env ExprCxConstant
    |> compile_time_eval_bigint env
    |> Bigint.to_int_exn
  in
  if value > 0
  then value
  else raise_s [%message "expected positive integer" ~info:(info: Info.t)]

and gen_wildcard env: P4string.t =
  let str = Renamer.freshen_name (Checker_env.renamer env) "__wild" in
  {tags = Info.dummy; str}

and translate_type' ?(gen_wildcards=false) (env: Checker_env.t) (typ: Types.Type.t) : coq_P4Type * P4string.t list =
  let open Types.Type in
  let ret (t: coq_P4Type) = t, [] in
  match snd typ with
  | Bool -> ret TypBool
  | Error -> ret TypError
  | Integer -> ret TypInteger
  | String -> ret TypString
  | IntType e -> ret @@ TypInt (eval_to_positive_int env (fst typ) e)
  | BitType e -> ret @@ TypBit (eval_to_positive_int env (fst typ) e)
  | VarBit e -> ret @@ TypVarBit (eval_to_positive_int env (fst typ) e)
  | TypeName ps -> ret @@ TypTypeName ps
  | SpecializedType {base; args} ->
    let args, wildcards =
      args
      |> List.map ~f:(translate_type' ~gen_wildcards env)
      |> List.unzip
    in
    TypSpecializedType (translate_type env base, args),
    List.concat wildcards
  | HeaderStack {header=ht; size=e} ->
    let hdt = translate_type env ht in
    let len =
      e
      |> type_expression env ExprCxConstant
      |> compile_time_eval_bigint env
      |> Bigint.to_int_exn in
    ret @@ TypArray (hdt, len)
  | Tuple tlist ->
    ret @@ TypTuple (List.map ~f:(translate_type env) tlist)
  | Void -> ret TypVoid
  | DontCare ->
    let name = gen_wildcard env in
    TypTypeName (BareName name), [name]

and translate_type (env: Checker_env.t) (typ: Types.Type.t) : coq_P4Type =
  fst (translate_type' env typ)

and translate_type_opt (env: Checker_env.t) (typ: Types.Type.t) : coq_P4Type option =
  match snd typ with
  | DontCare -> None
  | _ -> Some (translate_type env typ)

and hash_default_arg env (arg: Types.Expression.t option): int option =
  match arg with
  | Some exp -> Some (Checker_env.add_default_arg exp env)
  | None -> None

(* Translates Types.Parameters to Typed.Parameters *)
and translate_parameters env params =
  let translate_parameter (info, param : Types.Parameter.t) =
    let default_arg_id = hash_default_arg env param.opt_value in
    MkParameter (is_optional (info, param),
                 translate_direction param.direction,
                 translate_type env param.typ,
                 default_arg_id,
                 param.variable)
  in
  List.map ~f:translate_parameter params

and expr_of_arg (arg: Argument.t): Expression.t option =
  match snd arg with
  | Missing -> None
  | KeyValue { value; _ }
  | Expression { value } -> Some value

(* Returns true if type typ is a well-formed type *)
and is_well_formed_type env (typ: coq_P4Type) : bool =
  match saturate_type env typ with
  (* Base types *)
  | TypBool
  | TypString
  | TypInteger
  | TypInt _
  | TypBit _
  | TypVarBit _
  | TypError
  | TypMatchKind
  | TypVoid -> true
  (* Recursive types *)
  | TypArray (typ, _) as arr_typ ->
    is_well_formed_type env typ &&
    is_valid_nested_type env arr_typ typ
  | TypTuple types
  | TypList types ->
    List.for_all ~f:(is_well_formed_type env) types &&
    List.for_all ~f:(is_valid_nested_type env typ) types
  | TypSet typ ->
    is_well_formed_type env typ
  | TypEnum (_, typ, _) ->
    begin match typ with
      | None -> true
      | Some typ -> is_well_formed_type env typ
    end
  | TypRecord fields
  | TypHeaderUnion fields
  | TypStruct fields ->
    let field_ok (MkFieldType (_, field_typ): coq_FieldType) =
      is_well_formed_type env field_typ &&
      is_valid_nested_type env typ field_typ
    in
    List.for_all ~f:field_ok fields
  | TypHeader fields ->
    let field_ok (MkFieldType (_, field_typ): coq_FieldType) =
      is_well_formed_type env field_typ &&
      is_valid_nested_type ~in_header:true env typ field_typ
    in
    List.for_all ~f:field_ok fields
  | TypAction (data_params, ctrl_params) ->
    are_param_types_well_formed env data_params &&
    are_construct_params_types_well_formed env ctrl_params
  (* Type names *)
  | TypTypeName name ->
    Checker_env.resolve_type_name_opt name env <> None
  | TypTable result_typ_name ->
    Checker_env.resolve_type_name_opt (BareName result_typ_name) env <> None
  | TypNewType (name, typ) ->
    is_well_formed_type env typ
  (* Polymorphic types *)
  | TypFunction (MkFunctionType (tps, ps, _, rt)) ->
    let env = Checker_env.insert_type_vars tps env in
    are_param_types_well_formed env ps && is_well_formed_type env rt
  | TypConstructor (tps, ws, ps, rt) ->
    let env = Checker_env.insert_type_vars tps env in
    are_construct_params_types_well_formed env ps && is_well_formed_type env rt
  | TypExtern name ->
    begin match Checker_env.find_extern_opt (BareName name) env with
    | Some {type_params = []; _} -> true
    | _ -> false
    end
  | TypParser ctrl
  | TypControl ctrl ->
    let MkControlType (tps, ps) = ctrl in
    let env = Checker_env.insert_type_vars tps env in
    are_param_types_well_formed env ps
  | TypPackage (tps, _, cps) ->
    let env = Checker_env.insert_type_vars tps env in
    are_construct_params_types_well_formed env cps
  (* Type Application *)
  | TypSpecializedType (base_typ, typ_args) ->
    let base_typ = saturate_type env base_typ in
    begin match base_typ with
    | TypExtern name ->
      let ext = Checker_env.find_extern (BareName name) env in
      List.for_all ~f:(is_well_formed_type env) typ_args
      && List.length ext.type_params = List.length typ_args
    | typ ->
      let type_params = get_type_params typ in
      is_well_formed_type env base_typ
      && List.for_all ~f:(is_well_formed_type env) typ_args
      && List.length type_params = List.length typ_args
    end

and are_param_types_well_formed env (params:coq_P4Parameter list) : bool =
  let check (MkParameter (_, _, typ, _, _)) = is_well_formed_type env typ in
  List.for_all ~f:check params

and are_construct_params_types_well_formed env (construct_params: coq_P4Parameter list) : bool =
  let check (MkParameter (_, dir, typ, _, _)) =
    eq_dir dir Directionless &&
    is_well_formed_type env typ
  in
  List.for_all ~f:check construct_params

and ctx_of_kind (k: coq_FunctionKind) : Typed.coq_ParamContext =
  match k with
  | FunParser -> ParamCxRuntime ParamCxDeclParser
  | FunControl -> ParamCxRuntime ParamCxDeclControl
  | FunExtern -> ParamCxRuntime ParamCxDeclMethod
  | FunTable -> ParamCxRuntime ParamCxDeclControl
  | FunAction -> ParamCxRuntime ParamCxDeclAction
  | FunFunction -> ParamCxRuntime ParamCxDeclFunction
  | FunBuiltin -> ParamCxRuntime ParamCxDeclMethod

and is_valid_param_type env (ctx: Typed.coq_ParamContext) (typ: coq_P4Type) =
  let typ = reduce_to_underlying_type env typ in
  match ctx with
  | ParamCxConstructor decl ->
    begin match typ, decl with
      | TypPackage _, ParamCxDeclPackage -> true
      | TypPackage _, _ -> false
      | TypParser _, ParamCxDeclPackage
      | TypParser _, ParamCxDeclParser -> true
      | TypParser _, _ -> false
      | TypControl _, ParamCxDeclPackage
      | TypControl _, ParamCxDeclControl -> true
      | TypControl _, _ -> false
      | TypExtern _, ParamCxDeclPackage
      | TypExtern _, ParamCxDeclParser
      | TypExtern _, ParamCxDeclControl
      | TypExtern _, ParamCxDeclMethod -> true
      | TypExtern _, _ -> false
      | TypFunction _, _ -> false
      | TypAction _, _ -> false
      | TypTable _, _ -> false
      | TypSet _, _ -> false
      | _ -> true
    end
  | ParamCxRuntime decl ->
    begin match typ, decl with
      | TypPackage _, _ -> false
      | TypParser _, _ -> false
      | TypControl _, _ -> false
      | TypExtern _, ParamCxDeclParser
      | TypExtern _, ParamCxDeclControl
      | TypExtern _, ParamCxDeclMethod -> true
      | TypExtern _, _ -> false
      | TypTable _, _ -> false
      | TypSet _, _ -> false
      | TypAction _, _ -> false
      | TypFunction _, _ -> false
      | _ -> true
    end

and is_valid_param_type_kind env (kind: coq_FunctionKind) (typ: coq_P4Type) =
  match kind with
  | FunParser -> is_valid_param_type env (ParamCxRuntime ParamCxDeclParser) typ
  | FunControl -> is_valid_param_type env (ParamCxRuntime ParamCxDeclControl) typ
  | FunExtern -> is_valid_param_type env (ParamCxRuntime ParamCxDeclMethod) typ
  | FunTable -> false
  | FunAction -> is_valid_param_type env (ParamCxRuntime ParamCxDeclAction) typ
  | FunFunction -> is_valid_param_type env (ParamCxRuntime ParamCxDeclFunction) typ
  | FunBuiltin -> is_valid_param_type env (ParamCxRuntime ParamCxDeclMethod) typ

and is_valid_nested_type ?(in_header=false) (env: Checker_env.t) (outer_type: coq_P4Type) (inner_type: coq_P4Type) =
  let inner_type = reduce_to_underlying_type env inner_type in
  let field_ok (MkFieldType (_, typ)) =
    is_valid_nested_type ~in_header env inner_type typ
  in
  match reduce_to_underlying_type env outer_type with
  | TypHeader _ ->
    begin match inner_type with
      | TypBit _
      | TypInt _
      | TypVarBit _
      | TypBool
      | TypEnum (_, Some _, _) ->
        true
      | TypStruct fields ->
        List.for_all ~f:field_ok fields
      | _ ->
        false
    end
  | TypHeaderUnion _ ->
    begin match inner_type with
      | TypHeader _ -> true
      | _ -> false
    end
  | TypStruct _
  | TypList _
  | TypTuple _ ->
    begin match inner_type with
      | TypTypeName _
      | TypBit _
      | TypInt _
      | TypEnum _
      | TypBool -> true
      | TypStruct fields ->
        not in_header ||
        List.for_all ~f:field_ok fields
      | TypHeader _
      | TypVarBit _
      | TypError
      | TypArray _
      | TypHeaderUnion _
      | TypTuple _ ->
        not in_header
      | _ ->
        false
    end
  | TypArray _ ->
    begin match inner_type with
      | TypHeader _ -> true
      | TypHeaderUnion _ -> true
      | _ -> false
    end
  | _ -> false

and is_compile_time_only_type env typ =
  match reduce_to_underlying_type env typ with
  | TypInteger
  | TypString -> true
  | _ -> false


and validate_param env ctx (typ: coq_P4Type) dir info opt_value =
  if is_extern env typ && not @@ eq_dir dir Directionless
  then failwith "Externs as parameters must be directionless.";
  if is_compile_time_only_type env typ && not @@ eq_dir dir Directionless
  then failwith "Parameters of this type must be directionless.";
  if not @@ is_well_formed_type env typ
  then raise_s [%message "Parameter type is not well-formed." ~typ:(typ:coq_P4Type)];
  if not @@ is_valid_param_type env ctx typ
  then failwith "Type cannot be passed as a parameter.";
  if opt_value <> None && not (eq_dir dir Directionless) && not (eq_dir dir In)
  then raise_s [%message "Only directionless and in parameters may have default arguments" ~info:(info:Info.t)]

and type_param' ?(gen_wildcards=false) env (ctx: Typed.coq_ParamContext) (param_info, param : Types.Parameter.t) : coq_P4Parameter * P4string.t list =
  let typ, wildcards = translate_type' ~gen_wildcards env param.typ in
  let env = Checker_env.insert_type_vars wildcards env in
  let dir = translate_direction param.direction in
  let opt_arg_id = hash_default_arg env param.opt_value in
  validate_param env ctx typ dir param_info opt_arg_id;
  MkParameter (is_optional (param_info, param),
               translate_direction param.direction,
               typ,
               opt_arg_id,
               param.variable),
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

and type_constructor_param env decl_kind (param: Types.Parameter.t) : coq_P4Parameter =
  if (snd param).direction <> None
  then raise_s [%message "Constructor parameters must be directionless"
        ~param:(param: Types.Parameter.t)];
  type_param env (ParamCxConstructor decl_kind) param

and type_constructor_params env ctx params =
  List.map ~f:(type_constructor_param env ctx) params

and type_int (int: P4int.t) : Prog.coq_ExpressionPreT * coq_P4Type * direction =
  let typ = 
    match int.width_signed with
    | None -> TypInteger
    | Some (width, true) -> TypInt width
    | Some (width, false) -> TypBit width
  in
  ExpInt int, typ, Directionless

(* Section 8.15
 * ------------
 *
 * Δ, T, Γ |- a : t[size]      Δ, T, Γ |- i : u, where numeric(u)
 * ----------------------------------------------------------
 *                Δ, T, Γ |- a[i] : t
 *
 * Some architectures may further require ctk(i).
*)
and type_array_access env ctx (array: Types.Expression.t) index
  : Prog.coq_ExpressionPreT * coq_P4Type * direction =
  let (MkExpression (_, _, array_typ, array_dir) as array_typed) =
    type_expression env ctx array
  in
  let (MkExpression (_, _, idx_typ, _) as idx_typed) =
    type_expression env ctx index
  in
  let element_typ = assert_array (info array) array_typ |> fst in
  assert_numeric (info index) idx_typ |> ignore;
  ExpArrayAccess (array_typed, idx_typed),
  element_typ,
  array_dir

and is_numeric (typ: coq_P4Type) : bool =
  match typ with
  | TypInt _
  | TypBit _
  | TypVarBit _
  | TypInteger -> true
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
and type_bit_string_access env ctx bits lo hi
  : Prog.coq_ExpressionPreT * coq_P4Type * direction =
  let (MkExpression (_, _, bits_typ, bits_dir) as bits_typed) = type_expression env ctx bits in
  match reduce_type env bits_typ with
  | TypInt width
  | TypBit width ->
    let (MkExpression (_, _, lo_typ, _) as lo_typed) =
      type_expression env ExprCxConstant lo
    in
    let typ_lo = saturate_type env lo_typ in
    let (MkExpression (_, _, hi_typ, _) as hi_typed) =
      type_expression env ExprCxConstant hi
    in
    let typ_hi = saturate_type env hi_typ in
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
    ExpBitStringAccess (bits_typed, val_lo, val_hi),
    TypBit diff,
    bits_dir
  | typ ->
    failwith "Cannot bitslice this type."

(* Section 8.11
 * ------------
 *
 *      1 <= i <= n; Δ, T, Γ |- xi : ti
 * ------------------------------------------
 * Δ, T, Γ |- { x1, ..., xn } : (t1, ..., tn)
 *
 *)
and type_list env ctx values : Prog.coq_ExpressionPreT * coq_P4Type * direction =
  let typed_exprs = List.map ~f:(type_expression env ctx) values in
  let types = List.map ~f:type_of_expr typed_exprs in
  ExpList typed_exprs, TypList types, Directionless

and type_key_val env ctx ((info, entry): Types.KeyValue.t) : Prog.coq_KeyValue =
  MkKeyValue (info, entry.key, type_expression env ctx entry.value)

and type_record env ctx entries =
  let entries_typed = List.map ~f:(type_key_val env ctx) entries in
  let rec_typed : Prog.coq_ExpressionPreT =
    ExpRecord entries_typed
  in
  let kv_to_field (kv: Prog.coq_KeyValue) =
    let MkKeyValue (tags, key, value) = kv in
    MkFieldType (key, type_of_expr value)
  in
  let fields = List.map ~f:kv_to_field entries_typed in
  rec_typed, TypRecord fields, Directionless

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
and type_unary_op env ctx (op: Op.uni) arg : Prog.coq_ExpressionPreT * coq_P4Type * direction =
  let arg_typed = type_expression env ctx arg in
  let MkExpression (_, _, arg_typ, arg_dir) = arg_typed in
  begin match snd op with
    | Not    -> assert_bool (info arg) arg_typ |> ignore
    | BitNot -> assert_bit (info arg) arg_typ |> ignore
    | UMinus -> assert_numeric (info arg) arg_typ |> ignore
  end;
  ExpUnaryOp (uop_to_coq_uop (snd op), arg_typed), arg_typ, arg_dir

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
and implicit_cast env l r : coq_P4Type option * coq_P4Type option =
  match saturate_type env (type_of_expr l), saturate_type env (type_of_expr r) with
  | TypBit width, TypInteger ->
    None, Some (TypBit width)
  | TypInteger, TypBit width ->
    Some (TypBit width), None
  | TypInt width, TypInteger ->
    None, Some (TypInt width)
  | TypInteger, TypInt width ->
    Some (TypInt width), None
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
  let cast typ (expr : Prog.coq_Expression) : Prog.coq_Expression =
    let MkExpression (expr_info, pre_expr, etyp, dir) = expr in 
    MkExpression (expr_info, ExpCast (typ, expr), typ, dir)
  in
  let cast_opt = function
    | Some typ -> cast typ
    | None -> fun e -> e
  in
  let cast_type_l, cast_type_r = implicit_cast env l_typed r_typed in
  if op <> Op.Shl && op <> Op.Shr
  then cast_opt cast_type_l l_typed, cast_opt cast_type_r r_typed
  else l_typed, r_typed

(* TODO: Checking if two values of this type be compared for equality
 * (==) or inequality (!=).
*)
and type_has_equality_tests env (typ: coq_P4Type) =
  match reduce_type env typ with
  | TypBool
  | TypString
  | TypInteger
  | TypInt _
  | TypBit _
  | TypVarBit _
  | TypError
  | TypMatchKind ->
    true
  | TypArray (typ, _)
  | TypSet typ ->
    type_has_equality_tests env typ
  | TypTuple types
  | TypList types ->
    List.for_all ~f:(type_has_equality_tests env) types
  | TypHeader fields
  | TypHeaderUnion fields
  | TypStruct fields
  | TypRecord fields ->
    List.for_all fields
      ~f:(fun (MkFieldType (_, field_typ)) ->
          type_has_equality_tests env field_typ)
  | TypNewType (_, typ) ->
    type_has_equality_tests env typ
  | TypEnum (_, typ, _) ->
    begin match typ with
      | Some typ -> type_has_equality_tests env typ
      | None -> true
    end
  | TypTypeName name ->
    failwith "type name in saturated type?"
  | _ ->
    false

and is_nonnegative_numeric env (e: Prog.coq_Expression) : bool =
  match type_of_expr e with
  | TypInteger ->
    let e_value = compile_time_eval_bigint env e in
    Bigint.(e_value >= zero)
  | TypBit _ -> true
  | _ -> false

and is_positive_numeric env (e: Prog.coq_Expression) : bool =
  match type_of_expr e with
  | TypInteger ->
    let e_value = compile_time_eval_bigint env e in
    Bigint.(e_value > zero)
  | TypBit _ ->
    begin match compile_time_eval_expr env e with
      | None ->
        true (* XXX: bit<> values can be zero... *)
      | Some value ->
        match bigint_of_value value with
        | Some e_value -> Bigint.(e_value > zero)
        | None ->
          failwith "bit<> evaluated to non numerical value?"
    end
  | _ -> false

and check_div_args env left_arg right_arg =
  if is_nonnegative_numeric env left_arg && is_positive_numeric env right_arg
  then ()
  else failwith "Arguments to division must be positive."

and type_binary_op env ctx exp_info (op_info, op) (l, r) =
  let typed_l, typed_r = coerce_binary_op_args env ctx op l r in
  check_binary_op env exp_info (op_info, op) typed_l typed_r

and check_binary_op env info (op_info, op) typed_l typed_r: Prog.coq_ExpressionPreT * Typed.coq_P4Type * Typed.direction =
  let open Op in
  let l_typ = saturate_type env (type_of_expr typed_l) in
  let r_typ = saturate_type env (type_of_expr typed_r) in
  let dir =
    match dir_of_expr typed_l, dir_of_expr typed_r with
    | In, In -> In
    | _ -> Directionless
  in
  let typ =
    match op with
    | And | Or ->
      begin match l_typ, r_typ with
        | TypBool, TypBool -> TypBool
        | TypBool, r -> raise_mismatch (op_info) "Operand must be a bool" r
        | l, r -> raise_mismatch (op_info) "Operand must be a bool" l
      end
    (* Basic numeric operations are defined on both arbitrary and fixed-width integers *)
    | Plus | Minus | Mul ->
      begin match l_typ, r_typ with
        | TypInteger, TypInteger -> TypInteger
        | TypBit l, TypBit r when l = r -> TypBit l
        | TypInt l, TypInt r when l = r -> TypInt l
        | _, _ -> failwith "Binop unsupported."
      end
    | Eq | NotEq ->
      if type_equality env [] l_typ r_typ
      then if type_has_equality_tests env l_typ
        then TypBool
        else failwith "bad error message: type doesn't have equality tests (== and !=)"
      else raise_type_error op_info (Type_Difference (l_typ, r_typ))
    (* Saturating operators are only defined on finite-width signed or unsigned integers *)
    | PlusSat | MinusSat ->
      begin match l_typ, r_typ with
        | TypBit l, TypBit r when l = r ->
          TypBit l
        | TypInt l, TypInt r when l = r ->
          TypInt l
        | TypBit _, r | TypInt _, r ->
          raise_mismatch (op_info) "Operand must have type int<w> or bit<w>" r
        | l, r ->
          raise_mismatch (op_info) "Operand must have type int<w> or bit<w>" l
      end
    (* Bitwise operators are only defined on bitstrings of the same width *)
    | BitAnd | BitXor | BitOr ->
      begin match l_typ, r_typ with
        | TypBit l, TypBit r when l = r -> TypBit l
        | TypBit _, _ -> raise_mismatch (info_of_expr typed_r) "unsigned int" r_typ
        | _, _ -> raise_mismatch (info_of_expr typed_l) "unsigned int" l_typ
      end
    (* Bitstring concatentation is defined on any two bitstrings *)
    | PlusPlus ->
      begin match l_typ, r_typ with
        | TypBit l, TypBit r
        | TypInt l, TypBit r
        | TypBit l, TypInt r
        | TypInt l, TypInt r -> TypBit (l + r)
        | TypInt _, _
        | TypBit _, _ ->
          raise_mismatch (info_of_expr typed_r) "bit<> or int<>" r_typ
        | _, _ ->
          raise_mismatch (info_of_expr typed_l) "bit<> or int<>" l_typ
      end
    (* Comparison is defined on both arbitrary and fixed-width integers *)
    | Le | Ge | Lt | Gt ->
      begin match l_typ, r_typ with
        | TypInteger, TypInteger -> TypBool
        | TypBit l, TypBit r
        | TypInt l, TypInt r when l = r -> TypBool
        | _, _ -> raise_type_error op_info (Type_Difference (l_typ, r_typ))
      end
    (* Division is only defined on compile-time known arbitrary-precision positive integers *)
    | Div | Mod ->
      begin match l_typ, r_typ with
        | TypInteger, TypInteger ->
          check_div_args env typed_l typed_r;
          TypInteger
        | TypBit l_width, TypBit r_width when l_width = r_width ->
          check_div_args env typed_l typed_r;
          TypBit l_width
        | TypInteger, _ ->
          raise_mismatch (info_of_expr typed_r) "arbitrary precision integer" r_typ
        | _, _ ->
          raise_mismatch (info_of_expr typed_l) "arbitrary precision integer" l_typ
      end
    | Shl | Shr ->
      begin match l_typ, is_nonnegative_numeric env typed_r with
        | TypBit _, true
        | TypInt _, true -> l_typ
        | _, true -> failwith "Bad left hand argument to shift."
        | _ -> failwith "Bad right hand argument to shift."
      end
  in
  ExpBinaryOp (binop_to_coq_binop op, (typed_l, typed_r)), typ, dir

(* See section 8.9.2 "Explicit casts" *)
and cast_ok ?(explicit = false) env original_type new_type =
  let original_type = saturate_type env original_type in
  let new_type = saturate_type env new_type in
  match original_type, new_type with
  | TypSet t1, TypSet t2 ->
    type_equality env [] t1 t2
  | t1, TypSet t2 ->
    not explicit &&
    type_equality env [] t1 t2
  | TypBit 1, TypBool
  | TypBool, TypBit 1
  | TypInt _, TypBit _
  | TypBit _, TypInt _ ->
    explicit
  | TypBit width1, TypBit width2
  | TypInt width1, TypInt width2 ->
    width1 = width2 || explicit
  | TypInteger, TypBit _
  | TypInteger, TypInt _ ->
    true
  | TypEnum (name, Some t, members), TypEnum (_, Some t', _)
  | TypEnum (name, Some t, members), t'
  | t', TypEnum (name, Some t, members) ->
    type_equality env [] t t'
  | TypNewType (name1, typ1),
    TypNewType (name2, typ2) ->
    type_equality env [] typ1 new_type
    || type_equality env [] original_type typ2
  | TypNewType (name, typ), t ->
    cast_ok ~explicit env typ t
  | t, TypNewType (name, typ) ->
    cast_ok ~explicit env t typ
  | TypList types1, TypTuple types2 ->
    type_equality env [] (TypTuple types1) (TypTuple types2)
  | TypList types1, TypHeader rec2
  | TypList types1, TypStruct rec2 ->
    let types2 = List.map ~f:(fun (MkFieldType (_, typ)) -> typ) rec2 in
    not explicit && type_equality env [] (TypList types2) original_type
  | TypRecord rec1, TypHeader rec2
  | TypRecord rec1, TypStruct rec2 ->
    type_equality env [] (TypRecord rec1) (TypRecord rec2)
  | _ -> not explicit && type_equality env [] original_type new_type

(* Section 8.9 *)
and type_cast env ctx typ expr : Prog.coq_ExpressionPreT * coq_P4Type * direction =
  let expr_typed = type_expression env ctx expr in
  let expr_type = saturate_type env (type_of_expr expr_typed) in
  let new_type = translate_type env typ in
  let new_type_sat = saturate_type env new_type in
  if not @@ is_well_formed_type env new_type
  then failwith "Ill-formed type.";
  if cast_ok ~explicit:true env expr_type new_type_sat
  then ExpCast (new_type, expr_typed), new_type, Directionless
  else failwith "Illegal explicit cast."

(* ? *)
and type_type_member env ctx typ name : Prog.coq_ExpressionPreT * coq_P4Type * direction =
  let real_name = real_name_for_type_member env typ name in
  let full_type, dir = Checker_env.find_type_of real_name env in
  ExpTypeMember (typ, name), full_type, dir

and type_error_member env ctx (name: P4string.t) : Prog.coq_ExpressionPreT * coq_P4Type * direction =
  let packed_name: P4string.t = {name with str = "error." ^ name.str} in
  let (e, _) = Checker_env.find_type_of (BareName packed_name) env in
  if e <> TypError then failwith "Error member not an error?";
  ExpErrorMember name, TypError, Directionless

and header_methods typ =
  let fake_fields: coq_FieldType list =
    [MkFieldType ({tags=Info.dummy; str="isValid"},
                  TypFunction (MkFunctionType ([], [], FunBuiltin, TypBool)))]
  in
  match typ with
  | TypHeader fields -> fake_fields
  | _ -> []

and type_expression_member_builtin env (ctx: Typed.coq_ExprContext) info typ (name: P4string.t) : coq_P4Type =
  let fail () =
    raise_unfound_member info name.str in
  match typ with
  | TypArray (typ, _) ->
    let idx_typ = TypBit 32 in
    begin match name.str with
      | "size"
      | "lastIndex" ->
        idx_typ
      | "next"
      | "last" ->
        begin match ctx with
          | ExprCxParserState ->
            typ
          | _ -> failwith "can only use .last or .next within a parser"
        end
      | _ -> fail ()
    end
  | _ -> fail ()

and type_expression_member_function_builtin env info typ (name: P4string.t) : coq_P4Type option =
  match typ with
  | TypControl (MkControlType ([], ps)) ->
    begin match name.str with
      | "apply" ->
        Some (TypFunction (MkFunctionType ([], ps, FunControl, TypVoid)))
      | _ -> None
    end
  | TypParser (MkControlType ([], ps)) ->
    begin match name.str with
      | "apply" ->
        Some (TypFunction (MkFunctionType ([], ps, FunParser, TypVoid)))
      | _ -> None
    end
  | TypTable result_typ_name ->
    begin match name.str with
      | "apply" ->
        let ret = TypTypeName (BareName result_typ_name) in
        Some (TypFunction (MkFunctionType ([], [], FunTable, ret)))
      | _ -> None
    end
  | TypStruct _ ->
    begin match name.str with
      | "minSizeInBits" ->
        Some (TypFunction (MkFunctionType ([], [], FunBuiltin, TypInteger)))
      | "minSizeInBytes" ->
        Some (TypFunction (MkFunctionType ([], [], FunBuiltin, TypInteger)))
      | _ -> None
    end
  | TypHeader _ ->
    begin match name.str with
      | "isValid" ->
        Some (TypFunction (MkFunctionType ([], [], FunBuiltin, TypBool)))
      | "setValid"
      | "setInvalid" ->
        Some (TypFunction (MkFunctionType ([], [], FunBuiltin, TypVoid)))
      | "minSizeInBits" ->
        Some (TypFunction (MkFunctionType ([], [], FunBuiltin, TypInteger)))
      | "minSizeInBytes" ->
        Some (TypFunction (MkFunctionType ([], [], FunBuiltin, TypInteger)))
      | _ -> None
    end
  | TypArray (typ, _) ->
    begin match name.str with
      | "minSizeInBits" ->
        Some (TypFunction (MkFunctionType ([], [], FunBuiltin, TypInteger)))
      | "minSizeInBytes" ->
        Some (TypFunction (MkFunctionType ([], [], FunBuiltin, TypInteger)))
      | "push_front"
      | "pop_front" ->
        let parameters: coq_P4Parameter list =
          [MkParameter (false, Directionless, TypInteger, None, {tags=Info.dummy; str="count"})]
        in
        Some (TypFunction (MkFunctionType ([], parameters, FunBuiltin, TypVoid)))
      | _ -> None
    end
  | TypHeaderUnion _ ->
    begin match name.str with
      | "isValid" ->
        Some (TypFunction (MkFunctionType ([], [], FunBuiltin, TypBool)))
      | "minSizeInBits" ->
        Some (TypFunction (MkFunctionType ([], [], FunBuiltin, TypInteger)))
      | "minSizeInBytes" ->
        Some (TypFunction (MkFunctionType ([], [], FunBuiltin, TypInteger)))
      | _ -> None
    end
  | _ -> None

(* Sections 6.6, 8.14 *)
and type_expression_member env ctx expr name =
  let typed_expr = type_expression env ctx expr in
  let expr_typ = reduce_type env (type_of_expr typed_expr) in
  let methods = header_methods (type_of_expr typed_expr) in
  let rec find_type expr_typ =
    match expr_typ with
    | TypHeader fields
    | TypHeaderUnion fields
    | TypStruct fields ->
      let fs = fields @ methods in
      let matches (MkFieldType (field_name, _) : coq_FieldType) =
        P4string.eq field_name name
      in
      begin match List.find ~f:matches fs with
        | Some (MkFieldType (_, field_typ)) -> field_typ
        | None -> type_expression_member_builtin env ctx (info expr) expr_typ name
      end
    | TypSpecializedType (TypExtern extern_name, args) ->
       begin match Checker_env.find_extern_opt (BareName extern_name) env with
       | Some {type_params; methods} ->
          let extended_env = Checker_env.insert_types (List.zip_exn type_params args) env in
          let matches (m: Prog.coq_ExternMethod) =
            P4string.eq m.name name
          in
          begin match List.find ~f:matches methods with
          | Some m -> reduce_type extended_env (TypFunction m.typ)
          | None -> type_expression_member_builtin env ctx (info expr) expr_typ name
          end
       | None -> failwith "methods not found for extern"
       end
    | TypExtern extern_name ->
       find_type (TypSpecializedType (TypExtern extern_name, []))
    | _ -> type_expression_member_builtin env ctx (info expr) expr_typ name
  in
  let expr_typed: Prog.coq_ExpressionPreT = ExpExpressionMember (typed_expr, name) in
  expr_typed, find_type expr_typ, Directionless

(* Section 8.4.1
 * -------------
 *
 * Δ, T, Γ |- cond : bool    Δ, T, Γ |- tru : t    Δ, T, Γ |- fls : t;
 * -------------------------------------------------------------------
 *              Δ, T, Γ |- cond ? tru : fls : t
*)
and type_ternary env ctx cond tru fls: Prog.coq_ExpressionPreT * _ * _ =
  let cond_typed = type_expression env ctx cond in
  assert_bool (info cond) (type_of_expr cond_typed) |> ignore;
  let fls_typed = type_expression env ctx fls in
  let tru_typed = type_expression env ctx tru in
  assert_same_type env (info tru) (info fls) (type_of_expr tru_typed) (type_of_expr fls_typed) |> ignore;
  match type_of_expr tru_typed with
  | TypInteger ->
    (* TODO this is allowed if cond is compile-time known *)
    failwith "Conditional expressions may not have arbitrary width integer type"
  | t ->
    ExpTernary (cond_typed, tru_typed, fls_typed), t, Directionless

and match_params_to_args env call_site_info params args : (coq_P4Parameter * Expression.t option) list =
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
    match_positional_args_to_params env call_site_info params args
  | Some `Positional ->
    match_positional_args_to_params env call_site_info params args
  | Some `Named ->
    match_named_args_to_params env call_site_info params args

and match_positional_args_to_params env call_site_info params args =
  let conv param arg =
    let open Types.Argument in
    match arg with
    | Expression { value } -> param, Some value
    | Missing -> param, None
    | _ -> failwith "expected positional argument"
  in
  let rec go (params: coq_P4Parameter list) (args: Types.Argument.pre_t list) =
    match params, args with
    | param :: params, arg :: args ->
      conv param arg :: go params args
    | param :: params, [] ->
      begin match find_default_arg env param with
        | Some expr -> conv param (Expression {value = expr}) :: go params args
        | None ->
          if opt_of_param param
          then conv param Missing :: go params args
          else raise_s [%message "missing argument for parameter"
                ~info:(call_site_info: Info.t)
                ~param:(param: coq_P4Parameter)]
      end
    | [], arg :: args ->
      raise_s [%message "too many arguments"
          ~info:(call_site_info: Info.t)]
    | [], [] -> []
  in
  go params args

and match_named_args_to_params env call_site_info (params: coq_P4Parameter list) (args: Types.Argument.pre_t list) =
  match params with
  | p :: params ->
    let right_arg : Argument.pre_t -> _ = function
      | KeyValue {key; value} ->
        if P4string.eq (var_of_param p) key
        then Some value
        else None
      | _ -> None
    in
    let maybe_arg_for_p, other_args =
      Util.find_map_and_drop ~f:right_arg args
    in
    begin match maybe_arg_for_p, find_default_arg env p with
      | Some arg_for_p, _
      | None, Some arg_for_p ->
        (p, Some arg_for_p) :: match_named_args_to_params env call_site_info params other_args
      | None, None ->
        if opt_of_param p
        then (p, None) :: match_named_args_to_params env call_site_info params other_args
        else raise_s [%message "parameter has no matching argument"
              ~call_site:(call_site_info: Info.t)
              ~param:(p: coq_P4Parameter)]
    end
  | [] ->
    match args with
    | [] -> []
    | a :: rest ->
      raise_s [%message "too many arguments supplied at call site"
          ~info:(call_site_info: Info.t)
          ~unused_args:(args : Types.Argument.pre_t list)]

and is_lvalue env (expr_typed: Prog.coq_Expression) =
  let MkExpression (_, expr, expr_typ, expr_dir) = expr_typed in
  match expr with
  | ExpName name ->
    let typ = reduce_type env expr_typ in
    let const = Checker_env.find_const_opt name env in
    begin match expr_dir, typ with
      | In, _
      | Directionless, _ -> false
      | _, TypExtern _ -> false
      | _, TypInteger -> false
      | _, TypString -> false
      | _ ->
        begin match const with
          | Some constant -> false
          | _ -> true
        end
    end
  | ExpExpressionMember (lvalue, _)
  | ExpArrayAccess (lvalue, _)
  | ExpBitStringAccess (lvalue, _, _) ->
    is_lvalue env lvalue
  | _ -> false

and check_direction env dir (arg_typed: Prog.coq_Expression) =
  let MkExpression (_, _, arg_type, arg_dir) = arg_typed in
  match dir with
  | Directionless -> ()
  | In ->
    begin match arg_type with
      | TypExtern _ ->
        raise_s [%message "externs should always be directionless"]
      | _ -> ()
    end
  | Out
  | InOut ->
    if not @@ is_lvalue env arg_typed
    then failwith "Expected l-value.";
    if eq_dir arg_dir In
    then failwith "In parameter passed as out parameter."

(* Section 8.17: Typing Function Calls *)
and cast_param_arg env ctx call_info (param, expr: coq_P4Parameter * Expression.t option) =
  let MkParameter (param_opt, param_dir, param_typ, param_opt_value, param_var) = param in
  match expr with
  | Some expr ->
    let typed_arg = cast_expression env ctx param_typ expr in
    check_direction env param_dir typed_arg;
    param, Some typed_arg
  | None ->
    if param_dir <> Out && not param_opt
    then failwith "Don't care argument (underscore) provided for non-out parameter."
    else if param_typ = TypVoid
    then failwith "could not infer valid type for don't care argument"
    else param, None

and call_ok (ctx: coq_ExprContext) (fn_kind: coq_FunctionKind) : bool =
  begin match ctx, fn_kind with
    | ExprCxParserState, FunParser -> true
    | _, FunParser -> false
    | ExprCxApplyBlock, FunControl -> true
    | _, FunControl -> false
    | ExprCxFunction, FunExtern -> false
    | _, FunExtern -> true
    | ExprCxApplyBlock, FunTable -> true
    | _, FunTable -> false
    | ExprCxApplyBlock, FunAction -> true
    | ExprCxAction, FunAction -> true
    | ExprCxTableAction, FunAction -> true
    | _, FunAction -> false
    | ExprCxParserState, FunFunction -> true
    | ExprCxApplyBlock, FunFunction -> true
    | ExprCxAction, FunFunction -> true
    | ExprCxFunction, FunFunction -> true
    | ExprCxDeclLocals, FunFunction -> true
    | _, FunFunction -> false
    | _, FunBuiltin -> true
  end

and type_function_call env ctx call_info func type_args args =
  let func_typed = resolve_function_overload env ctx func args in
  let func_type = type_of_expr func_typed in
  let type_params, params, kind, return_type =
    match func_type with
    | TypFunction (MkFunctionType (type_params, parameters, kind, return)) ->
      type_params, parameters, kind, return
    | TypAction (data_params, ctrl_params) ->
      let params = data_params @ ctrl_params in
      [], params, FunAction, TypVoid
    | _ ->
      failwith "Type is not callable."
  in
  let type_args = List.map ~f:(translate_type_opt env) type_args in
  let params_args = match_params_to_args env (fst func) params args in
  let type_params_args =
    match List.zip type_params type_args with
    | Ok v -> v
    | Unequal_lengths ->
      match type_args with
      | [] -> List.map ~f:(fun v -> v, None) type_params
      | _ -> failwith "Mismatch in type arguments."
  in
  let type_params_args =
    infer_type_arguments env ctx return_type type_params_args params_args type_params_args
  in
  let env = Checker_env.insert_types type_params_args env in
  let subst_param_arg ((MkParameter (opt, dir, typ, opt_value, var):coq_P4Parameter), arg) =
    let typ = saturate_type env typ in
    let param = MkParameter (opt, dir, typ, opt_value, var) in
    validate_param env (ctx_of_kind kind) typ dir call_info opt_value;
    param, arg
  in
  let params_args' = List.map params_args ~f:subst_param_arg in
  let typed_params_args = List.map ~f:(cast_param_arg env ctx call_info) params_args' in
  let out_type_args = List.map ~f:snd type_params_args in
  let out_args = List.map ~f:snd typed_params_args in
  let typ = saturate_type env return_type in
  let call: Prog.coq_ExpressionPreT = ExpFunctionCall (func_typed, out_type_args, out_args) in
  if call_ok ctx kind
  then call, typ, Directionless
  else failwith "Call not allowed in this context."

and select_constructor_params env info methods args =
  let matching_constructor (proto: Prog.coq_MethodPrototype) =
    match proto with
    | ProtoConstructor (_, _, params) ->
      begin try
          let _ = match_params_to_args env info params args in
          true
        with _ -> false
      end
    | ProtoMethod _ -> false
    | ProtoAbstractMethod _ -> false
  in
  match List.find ~f:matching_constructor methods with
  | Some (ProtoConstructor (_, _, params)) ->
    Some (match_params_to_args env info params args)
  | _ -> None

and get_decl_type_params (decl : Prog.coq_Declaration) =
  match decl with
  | DeclExternObject (_, _, type_params, _)
  | DeclParser (_, _, type_params, _, _, _, _)
  | DeclParserType (_, _, type_params, _)
  | DeclControl (_, _, type_params, _, _, _, _)
  | DeclControlType (_, _, type_params, _)
  | DeclPackageType (_, _, type_params, _) ->
    type_params
  | _ ->
    []

and get_decl_constructor_params env info (decl : Prog.coq_Declaration) args =
  let params_maybe_args =
    match decl with
    | DeclPackageType (_, _, _, constructor_params)
    | DeclParser (_, _, _, _, constructor_params, _, _)
    | DeclControl (_, _, _, _, constructor_params, _, _) ->
      Some (match_params_to_args env info constructor_params args)
    | DeclExternObject (_, _, _, methods) ->
      select_constructor_params env info methods args
    | _ ->
      None
  in
  match params_maybe_args with
  | Some ps -> ps
  | None ->
    failwith "Type does not have a constructor for these arguments."

and overload_param_count_ok (args: Argument.t list) (params: coq_P4Parameter list) =
  match params, args with
  | param :: params, arg :: args ->
    overload_param_count_ok args params
  | param :: params, [] ->
    (opt_of_param param || has_default_arg param)
    && overload_param_count_ok [] params
  | [], arg :: args ->
    false
  | [], [] ->
    true

and overload_param_names_ok (arg_names: P4string.t list) (params: coq_P4Parameter list) =
  let param_has_arg param =
    opt_of_param param || has_default_arg param ||
    List.exists arg_names
      ~f:(fun arg_name -> P4string.eq arg_name (var_of_param param))
  in
  let arg_has_param (arg_name: P4string.t) =
    List.exists params
      ~f:(fun (MkParameter (_, _, _, _, var): coq_P4Parameter) ->
          P4string.eq arg_name var)
  in
  List.for_all params ~f:param_has_arg && List.for_all arg_names ~f:arg_has_param

and resolve_constructor_overload_by ~f:(f: coq_P4Parameter list -> bool) env type_name =
  let ok : coq_P4Type -> bool =
    function
    | TypConstructor (_, _, parameters, _) -> f parameters
    | _ -> false
  in
  let candidates = Checker_env.find_types_of type_name env in
  match
    candidates
    |> List.map ~f:fst
    |> List.find ~f:ok
  with
  | Some (Typed.TypConstructor (ts, ws, ps, ret)) -> ts, ws, ps, ret
  | ctor -> failwith "Bad constructor type or no matching constructor."

and resolve_constructor_overload env type_name args =
  let arg_name arg =
    match snd arg with
    | Argument.KeyValue {key; _} -> Some key
    | _ -> None
  in
  match list_option_flip (List.map ~f:arg_name args) with
  | Some arg_names ->
    resolve_constructor_overload_by ~f:(overload_param_names_ok arg_names) env type_name
  | None ->
    resolve_constructor_overload_by ~f:(overload_param_count_ok args) env type_name

and resolve_function_overload_by ~f env ctx func : Prog.coq_Expression =
  let open Types.Expression in
  match snd func with
  | Name name ->
    let ok : coq_P4Type -> bool =
      function
      | TypFunction (MkFunctionType (_, parameters, _, _)) ->
        f parameters
      | _ -> false
    in
    begin match
        Checker_env.find_types_of name env
        |> List.map ~f:fst
        |> List.find ~f:ok
      with
      | Some typ -> MkExpression (fst func, ExpName name, typ, Directionless)
      | _ -> type_expression env ctx func
    end
  | ExpressionMember { expr; name } ->
    let expr_typed = type_expression env ctx expr in
    let expr_type = type_of_expr expr_typed in
    let prog_member: Prog.coq_ExpressionPreT =
      ExpExpressionMember (expr_typed, name)
    in
    let rec resolve_by_type typ : Prog.coq_Expression =
      begin match reduce_type env typ with
        | TypSpecializedType (TypExtern extern_name, args) ->
          let (MkExpression (info, expr, typ, dir)) = resolve_by_type (TypExtern extern_name) in
          let ext = Checker_env.find_extern (BareName extern_name) env in 
          let env_with_args = Checker_env.insert_types (List.zip_exn ext.type_params args) env in
          let typ = reduce_type env_with_args typ in
          MkExpression (info, expr, typ, dir)
        | TypExtern extern_name ->
          let ext = Checker_env.find_extern (BareName extern_name) env in 
          let works (meth: Prog.coq_ExternMethod) =
            let params = params_of_fn_type meth.typ in
            P4string.eq meth.name name && f params
          in
          begin match List.find ~f:works ext.methods with
            | Some p -> MkExpression (fst func, prog_member, TypFunction p.typ, Directionless)
            | None -> failwith "couldn't find matching method"
          end
        | _ ->
          let typ = saturate_type env (type_of_expr expr_typed) in
          begin match type_expression_member_function_builtin env info typ name with
            | Some typ -> MkExpression (fst func, prog_member, typ, Directionless)
            | None -> type_expression env ctx func
          end
      end
    in
    resolve_by_type expr_type
  | _ -> type_expression env ctx func

and resolve_function_overload env ctx type_name args =
  let arg_name arg =
    match snd arg with
    | Argument.KeyValue {key; _} -> Some key
    | _ -> None
  in
  match list_option_flip (List.map ~f:arg_name args) with
  | Some arg_names ->
    resolve_function_overload_by ~f:(overload_param_names_ok arg_names) env ctx type_name
  | None ->
    resolve_function_overload_by ~f:(overload_param_count_ok args) env ctx type_name

and type_constructor_invocation env ctx info decl_name type_args args : Prog.coq_Expression list * coq_P4Type =
  let type_args = List.map ~f:(translate_type_opt env) type_args in
  let t_params, w_params, params, ret = resolve_constructor_overload env decl_name args in
  let params_args = match_params_to_args env info params args in
  let type_params_args = infer_constructor_type_args env ctx t_params w_params params_args type_args in
  let env' = Checker_env.insert_types type_params_args env in
  let cast_arg (param, arg: coq_P4Parameter * Types.Expression.t option) =
    let MkParameter (is_opt, _, _, _, _) = param in
    match cast_param_arg env' ctx info (param, arg) with
    | _, Some e ->
      if compile_time_known_expr env e
      then Some e
      else failwith "Constructor argument is not compile-time known."
    | _, None ->
      if is_opt
      then None
      else failwith "Missing constructor argument."
  in
  let args_typed =
    params_args
    |> List.filter_map ~f:cast_arg
  in
  let ret = saturate_type env' ret in
  args_typed, ret

(* Section 14.1 *)
and type_nameless_instantiation env ctx info typ args =
  match snd typ with
  | Type.SpecializedType { base; args = type_args } ->
    begin match snd base with
      | TypeName decl_name ->
        let out_args, out_typ =
          type_constructor_invocation env ctx info decl_name type_args args
        in
        ExpNamelessInstantiation (translate_type env typ, out_args),
        out_typ,
        Directionless
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
and type_mask env ctx expr mask =
  let expr_typed = type_expression env ctx expr in
  let mask_typed = type_expression env ctx mask in
  let res_typ : coq_P4Type =
    match (type_of_expr expr_typed), (type_of_expr mask_typed) with
    | TypBit w1, TypBit w2 when w1 = w2 ->
      TypBit w1
    | TypBit width, TypInteger
    | TypInteger, TypBit width ->
      TypBit width
    | TypInteger, TypInteger ->
      TypInteger
    | l_typ, r_typ -> failwith "bad type for mask operation &&&"
  in
  ExpMask (expr_typed, mask_typed),
  TypSet res_typ,
  Directionless

(* Section 8.12.4 *)
and type_range env ctx lo hi = 
  let lo_typed = type_expression env ctx lo in
  let hi_typed = type_expression env ctx hi in
  let typ : coq_P4Type =
    match (type_of_expr lo_typed), (type_of_expr hi_typed) with
    | TypBit l, TypBit r when l = r ->
      TypBit l
    | TypInt l, TypInt r when l = r ->
      TypInt l
    | TypInteger, TypInteger -> TypInteger
    (* TODO: add pretty-printer and [to_string] for Typed module *)
    | TypBit width, hi_typ ->
      raise_mismatch (info hi) ("bit<" ^ (string_of_int width) ^ ">") hi_typ
    | TypInt width, hi_typ ->
      raise_mismatch (info hi) ("int<" ^ (string_of_int width) ^ ">") hi_typ
    | lo_typ, _ -> raise_mismatch (Info.merge (info lo) (info hi)) "int or bit" lo_typ
  in
  ExpRange (lo_typed, hi_typed), TypSet typ, Directionless

and check_statement_legal_in (ctx: coq_StmtContext) (stmt: Types.Statement.t) : unit =
  match ctx, snd stmt with
  | StmtCxAction, Switch _ ->
    failwith "Branching statement not allowed in action."
  | StmtCxParserState, Conditional _
  | StmtCxParserState, Switch _ ->
    failwith "Branching statement not allowed in parser."
  | _ -> ()

and type_statement (env: Checker_env.t) (ctx: coq_StmtContext) (stmt: Types.Statement.t)
  : Prog.coq_Statement * Checker_env.t =
  check_statement_legal_in ctx stmt;
  match snd stmt with
  | MethodCall { func; type_args; args } ->
    type_method_call env ctx (fst stmt) func type_args args
  | Assignment { lhs; rhs } ->
    type_assignment env ctx (fst stmt) lhs rhs
  | DirectApplication { typ; args } ->
    type_direct_application env ctx (fst stmt) typ args
  | Conditional { cond; tru; fls } ->
    type_conditional env ctx (fst stmt) cond tru fls
  | BlockStatement { block } ->
    type_block env ctx (fst stmt) block
  | Exit ->
    MkStatement (fst stmt, StatExit, StmVoid), env
  | EmptyStatement ->
      MkStatement (fst stmt, StatEmpty, StmUnit), env
  | Return { expr } ->
    type_return env ctx (fst stmt) expr
  | Switch { expr; cases } ->
    type_switch env ctx (fst stmt) expr cases
  | DeclarationStatement { decl } ->
    type_declaration_statement env ctx (fst stmt) decl

(* Section 8.17 *)
and type_method_call env ctx call_info func type_args args =
  let expr_ctx = expr_ctxt_of_stmt_ctxt ctx in
  let call, typ, dir =
    type_function_call env expr_ctx call_info func type_args args
  in
  match call with
  | ExpFunctionCall (func, type_args, args) ->
    MkStatement (call_info, StatMethodCall (func, type_args, args), StmUnit),
    env
  | _ -> failwith "function call not typed as FunctionCall?"

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
and type_assignment env ctx stmt_info lhs rhs =
  let expr_ctx = expr_ctxt_of_stmt_ctxt ctx in
  let lhs_typed = type_expression env expr_ctx lhs in
  if not @@ is_lvalue env lhs_typed
  then raise_s [%message "Must be an lvalue"
        ~lhs:(lhs:Types.Expression.t)]
  else
    let rhs_typed = cast_expression env expr_ctx (type_of_expr lhs_typed) rhs in
    ignore (assert_same_type env (info lhs) (info rhs)
              (type_of_expr lhs_typed) (type_of_expr rhs_typed));
    MkStatement (stmt_info, StatAssignment (lhs_typed, rhs_typed), StmUnit),
    env

(* This belongs in an elaboration pass, really. - Ryan *)
and type_direct_application env ctx stmt_info typ args =
  let expr_ctx = expr_ctxt_of_stmt_ctxt ctx in
  let open Types.Expression in
  let instance = NamelessInstantiation {typ = typ; args = []} in
  let apply = ExpressionMember {expr = Info.dummy, instance;
                                name = {tags=Info.dummy; str="apply"}} in
  let call = FunctionCall {func = Info.dummy, apply;
                           type_args = [];
                           args} in
  let call_typed = type_expression env expr_ctx (Info.dummy, call) in
  match preexpr_of_expr call_typed with
  | ExpFunctionCall (func, [], args) ->
    let args =
      List.map args
        ~f:(function
            | Some a -> a
            | None -> failwith "missing argument")
    in
    let stmt: Prog.coq_StatementPreT =
      StatDirectApplication (translate_type env typ, args)
    in
    MkStatement (stmt_info, stmt, StmUnit),
    env
  | _ -> failwith "function call not typed as FunctionCall?"

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
and type_conditional env ctx stmt_info cond true_branch false_branch =
  let expr_ctx = expr_ctxt_of_stmt_ctxt ctx in
  let expr_typed = cast_expression env expr_ctx TypBool cond in
  assert_bool (info cond) (type_of_expr expr_typed) |> ignore;
  let type' stmt = fst (type_statement env ctx stmt) in
  let true_typed = type' true_branch in
  let true_type = type_of_stmt true_typed in
  let false_typed = option_map type' false_branch in
  let stmt_out: Prog.coq_StatementPreT =
    StatConditional (expr_typed, true_typed, false_typed)
  in
  match false_typed with
  | None -> MkStatement (stmt_info, stmt_out, StmUnit), env
  | Some false_typed ->
    let typ =
      match true_type, type_of_stmt false_typed with
      | StmVoid, StmVoid -> StmVoid
      | _ -> StmUnit
    in
    MkStatement (stmt_info, stmt_out, typ), env

and type_statements env ctx statements =
  let fold (prev_type, stmts, env) statement =
    (* Cannot have statements after a void statement *)
    let stmt_typed, env = type_statement env ctx statement in
    let next_typ =
      match prev_type, type_of_stmt stmt_typed with
      | _, StmVoid
      | StmVoid, _ -> StmVoid
      | _ -> StmUnit
    in
    (next_typ, stmt_typed :: stmts, env)
  in
  List.fold_left ~f:fold ~init:(StmUnit, [], env) statements


and rev_list_to_block info: Prog.coq_Statement list -> Prog.coq_Block =
  let f block stmt: Prog.coq_Block = BlockCons (stmt, block) in
  let init: Prog.coq_Block = BlockEmpty info in
  List.fold_left ~f ~init

and type_block env ctx stmt_info block =
  let typ, stmts, env' = type_statements env ctx (snd block).statements in
  let block = rev_list_to_block stmt_info stmts in
  MkStatement (stmt_info, StatBlock block, typ), env

(* Section 11.4
 * Can a return statement update the environment?
 *
 *          Δ, T, Γ |- e : t
 * ---------------------------------------------
 *    Δ, T, Γ |- return e: void ,Δ, T, Γ
*)
and type_return env ctx stmt_info expr =
  let expr_ctx = expr_ctxt_of_stmt_ctxt ctx in
  let ret_typ =
    match ctx with
    | StmtCxApplyBlock
    | StmtCxAction -> TypVoid
    | StmtCxFunction t -> t
    | StmtCxParserState -> failwith "return in parser state not allowed"
  in
  let (stmt, typ) : Prog.coq_StatementPreT * coq_P4Type =
    match expr with
    | None -> StatReturn None, TypVoid
    | Some e ->
      let e_typed = cast_expression env expr_ctx ret_typ e in
      StatReturn (Some e_typed), type_of_expr e_typed
  in
  MkStatement (stmt_info, stmt, StmVoid), env

(* Section 11.7 *)
and type_switch env ctx stmt_info expr cases =
  let open Types.Statement in
  let expr_ctx = expr_ctxt_of_stmt_ctxt ctx in
  if ctx <> StmtCxApplyBlock
  then failwith "switch statements not allowed in context";
  let expr_typed = type_expression env expr_ctx expr in
  let action_typ_name, action_names =
    match reduce_type env (type_of_expr expr_typed) with
    | TypEnum (name, _, names) -> name, names
    | _ -> raise_mismatch stmt_info "table action enum" (type_of_expr expr_typed)
  in
  let lbl_seen cases_done lbl =
    let case_name_eq label (case: Prog.coq_StatementSwitchCase) =
      match case with
      | StatSwCaseAction (_, lbl, _)
      | StatSwCaseFallThrough (_, lbl) ->
        match label, lbl with
        | Default, StatSwLabDefault _ -> true
        | Name n1, StatSwLabName (_, n2) ->
          P4string.eq n1 n2
        | _ -> false
    in
    List.exists ~f:(case_name_eq lbl) cases_done
  in
  let label_checker cases_done (label: Types.Statement.switch_label): Prog.coq_StatementSwitchLabel =
    if lbl_seen cases_done (snd label) then raise (Type ((fst label), Duplicate));
    if lbl_seen cases_done Default then raise (Type ((fst label), UnreachableBlock));
    match snd label with
    | Default ->
      StatSwLabDefault (fst label)
    | Name name ->
      if List.mem ~equal:P4string.eq action_names name
      then StatSwLabName (fst label, name)
      else raise_unfound_member name.tags name.str
  in
  let case_checker cases_done (case_info, case) =
    match case with
    | Action { label; code = block } ->
      let block_stmt_typed, env = type_block env ctx (fst block) block in
      let label_typed = label_checker cases_done label in
      let block_typed =
        match prestmt_of_stmt block_stmt_typed with
        | StatBlock block -> block
        | _ -> failwith "bug: expected block"
      in
      cases_done @ [StatSwCaseAction (case_info, label_typed, block_typed)]
    | FallThrough { label } ->
      let label_typed = label_checker cases_done label in
      cases_done @ [StatSwCaseFallThrough (case_info, label_typed)]
  in
  let cases = List.fold ~init:[] ~f:case_checker cases in
  MkStatement (stmt_info, StatSwitch (expr_typed, cases), StmUnit), env

and stmt_of_decl_stmt (decl: Prog.coq_Declaration) : Prog.coq_Statement =
  let info, (stmt: Prog.coq_StatementPreT) =
    match decl with
    | DeclConstant (info, typ, name, value) ->
      info, StatConstant (typ, name, value)
    | DeclVariable (info, typ, name, init) ->
      info, StatVariable (typ, name, init)
    | DeclInstantiation (info, typ, args, name, init) ->
      info, StatInstantiation (typ, args, name, init)
    | _ ->
      Info.dummy, StatEmpty
  in
  MkStatement (info, stmt, StmUnit)

(* Section 10.3 *)
and type_declaration_statement env ctx stmt_info (decl: Declaration.t) : Prog.coq_Statement * Checker_env.t =
  match snd decl with
  | Constant _
  | Instantiation _
  | Variable _ ->
    let decl_typed, env' = type_declaration env (DeclCxStatement ctx) decl in
    stmt_of_decl_stmt decl_typed, env'
  | _ -> raise_s [%message "declaration used as statement, but that's not allowed. Parser bug?" ~decl:(decl: Types.Declaration.t)]

(* Section 10.1
 *
 *          Δ, T, Γ |- e : t' = t
 * ---------------------------------------------
 *    Δ, T, Γ |- const t x = e : Δ, T, Γ[x -> t]
*)
and type_constant env ctx decl_info annotations typ name expr : Prog.coq_Declaration * Checker_env.t =
  let expr_ctx = expr_ctxt_of_decl_ctxt ctx in
  let expected_typ = translate_type env typ in
  let typed_expr = cast_expression env expr_ctx expected_typ expr in
  match compile_time_eval_expr env typed_expr with
  | Some value ->
    DeclConstant (decl_info, translate_type env typ, name, value),
    env
    |> Checker_env.insert_dir_type_of (BareName name) expected_typ Directionless
    |> Checker_env.insert_const (BareName name) (ValBase value)
  | None ->
    failwith "expression not compile-time-known"

and insert_params (env: Checker_env.t) (params: Types.Parameter.t list) : Checker_env.t =
  let open Types.Parameter in
  let insert_param env (_, p) =
    let typ = translate_type env p.typ in
    let dir = translate_direction p.direction in
    Checker_env.insert_dir_type_of (BareName p.variable) typ dir env
  in
  List.fold_left ~f:insert_param ~init:env params

(* Section 10.3 *)
and type_instantiation env ctx info annotations typ args name : Prog.coq_Declaration * Checker_env.t =
  let expr_ctx = expr_ctxt_of_decl_ctxt ctx in
  let instance_typed = type_nameless_instantiation env expr_ctx info typ args in
  let instance_expr, instance_type, instance_dir = instance_typed in
  begin match instance_type, ctx with
    | TypControl _, DeclCxTopLevel ->
      failwith "controls cannot be instantiated in the top level scope"
    | TypParser _, DeclCxTopLevel ->
      failwith "parsers cannot be instantiated in the top level scope"
    | _ -> ()
  end;
  match instance_expr with
  | ExpNamelessInstantiation (typ, args) ->
    DeclInstantiation (info, typ, args, name, None),
    Checker_env.insert_type_of (BareName name) instance_type env
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
  infer_type_arguments env ctx TypVoid full_params_args params_args []

(* Terrible hack - Ryan *)
and check_match_type_eq env info set_type element_type =
  match set_type with
  | TypSet (TypEnum (_, Some carrier, _)) ->
    check_match_type_eq env info (TypSet carrier) element_type
  | _ ->
    match element_type with
    | TypEnum (_, Some elt_carrier, _) ->
      check_match_type_eq env info set_type elt_carrier
    | _ ->
      assert_type_equality env info set_type (TypSet element_type)

and check_match env ctx (info, m: Types.Match.t) (expected_type: coq_P4Type) : Prog.coq_Match =
  match m with
  | Default
  | DontCare ->
    MkMatch (info, MatchDontCare, TypSet expected_type)
  | Expression { expr } ->
    let expr_typed = cast_expression env ctx (TypSet expected_type) expr in
    let typ = type_of_expr expr_typed in
    check_match_type_eq env info typ expected_type;
    MkMatch (info, MatchExpression expr_typed, TypSet typ)

and check_match_product env ctx (ms: Types.Match.t list) (expected_types: coq_P4Type list) =
  match ms, expected_types with
  | [m], [t] ->
    [check_match env ctx m t]
  | [m], types ->
    [check_match env ctx m (TypList types)]
  | ms, types ->
    List.map ~f:(fun (m, t) -> check_match env ctx m t) @@ List.zip_exn ms types

and type_select_case env ctx state_names expr_types ((case_info, case): Types.Parser.case) : Prog.coq_ParserCase =
  let matches_typed = check_match_product env ctx case.matches expr_types in
  if List.mem ~equal:P4string.eq state_names case.next
  then MkParserCase (case_info, matches_typed, case.next)
  else raise_s [%message "state name unknown" ~name:(case.next.str: string)]

and type_transition env ctx state_names transition : Prog.coq_ParserTransition =
  let open Parser in
  let trans_info = fst transition in
  match snd transition with
  | Direct {next} ->
    if List.mem ~equal:P4string.eq state_names next
    then ParserDirect (trans_info, next)
    else raise @@ Type (next.tags, (Error.Unbound next.str))
  | Select {exprs; cases} ->
    let exprs_typed = List.map ~f:(type_expression env ctx) exprs in
    let expr_types = List.map ~f:type_of_expr exprs_typed in
    let cases_typed =
      List.map ~f:(type_select_case env ctx state_names expr_types) cases
    in
    ParserSelect (trans_info, exprs_typed, cases_typed)

and type_parser_state env state_names (state: Parser.state) : Prog.coq_ParserState =
  let (_, stmts_typed, env) = type_statements env StmtCxParserState (snd state).statements in
  let transition_typed = type_transition env ExprCxParserState state_names (snd state).transition in
  MkParserState (fst state, (snd state).name, stmts_typed, transition_typed)

and check_state_names names =
  match List.find_a_dup names
          ~compare:(fun (x: P4string.t) y ->
              String.compare x.str y.str)
  with
  | Some duplicated -> raise_s [%message "duplicate state name in parser" ~state:duplicated.str]
  | None ->
    if List.mem ~equal:P4string.eq names {tags=Info.dummy; str="start"}
    then ()
    else raise_s [%message "parser is missing start state"];

and open_parser_scope env ctx params constructor_params locals states =
  let open Parser in
  let constructor_params_typed = type_constructor_params env ctx constructor_params in
  let params_typed = type_params env (ParamCxRuntime ctx) params in
  let env = insert_params env constructor_params in
  let env = insert_params env params in
  let locals_typed, env = type_declarations env DeclCxNested locals in
  let program_state_names = List.map ~f:(fun (_, state) -> state.name) states in
  (* TODO: check that no program_state_names overlap w/ standard ones
   * and that there is some "start" state *)
  let accept: P4string.t = {tags=Info.dummy; str="accept"} in
  let reject: P4string.t = {tags=Info.dummy; str="reject"} in
  let state_names = program_state_names @ [accept; reject] in
  check_state_names state_names;
  (env, state_names, constructor_params_typed, params_typed, locals_typed)

(* Section 12.2 *)
and type_parser env info name annotations type_params params constructor_params locals states =
  if List.length type_params > 0
  then failwith "Parser declarations cannot have type parameters";
  let env', state_names, constructor_params_typed, params_typed, locals_typed =
    open_parser_scope env ParamCxDeclParser params constructor_params locals states
  in
  let states_typed = List.map ~f:(type_parser_state env' state_names) states in
  let parser_typed : Prog.coq_Declaration =
    DeclParser (info,
                name,
                [],
                params_typed,
                constructor_params_typed,
                locals_typed,
                states_typed)
  in
  let parser_type = Typed.MkControlType ([], params_typed) in
  let ctor_type = Typed.TypConstructor ([], [], constructor_params_typed, TypParser parser_type) in
  let env = Checker_env.insert_type_of (BareName name) ctor_type env in
  parser_typed, env

and open_control_scope env ctx params constructor_params locals =
  let params_typed = type_params env (ParamCxRuntime ctx) params in
  let constructor_params_typed = type_constructor_params env ctx constructor_params in
  let env = insert_params env constructor_params in
  let env = insert_params env params in
  let locals_typed, env = type_declarations env DeclCxNested locals in
  env, params_typed, constructor_params_typed, locals_typed

(* Section 13 *)
and type_control env info name annotations type_params params constructor_params locals apply =
  if List.length type_params > 0
  then failwith "Control declarations cannot have type parameters";
  let inner_env, params_typed, constructor_params_typed, locals_typed =
    open_control_scope env ParamCxDeclControl params constructor_params locals
  in
  let block_typed, _ = type_block inner_env StmtCxApplyBlock (fst apply) apply in
  let apply_typed =
    match prestmt_of_stmt block_typed with
    | StatBlock block -> block
    | _ -> failwith "expected BlockStatement"
  in
  let control : Prog.coq_Declaration =
    DeclControl (info,
                 name,
                 [],
                 params_typed,
                 constructor_params_typed,
                 locals_typed,
                 apply_typed)
  in
  let control_type =
    Typed.MkControlType ([], params_typed)
  in
  let ctor_type = Typed.TypConstructor ([], [], constructor_params_typed, TypControl control_type) in
  let env = Checker_env.insert_type_of (BareName name) ctor_type env in
  control, env

(* Section 9

 * Function Declaration:
 *
 *        Γ' = union over i Γ (xi -> di ti)
 *   forall k,  Δk, Tk, Γk' |- stk+1 : Δk+1, Tk+1, Γk+1'
 *     stk = return ek => Δk, Tk, Γk' |- ek : t' = tr
 * -------------------------------------------------------
 *    Δ, T, Γ |- tr fn<...Aj,...>(...di ti xi,...){...stk;...}
*)
and type_function env (ctx: Typed.coq_StmtContext) info return name type_params params body =
  let (paramctx: Typed.coq_ParamContextDeclaration), (kind: Typed.coq_FunctionKind) =
    match ctx with
    | StmtCxFunction _ -> ParamCxDeclFunction, FunFunction
    | StmtCxAction -> ParamCxDeclAction, FunAction
    | _ -> failwith "bad context for function"
  in
  let body_env = Checker_env.insert_type_vars type_params env in
  let params_typed = List.map ~f:(type_param body_env (ParamCxRuntime paramctx)) params in
  let return_type = return |> translate_type env in
  let body_env = insert_params body_env params in
  let body_stmt_typed, _ = type_block body_env ctx (fst body) body in
  let body_typed : Prog.coq_Block =
    match body_stmt_typed, return_type with
    | MkStatement (_, StatBlock blk, _), TypVoid
    | MkStatement (_, StatBlock blk, StmVoid), _ ->
      blk
    | MkStatement (_, StatBlock blk, StmUnit), non_void ->
      failwith "function body does not return a value of the required type"
    | _ ->
      failwith "bug: expected BlockStatement"
  in
  let funtype = MkFunctionType (type_params, params_typed, kind, return_type) in
  let env = Checker_env.insert_type_of (BareName name) (TypFunction funtype) env in
  let fn_typed : Prog.coq_Declaration =
    DeclFunction (info,
                  return_type,
                  name,
                  type_params,
                  params_typed,
                  body_typed)
  in
  fn_typed, env

(* Section 7.2.9.1 *)
and type_extern_function env info annotations return name type_params params =
  let return = return |> translate_type env in
  let env' = Checker_env.insert_type_vars type_params env in
  let params_typed = List.map ~f:(type_param env' (ParamCxRuntime ParamCxDeclFunction)) params in
  let typ: coq_FunctionType =
    MkFunctionType (type_params, params_typed, FunExtern, return)
  in
  let fn_typed: Prog.coq_Declaration =
    DeclExternFunction (info, return, name, type_params, params_typed)
  in
  fn_typed, Checker_env.insert_type_of (BareName name) (TypFunction typ) env

and is_variable_type env (typ: coq_P4Type) =
  let typ = saturate_type env typ in
  match typ with
  | TypTypeName name -> true
  | TypNewType (_, typ) ->
    is_variable_type env typ
  | TypBool
  | TypInt _
  | TypBit _
  | TypVarBit _
  | TypArray _
  | TypTuple _
  | TypRecord _
  | TypError
  | TypMatchKind
  | TypHeader _
  | TypHeaderUnion _
  | TypStruct _
  | TypEnum _ ->
    true
  | TypString
  | TypInteger
  | TypList _
  | TypSet _
  | TypVoid
  | TypSpecializedType _
  | TypPackage _
  | TypControl _
  | TypParser _
  | TypExtern _
  | TypFunction _
  | TypAction _
  | TypConstructor _
  | TypTable _ ->
    false

(* Section 10.2
 *
 *          Δ, T, Γ |- e : t' = t
 * ---------------------------------------------
 *    Δ, T, Γ |- t x = e : Δ, T, Γ[x -> t]
*)
and type_variable env ctx info annotations typ name init =
  let expr_ctx = expr_ctxt_of_decl_ctxt ctx in
  let expected_typ = translate_type env typ in
  if not @@ is_variable_type env expected_typ
  then failwith "Cannot declare variables of this type";
  if not @@ is_well_formed_type env expected_typ
  then failwith "type is not well-formed";
  if ctx = DeclCxTopLevel
  then failwith "variables cannot be declared at the top level";
  let init_typed =
    match init with
    | None -> None
    | Some value ->
      let expected_typ = translate_type env typ in
      let typed_expr = cast_expression env expr_ctx expected_typ value in
      Some typed_expr
  in
  let var_typed : Prog.coq_Declaration =
    DeclVariable (info, expected_typ, name, init_typed)
  in
  let env = Checker_env.insert_dir_type_of (BareName name) expected_typ InOut env in
  var_typed, env

(* Section 12.11 *)
and type_value_set env ctx info annotations typ size name =
  let element_type = translate_type env typ in
  let size_typed = type_expression env ExprCxConstant size in
  let env = Checker_env.insert_type_of (BareName name) (TypSet element_type) env in
  let value_set : Prog.coq_Declaration =
    DeclValueSet (info, element_type, size_typed, name)
  in
  value_set, env

(* Section 13.1 *)
and type_action env info annotations name params body =
  let fn_typed, fn_env =
    type_function env StmtCxAction info (Info.dummy, Types.Type.Void) name [] params body
  in
  let action_typed, action_type =
    match fn_typed with
    | DeclFunction (info, return, name, type_params, params, body) ->
      let data_params, ctrl_params =
        List.split_while params
          ~f:(fun (MkParameter (_, dir, _, _, _)) -> dir <> Directionless)
      in
      let check_ctrl (MkParameter (_, dir, _, _, _)) =
        if dir <> Directionless
        then failwith "data parameter after a control parameter in action declaration"
      in
      List.iter ~f:check_ctrl ctrl_params;
      let action_type : coq_P4Type = TypAction (data_params, ctrl_params) in
      let action: Prog.coq_Declaration =
        DeclAction (info, name, data_params, ctrl_params, body)
      in
      action, action_type
    | _ -> failwith "expected function declaration"
  in
  action_typed,
  Checker_env.insert_type_of (BareName name) action_type env

(* Section 13.2 *)
and type_table env ctx info annotations name properties : Prog.coq_Declaration * Checker_env.t =
  type_table' env ctx info annotations name None [] None None None (List.map ~f:snd properties)

and type_keys env ctx keys =
  let expr_ctx = expr_ctxt_of_decl_ctxt ctx in
  let type_key key: Prog.coq_TableKey =
    let {key; match_kind; annotations}: Table.pre_key = snd key in
    match Checker_env.find_type_of_opt (BareName match_kind) env with
    | Some (TypMatchKind, _) ->
      let expr_typed = type_expression env expr_ctx key in
      MkTableKey (fst key, expr_typed, match_kind)
    | _ ->
      raise_s [%message "invalid match_kind" ~match_kind:match_kind.str]
  in
  List.map ~f:type_key keys

and type_table_actions env ctx key_types actions =
  let expr_ctx = expr_ctxt_of_decl_ctxt ctx in
  let type_table_action (call_info, action: Table.action_ref) : Prog.coq_TableActionRef =
    let name = action.name in
    let data_params =
      match Checker_env.find_type_of_opt name env with
      | Some (TypAction (data_params, _), _) ->
        data_params
      | _ ->
        raise_s [%message "invalid action" ~action:(action.name: P4name.t)]
    in
    (* Below should fail if there are control plane arguments *)
    let params_args = match_params_to_args env call_info data_params action.args in
    let type_param_arg env (param, expr: coq_P4Parameter * Expression.t option) =
      match expr with
      | Some expr ->
        let arg_typed = cast_expression env expr_ctx (type_of_param param) expr in
        check_direction env (dir_of_param param) arg_typed;
        Some arg_typed
      | None ->
        match dir_of_param param with
        | Out -> None
        | _ ->
          failwith "don't care argument (underscore) provided for non-out parameter"
    in
    let args_typed = List.map ~f:(type_param_arg env) params_args in
    let pre_ref: Prog.coq_TablePreActionRef = 
      MkTablePreActionRef (name, args_typed)
    in
    MkTableActionRef (call_info, pre_ref, fst @@ Checker_env.find_type_of name env)
  in
  let action_typs = List.map ~f:type_table_action actions in
  (* Need to fail in the case of duplicate action names *)
  let action_names = List.map ~f:(fun a -> (snd a).name) actions in
  List.zip_exn action_names action_typs

and type_table_entries env ctx entries key_typs action_map =
  let expr_ctx = expr_ctxt_of_decl_ctxt ctx in
  let type_table_entry (entry_info, entry: Table.entry) : Prog.coq_TableEntry =
    let matches_typed = check_match_product env expr_ctx entry.matches key_typs in
    match List.Assoc.find action_map ~equal:P4name.name_eq (snd entry.action).name with
    | None ->
      failwith "Entry must call an action in the table."
    | Some (Poulet4.Syntax.MkTableActionRef (action_info, action,
                                             TypAction (data_params, ctrl_params))) ->
      let type_arg (param: coq_P4Parameter) (arg_info, arg: Argument.t) =
        begin match arg with
          (* Direction handling probably is incorrect here. *)
          | Expression {value = exp} ->
            Some (cast_expression env expr_ctx (type_of_param param) exp)
          | _ -> failwith "Actions in entries only support positional arguments."
        end in
      let args_typed = List.map2_exn ~f:type_arg ctrl_params (snd entry.action).args in
      let pre_action_ref : Prog.coq_TablePreActionRef =
        MkTablePreActionRef ((snd entry.action).name, args_typed)
      in
      let action_ref_typed : Prog.coq_TableActionRef =
        MkTableActionRef (action_info, pre_action_ref, TypAction (data_params, ctrl_params))
      in
      MkTableEntry (entry_info, matches_typed, action_ref_typed)
    | _ -> failwith "Table actions must have action types."
  in
  List.map ~f:type_table_entry entries

(* syntactic equality of expressions *)
and expr_eq env (expr1: Prog.coq_Expression) (expr2: Prog.coq_Expression) : bool =
  let key_val_eq ((MkKeyValue (_, k1, v1)): Prog.coq_KeyValue)
                 ((MkKeyValue (_, k2, v2)): Prog.coq_KeyValue) =
    P4string.eq k1 k2 && expr_eq env v1 v2
  in
  let e1 = preexpr_of_expr expr1 in
  let e2 = preexpr_of_expr expr2 in
  match e1, e2 with
  | ExpBool true, ExpBool true
  | ExpBool false, ExpBool false
  | ExpDontCare, ExpDontCare -> true
  | ExpInt ({value=val1; width_signed=width1; _}),
    ExpInt ({value=val2; width_signed=width2; _})
    -> Bigint.(val1 = val2) && width1 = width2
  | ExpString s1,
    ExpString s2
    -> P4string.eq s1 s2
  | ExpName n1, ExpName n2
    -> P4name.name_eq n1 n2
  | ExpArrayAccess (a1, i1),
    ExpArrayAccess (a2, i2)
    -> expr_eq env a1 a2 && expr_eq env i1 i2
  | ExpBitStringAccess (b1, l1, h1),
    ExpBitStringAccess (b2, l2, h2)
    -> expr_eq env b1 b2 && Bigint.equal l1 l2 && Bigint.equal h1 h2
  | ExpList v1, ExpList v2
    -> List.equal (expr_eq env) v1 v2
  | ExpRecord kv1, ExpRecord kv2
    -> List.equal key_val_eq kv1 kv2
  | ExpUnaryOp (o1, e1),
    ExpUnaryOp (o2, e2)
    -> o1 = o2 && expr_eq env e1 e2
  | ExpBinaryOp (b1, (l1, r1)),
    ExpBinaryOp (b2, (l2, r2))
    -> b1 = b2 && expr_eq env l1 l2 && expr_eq env r1 r2
  | ExpCast (t1, e1), ExpCast (t2, e2)
    -> type_equality env [] t1 t2 && expr_eq env e1 e2
  | ExpTypeMember (n1, s1),
    ExpTypeMember (n2, s2)
    -> P4name.name_eq n1 n2 && P4string.eq s1 s2
  | ExpErrorMember s1,
    ExpErrorMember s2
    -> P4string.eq s1 s2
  | ExpExpressionMember (e1, s1),
    ExpExpressionMember (e2, s2)
    -> expr_eq env e1 e2 && P4string.eq s1 s2
  | ExpTernary (c1, t1, f1),
    ExpTernary (c2, t2, f2)
    -> expr_eq env c1 c2 && expr_eq env t1 t2 && expr_eq env f1 f2
  | ExpFunctionCall (e1, t1, l1),
    ExpFunctionCall (e2, t2, l2)
    -> expr_eq env e1 e2 &&
       List.equal (Util.eq_opt ~f:(expr_eq env)) l1 l2
  | ExpNamelessInstantiation (t1, e1),
    ExpNamelessInstantiation (t2, e2)
    -> List.equal (expr_eq env) e1 e2
  | ExpMask (e1, m1), ExpMask (e2, m2)
    -> expr_eq env e1 e2 && expr_eq env m1 m2
  | ExpRange (l1, h1), ExpRange (l2, h2) 
    -> expr_eq env l1 l2 && expr_eq env h1 h2
  | _ -> false

and type_default_action
    env ctx (action_map : (P4name.t * Prog.coq_TableActionRef) list)
    action_expr : Prog.coq_TableActionRef =
  let expr_ctx: Typed.coq_ExprContext = ExprCxTableAction in
  let action_expr_typed = type_expression env expr_ctx action_expr in
  match preexpr_of_expr action_expr_typed with
  | ExpFunctionCall (MkExpression (_, (ExpName action_name), _, _), [], args) ->
    begin match List.Assoc.find ~equal:P4name.name_eq action_map action_name with
      | None -> failwith "couldn't find default action in action_map"
      | Some (MkTableActionRef (_, MkTablePreActionRef (_, prop_args), _)) ->
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
          MkTableActionRef (fst action_expr,
                            MkTablePreActionRef (action_name, args),
                            type_of_expr action_expr_typed)
        else raise_s [%message "default action's prefix of arguments do not match those of that in table actions property"]
    end
  | ExpName action_name ->
     let acts = List.map ~f:(fun (n, a) -> P4name.name_only n, a) action_map in
     let act = P4name.name_only action_name in
    if not @@ List.Assoc.mem ~equal:(=) acts act
    then failwith "couldn't find default action in action_map";
    MkTableActionRef (fst action_expr,
                      MkTablePreActionRef (action_name, []),
                      type_of_expr action_expr_typed)
  | e ->
    failwith "couldn't type default action as functioncall"

and keys_actions_ok keys actions =
  match keys with
  | Some [] -> true
  | Some ks -> List.length actions > 0
  | None -> List.length actions > 0

and type_table' env ctx info annotations (name: P4string.t) key_types action_map entries_typed size default_typed properties =
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
        raise_s [%message "multiple key properties in table?" ~name:name.str]
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
            let key_types' = List.map keys_typed
                ~f:(fun (MkTableKey (_, expr, _)) -> type_of_expr expr)
            in
            let entries_typed = type_table_entries env ctx entries key_types' action_map in
            type_table' env ctx info annotations name key_types action_map (Some entries_typed) size default_typed rest
          | None -> failwith "entries with no keys?"
        end
    end
  | Custom { name = {str = "default_action";_}; value; _ } :: rest ->
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
  | Custom { name = {str="size"; _}; value; _ } :: rest ->
    if size <> None then failwith "duplicated size properties?";
    let expr_ctx = expr_ctxt_of_decl_ctxt ctx in
    let value_typed = type_expression env expr_ctx value in
    let _ = assert_numeric (fst value) (type_of_expr value_typed) in
    let size = compile_time_eval_expr env value_typed in
    begin match size with
      | Some (ValBaseInteger size) ->
        let size: P4int.t = {tags=fst value; value=size; width_signed=None} in
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
    (* Aggregate table information. *)
    let action_names = action_map
                       |> begin fun l ->
                         if keys_actions_ok key_types l
                         then l
                         else raise_s [%message "Table must have a non-empty actions property"] end
                       |> List.map ~f:fst
                       |> List.map ~f:P4name.name_only
                       |> List.map ~f:(fun str -> {P4string.tags=Info.dummy; str})
    in
    let action_enum_name = {name with str="action_list_" ^ name.str} in
    let action_enum_typ = TypEnum (action_enum_name, None, action_names) in
    let key =
      match key_types with
      | Some ks -> ks
      | None -> failwith "no key property in table?"
    in
    (* Populate environment with action_enum *)
    (* names of action list enums are "action_list_<<table name>>" *)
    let env =
      Checker_env.insert_type (BareName action_enum_name)
        action_enum_typ env
    in
    let hit_field = MkFieldType ({tags=Info.dummy; str="hit"}, TypBool) in
    let miss_field = MkFieldType ({tags=Info.dummy; str="miss"}, TypBool) in
    (* How to represent the type of an enum member *)
    let run_field = MkFieldType ({tags=Info.dummy; str="action_run"}, action_enum_typ) in
    let apply_result_typ = TypStruct [hit_field; miss_field; run_field] in
    (* names of table apply results are "apply_result_<<table name>>" *)
    let result_typ_name = {name with str = "apply_result_" ^ name.str} in
    let env = Checker_env.insert_type (BareName result_typ_name) apply_result_typ env in
    let table_typ = TypTable result_typ_name in
    let table_typed : Prog.coq_Declaration =
      DeclTable (info,
                 name,
                 key,
                 List.map ~f:snd action_map,
                 entries_typed,
                 default_typed,
                 size,
                 [])
    in
    table_typed, Checker_env.insert_type_of (BareName name) table_typ env

(* Section 7.2.2 *)
and type_header env info annotations name fields =
  let fields_typed, type_fields = fields
                                  |> List.map ~f:(type_field env)
                                  |> List.unzip in
  let header_typ = TypHeader type_fields in
  if not @@ is_well_formed_type env header_typ
  then failwith "bad header type";
  let env = Checker_env.insert_type (BareName name) header_typ env in
  Poulet4.Syntax.DeclHeader (info, name, fields_typed), env

and type_field env (field_info, field) =
  let open Types.Declaration in
  let typ = saturate_type env (translate_type env field.typ) in
  let pre_field : Prog.coq_DeclarationField =
    MkDeclarationField (field_info, typ, field.name) in
  let pre_record_field : coq_FieldType =
    MkFieldType (field.name, typ) in
  pre_field, pre_record_field

and type_header_union_field env (field_info, field) =
  let open Types.Declaration in
  let typ = translate_type env field.typ in
  match saturate_type env typ with
  | TypHeader _ ->
    type_field env (field_info, field)
  | _ -> raise_s [%message "header union fields must have header type"
             ~field:((field_info, field): Types.Declaration.field)]

(* Section 7.2.3 *)
and type_header_union env info annotations name fields =
  let fields_typed, type_fields =
    List.unzip @@ List.map ~f:(type_header_union_field env) fields
  in
  let header_typ = TypHeaderUnion type_fields in
  if not @@ is_well_formed_type env header_typ
  then failwith "bad header type";
  let env = Checker_env.insert_type (BareName name) header_typ env in
  let header: Prog.coq_Declaration =
    DeclHeaderUnion (info, name, fields_typed) in
  header, env

(* Section 7.2.5 *)
and type_struct env info annotations name fields =
  let fields_typed, type_fields = List.unzip @@ List.map ~f:(type_field env) fields in
  let struct_typ = TypStruct type_fields in
  if not @@ is_well_formed_type env struct_typ
  then failwith "bad struct type";
  let env =
    Checker_env.insert_type (BareName name) struct_typ env in
  let struct_decl: Prog.coq_Declaration =
    DeclStruct (info, name, fields_typed) in
  struct_decl, env

(* Auxillary function for [type_error] and [type_match_kind],
 * which require unique names *)
and fold_unique members (_, member) =
  if List.mem ~equal:P4string.eq members member then
    failwith "Name already bound"
  else
    member :: members

(* Section 7.1.2 *)
(* called by type_type_declaration *)
and type_error env info members : Prog.coq_Declaration * Checker_env.t =
  let add_err env (e: P4string.t) =
    let name: P4name.t =
      QualifiedName ([], {tags = e.tags; str = "error." ^ e.str})
    in
    env
    |> Checker_env.insert_type_of name TypError
    |> Checker_env.insert_const name (ValBase (ValBaseError e))
  in
  let env = List.fold_left ~f:add_err ~init:env members in
  DeclError (info, members), env

(* Section 7.1.3 *)
and type_match_kind env info members : Prog.coq_Declaration * Checker_env.t =
  let add_mk env (e: P4string.t) =
    let name: P4name.t = QualifiedName ([], e) in
    env
    |> Checker_env.insert_type_of name TypMatchKind
    |> Checker_env.insert_const name (ValBase (ValBaseMatchKind e))
  in
  let env = List.fold_left ~f:add_mk ~init:env members in
  DeclMatchKind (info, members), env

(* Section 7.2.1 *)
and type_enum env info annotations (name: P4string.t) members : Prog.coq_Declaration * Checker_env.t =
  let enum_typ =
    TypEnum (name, None, members)
  in
  let add_member env (member: P4string.t) =
    let member_name: P4name.t =
      QualifiedName ([], {tags = member.tags;
                          str = name.str ^ "." ^ member.str}) in
    let enum_val: Prog.coq_Value =
      ValBase (ValBaseEnumField (name, member)) in
    env
    |> Checker_env.insert_type_of member_name enum_typ
    |> Checker_env.insert_const member_name enum_val
  in
  let env = Checker_env.insert_type (QualifiedName ([], name)) enum_typ env in
  let env = List.fold_left ~f:add_member ~init:env members in
  DeclEnum (info, name, members), env

(* Section 8.3 *)
and type_serializable_enum env ctx info annotations underlying_type
    (name: P4string.t) (members: (P4string.t * Expression.t) list)
  : Prog.coq_Declaration * Checker_env.t =
  let expr_ctx = expr_ctxt_of_decl_ctxt ctx in
  let underlying_type =
    underlying_type
    |> translate_type env
    |> saturate_type env
  in
  let underlying_type =
    match underlying_type with
    | TypInt _ | TypBit _ -> underlying_type
    | _ -> raise_mismatch info "fixed width numeric type for enum" underlying_type
  in
  let member_names = List.map ~f:fst members in
  let enum_type: coq_P4Type =
    TypEnum (name, Some underlying_type, member_names)
  in
  let add_member (env, members_typed) ((member: P4string.t), expr) =
    let member_name: P4name.t =
      QualifiedName ([], {member with
                          str=name.str ^ "." ^ member.str}) in
    let expr_typed = cast_expression env expr_ctx underlying_type expr in
    match compile_time_eval_expr env expr_typed with
    | Some value ->
      let enum_val: Prog.coq_Value =
        ValBase (ValBaseEnumField (name, member)) in
      env
      |> Checker_env.insert_type_of member_name enum_type
      |> Checker_env.insert_const member_name
        enum_val, members_typed @ [member, expr_typed]
    | None -> failwith "could not evaluate enum member"
  in
  let env = Checker_env.insert_type (QualifiedName ([], name)) enum_type env in
  let env, members = List.fold_left ~f:add_member ~init:(env, []) members in
  DeclSerializableEnum (info, enum_type, name, members), env

and type_extern_object env info annotations obj_name t_params methods =
  let extern_type = TypExtern obj_name in
  let extern_methods: Prog.coq_ExternMethods = {type_params = t_params; methods = []} in
  let env' = env
             |> Checker_env.insert_type_vars t_params
             |> Checker_env.insert_type (BareName obj_name) extern_type
             |> Checker_env.insert_extern (BareName obj_name) extern_methods
  in
  let consume_method (constructors, methods) m =
    match snd m with
    | MethodPrototype.Constructor { annotations; name = cname; params } ->
       if P4string.neq cname obj_name then failwith "Constructor name and type name disagree";
       let params_typed = type_constructor_params env' ParamCxDeclMethod params in
       let constructor_typed: Prog.coq_MethodPrototype =
         ProtoConstructor (info, cname, params_typed)
       in
       (constructor_typed :: constructors, methods)
    | MethodPrototype.Method { annotations; return; name; type_params = t_params; params }
    | MethodPrototype.AbstractMethod { annotations; return; name; type_params = t_params; params } ->
      if P4string.eq name obj_name
      then raise_s [%message "extern method must have different name from extern"
            ~m:(m: MethodPrototype.t)];
      let method_type_params = t_params in
      let method_type_params' = t_params in
      let env' = Checker_env.insert_type_vars method_type_params' env' in
      let params_typed = type_params env' (ParamCxRuntime ParamCxDeclMethod) params in
      let return_typed = translate_type env' return in
      let method_typed: Prog.coq_MethodPrototype =
        match snd m with
        | Method _ ->
          ProtoMethod (info, return_typed, name, method_type_params, params_typed)
        | AbstractMethod _ ->
          ProtoAbstractMethod (info, return_typed, name, method_type_params, params_typed)
        | _ -> failwith "bug"
      in
      (constructors, method_typed :: methods)
  in
  let (cs, ms) = List.fold_left ~f:consume_method ~init:([], []) methods in
  let extern_decl: Prog.coq_Declaration =
    DeclExternObject (info, obj_name, t_params, cs @ ms) in
  let extern_methods: Prog.coq_ExternMethods =
    { type_params = t_params;
      methods = List.map ~f:(method_prototype_to_extern_method obj_name) ms }
  in
  let extern_ctors =
    List.map cs ~f:(function
        | ProtoConstructor (_, cname, params_typed) ->
           if t_params <> []
           then let generic_args = List.map t_params ~f:(fun ty -> TypTypeName (BareName ty)) in
                TypConstructor (t_params, [], params_typed,
                                TypSpecializedType (extern_type, generic_args))
           else TypConstructor (t_params, [], params_typed, extern_type)
        | _ -> failwith "bug: expected constructor")
  in
  let env = Checker_env.insert_type (BareName obj_name) extern_type env in
  let env = Checker_env.insert_extern (BareName obj_name) extern_methods env in
  let env = List.fold extern_ctors ~init:env
              ~f:(fun env t -> Checker_env.insert_type_of (BareName obj_name) t env)
  in
  extern_decl, env

and method_prototype_to_extern_method extern_name (m: Prog.coq_MethodPrototype)
  : Prog.coq_ExternMethod =
  match m with
  | ProtoConstructor (_, name, params) ->
    { name = name;
      typ = MkFunctionType ([], params, FunExtern, TypTypeName (BareName extern_name)) }
  | ProtoAbstractMethod (_, return, name, type_params, params)
  | ProtoMethod (_, return, name, type_params, params) ->
    { name = name;
      typ = MkFunctionType (type_params, params, FunExtern, return) }

(* Section 7.3 *)
and type_type_def env ctx info annotations name typ_or_decl =
  match typ_or_decl with
  | Left typ ->
    let typ = translate_type env typ in
    let typedef_typed: Prog.coq_Declaration =
      DeclTypeDef (info, name, Coq_inl typ)
    in
    typedef_typed, Checker_env.insert_type (BareName name) typ env
  | Right decl ->
    let decl_name = Declaration.name decl in
    let decl_typed, env' = type_declaration env ctx decl in
    let decl_typ = Checker_env.resolve_type_name (BareName decl_name) env' in
    let typedef_typed: Prog.coq_Declaration =
      DeclTypeDef (info, name, Coq_inr decl_typed) in
    typedef_typed, Checker_env.insert_type (BareName name) decl_typ env'

and type_new_type env ctx info annotations name typ_or_decl =
  match typ_or_decl with
  | Left typ ->
    let typ = translate_type env typ in
    let newtype_typed: Prog.coq_Declaration =
      DeclNewType (info, name, Coq_inl typ) in
    let newtype = TypNewType (name, typ) in
    newtype_typed, Checker_env.insert_type (BareName name) newtype env
  | Right decl ->
    let decl_name = Declaration.name decl in
    let decl_typed, env = type_declaration env ctx decl in
    let decl_typ = Checker_env.resolve_type_name (BareName decl_name) env in
    let newtype_typed: Prog.coq_Declaration =
      DeclNewType (info, name, Coq_inr decl_typed) in
    let newtype = TypNewType (name, decl_typ) in
    newtype_typed, Checker_env.insert_type (BareName name) newtype env

(* Section 7.2.11.2 *)
and type_control_type env info annotations name t_params params =
  let body_env = Checker_env.insert_type_vars t_params env in
  let params_typed = type_params body_env (ParamCxRuntime ParamCxDeclControl) params in
  let ctrl_decl: Prog.coq_Declaration =
    DeclControlType (info, name, t_params, params_typed) in
  let ctrl_typ = TypControl (MkControlType (t_params, params_typed)) in
  ctrl_decl, Checker_env.insert_type (BareName name) ctrl_typ env

(* Section 7.2.11 *)
and type_parser_type env info annotations name t_params params =
  let body_env = Checker_env.insert_type_vars t_params env in
  let params_typed = type_params body_env (ParamCxRuntime ParamCxDeclParser) params in
  let parser_decl: Prog.coq_Declaration =
    DeclParserType (info, name, t_params, params_typed) in
  let parser_typ = TypParser (MkControlType (t_params, params_typed)) in
  parser_decl, Checker_env.insert_type (BareName name) parser_typ env

(* Section 7.2.12 *)
and type_package_type env info annotations name t_params params =
  let body_env = Checker_env.insert_type_vars t_params env in
  let params_typed, wildcard_params =
    type_params' ~gen_wildcards:true body_env (ParamCxConstructor ParamCxDeclPackage) params in
  let pkg_decl: Prog.coq_Declaration =
    DeclPackageType (info, name, t_params, params_typed)
  in
  let pkg_typ = TypPackage (t_params, wildcard_params, params_typed) in
  let ret     = TypPackage ([],       wildcard_params, params_typed) in
  let ctor_typ = TypConstructor (t_params, wildcard_params, params_typed, ret) in
  let env' =
    env
    |> Checker_env.insert_type_of (BareName name) ctor_typ
    |> Checker_env.insert_type (BareName name) pkg_typ
  in
  pkg_decl, env'

and check_param_shadowing params constructor_params =
  let open Types.Parameter in 
  let all_params = params @ constructor_params in
  let names = List.map ~f:(fun (_, p) -> p.variable) all_params in
  match List.find_a_dup names
          ~compare:(fun (x:P4string.t) y ->
              String.compare x.str y.str)
  with
  | Some dup -> raise_s [%message "duplicate parameter" ~dup:(dup.str)]
  | None -> ()

and type_declaration (env: Checker_env.t) (ctx: coq_DeclContext) (decl: Types.Declaration.t) : Prog.coq_Declaration * Checker_env.t =
  match snd decl with
  | Constant { annotations; typ; name; value } ->
    type_constant env ctx (fst decl) annotations typ name value
  | Instantiation { annotations; typ; args; name; init } ->
    begin match init with
      | Some init -> failwith "initializer block in instantiation unsupported"
      | None -> type_instantiation env ctx (fst decl) annotations typ args name
    end
  | Parser { annotations; name; type_params; params; constructor_params; locals; states } ->
    check_param_shadowing params constructor_params;
    type_parser env (fst decl) name annotations type_params params constructor_params locals states
  | Control { annotations; name; type_params; params; constructor_params; locals; apply } ->
    check_param_shadowing params constructor_params;
    type_control env (fst decl) name annotations type_params params constructor_params locals apply
  | Function { return; name; type_params; params; body } ->
    check_param_shadowing params [];
    let ret_type = translate_type env return in
    let ctx: coq_StmtContext = StmtCxFunction ret_type in
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

and type_declarations env ctx decls: Prog.coq_Declaration list * Checker_env.t =
  let f (decls_typed, env) decl =
    let decl_typed, env = type_declaration env ctx decl in
    decls_typed @ [decl_typed], env
  in
  let decls, env = List.fold_left ~f ~init:([], env) decls in
  decls, env

(* Entry point function for type checker *)
let check_program renamer (program:Types.program) : Checker_env.t * Prog.program =
  let Program top_decls = program in
  let initial_env = Checker_env.empty_with_renamer renamer in
  let prog, env = type_declarations initial_env DeclCxTopLevel top_decls in
  env, prog
