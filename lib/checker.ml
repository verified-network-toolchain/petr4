open Surface
open Poulet4.Typed
open Poulet4.Syntax
open P4light
open Util

(* hack *)
module Petr4Error = Error
open Core
open Petr4Error
module Error = Petr4Error
let (=) = Stdlib.(=)
let (<>) = Stdlib.(<>)

let is_default (lbl: Surface.Statement.switch_label) =
  match lbl with
  | Default _ -> true
  | _ -> false

let make_assert expected unwrap = fun tags typ ->
  match unwrap typ with
  | Some v -> v
  | None -> raise_mismatch tags expected typ

let binop_to_coq_binop (n: Op.bin) : P4light.coq_OpBin =
  match n with
  | Op.Plus _ -> Plus
  | Op.PlusSat _ -> PlusSat
  | Op.Minus _ -> Minus
  | Op.MinusSat _ -> MinusSat
  | Op.Mul _ -> Mul
  | Op.Div _ -> Div
  | Op.Mod _ -> Mod
  | Op.Shl _ -> Shl
  | Op.Shr _ -> Shr
  | Op.Le _ -> Le
  | Op.Ge _ -> Ge
  | Op.Lt _ -> Lt
  | Op.Gt _ -> Gt
  | Op.Eq _ -> Eq
  | Op.NotEq _ -> NotEq
  | Op.BitAnd _ -> BitAnd
  | Op.BitXor _ -> BitXor
  | Op.BitOr _ -> BitOr
  | Op.PlusPlus _ -> PlusPlus
  | Op.And _ -> And
  | Op.Or _ -> Or

let uop_to_coq_uop (n: _ Op.puni) : P4light.coq_OpUni =
  match n with
  | Op.Not _ -> Not
  | Op.BitNot _ -> BitNot
  | Op.UMinus _ -> UMinus

let info_of_expr (MkExpression (info, _, _, _): P4light.coq_Expression) = info

let preexpr_of_expr (MkExpression (_, exp, _, _): P4light.coq_Expression) = exp

let type_of_expr (MkExpression (_, _, typ, _): P4light.coq_Expression) = typ

let dir_of_expr (MkExpression (_, _, _, dir): P4light.coq_Expression) = dir

let info_of_stmt (MkStatement (info, _, _): P4light.coq_Statement) = info

let prestmt_of_stmt (MkStatement (_, stmt, _): P4light.coq_Statement) = stmt

let type_of_stmt (MkStatement (_, _, typ): P4light.coq_Statement) = typ

let opt_of_param (MkParameter (opt, _, _, _, _): P4light.coq_P4Parameter) = opt

let dir_of_param (MkParameter (_, dir, _, _, _): P4light.coq_P4Parameter) = dir

let type_of_param (MkParameter (_, _, typ, _, _): P4light.coq_P4Parameter) = typ

let default_arg_id_of_param (MkParameter (_, _, _, default_arg, _): P4light.coq_P4Parameter) = default_arg

let var_of_param (MkParameter (_, _, _, _, var): P4light.coq_P4Parameter) = var

let has_default_arg p =
  default_arg_id_of_param p <> None

let find_default_arg env (MkParameter (_, _, _, arg_id, _): P4light.coq_P4Parameter) =
  match arg_id with
  | Some arg_id -> Checker_env.find_default_arg (Bigint.to_int_exn arg_id) env |> Some
  | None -> None

let is_optional (param: Surface.Parameter.t) =
  let f (a: Surface.Annotation.t) =
    match a.body with
    | Empty _ -> String.equal a.name.str "optional"
    | _ -> false
  in
  List.exists ~f param.annotations

let params_of_fn_type (MkFunctionType (_, parameters, _, _)) = parameters

let assert_array = make_assert "array"
    begin function
      | TypArray (typ, size) -> Some (typ, size)
      | _ -> None
    end

let assert_bool = make_assert "bool"
    begin function
      | TypBool -> Some TypBool
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

let field_cmp (f1: coq_FieldType) (f2: coq_FieldType) : int =
  String.compare (fst f1).str (fst f2).str

let sort_fields = List.sort ~compare:field_cmp

let add_cast_unsafe (expr: P4light.coq_Expression) new_typ : P4light.coq_Expression =
  MkExpression (P4info.dummy, ExpCast (new_typ, expr), new_typ, dir_of_expr expr)

let rec val_to_literal (v: P4light.coq_Value) : P4light.coq_Expression =
  let fs_to_literals fs: P4light.coq_Expression * (P4string.t * coq_P4Type) list =
     let names = List.map ~f:fst fs in
     let vs = List.map ~f:snd fs in
     let es = List.map ~f:val_to_literal vs in
     let typs = List.map ~f:type_of_expr es in
     (MkExpression (P4info.dummy, ExpList es, TypList typs, In), List.zip_exn names typs)
  in
  match v with
  | ValBool b ->
     MkExpression (P4info.dummy, ExpBool b, TypBool, In)
  | ValInteger v ->
     let i: P4int.t = {tags = P4info.dummy; value = v; width_signed = None } in
     MkExpression (P4info.dummy, ExpInt i, TypInteger, In)
  | ValBit (width, v) ->
     let width = Bigint.of_int width in
     let i: P4int.t = {tags = P4info.dummy; value = v; width_signed = Some (width, false) } in
     MkExpression (P4info.dummy, ExpInt i, TypBit width, In)
  | ValInt (width, v) ->
     let width = Bigint.of_int width in
     let i: P4int.t = {tags = P4info.dummy; value = v; width_signed = Some (width, true) } in
     MkExpression (P4info.dummy, ExpInt i, TypInt width, In)
  | ValString s ->
     MkExpression (P4info.dummy, ExpString s, TypString, In)
  | ValTuple vs ->
     let es = List.map ~f:val_to_literal vs in
     let typs = List.map ~f:type_of_expr es in
     MkExpression (P4info.dummy, ExpList es, TypTuple typs, In)
  | ValRecord fs ->
     let e, t = fs_to_literals fs in
     add_cast_unsafe e (TypRecord t)
  | ValError e ->
     MkExpression (P4info.dummy, ExpErrorMember e, TypError, In)
  | ValMatchKind mk ->
     MkExpression (P4info.dummy, ExpTypeMember ({str="match_kind"; tags=P4info.dummy}, mk), TypMatchKind, In)
  | ValStruct fs ->
     let e, t = fs_to_literals fs in
     add_cast_unsafe e (TypStruct t)
  | ValHeader (fs, valid) ->
     if not valid then failwith "invalid header at compile time";
     let e, t = fs_to_literals fs in
     add_cast_unsafe e (TypHeader t)
  | ValEnumField (typ, mem)
  | ValSenumField (typ, mem, _) ->
     MkExpression (P4info.dummy, ExpTypeMember (typ, mem), TypTypeName typ, In)
  | ValSenum vs -> failwith "ValSenum unsupported"

let assert_runtime_numeric = make_assert "bit<> or int<>"
  begin function
  | TypInt typ
  | TypBit typ -> Some typ
  | _ -> None
  end


(* Checks if [t] is a specific p4 type as satisfied by [f] under [env] *)
let rec is_extern (env: Checker_env.t) (typ: P4light.coq_P4Type) =
  match typ with
  | TypExtern _ -> true
  | TypTypeName n ->
    begin match Checker_env.resolve_type_name (BareName n) env with
      | TypTypeName n' ->
        if P4string.eq n n'
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

let rec min_size_in_bits' env (info: P4info.t) (hdr_type: coq_P4Type) : int =
  match saturate_type env hdr_type with
  | TypBit width | TypInt width ->
    Bigint.to_int_exn width
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

and field_width_bits env info ((_, typ): coq_FieldType) : int =
  min_size_in_bits' env info typ

and min_size_in_bits env (info: P4info.t) (hdr_type: coq_P4Type) : Bigint.t =
  Bigint.of_int (min_size_in_bits' env info hdr_type)

and min_size_in_bytes env tags hdr_type =
  let bits = min_size_in_bits' env tags hdr_type in
  Bigint.of_int ((bits + 7) asr 3)

(* Evaluate the expression [expr] at compile time. Make sure to
 * typecheck the expression before trying to evaluate it! *)
and compile_time_eval_expr (env: Checker_env.t) (expr: P4light.coq_Expression) : P4light.coq_Value option =
  let MkExpression (tags, expr, typ, dir) = expr in
  match expr with
  | ExpName (name, _) ->
    Checker_env.find_const_opt name env
  | ExpBool b -> Some (ValBool b)
  | ExpString str -> Some (ValString str)
  | ExpInt i ->
    begin match i.width_signed with
      | None ->
        Some (ValInteger i.value)
      | Some (width, signed) ->
        if signed
        then Some (Bitstring.int_of_rawint i.value (Bigint.to_int_exn width))
        else Some (Bitstring.bit_of_rawint i.value (Bigint.to_int_exn width))
    end
  | ExpUnaryOp (op, arg) ->
    begin match compile_time_eval_expr env arg with
      | Some arg ->
        Some (Ops.interp_unary_op op arg)
      | None -> None
    end
  | ExpBinaryOp (op, l, r) ->
    begin match compile_time_eval_expr env l,
                compile_time_eval_expr env r with
    | Some l, Some r ->
      Some (Ops.interp_binary_op op l r)
    | _ -> None
    end
  | ExpCast (typ, expr) ->
    let expr_val = compile_time_eval_expr env expr in
    let type_lookup name = Checker_env.resolve_type_name (BareName name) env in
    option_map (Ops.interp_cast ~type_lookup typ) expr_val
  | ExpList values ->
    begin match compile_time_eval_exprs env values with
      | Some vals -> Some (ValTuple vals)
      | None -> None
    end
  | ExpTypeMember (typ, name) ->
    let real_name = real_name_for_type_member env (BareName typ) name in
    Checker_env.find_const_opt real_name env
  | ExpErrorMember t ->
    Some (ValError t)
  | ExpRecord entries ->
    let opt_entries =
      List.map ~f:(fun (key, value) ->
          match compile_time_eval_expr env value with
          | Some v -> Some (key, v)
          | None -> None)
        entries
    in
    begin match Util.list_option_flip opt_entries with
      | Some es -> Some (ValRecord es)
      | None -> None
    end
  | ExpBitStringAccess (bits, hi, lo) ->
    begin match compile_time_eval_expr env bits with
      | Some (ValInt (w, v))
      | Some (ValBit (w, v)) ->
        let slice_val = Bitstring.bitstring_slice v hi lo in
        Some (ValBit (Bigint.(to_int_exn (max (hi - lo) zero)), slice_val))
      | _ -> None
    end
  | ExpDontCare -> failwith "set expression in non-set context"
  | ExpExpressionMember (expr, {str="size";_}) ->
    begin match saturate_type env (type_of_expr expr) with
      | TypArray (_, size) -> Some (ValInteger size)
      | _ -> None
    end
  | ExpExpressionMember (expr, name) ->
    begin match compile_time_eval_expr env expr with
      | Some (ValStruct fields) ->
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
        Some (ValInteger size)
      | ExpExpressionMember (expr, {str="minSizeInBytes"; _}) ->
        let MkExpression (i, expr, typ, _) = expr in
        let typ = saturate_type env typ in
        let size = min_size_in_bytes env i typ in
        Some (ValInteger size)
      | _ -> None
    end
  | _ ->
    None

and compile_time_eval_exprs env exprs : P4light.coq_Value list option =
  let options = List.map ~f:(compile_time_eval_expr env) exprs in
  Util.list_option_flip options

and bigint_of_value (v: P4light.coq_Value) =
  match v with
  | ValInt (_, v)
  | ValBit (_, v)
  | ValInteger v ->
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
and compile_time_eval_decl (env: Checker_env.t) (decl: P4light.coq_Declaration) : Checker_env.t =
  match decl with
  | DeclConstant (_, _, name, exp) ->
     begin match compile_time_eval_expr env exp with
     | Some value ->
        Checker_env.insert_const (BareName name) value env
     | None -> env
     end
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
  let saturate_field env (name, typ) =
    (name, saturate_type env typ)
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
    let env = Checker_env.insert_type_vars ~shadow:true type_params env in
    MkControlType (type_params, List.map ~f:(saturate_param env) params)
  in
  let saturate_function env (MkFunctionType (type_params, params, kind, ret)) =
    let env = Checker_env.insert_type_vars ~shadow:true type_params env in
    MkFunctionType (type_params,
                    saturate_params env params,
                    kind,
                    saturate_type env ret)
  in
  match typ with
  | TypTypeName t ->
    begin match Checker_env.resolve_type_name_opt (BareName t) env with
      | None -> typ
      | Some (TypTypeName t') ->
        if P4string.eq t' t
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
    let env = Checker_env.insert_type_vars ~shadow:true type_params env in
    let env = Checker_env.insert_type_vars ~shadow:true wildcard_params env in
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
    let env = Checker_env.insert_type_vars ~shadow:true type_params env in
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

(* removes all the enums recursively after reducing a type. *)
and reduce_enums_in_type (env: Checker_env.t) (typ: coq_P4Type) : coq_P4Type =
  let typ = reduce_type env typ in
  match typ with
  | TypEnum (_, Some typ, _) -> reduce_enums_in_type env typ
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

and constraints_to_type_args (cs: var_constraints) : (P4string.t * coq_P4Type) list =
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
      | None -> failwith "Could not solve type equality."
                                  (*~param:(param_type: coq_P4Type) ~arg_typ:(expr_typ: coq_P4Type)]*)
    end
  | (param_type, None) :: more ->
    gen_all_constraints env ctx unknowns more constraints
  | [] ->
    constraints

and infer_type_arguments env ctx type_params_args params_args =
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
  params_args' @ constraints_to_type_args constraints

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


and solve_record_type_equality env equiv_vars unknowns (rec1: coq_FieldType list) (rec2: coq_FieldType list) =
  let solve_fields ((name1, type1), (name2, type2)) =
    if P4string.eq name1 name2
    then solve_types env equiv_vars unknowns type1 type2
    else None
  in
  let fields1 = sort_fields rec1 in
  let fields2 = sort_fields rec2 in
  solve_lists env unknowns fields1 fields2 ~f:solve_fields

and solve_params_equality env equiv_vars unknowns ps1 ps2 =
  let param_eq (p1, p2) =
    match p1, p2 with
    | Some (MkParameter (opt1, dir1, typ1, _, var1)),
      Some (MkParameter (opt2, dir2, typ2, _, var2)) ->
        if eq_dir dir1 dir2
        then solve_types env equiv_vars unknowns typ1 typ2 
        else None
    | Some (MkParameter (opt, dir, typ, _, var)), None
    | None, Some (MkParameter (opt, dir, typ, _, var)) ->
        if opt
        then Some (empty_constraints unknowns)
        else None
    | None, None -> failwith "BUG: only one parameter can be None."
  in
  let add_opt ps = List.map ~f:(fun p -> Some p) ps in
  let ps1_len = List.length ps1 in
  let ps2_len = List.length ps2 in
  let ps1', ps2' = 
    if ps1_len < ps2_len
    then (add_opt ps1) @ (List.init (ps2_len - ps1_len) ~f:(fun _ -> None)), add_opt ps2
    else add_opt ps1, (add_opt ps2) @ (List.init (ps1_len - ps2_len) ~f:(fun _ -> None))
  in
    solve_lists env unknowns ~f:param_eq ps1' ps2'

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
    | TypSpecializedType (TypExtern e1, args1),
      TypSpecializedType (TypExtern e2, args2) ->
      let ok (t1, t2) = solve_types env equiv_vars unknowns t1 t2 in
      if P4string.eq e1 e2
      then solve_lists env unknowns ~f:ok args1 args2
      else None
    | TypSpecializedType (base, args), _
    | _, TypSpecializedType (base, args) ->
       failwith "Stuck specialized type." (*~t:(TypSpecializedType (base, args):coq_P4Type)]*)
    | TypTypeName ( tv1), TypTypeName ( tv2) ->
      if type_vars_equal_under equiv_vars tv1 tv2
      then Some (empty_constraints unknowns)
      else if List.mem ~equal:P4string.eq unknowns tv1
      then Some (single_constraint unknowns tv1 t2)
      else None
    | TypTypeName ( tv), typ ->
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
  let entry_cmp (e1: KeyValue.t) (e2: KeyValue.t) =
    String.compare e1.key.str e2.key.str
  in
  List.sort ~compare:entry_cmp entries

(* [type_equality env t1 t2] is true if and only if expression type t1
 * is equivalent to expression type t2 under environment env.
 *  Alpha equivalent types are equal. *)
and type_equality env equiv_vars t1 t2 : bool =
  solve_types ~casts:false env equiv_vars [] t1 t2 <> None

and assert_same_type (env: Checker_env.t) tags1 tags2 (typ1: coq_P4Type) (typ2: coq_P4Type) =
  if type_equality env [] typ1 typ2
  then (typ1, typ2)
  else let tags = P4info.merge tags1 tags2 in
    raise_type_error tags (Type_Difference (typ1, typ2))

and assert_type_equality env tags (t1: coq_P4Type) (t2: coq_P4Type) : unit =
  let t1 = reduce_type env t1 in
  let t2 = reduce_type env t2 in
  if type_equality env [] t1 t2
  then ()
  else raise @@ Error.Type (tags, Type_Difference (t1, t2))

(* determinez if the value of an expression can be known at compile time.
   it returns true for externs, packages, controls, and parsers.*)
and compile_time_known_expr (env: Checker_env.t) (expr: P4light.coq_Expression) : bool =
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

(*
  judgment rule is as follows. it type check exp under environment e and context c.
  it also infers type as well as doing a pass from types to prog. 

   e, c |- exp ~~> prog_exp

   Note: prog_exp is a record with three fields: expr, typ, dir.
   For simplicity, I omitted the name of the fields but the order is kept.
   Also, for simplicity, I omitted tags.
   Data constructors start with a capital letter.
   Where possible data constructors are omitted and instead the name of the
   expression implies the data constructor, e.g., str indicates an expression
   that is a string.

   e, c |- True {tags} ~~> {True {tags}; Bool; Directionless; tags}

*)

and type_expression
    (env: Checker_env.t)
    (ctx: P4light.coq_ExprContext)
    (exp: Expression.t)
  : P4light.coq_Expression =
  match exp with
  | True {tags} ->
    MkExpression (tags, ExpBool true, TypBool, Directionless)
  | False {tags} ->
    MkExpression (tags, ExpBool false, TypBool, Directionless)
  | String {tags; str} ->
    MkExpression (tags, ExpString str, TypString, Directionless)
  | Int {tags; x}->
    type_int x
  | Name {tags; name} ->
    let typ, dir = Checker_env.find_type_of name env in
    MkExpression (tags, ExpName (name, P4light.noLocator), typ, dir)
  | ArrayAccess { array; index; tags } ->
    type_array_access env ctx tags array index
  | BitStringAccess { bits; lo; hi ; tags} ->
    type_bit_string_access env ctx tags bits lo hi
  | List { values; tags } ->
    type_list env ctx tags values
  | Record { entries; tags } ->
    type_record env ctx tags entries
  | UnaryOp { op; arg; tags } ->
    type_unary_op env ctx tags op arg
  | BinaryOp { op; args; tags } ->
    type_binary_op env ctx tags op args
  | Cast { typ; expr; tags } ->
    type_cast env ctx tags typ expr
  | TypeMember { typ; name; tags } ->
    type_type_member env ctx tags typ name
  | ErrorMember {tags; err} ->
    type_error_member env ctx tags err
  | ExpressionMember { expr; name; tags } ->
    type_expression_member env ctx tags expr name
  | Ternary { cond; tru; fls; tags } ->
    type_ternary env ctx tags cond tru fls
  | FunctionCall { func; type_args; args; tags } ->
    type_function_call env ctx tags func type_args args
  | NamelessInstantiation { typ; args; tags } ->
    type_nameless_instantiation env ctx tags typ args
  | Mask { expr; mask; tags } ->
    failwith "mask outside of set context"
  | Range { lo; hi; tags } ->
    failwith "range outside of set context"

and add_cast env (expr: coq_Expression) new_typ =
  let orig_typ = type_of_expr expr in
  if cast_ok env orig_typ new_typ
  then add_cast_unsafe expr new_typ
  else begin
    Printf.printf "Cannot cast\n%!";
    Printp4.print_expr Format.str_formatter expr;
    Printf.printf "to type\n%!";
    Printp4.print_type Format.std_formatter new_typ;
    failwith "Typecast error"
  end

and cast_if_needed env (expr: P4light.coq_Expression) typ : P4light.coq_Expression =
  let MkExpression (info, pre_expr, expr_typ, dir) = expr in
  if type_equality env [] expr_typ typ
  then expr
  else match typ with
    | TypSet elt_typ -> add_cast env (cast_if_needed env expr elt_typ) typ
    | typ -> add_cast env expr typ

and cast_to_same_type (env: Checker_env.t) (ctx: P4light.coq_ExprContext) (exp1: Expression.t) (exp2: Expression.t) =
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

(* takes a type and surface syntax expression. after generating the IR expression by type_expression, it checks if the given type and type of IR expression are equal it just returns the IR exp o.w. it casts (if possible) the IR expression to the given type.  NOTE: it already know the cast, if needed, is valid. *)
and cast_expression (env: Checker_env.t) ctx (typ: coq_P4Type) (exp: Expression.t) =
  let typ = reduce_type env typ in
  match exp with
  | String {tags; _}
  | Cast {tags; _} ->
     let exp_typed = type_expression env ctx exp in
     assert_type_equality env tags typ (type_of_expr exp_typed);
     exp_typed
  | True _
  | False _
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
  | BinaryOp {op = Op.Shl _; args = _; tags = _}
  | BinaryOp {op = Op.Shr _; args = _; tags = _}
  | BinaryOp {op = Op.PlusPlus _; args = _; tags = _} ->
     let exp_typed = type_expression env ctx exp in
     cast_if_needed env exp_typed typ
  | List { values; tags } ->
     let rec get_types (typ: coq_P4Type) =
       match typ with
       | TypTuple types
       | TypList types ->
          types
       | TypHeader fields
       | TypStruct fields ->
          List.map ~f:snd fields
       | TypSet t ->
          get_types t
       | _ -> [typ]
     in
     let types = get_types typ in
     let values_casted =
       List.zip_exn types values
       |> List.map ~f:(fun (t, v) -> cast_expression env ctx t v)
     in
     let exp_typed: coq_Expression =
       MkExpression (tags,
                     ExpList (values_casted),
                     TypList types,
                     Directionless)
     in
     cast_if_needed env exp_typed typ
  | Record { entries; tags } ->
     let entries = sort_entries entries in
     let fields =
       match typ with
       | TypRecord fields
       | TypHeader fields
       | TypStruct fields ->
         sort_fields fields
       | _ -> failwith "can't cast record"
     in
     let cast_entry (field, entry: coq_FieldType * KeyValue.t) =
       if (fst field).str <> entry.key.str
       then failwith "bad names";
       let value_typed: coq_Expression =
         cast_expression env ctx (snd field) entry.value
       in
       (entry.key, value_typed)
     in
     let entries_casted =
       List.zip_exn fields entries
       |> List.map ~f:cast_entry
     in
     let exp_typed: coq_Expression =
       MkExpression (tags,
                     ExpRecord entries_casted,
                     TypRecord fields,
                     Directionless)
     in
     cast_if_needed env exp_typed typ
  | BinaryOp {op = Op.Eq _ as op; args = (left, right); tags}
  | BinaryOp {op = Op.NotEq _  as op; args = (left, right); tags}
  | BinaryOp {op = Op.Lt _ as op; args = (left, right); tags}
  | BinaryOp {op = Op.Le _ as op; args = (left, right); tags}
  | BinaryOp {op = Op.Gt _ as op; args = (left, right); tags}
  | BinaryOp {op = Op.Ge _ as op; args = (left, right); tags} ->
     let left_typed, right_typed = cast_to_same_type env ctx left right in
     let exp_typed = check_binary_op env tags op left_typed right_typed in
     cast_if_needed env exp_typed typ
  | BinaryOp {op = Op.Div _ as op; args = (left, right); tags}
  | BinaryOp {op = Op.Mod _ as op; args = (left, right); tags} ->
     let exp_typed = type_binary_op env ctx tags op (left, right) in
     cast_if_needed env exp_typed typ
  | BinaryOp {op; args = (left, right); tags} ->
     let left_typed = cast_expression env ctx typ left in
     let is_shr op =
       match op with
       | Op.Shr {tags} -> true
       | _ -> false
     in
     let is_shl op =
       match op with
       | Op.Shl {tags} -> true
       | _ -> false
     in
     let right_typed =
       if not (is_shr op) && not (is_shl op)
       then cast_expression env ctx typ right
       else type_expression env ctx right
     in check_binary_op env tags op left_typed right_typed
  | Ternary { cond; tru; fls; tags } ->
     let cond_typed = cast_expression env ctx TypBool cond in
     let tru_typed = cast_expression env ctx typ tru in
     let fls_typed = cast_expression env ctx typ fls in
     MkExpression (tags,
                   ExpTernary (cond_typed, tru_typed, fls_typed),
                   typ,
                   Directionless)
  | Mask { expr; mask; tags } ->
     failwith "mask casts unimplemented"
  | Range { lo; hi; tags } ->
     failwith "range casts unimplemented"

and translate_direction (dir: Surface.Direction.t option) : P4light.direction =
  match dir with
  | Some (In _) -> In
  | Some (Out _) -> Out
  | Some (InOut _) -> InOut
  | None -> Directionless

and eval_to_positive_int env tags expr =
  let value =
    expr
    |> type_expression env ExprCxConstant
    |> compile_time_eval_bigint env
  in
  if Bigint.(value > zero)
  then value
  else failwith "expected positive integer" (*~info:(info: P4info.t)]*)

and eval_to_nonneg_int env tags expr =
  let value =
    expr
    |> type_expression env ExprCxConstant
    |> compile_time_eval_bigint env
  in
  if Bigint.(value >= zero)
  then value
  else failwith "expected non-negative integer" (*~info:(info: P4info.t)]*)


and gen_wildcard env: P4string.t =
  let str = Renamer.freshen_name (Checker_env.renamer env) "__wild" in
  {tags = P4info.dummy; str}

(* It translates types.type.t to typed.type.t

   It also returns the list of variable names generated.
*)
and translate_type' ?(gen_wildcards=false) (env: Checker_env.t) (typ: Surface.Type.t) : coq_P4Type * P4string.t list =
  let open Surface.Type in
  let ret (t: coq_P4Type) = t, [] in
  match typ with
  | Bool _ -> ret TypBool
  | Error _ -> ret TypError
  | Integer _ -> ret TypInteger
  | String _ -> ret TypString
  | IntType {tags; expr} -> ret @@ TypInt (eval_to_positive_int env tags expr)
  | BitType {tags; expr} -> ret @@ TypBit (eval_to_nonneg_int env tags expr)
  | VarBit {tags; expr} -> ret @@ TypVarBit (eval_to_nonneg_int env tags expr)
  | TypeName {name = nm; _} ->
    ret @@ TypTypeName (P4name.p4string_name_only nm)
  | SpecializedType {base; args; tags} ->
     let args, wildcards =
       args
       |> List.map ~f:(translate_type' ~gen_wildcards env )
       |> List.unzip
     in
     (TypSpecializedType (translate_type env base, args),
      List.concat wildcards)
  | HeaderStack {header=ht; size=e; tags} ->
     let hdt = translate_type env ht in
     let len =
       e
       |> type_expression env ExprCxConstant
       |> compile_time_eval_bigint env
       |> Bigint.to_int_exn in
     ret @@ TypArray (hdt, Bigint.of_int len)
  | Tuple {tags; xs} ->
     ret @@ TypTuple (List.map ~f:(translate_type env) xs)
  | Void _ -> ret TypVoid
  | DontCare {tags} ->
    if gen_wildcards
    then let name = gen_wildcard env in
         TypTypeName (name), [name]
    else failwith "not generating wildcards" (*~info:(fst typ: P4info.t)] *)

and translate_type (env: Checker_env.t) (typ: Surface.Type.t) : coq_P4Type =
  fst (translate_type' env typ)

and translate_type_opt (env: Checker_env.t) (typ: Surface.Type.t) : coq_P4Type option =
  match typ with
  | DontCare _ -> None
  | _ -> Some (translate_type env typ)

and hash_default_arg env (arg: Surface.Expression.t option): int option =
  match arg with
  | Some exp -> Some (Checker_env.add_default_arg exp env)
  | None -> None

(* Translates Surface.Parameters to P4light.Parameters *)
and translate_parameters env params =
  let translate_parameter (param : Surface.Parameter.t) =
    let default_arg_id = hash_default_arg env param.opt_value in
    MkParameter (is_optional param,
                 translate_direction param.direction,
                 translate_type env param.typ,
                 option_map Bigint.of_int default_arg_id,
                 param.variable)
  in
  List.map ~f:translate_parameter params

and expr_of_arg (arg: Argument.t): Expression.t option =
  match arg with
  | Missing _ -> None
  | KeyValue { value; _ }
  | Expression { value; _ } -> Some value

(*
   has the judgment (stating that the type t is well-formed under environment e)
   e |- t

   e |- Bool

   e |- String

   e |- Integer

   e |- Int<n>

   e |- Bit<n>

   e |- VarBit<n>

   e |- Error

   e |- MatchKind

   e |- Void

* Array type:
   e |- t
   isValidNested (t[n],t)
   ----------------------------------
   e |- t[n]

* Tuple type:
   1 <= i <= n; e |- ti
   1 <= i <= n; is_valid_nested_type(<t1,...,tn>, ti)_e
   ----------------------------------
   e |- tuple <t1, ..., tn>

* List type
   1 <= i <= n; e |- ti
   1 <= i <= n; is_valid_nested_type([t1,...,tn], ti)_e
   ----------------------------------
   e |- [t1, ..., tn]

* Set type:
   e |- t
   ----------------------------------
   e |- set<t>

* Enum type:
   ** the case where typ is Some typ.
   * X is the name of the enum.
   * li is the name of the field.

   e |- t
   -----------------------------------
   e |- enum t X {l1, ..., ln}

   ** the case where type is None.

   e |- enum X {l1, ..., ln}

* Record and struct and header union ({l1:h1, ..., ln:hn}) type:
   1 <= i <= n; e |- ti
   1 <= i <= n; is_valid_nested_type(record {f1 : t1, ..., fn : tn}, ti)_e
   1 <= i < j <= n; fi != fj
   ------------------------------------
   e |- record {f1 : t1, ..., fn : tn}

* header: 
   1 <= i <= n; e |- ti
   1 <= i <= n; is_valid_nested_type(header {f1 : t1, ..., fn : tn}, ti)_e
   1 <= i < j <= n; fi != fj
   ------------------------------------
   e |- header {l1 : t1, ..., ln : tn}

* new type (name = typ):
   e |- t
   ----------------------------------
   e |- type t n 

* specialized type:
   look at spec

* package type:
   look at spec

* control type:
   look at spec

* parser type:
   look at spec

* extern type:
   look at spec

* function type (<return type> <function name> (x1, ..., xn) {...}):
   look at spec

* action type:
   look at spec

* constructor type:
   look at spec

* table type:
   look at spec

* type name:
   look at spec
*)
(* Returns true if type typ is a well-formed type *)
and is_well_formed_type env (typ: coq_P4Type) : bool =
  match saturate_type env typ with
  (* Base types *)
  | TypBit w
  | TypVarBit w ->
    Bigint.(w >= zero)
  | TypInt w ->
    Bigint.(w > zero)
  | TypBool
  | TypString
  | TypInteger
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
    let field_ok ((_, field_typ): coq_FieldType) =
      is_well_formed_type env field_typ &&
      is_valid_nested_type env typ field_typ
    in
    List.for_all ~f:field_ok fields &&
      not (List.contains_dup ~compare:field_cmp fields)
  | TypHeader fields ->
    let field_ok ((_, field_typ): coq_FieldType) =
      is_well_formed_type env field_typ &&
      is_valid_nested_type ~in_header:true env typ field_typ
    in
    List.for_all ~f:field_ok fields &&
      not (List.contains_dup ~compare:field_cmp fields)
  | TypAction (data_params, ctrl_params) ->
    are_param_types_well_formed env data_params &&
    are_construct_params_types_well_formed env ctrl_params
  (* Type names *)
  | TypTypeName name ->
    Checker_env.resolve_type_name_opt (BareName name) env <> None
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
  (* TODO: discuss! according to p4 spec parser, control, and package
     cannot be type args to methods, parsers, controls, tables, and
     actions.  but we're not checking this.*)
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

and ctx_of_kind (k: coq_FunctionKind) : P4light.coq_ParamContext =
  match k with
  | FunParser -> ParamCxRuntime ParamCxDeclParser
  | FunControl -> ParamCxRuntime ParamCxDeclControl
  | FunExtern -> ParamCxRuntime ParamCxDeclMethod
  | FunTable -> ParamCxRuntime ParamCxDeclControl
  | FunAction -> ParamCxRuntime ParamCxDeclAction
  | FunFunction -> ParamCxRuntime ParamCxDeclFunction
  | FunBuiltin -> ParamCxRuntime ParamCxDeclMethod

and is_valid_param_type env (ctx: P4light.coq_ParamContext) (typ: coq_P4Type) =
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

(*  TODO: discuss with Ryan. doesn't match p4 spec for outer header.
          also, role of in_header. *)
and is_valid_nested_type ?(in_header=false) (env: Checker_env.t) (outer_type: coq_P4Type) (inner_type: coq_P4Type) =
  let inner_type = reduce_to_underlying_type env inner_type in
  let field_ok ((_, typ)) =
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
  then failwith "Parameter type is not well-formed."; (*~typ:(typ:coq_P4Type)];*)
  if not @@ is_valid_param_type env ctx typ
  then failwith "Type cannot be passed as a parameter."; (* ~typ:(typ:coq_P4Type) ~info:(info:P4info.t)];*)
  if opt_value <> None && not (eq_dir dir Directionless) && not (eq_dir dir In)
  then failwith "Only directionless and in parameters may have default arguments" (*~info:(info:P4info.t)]*)

and type_param ?(gen_wildcards=false) env (ctx: P4light.coq_ParamContext) (param : Surface.Parameter.t) : coq_P4Parameter * P4string.t list =
  let typ, wildcards = translate_type' ~gen_wildcards env param.typ in
  let env = Checker_env.insert_type_vars wildcards env in
  let dir = translate_direction param.direction in
  let opt_arg_id = hash_default_arg env param.opt_value in
  validate_param env ctx typ dir param.tags opt_arg_id;
  MkParameter (is_optional param,
               translate_direction param.direction,
               typ,
               option_map Bigint.of_int opt_arg_id,
               param.variable),
  wildcards

and type_params' ?(gen_wildcards=false) env ctx params : coq_P4Parameter list * P4string.t list =
  let params, wildcard_lists =
    params
    |> List.map ~f:(type_param ~gen_wildcards env ctx)
    |> List.unzip
  in
  params, List.concat wildcard_lists

and type_params env ctx param : coq_P4Parameter list =
  fst (type_params' env ctx param)

and type_constructor_param env decl_kind (param: Surface.Parameter.t) : coq_P4Parameter * P4string.t list =
  if param.direction <> None
  then failwith "Constructor parameters must be directionless";
         (*~param:(param: Surface.Parameter.t)];*)
  type_param env ~gen_wildcards:true (ParamCxConstructor decl_kind) param

and type_constructor_params env decl_kind params =
  let params, wildcard_lists =
    params
    |> List.map ~f:(type_constructor_param env decl_kind)
    |> List.unzip
  in
  params, List.concat wildcard_lists

(* e, c, {value; Some (width, True)} |- {value; Bit {width}; Directionless} *)
(* e, c, {value; Some (width, False)} |- {value; Int {width}; Directionless} *)
(* e, c, {value; None} |- {value; Integer; Directionless} *)
and type_int (int: P4int.t) : coq_Expression =
  let typ = 
    match int.width_signed with
    | None -> TypInteger
    | Some (width, true) -> TypInt width
    | Some (width, false) -> TypBit width
  in
  MkExpression (int.tags, ExpInt int, typ, Directionless)

(* Section 8.15
 * ------------
 *
 * Δ, T, Γ |- a : t[size]      Δ, T, Γ |- i : u, where numeric(u)
 * ----------------------------------------------------------
 *                Δ, T, Γ |- a[i] : t
 *
 * Some architectures may further require ctk(i).

   e, c, a |- {a', t[size], d}            e, c, i |- {i', t', d'}
     is_array(t[size])                         is_numeric(t')
   ------------------------------------------------------------
   e, c, a[i] |- {a'[i'], t, d}

 *)
and type_array_access env ctx tags (array: Surface.Expression.t) index
  : coq_Expression =
  let (MkExpression (array_tags, _, array_typ, array_dir) as array_typed) =
    type_expression env ctx array
  in
  let (MkExpression (_, _, idx_typ, _) as idx_typed) =
    type_expression env ctx index
  in
  let element_typ = assert_array (Expression.tags array) array_typ |> fst in
  assert_numeric (Expression.tags index) idx_typ |> ignore;
  MkExpression (array_tags,
                ExpArrayAccess (array_typed, idx_typed),
                element_typ,
                array_dir)

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



   e, Constant |- h ~~> {h', t'', d''}
   is_numeric(t'')
   h'' = [[h']]_e
   e, Constant |- l ~~> {l', t', d'}
   is_nuimeric(t')
   l'' = [[l]]_e
   0 <= l'' < w
   l'' <= h'' < w
   e, c | b ~~> {b', t, d}
   t ?= Int{w} or t ?= Bit{w}
   --------------------------------
   e, c |- b[l:h] ~~> {b[l'':h''], Bit{h''-l''}, d}


 *)
and type_bit_string_access env ctx tags bits lo hi : coq_Expression =
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
    (* Bounds checking *)
    assert (Bigint.(<=) Bigint.zero val_lo);
    assert (Bigint.(<) val_lo width);
    assert (Bigint.(<=) val_lo val_hi);
    assert (Bigint.(<) val_hi width);
    let diff = Bigint.(-) val_hi val_lo |> Bigint.to_int_exn |> (+) 1 in
    MkExpression (tags,
                  ExpBitStringAccess (bits_typed, val_lo, val_hi),
                  TypBit (Bigint.of_int diff),
                  bits_dir)
  | typ ->
    failwith "Cannot bitslice this type."

(* Section 8.11
 * ------------
 *
 *      1 <= i <= n; Δ, T, Γ |- xi : ti
 * ------------------------------------------
 * Δ, T, Γ |- { x1, ..., xn } : (t1, ..., tn)
 *

   1 <= i <= n; e, c |- xi ~~> {xi', ti, di}
   --------------------------------------------------------------------
   e, c |- [x1, .., xn] ~~> {[x1', .., xn'], [t1, .. tn], Directionless}

 *)
and type_list env ctx tags values : coq_Expression =
  let typed_exprs = List.map ~f:(type_expression env ctx) values in
  let types = List.map ~f:type_of_expr typed_exprs in
  MkExpression (tags, ExpList typed_exprs, TypList types, Directionless)

and type_key_val env ctx ({tags; key; value}: Surface.KeyValue.t) =
  (key, type_expression env ctx value)

and type_record env ctx tags entries : coq_Expression =
  let entries_typed = List.map ~f:(type_key_val env ctx) entries in
  let rec_typed : P4light.coq_ExpressionPreT =
    ExpRecord entries_typed
  in
  let kv_to_field kv =
    let (key, value) = kv in
    (key, type_of_expr value)
  in
  let fields = List.map ~f:kv_to_field entries_typed in
  MkExpression (tags, rec_typed, TypRecord fields, Directionless)

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

   Logical negation:

   e, c |-  e ~~> {e', Bool, d}
   ---------------------------------
   e, c |- !e ~~> {!e', Bool, d}

   Bitwise complement:

   e, c |-  e ~~> {e', Bin<n>, d}
   ---------------------------------
   e, c |- ~e ~~> {~e', Bit<n>, d}

   Unary minus:

   e, c |-  e ~~> {e', Int, d}
   ---------------------------------
   e, c |- -e ~~> {-e', Int, d}

   e, c |-  e ~~> {e', Int<n>, d}
   ---------------------------------
   e, c |- -e ~~> {-e', Int<n>, d}

 *)
and type_unary_op env ctx tags (op: Op.uni) arg : coq_Expression =
  let arg_typed = type_expression env ctx arg in
  let MkExpression (_, _, arg_typ, arg_dir) = arg_typed in
  begin match op with
    | Not _    -> assert_bool (Expression.tags arg) arg_typ |> ignore
    | BitNot _ -> assert_runtime_numeric (Expression.tags arg) arg_typ |> ignore
    | UMinus _ -> assert_numeric (Expression.tags arg) arg_typ |> ignore
  end;
  MkExpression (tags, ExpUnaryOp (uop_to_coq_uop op, arg_typed), arg_typ, arg_dir)

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
 * Δ, T, Γ |- e1 eq_bop e2 : t
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

(*

   NOTE: implicit_cast(t1,t2)_e is defined above. Note that it casts args
         after saturating them, i.e., replacing all type references with
         the type they're refering to. int CTK is Integer.
   NOTE: cast(typ,expr) generataes a cast expr instead of expr in the triple
         of Prog.Expression, i.e., Cast {typ,expr}, typ, expr.dir.

* for binary ops except shifts and bit concatenation:   
   e, c |- l ~~> l', t', d'
   e, c |- r ~~> r', t'', d''
   t = implicit_cast(t',t'')_e
   l'' = cast(t, l'), t, d'
   r'' = cast(t, r'), t, d''
   --------------------------------------------------
   e, c |- l ?.? r ==> (l'', r'') 

* for shift ops and bit concatentation (>>, <<, ++):
   e, c |- l ~~> l', t', d'
   e, c |- r ~~> r', t'', d''
   --------------------------------------------------
   e, c |- l ?.? r ==> (l', t', d'; r', t'', d'') 
*)
and coerce_binary_op_args env ctx op l r =
  let l_typed = type_expression env ctx l in
  let r_typed = type_expression env ctx r in
  let cast typ (expr : P4light.coq_Expression) : P4light.coq_Expression =
    let MkExpression (expr_info, pre_expr, etyp, dir) = expr in 
    MkExpression (expr_info, ExpCast (typ, expr), typ, dir)
  in
  let cast_opt = function
    | Some typ -> cast typ
    | None -> fun e -> e
  in
  let cast_type_l, cast_type_r = implicit_cast env l_typed r_typed in
  let is_shl op =
    match op with
    | Op.Shl {tags} -> true
    | _ -> false
  in
  let is_shr op =
    match op with
    | Op.Shr {tags} -> true
    | _ -> false
  in
  let is_pluplus op =
    match op with
    | Op.PlusPlus {tags} -> true
    | _ -> false
  in
  if not (is_shl op) && not (is_shr op) && not (is_pluplus op)
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
  | TypStruct fields ->
    List.for_all fields
      ~f:(fun ((_, field_typ)) ->
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

and is_nonnegative_numeric env (e: P4light.coq_Expression) : bool =
  match type_of_expr e with
  | TypInteger ->
    let e_value = compile_time_eval_bigint env e in
    Bigint.(e_value >= zero)
  | TypBit _ -> true
  | _ -> false

and is_positive_numeric env (e: P4light.coq_Expression) : bool =
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

(*

   e, c |- l ?.? r ==> (l', r')
   e |- l' ?.? r' --> {l'' ?.? r'', t, d}
   ------------------------------------------------------
   e, c |- l ?.? r ~~> {l'' ?.? r'', t, d}
*)
and type_binary_op env ctx tags (op : Surface.Op.bin) (l, r) : coq_Expression =
  let typed_l, typed_r = coerce_binary_op_args env ctx op l r in
  check_binary_op env tags op typed_l typed_r


(*

   Note: in_or_dirless(typ1, typ2) retunrs direction of In if both typ1 and typ2
         have In direction, o.w., it returns a directionless direction. 

* logical ops: And (&), Or (|):

   lt = reduce_enums(l.t)_e
   rt = reduce_enums(r.t)_e
   d = in_or_dirless(lt, rt)
   lt ?= rt ?= Bool
   ----------------------------------------------
   e |- l & r --> {l & r, Bool, d}

* basic numeric ops: +, -, *:
   lt = reduce_enums(l.t)_e
   rt = reduce_enums(r.t)_e
   d = in_or_dirless(lt, rt)
        lt ?= rt ?= Bit<n>; t = Bit<n>
     or lt ?= rt ?= Integer; t = Integer
     or lt ?= rt ?= Int <n>; t = Int<n>
   --------------------------------------------
   e |- l + r --> {l + r, t, d}

* equality checks (==, !=):

   Note: typ1 ==e,c typ2 is type_equality.
         has_eq(typ)e is type_has_equality_tests.

   lt = reduce_enums(l.t)_e
   rt = reduce_enums(r.t)_e
   d = in_or_dirless(lt, rt)
   lt ==e,[] rt
   has_eq(lt)_e
   ---------------------------------------------
   e |- l == r --> l == r, Bool, d

* plusSat, MinusSat:
   lt = reduce_enums(l.t)_e
   rt = reduce_enums(r.t)_e
   d = in_or_dirless(lt, rt)
      lt ?= rt ?= Bit<n>; t = Bit<n>
   or lt ?= rt ?= Int<n>; t = Int<n>
   ---------------------------------------------
   e |- l |+| r --> l |+| r, t, d

* bitwise ops (&, |, X):
   lt = reduce_enums(l.t)_e
   rt = reduce_enums(r.t)_e
   d = in_or_dirless(lt, rt)
      lt ?= rt ?= Bit<n>; t = Bit<n>
   or lt ?= rt ?= Int<n>; t = Int<n>
   ---------------------------------------------
   e |- l & r --> l & r, t, d

* Bitstring concatenation (++):
   lt = reduce_enums(l.t)_e
   rt = reduce_enums(r.t)_e
   d = in_or_dirless(lt, rt)
      lt ?= Bit<n>, rt ?= Bit<m> or Int<m>; t = Bit<n+m>
   or lt ?= Int<n>, rt ?= Int<m> or Bit<m>; t = Int<n+m>
   ------------------------------------------------------
   e |- l ++ r --> l ++ r, t, d

* comparison ops (<, <=, >, >=):
   lt = reduce_enums(l.t)_e
   rt = reduce_enums(r.t)_e
   d = in_or_dirless(lt, rt)
      lt ?= rt ?= Integer
   or lt ?= rt ?= Bit<n>
   or lt ?= rt ?= Int<n>
   ---------------------------------------------
   e |- l < r --> l < r, Bool, d

* div and mod (/, %):
   lt = reduce_enums(l.t)_e
   rt = reduce_enums(r.t)_e
   d = in_or_dirless(lt, rt)
      lt ?= rt ?= Integer, nonneg(l)_e, pos(r)_e; t = Integer
   or lt ?= rt ?= Bit<n>, nonneg(l)_e, pos(r)_e; t = Bit<n>
   ---------------------------------------------------------
   e |- l / r --> l / r, t, d

* shift ops (>>, <<):
   lt = reduce_enums(l.t)_e
   rt = reduce_enums(r.t)_e
   d = in_or_dirless(lt, rt)
   nonneg(r)_e
      lt ?= Bit or Int
   or lt ?= Integer, compile_time_known(r)_e
   ------------------------------------------------------
   e |- l >> r --> l >> r, lt, d

*)

and check_binary_op env tags (op : Surface.Op.bin) typed_l typed_r : coq_Expression =
  let open Op in
  let l_typ = reduce_enums_in_type env (type_of_expr typed_l) in
  let r_typ = reduce_enums_in_type env (type_of_expr typed_r) in
  let dir =
    match dir_of_expr typed_l, dir_of_expr typed_r with
    | In, In -> In
    | _ -> Directionless
  in
  let typ =
    match op with
    | And {tags} | Or {tags} ->
      begin match l_typ, r_typ with
        | TypBool, TypBool -> TypBool
        | TypBool, r -> raise_mismatch tags "Operand must be a bool" r
        | l, r -> raise_mismatch tags "Operand must be a bool" l
      end
    (* Basic numeric operations are defined on both arbitrary and fixed-width integers *)
    | Plus {tags} | Minus {tags} | Mul {tags} ->
      begin match l_typ, r_typ with
        | TypInteger, TypInteger -> TypInteger
        | TypBit l, TypBit r when l = r -> TypBit l
        | TypInt l, TypInt r when l = r -> TypInt l
        | _, _ -> failwith "Binop unsupported."
      end
    | Eq {tags} | NotEq {tags} ->
       if type_equality env [] l_typ r_typ
       then if type_has_equality_tests env l_typ
            then TypBool
            else failwith "bad error message: type doesn't have equality tests (== and !=)"
       else raise_type_error tags (Type_Difference (l_typ, r_typ))
    (* Saturating operators are only defined on finite-width signed or unsigned integers *)
    | PlusSat {tags} | MinusSat {tags} ->
      begin match l_typ, r_typ with
        | TypBit l, TypBit r when l = r ->
          TypBit l
        | TypInt l, TypInt r when l = r ->
          TypInt l
        | TypBit _, r | TypInt _, r ->
          raise_mismatch tags "Operand must have type int<w> or bit<w>" r
        | l, r ->
          raise_mismatch tags "Operand must have type int<w> or bit<w>" l
      end
    (* Bitwise operators are only defined on bitstrings of the same width *)
       (* TODO: discuss with Ryan. discrepency with spec. *)
    | BitAnd {tags} | BitXor {tags} | BitOr {tags} ->
      begin match l_typ, r_typ with
        | TypBit l, TypBit r when l = r -> TypBit l
        | TypInt l, TypInt r when l = r -> TypInt l
        | TypBit _, _ -> raise_mismatch (info_of_expr typed_r) "unsigned int" r_typ
        | _, _ -> raise_mismatch (info_of_expr typed_l) "unsigned int" l_typ
      end
    (* Bitstring concatentation is defined on any two bitstrings *)
    (* TODO: discuss with Ryan. discrepency with spec. *)
    | PlusPlus {tags} ->
      begin match l_typ, r_typ with
        | TypBit l, TypBit r
        | TypBit l, TypInt r -> TypBit Bigint.(l + r)
        | TypInt l, TypBit r
        | TypInt l, TypInt r -> TypInt Bigint.(l + r)
        | TypInt _, _
        | TypBit _, _ ->
          raise_mismatch (info_of_expr typed_r) "bit<> or int<>" r_typ
        | _, _ ->
          raise_mismatch (info_of_expr typed_l) "bit<> or int<>" l_typ
      end
    (* Comparison is defined on both arbitrary and fixed-width integers *)
    | Le {tags} | Ge {tags} | Lt {tags} | Gt {tags} ->
      begin match l_typ, r_typ with
        | TypInteger, TypInteger -> TypBool
        | TypBit l, TypBit r
        | TypInt l, TypInt r when l = r -> TypBool
        | _, _ -> raise_type_error tags (Type_Difference (l_typ, r_typ))
      end
    (* Division is only defined on compile-time known arbitrary-precision positive integers *)
       (* TODO: discuss with Ryan. then why do we allow it for bit<w> too?*)
    | Div {tags} | Mod {tags} ->
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
       (* TODO: check this with Ryan. section 8.5 of spec.  *)
    | Shl {tags} | Shr {tags} ->
      begin match l_typ, is_nonnegative_numeric env typed_r with
        | TypBit _, true
        | TypInt _, true -> l_typ
        | TypInteger, true ->
          if compile_time_known_expr env typed_r
          then l_typ
          else failwith "bad right hand argument to shift"
        | _, true -> failwith "Bad left hand argument to shift."
        | _ -> failwith "Bad right hand argument to shift."
      end
  in
  MkExpression (tags, ExpBinaryOp (binop_to_coq_binop op, typed_l, typed_r), typ, dir)

(* See section 8.9.2 "Explicit casts" *)
(* cast judgment in spec. *)
and cast_ok ?(explicit = false) env original_type new_type =
  let original_type = saturate_type env original_type in
  let new_type = saturate_type env new_type in
  match original_type, new_type with
  | TypSet t1, TypSet t2 ->
    type_equality env [] t1 t2
  | t1, TypSet t2 ->
    not explicit &&
    type_equality env [] t1 t2
  | TypBit b, TypBool
  | TypBool, TypBit b ->
     Bigint.(b = one) && explicit
  | TypInteger, TypBool ->
    explicit
  | TypInt width1, TypBit width2 
  | TypBit width1, TypInt width2 ->
    explicit && Bigint.(width1 = width2)
  | TypBit width1, TypBit width2
  | TypInt width1, TypInt width2 ->
    width1 = width2 || explicit
  | TypInteger, TypBit _
  | TypInteger, TypInt _ ->
    true
  | TypBit _, TypInteger
  | TypInt _, TypInteger ->
    explicit
  | TypEnum (name, Some t, members), TypEnum (_, Some t', _)
  | t, TypEnum (name, Some t', members) ->
    explicit && type_equality env [] t t'
  | TypEnum (name, Some t, members), t' ->
    type_equality env [] t t'
  | TypNewType (name, typ), t ->
    cast_ok ~explicit env typ t
  | t, TypNewType (name, typ) ->
    cast_ok ~explicit env t typ
  | TypList types1, TypTuple types2 ->
    type_equality env [] (TypTuple types1) (TypTuple types2)
  | TypList types1, TypHeader rec2
  | TypList types1, TypStruct rec2 ->
    let types2 = List.map ~f:(fun ((_, typ)) -> typ) rec2 in
     casts_ok ~explicit env types1 types2 ||
       type_equality env [] (TypTuple types1) (TypTuple types2)
  (* record --> header and record --> struct is required to allow a statment such as x = (type) exp where type is the name of struct or header and exp is an expression of record type. section 8.13 of P4 spec v1.2.3*)
  | TypRecord rec1, TypHeader rec2
  | TypRecord rec1, TypStruct rec2
  | TypStruct rec1, TypStruct rec2
  | TypHeader rec1, TypHeader rec2 ->
    let types1 = List.map ~f:snd rec1 in
    let types2 = List.map ~f:snd rec2 in
    casts_ok ~explicit env types1 types2 ||
      type_equality env [] (TypRecord rec1) (TypRecord rec2)
  | _ -> type_equality env [] original_type new_type

and casts_ok ?(explicit = false) env original_types new_types =
  match List.zip original_types new_types with
  | Ok pairs ->
     List.for_all pairs ~f:(fun (orig_typ, new_typ) ->
         cast_ok ~explicit env orig_typ new_typ)
  | Unequal_lengths ->
     false

(* Section 8.9 *)
(*
   NOTE: trans(t)_e,[vars] translate Surface.type.t to Typed.type.t.
         I haven't decided if we want to mention that these are
         even different. [CAN ASK NATE IN REPORT!]
         e |- typ is type_well_formed judgement.
         e |- typ1, typ2 is judgment form for explicit cast ok.

   DISCUSS: saturating types twice. once in this function and another
            time in the cast_ok but this function doesn't reaLLY need them
            to be sat except for cast_ok. TODO after doc. 

   e, c | exp ~~> exp', t', d
   t'' = saturate(t')_e
   t''' = trans(t'')_e,[]
   t'''' = saturate(t''')_e
   e |- t'''
   e |- t', t'''
   ------------------------------------------------------
   e, c | (t) exp ~~>  (t''') exp', t''', directionless
*)
and type_cast env ctx tags typ expr : coq_Expression =
  let expr_typed = type_expression env ctx expr in
  let expr_type = saturate_type env (type_of_expr expr_typed) in
  let new_type = translate_type env typ in
  let new_type_sat = saturate_type env new_type in
  if not @@ is_well_formed_type env new_type
  then failwith "Ill-formed type.";
  if cast_ok ~explicit:true env expr_type new_type_sat
  then MkExpression (tags, ExpCast (new_type, expr_typed), new_type, Directionless)
  else failwith "Illegal explicit cast."

(* ? *)
and type_type_member env ctx tags typ name : coq_Expression =
  let real_name = real_name_for_type_member env typ name in
  let full_type, dir = Checker_env.find_type_of real_name env in
  MkExpression (tags, ExpTypeMember (P4name.p4string_name_only typ, name), full_type, dir)

and type_error_member env ctx tags (name: P4string.t) : coq_Expression =
  let packed_name: P4string.t = {name with str = "error." ^ name.str} in
  let (e, _) = Checker_env.find_type_of (BareName packed_name) env in
  if e <> TypError then failwith "Error member not an error?";
  MkExpression (tags, ExpErrorMember name, TypError, Directionless)

(* takes a type and if it's a header it returns a list of record type that has
   isValid as a built in function. ow. returns an empty list.*)
and header_methods typ =
  let fake_fields: coq_FieldType list =
    [({tags=P4info.dummy; str="isValid"},
                  TypFunction (MkFunctionType ([], [], FunBuiltin, TypBool)))]
  in
  match typ with
  | TypHeader fields -> fake_fields
  | _ -> []

(* takes a type, name, context. if type is an array and name is either size or lastindex
   it returns the type Bit<32>. if type is an array and name is next or last and
   context is parser state it returns the initial type passed in. ow. error.*)
and type_expression_member_builtin env (ctx: P4light.coq_ExprContext) info typ (name: P4string.t) : coq_P4Type =
  let fail () =
    raise_unfound_member info name.str in
  match typ with
  | TypArray (typ, _) ->
    let idx_typ = TypBit (Bigint.of_int 32) in
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
        let ret = TypTypeName ( result_typ_name) in
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
          [MkParameter (false, Directionless, TypInteger, None, {tags=P4info.dummy; str="count"})]
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
(* look at spec. *)
(* In cases where the field is being looked up and it is not found (i.e., None)
   the builtin helper is called for ease maintanance of the code in case we
   need to extend builtin fields. *)
and type_expression_member env ctx tags expr name : coq_Expression =
  let typed_expr = type_expression env ctx expr in
  let expr_typ = reduce_type env (type_of_expr typed_expr) in
  let methods = header_methods (type_of_expr typed_expr) in
  let rec find_type expr_typ =
    match expr_typ with
    | TypHeader fields
    | TypHeaderUnion fields
    | TypStruct fields ->
      let fs = fields @ methods in
      let matches ((field_name, _) : coq_FieldType) =
        P4string.eq field_name name
      in
      begin match List.find ~f:matches fs with
        | Some ((_, field_typ)) -> field_typ
        | None -> type_expression_member_builtin env ctx (Expression.tags expr) expr_typ name
      end
    | TypSpecializedType (TypExtern extern_name, args) ->
       begin match Checker_env.find_extern_opt (BareName extern_name) env with
       | Some {type_params; methods; abst_methods} ->
          let extended_env = Checker_env.insert_types (List.zip_exn type_params args) env in
          let matches (m: P4light.coq_ExternMethod) =
            P4string.eq m.name name
          in
          begin match List.find ~f:matches (methods @ abst_methods) with
          | Some m -> reduce_type extended_env (TypFunction m.typ)
          | None -> type_expression_member_builtin env ctx (Expression.tags expr) expr_typ name
          end
       | None -> failwith "methods not found for extern"
       end
    | TypExtern extern_name ->
       find_type (TypSpecializedType (TypExtern extern_name, []))
    | _ -> type_expression_member_builtin env ctx (Expression.tags expr) expr_typ name
  in
  let expr_typed: P4light.coq_ExpressionPreT = ExpExpressionMember (typed_expr, name) in
  MkExpression (tags, expr_typed, find_type expr_typ, Directionless)

(* Section 8.4.1
 * -------------
 *
 * Δ, T, Γ |- cond : bool    Δ, T, Γ |- tru : t    Δ, T, Γ |- fls : t;
 * -------------------------------------------------------------------
 *              Δ, T, Γ |- cond ? tru : fls : t

   e, c |- cond ~~> {cond', Bool, d}
   e, c |- tru ~~> {tru', t', d'}
   e, c |- fls ~~> {fls', t'', d''}
   t' ?= t'' and t' ?<> Integer
   -------------------------------------
   e, c |- cond ? tru : fls ~~> {cond' ? tru' : fls', t', Directionless}
 *)
and type_ternary env ctx tags cond tru fls: coq_Expression =
  let cond_typed = type_expression env ctx cond in
  assert_bool (Expression.tags cond) (type_of_expr cond_typed) |> ignore;
  let fls_typed = type_expression env ctx fls in
  let tru_typed = type_expression env ctx tru in
  assert_same_type env (Expression.tags tru) (Expression.tags fls) (type_of_expr tru_typed) (type_of_expr fls_typed) |> ignore;
  match type_of_expr tru_typed with
  | TypInteger ->
    (* TODO this is allowed if cond is compile-time known *)
    failwith "Conditional expressions may not have arbitrary width integer type"
  | t ->
    MkExpression (tags, ExpTernary (cond_typed, tru_typed, fls_typed), t, Directionless)

and match_params_to_args env call_site_info params args : (coq_P4Parameter * Expression.t option) list =
  let rec get_mode mode (args: Surface.Argument.t list) =
    match mode, args with
    | None, Expression { value; _ } :: args
    | Some `Positional, Expression { value; _ } :: args ->
      get_mode (Some `Positional) args
    | None, Missing _ :: args
    | Some `Positional, Missing _ :: args ->
      get_mode (Some `Positional) args
    | None, KeyValue { key; value; _ } :: args
    | Some `Named, KeyValue { key; value; _ } :: args ->
      get_mode (Some `Named) args
    | m, [] -> m
    | _ -> failwith "mixed positional and named arguments at call site"
                    (*~info:(call_site_info: P4info.t)]*)
  in
  (* let args = List.map ~f:snd args in *)
  match get_mode None args with
  | None ->
    match_positional_args_to_params env call_site_info params args
  | Some `Positional ->
    match_positional_args_to_params env call_site_info params args
  | Some `Named ->
    match_named_args_to_params env call_site_info params args

and match_positional_args_to_params env call_site_info params args =
  let conv param arg =
    let open Surface.Argument in
    match arg with
    | Expression { value; _ } -> param, Some value
    | Missing {tags} -> param, None
    | _ -> failwith "expected positional argument"
  in
  let rec go (params: coq_P4Parameter list) (args: Surface.Argument.t list) =
    match params, args with
    | param :: params, arg :: args ->
      conv param arg :: go params args
    | param :: params, [] ->
      begin match find_default_arg env param with
        | Some expr -> conv param (Expression {value = expr; tags = P4info.dummy}) :: go params args
        | None ->
          if opt_of_param param
          then conv param (Missing { tags = P4info.dummy }) :: go params args
          else failwith "missing argument for parameter"
                (*~info:(call_site_info: P4info.t)
                ~param:(param: coq_P4Parameter)]*)
      end
    | [], arg :: args ->
      failwith "too many arguments"
    (*~info:(call_site_info: P4info.t)]*)
    | [], [] -> []
  in
  go params args

(* matches the arguments to parameters based on parameter names.
   if the parameter and argument have the same name it bundles up the parameter name and the
   argument value.
   if the parameter has opt_value and there is no argument with the name of parameter it
   bundles up the parameter name with its opt_value. but if the paremeter doesn't have
   opt_value and is optional, it bundles up the parameter name with none. ow., it raises a
   mismatch error. *)
and match_named_args_to_params
    env
    call_site_info
    (params: coq_P4Parameter list)
    (args: Surface.Argument.t list) =
  match params with
  | p :: params ->
    let right_arg : Argument.t -> _ = function
      | KeyValue {key; value; _} ->
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
        else failwith "parameter has no matching argument"
              (*~call_site:(call_site_info: P4info.t)
              ~param:(p: coq_P4Parameter)]*)
    end
  | [] ->
    match args with
    | [] -> []
    | a :: rest ->
      failwith "too many arguments supplied at call site"
          (*~info:(call_site_info: P4info.t)
          ~unused_args:(args : Surface.Argument.pre_t list)]*)

and is_lvalue env (expr_typed: P4light.coq_Expression) =
  let MkExpression (_, expr, expr_typ, expr_dir) = expr_typed in
  match expr with
  | ExpName (name, _) ->
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

and check_direction env dir (arg_typed: P4light.coq_Expression) =
  let MkExpression (_, _, arg_type, arg_dir) = arg_typed in
  match dir with
  | Directionless -> ()
  | In ->
    begin match arg_type with
      | TypExtern _ ->
        failwith "externs should always be directionless"
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
    (* ATTN: Temporary change to allow extern used in the initializers *)
    | ExprCxMethod, FunExtern -> true
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

and type_function_call env ctx call_tags func type_args args : coq_Expression =
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
  let type_args = List.map type_args ~f:(fun t -> t
                                                  |> translate_type_opt env
                                                  |> option_map (reduce_type env)) in
  let params_args = match_params_to_args env (Expression.tags func) params args in
  let type_params_args =
    match List.zip type_params type_args with
    | Ok v -> v
    | Unequal_lengths ->
      match type_args with
      | [] -> List.map ~f:(fun v -> v, None) type_params
      | _ -> failwith "Mismatch in type arguments."
  in
  let type_params_args =
    infer_type_arguments env ctx type_params_args params_args
  in
  let env = Checker_env.insert_types type_params_args env in
  let subst_param_arg ((MkParameter (opt, dir, typ, opt_value, var):coq_P4Parameter), arg) =
    let typ = saturate_type env typ in
    let param = MkParameter (opt, dir, typ, opt_value, var) in
    validate_param env (ctx_of_kind kind) typ dir call_tags (option_map Bigint.to_int_exn opt_value);
    param, arg
  in
  let params_args' = List.map params_args ~f:subst_param_arg in
  let typed_params_args = List.map ~f:(cast_param_arg env ctx call_tags) params_args' in
  let out_type_args = List.map ~f:snd type_params_args in
  let out_args = List.map ~f:snd typed_params_args in
  let typ = saturate_type env return_type in
  let call: P4light.coq_ExpressionPreT = ExpFunctionCall (func_typed, out_type_args, out_args) in
  if call_ok ctx kind
  then MkExpression (call_tags, call, typ, Directionless)
  else failwith "Call not allowed in this context." 
            (*~ctx:(ctx: coq_ExprContext) ~kind:(kind: P4light.coq_FunctionKind)] *)

and select_constructor_params env info methods args =
  let matching_constructor (proto: P4light.coq_MethodPrototype) =
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

(* Unused; 
   One thing to note is that DeclExternObject is different from other declarations in that 
   it does not include wildcards appearing in individual constructors. 
   Example: Hash in tofino.p4 *)
  and get_decl_type_params (decl : P4light.coq_Declaration) =
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

and get_decl_constructor_params env info (decl : P4light.coq_Declaration) args =
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

and overload_param_count_ok args (params: coq_P4Parameter list) =
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
  | Some (TypConstructor (ts, ws, ps, ret)) -> ts, ws, ps, ret
  | ctor -> failwith "Bad constructor type or no matching constructor."

and resolve_constructor_overload env type_name args =
  let arg_name arg =
    match arg with
    | Argument.KeyValue {key; _} -> Some key
    | _ -> None
  in
  match list_option_flip (List.map ~f:arg_name args) with
  | Some arg_names ->
    resolve_constructor_overload_by ~f:(overload_param_names_ok arg_names) env type_name
  | None ->
    resolve_constructor_overload_by ~f:(overload_param_count_ok args) env type_name

and resolve_function_overload_by ~f env ctx func : P4light.coq_Expression =
  let open Surface.Expression in
  match func with
  | Name {name; tags} ->
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
      | Some typ -> MkExpression (tags, ExpName (name, P4light.noLocator), typ, Directionless)
      | _ -> type_expression env ctx func
    end
  | ExpressionMember { expr; name; tags } ->
    let expr_typed = type_expression env ctx expr in
    let expr_type = type_of_expr expr_typed in
    let prog_member: P4light.coq_ExpressionPreT =
      ExpExpressionMember (expr_typed, name)
    in
    let rec resolve_by_type typ : P4light.coq_Expression =
      begin match reduce_type env typ with
        | TypSpecializedType (TypExtern extern_name, args) ->
          let (MkExpression (info, expr, typ, dir)) = resolve_by_type (TypExtern extern_name) in
          let ext = Checker_env.find_extern (BareName extern_name) env in 
          let env_with_args = Checker_env.insert_types (List.zip_exn ext.type_params args) env in
          let typ = reduce_type env_with_args typ in
          MkExpression (info, expr, typ, dir)
        | TypExtern extern_name ->
          let ext = Checker_env.find_extern (BareName extern_name) env in 
          let works (meth: P4light.coq_ExternMethod) =
            let params = params_of_fn_type meth.typ in
            P4string.eq meth.name name && f params
          in
          begin match List.find ~f:works (ext.methods @ ext.abst_methods) with
            | Some p -> MkExpression (tags, prog_member, TypFunction p.typ, Directionless)
            | None -> failwith "couldn't find matching method"
          end
        | _ ->
          let typ = saturate_type env (type_of_expr expr_typed) in
          begin match type_expression_member_function_builtin env tags typ name with
            | Some typ -> MkExpression (tags, prog_member, typ, Directionless)
            | None -> type_expression env ctx func
          end
      end
    in
    resolve_by_type expr_type
  | _ -> type_expression env ctx func

and resolve_function_overload env ctx type_name args =
  let arg_name arg =
    match arg with
    | Argument.KeyValue {key; _} -> Some key
    | _ -> None
  in
  match list_option_flip (List.map ~f:arg_name args) with
  | Some arg_names ->
    resolve_function_overload_by ~f:(overload_param_names_ok arg_names) env ctx type_name
  | None ->
    resolve_function_overload_by ~f:(overload_param_count_ok args) env ctx type_name

and type_constructor_invocation env ctx info decl_name type_args args : P4light.coq_Expression list * coq_P4Type list * coq_P4Type =
  let type_args = List.map ~f:(translate_type_opt env) type_args in
  let t_params, w_params, params, ret = resolve_constructor_overload env decl_name args in
  let params_args = match_params_to_args env info params args in
  let type_params_args = infer_constructor_type_args env ctx t_params w_params params_args type_args in
  let env' = Checker_env.insert_types type_params_args env in
  let cast_arg (param, arg: coq_P4Parameter * Surface.Expression.t option) =
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
  args_typed, List.map ~f:snd type_params_args, ret

(* Section 14.1 *)
(*
   look at spec
*)
and type_nameless_instantiation env ctx tags typ args : coq_Expression =
  match typ with
  | Type.SpecializedType { base; args = type_args; tags } ->
    begin match base with
      | TypeName { name = decl_name; _ } ->
        let out_args, out_type_args, out_typ =
          type_constructor_invocation env ctx tags decl_name type_args args
        in
        MkExpression (tags, ExpNamelessInstantiation (TypSpecializedType (translate_type env base, out_type_args), out_args),
        out_typ,
        Directionless)
      | _ ->
        failwith "don't know how to instantiate this type"
                          (*~typ:(typ: Surface.Type.t)]*)
    end
  | TypeName {name = tn; tags} ->
    let typ = Surface.Type.SpecializedType { base = typ; args = []; tags } in
    type_nameless_instantiation env ctx tags typ args
  | _ ->
    failwith "don't know how to instantiate this type"
         (*~typ:(typ: Surface.Type.t)]*)

(* Section 8.12.3 *)
(*

   e, c |- msk ~~> {msk', t', d'}
   e, c |- expr ~~> {expr', t'', d''}
   (t ?= t' ?= Bit<n>; t = Bit<n>) or (t ?= t' ?= Integer; t = Integer)
   or (t ?= Bit<n> and t' ?= Integer; t = Bit<n>)
   or (t' ?= Bit<n> and t ?= Integer; t = Bit<n>)
   -----------------------------------------------------------
   e, c |- msk ^ expr ~~> {msk' @ expr', Set t, Directionless}
*)
and type_mask env ctx expr mask =
  let expr_typed, mask_typed = cast_to_same_type env ctx expr mask in
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
  MatchMask (expr_typed, mask_typed), res_typ

(* Section 8.12.4 *)
(*

   e, c |- l ~~> {l', t, d}
   e, c |- h ~~> {h', t', d'}
   t ?= t' ?= Bit<n> or t ?= t' ?= Int<n> or t ?= t' ?= Integer 
   -------------------------------------------------------------
   e, c |- <l:h> ~~> {<l':h'>, Set t, Directionless}

*)
and type_range env ctx lo hi = 
  let lo_typed, hi_typed = cast_to_same_type env ctx lo hi in
  let typ : coq_P4Type =
    match (type_of_expr lo_typed), (type_of_expr hi_typed) with
    | TypBit l, TypBit r when l = r ->
      TypBit l
    | TypInt l, TypInt r when l = r ->
      TypInt l
    | TypInteger, TypInteger -> TypInteger
    (* TODO: add pretty-printer and [to_string] for P4light module *)
    | TypBit width, hi_typ ->
      raise_mismatch (Expression.tags hi) ("bit<" ^ (Bigint.to_string width) ^ ">") hi_typ
    | TypInt width, hi_typ ->
      raise_mismatch (Expression.tags hi) ("int<" ^ (Bigint.to_string width) ^ ">") hi_typ
    | lo_typ, _ -> raise_mismatch (P4info.merge (Expression.tags lo) (Expression.tags hi)) "int or bit" lo_typ
  in
  MatchRange (lo_typed, hi_typed), typ

and check_statement_legal_in (ctx: coq_StmtContext) (stmt: Surface.Statement.t) : unit =
  match ctx, stmt with
  | StmtCxAction, Switch _ ->
    failwith "Branching statement not allowed in action."
  | StmtCxParserState, Conditional _
  | StmtCxParserState, Switch _ ->
    failwith "Branching statement not allowed in parser."
  | _ -> ()

and type_statement (env: Checker_env.t) (ctx: coq_StmtContext) (stmt: Surface.Statement.t)
  : P4light.coq_Statement * Checker_env.t =
  check_statement_legal_in ctx stmt;
  match stmt with
  | MethodCall { func; type_args; args; tags } ->
    type_method_call env ctx tags func type_args args
  | Assignment { lhs; rhs; tags } ->
    type_assignment env ctx tags lhs rhs
  | DirectApplication { typ; args; tags } ->
    type_direct_application env ctx tags typ args
  | Conditional { cond; tru; fls; tags } ->
    type_conditional env ctx tags cond tru fls
  | BlockStatement { block; tags } ->
    type_block env ctx tags block
  | Exit { tags } ->
    MkStatement (tags, StatExit, StmVoid), env
  | EmptyStatement { tags }->
      MkStatement (tags, StatEmpty, StmUnit), env
  | Return { expr; tags } ->
    type_return env ctx tags expr
  | Switch { expr; cases; tags } ->
    type_switch env ctx tags expr cases
  | DeclarationStatement { decl; tags } ->
    type_declaration_statement env ctx tags decl

(* Section 8.17 *)
and type_method_call env ctx call_info func type_args args =
  let expr_ctx = expr_ctxt_of_stmt_ctxt ctx in
  let call_typed =
    type_function_call env expr_ctx call_info func type_args args
  in
  match call_typed with
  | MkExpression (tags, ExpFunctionCall (func, type_args, args), _, _) ->
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
  then failwith "Must be an lvalue"
                         (*~lhs:(lhs:Surface.Expression.t)]*)
  else
    let rhs_typed = cast_expression env expr_ctx (type_of_expr lhs_typed) rhs in
    ignore (assert_same_type env (Expression.tags lhs) (Expression.tags rhs)
              (type_of_expr lhs_typed) (type_of_expr rhs_typed));
    MkStatement (stmt_info, StatAssignment (lhs_typed, rhs_typed), StmUnit),
    env

(* This belongs in an elaboration pass, really. - Ryan *)
and type_direct_application env ctx stmt_tags typ args =
  let expr_ctx = expr_ctxt_of_stmt_ctxt ctx in
  let open Surface.Expression in
  let instance = NamelessInstantiation {typ = typ; args = []; tags = stmt_tags} in
  let apply = ExpressionMember {expr = instance;
                                name = {tags = P4info.dummy; str = "apply"};
                                tags = stmt_tags} in
  let call_typed =
    type_function_call env expr_ctx P4info.dummy apply [] args
  in
  match call_typed with
  | MkExpression (tags, ExpFunctionCall (MkExpression (_, _, func_typ, _), type_args, args), _, _) ->
    let stmt: P4light.coq_StatementPreT =
      StatDirectApplication (translate_type env typ, func_typ, args)
    in
    MkStatement (stmt_tags, stmt, StmUnit),
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
  assert_bool (Expression.tags cond) (type_of_expr expr_typed) |> ignore;
  let env' = Checker_env.push_scope env in
  let type' stmt = fst (type_statement env' ctx stmt) in
  let true_typed = type' true_branch in
  let true_type = type_of_stmt true_typed in
  let false_typed = option_map type' false_branch in
  let stmt_out: P4light.coq_StatementPreT =
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
  let st_typ, stmts_typed, env' =
    List.fold_left ~f:fold ~init:(StmUnit, [], env) statements in
  st_typ, List.rev stmts_typed, env'

and list_to_block info: P4light.coq_Statement list -> P4light.coq_Block =
  let f stmt block = BlockCons (stmt, block) in
  let init = BlockEmpty info in
  List.fold_right ~f ~init

and type_block env ctx stmt_info block =
  let env' = Checker_env.push_scope env in
  let typ, stmts, env' = type_statements env' ctx block.statements in
  let block = list_to_block stmt_info stmts in
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
    | StmtCxFunction t
    | StmtCxMethod t  -> t
    | StmtCxParserState -> failwith "return in parser state not allowed"
  in
  let (stmt, typ) : P4light.coq_StatementPreT * coq_P4Type =
    match expr with
    | None -> StatReturn None, TypVoid
    | Some e ->
      let e_typed = cast_expression env expr_ctx ret_typ e in
      StatReturn (Some e_typed), type_of_expr e_typed
  in
  MkStatement (stmt_info, stmt, StmVoid), env

(* Section 11.7 *)
and type_switch env ctx stmt_info expr cases =
  let open Surface.Statement in
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
    let case_name_eq label (case: P4light.coq_StatementSwitchCase) =
      match case with
      | StatSwCaseAction (_, lbl, _)
      | StatSwCaseFallThrough (_, lbl) ->
        match label, lbl with
        | Default _, StatSwLabDefault _ -> true
        | Name {name = n1; _}, StatSwLabName (_, n2) ->
          P4string.eq n1 n2
        | _ -> false
    in
    List.exists ~f:(case_name_eq lbl) cases_done
  in
  let label_checker cases_done (label: Surface.Statement.switch_label): P4light.coq_StatementSwitchLabel =
    if lbl_seen cases_done label then raise (Type (tags_label label, Duplicate));
    if lbl_seen cases_done (Default { tags = P4info.dummy }) then raise (Type (tags_label label, UnreachableBlock));
    match label with
    | Default { tags } ->
      StatSwLabDefault tags
    | Name { name; tags } ->
      if List.mem ~equal:P4string.eq action_names name
      then StatSwLabName (tags, name)
      else raise_unfound_member name.tags name.str
  in
  let case_checker cases_done case =
    match case with
    | Action { label; code = block; tags } ->
      let block_stmt_typed, env = type_block env ctx tags block in
      let label_typed = label_checker cases_done label in
      let block_typed =
        match prestmt_of_stmt block_stmt_typed with
        | StatBlock block -> block
        | _ -> failwith "bug: expected block"
      in
      cases_done @ [StatSwCaseAction (tags, label_typed, block_typed)]
    | FallThrough { label; tags } ->
      let label_typed = label_checker cases_done label in
      cases_done @ [StatSwCaseFallThrough (tags, label_typed)]
  in
  let cases = List.fold ~init:[] ~f:case_checker cases in
  MkStatement (stmt_info, StatSwitch (expr_typed, cases), StmUnit), env

and init_of_decl (decl: P4light.coq_Declaration) : P4light.coq_Initializer =
  match decl with
  | DeclInstantiation (info, typ, args, name, init) ->
    InitInstantiation (info, typ, args, name, inits_of_decls init)
  | DeclFunction (info, return_type, name, t_params, params_typed, body_typed) ->
    InitFunction (info, return_type, name, t_params, params_typed, body_typed)
  | _ -> failwith "BUG: expected DeclInstantiation or DeclFunction."

and inits_of_decls (decls: P4light.coq_Declaration list) : P4light.coq_Initializer list =
  List.map ~f:init_of_decl decls

and stmt_of_decl_stmt (decl: P4light.coq_Declaration) : P4light.coq_Statement =
  let info, (stmt: P4light.coq_StatementPreT) =
    match decl with
    | DeclConstant (info, typ, name, value) ->
      info, StatConstant (typ, name, value, P4light.noLocator)
    | DeclVariable (info, typ, name, init) ->
      info, StatVariable (typ, name, init, P4light.noLocator)
    | DeclInstantiation (info, typ, args, name, init) ->
      info, StatInstantiation (typ, args, name, inits_of_decls init)
    | _ ->
      P4info.dummy, StatEmpty
  in
  MkStatement (info, stmt, StmUnit)

(* Section 10.3 *)
and type_declaration_statement env ctx stmt_info (decl: Declaration.t) : P4light.coq_Statement * Checker_env.t =
  match decl with
  | Constant _
  | Instantiation _
  | Variable _ ->
    let decl_typed, env' = type_declaration env (DeclCxStatement ctx) decl in
    stmt_of_decl_stmt decl_typed, env'
  | _ -> failwith "declaration used as statement, but that's not allowed. Parser bug?"(* ~decl:(decl: Surface.Declaration.t)]*)

(* Section 10.1
 *
 *          Δ, T, Γ |- e : t' = t
 * ---------------------------------------------
 *    Δ, T, Γ |- const t x = e : Δ, T, Γ[x -> t]
*)
and type_constant env ctx decl_info annotations typ name expr : P4light.coq_Declaration * Checker_env.t =
  let expr_ctx = expr_ctxt_of_decl_ctxt ctx in
  let expected_typ = translate_type env typ in
  let typed_expr = cast_expression env expr_ctx expected_typ expr in
  match compile_time_eval_expr env typed_expr with
  | Some value ->
    let exp = val_to_literal value in
    DeclConstant (decl_info, translate_type env typ, name, exp),
    env
    |> Checker_env.insert_dir_type_of (BareName name) expected_typ Directionless
    |> Checker_env.insert_const (BareName name) value
  | None ->
    failwith "expression not compile-time-known"

and insert_params (env: Checker_env.t) (params: Surface.Parameter.t list) : Checker_env.t =
  let open Surface.Parameter in
  let insert_param env p =
    let typ = translate_type env p.typ in
    let dir = translate_direction p.direction in
    Checker_env.insert_dir_type_of ~shadow:true (BareName p.variable) typ dir env
  in
  (* Printf.printf "insert params -- env %s \n%!" (CheckerEnv.show env); *)
  List.fold_left ~f:insert_param ~init:env params

and type_initializer env env_top ctx (init: Surface.Statement.t) : P4light.coq_Declaration * Checker_env.t  * Checker_env.t =
  begin match init with
  | DeclarationStatement { decl; tags } ->
    begin match decl with
    | Function {return; name; type_params; params; body; tags } ->
      check_param_shadowing params [];
      let ret_type = translate_type env_top return in
      let ctx: coq_StmtContext = StmtCxMethod ret_type in
      let typed_func, _ = type_function env_top ctx tags return name type_params params body in
      begin match typed_func with
      (* @synchronous allows access to other instantiations but not function declarations *)
      | DeclFunction _ ->
        typed_func, env, env_top
      | _ -> failwith "BUG: expected DeclFunction."
      end
    (* More restrictions on instantiations? Variable declarations allowed? *)
    | Instantiation { annotations; typ; args; name; init; tags } ->
      let typed_instance, instance_type =
        type_instantiation env ctx tags annotations typ args name init in
      begin match typed_instance with
      | DeclInstantiation (info, typ, args, name, init_typed) ->
        typed_instance,
        Checker_env.insert_type_of (BareName name) instance_type env,
        Checker_env.insert_type_of (BareName name) instance_type env_top
      | _ -> failwith "BUG: expected DeclInstantiation."
      end
    | _ -> failwith "Unexpected declarations in the list of initializers."
    end
  | _ -> failwith "Unexpected statement as the initializer."
  end

and type_initializers env ctx instance_type (inits: Surface.Statement.t list): P4light.coq_Declaration list * int =
  let env_top = 
    Checker_env.insert_type_of (BareName {tags=P4info.dummy; str="this"}) instance_type (Checker_env.top_scope env) in
  let extern_name, args =
    match instance_type with
    | TypExtern extern_name -> extern_name, []
    | TypSpecializedType (TypExtern extern_name, args) -> extern_name, args
    | _ -> failwith "Initializers are allowed only in the instantiation of an extern object."
                            (*~typ:(instance_type : P4light.coq_P4Type)]*)
  in let ext = Checker_env.find_extern (BareName extern_name) env in 
  let env_with_args = Checker_env.insert_types (List.zip_exn ext.type_params args) env in
  let decls_abst = List.map ~f:(fun m -> (m.name, reduce_type env_with_args (TypFunction m.typ))) ext.abst_methods in
  let check_initializer (inits_typed, num_absts, env, env_top) decl =
    let init_typed, env', env_top' = type_initializer env env_top ctx decl in
    let num_absts' = 
    begin match init_typed with
    | DeclFunction (info, return_type, name, t_params, params_typed, body_typed) ->
      begin match List.find ~f:(fun decl -> P4string.eq name (fst decl)) decls_abst with
      | Some (name, decl_type) ->
        let init_type = TypFunction (MkFunctionType (t_params, params_typed, FunExtern, return_type)) in
          assert_type_equality env' name.tags decl_type init_type
      | None -> ()
      end;
      num_absts + 1
    | _ -> num_absts
    end
    in inits_typed @ [init_typed], num_absts', env', env_top'
  in let inits_typed, num_absts, _, _ = List.fold_left ~f:check_initializer ~init:([], 0, env, env_top) inits in
     inits_typed, num_absts

(* Section 10.3 *)
and type_instantiation env ctx info annotations typ args name init_block : P4light.coq_Declaration * coq_P4Type =
  let expr_ctx = expr_ctxt_of_decl_ctxt ctx in
  let instance_typed = type_nameless_instantiation env expr_ctx info typ args in
  let (MkExpression (_, instance_expr, instance_type, instance_dir)) = instance_typed in
  begin match instance_type, ctx with
    | TypControl _, DeclCxTopLevel ->
      failwith "controls cannot be instantiated in the top level scope"
    | TypParser _, DeclCxTopLevel ->
      failwith "parsers cannot be instantiated in the top level scope"
    | _ -> ()
  end;
  let inits_typed, num_absts =
    begin match init_block with
      | Some init_block -> type_initializers env ctx instance_type init_block.statements
      | None -> [], 0
    end in
  begin match instance_type with
  | TypExtern extern_name
  | TypSpecializedType (TypExtern extern_name, _) ->
    let ext = Checker_env.find_extern (BareName extern_name) env in 
    if List.length ext.abst_methods <> num_absts
    then failwith "Abstract methods are not fully initialized during instantiation."
  | _ -> ()
  end;
  match instance_expr with
  | ExpNamelessInstantiation (typ, args) ->
    DeclInstantiation (info, typ, args, name, inits_typed), instance_type
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
  infer_type_arguments env ctx full_params_args params_args

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

and check_set_expression env ctx (m: Surface.Expression.t) (expected_type: coq_P4Type) : P4light.coq_MatchPreT * coq_P4Type =
  match m with
  | Mask {expr; mask; tags} ->
     let m_typed, typ = type_mask env ctx expr mask in
     m_typed, expected_type
  | Range {lo; hi; tags} ->
     let m_typed, typ = type_range env ctx lo hi in
     m_typed, expected_type
  | e ->
     let e_typed = type_expression env ctx e in
     let e_typ = type_of_expr e_typed in
     if type_equality env [] e_typ expected_type
     then MatchCast (TypSet expected_type, e_typed), expected_type
     else if cast_ok env e_typ expected_type
     then MatchCast (TypSet expected_type, e_typed), expected_type
     else if type_equality env [] e_typ (TypSet expected_type)
     then MatchCast (TypSet expected_type, e_typed), expected_type
     else if cast_ok env e_typ (TypSet expected_type)
     then MatchCast (TypSet expected_type, e_typed), expected_type
     else failwith "set expression ill-typed"

and check_match env ctx (m: Surface.Match.t) (expected_type: coq_P4Type) : P4light.coq_Match =
  match m with
  | Default { tags }
  | DontCare { tags } ->
    MkMatch (tags, MatchDontCare, expected_type)
  | Expression { expr; tags } ->
    let m_typed, typ = check_set_expression env ctx expr expected_type in
    MkMatch (tags, m_typed, typ)

and check_match_product env ctx (ms: Surface.Match.t list) (expected_types: coq_P4Type list) =
  match ms, expected_types with
  | [m], [t] ->
    [check_match env ctx m t]
  | [m], types ->
    [check_match env ctx m (TypList types)]
  | ms, types ->
    List.map ~f:(fun (m, t) -> check_match env ctx m t) @@ List.zip_exn ms types

and type_select_case env ctx state_names expr_types (case: Surface.Parser.case) : P4light.coq_ParserCase =
  let matches_typed = check_match_product env ctx case.matches expr_types in
  if List.mem ~equal:P4string.eq state_names case.next
  then MkParserCase (case.tags, matches_typed, case.next)
  else failwith "state name unknown" (*~name:(case.next.str: string)]*)

and type_transition env ctx state_names transition : P4light.coq_ParserTransition =
  match transition with
  | Surface.Parser.Direct {next; tags} ->
    if List.mem ~equal:P4string.eq state_names next
    then ParserDirect (tags, next)
    else raise @@ Type (next.tags, (Error.Unbound next.str))
  | Surface.Parser.Select {exprs; cases; tags} ->
    let exprs_typed = List.map ~f:(type_expression env ctx) exprs in
    let expr_types = List.map ~f:type_of_expr exprs_typed in
    let cases_typed =
      List.map ~f:(type_select_case env ctx state_names expr_types) cases
    in
    ParserSelect (tags, exprs_typed, cases_typed)

and type_parser_state env state_names (state: Parser.state) : P4light.coq_ParserState =
  let env = Checker_env.push_scope env in
  let (_, stmts_typed, env) = type_statements env StmtCxParserState state.statements in
  let transition_typed = type_transition env ExprCxParserState state_names state.transition in
  MkParserState (state.tags, state.name, stmts_typed, transition_typed)

and check_state_names names =
  match List.find_a_dup names
          ~compare:(fun (x: P4string.t) y ->
              String.compare x.str y.str)
  with
  | Some duplicated -> failwith "duplicate state name in parser" (*~state:duplicated.str]*)
  | None ->
    if List.mem ~equal:P4string.eq names {tags=P4info.dummy; str="start"}
    then ()
    else failwith "parser is missing start state"

and open_parser_scope env ctx params constructor_params locals (states: Parser.state list) =
  let env = Checker_env.push_scope env in
  let constructor_params_typed, _ = type_constructor_params env ctx constructor_params in
  let params_typed = type_params env (ParamCxRuntime ctx) params in
  let env = insert_params env constructor_params in
  (* Printf.printf "open parser scope %s \n%!" "blah blha"; *)
  let env = insert_params env params in
  let locals_typed, env = type_declarations env DeclCxNested locals in
  let program_state_names = List.map ~f:(fun state -> state.name) states in
  (* TODO: check that no program_state_names overlap w/ standard ones
   * and that there is some "start" state *)
  let accept: P4string.t = {tags=P4info.dummy; str="accept"} in
  let reject: P4string.t = {tags=P4info.dummy; str="reject"} in
  let state_names = program_state_names @ [accept; reject] in
  check_state_names state_names;
  (env, state_names, constructor_params_typed, params_typed, locals_typed)

(* Section 12.2 *)
and type_parser env info name annotations type_params params constructor_params locals (states: Parser.state list) =
  if List.length type_params > 0
  then failwith "Parser declarations cannot have type parameters";
  let env', state_names, constructor_params_typed, params_typed, locals_typed =
    open_parser_scope env ParamCxDeclParser params constructor_params locals states
  in
  let states_typed = List.map ~f:(type_parser_state env' state_names) states in
  let parser_typed : P4light.coq_Declaration =
    DeclParser (info,
                name,
                [],
                params_typed,
                constructor_params_typed,
                locals_typed,
                states_typed)
  in
  let parser_type = MkControlType ([], params_typed) in
  let ctor_type = TypConstructor ([], [], constructor_params_typed, TypParser parser_type) in
  let env = Checker_env.insert_type_of (BareName name) ctor_type env in
  parser_typed, env

and open_control_scope env ctx params constructor_params locals =
  let env = Checker_env.push_scope env in
  let params_typed = type_params env (ParamCxRuntime ctx) params in
  let constructor_params_typed, _ = type_constructor_params env ctx constructor_params in
  let env = insert_params env constructor_params in
  let env = insert_params env params in
  let locals_typed, env = type_declarations env DeclCxNested locals in
  env, params_typed, constructor_params_typed, locals_typed

(* Section 13 *)
and type_control env info name annotations type_params params
    constructor_params locals (apply: Block.t) =
  (*
  begin match Checker_env.find_type_of_opt (BareName name) env with
  | None -> ()
  | Some (t, _) ->
     match saturate_type env t with
     | TypConstructor (_, _, _, TypControl _) -> ()
     | bad_type -> failwith "cannot shadow object with control" ~bad_type:(bad_type: coq_P4Type)]
  end;
   *)
  if List.length type_params > 0
  then failwith "Control declarations cannot have type parameters";
  let inner_env, params_typed, constructor_params_typed, locals_typed =
    open_control_scope env ParamCxDeclControl params constructor_params locals
  in
  let block_typed, _ = type_block inner_env StmtCxApplyBlock apply.tags apply in
  let apply_typed =
    match prestmt_of_stmt block_typed with
    | StatBlock block -> block
    | _ -> failwith "expected BlockStatement"
  in
  let control : P4light.coq_Declaration =
    DeclControl (info,
                 name,
                 [],
                 params_typed,
                 constructor_params_typed,
                 locals_typed,
                 apply_typed)
  in
  let control_type =
    MkControlType ([], params_typed)
  in
  let ctor_type = TypConstructor ([], [], constructor_params_typed, TypControl control_type) in
  let env = Checker_env.insert_type_of ~shadow:true (BareName name) ctor_type env in
  control, env

and add_direction (param: Surface.Parameter.t) : Surface.Parameter.t =
  let open Surface in 
  let direction: Direction.t option = Some (In { tags = P4info.dummy }) in
  match param.direction with
  | None -> {param with direction}
  | _ -> param

(* Section 9

 * Function Declaration:
 *
 *        Γ' = union over i Γ (xi -> di ti)
 *   forall k,  Δk, Tk, Γk' |- stk+1 : Δk+1, Tk+1, Γk+1'
 *     stk = return ek => Δk, Tk, Γk' |- ek : t' = tr
 * -------------------------------------------------------
 *    Δ, T, Γ |- tr fn<...Aj,...>(...di ti xi,...){...stk;...}
*)
and type_function ?(add_dirs = false) env (ctx: P4light.coq_StmtContext) info return name t_params params body : P4light.coq_Declaration * coq_P4Type =
  let env = Checker_env.push_scope env in
  let (paramctx: P4light.coq_ParamContextDeclaration), (kind: P4light.coq_FunctionKind) =
    match ctx with
    | StmtCxMethod _ -> ParamCxDeclMethod, FunExtern
    | StmtCxFunction _ -> ParamCxDeclFunction, FunFunction
    | StmtCxAction -> ParamCxDeclAction, FunAction
    | _ -> failwith "bad context for function"
  in
  let body_env = Checker_env.insert_type_vars t_params env in
  let params_typed = type_params body_env (ParamCxRuntime paramctx) params in
  let params_body =
    if add_dirs
    then List.map ~f:add_direction params
    else params
  in
  let return_type = return |> translate_type env in
  let body_env = insert_params body_env params_body in
  let body_stmt_typed, _ = type_block body_env ctx body.tags body in
  let body_typed : P4light.coq_Block =
    match body_stmt_typed, return_type with
    | MkStatement (_, StatBlock blk, _), TypVoid
    | MkStatement (_, StatBlock blk, StmVoid), _ ->
      blk
    | MkStatement (_, StatBlock blk, StmUnit), non_void ->
      failwith "function body does not return a value of the required type"
    | _ ->
      failwith "bug: expected BlockStatement"
  in
  let funtype =
    MkFunctionType (t_params,
                    params_typed,
                    kind,
                    return_type) in
  let fn_typed : P4light.coq_Declaration =
    DeclFunction (info,
                  return_type,
                  name,
                  t_params,
                  params_typed,
                  body_typed) in
  fn_typed, TypFunction funtype

(* Section 7.2.9.1 *)
and type_extern_function env info annotations return name t_params params =
  let return = return |> translate_type env in
  let env' = Checker_env.insert_type_vars t_params env in
  let params_typed, wildcards =
    type_params' ~gen_wildcards:true env' (ParamCxRuntime ParamCxDeclMethod) params in
  let typ: coq_FunctionType =
    MkFunctionType (t_params @ wildcards, params_typed, FunExtern, return)
  in
  let fn_typed: P4light.coq_Declaration =
    DeclExternFunction (info, return, name, t_params @ wildcards, params_typed)
  in
  fn_typed, Checker_env.insert_type_of ~shadow:true (BareName name) (TypFunction typ) env

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
  let var_typed : P4light.coq_Declaration =
    DeclVariable (info, expected_typ, name, init_typed)
  in
  let env = Checker_env.insert_dir_type_of ~shadow:true (BareName name) expected_typ InOut env in
  var_typed, env

(* Section 12.11 *)
and type_value_set env ctx info annotations typ size name =
  let element_type = translate_type env typ in
  let size_typed = type_expression env ExprCxConstant size in
  let size_typed = compile_time_eval_bigint env size_typed in
  let env = Checker_env.insert_type_of (BareName name) (TypSet element_type) env in
  let value_set : P4light.coq_Declaration =
    DeclValueSet (info, element_type, size_typed, name)
  in
  value_set, env

(* Section 13.1 *)
and type_action env tags annotations name params body =
  let fn_typed, fn_env =
    type_function ~add_dirs:true
      env StmtCxAction tags
      (Surface.Type.Void { tags = P4info.dummy }) name [] params body
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
      let action: P4light.coq_Declaration =
        DeclAction (info, name, data_params, ctrl_params, body)
      in
      action, action_type
    | _ -> failwith "expected function declaration"
  in
  begin match Checker_env.find_type_of_opt (BareName name) env with
  | None
  | Some (TypAction _, _) -> ()
  | Some (other_type, _) -> failwith "cannot shadow with action" (*~other_type:(other_type:coq_P4Type)]*)
  end;
  action_typed,
  Checker_env.insert_type_of ~shadow:true (BareName name) action_type env

(* Section 13.2 *)
and type_table env ctx info annotations name properties : P4light.coq_Declaration * Checker_env.t =
  type_table' env ctx info annotations name None [] None None None properties

and type_keys env ctx keys =
  let expr_ctx = expr_ctxt_of_decl_ctxt ctx in
  let type_key key: P4light.coq_TableKey =
    let {key; match_kind; annotations; tags}: Table.key = key in
    match Checker_env.find_type_of_opt (BareName match_kind) env with
    | Some (TypMatchKind, _) ->
      let expr_typed = type_expression env expr_ctx key in
      MkTableKey (tags, expr_typed, match_kind)
    | _ ->
     failwith "invalid match_kind" (*~match_kind:match_kind.str]*)
  in
  List.map ~f:type_key keys

and type_table_actions env ctx key_types actions =
  let expr_ctx = expr_ctxt_of_decl_ctxt ctx in
  let type_table_action (action: Table.action_ref) : P4light.coq_TableActionRef =
    let name = action.name in
    let data_params =
      match Checker_env.find_type_of_opt name env with
      | Some (TypAction (data_params, _), _) ->
        data_params
      | _ ->
       failwith "invalid action" (*~action:(action.name: P4name.t)]*)
    in
    (* Below should fail if there are control plane arguments *)
    let params_args = match_params_to_args env action.tags data_params action.args in
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
    let pre_ref: P4light.coq_TablePreActionRef = 
      MkTablePreActionRef (name, args_typed)
    in
    MkTableActionRef (action.tags, pre_ref, fst @@ Checker_env.find_type_of name env)
  in
  let action_typs = List.map ~f:type_table_action actions in
  (* Need to fail in the case of duplicate action names *)
  let action_names = List.map ~f:(fun a -> a.name) actions in
  List.zip_exn action_names action_typs

and type_table_entry env ctx key_typs action_map (entry: Table.entry) : P4light.coq_TableEntry =
  let expr_ctx = expr_ctxt_of_decl_ctxt ctx in
  let matches_typed = check_match_product env expr_ctx entry.matches key_typs in
  let action_ref_typed = type_action_ref env ctx action_map entry.action in
  MkTableEntry (entry.tags, matches_typed, action_ref_typed)

and type_table_entries env ctx entries key_typs action_map =
  List.map ~f:(type_table_entry env ctx key_typs action_map) entries

(* syntactic equality of expressions *)
and expr_eq env (expr1: P4light.coq_Expression) (expr2: P4light.coq_Expression) : bool =
  let key_val_eq ((k1, v1)) ((k2, v2)) =
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
  | ExpName (n1, _), ExpName (n2, _)
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
  | ExpBinaryOp (b1, l1, r1),
    ExpBinaryOp (b2, l2, r2)
    -> b1 = b2 && expr_eq env l1 l2 && expr_eq env r1 r2
  | ExpCast (t1, e1), ExpCast (t2, e2)
    -> type_equality env [] t1 t2 && expr_eq env e1 e2
  | ExpTypeMember (n1, s1),
    ExpTypeMember (n2, s2)
    -> P4string.eq n1 n2 && P4string.eq s1 s2
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
  | _ -> false

and expr_of_action_ref (aref : Table.action_ref) =
  let open Expression in
  let func = aref.name in
  FunctionCall { func = Name { name = func; tags = P4name.name_tags func };
                 type_args = [];
                 args = aref.args;
                 tags = aref.tags }

and type_action_ref env ctx
    (action_map : (P4name.t * P4light.coq_TableActionRef) list)
    action_ref : P4light.coq_TableActionRef =
  let expr_ctx: P4light.coq_ExprContext = ExprCxTableAction in
  let action_expr = expr_of_action_ref action_ref in
  let action_expr_typed = type_expression env expr_ctx action_expr in
  match preexpr_of_expr action_expr_typed with
  | ExpFunctionCall (MkExpression (_, (ExpName (action_name, _)), _, _), [], args) ->
    begin match List.Assoc.find ~equal:P4name.name_eq action_map action_name with
      | None -> failwith "couldn't find action in action_map"
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
               | None -> failwith "action argument is not compile-time known"
               (* is there a way to convert from values to expressions?
                * this seems wasteful... *)
               | Some _ -> true
             end
        then
          MkTableActionRef (Expression.tags action_expr,
                            MkTablePreActionRef (action_name, args),
                            fst @@ Checker_env.find_type_of action_name env)
        else failwith "action's arguments do not match the table actions property"
    end
  | ExpName (action_name, _) ->
     let acts = List.map ~f:(fun (n, a) -> P4name.name_only n, a) action_map in
     let act = P4name.name_only action_name in
    if not @@ List.Assoc.mem ~equal:(=) acts act
    then failwith "couldn't find action in action_map";
    MkTableActionRef (Expression.tags action_expr,
                      MkTablePreActionRef (action_name, []),
                      type_of_expr action_expr_typed)
  | e ->
    failwith "couldn't type action as functioncall"

and type_default_action
    env ctx (action_map : (P4name.t * P4light.coq_TableActionRef) list)
    action_expr : P4light.coq_TableActionRef =
  type_action_ref env ctx action_map action_expr

and keys_actions_ok keys actions =
  match keys with
  | Some [] -> true
  | Some ks -> List.length actions > 0
  | None -> List.length actions > 0

and type_table' env ctx info annotations (name: P4string.t) key_types action_map entries_typed size default_typed properties =
  let open Surface.Table in
  match properties with
  | Key { keys; tags } :: rest ->
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
        failwith "multiple key properties in table?" (*~name:name.str]*)
    end
  | Actions { actions; tags } :: rest ->
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
        type_table' env ctx tags annotations
          name
          key_types
          action_map
          entries_typed
          size
          default_typed
          rest
    end
  | Entries { entries; tags } :: rest ->
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
  | DefaultAction act :: rest ->
    begin match default_typed with
      | None ->
        let default_typed = type_default_action env ctx action_map act.action in
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
    let _ = assert_numeric (Expression.tags value) (type_of_expr value_typed) in
    let size = compile_time_eval_expr env value_typed in
    begin match size with
      | Some (ValInteger size) ->
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
                         else failwith "Table must have a non-empty actions property" end
                       |> List.map ~f:fst
                       |> List.map ~f:P4name.p4string_name_only
    in
    let action_enum_name = {name with str="action_list_" ^ name.str} in
    let action_enum_typ = TypEnum (action_enum_name, None, action_names) in
    let key =
      match key_types with
      | Some ks -> ks
      | None -> failwith "no key property in table?"
    in
    (* If the key property is empty or missing, there's no look up table. *)
    let entries_typed =
      match key with
      | [] -> Some []
      | _ -> entries_typed
    in
    (* Populate environment with action_enum *)
    (* names of action list enums are "action_list_<<table name>>" *)
    let env =
      Checker_env.insert_type (BareName action_enum_name)
        action_enum_typ env
    in
    let hit_field : P4string.t * coq_P4Type =
      ({tags=P4info.dummy; str="hit"}, TypBool) in
    let miss_field : P4string.t * coq_P4Type =
      ({tags=P4info.dummy; str="miss"}, TypBool) in
    (* How to represent the type of an enum member *)
    let run_field : P4string.t * coq_P4Type =
      ({tags=P4info.dummy; str="action_run"}, action_enum_typ) in
    let apply_result_typ = TypStruct [hit_field; miss_field; run_field] in
    (* names of table apply results are "apply_result_<<table name>>" *)
    let result_typ_name = {name with str = "apply_result_" ^ name.str} in
    let env = Checker_env.insert_type (BareName result_typ_name) apply_result_typ env in
    let table_typ = TypTable result_typ_name in
    let table_typed : P4light.coq_Declaration =
      DeclTable (info,
                 name,
                 key,
                 List.map ~f:snd action_map,
                 entries_typed,
                 default_typed,
                 size,
                 [])
    in
    table_typed, Checker_env.insert_type_of ~shadow:true (BareName name) table_typ env

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

and type_field env field =
  let open Surface.Declaration in
  let raw_typ = translate_type env field.typ in 
  let typ = saturate_type env raw_typ in
  let pre_field : P4light.coq_DeclarationField =
    MkDeclarationField (field.tags, raw_typ, field.name) in
  let pre_record_field : coq_FieldType =
    (field.name, typ) in
  pre_field, pre_record_field

and type_header_union_field env field =
  let open Surface.Declaration in
  let typ = translate_type env field.typ in
  match saturate_type env typ with
  | TypHeader _ ->
    type_field env field
  | _ -> failwith "header union fields must have header type"
(*~field:((field_info, field): Surface.Declaration.field)]*)

(* Section 7.2.3 *)
and type_header_union env tags annotations name fields =
  let fields_typed, type_fields =
    List.unzip @@ List.map ~f:(type_header_union_field env) fields
  in
  let header_typ = TypHeaderUnion type_fields in
  if not @@ is_well_formed_type env header_typ
  then failwith "bad header type";
  let env = Checker_env.insert_type (BareName name) header_typ env in
  let header: P4light.coq_Declaration =
    DeclHeaderUnion (tags, name, fields_typed) in
  header, env

(* Section 7.2.5 *)
and type_struct env tags annotations (name: P4string.t) fields =
  let fields_typed, type_fields = List.unzip @@ List.map ~f:(type_field env) fields in
  let struct_typ = TypStruct type_fields in
  if not @@ is_well_formed_type env struct_typ
  then failwith "bad struct type";
  let env =
    Checker_env.insert_type (BareName name) struct_typ env in
  let struct_decl: P4light.coq_Declaration =
    DeclStruct (tags, name, fields_typed) in
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
and type_error env info members : P4light.coq_Declaration * Checker_env.t =
  let add_err env (e: P4string.t) =
    let name: P4name.t =
      QualifiedName ([], {tags = e.tags; str = "error." ^ e.str})
    in
    env
    |> Checker_env.insert_type_of name TypError
    |> Checker_env.insert_const name (ValError e)
  in
  let env = List.fold_left ~f:add_err ~init:env members in
  DeclError (info, members), env

(* Section 7.1.3 *)
and type_match_kind env info members : P4light.coq_Declaration * Checker_env.t =
  let add_mk env (e: P4string.t) =
    let name: P4name.t = QualifiedName ([], e) in
    env
    |> Checker_env.insert_type_of name TypMatchKind
    |> Checker_env.insert_const name (ValMatchKind e)
  in
  let env = List.fold_left ~f:add_mk ~init:env members in
  DeclMatchKind (info, members), env

(* Section 7.2.1 *)
and type_enum env info annotations (name: P4string.t) members : P4light.coq_Declaration * Checker_env.t =
  let enum_typ =
    TypEnum (name, None, members)
  in
  let add_member env (member: P4string.t) =
    let member_name: P4name.t =
      QualifiedName ([], {tags = member.tags;
                          str = name.str ^ "." ^ member.str}) in
    let enum_val: P4light.coq_Value = ValEnumField (name, member) in
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
  : P4light.coq_Declaration * Checker_env.t =
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
      let expr_of_val = val_to_literal value in
      let enum_val: P4light.coq_Value = ValEnumField (name, member) in
      env
      |> Checker_env.insert_type_of member_name enum_type
      |> Checker_env.insert_const
        member_name
        enum_val, members_typed @ [member, expr_of_val]
    | None -> failwith "could not evaluate enum member"
  in
  let env = Checker_env.insert_type (QualifiedName ([], name)) enum_type env in
  let env, members = List.fold_left ~f:add_member ~init:(env, []) members in
  DeclSerializableEnum (info, enum_type, name, members), env

and type_extern_object env info annotations obj_name t_params methods =
  let extern_type = TypExtern obj_name in
  let extern_methods: P4light.coq_ExternMethods = {type_params = t_params; methods = []; abst_methods = []} in
  let env' = env
             |> Checker_env.insert_type_vars t_params
             |> Checker_env.insert_type (BareName obj_name) extern_type
             |> Checker_env.insert_extern (BareName obj_name) extern_methods
  in
  let consume_method (constructors, cstr_wildcards, methods) m =
    match m with
    | MethodPrototype.Constructor { annotations; name = cname; params; tags } ->
      if P4string.neq cname obj_name then failwith "Constructor name and type name disagree";
      let params_typed, param_wildcards = 
        type_constructor_params env' ParamCxDeclMethod params in
      let constructor_typed: P4light.coq_MethodPrototype =
        ProtoConstructor (tags, cname, params_typed)
      in
      (constructor_typed :: constructors, param_wildcards::cstr_wildcards, methods)
    | MethodPrototype.Method { annotations; return; name;
                               type_params = t_params; params; tags }
    | MethodPrototype.AbstractMethod { annotations; return; name;
                                       type_params = t_params; params; tags } ->
      if P4string.eq name obj_name
      then failwith "extern method must have different name from extern"; (*~m:(m: MethodPrototype.t)];*)
      let env' = Checker_env.insert_type_vars t_params env' in
      let params_typed, param_wildcards =
        type_params' ~gen_wildcards:true env' (ParamCxRuntime ParamCxDeclMethod) params in
      let return_typed = translate_type env' return in
      let method_typed: P4light.coq_MethodPrototype =
        match m with
        | Method _ ->
          ProtoMethod (tags, return_typed, name, t_params @ param_wildcards, params_typed)
        | AbstractMethod _ ->
          ProtoAbstractMethod (tags, return_typed, name, t_params @ param_wildcards, params_typed)
        | _ -> failwith "bug"
      in
      (constructors, cstr_wildcards, method_typed :: methods)
  in
  let (cs, cws, ms) = List.fold_left ~f:consume_method ~init:([], [], []) methods in
  let extern_decl: P4light.coq_Declaration =
    DeclExternObject (info, obj_name, t_params, cs @ ms) in
  let is_abst_method (m: P4light.coq_MethodPrototype) = 
    match m with ProtoAbstractMethod _ -> true | _ -> false in
  let extern_methods: P4light.coq_ExternMethods =
    { type_params = t_params;
      methods = List.map ~f:(method_prototype_to_extern_method obj_name) (List.filter ~f:(fun m -> not (is_abst_method m)) ms);
      abst_methods = List.map ~f:(method_prototype_to_extern_method obj_name) (List.filter ~f:is_abst_method ms) }
  in
  let cs_ws = List.zip_exn cs cws in
  let extern_ctors =
    List.map cs_ws ~f:(function
        | ProtoConstructor (_, cname, params_typed), ws ->
           if t_params <> []
           then let generic_args = List.map t_params ~f:(fun ty -> TypTypeName ( ty)) in
                TypConstructor (t_params, ws, params_typed,
                                TypSpecializedType (extern_type, generic_args))
           else TypConstructor (t_params, ws, params_typed, extern_type)
        | _ -> failwith "bug: expected constructor")
  in
  let env = Checker_env.insert_type (BareName obj_name) extern_type env in
  let env = Checker_env.insert_extern (BareName obj_name) extern_methods env in
  let env = List.fold extern_ctors ~init:env
              ~f:(fun env t -> Checker_env.insert_type_of
                                 ~shadow:true
                                 (BareName obj_name)
                                 t
                                 env)
  in
  extern_decl, env

and method_prototype_to_extern_method extern_name (m: P4light.coq_MethodPrototype)
  : P4light.coq_ExternMethod =
  match m with
  | ProtoConstructor (_, name, params) ->
    { name = name;
      typ = MkFunctionType ([], params, FunExtern, TypTypeName ( extern_name)) }
  | ProtoAbstractMethod (_, return, name, type_params, params)
  | ProtoMethod (_, return, name, type_params, params) ->
    { name = name;
      typ = MkFunctionType (type_params, params, FunExtern, return) }

(* Section 7.3 *)
and type_type_def env ctx tags annotations name typ_or_decl =
  match typ_or_decl with
  | Left typ ->
    let typ = translate_type env typ in
    let typedef_typed: P4light.coq_Declaration =
      DeclTypeDef (tags, name, Coq_inl typ)
    in
    typedef_typed, Checker_env.insert_type (BareName name) typ env
  | Right decl ->
    let decl_name = Declaration.name decl in
    let decl_typed, env' = type_declaration env ctx decl in
    let decl_typ = Checker_env.resolve_type_name (BareName decl_name) env' in
    let typedef_typed: P4light.coq_Declaration =
      DeclTypeDef (tags, name, Coq_inr decl_typed) in
    typedef_typed, Checker_env.insert_type (BareName name) decl_typ env'

and type_new_type env ctx info annotations name typ_or_decl =
  match typ_or_decl with
  | Left typ ->
    let typ = translate_type env typ in
    let newtype_typed: P4light.coq_Declaration =
      DeclNewType (info, name, Coq_inl typ) in
    let newtype = TypNewType (name, typ) in
    newtype_typed, Checker_env.insert_type (BareName name) newtype env
  | Right decl ->
    let decl_name = Declaration.name decl in
    let decl_typed, env = type_declaration env ctx decl in
    let decl_typ = Checker_env.resolve_type_name (BareName decl_name) env in
    let newtype_typed: P4light.coq_Declaration =
      DeclNewType (info, name, Coq_inr decl_typed) in
    let newtype = TypNewType (name, decl_typ) in
    newtype_typed, Checker_env.insert_type (BareName name) newtype env

(* Section 7.2.11.2 *)
and type_control_type env info annotations name t_params params =
  let body_env = Checker_env.insert_type_vars t_params env in
  let params_typed, wildcards =
    type_params' ~gen_wildcards:true body_env (ParamCxRuntime ParamCxDeclControl) params in
  let ctrl_decl: P4light.coq_Declaration =
    DeclControlType (info, name, t_params @ wildcards, params_typed) in
  let ctrl_typ = TypControl (MkControlType (t_params @ wildcards, params_typed)) in
  ctrl_decl, Checker_env.insert_type (BareName name) ctrl_typ env

(* Section 7.2.11 *)
and type_parser_type env info annotations name t_params params =
  let body_env = Checker_env.insert_type_vars t_params env in
  let params_typed, wildcards =
    type_params' ~gen_wildcards:true body_env (ParamCxRuntime ParamCxDeclParser) params in
  let parser_decl: P4light.coq_Declaration =
    DeclParserType (info, name, t_params @ wildcards, params_typed) in
  let parser_typ = TypParser (MkControlType (t_params @ wildcards, params_typed)) in
  parser_decl, Checker_env.insert_type (BareName name) parser_typ env

(* Section 7.2.12 *)
and type_package_type env info annotations name t_params params =
  begin match Checker_env.resolve_type_name_opt (BareName name) env with
  | None
  | Some (TypPackage _) -> ()
  | Some other_type -> failwith "cannot shadow object with package"
  end;
  begin match Checker_env.find_type_of_opt (BareName name) env with
  | None
  | Some (TypConstructor (_, _, _, TypPackage _), _) -> ()
  | Some other_type -> failwith "cannot shadow object with package constructor"
  end;
  let body_env = Checker_env.insert_type_vars t_params env in
  let params_typed, wildcard_params =
    type_params' ~gen_wildcards:true body_env (ParamCxConstructor ParamCxDeclPackage) params in
  let pkg_decl: P4light.coq_Declaration =
    DeclPackageType (info, name, t_params, params_typed)
  in
  let pkg_typ = TypPackage (t_params, wildcard_params, params_typed) in
  let ret     = TypPackage ([],       wildcard_params, params_typed) in
  let ctor_typ = TypConstructor (t_params, wildcard_params, params_typed, ret) in
  let env' =
    env
    |> Checker_env.insert_type_of ~shadow:true (BareName name) ctor_typ
    |> Checker_env.insert_type ~shadow:true (BareName name) pkg_typ
  in
  pkg_decl, env'

and check_param_shadowing params constructor_params =
  let open Surface.Parameter in 
  let all_params = params @ constructor_params in
  let names = List.map ~f:(fun p -> p.variable) all_params in
  match List.find_a_dup names
          ~compare:(fun (x:P4string.t) y ->
              String.compare x.str y.str)
  with
  | Some dup -> failwith "duplicate parameter" (*~dup:(dup.str)]*)
  | None -> ()

and type_declaration (env: Checker_env.t) (ctx: coq_DeclContext) (decl: Surface.Declaration.t) : P4light.coq_Declaration * Checker_env.t =
  match decl with
  | Constant { annotations; typ; name; value; tags } ->
    type_constant env ctx tags annotations typ name value
  | Instantiation { annotations; typ; args; name; init; tags } ->
    let decl_typed, instance_type =
      type_instantiation env ctx tags annotations typ args name init
    in
    decl_typed, Checker_env.insert_type_of (BareName name) instance_type env
  | Parser { annotations; name; type_params; params; constructor_params; locals; states; tags } ->
    check_param_shadowing params constructor_params;
    type_parser env tags name annotations type_params params constructor_params locals states
  | Control { annotations; name; type_params; params; constructor_params; locals; apply; tags } ->
    check_param_shadowing params constructor_params;
    type_control env tags name annotations type_params params constructor_params locals apply
  | Function { return; name; type_params; params; body; tags } ->
    check_param_shadowing params [];
    let ret_type = translate_type env return in
    let ctx: coq_StmtContext = StmtCxFunction ret_type in
    let decl_typed, fn_type =
      type_function env ctx tags return name type_params params body
    in
    decl_typed, Checker_env.insert_type_of (BareName name) fn_type env
  | Action { annotations; name; params; body; tags } ->
    check_param_shadowing params [];
    type_action env tags annotations name params body
  | ExternFunction { annotations; return; name; type_params; params; tags } ->
    check_param_shadowing params [];
    type_extern_function env tags annotations return name type_params params
  | Variable { annotations; typ; name; init; tags } ->
    type_variable env ctx tags annotations typ name init
  | ValueSet { annotations; typ; size; name; tags } ->
    type_value_set env ctx tags annotations typ size name
  | Table { annotations; name; properties; tags } ->
    type_table env ctx tags annotations name properties
  | Header { annotations; name; fields; tags } ->
    type_header env tags annotations name fields
  | HeaderUnion { annotations; name; fields; tags } ->
    type_header_union env tags annotations name fields
  | Struct { annotations; name; fields; tags } ->
    type_struct env tags annotations name fields
  | Error { members; tags } ->
    type_error env tags members
  | MatchKind { members; tags } ->
    type_match_kind env tags members
  | Enum { annotations; name; members; tags } ->
    type_enum env tags annotations name members
  | SerializableEnum { annotations; typ; name; members; tags } ->
    type_serializable_enum env ctx tags annotations typ name members
  | ExternObject { annotations; name; type_params; methods; tags } ->
    type_extern_object env tags annotations name type_params methods
  | TypeDef { annotations; name; typ_or_decl; tags } ->
    type_type_def env ctx tags annotations name typ_or_decl
  | NewType { annotations; name; typ_or_decl; tags } ->
    type_new_type env ctx tags annotations name typ_or_decl
  | ControlType { annotations; name; type_params; params; tags } ->
    check_param_shadowing params [];
    type_control_type env tags annotations name type_params params
  | ParserType { annotations; name; type_params; params; tags } ->
    check_param_shadowing params [];
    type_parser_type env tags annotations name type_params params
  | PackageType { annotations; name; type_params; params; tags } ->
    check_param_shadowing params [];
    type_package_type env tags annotations name type_params params

and type_declarations env ctx decls: P4light.coq_Declaration list * Checker_env.t =
  let f (decls_typed, env) decl =
    let decl_typed, env = type_declaration env ctx decl in
    decls_typed @ [decl_typed], env
  in
  let decls, env = List.fold_left ~f ~init:([], env) decls in
  decls, env

(* Entry point function for type checker *)
let check_program renamer (program:Surface.program) : Checker_env.t * P4light.program =
  let Program top_decls = program in
  let initial_env = Checker_env.empty_with_renamer renamer in
  let prog, env = type_declarations initial_env DeclCxTopLevel top_decls in
  env, prog
