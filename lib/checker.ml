open Types
open Typed
open Util
open Env
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

let rec is_lvalue (_, expr) =
  let open Types.Expression in
  match expr with
  | Name _ -> true
  | ExpressionMember { expr = lvalue; _ }
  | ArrayAccess { array = lvalue; _ }
  | BitStringAccess { bits = lvalue; _ } ->
     is_lvalue lvalue
  | _ -> false

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
     option_map (Ops.interp_cast ~type_lookup typ) expr_val
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
     | Some es -> Some (Prog.Value.VStruct { fields = es })
     | None -> None
     end
  | BitStringAccess{bits; hi; lo} ->
     begin match compile_time_eval_expr env bits with
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
  | Extern {type_params; _}
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
and saturate_type (env: CheckerEnv.t) (typ: Typed.Type.t) : Typed.Type.t =
  let open Type in
  let saturate_field env (field: RecordType.field) =
    {field with typ = saturate_type env field.typ}
  in
  let saturate_rec env ({fields;} : RecordType.t) : RecordType.t =
    {fields = List.map ~f:(saturate_field env) fields;}
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
  and saturate_constructor env (ctor: ConstructorType.t) : ConstructorType.t =
    { type_params = ctor.type_params;
      parameters = List.map ~f:(saturate_construct_param env) ctor.parameters;
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
      Extern (saturate_extern env extern)
  | Function func ->
      Function (saturate_function env func)
  | Action action ->
    Action (saturate_action env action)
  | Constructor ctor ->
     Constructor (saturate_constructor env ctor)

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
     let arg_typed = type_expression env arg in
     let param_type = param.Parameter.typ in
     begin match solve_types env [] unknowns param_type (snd arg_typed).typ with
     | Some arg_constraints ->
        let constraints = merge_constraints env constraints arg_constraints in
        gen_all_constraints env unknowns more constraints
     | None -> raise_s [%message "could not solve type equality t1 = t2"
                           ~t1:(param_type: Typed.Type.t)
                           ~t2:((snd arg_typed).typ: Typed.Type.t)
                           ~unknowns:(unknowns: string list)
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
       CheckerEnv.insert_type (BareName (Info.dummy, type_var)) arg env, (type_var, arg) :: args, unknowns
    | None ->
       CheckerEnv.insert_type_var (BareName (Info.dummy, type_var)) env, args, type_var :: unknowns
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
  |> option_map List.rev

and solve_constructor_params_equality env equiv_vars unknowns ps1 ps2 =
  let open Typed.ConstructParam in
  let solve_params (p1, p2) =
    solve_types env equiv_vars unknowns p1.typ p2.typ
  in
  solve_lists env unknowns ps1 ps2 ~f:solve_params

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

and solve_constructor_type_equality env equiv_vars unknowns ctor1 ctor2 =
  let open ConstructorType in
  match List.zip ctor1.type_params ctor2.type_params with
  | Ok param_pairs ->
     let equiv_vars' = equiv_vars @ param_pairs in
     merge_solutions env (solve_types env equiv_vars' unknowns ctor1.return ctor2.return)
                         (solve_constructor_params_equality env equiv_vars' unknowns ctor1.parameters ctor2.parameters)
  | Unequal_lengths -> None


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
                (t1: Typed.Type.t)
                (t2: Typed.Type.t)
  : soln =
  let t1 = reduce_type env t1 in
  let t2 = reduce_type env t2 in
  begin match t1, t2 with
    | TypeName (QualifiedName _), _
    | _, TypeName (QualifiedName _) ->
        failwith "Name in saturated type?"

    | SpecializedType _, _
    | _, SpecializedType _ ->
       raise_s [%message "Stuck specialized type?" ~t1:(t1: Typed.Type.t)
                                                   ~t2:(t2: Typed.Type.t)]

    | TypeName (BareName (_, tv1)), TypeName (BareName (i2, tv2)) ->
        if type_vars_equal_under env equiv_vars tv1 tv2
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

    | Record rec1, Record rec2
    | Struct rec1, Record rec2
    | Header rec1, Record rec2 ->
       solve_record_type_equality env equiv_vars unknowns rec1 rec2

    | Struct {fields; _}, List {types}
    | Header {fields; _}, List {types} ->
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

    | Constructor ctor1, Constructor ctor2 ->
        solve_constructor_type_equality env equiv_vars unknowns ctor1 ctor2

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
       let typ, dir = CheckerEnv.find_type_of name env in
       { expr = E.Name name;
         typ = typ;
         dir = dir }
    | ArrayAccess { array; index } ->
       type_array_access env array index
    | BitStringAccess { bits; lo; hi } ->
       type_bit_string_access env bits lo hi
    | List { values } ->
       type_list env values
    | Record { entries } ->
       type_record env entries
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

and eval_to_int env expr =
  expr
  |> type_expression env
  |> compile_time_eval_bigint env
  |> Bigint.to_int_exn

and translate_type : CheckerEnv.t -> string list -> Types.Type.t -> Typed.Type.t =
  fun env vars typ ->
  let open Types.Type in
  (* let eval e =
    Eval.eval_expression ([],[]) (CheckerEnv.eval_env_of_t env) Eval.empty_state e
    |> fun (a,_,b) -> (a,b)
  in *)
  (* let get_int_from_bigint num =
    begin match Bigint.to_int num with
      | Some n -> n;
      | None -> failwith "numeric type parameter is too large"
    end in *)
  match snd typ with
  | Bool -> Bool
  | Error -> Error
  | Integer -> Integer
  | String -> String
  | IntType e -> Int {width = eval_to_int env e}
  | BitType e -> Bit {width = eval_to_int env e}
  | VarBit e -> VarBit {width = eval_to_int env e}
  | TypeName ps -> TypeName ps
  | SpecializedType {base; args} ->
      SpecializedType {base = (translate_type env vars base);
                       args = (List.map ~f:(translate_type env vars) args)}
  | HeaderStack {header=ht; size=e}
    -> let hdt = translate_type env vars ht in
    let len = 
      e
      |> type_expression env
      |> compile_time_eval_bigint env
      |> Bigint.to_int_exn in
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
  | Record {fields; _}
  | Header {fields; _}
  | HeaderUnion {fields; _}
  | Struct {fields; _} ->
    let open RecordType in
    List.for_all ~f:(fun field -> field.typ |> is_well_formed_type env) fields
  | Action { data_params=dps; ctrl_params=cps } ->
    let res1 : bool = (are_param_types_well_formed env dps) in
    let res2 : bool = (are_construct_params_types_well_formed env cps) in
    res1 && res2

  (* Type names *)
  | TypeName name ->
    begin match CheckerEnv.resolve_type_name_opt name env with
    | None -> false
    | Some _ -> true (* Unsure of what to do in this case *)
    end
  | Table {result_typ_name=name} ->
    begin match CheckerEnv.resolve_type_name_opt (BareName (Info.dummy, name)) env with
    | None -> false
    | Some _ -> true (* Unsure of what to do in this case *)
    end
  | NewType {name; typ} ->
     is_well_formed_type env typ

  (* Polymorphic types *)
  | Function {type_params=tps; parameters=ps; return=rt} ->
    let env = CheckerEnv.insert_type_vars tps env in
    are_param_types_well_formed env ps && is_well_formed_type env rt
  | Constructor {type_params=tps; parameters=ps; return=rt} ->
    let env = CheckerEnv.insert_type_vars tps env in
    are_construct_params_types_well_formed env ps && is_well_formed_type env rt
  | Extern {type_params=tps; methods=methods} ->
    let env = CheckerEnv.insert_type_vars tps env in
    let open ExternType in
    let folder (env,result) m =
      if is_well_formed_type env (Type.Function m.typ) then
        (CheckerEnv.insert_type_of (BareName (Info.dummy, m.name))
           (Type.Function m.typ) env,result)
      else (env,false) in
    List.fold_left ~f:folder ~init:(env,true) methods |> snd
  | Parser {type_params=tps; parameters=ps;_}
  | Control {type_params=tps; parameters=ps;_} ->
    let env = CheckerEnv.insert_type_vars tps env in
    are_param_types_well_formed env ps
  | Package {type_params=tps; parameters=cps;_} ->
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

and type_param env (param_info, param : Types.Parameter.t) : Prog.TypeParameter.t =
  let typ = translate_type env [] param.typ in
  if is_well_formed_type env typ
  then
    let opt_value_typed =
      match param.opt_value with
      | Some value ->
         let value_typed = type_expression env value in
         assert_type_equality env param_info (snd value_typed).typ typ;
         Some value_typed
      | None -> None
    in
    (Info.dummy, { annotations = param.annotations;
                      direction = translate_direction param.direction;
                      typ = typ;
                      variable = param.variable;
                      opt_value = opt_value_typed })
  else raise_s [%message "Parameter type is not well-formed"
                   ~param:((param_info, param): Types.Parameter.t)]

and type_params env params =
  List.map ~f:(type_param env) params

and type_constructor_param env (param: Types.Parameter.t) : Prog.TypeParameter.t =
  if (snd param).direction <> None
  then raise_s [%message "Constructor parameters must be directionless"
                   ~param:(param: Types.Parameter.t)]
  else type_param env param

and type_constructor_params env params =
  List.map ~f:(type_constructor_param env) params

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
  match reduce_type env (snd bits_typed).typ with
  | Int { width }
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
and type_list env values : Prog.Expression.typed_t =
  let typed_exprs = List.map ~f:(type_expression env) values in
  let types = List.map ~f:(fun e -> (snd e).typ) typed_exprs in
  { expr = List { values = typed_exprs };
    typ = Type.List { types };
    dir = Directionless }

and type_key_val env ((info, entry): Types.KeyValue.t) : Prog.KeyValue.t =
  info,
  { key = entry.key;
    value = type_expression env entry.value }
  
and type_record env entries : Prog.Expression.typed_t =
  let entries_typed = List.map ~f:(type_key_val env) entries in
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

and coerce_binary_op_args env op l r =
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
  if op <> Op.Shl && op <> Op.Shr
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
  | Tuple { types }
  | List { types } ->
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
  if is_positive_numeric env left_arg && is_positive_numeric env right_arg
  then ()
  else raise_s [%message "arguments to division must be positive"
                   ~divisor:(right_arg:Prog.Expression.t)
                   ~dividend:(left_arg:Prog.Expression.t)];

and type_binary_op env (op_info, op) (l, r) : Prog.Expression.typed_t =
  let open Op in
  let open Typed.Type in
  let typed_l, typed_r = coerce_binary_op_args env op l r in
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
       | _, _ -> raise_s [%message "this binop unimplemented"
                             ~l_typ:(l_typ:Typed.Type.t)
                             ~r_typ:(r_typ:Typed.Type.t)]
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
       | Bit { width = l }, Bit { width = r }
       | Int { width = l }, Bit { width = r }
       | Bit { width = l }, Int { width = r }
       | Int { width = l }, Int { width = r } -> Bit { width = l + r }
       | Int { width = _ }, _
       | Bit { width = _ }, _ -> raise_mismatch (info r) "bit<> or int<>" r_typ
       | _, _ -> raise_mismatch (info l) "bit<> or int<>" l_typ
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
       | Integer, _ -> raise_mismatch (info r) "arbitrary precision integer" r_typ
       | _, _ -> raise_mismatch (info l) "arbitrary precision integer" l_typ
       end
    | Shl | Shr ->
       begin match l_typ, is_nonnegative_numeric env typed_r with
       | Bit _, true
       | Int _, true -> l_typ
       | _, true -> raise_s [%message "bad left hand argument to shift" ~l_typ:(l_typ: Typed.Type.t)]
       | _ -> raise_s [%message "bad right hand argument to shift" ~typed_r:(typed_r: Prog.Expression.t)]
       end
  in
  { expr = BinaryOp { op = (op_info, op); args = (typed_l, typed_r) };
    typ = typ;
    dir = dir }

(* See section 8.9.2 "Explicit casts" *)
and cast_ok env original_type new_type =
  let open Typed.Type in
  match original_type, new_type with
  | Bit { width = 1 }, Bool
  | Bool, Bit { width = 1 }
  | Int { width = _ }, Bit { width = _ }
  | Bit { width = _ }, Int { width = _ }
  | Bit { width = _ }, Bit { width = _ }
  | Int { width = _ }, Int { width = _ }
  | Integer, Bit { width = _ }
  | Integer, Int { width = _ } ->
     true
  | Enum { name; typ = Some t; members }, t'
  | t', Enum { name; typ = Some t; members } ->
     type_equality env t t'
  | NewType { name = name1; typ = typ1 },
    NewType { name = name2; typ = typ2 } ->
     type_equality env typ1 new_type
     || type_equality env original_type typ2
  | NewType { name; typ }, t
  | t, NewType { name; typ } ->
     type_equality env typ t
  | Record rec1, Header rec2
  | Record rec1, Struct rec2 ->
     type_equality env new_type original_type
  | _ -> original_type = new_type

(* Section 8.9 *)
and type_cast env typ expr : Prog.Expression.typed_t =
  let expr_typed = type_expression env expr in
  let expr_type = saturate_type env (snd expr_typed).typ in
  let new_type = translate_type env [] typ in
  let new_type_sat = saturate_type env (translate_type env [] typ) in
  if cast_ok env expr_type new_type_sat
  then { dir = Directionless; typ = new_type; expr = Cast {typ = new_type; expr = expr_typed} }
  else raise_s [%message "illegal explicit cast"
                   ~old_type:(expr_type: Typed.Type.t)
                   ~new_type:(new_type_sat: Typed.Type.t)]

(* ? *)
and type_type_member env typ name : Prog.Expression.typed_t =
   let real_name = real_name_for_type_member env typ name in
   let full_type, dir = CheckerEnv.find_type_of real_name env in
   { expr = TypeMember { typ;
                         name = name };
     typ = full_type;
     dir }
     (*
  let typ = translate_type env [] typ in
  let full_typ = saturate_type env typ
  in
      *)

(* Section 8.2
 * -----------
 *
 *       (e, error) ∈ T
 * --------------------------
 * Δ, T, Γ |- error.e : error
 *
 *)
and type_error_member env name : Prog.Expression.typed_t =
  let (e, _) = CheckerEnv.find_type_of (BareName (Info.dummy, "error." ^ (snd name))) env in
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
  | Type.Header { fields; _ } -> fake_fields
  | _ -> []

and type_expression_member_builtin env info typ name : Typed.Type.t =
  let open Typed.Type in
  let fail () =
    raise_unfound_member info (snd name) in
  match typ with
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
     | _ -> fail ()
     end
  | _ -> fail ()

and type_expression_member_function_builtin env info typ name : Typed.Type.t option =
  let open Typed.Type in
  match typ with
  | Control { type_params = []; parameters = ps; _ }
  | Parser { type_params = []; parameters = ps; _ } ->
     begin match snd name with
     | "apply" ->
        Some (Function { type_params = [];
                         parameters = ps;
                         return = Void })
     | _ -> None
     end
  | Table { result_typ_name } ->
     begin match snd name with
     | "apply" ->
        Some (Function { type_params = []; parameters = [];
                         return = TypeName (BareName (Info.dummy, result_typ_name)) })
     | _ -> None
     end
  | Struct _ ->
     begin match snd name with
     | "minSizeInBits" ->
        Some (Function { type_params = []; parameters = []; return = Integer })
     | "minSizeInBytes" ->
        Some (Function { type_params = []; parameters = []; return = Integer })
     | _ -> None
     end
  | Header _ ->
     begin match snd name with
     | "isValid" ->
        Some (Function { type_params = []; parameters = []; return = Bool })
     | "setValid"
     | "setInvalid" ->
        Some (Function { type_params = []; parameters = []; return = Void })
     | "minSizeInBits" ->
        Some (Function { type_params = []; parameters = []; return = Integer })
     | "minSizeInBytes" ->
        Some (Function { type_params = []; parameters = []; return = Integer })
     | _ -> None
     end
  | Array { typ; _ } ->
     begin match snd name with
     | "minSizeInBits" ->
        Some (Function { type_params = []; parameters = []; return = Integer })
     | "minSizeInBytes" ->
        Some (Function { type_params = []; parameters = []; return = Integer })
     | "push_front"
     | "pop_front" ->
        let parameters: Typed.Parameter.t list =
          [{ variable = Info.dummy, "count";
             typ = Integer;
             direction = Directionless;
             annotations = [] }]
        in
        Some (Function { type_params = []; parameters; return = Void })
     | _ -> None
     end
  | HeaderUnion _ ->
     begin match snd name with
     | "isValid" ->
        Some (Function { type_params = []; parameters = []; return = Bool })
     | "minSizeInBits" ->
        Some (Function { type_params = []; parameters = []; return = Integer })
     | "minSizeInBytes" ->
        Some (Function { type_params = []; parameters = []; return = Integer })
     | _ -> None
     end
  | _ -> None

(* Sections 6.6, 8.14 *)
and type_expression_member env expr name : Prog.Expression.typed_t =
  let typed_expr = type_expression env expr in
  let expr_typ = reduce_type env (snd typed_expr).typ in
  let open RecordType in
  let methods = header_methods (snd typed_expr).typ in
  let typ = 
    match expr_typ with
    | Header {fields=fs;_}
    | HeaderUnion {fields=fs;_}
    | Struct {fields=fs;_} ->
       let fs = fs @ methods in
       let matches (f : field) = f.name = snd name in
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
                 ~args:(args: Types.Argument.pre_t list)
                 ~params:(params: Prog.TypeParameter.t list)]

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

(* Section 8.17: Typing Function Calls *)
and type_param_arg env call_info (param, expr: Typed.Parameter.t * Expression.t option) =
  match expr with
  | Some expr ->
     let info, typed_arg = type_expression env expr in
     check_direction env param.direction expr typed_arg.dir;
     assert_type_equality env call_info param.typ typed_arg.typ
  | None ->
     if param.direction <> Out
     then raise_s [%message "don't care argument (underscore) provided for non-out parameter"
                      ~call_site:(call_info: Info.t)
                      ~param:(snd param.variable)]

and type_function_call env call_info func type_args args : Prog.Expression.typed_t =
  let open Prog.Expression in
  let func_typed = resolve_function_overload env func args in
  let func_type = (snd func_typed).typ in
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

and resolve_constructor_overload_by ~f env type_name =
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
  let param_name param = ConstructParam.(param.name) in
  match list_option_flip (List.map ~f:arg_name args) with 
  | Some arg_names ->
     let param_names_ok params =
       let param_names = List.map ~f:param_name params in
       Util.sorted_eq_strings param_names arg_names
     in
     resolve_constructor_overload_by ~f:param_names_ok env type_name
  | None -> 
     let param_count_ok params =
       List.length params = List.length args
     in
     resolve_constructor_overload_by ~f:param_count_ok env type_name

and resolve_function_overload_by ~f env func : Prog.Expression.t =
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
     | _ -> snd @@ type_expression env func
     end
  | ExpressionMember { expr; name } ->
     let expr_typed = type_expression env expr in
     let prog_member = Prog.Expression.ExpressionMember { expr = expr_typed;
                                                          name = name }
     in
     begin match reduce_type env (snd expr_typed).typ with
     | Extern { methods; _ } ->
        let works (meth: Typed.ExternType.extern_method) =
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
           snd @@ type_expression env func
        end
     end
  | _ -> snd @@ type_expression env func

and resolve_function_overload env type_name args =
  let arg_name arg =
    match snd arg with
    | Argument.KeyValue {key; _} -> Some (snd key)
    | _ -> None
  in
  let param_name param = Parameter.(snd param.variable) in
  match list_option_flip (List.map ~f:arg_name args) with 
  | Some arg_names ->
     let param_names_ok params =
       let param_names = List.map ~f:param_name params in
       Util.sorted_eq_strings param_names arg_names
     in
     resolve_function_overload_by ~f:param_names_ok env type_name
  | None -> 
     let param_count_ok params =
       List.length params = List.length args
     in
     resolve_function_overload_by ~f:param_count_ok env type_name

and type_constructor_invocation env info decl_name type_args args : Prog.Expression.t list * Typed.Type.t =
  let open Typed.ConstructorType in
  let type_args = List.map ~f:(translate_type_opt env []) type_args in
  let constructor_type = resolve_constructor_overload env decl_name args in
  let t_params = constructor_type.type_params in
  let prog_params = constructor_params_to_prog_params constructor_type.parameters in
  let params_args = match_params_to_args info prog_params args in
  let type_params_args = infer_constructor_type_args env t_params params_args type_args in
  let env' = CheckerEnv.insert_types type_params_args env in
  let check_arg (param, arg: Prog.TypeParameter.t * Types.Expression.t option) =
    match arg with
    | Some arg ->
       let arg_typed = type_expression env' arg in
       assert_type_equality env' info (snd param).typ (snd arg_typed).typ;
       arg_typed
    | None -> failwith "missing constructor argument"
  in
  let ret = saturate_type env' constructor_type.return in
  let args_typed = List.map ~f:check_arg params_args in
  args_typed, ret

(* Section 14.1 *)
and type_nameless_instantiation env info typ args =
  let open Prog.Expression in
  match snd typ with
  | SpecializedType { base; args = type_args } ->
     begin match snd base with
     | TypeName decl_name ->
        let out_args, out_typ = type_constructor_invocation env info decl_name type_args args in
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
and type_range env lo hi : Prog.Expression.typed_t =
  let lo_typed = type_expression env lo in
  let hi_typed = type_expression env hi in
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

and type_statement (env: CheckerEnv.t) (ctx: StmtContext.t) (stm: Statement.t) : (Prog.Statement.t * CheckerEnv.t) =
  let open Prog.Statement in
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
and type_assignment env ctx lhs rhs =
  let open Prog.Statement in
  if not @@ is_lvalue lhs
  then raise_s [%message "Must be an lvalue"
                   ~lhs:(lhs:Types.Expression.t)]
  else 
    let lhs_typed = type_expression env lhs in
    let rhs_typed = type_expression env rhs in
    ignore (assert_same_type env (info lhs) (info rhs)
              (snd lhs_typed).typ (snd rhs_typed).typ);
    { stmt = Assignment { lhs = lhs_typed; rhs = rhs_typed };
      typ = StmType.Unit },
    env

(* This belongs in an elaboration pass, really. - Ryan *)
and type_direct_application env ctx typ args =
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
and type_conditional env ctx cond tru fls =
  let open Prog.Statement in
  let expr_typed = type_expression env cond in
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
  let (stmt, typ) : Prog.Statement.pre_t * Typed.Type.t = 
    match expr with
    | None -> Return { expr = None }, Typed.Type.Void
    | Some e ->
       let e_typed = type_expression env e in
       Return { expr = Some e_typed }, (snd e_typed).typ
  in
  let ret: Prog.Statement.typed_t * CheckerEnv.t =
    { stmt = stmt; typ = StmType.Void }, env
  in
  match ctx, typ with
  | ApplyBlock, Void
  | Action, Void -> ret
  | Function t, t' ->
     assert_type_equality env info t t';
     ret
  | _ ->
     raise_s [%message "return statements not allowed in context"
                 ~info:(info: Info.t)
                 ~ctx:(ctx: StmtContext.t)]

(* Section 11.7 *)
and type_switch env ctx info expr cases =
  let open Types.Statement in
  if ctx <> ApplyBlock
  then raise_s [%message "switch statements not allowed in context"
                   ~ctx:(ctx: StmtContext.t)];
  let expr_typed = type_expression env expr in
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
     let decl_typed, env' = type_declaration env decl in
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
and type_constant env decl_info annotations typ name expr : Prog.Declaration.t * CheckerEnv.t =
  let expected_typ = translate_type env [] typ in
  let typed_expr = type_expression env expr in
  assert_same_type env decl_info (fst expr)
    expected_typ (snd typed_expr).typ |> ignore;
  match compile_time_eval_expr env typed_expr with
  | Some value ->
     (decl_info, Constant { annotations; typ = expected_typ; name = name; value = value }),
     env
     |> CheckerEnv.insert_dir_type_of (BareName name) expected_typ In
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
and type_instantiation env info annotations typ args name : Prog.Declaration.t * CheckerEnv.t =
  let instance_typed = type_nameless_instantiation env info typ args in
  let instance_type = instance_typed.typ in
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

and prog_param_to_typed_param (_, p: Prog.TypeParameter.t) : Typed.Parameter.t =
  { annotations = p.annotations;
    direction = p.direction;
    typ= p.typ;
    variable = p.variable }

and prog_params_to_typed_params ps =
  List.map ~f:prog_param_to_typed_param ps

and prog_param_to_constructor_param (_, p: Prog.TypeParameter.t) : Typed.ConstructParam.t =
  { name = snd p.variable;
    typ = p.typ }

and prog_params_to_constructor_params ps =
  List.map ~f:prog_param_to_constructor_param ps

and constructor_param_to_prog_param (p: Typed.ConstructParam.t) : Prog.TypeParameter.t =
  Info.dummy, { annotations = [];
                direction = Directionless;
                opt_value = None;
                variable = Info.dummy, p.name;
                typ = p.typ }

and constructor_params_to_prog_params ps =
  List.map ~f:constructor_param_to_prog_param ps

and infer_constructor_type_args env type_params params_args type_args =
  let type_params_args =
    match List.zip type_params type_args with
    | Ok v -> v
    | Unequal_lengths ->
       if type_args = []
       then List.map ~f:(fun v -> v, None) type_params
       else failwith "mismatch in type arguments"
  in
  let inference_params_args =
    List.map params_args
      ~f:(fun (cons_param, arg) -> prog_param_to_typed_param cons_param, arg)
  in
  infer_type_arguments env Typed.Type.Void type_params_args inference_params_args []

and type_set_expression env (expr: Types.Expression.t) =
  let (info, e_typed) = type_expression env expr in
  match e_typed.typ with
  | Set t ->
     info, e_typed
  | non_set_type ->
     info, {e_typed with typ = Set non_set_type}

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
    
and check_match env (info, m: Types.Match.t) (expected_type: Type.t) : Prog.Match.t =
  match m with
  | Default
  | DontCare -> 
     let set = Type.Set expected_type in
     info, { expr = DontCare; typ = set }
  | Expression { expr } ->
     let expr_typed = type_set_expression env expr in
     let typ = (snd expr_typed).typ in
     check_match_type_eq env info typ expected_type;
     info, { expr = Expression {expr = expr_typed};
             typ = Type.Set typ } 

and check_match_product env (ms: Types.Match.t list) (expected_types: Type.t list) =
  match ms, expected_types with
  | [m], [t] ->
     [check_match env m t]
  | [m], types ->
     [check_match env m (List { types })]
  | ms, types ->
     List.map ~f:(fun (m, t) -> check_match env m t) @@ List.zip_exn ms types

and type_select_case env state_names expr_types ((case_info, case): Types.Parser.case) : Prog.Parser.case =
  let matches_typed = check_match_product env case.matches expr_types in
  if List.mem ~equal:(=) state_names (snd case.next)
  then case_info, { matches = matches_typed; next = case.next }
  else raise_s [%message "state name unknown" ~name:(snd case.next: string)]

and type_transition env state_names transition : Prog.Parser.transition =
  let open Parser in
  fst transition,
  match snd transition with
  | Direct {next = (name_info, name')} ->
      if List.mem ~equal:(=) state_names name'
      then Direct { next = (name_info, name') }
      else raise @@ Type (name_info, (Error.Unbound name'))
  | Select {exprs; cases} ->
      let exprs_typed = List.map ~f:(type_expression env) exprs in
      let expr_types = List.map ~f:(fun (_, e) -> e.typ) exprs_typed in
      let cases_typed = 
        List.map ~f:(type_select_case env state_names expr_types) cases
      in
      Select { exprs = exprs_typed; cases = cases_typed }

and type_parser_state env state_names (state: Parser.state) : Prog.Parser.state =
  let (_, stmts_typed, env) = type_statements env ParserState (snd state).statements in
  let transition_typed = type_transition env state_names (snd state).transition in
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

and open_parser_scope env params constructor_params locals states =
  let open Parser in
  let constructor_params_typed = type_constructor_params env constructor_params in
  let params_typed = type_params env params in
  let env = insert_params env constructor_params in
  let env = insert_params env params in
  let locals_typed, env = type_declarations env locals in
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
    open_parser_scope env params constructor_params locals states
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
      parameters = prog_params_to_typed_params params_typed }
  in
  let ctor : Typed.ConstructorType.t =
    { type_params = [];
      parameters = List.map ~f:prog_param_to_constructor_param constructor_params_typed;
      return = Parser parser_typ }
  in
  let env = CheckerEnv.insert_type_of (BareName name) (Constructor ctor) env in
  (info, parser_typed), env

and open_control_scope env params constructor_params locals =
  let params_typed = type_params env params in
  let constructor_params_typed = type_constructor_params env constructor_params in
  let env = insert_params env constructor_params in
  let env = insert_params env params in
  let locals_typed, env = type_declarations env locals in
  env, params_typed, constructor_params_typed, locals_typed

(* Section 13 *)
and type_control env info name annotations type_params params constructor_params locals apply =
  if List.length type_params > 0
  then raise_s [%message "Control declarations cannot have type parameters" ~name:(snd name)]
  else
    let env', params_typed, constructor_params_typed, locals_typed =
      open_control_scope env params constructor_params locals
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
                           parameters = List.map ~f:prog_param_to_typed_param params_typed }
    in
    let ctor : Typed.ConstructorType.t =
      { type_params = [];
        parameters = List.map ~f:prog_param_to_constructor_param constructor_params_typed;
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
and type_function env info return name type_params params body =
  let t_params = List.map ~f:snd type_params in
  let body_env = CheckerEnv.insert_type_vars t_params env in
  let params_typed = List.map ~f:(type_param body_env) params in
  let return_type = return |> translate_type env t_params in
  let typ_params = List.map ~f:prog_param_to_typed_param params_typed in
  let body_env = insert_params body_env params in
  let body_stmt_typed, _ = type_block body_env (Function return_type) body in
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
    Type.Function { parameters = typ_params;
                    type_params = List.map ~f:snd type_params;
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
  let params_typed = List.map ~f:(type_param env') params in
  let params = List.map ~f:prog_param_to_typed_param params_typed in
  let typ: Typed.FunctionType.t =
    { type_params = t_params;
      parameters = params;
      return = return }
  in
  let fn_typed : Prog.Declaration.pre_t =
    ExternFunction { annotations;
                     return;
                     type_params;
                     params = params_typed;
                     name = name }
  in
  (info, fn_typed), CheckerEnv.insert_type_of (BareName name) (Function typ) env

(* Section 10.2
 *
 *          Δ, T, Γ |- e : t' = t
 * ---------------------------------------------
 *    Δ, T, Γ |- t x = e : Δ, T, Γ[x -> t]
 *)
and type_variable env info annotations typ name init =
  let expected_typ = translate_type env [] typ in
  let init_typed =
    match init with
    | None ->
       None
    | Some value ->
       let expected_typ = translate_type env [] typ in
       let typed_expr = type_expression env value in
       assert_same_type env info (fst value)
         expected_typ (snd typed_expr).typ |> ignore;
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
and type_value_set env info annotations typ size name =
  let element_type = translate_type env [] typ in
  let size_typed = type_expression env size in
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
    type_function env info (Info.dummy, Types.Type.Void) name [] params body
  in
  let action_typed, action_type =
    match snd fn_typed with
    | Function { return; name; type_params; params; body } ->
       let data_params, ctrl_params =
         List.split_while params
           ~f:(fun (_, p) -> p.direction <> Directionless)
       in
       let check_ctrl p =
         let open Prog.TypeParameter in
         if (snd p).direction <> Directionless
         then raise_s [%message "data parameter after a control parameter in action declaration"
                          ~data_param:(p: Prog.TypeParameter.t)
                          ~action_info:(info: Info.t)]
       in
       List.iter ~f:check_ctrl ctrl_params;
       let action_type : Typed.Type.t =
         Action { data_params = prog_params_to_typed_params data_params;
                  ctrl_params = prog_params_to_constructor_params ctrl_params; }
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
and type_table env info annotations name properties : Prog.Declaration.t * CheckerEnv.t =
  type_table' env info annotations name None [] None None None (List.map ~f:snd properties)

and type_keys env keys =
  let open Prog.Table in
  let type_key key =
    let {key; match_kind; annotations}: Table.pre_key = snd key in
    match CheckerEnv.find_type_of_opt (BareName match_kind) env with
    | Some (MatchKind, _) ->
       let expr_typed = type_expression env key in
       (fst key, { annotations; key = expr_typed; match_kind })
    | _ ->
       raise_s [%message "invalid match_kind" ~match_kind:(snd match_kind)]
  in
  List.map ~f:type_key keys

and type_table_actions env key_types actions =
  let type_table_action (call_info, action: Table.action_ref) =
    let data_params =
      match CheckerEnv.find_type_of_opt action.name env with
      | Some (Action action_typ, _) ->
         action_typ.data_params
      | _ ->
         raise_s [%message "invalid action" ~action:(action.name: Types.name)]
    in
    (* Below should fail if there are control plane arguments *)
    let params_args = match_params_to_args' call_info data_params action.args in
    let type_param_arg env (param, expr: Typed.Parameter.t * Expression.t option) =
      match expr with
      | Some expr ->
         let arg_typed = type_expression env expr in
         check_direction env param.direction expr (snd arg_typed).dir;
         assert_type_equality env call_info (snd arg_typed).typ param.typ;
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
  let action_names = List.map ~f:(fun (_, action: Table.action_ref) -> name_only action.name) actions in
  List.zip_exn action_names action_typs

and type_table_entries env entries key_typs action_map =
  let open Prog.Table in
  let type_table_entry (entry_info, entry: Table.entry) : Prog.Table.entry =
    let matches_typed = check_match_product env entry.matches key_typs in
    match List.Assoc.find action_map ~equal:(=) (name_only (snd entry.action).name) with
    | None ->
       failwith "Entry must call an action in the table."
    | Some (action_info, { action; typ = Action { data_params; ctrl_params } }) ->
       let type_arg (param:Typed.ConstructParam.t) (arg_info, arg:Argument.t) =
         begin match arg with
         (* Direction handling probably is incorrect here. *)
         | Expression { value = exp } ->
            let exp_typed = type_expression env exp in
            assert_type_equality env (fst exp) param.typ (snd exp_typed).typ;
            Some exp_typed
         | _ ->
            failwith "Actions in entries only support positional arguments."
         end in
       let args_typed = List.map2_exn ~f:type_arg ctrl_params (snd entry.action).args in
       let action_ref_typed : Prog.Table.action_ref =
         action_info,
         { action =
             { annotations = (snd entry.action).annotations;
               name = (snd entry.action).name;
               args =  args_typed };
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

and type_default_action env action_map action_expr: Prog.Table.action_ref =
  let action_expr_typed = type_expression env action_expr in
  match (snd action_expr_typed).expr with
  | FunctionCall { func = _, {expr = Name action_name; _}; type_args = []; args = args } ->
     let name = name_only action_name in
     if List.Assoc.mem ~equal:String.equal action_map name
     then fst action_expr,
          { action = { annotations = [];
                       name = action_name;
                       args = args };
            typ = (snd action_expr_typed).typ }
     else failwith "couldn't find default action in action_map"
  | Name action_name ->
     let name = name_only action_name in
     if List.Assoc.mem ~equal:String.equal action_map name
     then fst action_expr,
          { action = { annotations = [];
                       name = action_name;
                       args = [] };
            typ = (snd action_expr_typed).typ }
     else failwith "couldn't find default action in action_map"
  | e ->
     failwith "couldn't type default action as functioncall"

and type_table' env info annotations name key_types action_map entries_typed size default_typed properties =
  let open Types.Table in
  match properties with
  | Key { keys } :: rest ->
     begin match key_types with
     | None ->
        type_table' env info annotations
          name
          (Some (type_keys env keys))
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
           type_table' env info annotations
             name
             None
             action_map
             entries_typed
             size
             default_typed
             props
        | None, props ->
           type_table' env info annotations
             name
             (Some [])
             action_map
             entries_typed
             size
             default_typed
             props
        end
     | Some kts ->
        let action_map = type_table_actions env kts actions in
        type_table' env info annotations
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
           let entries_typed = type_table_entries env entries key_types' action_map in
           type_table' env info annotations name key_types action_map (Some entries_typed) size default_typed rest
        | None -> failwith "entries with no keys?"
        end
     end
  | Custom { name = (_, "default_action"); value; _ } :: rest ->
     begin match default_typed with
     | None ->
        let default_typed = type_default_action env action_map value in
        type_table' env info annotations
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
     let value_typed = type_expression env value in
     let _ = assert_numeric (fst value) (snd value_typed).typ in
     let size = compile_time_eval_expr env value_typed in
     begin match size with
     | Some (VInteger size) ->
        let size: P4Int.t =
          fst value, { value = size; width_signed = None }
        in
        type_table' env info annotations
          name
          key_types
          action_map
          entries_typed
          (Some size)
          default_typed
          rest
     | _ ->
        type_table' env info annotations
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
     type_table' env info annotations
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
    let action_names = List.map ~f:fst action_map in
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
  let env = CheckerEnv.insert_type (BareName name) header_typ env in
  let header = Prog.Declaration.Header { annotations; name; fields = fields_typed } in
  (info, header), env

and type_field env (field_info, field) =
  let open Types.Declaration in
  let typ = translate_type env [] field.typ in
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
  let env = CheckerEnv.insert_type (BareName name) header_typ env in
  let header = Prog.Declaration.HeaderUnion { annotations; name; fields = fields_typed } in
  (info, header), env

(* Section 7.2.5 *)
and type_struct env info annotations name fields =
  let fields_typed, type_fields = List.unzip @@ List.map ~f:(type_field env) fields in
  let struct_typ = Type.Struct { fields = type_fields; } in
  let env = CheckerEnv.insert_type (BareName name) struct_typ env in
  let struct_decl = Prog.Declaration.Header { annotations; name; fields = fields_typed } in
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
and type_serializable_enum env info annotations underlying_type name members =
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
    let expr_typed = type_expression env expr in
    assert_type_equality env (fst expr) underlying_type (snd expr_typed).typ;
    match compile_time_eval_expr env expr_typed with
    | Some value ->
       env
       |> CheckerEnv.insert_type_of member_name enum_type
       |> CheckerEnv.insert_const member_name
            (VEnumField { typ_name = snd name;
                          enum_name = member }),
       members_typed @ [ member_info, member ]
    | None -> failwith "could not evaluate enum member"
  in
  let env = CheckerEnv.insert_type (QualifiedName ([], name)) enum_type env in
  let env, member_names = List.fold_left ~f:add_member ~init:(env, []) members in
  let enum_typed =
    Prog.Declaration.Enum { annotations; name; members = member_names } in
  (info, enum_typed), env

(* Section 7.2.9.2 *)
and type_extern_object env info annotations obj_name t_params methods =
  let type_params' = List.map ~f:snd t_params in
  let env' = CheckerEnv.insert_type_vars type_params' env in
  let consume_method (constructors, methods) m =
    match snd m with
    | MethodPrototype.Constructor { annotations; name = cname; params } ->
       assert (snd cname = snd obj_name);
       let params_typed = type_constructor_params env' params in
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
       let params_typed = type_params env'' params in
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
  let extern_typ: ExternType.t =
    { type_params = type_params';
      methods = List.map ms
                  ~f:(method_prototype_to_extern_method obj_name) }
  in
  let to_typename s = Type.TypeName (BareName (Info.dummy, s)) in
  let extern_ctors =
    List.map cs ~f:(function
        | _, Prog.MethodPrototype.Constructor
              { annotations; name = cname; params = params_typed } ->
           Type.Constructor
             { type_params = type_params';
               parameters = prog_params_to_constructor_params params_typed;
               return = SpecializedType
                          { base = Extern extern_typ;
                            args = List.map ~f:to_typename type_params' } }
        | _ -> failwith "bug: expected constructor")
  in
  let env = CheckerEnv.insert_type (BareName obj_name) (Extern extern_typ) env in
  let env = List.fold extern_ctors ~init:env
              ~f:(fun env t -> CheckerEnv.insert_type_of (BareName obj_name) t env)
  in
  (info, extern_decl), env

and method_prototype_to_extern_method extern_name (m: Prog.MethodPrototype.t) :
  Typed.ExternType.extern_method =
    let open Typed.Type in
    let open Typed.ExternType in
    let name, (fn : Typed.FunctionType.t) =
      match snd m with
      | Constructor { annotations; name; params } ->
          name,
          { type_params = [];
            return = TypeName (BareName extern_name);
            parameters = prog_params_to_typed_params params }
      | AbstractMethod { annotations; return; name; type_params; params }
      | Method { annotations; return; name; type_params; params } ->
          name,
          { type_params = List.map ~f:snd type_params;
            return = return;
            parameters = prog_params_to_typed_params params }
    in
    { name = snd name;
      typ = fn }

(* Section 7.3 *)
and type_type_def env info annotations name typ_or_decl =
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
     let decl_typed, env' = type_declaration env decl in
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
and type_new_type env info annotations name typ_or_decl =
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
     let decl_typed, env' = type_declaration env decl in
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
  let params_typed = type_params body_env params in
  let params_for_type = prog_params_to_typed_params params_typed in
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
  let params_typed = type_params body_env params in
  let params_for_type = prog_params_to_typed_params params_typed in
  let parser_decl =
    Prog.Declaration.ParserType
      { annotations;
        name;
        type_params = t_params;
        params = params_typed }
  in
  let parser_typ = Type.Parser { type_params = simple_t_params;
                                 parameters = params_for_type } in
  (info, parser_decl), CheckerEnv.insert_type (BareName name) parser_typ env

(* Section 7.2.12 *)
and type_package_type env info annotations name t_params params =
  let simple_t_params = List.map ~f:snd t_params in
  let body_env = CheckerEnv.insert_type_vars simple_t_params env in
  let params_typed = type_params body_env params in
  let params_for_type = prog_params_to_constructor_params params_typed in
  let pkg_decl =
    Prog.Declaration.PackageType
      { annotations;
        name;
        type_params = t_params;
        params = params_typed }
  in
  let pkg_typ: Typed.PackageType.t =
    { type_params = simple_t_params;
      parameters = params_for_type }
  in
  let ret = Type.Package { pkg_typ with type_params = [] } in
  let ctor_typ =
    Type.Constructor { type_params = simple_t_params;
                       parameters = params_for_type;
                       return = ret }
  in
  let env' =
    env
    |> CheckerEnv.insert_type_of (BareName name) ctor_typ
    |> CheckerEnv.insert_type (BareName name) (Type.Package pkg_typ)
  in
  (info, pkg_decl), env'

and type_declaration (env: CheckerEnv.t) (decl: Types.Declaration.t) : Prog.Declaration.t * CheckerEnv.t =
  match snd decl with
  | Constant { annotations; typ; name; value } ->
     type_constant env (fst decl) annotations typ name value
  | Instantiation { annotations; typ; args; name; init } ->
     begin match init with
     | Some init -> failwith "initializer block in instantiation unsupported"
     | None -> type_instantiation env (fst decl) annotations typ args name
     end
  | Parser { annotations; name; type_params = _; params; constructor_params; locals; states } ->
     type_parser env (fst decl) name annotations params constructor_params locals states
  | Control { annotations; name; type_params; params; constructor_params; locals; apply } ->
     type_control env (fst decl) name annotations type_params params constructor_params locals apply
  | Function { return; name; type_params; params; body } ->
     type_function env (fst decl) return name type_params params body
  | ExternFunction { annotations; return; name; type_params; params } ->
     type_extern_function env (fst decl) annotations return name type_params params
  | Variable { annotations; typ; name; init } ->
     type_variable env (fst decl) annotations typ name init
  | ValueSet { annotations; typ; size; name } ->
     type_value_set env (fst decl) annotations typ size name
  | Action { annotations; name; params; body } ->
     type_action env (fst decl) annotations name params body
  | Table { annotations; name; properties } ->
     type_table env (fst decl) annotations name properties
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
     type_serializable_enum env (fst decl) annotations typ name members
  | ExternObject { annotations; name; type_params; methods } ->
     type_extern_object env (fst decl) annotations name type_params methods
  | TypeDef { annotations; name; typ_or_decl } ->
     type_type_def env (fst decl) annotations name typ_or_decl
  | NewType { annotations; name; typ_or_decl } ->
     type_new_type env (fst decl) annotations name typ_or_decl
  | ControlType { annotations; name; type_params; params } ->
     type_control_type env (fst decl) annotations name type_params params
  | ParserType { annotations; name; type_params; params } ->
     type_parser_type env (fst decl) annotations name type_params params
  | PackageType { annotations; name; type_params; params } ->
     type_package_type env (fst decl) annotations name type_params params

and type_declarations env decls =
  let f (decls_typed, env) decl =
    let decl_typed, env = type_declaration env decl in
    decls_typed @ [decl_typed], env
  in
  let decls, env = List.fold_left ~f ~init:([], env) decls in
  decls, env

(* Entry point function for type checker *)
let check_program (program:Types.program) : CheckerEnv.t * Prog.program =
  let Program top_decls = program in
  let prog, env = type_declarations CheckerEnv.empty_t top_decls in
  env, Prog.Program prog
