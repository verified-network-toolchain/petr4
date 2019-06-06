open Types
open Typed
open Error

let make_assert expected unwrap = fun info typ ->
  match unwrap typ with
  | Some v -> v
  | None -> raise_mismatch info expected typ

let option_map f = function
  | Some x -> Some (f x)
  | None -> None

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

let insert_type_vars : Env.checker_env -> string list -> Env.checker_env =
  List.fold_left (Core.Fn.flip Env.insert_type_var)

(* Eliminate all type references in typ and replace them with the type they
 * refer to. The result of saturation will contain no TypeName constructors
 * anywhere. It may contain TypeVar constructors.
 *
 * Warning: this will loop forever if you give it an environment with circular
 * TypeName references.
 *)
let rec saturate_type (env: Env.checker_env) (typ: Type.t) : Type.t =
  let open Type in
  let saturate_field env (field: RecordType.field) =
    {field with typ = saturate_type env field.typ}
  in
  let saturate_rec env ({fields}: RecordType.t) : RecordType.t =
    {fields = List.map (saturate_field env) fields}
  in
  let saturate_construct_param env (param: ConstructParam.t) =
    {param with typ = saturate_type env param.typ}
  in
  let saturate_param env (param: Parameter.t) =
    {param with typ = saturate_type env param.typ}
  in
  let saturate_pkg env (pkg: PackageType.t) : PackageType.t = 
    let env = insert_type_vars env pkg.type_params in
    {type_params = pkg.type_params;
     parameters = List.map (saturate_construct_param env) pkg.parameters}
  in
  let saturate_ctrl env (ctrl: ControlType.t) : ControlType.t =
    let env = insert_type_vars env ctrl.type_params in
    {type_params = ctrl.type_params;
     parameters = List.map (saturate_param env) ctrl.parameters}
  in
  let saturate_function env (fn: FunctionType.t) : FunctionType.t =
    let env = insert_type_vars env fn.type_params in
    {type_params = fn.type_params;
     parameters = List.map (saturate_param env) fn.parameters;
     return = saturate_type env fn.return}
  in
  match typ with
  | TypeName typ ->
      saturate_type env (Env.resolve_type_name typ env)
  | Bool | String | Integer
  | Int _ | Bit _ | VarBit _ 
  | TypeVar _
  | Error | MatchKind | Void ->
      typ
  | Array arr ->
      Array {arr with typ = saturate_type env arr.typ}
  | Tuple {types} ->
      Tuple {types = List.map (saturate_type env) types}
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
  | Package pkg ->
      Package (saturate_pkg env pkg)
  | Control control ->
      Control (saturate_ctrl env control)
  | Parser control ->
      Parser (saturate_ctrl env control)
  | Function func ->
      Function (saturate_function env func)

let rec record_type_equality env equiv_vars (rec1: RecordType.t) (rec2: RecordType.t) : bool =
  let open RecordType in
  let field_eq (f1, f2) =
    f1.name = f2.name && type_equality' env equiv_vars f1.typ f2.typ
  in
  let field_cmp f1 f2 =
    String.compare f1.name f2.name
  in
  let fields1 = List.sort field_cmp rec1.fields in
  let fields2 = List.sort field_cmp rec2.fields in
  let field_pairs = List.combine fields1 fields2 in
  List.for_all field_eq field_pairs

and enum_type_equality env equiv_vars enum1 enum2 : bool =
  let open EnumType in
  let same_typ =
    match enum1.typ, enum2.typ with 
    | Some typ1, Some typ2 -> 
        type_equality' env equiv_vars typ1 typ2
    | None, None -> true
    | _, _ -> false
  in
  let mems1 = List.sort String.compare enum1.members in
  let mems2 = List.sort String.compare enum2.members in
  mems1 = mems2 && same_typ

and constructor_params_equality env equiv_vars ps1 ps2 : bool =
  let open ConstructParam in
  let param_eq (p1, p2) =
    type_equality' env equiv_vars p1.typ p2.typ &&
    p1.name = p2.name
  in
  if List.length ps1 <> List.length ps2
  then false
  else List.for_all param_eq (List.combine ps1 ps2)

and package_type_equality env equiv_vars pkg1 pkg2 : bool =
  let open PackageType in
  if List.length pkg1.type_params <> List.length pkg2.type_params
  then false
  else
    let equiv_vars' = 
      equiv_vars @ List.combine pkg1.type_params pkg2.type_params
    in
    constructor_params_equality env equiv_vars' pkg1.parameters pkg2.parameters

and params_equality env equiv_vars ps1 ps2 : bool =
  let open Parameter in
  let param_eq (p1, p2) =
    type_equality' env equiv_vars p1.typ p2.typ &&
    p1.name = p2.name &&
    p1.direction = p2.direction
  in
  if List.length ps1 <> List.length ps2
  then false
  else List.for_all param_eq (List.combine ps1 ps2)

and control_type_equality env equiv_vars ctrl1 ctrl2 : bool =
  let open ControlType in
  if List.length ctrl1.type_params <> List.length ctrl2.type_params
  then false
  else
    let equiv_vars' = 
      equiv_vars @ List.combine ctrl1.type_params ctrl2.type_params
    in
    params_equality env equiv_vars' ctrl1.parameters ctrl2.parameters

and function_type_equality env equiv_vars func1 func2 : bool =
  let open FunctionType in
  if List.length func1.type_params <> List.length func2.type_params
  then false
  else
    let equiv_vars' = 
      equiv_vars @ List.combine func1.type_params func2.type_params
    in
    type_equality' env equiv_vars' func1.return func2.return &&
    params_equality env equiv_vars' func1.parameters func2.parameters

and type_vars_equal_under env equiv_vars tv1 tv2 =
  match equiv_vars with
  | (a, b)::rest ->
      if tv1 = a || tv2 = b
      then tv1 = a && tv2 = b
      else type_vars_equal_under env rest tv1 tv2
  | [] ->
      tv1 = tv2

(* [type_equality env t1 t2] is true if and only if expression type t1
 * is equivalent to expression type t2 under environment env.
 *  Alpha equivalent types are equal. *)
and type_equality env t1 t2 =
  type_equality' env [] t1 t2

and type_equality' (env: Env.checker_env) 
                   (equiv_vars: (string * string) list) 
                   (t1:Type.t) (t2:Type.t) : bool =
  let t1' = saturate_type env t1  in
  let t2' = saturate_type env t2 in
  begin match t1', t2' with
    | TypeName _, _
    | _, TypeName _ ->
        failwith "TypeName in saturated type?"

    | Bool, Bool
    | String, String
    | Integer, Integer
    | Error, Error
    | MatchKind, MatchKind
    | Void, Void ->
        true

    | Bit { width = l}, Bit {width = r}
    | Int { width = l}, Int {width = r}
    | VarBit {width = l}, VarBit {width = r} ->
        l = r

    | Array {typ = lt; size = ls}, Array {typ = rt; size = rs} ->
        ls = rs && type_equality' env equiv_vars lt rt

    | Tuple {types = types1}, Tuple {types = types2} ->
        let type_pairs = List.combine types1 types2 in
        List.for_all (fun (t1, t2) -> type_equality' env equiv_vars t1 t2) type_pairs

    | Set ty1, Set ty2 ->
        type_equality' env equiv_vars ty1 ty2

    | TypeVar tv1, TypeVar tv2 ->
        type_vars_equal_under env equiv_vars tv1 tv2

    | Header rec1, Header rec2
    | HeaderUnion rec1, HeaderUnion rec2
    | Struct rec1, Struct rec2 ->
        record_type_equality env equiv_vars rec1 rec2

    | Enum enum1, Enum enum2 ->
        enum_type_equality env equiv_vars enum1 enum2

    | Package pkg1, Package pkg2 ->
        package_type_equality env equiv_vars pkg1 pkg2

    | Control ctrl1, Control ctrl2
    | Parser ctrl1, Parser ctrl2 ->
        control_type_equality env equiv_vars ctrl1 ctrl2

    | Function func1, Function func2 ->
        function_type_equality env equiv_vars func1 func2

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
    | Set _, _
    | TypeVar _, _
    | Header _, _
    | HeaderUnion _, _
    | Struct _, _
    | Enum _, _
    | Control _, _
    | Parser _, _
    | Package _, _
    | Function _, _ ->
        false
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
  List.for_all check_params (List.combine p1s p2s)

(* Checks that a list of constructor parameters is type equivalent.
 * True if equivalent, false otherwise.
 * Parameter names are ignored.
 * The order of parameters is significant. *)
and construct_param_equality env p1s p2s =
  let open ConstructParam in
  let check_params = fun (par1,par2) ->
    type_equality env par1.typ par2.typ in
  List.for_all check_params (List.combine p1s p2s)

let assert_same_type (env: Env.checker_env) info1 info2 (typ1: Type.t) (typ2: Type.t) =
  if type_equality env typ1 typ2 then (typ1, typ2)
else
  let info = Info.merge info1 info2 in
    raise_type_error info (Type_Difference (typ1, typ2))

let compile_time_known_expr (_: Env.checker_env) (_: Expression.t) : unit =
  failwith "Unimplemented"

let rec type_expression_dir (env: Env.checker_env) ((_, exp): Expression.t) : Type.t
* direction =
  match exp with
  | True ->
    (Type.Bool, Directionless)
  | False ->
    (Type.Bool, Directionless)
  | String _ ->
    (Type.String, Directionless)
  | Int i ->
    (type_int i, Directionless)
  | Name name ->
    Env.find_type_of (snd name) env
  | TopLevel name ->
    Env.find_type_of_toplevel (snd name) env
  | ArrayAccess { array; index } ->
    type_array_access env array index
  | BitStringAccess { bits; lo; hi } ->
    type_bit_string_access env bits lo hi
  | List { values } ->
    (type_list env values, Directionless)
  | UnaryOp { op; arg } ->
    type_unary_op env op arg
  | BinaryOp { op; args } ->
    (type_binary_op env op args, Directionless)
  | Cast { typ; expr } ->
    type_cast env typ expr
  | TypeMember { typ; name } ->
    type_type_member env typ name
  | ErrorMember name ->
    (type_error_member env name, Directionless)
  | ExpressionMember { expr; name } ->
    (type_expression_member env expr name, Directionless)
  | Ternary { cond; tru; fls } ->
    (type_ternary env cond tru fls, Directionless)
  | FunctionCall { func; type_args; args } ->
    (type_function_call env func type_args args, Directionless)
  | NamelessInstantiation { typ; args } ->
    (type_nameless_instantiation env typ args, Directionless)
  | Mask { expr; mask } ->
    (type_mask env expr mask, Directionless)
  | Range { lo; hi } ->
    (type_range env lo hi, Directionless)

and type_expression (env: Env.checker_env) (exp : Expression.t) : Type.t =
  fst (type_expression_dir env exp)

and translate_type (env: Env.checker_env) (typ: Types.Type.t) : Typed.Type.t =
  let open Types.Type in
  let eval e =
    Eval.eval_expression (Env.eval_env_of_checker_env env) e
  in
  let get_int_from_bigint num =
    begin match Bigint.to_int num with
      | Some n -> n;
      | None -> failwith "numeric type parameter is too large"
    end in
  match snd typ with
  | Bool -> Bool
  | Error -> Error
  | IntType e ->
    begin match eval e with
      | Int {value=v; _}
      | Bit {value=v; _}
      | Integer v     -> Int ({width= get_int_from_bigint v})
      | _ -> failwith "int type param must evaluate to an int"
    end
  | BitType e ->
    begin match eval e with
      | Int {value=v; _}
      | Bit {value=v; _}
      | Integer v     -> Bit ({width= get_int_from_bigint v})
      | _ -> failwith "bit type param must evaluate to an int"
    end
  | VarBit e ->
    begin match eval e with
      | Int {value=v; _}
      | Bit {value=v; _}
      | Integer v     -> VarBit ({width= get_int_from_bigint v})
      | _ -> failwith "varbit type param must evaluate to an int"
    end
  | TopLevelType ps -> TypeName (snd ps)
  | TypeName ps -> TypeName (snd ps)
  | SpecializedType _ -> failwith "Unimplemented"
  | HeaderStack {header=ht; size=e}
    -> let hdt = translate_type env ht in
    let len =
      begin match eval e with
      | Int {value=v; _}
      | Bit {value=v; _}
      | Integer v     -> get_int_from_bigint v
      | _ -> failwith "header stack size must be a number"
      end in
    Array {typ=hdt; size=len}
  | Tuple tlist ->
    Tuple {types = List.map (translate_type env) tlist}
  | Void -> Void
  | DontCare -> failwith "TODO: type inference"

(* Translates Types.Parameters to Typed.Parameters *)
and translate_parameters env params =
  let p_folder = fun (acc:Parameter.t list) (p:Types.Parameter.t) ->
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
    let par = {name=p.variable |> snd;
               typ=p.typ |> translate_type env;
               direction=pd} in par::acc end in
  List.fold_left p_folder [] params |> List.rev

(* Translates Types.Parameters representing constructor parameters
 * to Typed.ConstructParams *)
and translate_construct_params env construct_params =
  let p_folder = fun (acc:ConstructParam.t list) (p:Types.Parameter.t) ->
    begin let open ConstructParam in
      let p = snd p in
      match p.direction with
      | None ->
      let par = {name=p.variable |> snd;
               typ=p.typ |> translate_type env}
               in par::acc
      | Some _ -> failwith "Constructor parameters must be directionless."
       end in
  List.fold_left p_folder [] construct_params |> List.rev


and type_int (_, value) =
  let open P4Int in
  match value.width_signed with
  | None -> Type.Integer
  | Some (width, true) -> Type.Int { width }
  | Some (width, false) -> Type.Bit { width }

(* Section 8.15
 * ------------
 *
 * Δ, T, Γ |- a : t[size]      Δ, T, Γ |- i : u, where numeric(u)
 * ----------------------------------------------------------
 *                Δ, T, Γ |- a[i] : t
 *
 * Some architectures may further require ctk(i).
 *)
and type_array_access env (array: Types.Expression.t) index =
  let (array_typ, array_dir) = type_expression_dir env array in
  let idx_typ = type_expression env index in
  assert_array (info array) array_typ |> ignore;
  assert_numeric (info index) idx_typ |> ignore;
  (array_typ, array_dir)

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
and type_bit_string_access _ _ _ _ =
  failwith "Unimplemented"

(* Section 8.11
 * ------------
 *
 *      1 <= i <= n; Δ, T, Γ |- xi : ti
 * ------------------------------------------
 * Δ, T, Γ |- { x1, ..., xn } : (t1, ..., tn)
 *
 *)
and type_list env values : Typed.Type.t =
  let type_valu v = type_expression env v in
  let types = List.map type_valu values in
  Type.Tuple { types }

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
and type_unary_op env (_, op) arg =
  let (arg_typ, dir) = type_expression_dir env arg in
  let open Op in
  begin match op with
  | Not    -> assert_bool (info arg) arg_typ    |> ignore
  | BitNot -> assert_bit (info arg) arg_typ     |> ignore
  | UMinus -> assert_numeric (info arg) arg_typ |> ignore
  end;
  (arg_typ, dir)

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
and type_binary_op env (_, op) (l, r) : Typed.Type.t =
  let open Op in
  let open Type in

  (* Implicit integer casts as per section 8.9.2
   *
   * Let implicit_cast(t1,t2) be defined as follows to describe
   * p4's impliciting casting behavior on operands in binary expressions:
   *
   * implicit_cast(bit<w>, bit<w>)    = bit<w>
   * implicit_cast(bit<w>, int CTK)   = bit<w>
   * implicit_cast(int CTK, bit<w>)   = bit<w>
   * implicit_cast(int<w>, int CTK)   = int<w>
   * implicit_cast(int CTK, int<w>)   = int<w>
   * implicit_cast(int<w>, int<w>)    = int<w>
   * implicit_cast(int CTK, int CTK)  = int CTK
   * implicit_cast(_, _)              = implicit_cast_error
   *
   *)
  let l_typ, r_typ =
    match type_expression env l, type_expression env r with
    | Bit { width }, Integer | Integer, Bit { width } -> Bit { width }, Bit { width }
    | Int { width }, Integer | Integer, Int { width } -> Int { width }, Int { width }
    | l_typ, r_typ -> l_typ, r_typ
  in

  match op with
  | And | Or ->
    assert_bool (info l) l_typ |> ignore;
    assert_bool (info r) r_typ |> ignore;
    Bool

  (* Basic numeric operations are defined on both arbitrary and fixed-width integers *)
  | Plus | Minus | Mul ->
    begin match l_typ, r_typ with
    | Integer, Integer -> Integer
    | Bit { width = l }, Bit { width = r } when l = r -> Bit { width = l }
    | Int { width = l }, Int { width = r } when l = r -> Int { width = l }
    | _, _ -> failwith "Unimplemented" (* TODO: better error message here *)
    end

  (* Equality is defined on TODO*)
  (*| Eq | NotEq when l_typ = r_typ -> Type.Bool *)(* FIXME *)
  | Eq | NotEq ->
     if type_equality env l_typ r_typ then Type.Bool
    else failwith "Types are not equal under equality operation."

  (* Saturating operators are only defined on finite-width signed or unsigned integers *)
  | PlusSat | MinusSat ->
    begin match l_typ, r_typ with
    | Bit { width = l }, Bit { width = r } when l = r -> Bit { width = l }
    | Int { width = l }, Int { width = r } when l = r -> Int { width = l }
    | _, _ -> failwith "Unimplemented" (* TODO: better error message here *)
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
    | Integer, Integer -> ()
    | Bit { width = l }, Bit { width = r } when l = r -> ()
    | Int { width = l }, Int { width = r } when l = r -> ()
    | _, _ -> failwith "Unimplemented" (* TODO: better error message here *)
    end;
    Bool

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
    begin match l_typ, r_typ with
      | Bit _, Bit _ -> l_typ
      | Int _, Bit _ -> l_typ
      | Integer, Bit _ -> l_typ
      | Bit _, Int _ -> l_typ
      | Int _, Int _ -> l_typ
      | Integer, Int _ -> l_typ
      | _ -> failwith "Shift operands have improper types" (*TODO better error handling*)
    end

(* Section 8.9 *)
and type_cast _ _ _ =
  failwith "type_cast Unimplemented"

(* ? *)
and type_type_member _ _ _ =
  failwith "Unimplemented"

(* Section 8.2
 * -----------
 *
 *       (e, error) ∈ T
 * --------------------------
 * Δ, T, Γ |- error.e : error
 *
 *)
and type_error_member env name : Typed.Type.t =
  let (e, _) = Env.find_type_of ("error." ^ (snd name)) env in
  match e with
  | Type.Error -> Type.Error
  | _ -> failwith "Error member not an error?"

(* Sections 6.6, 8.14 *)
and type_expression_member env expr name : Typed.Type.t =
  let expr_typ = expr
  |> type_expression env
  (* |> assert_header_or_struct (info expr) *)
  in
  let open RecordType in
  let fields =
    begin match expr_typ with
    | TypeName na ->
      begin match Env.resolve_type_name na env with
      | Header {fields=fs} | Struct {fields=fs} -> fs
      | _ -> failwith "not a record type"
      end
    | _ -> failwith "not a record type"
  end in
  List.find_opt (fun field -> field.name = snd name) fields
  |> begin function
  | Some field -> field.typ
  | None -> raise_unfound_member (info expr) (snd name)
  end

(* Section 8.4.1
 * -------------
 *
 * Δ, T, Γ |- cond : bool    Δ, T, Γ |- tru : t    Δ, T, Γ |- fls : t;
 * -------------------------------------------------------------------
 *              Δ, T, Γ |- cond ? tru : fls : t
 *)
and type_ternary env cond tru fls : Typed.Type.t =
  let _ = cond
  |> type_expression env
  |> assert_bool (info cond)
  in
  (type_expression env fls)
  |> ((type_expression env tru)
  |> assert_same_type env (info tru) (info fls))
  |> begin function
  | (Type.Integer, Type.Integer) -> failwith "unless the condition itself can be evaluated at compilation time"
  | (t1, _) -> t1
  end

(* Section 8.17: Typing Function Calls
 *
 * Arguments are positional:
 *   Δ (ef) = tr  f<...Ai,...>(...di ti,...)
 *  for all i  Δ (union over j)(Aj -> uj) , T, Γ ei : ti
 * ------------------------------------------------------
 *     Δ, T, Γ |- ef<...ui,...>(...ei,...) : tr
 *
 * Arguments are named:
 *   Δ (ef) = tr  f<...Ai,...>(...di ti,...)
 *  for all i  Δ (union over j)(Aj -> uj) , T, Γ ei : ti
 * ------------------------------------------------------
 *     Δ, T, Γ |- ef<...ui,...>(...ni = ei,...) : tr
 *
 *
*)
and check_call env func type_args args post_check : 'a =
  let arg_types = List.map (translate_type env) type_args in
  let get_fun_type = fun (ft:Types.Expression.t) ->
    begin match snd ft with
      | Name na ->
        begin match Env.resolve_type_name (snd na) env with
        | Type.Function fr -> fr
        | _ -> failwith "Function name must be associated with a function type."
        end
      | _ -> failwith "function name must be a string"
    end in
  let fun_type = get_fun_type func in
  let open Parameter in
  let params = fun_type.parameters in

  let typ_ps = fun_type.type_params in

  (* helper to extend delta environment *)
  let extend_delta environ (t_par, t_arg) =
    Env.insert_type t_par t_arg environ
  in
  let type_names_args = List.combine typ_ps arg_types in
  let env = List.fold_left extend_delta env type_names_args in

  (* Case 1: All atguments are positional *)
  let case1 = fun (arg:Argument.t) ->
    begin match snd arg with
      | Expression _ | Missing -> true
      | KeyValue _ -> false
    end in

  (* Case 2: All arguments are named *)
  let case2 = fun (arg:Argument.t) ->
    begin match snd arg with
      | KeyValue _ | Missing -> true
      | Expression _ -> false
    end in

  if List.for_all case1 args then begin
    let new_ctx = env in
    let check_positional = fun (par,arg:Parameter.t * Argument.t) ->
      begin match snd arg with
        | Expression {value=e} -> let t = type_expression new_ctx e in
          let pt = saturate_type new_ctx par.typ in
          if type_equality new_ctx t pt then true else failwith "Function argument has incorrect type."
        | Missing ->
          begin match par.direction with
            | Out -> true
            | _ -> failwith "Only out parameters can have don't care arguments."
          end
      | _ -> failwith "Should not get here"
      end in
    if List.for_all check_positional (List.combine params args)
    then post_check fun_type
    else failwith "Function call does not type check"
  end

  else if List.for_all case2 args then begin

    (* I need to align the order of arguments with the order
     * of parameters. This is important for updating the environment
     * and comparing each argument type to its
     * corresponding parameter type*)
    let comp_arg = fun (arg1:Argument.t) (arg2:Argument.t) ->
      begin match snd arg1,snd arg2 with
        | KeyValue {key= (_,n1) ;_},KeyValue{key= (_,n2) ;_} -> String.compare n1 n2
        | _ -> failwith "Only call comp_arg when arguments are named."
      end in
    let comp_param = fun (par1:Parameter.t) (par2:Parameter.t) ->
      begin match par1,par2 with
        | {name=n1; _}, {name=n2; _} ->  String.compare n1 n2
      end in
    let sorted_params = List.sort comp_param params in
    let sorted_args = List.sort comp_arg args in
    let new_ctx = env in
    let check_named = fun (par,arg:Parameter.t * Argument.t) ->
      begin match snd arg with
        | KeyValue {value=e; _} -> let t = type_expression new_ctx e in
          let pt = saturate_type new_ctx par.typ in
          if type_equality new_ctx t pt then true else failwith "Function argument has incorrect type."
        | Missing -> begin match par.direction with
            | Out -> true
            | _ -> failwith "Only out parameters can have don't care arguments."
          end
        | _ -> failwith "Arguments in a function call must be positional or named, not both"
      end in
    if  List.for_all check_named (List.combine sorted_params sorted_args)
    then post_check fun_type
    else failwith "Function call does not type check"
  end

  else failwith "All arguments must be positional or named, not both"

(* Section 8.17: Typing Function Calls *)
and type_function_call env func type_args args =
  let type_args  = List.rev type_args in
  let open FunctionType in
  (* helper to extend delta environment *)
  let arg_types = List.map (translate_type env) type_args in
  let post_check fun_type =
    let typ_ps = fun_type.type_params in

    (* helper to extend delta environment *)
    let extend_delta environ (t_par, t_arg) =
      Env.insert_type t_par t_arg environ
    in
    let env = List.fold_left extend_delta env (List.combine typ_ps arg_types) in
    match fun_type.return with
    | Void -> failwith "function call must be non-void inside an expression"
    | rt -> (saturate_type env rt),(StmType.Unit,env) in
  check_call env func type_args args post_check |> fst



(* Section 14.1 *)
and type_nameless_instantiation _ _ _ =
  failwith "Unimplemented"

(* Section 8.12.3 *)
and type_mask env expr mask =
  Type.Set
  (type_expression env expr
  |> assert_bit (info expr)
  |> ignore;
  type_expression env mask
  |> assert_bit (info mask))

(* Section 8.12.4 *)
and type_range env lo hi =
  let lo_typ = type_expression env lo in
  let hi_typ = type_expression env hi in
  match lo_typ, hi_typ with
  | Bit { width = l }, Bit { width = r } when l = r -> Set lo_typ
  | Int { width = l }, Int { width = r } when l = r -> Set lo_typ
  (* TODO: add pretty-printer and [to_string] for Typed module *)
  | Bit { width }, _ -> raise_mismatch (info hi) ("bit<" ^ (string_of_int width) ^ ">") hi_typ
  | Int { width }, _ -> raise_mismatch (info hi) ("int<" ^ (string_of_int width) ^ ">") hi_typ
  | _ -> raise_mismatch (Info.merge (info lo) (info hi)) "int or bit" lo_typ

and type_statement (env: Env.checker_env) (stm: Statement.t) : (StmType.t * Env.checker_env) =
  match snd stm with
  | MethodCall { func; type_args; args } ->
    type_method_call env func type_args args
  | Assignment { lhs; rhs } ->
    type_assignment env lhs rhs
  | DirectApplication { typ; args } ->
    type_direct_application env typ args
  | Conditional { cond; tru; fls } ->
    type_conditional env cond tru fls
  | BlockStatement { block } ->
    type_block_statement env block
  | Exit ->
    (StmType.Void, env)
  | EmptyStatement ->
    (StmType.Unit, env)
  | Return { expr } ->
    type_return env expr
  | Switch { expr; cases } ->
    type_switch env expr cases
  | DeclarationStatement { decl } ->
    type_declaration_statement env decl

(* Section 8.17 *)
and type_method_call env func type_args args =
  let type_args  = List.rev type_args in
  let open FunctionType in
  let post_check = fun ft ->
    let arg_types = List.map (translate_type env) type_args in
    (* helper to extend delta environment *)
    (* for now naively extend local delta environment instead of creating new symbols *)
    let extend_delta environ (t_par, t_arg) =
      Env.insert_type t_par t_arg environ
    in
    let env = List.fold_left extend_delta env (List.combine ft.type_params arg_types) in
    let pfold = fun (acc:Env.checker_env) (p:Parameter.t) ->
      match p.direction with
      | In -> acc
      | Directionless | Out | InOut -> (* only out variables are added to the environment *)
          Env.insert_type_of p.name p.typ env
    in
    Type.Error,(StmType.Unit,List.fold_left pfold env ft.parameters) in
  check_call env func type_args args post_check |> snd
  (* type_function_call env func type_args args *)

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
  let lhs_type = type_expression env lhs in
  let rhs_type = type_expression env rhs in
  ignore (assert_same_type env (info lhs) (info rhs) lhs_type rhs_type);
  (Unit, env)

(* Section 13.1 desugar and resugar the exceptions*)
and type_direct_application _ _ _ =
  failwith "Unimplemented"

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
  cond |> type_expression env
  |> assert_bool (info cond)
  |> ignore;
  let type' x = fst (type_statement env x) in
  let tru_typ = type' tru in
  let fls_typ = option_map type' fls in
  match fls_typ with
  | None -> (tru_typ, env) (*QUESTION: in old checker, type checks to Unit here*)
  | Some x ->
    (match tru_typ, x with
    | StmType.Void, StmType.Void -> (StmType.Void, env)
    | StmType.Unit, _ | _, StmType.Unit -> (StmType.Unit, env))

(* QUESTION: Why are we only allowing statements but not declarations *)
(* A block execuete a sequence of statements sequentially*)
and type_block_statement env block =
  let fold (prev_type, env) statement =
    (* Cannot have statements after a void statement *)
    match prev_type with
    | StmType.Void -> raise_internal_error "UnreachableBlock"
    | StmType.Unit -> type_statement env statement
  in
  List.fold_left fold (StmType.Unit, env) (snd block).statements

(* Section 11.4
 * Can a return statement update the environment?
 *
 *          Δ, T, Γ |- e : t
 * ---------------------------------------------
 *    Δ, T, Γ |- return e: void ,Δ, T, Γ
 *)
and type_return env expr =
  let ret = StmType.Void, env in
  match expr with
  | None -> ret
  | Some e -> let _ = type_expression env e in ret


(* Section 11.7 *)
and type_switch _ _ _ =
  failwith "Unimplemented"

(* Section 10.3 *)
and type_declaration_statement _ _ =
  failwith "Unimplemented"

and type_declaration (env: Env.checker_env) ((_, decl): Declaration.t) : Env.checker_env =
  match decl with
  | Constant { annotations = _; typ; name; value } ->
    type_constant env typ name value
  | Instantiation { annotations = _; typ; args; name } ->
    type_instantiation env typ args name
  | Parser { annotations = _; name; type_params; params; constructor_params; locals; states } ->
    type_parser env name type_params params constructor_params locals states
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

(* Section 10.1
 *
 *          Δ, T, Γ |- e : t' = t
 * ---------------------------------------------
 *    Δ, T, Γ |- const t x = e : Δ, T, Γ[x -> t]
 *)
and type_constant env typ name value =
  let expected_typ = translate_type env typ in
  let initialized_typ = type_expression env value in
  compile_time_known_expr env value;
  let expr_typ, _ = assert_same_type env (fst value) (fst value) expected_typ initialized_typ in
  Env.insert_dir_type_of (snd name) expr_typ In env

(* Section 10.3 *)
and type_instantiation _ _ _ _ =
  failwith "Unimplemented"

(* Section 12.2 *)
and type_parser _ _ _ _ _ _ _ =
  failwith "Unimplemented"

(* Section 13 *)
and type_control _ _ _ _ _ _ _ =
  failwith "Unimplemented"

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
  let p_fold = fun (acc,env:Parameter.t list * Env.checker_env) (p:Types.Parameter.t) ->
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
    let par = {name=p.variable |> snd;
              typ=p.typ |> translate_type env;
              direction=pd} in
    let new_env =
      Env.insert_dir_type_of (snd p.variable) par.typ par.direction env
    in
    par::acc, new_env end in
  let (ps,body_env) = List.fold_left p_fold ([],env) params in
  let ps = List.rev ps in
  let rt = return |> translate_type env  in
  let sfold = fun (prev_type,envi:StmType.t*Env.checker_env) (stmt:Statement.t) ->
    begin match prev_type with
      | Void -> failwith "UnreachableBlock" (* do we want to do this? *)
      | Unit ->
        let (st,new_env) = type_statement envi stmt in
        begin match snd stmt with
          | Return {expr=eo} ->
            begin match eo with
              | None -> failwith "return expression must have an expression"
              | Some e -> let te = type_expression envi e in
                if not (type_equality envi rt te) then failwith "body does not match return type"
                else (st,new_env)
            end
          | _ -> (st,new_env)
        end
    end in
  let _ = List.fold_left sfold (StmType.Unit, body_env) (snd body).statements in
  let open FunctionType in
  let funtype = Type.Function {parameters=ps;
                 type_params= type_params |> List.map snd;
                 return= rt} in
  Env.insert_type_of (snd name) funtype env

(* Section 7.2.9.1 *)
and type_extern_function _ _ _ _ _ =
  failwith "Unimplemented"

(* Section 10.2
 *
 *          Δ, T, Γ |- e : t' = t
 * ---------------------------------------------
 *    Δ, T, Γ |- t x = e : Δ, T, Γ[x -> t]
 *)
and type_variable env typ name init =
  let expected_typ = translate_type env typ in
  match init with
  | None ->
      Env.insert_dir_type_of (snd name) expected_typ In env
  | Some value -> let initialized_typ = type_expression env value in
    let expr_typ, _ = assert_same_type env (fst value) (fst value) expected_typ initialized_typ in
    Env.insert_dir_type_of (snd name) expr_typ In env

(* Section 12.11 *)
and type_value_set _ _ _ _ =
  failwith "Unimplemented"

(* Section 13.1 *)
and type_action _ _ _ _ =
  failwith "Unimplemented"

(* Section 13.2 *)
and type_table _ _ _ =
  failwith "Unimplemented"

(* TODO: is there a cleaner type for this?
 * Can't return a new environment because TypeDef and NewType might need the type (typ_or_decl field)
 * Can't return a single type because some nodes (e.g. Error, MatchKind) declare multiple bindings at once
 *)
and type_type_declaration (env: Env.checker_env) ((_, decl): TypeDeclaration.t) : Env.checker_env =
  match decl with
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

and type_field env field =
  let TypeDeclaration.{ annotations = _; typ; name } = snd field in
  let name = snd name in
  let typ = translate_type env typ in
  RecordType.{ name; typ }

(* Section 7.2.2 *)
and type_header env name fields =
  let fields = List.map (type_field env) fields in
  let header_typ = Type.Header { fields } in
  Env.insert_type (snd name) header_typ env

(* Section 7.2.3 *)
and type_header_union env name fields =
  let open RecordType in
  let union_folder = fun acc -> fun field ->
    begin let open Types.TypeDeclaration in
      let {typ=ht; name=fn; _} = snd field in
      let ht = begin match snd ht with
        | TypeName tn -> snd tn
        | _ -> failwith "Header Union fields must be Headers"
      end in
      match Env.resolve_type_name ht env with
      | Header _ -> {name = snd fn; typ=TypeName ht}::acc
      | _ -> failwith "Header Union field is undefined"
    end in
  let ufields = List.fold_left union_folder [] fields |> List.rev in
  let hu = Type.HeaderUnion {fields=ufields} in
  Env.insert_type (snd name) hu env

(* Section 7.2.5 *)
and type_struct env name fields =
  let fields = List.map (type_field env) fields in
  let struct_typ = Type.Struct { fields } in
  Env.insert_type (snd name) struct_typ env

(* Auxillary function for [type_error] and [type_match_kind],
 * which require unique names *)
and fold_unique members (_, member) =
  if List.mem member members then
    failwith "Name already bound"
  else
    member :: members

(* Section 7.1.2 *)
(* called by type_type_declaration *)
and type_error env members =
  let add_err env (_, e) =
    Env.insert_type_of_toplevel ("error." ^ e) Type.Error env
  in
  List.fold_left add_err env members

(* Section 7.1.3 *)
and type_match_kind env members =
  let add_mk env (_, m) =
    Env.insert_type_of_toplevel ("match_kind." ^ m) Type.MatchKind env
  in
  List.fold_left add_mk env members

(* Section 7.2.1 *)
and type_enum env name members =
  let members' = List.map snd members in
  let enum_typ = Type.Enum { members = members'; typ = None } in
  Env.insert_type (snd name) enum_typ env

(* Section 8.3 *)
and type_serializable_enum _ _ _ _ =
  failwith "Unimplemented"

(* Section 7.2.9.2 *)
and type_extern_object _ _ _ _ =
  failwith "Unimplemented"

(* Section 7.3 *)
and type_type_def _ _ _ =
  failwith "Unimplemented"

(* ? *)
and type_new_type _ _ _ =
  failwith "Unimplemented"

(* Section 7.2.11.2 *)
and type_control_type env name type_params params =
  let ps = translate_parameters env params in
  let tps = List.map snd type_params in
  let ctrl = Type.Control {type_params=tps; parameters=ps} in
  Env.insert_type (snd name) ctrl env

(* Section 7.2.11 *)
and type_parser_type env name type_params params =
  let ps = translate_parameters env params in
  let tps = List.map snd type_params in
  let ctrl = Type.Parser {type_params=tps; parameters=ps} in
  Env.insert_type (snd name) ctrl env

(* Section 7.2.12 *)
and type_package_type env name type_params params =
  let ps = translate_construct_params env params in
  let tps = List.map snd type_params in
  let ctrl = Type.Package {type_params=tps; parameters=ps} in
  Env.insert_type (snd name) ctrl env

(* Entry point function for type checker *)
let check_program (program:Types.program) : Env.checker_env =
  let top_decls = match program with Program tds -> tds in
  let init_acc = Env.empty_checker_env in
  let program_folder =
    fun (acc:Env.checker_env) -> fun (top_decl:Types.TopDeclaration.t) ->
      begin match top_decl with
      | TypeDeclaration type_decl -> type_type_declaration acc type_decl
      | Declaration decl -> type_declaration acc decl
      end in
  List.fold_left program_folder init_acc top_decls
