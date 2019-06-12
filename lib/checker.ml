open Types
open Typed
open Error
open Info

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
  | Bool -> Some ExpType.Bool
  | _ -> None
  end

let assert_bit = make_assert "unsigned int"
  begin function
  | Bit { width } -> Some (ExpType.Bit { width })
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

(* let assert_header_or_struct = make_assert "header or struct" *)
(*   begin function *)
(*   | Header record_typ *)
(*   | Struct record_typ -> Some record_typ *)
(*   | _ -> None *)
(*   end *)

(* Returns a type declaration alpha equivalent to [t]
 * where all occurences of [old_t] are replaced with [sub_t]
 * Needs to be fixed for new decl types.
 * tn is the name of the declared type.
 *
 * Known Problems: unsure of what environment to return in some cases:
 * enums, headers, structs, env threading for parameters
*)
let rec alpha_sub_decl (env:Env.t) (old_t:string) (sub_t:string) (tn:string) : Env.t =
  let partial_alpha_sub_exp = alpha_sub_exp env old_t sub_t in
  let open Parameter in
  let open ConstructParam in
  let param_mapper = fun (p:Parameter.t) -> {p with typ = partial_alpha_sub_exp p.typ |> fst} in
  let construct_param_mapper = fun (p:ConstructParam.t) -> {p with typ = partial_alpha_sub_exp p.typ |> fst} in
  let record_mapper = fun (r:RecordType.field) ->
    {r with typ=partial_alpha_sub_exp r.typ |> fst} in
  let td = Env.find (Info.dummy,tn) env.decl in
  match td with
  | MatchKind _ | Error _  | HeaderUnion _ -> env
  | Enum {typ=teo; fields=fs} ->
    let (new_teo,new_env) =
      begin match teo with
        | None -> None,env
        | Some te ->
          let (ty,en) = partial_alpha_sub_exp te in
          Some ty, en
      end in
    let new_td = DeclType.Enum {typ=new_teo; fields=fs} in
    {env with decl = Env.insert (Info.dummy,tn) new_td new_env.decl}
  | Header {fields=fs} ->
    let new_td = DeclType.Header {fields= List.map record_mapper fs} in
    {env with decl = Env.insert (Info.dummy,tn) new_td env.decl}
  | Struct {fields=fs} ->
    let new_td = DeclType.Struct {fields= List.map record_mapper fs} in
    {env with decl = Env.insert (Info.dummy,tn) new_td env.decl}
  | Function {type_params=tps; parameters=ps; return=rt} ->
    let new_tps = List.map (fun s -> if s = old_t then sub_t else s) tps in
    let new_ps = List.map param_mapper ps in
    let new_rt =
      begin match rt with
        | None -> None
        | Some ty -> Some (alpha_sub_exp env old_t sub_t ty |> fst)
      end in
    let new_td = DeclType.Function {type_params=new_tps; parameters=new_ps; return=new_rt} in
    {env with decl = Env.insert (Info.dummy,tn) new_td env.decl}
  | Parser {type_params=tps; parameters=ps} ->
    let new_tps = List.map (fun s -> if s = old_t then sub_t else s) tps in
    let new_ps = List.map param_mapper ps in
    let new_td = DeclType.Parser {type_params=new_tps; parameters=new_ps} in
    {env with decl = Env.insert (Info.dummy,tn) new_td env.decl}
  | Control {type_params=tps; parameters=ps} ->
    let new_tps = List.map (fun s -> if s = old_t then sub_t else s) tps in
    let new_ps = List.map param_mapper ps in
    let new_td = DeclType.Control {type_params=new_tps; parameters=new_ps} in
    {env with decl = Env.insert (Info.dummy,tn) new_td env.decl}
  | Package {type_params=tps; parameters=ps} ->
    let new_tps = List.map (fun s -> if s = old_t then sub_t else s) tps in
    let new_ps = List.map construct_param_mapper ps in
    let new_td = DeclType.Package {type_params=new_tps; parameters=new_ps} in
    {env with decl = Env.insert (Info.dummy,tn) new_td env.decl}

(* Returns a type expression alpha equivalent to [t]
 * where all occurences of [old_t] are replaced with [sub_t]
 *)
and alpha_sub_exp (env:Env.t) (old_t:string) (sub_t:string) (t:ExpType.t) : ExpType.t * Env.t =
  let partial_alpha_sub = alpha_sub_exp env old_t sub_t in
  match t with
  | TypeVar t_name -> if t_name = old_t then (TypeVar sub_t),env else t, env
  | String | Bool | Integer | Int _ | Bit _ | Var _ | Error -> t, env
  | Array {typ=teip; size=n} -> let (new_typ,new_env) = partial_alpha_sub teip in
    (Array {typ=new_typ; size=n}), new_env
  | Tuple {types=ts} ->
    let folder = fun (acc:ExpType.t list * Env.t) (teip:ExpType.t) ->
      begin let (new_typ,new_env) = alpha_sub_exp (snd acc) old_t sub_t teip in
        new_typ::(fst acc),new_env end in
    let (new_typs,final_env) = List.fold_left folder ([],env) ts in
    (Tuple {types=List.rev new_typs}),final_env
  | Set teip -> let (new_typ,new_env) = partial_alpha_sub teip in
    (Set new_typ), new_env
  | Name decl_name ->
    Name decl_name, alpha_sub_decl env old_t sub_t decl_name
  | Void -> Void,env
  (* | _ -> failwith "alpha_sub_exp edge match case" *)

(* Alpha Substitutes type params [t1s] for [t2s] in type [t]
 * where [t] is either an ExpType.t or a DeclType.t and
 * alpha_sub is the appropriate alpha substition function. *)
let alpha_sub_type_params env t2 t1s t2s : ExpType.t * Env.t =
  let typ_fold = fun (t,env:ExpType.t*Env.t) (tv_old,tv_sub:string*string) ->
    begin alpha_sub_exp env tv_old tv_sub t end in
  List.fold_left typ_fold (t2,env) (List.combine t2s t1s)

let rec check_decl_equality (env: Env.t) (t1:DeclType.t) (t2:DeclType.t) : bool =
  let rec_fields_match l r =
    let open RecordType in
    let field_compare = (fun fld1 fld2
                          -> String.compare fld1.name fld2.name) in
    let sl = List.sort field_compare l in
    let sr = List.sort field_compare r in
    let get_field_type = (fun fld -> fld.typ) in
    let tl = List.map get_field_type sl in
    let tr = List.map get_field_type sr in
    let checks = List.map2 (type_equality env) tl tr  in
    not (List.mem false checks) in

  let alpha_sub_fold_param env tp1s tp2s p2s : Env.t * Parameter.t list =
    begin let fold = fun (env,pl:Env.t*Parameter.t list) (p2:Parameter.t) ->
      let (new_t,new_env) = alpha_sub_type_params env p2.typ tp1s tp2s in
      let new_p2 = {p2 with typ=new_t} in (new_env,new_p2::pl) in
      let (nenv,ps) =  List.fold_left fold (env,[]) p2s in (nenv, List.rev ps) end in

  let alpha_sub_fold_construct_param env tp1s tp2s p2s : Env.t * ConstructParam.t list =
    begin let fold = fun (env,pl:Env.t*ConstructParam.t list) (p2:ConstructParam.t) ->
      let (new_t,new_env) = alpha_sub_type_params env p2.typ tp1s tp2s in
      let new_p2 = {p2 with typ=new_t} in (new_env,new_p2::pl) in
      let (nenv,ps) =  List.fold_left fold (env,[]) p2s in (nenv, List.rev ps) end in

  begin match t1, t2 with
    | HeaderUnion {union_fields = l}, HeaderUnion {union_fields = r} ->
        let open UnionType in
        let ufield_cmp = (fun uf1 uf2 -> String.compare uf1.name uf2.name) in
        let sl = List.sort ufield_cmp l in
        let sr = List.sort ufield_cmp r in
        let get_ufield_type = (fun uf -> Env.find (header_union_info,uf.h_type) env.exp |> fst) in
        let tl = List.map get_ufield_type sl in
        let tr = List.map get_ufield_type sr in
        let checks = List.map2 (type_equality env) tl tr in
        not (List.mem false checks)
      | Header {fields = l}, Header {fields = r}
        -> rec_fields_match l r
      | Struct {fields = l}, Struct { fields = r}
        -> rec_fields_match l r
      | Enum {typ = lto; fields = lfs}, Enum {typ = rto; fields = rfs}
        -> List.sort String.compare lfs = List.sort String.compare rfs &&
           begin match lto,rto with
             | Some lt, Some rt -> type_equality env lt rt
             | None, None -> true
             | _, _ -> false
           end
             (* why are errors lists of strings? *)
     | Error _, Error _ -> true
     | Control {type_params=tp1s; parameters=p1s;},
       Control {type_params=tp2s; parameters=p2s;}
     | Parser {type_params=tp1s; parameters=p1s;},
       Parser {type_params=tp2s; parameters=p2s;}
       -> let (nenv,newp2s) = alpha_sub_fold_param env tp1s tp2s p2s in
       param_equality nenv p1s newp2s
     | Package {type_params=tp1s; parameters=p1s;},
       Package {type_params=tp2s; parameters=p2s;}
       -> let (nenv,newp2s) = alpha_sub_fold_construct_param env tp1s tp2s p2s in
       construct_param_equality nenv p1s newp2s
     | Function {type_params=tp1s; parameters=p1s;return=r1},
       Function {type_params=tp2s; parameters=p2s;return=r2}
       -> let (nenv,newp2s) = alpha_sub_fold_param env tp1s tp2s p2s in
       param_equality nenv p1s newp2s &&
       begin match r1, r2 with
         | None, None -> true
         | Some rt1, Some rt2 ->
           let (newrt2,new_env) = alpha_sub_type_params env rt2 tp1s tp2s in
           type_equality new_env rt1 newrt2
         | _ -> false
         end
     | _,_  -> false
  end

(* alpha equivalent types are equal *)
and type_equality (env: Env.t) (t1:ExpType.t) (t2:ExpType.t) : bool =
  begin match t1,t2 with
    | Bool, Bool                                    -> true
    | String, String                                -> true
    | Bit { width = l}, Bit {width = r} when l = r  -> true
    | Int { width = l}, Int {width = r} when l = r  -> true
    | Integer, Integer                              -> true
    | Var {width = l}, Var {width = r} when l = r   -> true
    | Array {typ = lt; size = ls}, Array {typ = rt; size = rs}
      -> ls = rs && type_equality env lt rt
    | Error , Error                                 -> true
    | Tuple {types=t1s}, Tuple {types=t2s}
      -> let ts = List.combine t1s t2s in
      List.for_all (fun (ty1,ty2) -> type_equality env ty1 ty2) ts
    | Set ty1, Set ty2 -> type_equality env ty1 ty2
    | Name tn1, Name tn2
    | TypeVar tn1, TypeVar tn2 ->
      (* what to do if type names are not in the environment? *)
      let d1 = Env.find (Info.dummy,tn1) env.decl in
      let d2 = Env.find (Info.dummy,tn2) env.decl in
      check_decl_equality env d1 d2
    | _,_  -> false
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

let assert_same_type (env: Env.t) info1 info2 (typ1: ExpType.t) (typ2: ExpType.t) =
  if type_equality env typ1 typ2 then (typ1, typ2)
  else
    let info = Info.merge info1 info2 in
    raise_type_error info (Type_Difference (typ1, typ2))

let compile_time_known_expr (env: Env.t) (expr: Expression.t) : unit =
  failwith "Unimplemented"

let rec type_expression (env: Env.t) ((_, exp): Expression.t) : ExpType.t =
  match exp with
  | True ->
    ExpType.Bool
  | False ->
    ExpType.Bool
  | String _ ->
    ExpType.String
  | Int i ->
    type_int i
  | Name name ->
    Env.find name env.exp |> fst
  | TopLevel name ->
    Env.find_toplevel name env.exp |> fst
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
    type_function_call env func type_args args
  | NamelessInstantiation { typ; args } ->
    type_nameless_instantiation env typ args
  | Mask { expr; mask } ->
    type_mask env expr mask
  | Range { lo; hi } ->
    type_range env lo hi

and translate_type (env: Env.t) (typ: Type.t) : ExpType.t =
  let open Types.Type in
  let get_int_from_bigint num =
    begin match Bigint.to_int num with
      | Some n -> n;
      | None -> failwith "numeric type parameter is too large"
    end in
  match snd typ with
  | Bool -> Bool
  | Error -> Error
  | IntType e ->
    begin match Eval.eval_expression env e with
      | Int {value=v}
      | Bit {value=v}
      | Integer v     -> Int ({width= get_int_from_bigint v})
      | _ -> failwith "int type param must evaluate to an int"
    end
  | BitType e ->
    begin match Eval.eval_expression env e with
      | Int {value=v}
      | Bit {value=v}
      | Integer v     -> Bit ({width= get_int_from_bigint v})
      | _ -> failwith "bit type param must evaluate to an int"
    end
  | Varbit e ->
    begin match Eval.eval_expression env e with
      | Int {value=v}
      | Bit {value=v}
      | Integer v     -> Var ({width= get_int_from_bigint v})
      | _ -> failwith "varbit type param must evaluate to an int"
    end
  | TopLevelType ps -> Name (snd ps)
  | TypeName ps -> TypeVar (snd ps)
  | SpecializedType _ -> failwith "Unimplemented"
  | HeaderStack {header=ht; size=e}
    -> let hdt = translate_type env ht in
    let len =
      begin match Eval.eval_expression env e with
      | Int {value=v}
      | Bit {value=v}
      | Integer v     -> get_int_from_bigint v
      | _ -> failwith "header stack size must be a number"
      end in
    Array {typ=hdt; size=len}
  | Tuple tlist ->
    Tuple {types = List.map (translate_type env) tlist}
  | Void -> Void
  | DontCare -> failwith "TODO: type inference"


and type_int (_, value) =
  let open P4Int in
  match value.width_signed with
  | None -> ExpType.Integer
  | Some (width, true) -> ExpType.Int { width }
  | Some (width, false) -> ExpType.Bit { width }

(* Section 8.15
 * ------------
 *
 * Δ, T, Γ |- a : t[size]      Δ, T, Γ |- i : u, where numeric(u)
 * ----------------------------------------------------------
 *                Δ, T, Γ |- a[i] : t
 *
 * Some architectures may further require ctk(i).
 *)
and type_array_access env array index =
  let array_typ = array
  |> type_expression env
  |> assert_array (info array)
  in type_expression env index
  |> assert_numeric (info index)
  |> ignore;
  array_typ.typ

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
and type_bit_string_access env bits lo hi =
  failwith "Unimplemented"

(* Section 8.11
 * ------------
 *
 *      1 <= i <= n; Δ, T, Γ |- xi : ti
 * ------------------------------------------
 * Δ, T, Γ |- { x1, ..., xn } : (t1, ..., tn)
 *
 *)
and type_list env values =
  let type_valu = type_expression env in
  let types = List.map type_valu values in
  ExpType.Tuple { types }

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
  let arg_typ = type_expression env arg in
  let open Op in
  match op with
  | Not    -> assert_bool (info arg) arg_typ
  | BitNot -> assert_bit (info arg) arg_typ
  | UMinus -> assert_numeric (info arg) arg_typ |> ignore; arg_typ

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
and type_binary_op env (_, op) (l, r) =
  let open Op in
  let open ExpType in

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
  (*| Eq | NotEq when l_typ = r_typ -> ExpType.Bool *)(* FIXME *)
  | Eq | NotEq ->
     if type_equality env l_typ r_typ then ExpType.Bool
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
      | Bit { width = l }, Bit { width = r } -> l_typ
      | Int { width = l }, Bit { width = r } -> l_typ
      | Integer ,          Bit { width = r } -> l_typ
      | Bit { width = l }, Int { width = r } -> l_typ
      | Int { width = l }, Int { width = r } -> l_typ
      | Integer ,          Int { width = r } -> l_typ
      | _ -> failwith "Shift operands have improper types" (*TODO better error handling*)
    end

(* Section 8.9 *)
and type_cast env typ expr =
  failwith "type_cast Unimplemented"

(* ? *)
and type_type_member env typ name =
  failwith "Unimplemented"

(* Section 8.2
 * -----------
 *
 *       (e, error) ∈ T
 * --------------------------
 * Δ, T, Γ |- error.e : error
 *
 *)
and type_error_member env name =
  let errors = extract_errors env in
  if List.mem (snd name) errors then
    ExpType.Error
  else
    failwith "Unknown error"

(* Sections 6.6, 8.14 *)
and type_expression_member env expr name =
  let expr_typ = expr
  |> type_expression env
  (* |> assert_header_or_struct (info expr) *)
  in
  let open RecordType in
  let fields = begin match expr_typ with
    | Name na ->
      let d = Env.find (Info.dummy,na) env.decl in
      begin match d with
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
and type_ternary env cond tru fls =
  let _ = cond
  |> type_expression env
  |> assert_bool (info cond)
  in
  (type_expression env fls)
  |> ((type_expression env tru)
  |> assert_same_type env (info tru) (info fls))
  |> begin function
  | (ExpType.Integer, ExpType.Integer) -> failwith "unless the condition itself can be evaluated at compilation time"
  | (t1, t2) -> t1
  end

(* Section 8.17: Typing Function Calls
 *
 * Arguments are positional:
 *   Δ, T, Γ |- ef : tr  f<...Ai,...>(...di ti,...)
 *  for all i  Δ (union over j)(Aj -> uj) , T, Γ ei : ti
 * ------------------------------------------------------
 *     Δ, T, Γ |- ef<...ui,...>(...ei,...) : tr
 *
 * Arguments are named:
 *   Δ, T, Γ |- ef : tr  f<...Ai,...>(...di ti,...)
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
      begin match Env.find na env.decl with
      | DeclType.Function fr -> fr
      | _ -> failwith "Function name must be associated with a function type."
      end
    | _ -> failwith "function name must be a string"
  end in
let fun_type = get_fun_type func in
let open Parameter in
let params = fun_type.parameters in

let typ_ps = fun_type.type_params in

(* helper to extend delta environment *)
let extend_delta = fun (environ:Env.t) ((t_par,t_arg):string*ExpType.t) ->
  begin {environ with typ = Env.insert (Info.dummy, t_par)
                          t_arg environ.typ} end in

let env = List.fold_left extend_delta env (List.combine typ_ps arg_types) in

(* helper to extend the environment *)
(* unsure if this is necessary or makes sense *)
(* let extend_env = fun (environ:Env.t) ((par,ty),arg:(Parameter.t*ExpType.t)*Argument.t) ->
  begin {environ with exp=(Env.insert (fst arg,par.name)
                             (ty,par.direction) environ.exp)} end in *)

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
  (* rely on positional order *)
  (* Debugging:
  print_int (List.length params);
  print_newline ();
  print_int (List.length arg_types);
  print_newline (); *)
  let new_ctx = env in
    (* List.fold_left extend_env env (List.combine (List.combine params arg_types) args) in *)
  let check_positional = fun (par,arg:Parameter.t * Argument.t) ->
    begin match snd arg with
      | Expression {value=e} -> let t = type_expression new_ctx e in
        if type_equality new_ctx t par.typ then true else failwith "Function argument has incorrect type."
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
  (* let arg_list = List.combine args arg_types in *)
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
  (* let sorted_arg_types = List.map snd sorted_ta_list in *)

  let new_ctx = env in
    (* List.fold_left extend_env env (List.combine (List.combine sorted_params sorted_arg_types) sorted_args) in *)
  let check_named = fun (par,arg:Parameter.t * Argument.t) ->
    begin match snd arg with
      | KeyValue {value= e} -> let t = type_expression new_ctx e in
        if type_equality new_ctx t par.typ then true else failwith "Function argument has incorrect type."
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
  let open FunctionType in
  let post_check = fun ft ->
    match ft.return with
    | None -> failwith "function call must be non-void inside an expression"
    | Some rt -> rt,(StmType.Unit,env) in
  check_call env func type_args args post_check |> fst




(* Section 14.1 *)
and type_nameless_instantiation env typ args =
  failwith "Unimplemented"

(* Section 8.12.3 *)
and type_mask env expr mask =
  ExpType.Set
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

and expr_mem_check env expr mem =
  match expr with
  | (info', Expression.ExpressionMember {expr = _; name = (_, n)}) ->
    if n = mem then expr
    else raise_unfound_member info' mem
  | t -> raise_mismatch (fst t) "ExpressionMember" (type_expression env t)

and type_statement (env: Env.t) (stm: Statement.t) : (StmType.t * Env.t) =
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
  let open FunctionType in
  let post_check = fun ft ->
    let arg_types = List.map (translate_type env) type_args in
    (* helper to extend delta environment *)
    (* for now naively extend local delta environment instead of creating new symbols *)
    let extend_delta = fun (environ:Env.t) ((t_par,t_arg):string*ExpType.t) ->
      begin {environ with typ = Env.insert (Info.dummy, t_par)
                              t_arg environ.typ} end in
    let env = List.fold_left extend_delta env (List.combine ft.type_params arg_types) in
    let pfold = fun (acc:Env.t) (p:Parameter.t) ->
      match p.direction with
      | In -> acc
      | Out | InOut -> (* only out variables are added to the environment *)
        {env with exp = Env.insert (Info.dummy,p.name) (p.typ,p.direction) env.exp} in
    ExpType.Error,(StmType.Unit,List.fold_left pfold env ft.parameters) in
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
and type_direct_application env typ args =
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
and type_switch env expr cases =
  failwith "Unimplemented"

(* Section 10.3 *)
and type_declaration_statement env decl =
  failwith "Unimplemented"

and type_declaration (env: Env.t) ((_, decl): Declaration.t) : Env.t =
  match decl with
  | Constant { annotations = _; typ; name; value } ->
    type_constant env typ name value
  | Instantiation { annotations = _; typ; args; name } ->
    type_instantiation env typ args name
  | Parser { annotations = _; name; type_params; params; constructor_params; locals; states } ->
    type_parser env name type_params params constructor_params locals states
  | Control { annotations = _; name; type_params; params; constructor_params; locals; apply } ->
    type_control env name type_params params constructor_params locals apply
  | Package { annotations = _; name; type_params; params } ->
    type_package_type env name type_params params
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
  {env with exp = (Env.insert name (expr_typ,In) env.exp)}

(* Section 10.3 *)
and type_instantiation env typ args name =
  failwith "Unimplemented"

(* Section 12.2 *)
and type_parser env name type_params params ctor_params locals states =
  failwith "Unimplemented"

(* Section 13 *)
and type_control env name type_params params ctor_params locals apply =
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
  let p_fold = fun (acc,env:Parameter.t list * Env.t) (p:Types.Parameter.t) ->
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
      let new_env =  {env with exp = Env.insert p.variable (par.typ,par.direction) env.exp} in
    par::acc, new_env end in
  let (ps,body_env) = List.fold_left p_fold ([],env) params in
  let ps = List.rev ps in
  let rt = return |> translate_type env  in
  let sfold = fun (prev_type,envi:StmType.t*Env.t) (stmt:Statement.t) ->
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
  let funtype = DeclType.Function {parameters=ps;
                 type_params= type_params |> List.map snd;
                 return= Some rt} in
  {env with decl = Env.insert name funtype env.decl}

(* Section 7.2.9.1 *)
and type_extern_function env return name type_params params =
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
  | None -> {env with exp = (Env.insert name (expected_typ,In) env.exp)}
  | Some value -> let initialized_typ = type_expression env value in
    let expr_typ, _ = assert_same_type env (fst value) (fst value) expected_typ initialized_typ in
    {env with exp = (Env.insert name (expr_typ,In) env.exp)}


(* Section 12.11 *)
and type_value_set env typ size name =
  failwith "Unimplemented"

(* Section 13.1 *)
and type_action env name params body =
  failwith "Unimplemented"

(* Section 13.2 *)
and type_table env name properties =
  failwith "Unimplemented"

(* TODO: is there a cleaner type for this?
 * Can't return a new environment because TypeDef and NewType might need the type (typ_or_decl field)
 * Can't return a single type because some nodes (e.g. Error, MatchKind) declare multiple bindings at once
 *)
and type_type_declaration (env: Env.t) ((_, decl): TypeDeclaration.t) : Env.t =
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

and type_field env field =
  let TypeDeclaration.{ annotations = _; typ; name } = snd field in
  let name = snd name in
  let typ = translate_type env typ in
  RecordType.{ name; typ }

(* Section 7.2.2 *)
and type_header env name fields =
  let fields = List.map (type_field env) fields in
  let header_typ = DeclType.Header { fields } in
  { env with decl = Env.insert name header_typ env.decl }

(* Section 7.2.3 *)
and type_header_union env name fields =
  let open UnionType in
  let union_folder = fun acc -> fun field ->
    begin let open Types.TypeDeclaration in
      let {typ=ht; name=fn} = snd field in
      let ht = begin match snd ht with
        | TypeName tn -> snd tn
        | _ -> failwith "Header Union fields must be Headers"
      end in
      match Env.find (Info.dummy,ht) env.decl with
      | Header _ -> {name= snd fn; h_type=ht}::acc
      | _ -> failwith "Header Union field is undefined"
    end in
  let ufields = List.fold_left union_folder [] fields |> List.rev in
  let hu = DeclType.HeaderUnion {union_fields=ufields} in
  { env with decl = Env.insert name hu env.decl }

(* Section 7.2.5 *)
and type_struct env name fields =
  let fields = List.map (type_field env) fields in
  let struct_typ = DeclType.Struct { fields } in
  { env with decl = Env.insert name struct_typ env.decl }

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
  let errors = extract_errors env in
  let errors' = DeclType.Error (List.fold_left fold_unique errors members) in
  { env with decl = insert_errors errors' env }

and extract_errors env =
  match Env.find_toplevel (Info.dummy, "error") env.decl with
  | Error errors -> errors
  | _ -> failwith "[INTERNAL ERROR]: non-error type bound to error"

and insert_errors errors env =
  let open Env in
  Env.insert_toplevel (Info.dummy, "error") errors env.decl

(* Section 7.1.3 *)
and type_match_kind env members =
  let kinds = extract_match_kinds env in
  let kinds' = DeclType.MatchKind (List.fold_left fold_unique kinds members) in
  { env with decl = insert_match_kinds kinds' env }

and extract_match_kinds env =
  match Env.find_toplevel (Info.dummy, "match_kind") env.decl with
  | MatchKind kinds -> kinds
  | _ -> failwith "[INTERNAL ERROR]: non-error type bound to error"

and insert_match_kinds kinds env =
  let open Env in
  Env.insert_toplevel (Info.dummy, "match_kind") kinds env.decl

(* Section 7.2.1 *)
and type_enum env name members =
  let fields = List.map snd members in
  let enum_typ = DeclType.Enum { fields; typ = None } in
  { env with decl = Env.insert name enum_typ env.decl }

(* Section 8.3 *)
and type_serializable_enum env typ name members =
  failwith "Unimplemented"

(* Section 7.2.9.2 *)
and type_extern_object env name type_params methods =
  failwith "Unimplemented"

(* Section 7.3 *)
and type_type_def env name typ_or_decl =
  failwith "Unimplemented"

(* ? *)
and type_new_type env name typ_or_decl =
  failwith "Unimplemented"

(* Section 7.2.11.2 *)
and type_control_type env name type_params params =
  failwith "Unimplemented"

(* Section 7.2.11 *)
and type_parser_type env name type_params params =
  failwith "Unimplemented"

(* Section 7.2.12 *)
and type_package_type env name type_params params =
  failwith "Unimplemented"

(* Entry point function for type checker *)
let check_program (program:Types.program) : Env.t =
  let top_decls = match program with Program tds -> tds in
  let init_acc = Env.empty_env in
  let program_folder =
    fun (acc:Env.t) -> fun (top_decl:Types.TopDeclaration.t) ->
      begin match top_decl with
      | TypeDeclaration type_decl -> type_type_declaration acc type_decl
      | Declaration decl -> type_declaration acc decl
      end in
  List.fold_left program_folder init_acc top_decls
