module I = Info
open Core
open Env
open Types
open Value
module Info = I (* JNF: ugly hack *)

(*----------------------------------------------------------------------------*)
(* Declaration Evaluation *)
(*----------------------------------------------------------------------------*)

let rec eval_decl (env : EvalEnv.t) (d : Declaration.t) : EvalEnv.t =
  match snd d with
  | Constant {
      annotations = _;
      typ = t;
      value = v;
      name = (_,n);
    } -> eval_const_decl env t v n
  | Instantiation {
      annotations = _;
      typ = typ;
      args = args;
      name = (_,n);
    } -> eval_instantiation env typ args n
  | Parser {
      annotations = _;
      name = (_,n);
      type_params = _;
      params = _;
      constructor_params = _;
      locals = _;
      states = _;
    } -> eval_parser_decl env n d
  | Control {
      annotations = _;
      name = (_,n);
      type_params = _;
      params = _;
      constructor_params = _;
      locals = _;
      apply = _;
    } -> eval_control_decl env n d
  | Function {
      return = _;
      name = (_,n);
      type_params = _;
      params = ps;
      body = b;
    } -> eval_fun_decl env n ps b
  | ExternFunction {
      annotations = _;
      return = _;
      name = (_,n);
      type_params = _;
      params = ps;
    } -> eval_extern_fun_decl env n ps
  | Variable {
      annotations = _;
      typ = t;
      name = (_,n);
      init = v;
    } -> eval_decl_var env t n v
  | ValueSet {
      annotations = _;
      typ = _;
      size = _;
      name = _;
    } -> eval_set_decl ()
  | Action {
      annotations = _;
      name = (_,n);
      params = ps;
      body = b;
    } -> eval_action_decl env n ps b
  | Table {
      annotations = _;
      name = _;
      properties = _;
    } -> eval_table_decl ()
  | Header {
      annotations = _;
      name = (_,n);
      fields = _;
    } -> eval_header_decl env n d
  | HeaderUnion {
      annotations = _;
      name = (_,n);
      fields = _;
    } -> eval_union_decl env n d
  | Struct {
      annotations = _;
      name = (_,n);
      fields = _;
    } -> eval_struct_decl env n d
  | Error {
      members = l;
    } -> eval_error_decl env l
  | MatchKind {
      members = l;
    } -> eval_matchkind_decl env l
  | Enum {
      annotations = _;
      name = (_,n);
      members = _;
    } -> eval_enum_decl env n d
  | SerializableEnum {
      annotations = _;
      typ = _;
      name = _;
      members = _;
    } -> eval_senum_decl ()
  | ExternObject {
      annotations = _;
      name = (_,n);
      type_params = tps;
      methods = ms;
    } -> eval_extern_obj env n ms
  | TypeDef {
      annotations = _;
      name = _;
      typ_or_decl = _;
    } -> eval_type_def () (* probably needed for implicit casts *)
  | NewType {
      annotations = _;
      name = _;
      typ_or_decl = _;
    } -> eval_type_decl () (* probably needed for explicit casts *)
  | ControlType {
      annotations = _;
      name = (_,n);
      type_params = _;
      params = _;
    } -> eval_ctrltyp_decl env n d
  | ParserType {
      annotations = _;
      name = (_,n);
      type_params = _;
      params = _;
    } -> eval_prsrtyp_decl env n d
  | PackageType {
      annotations = _;
      name = (_,n);
      type_params = _;
      params = _;
    } -> eval_pkgtyp_decl env n d

and eval_const_decl (env : EvalEnv.t) (typ : Type.t) (e : Expression.t)
    (name : string) : EvalEnv.t =
  let name_expr = (Info.dummy, Expression.Name(Info.dummy, name)) in
  let env' = EvalEnv.insert_typ name typ env in
  fst (eval_assign env' SContinue name_expr e)

and eval_instantiation (env:EvalEnv.t) (typ : Type.t) (args : Argument.t list)
    (name : string) : EvalEnv.t =
  let (env', obj) = eval_nameless env typ args in
  EvalEnv.insert_val name obj env'

and eval_parser_decl (env : EvalEnv.t) (name : string)
    (decl : Declaration.t) : EvalEnv.t =
  EvalEnv.insert_decl name decl env

and eval_control_decl (env : EvalEnv.t) (name : string)
    (decl : Declaration.t) : EvalEnv.t =
  EvalEnv.insert_decl name decl env

and eval_fun_decl (env : EvalEnv.t) (name : string) (params : Parameter.t list)
    (body : Block.t) : EvalEnv.t =
  EvalEnv.insert_val name (VFun(params,body)) env

and eval_extern_fun_decl (env : EvalEnv.t) (name : string)
    (params : Parameter.t list) : EvalEnv.t =
  EvalEnv.insert_val name (VExternFun params) env

and eval_decl_var (env : EvalEnv.t) (typ : Type.t) (name : string)
    (init : Expression.t option) : EvalEnv.t =
  let env' = EvalEnv.insert_typ name typ env in
  match init with
  | None -> EvalEnv.insert_val name (init_val_of_typ env' name typ) env'
  | Some e ->
    let (env'', v) = eval_expression env' e in
    EvalEnv.insert_val name v env''

and eval_set_decl () = failwith "set decls unimplemented"

and eval_action_decl (env : EvalEnv.t) (name : string) (params : Parameter.t list)
    (body : Block.t) : EvalEnv.t  =
  EvalEnv.insert_val name (VAction(params, body)) env

and eval_table_decl () = failwith "tables unimplemented"

and eval_header_decl (env : EvalEnv.t) (name : string)
    (decl : Declaration.t) : EvalEnv.t =
  EvalEnv.insert_decl name decl env

and eval_union_decl (env : EvalEnv.t) (name : string)
    (decl : Declaration.t) : EvalEnv.t =
  EvalEnv.insert_decl name decl env

and eval_struct_decl (env : EvalEnv.t) (name : string)
    (decl : Declaration.t) : EvalEnv.t =
  EvalEnv.insert_decl name decl env

and eval_error_decl (env : EvalEnv.t) (errs : P4String.t list) : EvalEnv.t =
  let errs' = List.map errs ~f:snd in
  EvalEnv.insert_errs errs' env

and eval_matchkind_decl (env : EvalEnv.t) (mems : P4String.t list) : EvalEnv.t =
  mems
  |> List.map ~f:snd
  |> List.map ~f:(fun a -> (a, VMatchKind))
  |> (fun a -> EvalEnv.insert_vals a env)


and eval_enum_decl (env : EvalEnv.t) (name : string)
    (decl : Declaration.t) : EvalEnv.t =
  EvalEnv.insert_decl name decl env

and eval_senum_decl () = failwith "senums unimplemented"

and eval_extern_obj (env : EvalEnv.t) (name : string)
    (methods : MethodPrototype.t list) : EvalEnv.t =
  EvalEnv.insert_val name (VExternObject (name, methods)) env

and eval_type_def () = failwith "typedef unimplemented"

and eval_type_decl () = failwith "type decl unimplemented"

and eval_ctrltyp_decl (env : EvalEnv.t) (name : string)
    (decl : Declaration.t) : EvalEnv.t =
  EvalEnv.insert_decl name decl env

and eval_prsrtyp_decl (env : EvalEnv.t) (name : string)
    (decl : Declaration.t) : EvalEnv.t =
  EvalEnv.insert_decl name decl env

and eval_pkgtyp_decl (env : EvalEnv.t) (name : string)
    (decl : Declaration.t) : EvalEnv.t =
  EvalEnv.insert_decl name decl env

and init_val_of_typ (env : EvalEnv.t) (name : string) (typ : Type.t) : value =
  match snd typ with
  | Bool               -> VBool false
  | Error              -> VError "NoError"
  | IntType expr       -> init_val_of_int env expr
  | BitType expr       -> init_val_of_bit env expr
  | VarBit expr        -> failwith "varbit init unimplemented"
  | TopLevelType (_,n) -> init_val_of_typname env n name true
  | TypeName (_,n)     -> init_val_of_typname env n name false
  | SpecializedType _  -> failwith "specialized init unimplemented"
  | HeaderStack _      -> failwith "header stack init unimplemented"
  | Tuple _            -> failwith "tuple init unimplemented"
  | Void               -> VNull
  | DontCare           -> failwith "no init value for dont care types"

and init_val_of_int (env : EvalEnv.t) (expr : Expression.t) : value =
  match snd (eval_expression env expr) with
  | VInteger n -> VInt(Bigint.to_int_exn n, Bigint.zero)
  | _ -> failwith "int width is not an int"

and init_val_of_bit (env : EvalEnv.t) (expr : Expression.t) : value =
  match snd (eval_expression env expr) with
  | VInteger n -> VBit(Bigint.to_int_exn n, Bigint.zero)
  | _ -> failwith "bit width is not an int"

and init_val_of_typname (env : EvalEnv.t) (tname : string) (vname : string) (b : bool) : value =
  let f = EvalEnv.(if b then find_decl_toplevel else find_decl) in
  match snd (f tname env) with
  | Struct {fields=fs;_}      -> init_val_of_struct env vname fs
  | Header {fields=fs;_}      -> init_val_of_header env vname fs
  | HeaderUnion {fields=fs;_} -> init_val_of_union env vname fs
  | _ -> failwith "decl init value unimplemented"

and init_val_of_struct (env : EvalEnv.t) (name : string)
    (fs : Declaration.field list) : value =
  VStruct (name, List.map fs ~f:(init_binding_of_field env))

and init_val_of_header (env : EvalEnv.t) (name : string)
    (fs : Declaration.field list) : value =
  VHeader (name, List.map fs ~f:(init_binding_of_field env), false)

and init_val_of_union (env : EvalEnv.t) (name : string)
    (fs : Declaration.field list) : value =
  let fs' = List.map fs ~f:(init_binding_of_field env) in
  let bs = List.map fs' ~f:(fun (a,b) -> (a,false)) in
  VUnion (name, fs', bs)

(*----------------------------------------------------------------------------*)
(* Statement Evaluation *)
(*----------------------------------------------------------------------------*)

and eval_statement (env :EvalEnv.t) (sign : signal)
    (stm : Statement.t) : (EvalEnv.t * signal) =
  match snd stm with
  | MethodCall{func;type_args;args} -> eval_method_call env sign func args
  | Assignment{lhs;rhs}             -> eval_assign env sign lhs rhs
  | DirectApplication{typ;args}     -> failwith "direct applications unimplemented"
  | Conditional{cond;tru;fls}       -> eval_conditional env sign cond tru fls
  | BlockStatement{block}           -> eval_block env sign block
  | Exit                            -> failwith "exits unimplemented"
  | EmptyStatement                  -> (env, sign)
  | Return{expr}                    -> eval_return env sign expr
  | Switch{expr;cases}              -> failwith "switch stms unimplemented"
  | DeclarationStatement{decl}      -> eval_decl_stm env sign decl

and eval_method_call (env : EvalEnv.t) (sign : signal) (func : Expression.t)
    (args : Argument.t list) : EvalEnv.t * signal =
  match sign with
  | SContinue -> (fst (eval_funcall env func args), sign)
  | SReturn v -> (env, SReturn v)
  | SExit     -> failwith "exit unimplemented"

and eval_assign (env : EvalEnv.t) (s : signal) (lhs : Expression.t)
    (rhs : Expression.t) : EvalEnv.t * signal =
  print_endline "tis an assign";
  let (env', v) = eval_expression env rhs in
  let lv = lvalue_of_expr lhs in
  match s with
  | SContinue -> (eval_assign' env' lv v, SContinue)
  | SReturn v -> (env, SReturn v)
  | SExit     -> failwith "exit unimplemented"

and eval_assign' (env : EvalEnv.t) (lhs : lvalue) (rhs : value) : EvalEnv.t =
  match lhs with
  | LName n -> assign_name env n rhs
  | LTopName n -> failwith "top assign unimplemented"
  | LMember(lv, mname) -> print_endline "assigne to lmemeber"; assign_member env lv mname rhs
  | LBitAccess _ -> failwith "bitstring access assignment unimplemented"
  | LArrayAccess _ -> failwith "array access assignment unimplemented"

and assign_name (env : EvalEnv.t) (name : string) (rhs : value) : EvalEnv.t =
  let t = EvalEnv.find_typ name env in
  match rhs with
  | VTuple l ->
    let f = match snd (decl_of_typ env t) with
      | Declaration.Struct _ -> struct_of_list env name
      | Declaration.Header _ -> header_of_list env name
      | _ -> (fun l -> VTuple l) in (* implicit cast from tuples *)
    EvalEnv.insert_val name (f l) env
  | _ -> EvalEnv.insert_val name rhs env

and assign_member (env : EvalEnv.t) (lv : lvalue) (mname : string)
    (rhs : value) : EvalEnv.t =
  let v = value_of_lvalue env lv in
  print_endline "got past value of lvalue";
  let rhs' = match v with
    | VStruct(n,l)    -> print_endline "tis struct mem"; assign_struct_mem env rhs mname n l
    | VHeader(n,l,b)  -> print_endline "tis header mem"; assign_header_mem env rhs mname n l b
    | VUnion(n,vs,bs) -> print_endline "tis union mem"; assign_union_mem env rhs mname n vs bs
    | _ -> failwith "member assignment unimplemented" in
  eval_assign' env lv rhs'

and value_of_lvalue (env : EvalEnv.t) (lv : lvalue) : value =
  match lv with
  | LName n                -> EvalEnv.find_val n env
  | LTopName n             -> EvalEnv.find_val_toplevel n env
  | LMember(lv, n)         -> value_of_lmember env lv n
  | LBitAccess(lv, hi, lo) -> value_of_lbit env lv hi lo
  | LArrayAccess(lv, idx)  -> value_of_larray env lv idx

and value_of_lmember (env : EvalEnv.t) (lv : lvalue) (n : string) : value =
  match value_of_lvalue env lv with
  | VStruct(_, vs)
  | VHeader(_, vs, _)
  | VUnion(_, vs, _) -> List.Assoc.find_exn vs n ~equal:(=)
  | _ -> failwith "no lvalue member"

and value_of_lbit (env : EvalEnv.t) (lv : lvalue) (hi : Expression.t)
    (lo : Expression.t) : value =
  failwith "value of l unimplemented"

and value_of_larray (env : EvalEnv.t) (lv : lvalue)
    (idx : Expression.t) : value =
  failwith "value of l unimplemented"

and assign_struct_mem (env : EvalEnv.t) (rhs : value) (fname : string)
    (sname : string) (l : (string * value) list) : value =
  VStruct (sname, (fname, rhs) :: l)

and assign_header_mem (env : EvalEnv.t) (rhs : value) (fname : string)
    (hname : string) (l : (string * value) list) (b : bool) : value =
  VHeader(hname, (fname, rhs) :: l, b)

and assign_union_mem (env : EvalEnv.t) (rhs : value)
    (fname : string) (uname : string) (l : (string * value) list)
    (vbs : (string * bool) list) : value =
  let t = typ_of_union_field env uname fname in
  let dummy_env = EvalEnv.insert_typ fname t env in
  let rhs' = match rhs with
    | VTuple l -> header_of_list dummy_env fname l
    | x -> x in
  let vbs' = List.map vbs ~f:(fun (s,_) -> (s, s=fname)) in
  VUnion(uname, (fname, rhs') :: l, vbs')

and typ_of_union_field (env : EvalEnv.t) (uname : string)
    (fname : string) : Type.t =
  print_endline "doing the union mem thing";
  let t = EvalEnv.find_typ uname env in
  print_endline "found type";
  let (_, d) = decl_of_typ env t in
  print_endline "found decl";
  let fs = match d with
    | HeaderUnion u -> u.fields
    | _ -> failwith "not a union" in
  match List.filter fs ~f:(fun a -> snd (snd a).name = fname) with
  | h :: _ -> (snd h).typ
  | _ -> failwith "field name not found"

and eval_application () = failwith "direct application unimplemented"

and eval_conditional (env : EvalEnv.t) (sign : signal) (cond : Expression.t)
    (tru : Statement.t) (fls : Statement.t option) : EvalEnv.t * signal =
  match sign with
  | SContinue -> eval_conditional' env cond tru fls
  | SReturn v -> (env, SReturn v)
  | SExit     -> failwith "exit unimplmented"

and eval_conditional' (env : EvalEnv.t) (cond : Expression.t) (tru : Statement.t)
    (fls : Statement.t option) : EvalEnv.t * signal =
  let (env', v) = eval_expression env cond in
  match v with
    | VBool true  -> eval_statement env' SContinue tru
    | VBool false ->
      begin match fls with
        | None -> (env, SContinue)
        | Some fls' -> eval_statement env' SContinue fls'  end
    | _ -> failwith "conditional guard must be a bool"

and eval_block (env : EvalEnv.t) (sign :signal) (block : Block.t) : (EvalEnv.t * signal) =
  let block = snd block in
  let f (env,sign) stm =
    match sign with
    | SContinue -> eval_statement env sign stm
    | SReturn v -> (env, sign)
    | SExit     -> failwith "exit unimplemented" in
  List.fold_left block.statements ~init:(env,sign) ~f:f

and eval_exit () = failwith "exit unimplemented"

and eval_return (env : EvalEnv.t) (sign : signal)
    (expr : Expression.t option) : (EvalEnv.t * signal) =
  let (env',v) =
    match expr with
    | None   -> (env, VNull)
    | Some e -> eval_expression env e in
  match sign with
  | SContinue -> (env', SReturn v)
  | SReturn v -> (env, SReturn v)
  | SExit     -> failwith "exit unimplemented"

and eval_switch () = failwith "switch stm unimplemented"

and eval_decl_stm (env : EvalEnv.t) (sign : signal)
    (decl : Declaration.t) : EvalEnv.t * signal =
  match sign with
  | SContinue -> (eval_decl env decl, SContinue)
  | SReturn v -> (env, SReturn v)
  | SExit     -> failwith "exit unimplemented"

and lvalue_of_expr (expr : Expression.t) =
  match snd expr with
  | Name(_,n) -> LName n
  | TopLevel(_,n) -> LTopName n
  | ExpressionMember{expr=e; name=(_,n)} -> LMember(lvalue_of_expr e, n)
  | BitStringAccess{bits;lo;hi} -> LBitAccess(lvalue_of_expr bits, lo, hi)
  | ArrayAccess{array;index} -> LArrayAccess(lvalue_of_expr array, index)
  | _ -> failwith "not an lvalue"

and struct_of_list (env : EvalEnv.t) (name : string) (l : value list) : value =
  env
  |> EvalEnv.find_typ name
  |> decl_of_typ env
  |> snd
  |> (function Declaration.Struct s -> s.fields | _ -> failwith "not a struct")
  |> List.map ~f:(fun x -> snd (snd x).name)
  |> (fun fs i v -> (List.nth_exn fs i, v))
  |> (fun f -> List.mapi l ~f:f)
  |> (fun l -> VStruct (name, l))

and header_of_list (env : EvalEnv.t) (name : string) (l : value list) : value =
  env
  |> EvalEnv.find_typ name
  |> decl_of_typ env
  |> snd
  |> (function Declaration.Header s -> s.fields | _ -> failwith "not a struct")
  |> List.map ~f:(fun x -> snd (snd x).name)
  |> (fun fs i v -> (List.nth_exn fs i, v))
  |> (fun f -> List.mapi l ~f:f)
  |> (fun l -> VHeader (name, l, true))

(*----------------------------------------------------------------------------*)
(* Expression Evaluation *)
(*----------------------------------------------------------------------------*)

and eval_expression (env : EvalEnv.t) (exp : Expression.t) : EvalEnv.t * value =
  match snd exp with
  | True                              -> (env, VBool true)
  | False                             -> (env, VBool false)
  | Int(_,n)                          -> (env, eval_p4int n)
  | String (_,value)                  -> (env, VString value)
  | Name (_,name)                     -> (env, EvalEnv.find_val name env)
  | TopLevel (_,name)                 -> (env, EvalEnv.find_val_toplevel name env)
  | ArrayAccess({array=a; index=i})   -> eval_array env a i
  | BitStringAccess({bits;lo;hi})     -> eval_bit_string_access env bits lo hi
  | List{values}                      -> eval_list env values
  | UnaryOp{op;arg}                   -> eval_unary env op arg
  | BinaryOp{op; args=(l,r)}          -> eval_binop env op l r
  | Cast{typ;expr}                    -> eval_cast env typ expr
  | TypeMember{typ;name}              -> eval_typ_mem env typ (snd name)
  | ErrorMember t                     -> (env, EvalEnv.find_err (snd t) env)
  | ExpressionMember{expr;name}       -> eval_expr_mem env expr name
  | Ternary{cond;tru;fls}             -> eval_ternary env cond tru fls
  | FunctionCall{func;type_args;args} -> eval_funcall env func args
  | NamelessInstantiation{typ;args}   -> eval_nameless env typ args
  | Mask{expr;mask}                   -> eval_mask_expr env expr mask
  | Range{lo;hi}                      -> eval_range_expr env lo hi

and eval_p4int (n : P4Int.pre_t) : value =
  match n.width_signed with
  | None          -> VInteger n.value
  | Some(w,true)  -> VInt (w, n.value)
  | Some(w,false) -> VBit (w, n.value)

and eval_array (env : EvalEnv.t) (a : Expression.t)
    (i : Expression.t) : EvalEnv.t * value =
  failwith "header stacks unimplemented"

and eval_bit_string_access (env : EvalEnv.t) (s : Expression.t)
    (m : Expression.t) (l : Expression.t) : EvalEnv.t * value =
  let (env', m) = eval_expression env m in
  let (env'', l) = eval_expression env' l in
  let (env''', s) = eval_expression env'' s in
  let m' = int_of_val m in
  let l' = int_of_val l in
  match m, l, s with
  | VBit(_, vm), VBit(_, vl), VBit(w1, v1) ->
    let v = (Bigint.shift_left v1 (l'+1) |>
             Bigint.shift_right) (w1-m'+l') in
    (env''', VBit(m'-l'+1, v))
  | _ -> failwith "bit string access unimplemented"

and eval_list (env : EvalEnv.t) (values : Expression.t list) : EvalEnv.t * value =
  values
  |> List.fold_map ~f:eval_expression ~init:env
  |> (fun (e,l) -> (e, VTuple l))

and eval_unary (env : EvalEnv.t) (op : Op.uni) (e : Expression.t) : EvalEnv.t * value =
  let (env', e') = eval_expression env e in
  match snd op, e' with
  | UMinus, VBit(w,v) -> Bigint.(env', VBit(w, (power_of_two w) - v))
  | UMinus, VInt(w,v) -> Bigint.(env', VBit(w, -v))
  | BitNot, VBit(w,v) -> Bigint.(env', VBit(w, -v))
  | BitNot, VInt(w,v) -> Bigint.(env', VInt(w, -v))
  | Not, VBool b      -> (env', VBool (not b))
  | _ -> failwith "unary op unimplemented"

and eval_binop (env : EvalEnv.t) (op : Op.bin) (l : Expression.t)
    (r : Expression.t) : EvalEnv.t * value =
  let (env',l) = eval_expression env l in
  let (env'',r) = eval_expression env' r in
  let f = begin match snd op with
    | Plus     -> eval_two Bigint.( + )
    | PlusSat  -> eval_sat Bigint.( + )
    | Minus    -> eval_two Bigint.( - )
    | MinusSat -> eval_sat Bigint.( - )
    | Mul      -> eval_two Bigint.( * )
    | Div      -> eval_two Bigint.( / )
    | Mod      -> eval_two Bigint.rem
    | Shl      -> eval_shift Bigint.shift_left
    | Shr      -> eval_shift Bigint.shift_right
    | Le       -> eval_compare (<=)
    | Ge       -> eval_compare (>=)
    | Lt       -> eval_compare (<)
    | Gt       -> eval_compare (>)
    | Eq       -> eval_eq true
    | NotEq    -> eval_eq false
    | BitAnd   -> eval_two Bigint.bit_and
    | BitXor   -> eval_two Bigint.bit_xor
    | BitOr    -> eval_two Bigint.bit_or
    | PlusPlus -> eval_concat
    | And      -> eval_and_or (&&)
    | Or       -> eval_and_or (||) end in
  (env'', f l r)

and eval_cast (env : EvalEnv.t) (typ : Type.t)
    (expr : Expression.t) : EvalEnv.t * value =
  let build_bit w v =
    VBit (int_of_val w, Bigint.of_int v) in
  let changesize w v l =
    let new_w = l |> int_of_val in
    let value = if new_w >= w then v
      else (Bigint.shift_left v (w - new_w) |>
            Bigint.shift_right) (w - new_w) in
    (new_w, value) in
  let (env', expr') = eval_expression env expr in
  match expr', snd typ with
  | VBit(1, v), Type.Bool ->
    if Bigint.(=) v Bigint.zero
    then (env', VBool(false))
    else if Bigint.(=) v Bigint.one
    then (env', VBool(true))
    else failwith "can't cast this bitstring to bool"
  | VBool(b), Type.BitType(e) ->
    let (env'', e') = eval_expression env' e in
    if b then (env'', build_bit e' 1)
    else (env'', build_bit e' 0)
  | VInt(w, v), Type.BitType(w') ->
    let turn_pos w v =
      if Bigint.(<) v Bigint.zero
      then Bigint.(+) v (power_of_two (w+1))
      else v in
    (env', VBit(w, turn_pos w v))
  | VBit(w, v), Type.IntType(w') ->
    let neg_bit w v =
      if Bigint.(>=) v (power_of_two (w-1))
      then Bigint.(-) v (power_of_two w)
      else v in
    (env', VInt(w, neg_bit w v))
  | VBit(w, v), Type.BitType(l) ->
    let (env'', l') = eval_expression env' l in
    let width, value = changesize w v l' in
    (env'', VBit(width, value))
  (* TODO: validate: Should be shift_right_truncate*)
  | VInt(w, v), Type.IntType(l) ->
    let (env'', l') = eval_expression env l in
    let (width, value) = changesize w v l' in
    (env'', VInt(width, value))
  | _ -> failwith "type cast unimplemented" (* TODO *)

and eval_typ_mem (env : EvalEnv.t) (typ : Type.t)
    (name : string) : EvalEnv.t * value =
  match snd (decl_of_typ env typ) with
  | Declaration.Enum {members=ms;name=(_,n);_} ->
    let mems = List.map ms ~f:snd in
    if List.mem mems name ~equal:(=)
    then (env, VEnumField (n, name))
    else raise (UnboundName name)
  | _ -> failwith "typ mem unimplemented"

and eval_expr_mem (env : EvalEnv.t) (expr : Expression.t)
    (name : P4String.t) : EvalEnv.t * value =
  let (env', v) = eval_expression env expr in
  match v with
  | VNull
  | VBool _
  | VInteger _
  | VBit _
  | VInt _
  | VTuple _
  | VSet _
  | VString _
  | VError _
  | VMatchKind
  | VFun _
  | VBuiltinFun _
  | VAction _             -> failwith "expr member does not exist"
  | VStruct (_, fs)       -> eval_struct_mem env' (snd name) fs
  | VHeader (n, fs, vbit) -> eval_header_mem env' (snd name) expr fs vbit
  | VUnion (_, fs, _)     -> eval_union_mem env' (snd name) fs
  | VEnumField _
  | VExternFun _
  | VExternObject _
  | VRuntime _
  | VObjstate _           -> failwith "expr member unimplemented"

and eval_struct_mem (env : EvalEnv.t) (name : string)
    (fs : (string * value) list) : EvalEnv.t * value =
  (env, List.Assoc.find_exn fs name ~equal:(=))

and eval_header_mem (env : EvalEnv.t) (fname : string) (e : Expression.t)
    (fs : (string * value) list) (valid : bool) : EvalEnv.t * value =
  match fname with
  | "isValid"    -> (env, VBuiltinFun(fname, lvalue_of_expr e))
  | "setValid"   -> (env, VBuiltinFun(fname, lvalue_of_expr e))
  | "setInvalid" -> (env, VBuiltinFun(fname, lvalue_of_expr e))
  | _ -> (env, List.Assoc.find_exn fs fname ~equal:(=))

and eval_union_mem (env : EvalEnv.t) (fname : string)
    (fs : (string * value) list) : EvalEnv.t * value =
  (env, List.Assoc.find_exn fs fname ~equal:(=))

and eval_ternary (env : EvalEnv.t) (c : Expression.t) (te : Expression.t)
    (fe : Expression.t) : EvalEnv.t * value =
  let (env', c') = eval_expression env c in
  match c' with
  | VBool(true)  -> (eval_expression env' te)
  | VBool(false) -> (eval_expression env' fe)
  | _ -> failwith "ternary guard must be a bool"

and eval_funcall (env : EvalEnv.t) (func : Expression.t)
    (args : Argument.t list) : EvalEnv.t * value =
  let (env', cl) = eval_expression env func in
  match cl with
  | VNull
  | VBool _
  | VInteger _
  | VBit _
  | VInt _
  | VTuple _
  | VSet _
  | VString _
  | VError _
  | VMatchKind
  | VStruct _
  | VHeader _
  | VUnion _
  | VEnumField _
  | VExternFun _
  | VExternObject _
  | VRuntime _
  | VObjstate _            -> failwith "unreachable"
  | VBuiltinFun(n,vs)      -> eval_builtin env n vs
  | VAction (params, body)
  | VFun (params, body)    -> eval_funcall' env' params args body

and eval_builtin (env : EvalEnv.t) (name : string)
    (lv : lvalue) : EvalEnv.t * value =
  match name with
  | "setValid"   -> eval_setvalid env lv
  | "setInvalid" -> eval_setinvalid env lv
  | "isValid"    -> eval_isvalid env lv
  | _ -> failwith "builtin unimplemented"

and eval_setvalid (env : EvalEnv.t) (lv : lvalue) : EvalEnv.t * value =
  match lv with
  | LName n ->
    begin match EvalEnv.find_val n env with
      | VHeader (n', fs, b) ->
        (EvalEnv.insert_val n' (VHeader(n', fs, true)) env, VNull)
      | _ -> failwith "not a header" end
  | LMember(LName n1, n2) ->
    begin match EvalEnv.find_val n1 env with
      | VUnion (_, fs, vs) ->
        let vs' = List.map vs ~f:(fun (a,_) -> (a,false)) in
        print_endline "setvlaid worked fine";
        (EvalEnv.insert_val n1 (VUnion(n1, fs, vs')) env, VNull)
      | _ -> failwith "not a union" end
  | _ -> failwith "unimplemented header validity"

and eval_setinvalid (env : EvalEnv.t) (lv : lvalue) : EvalEnv.t * value =
  match lv with
  | LName n ->
    begin match EvalEnv.find_val n env with
      | VHeader (n', fs, b) ->
        (EvalEnv.insert_val n' (VHeader(n', fs, false)) env, VNull)
      | _ -> failwith "not a header" end
  | _ -> failwith "unimplemented header validity"

and eval_isvalid (env : EvalEnv.t) (lv : lvalue) : EvalEnv.t * value =
match lv with
  | LName n ->
    begin match EvalEnv.find_val n env with
      | VHeader (_, _, b) -> (env, VBool b)
      | _ -> failwith "not a header" end
  | LMember(LName n1, n2) ->
    begin match EvalEnv.find_val n1 env with
      | VUnion (_, fs, vs) ->
        (env, VBool(List.Assoc.find_exn vs n2 ~equal:(=)))
      | _ -> failwith "not a union" end
  | _ -> failwith "unimplemented header validity"

and eval_funcall' (env : EvalEnv.t) (params : Parameter.t list)
    (args : Argument.t list) (body : Block.t) : EvalEnv.t * value =
  let (env', fenv) = eval_inargs env params args in
  EvalEnv.print_env fenv;
  let (fenv', sign) = eval_block fenv SContinue body in
  EvalEnv.print_env fenv';
  let final_env = eval_outargs env' fenv' params args in
  match sign with
  | SReturn v -> (final_env, v)
  | SContinue -> (final_env, VNull)
  | SExit -> failwith "function did not return"

and eval_nameless (env : EvalEnv.t) (typ : Type.t)
    (args : Argument.t list) : EvalEnv.t * value =
  let (info ,decl) = decl_of_typ env typ in
  match decl with
  | Control typ_decl ->
    let (env',state) = eval_inargs env typ_decl.constructor_params args in
    let state' = state |> EvalEnv.get_val_firstlevel |> List.rev in
    (env', VObjstate((info, decl), state'))
  | Parser typ_decl ->
    let (env',state) = eval_inargs env typ_decl.constructor_params args in
    let state' = state |> EvalEnv.get_val_firstlevel |> List.rev in
    (env', VObjstate((info, decl), state'))
  | PackageType pack_decl ->
    let (env', state) = eval_inargs env pack_decl.params args in
    let state' = state |> EvalEnv.get_val_firstlevel |> List.rev in
    (env', VObjstate((info, decl), state'))
  | _ -> failwith "instantiation unimplemented"

and eval_mask_expr env e m =
  let (env', v1)  = eval_expression env  e in
  let (env'', v2) = eval_expression env' m in
  (env'', VSet(SMask(v1,v2)))

and eval_range_expr env lo hi =
  let (env', v1)  = eval_expression env  lo in
  let (env'', v2) = eval_expression env' hi in
  (env'', VSet(SRange(v1,v2)))


and eval_inargs (env : EvalEnv.t) (params : Parameter.t list)
      (args : Argument.t list) : EvalEnv.t * EvalEnv.t =
  let f env e =
    match snd e with
    | Argument.Expression {value=expr} -> eval_expression env expr
    | Argument.KeyValue _
    | Argument.Missing -> failwith "missing args unimplemented" in
  let (env',arg_vals) = List.fold_map args ~f:f ~init:env in
  let fenv = EvalEnv.push_scope (EvalEnv.get_toplevel env') in
  let g e (p : Parameter.t) v =
    let name = snd (snd p).variable in
    let v' = match v with
      | VHeader (n,l,b) -> VHeader (name, l, b)
      | VStruct (n,l) -> VStruct (name,l)
      | _ -> v in
    match (snd p).direction with
    | None ->
      e
      |> EvalEnv.insert_val (snd (snd p).variable) v'
      |> EvalEnv.insert_typ (snd (snd p).variable) (snd p).typ
    | Some x -> begin match snd x with
      | InOut
      | In ->
        e
        |> EvalEnv.insert_val (snd (snd p).variable) v'
        |> EvalEnv.insert_typ (snd (snd p).variable) (snd p).typ
      | Out -> e end in
  let fenv' = List.fold2_exn params arg_vals ~init:fenv ~f:g in
  (env', fenv')

and eval_outargs (env : EvalEnv.t) (fenv : EvalEnv.t)
    (params : Parameter.t list) (args : Argument.t list) : EvalEnv.t =
  let h e (p:Parameter.t) a =
    match (snd p).direction with
    | None -> e (* treat directionless as in *)
    | Some x -> begin match snd x with
      | InOut
      | Out ->
        let v = EvalEnv.find_val (snd (snd p).variable) fenv in
        let lhs = begin match snd a with
          | Argument.Expression {value=expr} -> expr
          | Argument.KeyValue _
          | Argument.Missing -> failwith "missing args unimplemented" end in
        eval_assign' e (lvalue_of_expr lhs) v
      | In -> e end in
  List.fold2_exn params args ~init:env ~f:h

and eval_sat op l r =
  let compute m n w =
    let a = Bigint.abs (op m n) in
    if  Bigint.(<) a m || Bigint.(<) a n then power_of_two w else a in
  match l,r with
  | VBit(w1,v1), VBit(w2, v2) -> VBit(w1, compute v1 v2 w1)
  | VInt(w1,v1), VInt(w2, v2) -> VInt(w1, compute v1 v2 (w1-1))
  | _ -> failwith "binary logical operation only works on bitstrings"

and eval_shift op l r =
  match l,r with
  | VBit(w1, v1), VBit(_, v2)
  | VBit(w1, v1), VInt(_, v2) ->
    if v1 >= Bigint.zero
    then VBit(w1, op v1 (Bigint.to_int_exn v2))
    else failwith "can't shift with a negative amount"
  | _ -> failwith "shift doesn't works on this type"

and eval_eq (op : bool) (l : value) (r : value) : value =
  match l,r with
  | VBit(_, v1), VBit(_, v2)
  | VInt(_, v1), VInt(_, v2)
  | VInteger v1, VInteger v2 -> VBool (if op then v1 = v2 else v1 <> v2)
  | VBool v1, VBool v2 -> VBool (if op then v1 = v2 else v1 <> v2)
  | _ -> failwith "equality for varbit binary comparison only works on bitstrings"

and eval_compare op l r =
  match l,r with
  | VBit(_, v1), VBit(_, v2)
  | VInt(_, v1), VInt(_, v2) -> VBool(op v1 v2)
  | _ -> failwith " binary comparison only works on fixed length integer"

and eval_two op l r =
  match l,r with
  | VBit(w1, v1), VBit(_, v2) -> VBit(w1, op v1 v2)
  | VInt(w1, v1), VInt(_, v2) -> VInt(w1, op v1 v2)
  | _ -> failwith "binary logical operation only works on bitstrings"

and eval_concat l r =
  let concat m n wn =
    Bigint.( + ) (Bigint.shift_left m wn) n in
  match l,r with
  | VBit(w1, v1), VBit(w2, v2) -> VBit(w1+w2, concat v1 v2 w2)
  | VInt(w1, v1), VInt(w2, v2) -> VInt(w1+w2, concat v1 v2 w2)
  | _ -> failwith " binary concatenation only works on fixed length integer"

and eval_and_or op l r =
  match l,r with
  | VBool(bl), VBool(br) -> VBool(op bl br)
  | _ -> failwith "and / or operation only works on Bools"

(*----------------------------------------------------------------------------*)
(* Parser Evaluation *)
(*----------------------------------------------------------------------------*)

and eval_parser (env : EvalEnv.t) (locals : Declaration.t list)
    (states : Parser.state list) : EvalEnv.t =
  let env' = List.fold_left locals ~init:env ~f:eval_decl in
  let states' = List.map states ~f:(fun s -> snd (snd s).name, s) in
  let start = List.Assoc.find_exn states' "start" ~equal:(=) in
  eval_state_machine env' states' start

and eval_state_machine (env : EvalEnv.t) (states : (string * Parser.state) list)
    (state : Parser.state) : EvalEnv.t =
  let (stms, transition) =
    match snd state with
    | {statements=stms; transition=t;_} -> (stms, t) in
  let stms' = (Info.dummy, Statement.BlockStatement
                 {block = (Info.dummy, {annotations = []; statements = stms})}) in
  let (env', _) = eval_statement env SContinue stms' in
  (* TODO: figure out how to thread the packet through statement evaluation *)
  eval_transition env' states transition

and eval_transition (env : EvalEnv.t) (states : (string * Parser.state) list)
    (transition : Parser.transition) : EvalEnv.t =
  match snd transition with
  | Direct {next = (_, "accept")} -> env
  | Direct {next = (_, "reject")} -> env
  | Direct {next = (_, next)} ->
    let state = List.Assoc.find_exn states next ~equal:(=) in
    eval_state_machine env states state
  | Select _ -> failwith "select statement unimplemented"

(* -------------------------------------------------------------------------- *)
(* Control Evaluation *)
(* -------------------------------------------------------------------------- *)

and eval_control (env : EvalEnv.t) (locals : Declaration.t list)
    (apply : Block.t) : EvalEnv.t =
  let env' = List.fold_left locals ~init:env ~f:eval_decl in
  let block = (Info.dummy, Statement.BlockStatement {block = apply}) in
  let (env'', sign) = eval_statement env' SContinue block in
  match sign with
  | SContinue
  | SExit -> env''
  | SReturn _ -> failwith "control should not return"

(*----------------------------------------------------------------------------*)
(* Helper functions *)
(*----------------------------------------------------------------------------*)

and decl_of_typ (e : EvalEnv.t) (t : Type.t) : Declaration.t =
  match snd t with
  | TypeName (_,s)                 -> (EvalEnv.find_decl s e)
  | TopLevelType (_,s)             -> (EvalEnv.find_decl_toplevel s e)
  | _ -> (Info.dummy, Error{members = []}) (* TODO: find better solution *)

and init_binding_of_field (env : EvalEnv.t)
    (f : Declaration.field) : string * value =
  let n = snd (snd f).name in
  (n, init_val_of_typ env n (snd f).typ)

and int_of_val (v : value) : int =
  match v with
  | VInteger n
  | VBit (_,n)
  | VInt (_,n) -> Bigint.to_int_exn n
  | _ -> failwith "not an int"

and power_of_two (w : int) : Bigint.t =
  Bigint.shift_left (Bigint.of_int 1) (w-1)

(* -------------------------------------------------------------------------- *)
(* Target and Architecture Dependent Evaluation *)
(* -------------------------------------------------------------------------- *)

let rec eval_main (env : EvalEnv.t) (pack : packet) : packet =
  let (_, obj, vs) =
    match EvalEnv.find_val "main" env with
    | VObjstate ((info, obj), vs) -> (info, obj, vs)
    | _ -> failwith "main not a stateful object" in
  let name =
    match obj with
    | Declaration.PackageType {name=(_,n);_} -> n
    | _ -> failwith "main is no a package" in
  match name with
  | "V1Switch" -> eval_v1switch env vs pack
  | "EmptyPackage" -> pack
  | _ -> failwith "architecture not supported"

and eval_v1switch (env : EvalEnv.t) (vs : (string * value) list)
    (pack : packet) : packet =
  let parser =
    List.Assoc.find_exn vs "p"   ~equal:(=) in
  let verify =
    List.Assoc.find_exn vs "vr"  ~equal:(=) in
  let ingress =
    List.Assoc.find_exn vs "ig"  ~equal:(=) in
  let egress =
    List.Assoc.find_exn vs "eg"  ~equal:(=) in
  let compute =
    List.Assoc.find_exn vs "ck"  ~equal:(=) in
  let deparser =
    List.Assoc.find_exn vs "dep" ~equal:(=) in
  let (_, obj, pvs) =
    match parser with
    | VObjstate ((info, obj), pvs) -> (info, obj, pvs)
    | _ -> failwith "parser is not a stateful object" in
  let params =
    match obj with
    | Parser {params=ps;_} -> ps
    | _ -> failwith "parser is not a parser object" in
  let pckt = VRuntime (Packet pack) in
  let hdr =
    init_val_of_typ env "hdr"      (snd (List.nth_exn params 1)).typ in
  let meta =
    init_val_of_typ env "meta"     (snd (List.nth_exn params 2)).typ in
  let std_meta =
    init_val_of_typ env "std_meta" (snd (List.nth_exn params 3)).typ in
  let env =
    EvalEnv.(env
             |> insert_val "packet"   pckt
             |> insert_val "hdr"      hdr
             |> insert_val "meta"     meta
             |> insert_val "std_meta" std_meta
             |> insert_typ "packet"   (snd (List.nth_exn params 0)).typ
             |> insert_typ "hdr"      (snd (List.nth_exn params 1)).typ
             |> insert_typ "meta"     (snd (List.nth_exn params 2)).typ
             |> insert_typ "std_meta" (snd (List.nth_exn params 3)).typ) in
  (* TODO: implement a more responsible way to generate variable names *)
  let pckt_expr =
    (Info.dummy, Argument.Expression {value = (Info.dummy, Name (Info.dummy, "packet"))}) in
  let hdr_expr =
    (Info.dummy, Argument.Expression {value = (Info.dummy, Name (Info.dummy, "hdr"))}) in
  let meta_expr =
    (Info.dummy, Argument.Expression {value = (Info.dummy, Name (Info.dummy, "meta"))}) in
  let std_meta_expr =
    (Info.dummy, Argument.Expression {value = (Info.dummy, Name (Info.dummy, "std_meta"))}) in
  let env = env
    |> eval_v1parser   parser   [pckt_expr; hdr_expr; meta_expr; std_meta_expr]
    |> eval_v1verify   verify   [hdr_expr; meta_expr]
    |> eval_v1ingress  ingress  [hdr_expr; meta_expr; std_meta_expr]
    |> eval_v1egress   egress   [hdr_expr; meta_expr; std_meta_expr]
    |> eval_v1compute  compute  [hdr_expr; meta_expr]
    |> eval_v1deparser deparser [pckt_expr; hdr_expr] in
  match EvalEnv.find_val "packet" env with
  | VRuntime (Packet p) -> p
  | _ -> failwith "pack not a packet"

and eval_v1parser (parser : value) (args : Argument.t list)
    (env : EvalEnv.t) : EvalEnv.t =
  let (_, decl, vs) =
    match parser with
    | VObjstate((info, decl), vs) -> (info, decl, vs)
    | _ -> failwith "v1 parser is not a stateful object" in
  let (params, locals, states) =
    match decl with
    | Parser {params=ps;locals=ls;states=ss;_} -> (ps,ls,ss)
    | _ -> failwith "v1 parser is not a parser" in
  let (env', penv) = eval_inargs env params args in
  let f a (x,y) = EvalEnv.insert_val x y a in
  let penv' = List.fold_left vs ~init:penv ~f:f in
  let penv'' = eval_parser penv' locals states in
  let final_env = eval_outargs env' penv'' params args in
  final_env

and eval_v1verify (control : value) (args : Argument.t list)
    (env : EvalEnv.t) : EvalEnv.t =
  env (* TODO*)

and eval_v1ingress (control : value) (args : Argument.t list)
    (env : EvalEnv.t) : EvalEnv.t =
  let (_, decl, vs) =
    match control with
    | VObjstate((info, decl), vs) -> (info,  decl, vs)
    | _ -> failwith "v1 ingress is not a stateful object" in
  let (params, locals, apply) =
    match decl with
    | Control{params=ps; locals=ls; apply=b; _} -> (ps, ls, b)
    | _ -> failwith "v1 ingress is not a control" in
  let (env', cenv) = eval_inargs env params args in
  let f a (x,y) = EvalEnv.insert_val x y a in
  let cenv' = List.fold_left vs ~init:cenv ~f:f in
  let cenv'' = eval_control cenv' locals apply in
  let final_env = eval_outargs env' cenv'' params args in
  print_endline "After Ingress";
  EvalEnv.print_env final_env;
  final_env

and eval_v1egress (control : value) (args : Argument.t list)
    (env : EvalEnv.t) : EvalEnv.t =
  env (* TODO *)

and eval_v1compute (control : value) (args : Argument.t list)
    (env : EvalEnv.t) : EvalEnv.t =
  env (* TODO *)

and eval_v1deparser (control : value) (args : Argument.t list)
    (env : EvalEnv.t) : EvalEnv.t =
  env (* TODO *)

(*----------------------------------------------------------------------------*)
(* Program Evaluation *)
(*----------------------------------------------------------------------------*)

let eval_program = function Program l ->
  let env = List.fold_left l ~init:EvalEnv.empty_eval_env ~f:eval_decl in
  EvalEnv.print_env env;
  Format.printf "Done\n";
  let packetin = Bigint.zero in
  let packout = eval_main env packetin in
  ignore packout
