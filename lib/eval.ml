module I = Info
open Core
open Env
open Types
open Value
module Info = I (* JNF: ugly hack *)

(*----------------------------------------------------------------------------*)
(* Helper functions, modules, types, etc *)
(*----------------------------------------------------------------------------*)

let rec type_lookup (e : EvalEnv.t) (t : Type.pre_t) : Declaration.t =
  match t with
  | TypeName (_,s)                 -> (EvalEnv.find_decl s e)
  | TopLevelType (_,s)             -> (EvalEnv.find_decl_toplevel s e)
  | SpecializedType ({base; args}) -> type_lookup e (snd base) (* TODO *)
  | _ -> failwith "lookup unexpected type"

module Eval_int: sig
  val to_int: value -> int
  val power2w: int -> Bigint.t
end = struct
  let to_int v =
    match v with
    | VInteger(v1)
    | VBit(_, v1)
    | VInt(_, v1) -> Bigint.to_int_exn v1
    | _ -> failwith "impossible to get "
  let power2w w = Bigint.shift_left (Bigint.of_int 1) (w-1)
end

(*----------------------------------------------------------------------------*)
(* Declaration Evaluation *)
(*----------------------------------------------------------------------------*)

let rec eval_decl (env : EvalEnv.t) (d : Declaration.t) : EvalEnv.t =
  match snd d with
  | Constant {
      annotations = _;
      typ = _;
      value = v;
      name = (_,n);
    } -> eval_const_decl env v n
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
      name = _;
      type_params = _;
      params = _;
    } -> eval_extern_fun_decl ()
  | Variable {
      annotations = _;
      typ = _;
      name = (_,n);
      init = v;
    } -> eval_decl_var env n v
  | ValueSet {
      annotations = _;
      typ = _;
      size = _;
      name = _;
    } -> eval_set_decl ()
  | Action {
      annotations = _;
      name = _;
      params = _;
      body = _;
    } -> eval_action_decl ()
  | Table {
      annotations = _;
      name = _;
      properties = _;
    } -> eval_table_decl ()
  | Header {
      annotations = _;
      name = _;
      fields = _;
    } -> eval_header_decl ()
  | HeaderUnion {
      annotations = _;
      name = _;
      fields = _;
    } -> eval_union_decl ()
  | Struct {
      annotations = _;
      name = _;
      fields = _;
    } -> eval_struct_decl ()
  | Error {
      members = _;
    } -> eval_error_decl ()
  | MatchKind {
      members = _;
    } -> eval_matchkind_decl ()
  | Enum {
      annotations = _;
      name = _;
      members = _;
    } -> eval_enum_decl ()
  | SerializableEnum {
      annotations = _;
      typ = _;
      name = _;
      members = _;
    } -> eval_senum_decl ()
  | ExternObject {
      annotations = _;
      name = _;
      type_params = _;
      methods = _;
    } -> eval_extern_obj ()
  | TypeDef {
      annotations = _;
      name = _;
      typ_or_decl = _;
    } -> eval_type_def ()
  | NewType {
      annotations = _;
      name = _;
      typ_or_decl = _;
    } -> eval_type_decl ()
  | ControlType {
      annotations = _;
      name = _;
      type_params = _;
      params = _;
    } -> eval_ctrltyp_decl ()
  | ParserType {
      annotations = _;
      name = _;
      type_params = _;
      params = _;
    } -> eval_prsrtyp_decl ()
  | PackageType {
      annotations = _;
      name = (_,name);
      type_params = _;
      params = _;
    } -> eval_pkgtyp_decl env name d

and eval_const_decl (env : EvalEnv.t) (e : Expression.t)
    (name : string) : EvalEnv.t =
  let (env', v) = eval_expression' env e in
  EvalEnv.insert_value env' name v

and eval_instantiation (env:EvalEnv.t) (typ : Type.t) (args : Argument.t list)
    (name : string) : EvalEnv.t =
  let (env', obj) = eval_nameless env typ args in
  EvalEnv.insert_value env' name obj

and eval_parser_decl (env : EvalEnv.t) (name : string)
    (decl : Declaration.t) : EvalEnv.t =
  EvalEnv.insert_decls env name decl

and eval_control_decl (env : EvalEnv.t) (name : string)
    (decl : Declaration.t) : EvalEnv.t =
  EvalEnv.insert_decls env name decl

and eval_fun_decl (env : EvalEnv.t) (name : string) (params : Parameter.t list)
    (body : Block.t) : EvalEnv.t =
  EvalEnv.insert_value env name (VFun(params,body))

and eval_extern_fun_decl () = failwith "unimplemented"

and eval_decl_var (env : EvalEnv.t) (name : string)
    (init : Expression.t option) : EvalEnv.t =
  match init with
  | None -> env
  | Some e ->
    let (env', v) = eval_expression' env e in
    EvalEnv.insert_value env' name v

and eval_set_decl () = failwith "unimplemented"

and eval_action_decl () = failwith "unimplemented"

and eval_table_decl () = failwith "unimplemented"

and eval_header_decl () = failwith "unimplemented"

and eval_union_decl () = failwith "unimplemented"

and eval_struct_decl () = failwith "unimplemented"

and eval_error_decl () = failwith "unimplemented"

and eval_matchkind_decl () = failwith "unimplemented"

and eval_enum_decl () = failwith "unimplemented"

and eval_senum_decl () = failwith "unimplemented"

and eval_extern_obj () = failwith "unimplemented"

and eval_type_def () = failwith "unimplemented"

and eval_type_decl () = failwith "unimplemented"

and eval_ctrltyp_decl () = failwith "unimplemented"

and eval_prsrtyp_decl () = failwith "unimplemented"

and eval_pkgtyp_decl (env : EvalEnv.t) (name : string)
    (decl : Declaration.t) : EvalEnv.t =
  EvalEnv.insert_decls env name decl

(*----------------------------------------------------------------------------*)
(* Statement Evaluation *)
(*----------------------------------------------------------------------------*)

(* TODO: flesh out implementation for statements*)
and eval_statement (env :EvalEnv.t) (sign : signal)
    (stm : Statement.t) : (EvalEnv.t * signal) =
  match snd stm with
  | MethodCall{func;type_args;args} -> eval_method_call env sign func args
  | Assignment{lhs;rhs}             -> eval_assign env sign lhs rhs
  | DirectApplication{typ;args}     -> failwith "unimplemented"
  | Conditional{cond;tru;fls}       -> eval_conditional env sign cond tru fls
  | BlockStatement{block}           -> eval_block env sign block
  | Exit                            -> failwith "unimplemented"
  | EmptyStatement                  -> (env, sign)
  | Return{expr}                    -> eval_return env sign expr
  | Switch{expr;cases}              -> failwith "unimplemented"
  | DeclarationStatement{decl}      -> eval_decl_stm env sign decl

and eval_method_call (env : EvalEnv.t) (sign : signal) (func : Expression.t)
    (args : Argument.t list) : EvalEnv.t * signal =
  match sign with
  | SReturn v -> (env, SReturn v)
  | SExit -> failwith "unimplemented"
  | SContinue ->
    let (env', _) = eval_funcall env func args in
    (env', SContinue)

and eval_assign (env : EvalEnv.t) (s : signal) (lhs : Expression.t)
    (rhs : Expression.t) : EvalEnv.t * signal =
  match s with
  | SContinue ->
    let (env', v) = eval_expression' env rhs in
    (eval_assign' env lhs v, SContinue)
  | SReturn v -> (env, SReturn v)
  | SExit -> failwith "unimplemented"

and eval_assign' (env : EvalEnv.t) (lhs : Expression.t) (rhs : value) : EvalEnv.t =
  match snd lhs with
  | Name (_,n) -> EvalEnv.insert_value env n rhs
  | BitStringAccess({bits; lo; hi}) -> failwith "unimplemented"
  | ArrayAccess({array = ar; index}) ->
    let (env', index') = eval_expression' env index in
    let i = Eval_int.to_int index' in
    let (env'', ar') = eval_expression' env' ar in
    begin match snd ar, ar' with
      | Name (_,n), VList l ->
        let rec helper acc = (function
            | h::d -> if acc = i then rhs::d else h::(helper (acc + 1) d)
            | [] -> []) in
        EvalEnv.insert_value env'' n (VList(helper 0 l))
      | _ -> failwith "array expected to evaluate to VList?" end
  | ExpressionMember({ expr; name}) -> failwith "unimplemented"
  | _ -> failwith "can't assign to the LHS"

and eval_application () = failwith "unimplemented"

and eval_conditional (env : EvalEnv.t) (sign : signal) (cond : Expression.t)
    (tru : Statement.t) (fls : Statement.t option) : EvalEnv.t * signal =
  match sign with
  | SExit -> failwith "unimplmented"
  | SReturn v -> (env, SReturn v)
  | SContinue ->
    let (env', v) = eval_expression' env cond in
    begin match v with
      | VBool true -> eval_statement env' SContinue tru
      | VBool false ->
        begin match fls with
          | None -> (env, SContinue)
          | Some fls' -> eval_statement env' SContinue fls'  end
      | VNull
      | VInteger _
      | VBit _
      | VInt _
      | VList _
      | VSet _
      | VString _
      | VError _
      | VFun _
      | VHeader_or_struct _
      | VObjstate _ -> failwith "conditional guard must be a bool" end

and eval_block (env : EvalEnv.t) (sign :signal) (block : Block.t) : (EvalEnv.t * signal) =
  let block = snd block in
  let rec f env s ss =
    match ss with
    | [] -> (env, s)
    | h :: d ->
      begin match s with
        | SContinue ->
          let (env', sign')= eval_statement env SContinue h in
          f env' sign' d
        | SReturn v -> (env, SReturn v)
        | SExit -> failwith "unimplemented" end in
  f env sign block.statements

and eval_exit () = failwith "unimplemented"

and eval_return (env : EvalEnv.t) (sign : signal)
    (expr : Expression.t option) : (EvalEnv.t * signal) =
  match sign with
  | SReturn v -> (env, SReturn v)
  | SExit -> failwith "unimplemented"
  | SContinue ->
    match expr with
    | None -> (env, SReturn VNull)
    | Some expr' ->
      let (env', v) = eval_expression' env expr' in
      (env', SReturn v)

and eval_switch () = failwith "unimplemented"

and eval_decl_stm (env : EvalEnv.t) (sign : signal)
    (decl : Declaration.t) : EvalEnv.t * signal =
  match sign with
  | SReturn v -> (env, SReturn v)
  | SExit -> failwith "unimplemented"
  | SContinue -> (eval_decl env decl, SContinue)

(*----------------------------------------------------------------------------*)
(* Expression Evaluation *)
(*----------------------------------------------------------------------------*)

and eval_expression' (env : EvalEnv.t) (exp : Expression.t) : EvalEnv.t * value =
  match snd exp with
  | True                              -> (env, VBool true)
  | False                             -> (env, VBool false)
  | Int(_,n)                          -> (env, eval_p4int n)
  | String (_,value)                  -> (env, VString value)
  | Name (_,name)                     -> (env, EvalEnv.find_value name env)
  | TopLevel (_,name)                 -> (env, EvalEnv.find_value_toplevel name env)
  | ArrayAccess({array=a; index=i})   -> eval_array env a i
  | BitStringAccess({bits;lo;hi})     -> eval_bit_string_access env bits lo hi
  | List{values}                      -> eval_list env values
  | UnaryOp{op;arg}                   -> eval_unary env op arg
  | BinaryOp{op; args=(l,r)}          -> eval_binop env op l r
  | Cast{typ;expr}                    -> eval_cast env typ expr
  | TypeMember{typ;name}              -> failwith "unimplemented"
  | ErrorMember t                     -> (env, VError t)
  | ExpressionMember{expr;name}       -> failwith "unimplemented"
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
    (i : Expression.t) : EvalEnv.t * value = (* TODO: probably wont represent header stacks as lists *)
  let (env', a') = eval_expression' env a in
  let (env'', i') = eval_expression' env' i in
  match a' with
  | VList l -> (env'', List.nth_exn l (Eval_int.to_int i'))
  | VNull
  | VBool _
  | VInteger _
  | VBit _
  | VInt _
  | VSet _
  | VString _
  | VError _
  | VFun _
  | VHeader_or_struct _
  | VObjstate _ -> failwith "impossible"
(* TODO: graceful failure *)

and eval_bit_string_access (env : EvalEnv.t) (s : Expression.t)
    (m : Expression.t) (l : Expression.t) : EvalEnv.t * value =
  let (env', m) = eval_expression' env m in
  let (env'', l) = eval_expression' env' l in
  let (env''', s) = eval_expression' env'' s in
  match m, l, s with
  | VBit(_, vm), VBit(_, vl), VBit(w1, v1) ->
    let m' = Eval_int.to_int m in
    let l' = Eval_int.to_int l in
    let w = m' - l' + 1 in
    let v = (Bigint.shift_left v1 (l'+1) |>
             Bigint.shift_right) (w1-m'+l') in
    (env''', VBit(w, v)) (*TODO: should be shift right trunc*)
  | _ -> failwith "bit string access impossible"
(* TODO: graceful failure *)

and eval_list (env : EvalEnv.t) (values : Expression.t list) : EvalEnv.t * value =
  let (env_final,l) = List.fold_map values ~f:eval_expression' ~init:env in
  (env_final, VList l)

and eval_unary (env : EvalEnv.t) (op : Op.uni) (e : Expression.t) : EvalEnv.t * value =
  let (env', e') = eval_expression' env e in
  match snd op, e' with
  | UMinus, VBit(w,v) -> Bigint.(env', VBit(w, (Eval_int.power2w w) - v))
  | UMinus, VInt(w,v) -> (env', VBit(w, Bigint.neg v))
  | BitNot, VBit(w,v) -> (env', VBit(w, Bigint.neg v))
  | BitNot, VInt(w,v) -> (env', VInt(w, Bigint.neg v))
  | Not, VBool b   -> (env', VBool (not b))
  | _ -> failwith "unary options don't apply"
(* TODO: fail gracefully *)

and eval_binop (env : EvalEnv.t) (op : Op.bin) (l : Expression.t)
    (r : Expression.t) : EvalEnv.t * value =
  let (env',l) = eval_expression' env l in
  let (env'',r) = eval_expression' env' r in
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
    VBit (Eval_int.to_int w, Bigint.of_int v) in
  let changesize w v l =
    let new_w = l |> Eval_int.to_int in
    let value = if new_w >= w then v
      else (Bigint.shift_left v (w - new_w) |>
            Bigint.shift_right) (w - new_w) in
    (new_w, value) in
  let (env', expr') = eval_expression' env expr in
  match expr', snd typ with
  | VBit(1, v), Type.Bool ->
    if Bigint.(=) v Bigint.zero
    then (env', VBool(false))
    else if Bigint.(=) v Bigint.one
    then (env', VBool(true))
    else failwith "can't cast this bitstring to bool"
  | VBool(b), Type.BitType(e) ->
    let (env'', e') = eval_expression' env' e in
    if b then (env'', build_bit e' 1)
    else (env'', build_bit e' 0)
  | VInt(w, v), Type.BitType(w') ->
    let turn_pos w v =
      if Bigint.(<) v Bigint.zero
      then Bigint.(+) v (Eval_int.power2w (w+1))
      else v in
    (env', VBit(w, turn_pos w v))
  | VBit(w, v), Type.IntType(w') ->
    let neg_bit w v =
      if Bigint.(>=) v (Eval_int.power2w (w-1))
      then Bigint.(-) v (Eval_int.power2w w)
      else v in
    (env', VInt(w, neg_bit w v))
  | VBit(w, v), Type.BitType(l) ->
    let (env'', l') = eval_expression' env' l in
    let width, value = changesize w v l' in
    (env'', VBit(width, value))
  (* TODO: validate: Should be shift_right_truncate*)
  | VInt(w, v), Type.IntType(l) ->
    let (env'', l') = eval_expression' env l in
    let (width, value) = changesize w v l' in
    (env'', VInt(width, value))
  | _ -> failwith "type cast case should be handled by compiler" (* TODO *)
(* TODO: graceful failure *)

and eval_typ_mem () = (* TODO: implement member lookup *)
  failwith "unimplemented"

and eval_expr_mem () = (* TODO: implement member lookup *)
  failwith "unimplemented"

and eval_ternary (env : EvalEnv.t) (c : Expression.t) (te : Expression.t)
    (fe : Expression.t) : EvalEnv.t * value =
  let (env', c') = eval_expression' env c in
  match c' with
  | VBool(true)  -> (eval_expression' env te)
  | VBool(false) -> (eval_expression' env fe)
  | _ -> failwith "impossible to typecheck the ternary expression"
(* TODO: fail gracefully *)

(* TODO: key-arguments and optional arguments not implemented;
         should work for return values and regular arguments *)
(* TODO: rework*)
and eval_funcall (env : EvalEnv.t) (func : Expression.t)
    (args : Argument.t list) : EvalEnv.t * value =
  (* print_endline "function call"; *)
  (* print_endline "env is:"; EvalEnv.print_env env; *)
  let (env', cl) = eval_expression' env func in
  (* print_endline "env' is: ";  EvalEnv.print_env env'; *)
  match cl with
  | VNull
  | VBool _
  | VInteger _
  | VBit _
  | VInt _
  | VList _
  | VSet _
  | VString _
  | VError _
  | VHeader_or_struct _
  | VObjstate _ -> failwith "not a function"
  | VFun (params, body) ->
    let f env e =
      match snd e with
      | Argument.Expression {value=expr} -> eval_expression' env expr
      | Argument.KeyValue _
      | Argument.Missing -> failwith "unimplemented" (* TODO*) in
    let (env'',arg_vals) = List.fold_map args ~f:f ~init:env' in
    (* print_endline "env'' is: "; EvalEnv.print_env env''; *)
    let fenv = EvalEnv.push_scope (EvalEnv.get_toplevel env'') in
    (* print_endline "clenv is: "; EvalEnv.print_env clenv; *)
    (* print_endline "clenv' is: "; EvalEnv.print_env clenv'; *)
    let g e (p : Parameter.t) v =
      match (snd p).direction with
      | None -> failwith "unimplemented"
      | Some x -> begin match snd x with
        | InOut
        | In -> EvalEnv.insert_value e (snd (snd p).variable) v
        | Out -> e end in
    let fenv' = List.fold2_exn params arg_vals ~init:fenv ~f:g in
    let (fenv'', sign) = eval_block fenv' SContinue body in
    let h e (p:Parameter.t) a =
      match (snd p).direction with
      | None -> failwith "unimplmented"
      | Some x -> begin match snd x with
        | InOut
        | Out ->
          let v = EvalEnv.find_value (snd (snd p).variable) fenv'' in
          let lhs = begin match snd a with
            | Argument.Expression {value=expr} -> expr
            | Argument.KeyValue _
            | Argument.Missing -> failwith "unimplemented" end in
          (* print_endline "doing assign"; *)
          eval_assign' e lhs v
        | In -> e end in
    let final_env = List.fold2_exn params args ~init:env'' ~f:h in
    (* print_endline "finish function call"; *)
    begin match sign with
      | SReturn v -> (final_env, v)
      | SContinue -> (final_env, VNull)
      | SExit -> failwith "function did no return" end
(* TODO: fail gracefully *)

and eval_nameless (env : EvalEnv.t) (typ : Type.t)
    (args : Argument.t list) : EvalEnv.t * value  =
  let positional_binding env ((param : Parameter.t), arg) =
    let param = snd param in
    match (snd arg) with
    | Argument.Expression {value} ->
      let (env', v) = eval_expression' env value in
      (env',(param.variable, v))
    | _ -> failwith "unimplemented" in
  let (info ,decl) = type_lookup env (snd typ) in
  match decl with
  | Control typ_decl ->
    let l = List.zip_exn typ_decl.constructor_params args in
    let (env', state) = List.fold_map l ~f:positional_binding ~init:env in
    (env', VObjstate {decl = (info, Control typ_decl); state = state})
  | Parser typ_decl ->
    let l = List.zip_exn typ_decl.constructor_params args in
    let (env', state) = List.fold_map l ~f:positional_binding ~init:env in
    (env', VObjstate{decl = (info, Parser typ_decl); state = state})
  | PackageType pack_decl ->
    let l = List.zip_exn pack_decl.params args in
    let (env', state) = List.fold_map l ~f:positional_binding ~init:env in
    (env', VObjstate{decl = (info, PackageType pack_decl); state = state})
  | _ -> failwith "unimplemented"
(* TODO: instantiation for other types *)

and eval_mask_expr env e m =
  let (env', v1)  = eval_expression' env  e in
  let (env'', v2) = eval_expression' env' m in
  (env'', VSet(SMask(v1,v2)))

and eval_range_expr env lo hi =
  let (env', v1)  = eval_expression' env  lo in
  let (env'', v2) = eval_expression' env' hi in
  (env'', VSet(SRange(v1,v2)))

(* TODO: these functions need to fail more gracefully *)
(* TODO: these function need to hanle raw ints *)
and eval_sat op l r =
  let compute m n w =
    let a = Bigint.abs (op m n) in
    if  Bigint.(<) a m || Bigint.(<) a n then Eval_int.power2w w else a in
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
(* Functions in the signature *)
(*----------------------------------------------------------------------------*)

let eval_expression (env : EvalEnv.t) (expr : Expression.t) : value =
  snd (eval_expression' env expr)

let eval = function Program l ->
  let env = List.fold_left l ~init:EvalEnv.empty_eval_env ~f:eval_decl in
  EvalEnv.print_env env;
  Format.printf "Done\n"
