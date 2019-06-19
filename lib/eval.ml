module I = Info
open Core
open Env
open Types
open Value
module Info = I (* JNF: ugly hack *)

(*----------------------------------------------------------------------------*)
(* Helper functions, modules, types, etc *)
(*----------------------------------------------------------------------------*)

type value = EvalEnv.t pre_value
(* type set = EvalEnv.t pre_set *)
(* type obj = EvalEnv.t pre_obj *)
type signal = EvalEnv.t pre_signal

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
    | VInteger(v1) -> Bigint.to_int_exn v1
    | VBit({ width = w1; value = v1 })
  | VInt({ width = w1; value = v1 }) -> Bigint.to_int_exn v1
    | _ -> failwith "impossible to get "
  let power2w w = Bigint.shift_left (Bigint.of_int 1) (w-1)
end

(*----------------------------------------------------------------------------*)
(* Declaration Evaluation *)
(*----------------------------------------------------------------------------*)

let rec eval_decl (env : EvalEnv.t) (d : Declaration.t) : EvalEnv.t =
  match snd d with
  | Constant({annotations; typ; name = (_,name); value}) ->
    let (v, env') = eval_expression' env value in
    EvalEnv.insert_value env' name v
  | Instantiation({annotations; typ; args; name}) ->
    eval_instantiation env typ args name
  | Parser({ name = (_,name); _ })
  | Control({ name = (_,name); _ }) ->
    EvalEnv.insert_decls env name d
  | Function { name=(_,name); params=params;body=body; _} ->
    EvalEnv.insert_value env name (VClosure(params,body,env))
  | ExternFunction _ -> failwith "unimplemented" (* TODO *)
  | Variable({annotations; typ; name; init}) ->
    eval_decl_var env annotations typ name init
  | ValueSet _ (* TODO *)
  | Action _ (* TODO *)
  | Table _ (* TODO *)
  | Header _ (* TODO *)
  | HeaderUnion _ (* TODO *)
  | Struct _ (* TODO *)
  | Error _ (* TODO *)
  | MatchKind  _ (* TODO *)
  | Enum _ (* TODO *)
  | SerializableEnum _ (* TODO *)
  | ExternObject _ (* TODO *)
  | TypeDef _ (* TODO *)
  | NewType _ (* TODO *)
  | ControlType _ (* TODO *)
  | ParserType _ -> failwith "unimplemented" (* TODO *)
  | PackageType({ name = (_,name); _ }) ->
    EvalEnv.insert_decls env name d

and eval_decl_var env annotations typ name init =
  match init with
  | None -> env
  | Some e ->
    let (v,env') = eval_expression' env e in
    EvalEnv.insert_value env' (snd name) v

and eval_instantiation (env:EvalEnv.t) typ args name =
  let (obj,env') = eval_nameless env typ args in
  EvalEnv.insert_value env' (snd name) obj

(*----------------------------------------------------------------------------*)
(* Statement Evaluation *)
(*----------------------------------------------------------------------------*)

(* TODO: flesh out implementation for statements*)
and eval_statement (env :EvalEnv.t) (stm : Statement.t) sign : (EvalEnv.t * signal) =
  match snd stm with
  | MethodCall{func;type_args;args} -> failwith "unimplemented"
  | Assignment{lhs;rhs}  (*TODO*)   -> eval_assign env sign lhs rhs
  | DirectApplication{typ;args}     -> failwith "unimplemented"
  | Conditional{cond;tru;fls}       -> eval_conditional env sign cond tru fls
  | BlockStatement{block}           -> eval_block env sign block
  | Exit                            -> failwith "unimplemented"
  | EmptyStatement                  -> (env, sign)
  | Return{expr}                    -> failwith "unimplemented"
  | Switch{expr;cases}              -> failwith "unimplemented"
  | DeclarationStatement{decl}      -> failwith "unimplemented "

and eval_method_call = failwith "unimplemented"

and eval_assign env s lhs rhs : EvalEnv.t * signal =
  match s with
  | SContinue ->
    let (v, env') = eval_expression' env rhs in
    (eval_assign' env lhs v, SContinue)
  | SReturn v -> (env, SReturn v)
  | SExit -> failwith "unimplemented"

and eval_assign' env lhs rhs: EvalEnv.t =
  match snd lhs with
  | Name (_,n) -> EvalEnv.insert_value env n rhs
  | BitStringAccess({bits; lo; hi}) -> failwith "unimplemented"
  | ArrayAccess({array = ar; index}) ->
  let (index',env') = eval_expression' env index in
  let i = Eval_int.to_int index' in
  let (ar', env'') = eval_expression' env' ar in
  begin match snd ar, ar' with
  | Name (_,n), VList l ->
    let rec helper acc = (function
        | h::d -> if acc = i then rhs::d else h::(helper (acc + 1) d)
        | [] -> [])
    in
    EvalEnv.insert_value env'' n (VList(helper 0 l))
  | _ -> failwith "array expected to evaluate to VList?"
  end
  | ExpressionMember({ expr; name}) -> failwith "unimplemented"
  | _ -> failwith "can't assign to the LHS"

and eval_application = failwith "unimplemented"

and eval_conditional env sign cond tru fls =
  match sign with
  | SExit -> failwith "unimplmented"
  | SReturn v -> (env, SReturn v)
  | SContinue ->
    let (v,env') = eval_expression' env cond in
    begin match v with
      | VBool true -> eval_statement env' tru SContinue
      | VBool false ->
        begin match fls with
          | None -> (env, SContinue)
          | Some fls' -> eval_statement env' fls' SContinue end
      | VNull
      | VInteger _
      | VBit _
      | VInt _
      | VList _
      | VSet _
      | VString _
      | VError _
      | VClosure _
      | VHeader_or_struct _
      | VObjstate _ -> failwith "conditional guard must be a bool" end

and eval_block env sign block: (EvalEnv.t * signal) =
  let block = snd block in
  let rec f env s ss =
    match ss with
    | [] -> (env, s)
    | h :: d ->
      begin match s with
        | SContinue ->
          let (env', sign')= eval_statement env h SContinue in
          f env' sign' d
        | SReturn v -> (env, SReturn v)
        | SExit -> failwith "unimplemented" end in
  f env sign block.statements

and eval_exit = failwith "unimplemented"

and eval_return = failwith "unimplemented"

and eval_switch = failwith "unimplemented"

and eval_decl_stm = failwith "unimplemented"

(*----------------------------------------------------------------------------*)
(* Expression Evaluation *)
(*----------------------------------------------------------------------------*)

and eval_expression' (env: EvalEnv.t) (exp: Expression.t) : value * EvalEnv.t =
  match snd exp with
  | True                              -> (VBool true, env)
  | False                             -> (VBool false, env)
  | Int(_,n)                          -> eval_p4int env n
  | String (_,value)                  -> (VString value, env)
  | Name (_,name)                     -> (EvalEnv.find_value name env, env)
  | TopLevel (_,name)                 -> (EvalEnv.find_value_toplevel name env, env)
  | ArrayAccess({array=a; index=i})   -> eval_array env a i
  | BitStringAccess({bits;lo;hi})     -> eval_bit_string_access env bits lo hi
  | List{values}                      -> eval_list env values
  | UnaryOp{op;arg}                   -> eval_unary op env arg
  | BinaryOp{op; args=(l,r)}          -> eval_binop op env l r
  | Cast{typ;expr}                    -> eval_cast env typ expr
  | TypeMember{typ;name}              -> eval_typ_mem env typ name
  | ErrorMember t                     -> (VError (t), env)
  | ExpressionMember{expr;name}       -> eval_expr_mem env expr name
  | Ternary{cond;tru;fls}             -> eval_ternary env cond tru fls
  | FunctionCall{func;type_args;args} -> eval_funcall env func args
  | NamelessInstantiation{typ;args}   -> eval_nameless env typ args
  | Mask{expr;mask}                   -> eval_mask_expr env expr mask
  | Range{lo;hi}                      -> eval_range_expr env lo hi

and eval_p4int env n =
  match n.width_signed with
  | None          -> (VInteger n.value, env)
  | Some(w,true)  -> (VInt {width=w; value=n.value}, env)
  | Some(w,false) -> (VBit {width=w; value=n.value}, env)

and eval_array env a i =
  let (a', env') = eval_expression' env a in
  let (i', env'') = eval_expression' env' i in
  match a' with
  | VList l -> (Base.List.nth_exn l (Eval_int.to_int i'), env'')
  | VNull
  | VBool _
  | VInteger _
  | VBit _
  | VInt _
  | VSet _
  | VString _
  | VError _
  | VClosure _
  | VHeader_or_struct _
  | VObjstate _ -> failwith "impossible"
(* TODO: graceful failure *)

and eval_bit_string_access env s m l =
  let (m,env') = eval_expression' env m in
  let (l,env'') = eval_expression' env' l in
  let (s,env''') = eval_expression' env'' s in
  match m, l, s with
  | VBit({ width = wm; value = vm }),
    VBit({ width = wl; value = vl }),
    VBit({ width = w1; value = v1 }) ->
    let m' = Eval_int.to_int m in
    let l' = Eval_int.to_int l in
    let w = m' - l' + 1 in
    let v = (Bigint.shift_left v1 (l'+1) |>
             Bigint.shift_right) (w1-m'+l') in
    (VBit({width = w; value = v;}), env''') (*TODO: should be shift right trunc*)
  | _ -> failwith "bit string access impossible"
(* TODO: graceful failure *)

and eval_list env values =
  let f (l,e) expr =
    let (v,e') = eval_expression' e expr in
    (v::l,e') in
  let (l,env_final) = List.fold_left values ~f:f ~init:([],env) in
  (VList l, env_final)

and eval_unary op env e =
  let (e',env') = eval_expression' env e in
  match snd op, e'  with
  | UMinus, VBit n ->
    Bigint.(VBit{n with value = (Eval_int.power2w n.width) - n.value}, env')
  | UMinus, VInt n -> (VBit{width = n.width; value = Bigint.neg n.value}, env')
  | BitNot, VBit n -> (VBit{n with value = Bigint.neg n.value}, env')
  | BitNot, VInt n -> (VInt{n with value = Bigint.neg n.value}, env')
  | Not, VBool b   -> (VBool (not b), env')
  | _ -> failwith "unary options don't apply"
(* TODO: fail gracefully *)

and eval_binop op env l r =
  let (l,env') = eval_expression' env l in
  let (r,env'') = eval_expression' env' r in
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
    | Eq       -> eval_eq (=)
    | NotEq    -> eval_eq (<>)
    | BitAnd   -> eval_two Bigint.bit_and
    | BitXor   -> eval_two Bigint.bit_xor
    | BitOr    -> eval_two Bigint.bit_or
    | PlusPlus -> eval_concat
    | And      -> eval_and_or (&&)
    | Or       -> eval_and_or (||) end in
  (f l r, env'')

and eval_cast env typ expr =
  let build_bit w v =
    VBit {width = Eval_int.to_int w;
          value = Bigint.of_int v} in
  let changesize w v l =
    let new_w = l |> Eval_int.to_int in
    let value = if new_w >= w then v
      else (Bigint.shift_left v (w - new_w) |>
            Bigint.shift_right) (w - new_w) in
    (new_w, value) in
  let (expr',env') = eval_expression' env expr in
  match expr', snd typ with
  | VBit({width = 1; value = v}), Type.Bool ->
    if Bigint.(=) v Bigint.zero
    then (VBool(false), env')
    else if Bigint.(=) v Bigint.one
    then (VBool(true), env')
    else failwith "can't cast this bitstring to bool"
  | VBool(b), Type.BitType(e) ->
    let (e',env'') = eval_expression' env' e in
    if b then (build_bit e' 1, env'')
    else (build_bit e' 0, env'')
  | VInt({width = w; value = v}), Type.BitType(w') ->
    let turn_pos w v =
      if Bigint.(<) v Bigint.zero
      then Bigint.(+) v (Eval_int.power2w (w+1))
      else v in
    (VBit({width = w; value = turn_pos w v}), env')
  | VBit({width = w; value = v}), Type.IntType(w') ->
    let neg_bit w v =
      if Bigint.(>=) v (Eval_int.power2w (w-1))
      then Bigint.(-) v (Eval_int.power2w w)
      else v in
    (VInt({width = w; value = neg_bit w v}), env')
  | VBit({width = w; value = v}), Type.BitType(l) ->
    let (l',env'') = eval_expression' env' l in
    let width, value = changesize w v l' in
    (VBit({width; value}), env'')
  (* TODO: validate: Should be shift_right_truncate*)
  | VInt({width = w; value = v}), Type.IntType(l) ->
    let (l',env'') = eval_expression' env l in
    let width, value = changesize w v l' in
    (VInt({width; value}), env'')
  | _ -> failwith "type cast case should be handled by compiler"
(* TODO: graceful failure *)

and eval_typ_mem env typ name = (* TODO: implement member lookup *)
  failwith "unimplemented"

and eval_expr_mem env expr name = (* TODO: implement member lookup *)
  failwith "unimplemented"

and eval_ternary env c te fe =
  let (c', env') = eval_expression' env c in
  match c' with
  | VBool(true)  -> (eval_expression' env te)
  | VBool(false) -> (eval_expression' env fe)
  | _ -> failwith "impossible to typecheck the ternary expression"
(* TODO: fail gracefully *)

(* TODO: key-arguments and optional arguments not implemented;
         should work for return values and regular arguments *)
and eval_funcall env func args =
  let (cl, env') = eval_expression' env func in
  match cl with
  | VClosure (params, body, clenv) ->
    let f env e = begin
      match snd e with
      | Argument.Expression {value=expr} ->
        let (v,e) = eval_expression' env expr in (e,v)
      | Argument.KeyValue _
      | Argument.Missing -> failwith "unimplemented" (* TODO*) end in
    let (env'',arg_vals) = List.fold_map args ~f:f ~init:env' in
    let clenv' = EvalEnv.push_scope clenv in
    let g e (p : Parameter.t) v =
      match (snd p).direction with
      | None -> failwith "unimplemented"
      | Some x -> begin match snd x with
        | InOut
        | In -> EvalEnv.insert_value e (snd (snd p).variable) v
        | Out -> e end in
    let clenv'' = List.fold2_exn params arg_vals ~init:clenv' ~f:g in
    let (env''', sign) = eval_block clenv'' SContinue body in
    let h e (p:Parameter.t) a =
      match (snd p).direction with
      | None -> failwith "unimplmented"
      | Some x -> begin match snd x with
        | InOut
        | Out ->
          let v = EvalEnv.find_value (snd (snd p).variable) clenv'' in
          let lhs = begin match snd a with
            | Argument.Expression {value=expr} -> expr
            | Argument.KeyValue _
            | Argument.Missing -> failwith "unimplemented" end in
          eval_assign' e lhs v
        | In -> e end in
    let final_env = List.fold2_exn params args ~init:env''' ~f:h in
    begin match sign with
      | SReturn v -> (v, final_env)
      | SContinue
      | SExit -> failwith "function did no return" end
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
(* TODO: fail gracefully *)

and eval_nameless env typ args =
  let positional_binding env ((param : Parameter.t), arg) =
    let param = snd param in
    match (snd arg) with
    | Argument.Expression {value} ->
      print_endline (Info.to_string (fst value));
      let (v, env') = eval_expression' env value in
      (env',(param.variable, v))
    | _ -> failwith "unimplemented" in
  let (info ,decl) = type_lookup env (snd typ) in
  match decl with
  | Control typ_decl ->
    let l = List.zip_exn typ_decl.constructor_params args in
    let (env', state) = List.fold_map l ~f:positional_binding ~init:env in
    (VObjstate {decl = (info, Control typ_decl); state = state}, env')
  | Parser typ_decl ->
    let l = List.zip_exn typ_decl.constructor_params args in
    let (env', state) = List.fold_map l ~f:positional_binding ~init:env in
    (VObjstate{decl = (info, Parser typ_decl); state = state}, env')
  | PackageType pack_decl ->
    let l = List.zip_exn pack_decl.params args in
    let (env', state) = List.fold_map l ~f:positional_binding ~init:env in
    (VObjstate{decl = (info, PackageType pack_decl); state = state}, env')
  | _ -> failwith "unimplemented"
(* TODO: instantiation for other types *)

and eval_mask_expr env e m =
  let (v1, env')  = eval_expression' env  e in
  let (v2, env'') = eval_expression' env' m in
  (VSet(SMask(v1,v2)), env'')

and eval_range_expr env lo hi =
  let (v1, env')  = eval_expression' env  lo in
  let (v2, env'') = eval_expression' env' hi in
  (VSet(SRange(v1,v2)), env'')

(* TODO: these functions need to fail more gracefully *)
and eval_sat op l r =
  let compute m n w =
    let a = Bigint.abs (op m n) in
    if  Bigint.(<) a m || Bigint.(<) a n then Eval_int.power2w w else a in
  match l,r with
  | VBit n1, VBit n2 -> VBit{n1 with value = compute n1.value n2.value n1.width}
  | VInt n1, VInt n2 -> VInt{n1 with value = compute n1.value n2.value (n1.width-1)}
  | _ -> failwith "binary logical operation only works on bitstrings"

and eval_shift op l r =
  match l,r with
  | VBit n1, VBit{value=v2;_}
  | VBit n1, VInt{value=v2;_} ->
    if n1.value >= Bigint.zero
    then VBit{n1 with value = op n1.value (Bigint.to_int_exn v2)}
    else failwith "can't shift with a negative amount"
  | _ -> failwith "shift doesn't works on this type"

and eval_eq op l r =
  match l,r with
  | VBit{value=v1;_}, VBit{value=v2;_}
  | VInt{value=v1;_}, VInt{value=v2;_}
  | VInteger v1, VInteger v2 -> VBool (op v1 v2)
  | _ -> failwith "equality for varbit binary comparison only works on bitstrings"

and eval_compare op l r =
  match l,r with
  | VBit{value=v1;_}, VBit{value=v2;_}
  | VInt{value=v1;_}, VInt{value=v2;_} -> VBool(op v1 v2)
  | _ -> failwith " binary comparison only works on fixed length integer"

and eval_two op l r =
  match l,r with
  | VBit{width=w1;value=v1}, VBit{value=v2;_}
  | VInt{width=w1;value=v1}, VInt{value=v2;_} ->
    VInt({ width = w1; value = op v1 v2})
  | _ -> failwith "binary logical operation only works on bitstrings"

and eval_concat l r =
  let concat m n wn =
    Bigint.( + ) (Bigint.shift_left m wn) n in
  match l,r with
  | VBit{width=w1;value=v1}, VBit{width=w2;value=v2}
  | VInt{width=w1;value=v1}, VInt{width=w2;value=v2} ->
    VInt{width = w1+w2; value = concat v1 v2 w2}
  | _ -> failwith " binary concatenation only works on fixed length integer"

and eval_and_or op l r =
  match l,r with
  | VBool(bl), VBool(br) -> VBool(op bl br)
  | _ -> failwith "and / or operation only works on Bools"

let eval_expression (env : EvalEnv.t) (expr : Expression.t) : value =
  fst (eval_expression' env expr)

let eval = function Program l ->
  let env = List.fold_left l ~init:EvalEnv.empty_eval_env ~f:eval_decl in
  Format.printf "Looking up main@\n";
  let top = EvalEnv.get_decl_toplevel env in
  Format.printf "TopEnv: [%a]@\n"
    (Pretty.format_list_sep (fun fmt (x,_) -> Format.fprintf fmt "%s" x) ", ")
    (* TODO: call to a function from Pretty that shouldn't be exposed in the signature *)
    top;
  let main = EvalEnv.find_value "main" env in
  ignore (main);
  Format.printf "Done"
