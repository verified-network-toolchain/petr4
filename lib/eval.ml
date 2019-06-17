module I = Info
open Core
module Info = I (* JNF: ugly hack *)
open Env

let silent_fail v =
  print_endline "Skipping for now...";
  v

let rec type_lookup (e : EvalEnv.t) =
  let open Types.Type in function
    | TypeName (_,s) ->
      Some (EvalEnv.find_decl s e)
    | TopLevelType (_,s) ->
      Some (EvalEnv.find_decl_toplevel s e)
    (* TODO deal with specialization? *)
    | SpecializedType ({base; args}) ->
      type_lookup e (snd base)
    | _ -> failwith "lookup unexpected type"

module Eval_int: sig
  val to_int: Value.t -> int
  val power2w: int -> Bigint.t
end = struct
  (* Cast Bit, Int, Integer in Value to integers *)
  let to_int = function
    | Value.Integer(v1)
      -> Bigint.to_int_exn v1
    | Value.Bit({ width = w1; value = v1 })
    | Value.Int({ width = w1; value = v1 })
      -> Bigint.to_int_exn v1
    | _ -> failwith "impossible to get "

  (* return 2^w, in Bigint.t*)
  let power2w w = Bigint.shift_left (Bigint.of_int 1) (w-1)
end

(* evaluating expression would not produce side-effect?*)
let rec eval_expression' (env: EvalEnv.t) (exp: Types.Expression.t) : Value.t * EvalEnv.t =
  let open Value in
  match snd exp with
  | True ->
    (Value.Bool true, env)
  | False ->
    (Value.Bool false, env)
  | Int (_, { width_signed = None; value }) ->
    (Value.Integer value, env)
  | Int (_, { width_signed = Some (width, true); value }) ->
    (Value.Int { width; value }, env)
  | Int (_, { width_signed = Some (width, false); value }) ->
    (Value.Bit { width; value }, env)
  | String (_, value) ->
    (Value.String value, env)
  | Name (_,name) ->
    (EvalEnv.find_value name env, env)
  | TopLevel (_,name) ->
    (EvalEnv.find_value_toplevel name env, env)
  | ArrayAccess ({ array = a; index = i }) ->
    eval_array env a i
  | BitStringAccess ({ bits = s; lo = i; hi = j }) ->
    (eval_bit_string_access env s i j, env)
  | List { values } ->
    let f = fun (l,e) expr ->
      let (v,e') = eval_expression' e expr in
      (v::l,e') in
    let (l,env_final) = values |> List.fold_left ~f:f ~init:([],env) in
    (Value.List l, env_final)
  | UnaryOp { op; arg = e } ->
    eval_unary op env e
  | BinaryOp { op; args = (l, r) } ->
    eval_binop op env l r
  | Cast { typ; expr } ->
    eval_cast env typ expr
  | TypeMember { typ; name } ->
    eval_typ_mem env typ name
  | ErrorMember t  -> (Error (t), env)
  | ExpressionMember { expr; name } ->
    eval_expr_mem env expr name
  | Ternary ({ cond ; tru; fls }) ->
    eval_ternary env cond tru fls
  | FunctionCall { func; type_args; args } ->
    eval_funcall env func args
  | NamelessInstantiation { typ; args } ->
    eval_nameless env typ args
  | Mask ({ expr = e; mask = m}) ->
    let (v1,env') = eval_expression' env e in
    let (v2,env'') = eval_expression' env' m in
    (Set ( Mask (v1, v2) ), env'')
  | Range {lo; hi} ->
    let (v1,env') = eval_expression' env lo in
    let (v2,env'') = eval_expression' env' hi in
    (Set ( Range (v1, v2) ), env'')

and eval_array env a i =
  (* header stack *)
  (* TODO: find a more graceful way to raise an error in both error cases*)
  let (a',env') = eval_expression' env a in
  match a' with
  | Value.List l ->
    let (i',env'') = eval_expression' env' i in
    (Base.List.nth_exn l (Eval_int.to_int i'), env')
  | Value.Bool _
  | Value.Integer _
  | Value.Bit _
  | Value.Int _
  | Value.Set _
  | Value.String _
  | Value.Error _
  | Value.Closure _
  | Value.Header_or_struct _
  | Value.Objstate _ -> failwith "impossible"

(* 7.2.7 *)
and eval_expr_mem env expr name =
  (* let rec lookup_field l s = match l with
    | [] -> failwith "unknown field name"
    | ((_,s'), value) :: t->
      if s = s' then value else lookup_field t s in *)
  match eval_expression' env expr with
  | _ -> failwith "unimplemented"
(* TODO: flesh out this detail once more is known about values *)


and eval_funcall env func args = failwith "unimplemented"
  (* match eval_expression' env func with
  | Closure(params,body) ->
    let env' = eval_args (push_scope env) args params in
    EvalEnv.pop_scope (eval_statement env' body) *)

and eval_nameless env typ args =
  let open Types in
  let positional_binding env ((param, arg) : (Parameter.t * Argument.t)) =
    match (snd arg) with
    | Argument.Expression {value} ->
      print_endline (Info.to_string (fst value));
      let v,env' = eval_expression' env value in
      (env',((snd param).variable, v))
    | _ -> failwith "unimplemented"
  in
  match type_lookup env (snd typ) with
  | None -> failwith "couldn't find type..."
  | Some (info, Declaration.Control typ_decl) ->
    let l = List.zip_exn typ_decl.constructor_params args in
    let (new_env,state) = List.fold_map l ~f:positional_binding ~init:env in
    ((Value.Objstate {
      decl = (info, Declaration.Control typ_decl);
      state = state;
    }), new_env)
  | Some (info, Declaration.Parser typ_decl) ->
    let l = List.zip_exn typ_decl.constructor_params args in
    let (new_env,state) = List.fold_map l ~f:positional_binding ~init:env in
    ((Value.Objstate {
      decl = (info, Declaration.Parser typ_decl);
      state = state;
    }), new_env)
  | Some (info, Declaration.PackageType pack_decl) ->
    let l = List.zip_exn pack_decl.params args in
    let (new_env,state) = List.fold_map l ~f:positional_binding ~init:env in
    ((Value.Objstate {
      decl = (info, Declaration.PackageType pack_decl);
      state = state
    }), new_env)
  | Some (_, Declaration.ExternFunction typ_decl) ->
    failwith "unimplemented"
  | Some _ -> failwith "unimplemented" (* TODO: can instantiation happen for other types? *)

and eval_typ_mem env typ name = (* TODO: implement member lookup *)
  match snd typ with
  | Types.Type.HeaderStack { header = (_, TypeName s) ; size = size } ->
    if s = name then failwith "look up the context"
    else failwith "member not exist"
  | _ -> failwith "unimplemented"

(* TODO: *)
and eval_args env args params = failwith "unimplemented"
  (* match List.zip_exn params args with
  | [] -> new_env
  | (param, arg) :: t -> insert *)

(* TODO: is this function obselete? *)
and eval_arg env arg param = failwith "unimplemented"
(*copy in copy out*)

(* TODO: flesh out implementation for statements*)
and eval_statement (env : EvalEnv.t) (s : Types.Statement.t) : EvalEnv.t =
  let open Types.Statement in
  match snd s with
  | Assignment({lhs; rhs}) ->
    eval_assign env lhs rhs
  | MethodCall({func; type_args; args}) ->
    failwith "unimplemented"
  | DirectApplication({typ; args}) ->
    failwith "unimplemented"
  | Conditional({cond; tru; fls}) ->
    eval_conditional env cond tru fls
  | BlockStatement({block}) ->
    eval_block env block
  | Exit -> env
  | EmptyStatement -> env
  | Return({expr}) -> env
  (*"TODO: difference between exit and return?"*)
  | Switch({expr; cases}) -> failwith "unimplemented"
  | DeclarationStatement({decl}) -> failwith "unimplemented "

and eval_conditional env cond tru fls =
  let v,env' = eval_expression' env cond in
  match v with
  | Value.Bool true -> eval_statement env' tru
  | Value.Bool false ->
    begin match fls with
      | None -> env
      | Some fls' -> eval_statement env' fls' end
  | Integer _
  | Bit _
  | Int _
  | List _
  | Set _
  | String _
  | Error _
  | Closure _
  | Header_or_struct _
  | Objstate _ -> failwith "conditional guard must be a bool"

and eval_block env block: EvalEnv.t =
  match snd block with
  | {annotations; statements} ->
    let rec loop env = function
      | [] -> env
      | h :: d -> begin
          match h with
          | _, Types.Statement.Exit -> env (* TODO: Fix: terminate all *)
          | _, Types.Statement.Return  _ -> env (* TODO: fix *)
          | _ -> loop (eval_statement env h) d
        end in
    loop env statements

and eval_assign env lhs rhs: EvalEnv.t =
  let open Types in
  match snd lhs with
  | Expression.Name (_,n) -> EvalEnv.insert_value env n (fst (eval_expression' env rhs))
  (* prefixedNonTypeName? *)
  | Expression.BitStringAccess({bits; lo; hi}) -> failwith "unimplemented"
  | Expression.ArrayAccess({array = ar; index}) ->
    let (index',env') = eval_expression' env index in
    let i = Eval_int.to_int index' in
    let (r, env'') = eval_expression' env' rhs in
    let (ar', env''') = eval_expression' env'' ar in
    begin match snd ar, ar' with
      | Expression.Name (_,n), List l ->
        let rec helper acc = (function
            | h::d -> if acc = i then r::d else h::(helper (acc + 1) d)
            | [] -> [])
        in
        EvalEnv.insert_value env''' n (Value.List(helper 0 l))
      | _ -> failwith "array expected to evaluate to Value.List?"
    end
  | Expression.ExpressionMember({ expr; name}) -> failwith "unimplemented"
  | _ -> failwith "can't assign to the LHS"

and eval_decl (env : EvalEnv.t) (d : Types.Declaration.t) : EvalEnv.t =
  let open Types.Declaration in
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
    EvalEnv.insert_value env name (Closure(params,body))
  | ExternFunction _ -> silent_fail env (* TODO *)
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
  | ParserType _ -> silent_fail env (* TODO *)
  | PackageType({ name = (_,name); _ }) ->
    EvalEnv.insert_decls env name d

(* to fix *)
and eval_decl_var env annotations typ name init =
  match init with
  | None -> env
  | Some e ->
    let (v,env') = eval_expression' env e in
    EvalEnv.insert_value env' (snd name) v

and eval_instantiation (env:EvalEnv.t) typ args name =
  print_endline (snd name); (* TODO: why are we printing here? *)
  let (obj,env') = eval_nameless env typ args in
  EvalEnv.insert_value env' (snd name) obj

and eval_decl_list (env: EvalEnv.t) (decl_list : Types.Declaration.t list) : EvalEnv.t =
  List.fold_left decl_list ~init:env ~f:eval_decl
    (* TODO: unnecessary warpper function? *)

(*-------------------------------------------------------------------*)
(*The following functions are not used when evaluating hello_world.p4*)
and eval_cast env typ expr =
  let open Types in
  let build_bit w v =
    Value.Bit({width = w |> Eval_int.to_int;
               value = Bigint.of_int v}) in
  let changesize w v l =
    let new_w = l |> Eval_int.to_int in
    let value = if new_w >= w then v
      else (Bigint.shift_left v (w - new_w) |>
            Bigint.shift_right) (w - new_w) in
    (new_w, value) in
  let (expr',env') = eval_expression' env expr in
  match expr', snd typ with
    | Value.Bit({width = 1; value = v}), Type.Bool ->
      if Bigint.(=) v Bigint.zero
      then (Value.Bool(false), env')
      else if Bigint.(=) v Bigint.one
      then (Value.Bool(true), env')
      else failwith "can't cast this bitstring to bool"
    | Value.Bool(b), Type.BitType(e) -> (* should only work when [e] is [1] *)
      let (e',env'') = eval_expression' env' e in
      if b then (build_bit e' 1, env'')
      else (build_bit e' 0, env'')
    | Value.Int({width = w; value = v}), Type.BitType(w') -> (* should only work when [w] is [w'] *)
      let turn_pos w v =
        if Bigint.(<) v Bigint.zero
        then Bigint.(+) v (Eval_int.power2w (w+1))
        else v in
      (Value.Bit({width = w; value = turn_pos w v}), env')
    | Value.Bit({width = w; value = v}), Type.IntType(w') -> (* should only work when [w] is [w'] *)
      let neg_bit w v =
        if Bigint.(>=) v (Eval_int.power2w (w-1))
        then Bigint.(-) v (Eval_int.power2w w)
        else v in
      (Value.Int({width = w; value = neg_bit w v}), env')
      (* preserves all bits unchanged and reinterprets values whose most-significant bit
      is 1 as negative values *)
    | Value.Bit({width = w; value = v}), Type.BitType(l) ->
      let (l',env'') = eval_expression' env' l in
      let width, value = changesize w v l' in
      (Value.Bit({width; value}), env'')
    (* TODO: validate: Should be shift_right_truncate*)
    (* truncates the value if W > X, and otherwise (i.e., if  W <= X) pads the value with zero bits; which side?*)
    | Value.Int({width = w; value = v}), Type.IntType(l) ->
      let (l',env'') = eval_expression' env l in
      let width, value = changesize w v l' in
      (Value.Int({width; value}), env'')
    | _ -> failwith "type cast case should be handled by compiler"
  (* TODO: graceful failure *)

and eval_ternary env c te fe =
  let (c', env') = eval_expression' env c in
  match c' with
    | Value.Bool(true)  -> (eval_expression' env te)
    | Value.Bool(false) -> (eval_expression' env fe)
    | _ -> failwith "impossible to typecheck the ternary expression" (* TODO: fail gracefully *)

(* b[m:l], m \geq l, m is index from left*)
and eval_bit_string_access env s m l =
  (* m, l are compile-time known values  *)
  (* TODO: assert that m is greater than l as specified in p4 spec *)
  (* TODO: graceful failure *)
  let (m,env') = eval_expression' env m in
  let (l,env'') = eval_expression' env' l in
  let (s,env''') = eval_expression' env'' s in
  match m, l, s with
  | Value.Bit({ width = wm; value = vm }), Value.Bit({ width = wl; value = vl }),
    Value.Bit({ width = w1; value = v1 }) ->
    let m' = Eval_int.to_int m in
    let l' = Eval_int.to_int l in
    Value.Bit({ width = m' - l' + 1;
                value = (Bigint.shift_left v1 (l'+1) |>
                         Bigint.shift_right) (w1-m'+l')}) (*TODO: should be shift right trunc*)
  | _ -> failwith "bit string access impossible"

and eval_unary op env e =
  let open Types.Op in
  let (e',env') = eval_expression' env e in
  match snd op, e'  with
    | UMinus, Value.Bit({ width = w; value = v}) ->
      (Value.Bit({ width = w; value = Bigint.(-) (Eval_int.power2w w) v }), env')
    | UMinus, Value.Int({ width = w; value = v}) ->
      (Value.Bit({ width = w; value = Bigint.neg v}), env')
    | BitNot, Value.Bit({ width = w; value = v}) ->
      (Value.Bit({ width = w; value = Bigint.neg v}), env')
    | BitNot, Value.Int({ width = w; value = v}) ->
      (Value.Int({ width = w; value = Bigint.neg v}), env')
    | Not,  Value.Bool b ->  (Value.Bool (not b), env')
    | _ -> failwith "unary options don't apply" (* TODO: fail gracefully *)

and eval_binop op env l r =
  let open Types.Op in
  let (l,env') = eval_expression' env l in
  let (r,env'') = eval_expression' env' r in
  let eval = match snd op with
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
    | Or       -> eval_and_or (||)
  in eval env'' l r

(* TODO: assert widths are the same? handled by type checker? implicit casting? *)
(* TODO: these functions need to fail more gracefully *)
(*assume the width for signed integer include the `sign` digits? *)
and eval_sat op env l r =
  let compute m n w =
    let a = Bigint.abs (op m n) in
    (* TODO: check < or <= *)
    if  Bigint.(<) a m || Bigint.(<) a n then Eval_int.power2w w else a in
  let v = begin match l,r with
  | Value.Bit({ width = w1; value = v1 }), Value.Bit({width = w2; value = v2 }) ->
    Value.Bit({ width = w1; value = compute v1 v2 w1} )
  | Value.Int({ width = w1; value = v1 }), Value.Int({width = w2; value = v2 }) ->
    Value.Int({ width = w1; value = compute v1 v2 (w1-1)})
  | _ -> failwith "binary logical operation only works on bitstrings" end in
  (v,env)


(* leftshift: Logical and arithmetic are the same
   rightshift: Logical and arithmetic are the same for positive but not negative
   assume that value in Value.Bit are positive Bigint
*)
and eval_shift op env l r =
  let open Value in
  let v = begin
  match l,r with
  | Value.Bit({ width = w1; value = v1 }), Value.Bit({width = w2; value = v2 })
  | Value.Bit({ width = w1; value = v1 }), Value.Int({width = w2; value = v2 }) ->
    if v1 >= Bigint.zero then
      Bit({width = w1; value = op v1 (Bigint.to_int_exn v2)})
    else failwith "can't shift with a negative amount"
  | _ -> failwith "shift doesn't works on this type" end in
  (v,env)

(* this would be impossible if type checked*)

and eval_eq op env l r =
  let v = begin
  match l,r with
  | Value.Bit({ width = _; value = v1 }), Value.Bit({width = _; value = v2 })
  | Value.Int({ width = _; value = v1 }), Value.Int({width = _; value = v2 })
  | Value.Integer v1, Value.Integer v2 ->
    if op v1 v2 then Value.Bool true else Value.Bool false
  | _ -> failwith "equality for varbit binary comparison only works on bitstrings" end in
  (v,env)

and eval_compare op env l r =
  let v = begin
  match l,r with
  | Value.Bit({ width = w1; value = v1 }), Value.Bit({width = w2; value = v2 })
  | Value.Int({ width = w1; value = v1 }), Value.Int({width = w2; value = v2 }) ->
    if op v1 v2 then Value.Bool true else Value.Bool false
  | _ -> failwith " binary comparison only works on fixed length integer" end in
  (v,env)

and eval_two op env l r =
  let v = begin
  match l,r with
  | Value.Bit({ width = w1; value = v1 }), Value.Bit({width = w2; value = v2 }) ->
    Value.Bit({ width = w1; value = op v1 v2} )
  | Value.Int({ width = w1; value = v1 }), Value.Int({width = w2; value = v2 }) ->
    Value.Int({ width = w1; value = op v1 v2})
  | _ -> failwith "binary logical operation only works on bitstrings" end in
  (v,env)

and eval_concat env l r =
  let concat (m:Bigint.t) (n:Bigint.t) shift_amount =
    Bigint.( + ) (Bigint.shift_left m shift_amount) n in
  let v = begin
  match l,r with
  | Value.Bit({ width = w1; value = v1 }), Value.Bit({width = w2; value = v2 }) ->
    Value.Bit({ width = w1+w2; value = concat v1 v2 w2})
  | Value.Int({ width = w1; value = v1 }), Value.Int({width = w2; value = v2 }) ->
    Value.Int({ width = w1+w2; value = concat v1 v2 w2})
  | _ -> failwith " binary concatenation only works on fixed length integer" end in
  (v,env)

and eval_and_or op env l r =
  let open Value in
  let v = begin
  match l,r with
  | Bool(bl), Bool(br) -> Bool(op bl br)
  | _ -> failwith "and / or operation only works on Bools" end in
  (v,env)

(*-------------------------------------------------------------------*)

let eval_expression (env : EvalEnv.t) (expr : Types.Expression.t) : Value.t =
  fst (eval_expression' env expr)

(* Entry point *)
let eval = function Types.Program l ->
  let env = eval_decl_list EvalEnv.empty_eval_env l in
  Format.printf "Looking up main@\n";
  let top = EvalEnv.get_decl_toplevel env in
  Format.printf "TopEnv: [%a]@\n"
    (Pretty.format_list_sep (fun fmt (x,_) -> Format.fprintf fmt "%s" x) ", ")
    (* TODO: call to a function from Pretty that shouldn't be exposed in the signature *)
    top;
  let main = EvalEnv.find_value "main" env in
  ignore (main);
  Format.printf "Done"
