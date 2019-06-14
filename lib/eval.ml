module I = Info
open Core
module Info = I (* JNF: ugly hack *)
open Env

(** Local module EvalEnv.t; need to fix this when finalizing type of Env*)
(* module Eval_env: sig
  type t =     {exp: (ExpType.t * direction) env ;
                typ: ExpType.t env;
                decl: DeclType.t  env;
                value: Value.t env;
                eval_decl: Types.Declaration.t env }

  val empty_env: t

  val insert_value: t -> P4String.t -> Value.t -> t

  val insert_decls: t -> P4String.t -> Declaration.t -> t

  val find: P4String.t -> 'a Env.env -> 'a

  val find_toplevel: P4String.t -> 'a Env.env -> 'a

end = struct
  type t = {exp: (ExpType.t * direction) env ;
            typ: ExpType.t env;
            decl: DeclType.t  env;
            value: Value.t env;
            eval_decl: Types.Declaration.t env }

  let empty_env = {
    exp   = [[]];
    typ   = [[]];
    decl  = [[]];
    value = [[]];
    eval_decl = [[]]
  }

  let insert name binding = function
    | []     -> raise_missing ()
    | h :: t -> ((name, binding) :: h) :: t

  let insert_value (e: t) name binding : t =
    {e with value = insert name binding e.value}

  let insert_decls (e: t) name binding : t =
    {e with eval_decl = insert name binding e.eval_decl}

  (* Looking for name in e from the current scope to top-level *)
  let find name (e: 'a Env.env) =
    Env.find name e

  let find_toplevel name (e: 'a Env.env) =
    Env.find_toplevel name e
end *)

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
let rec eval_expression (env: EvalEnv.t) (exp: Types.Expression.t) =
  let open Value in
  match snd exp with
  | True ->
    Value.Bool true
  | False ->
    Value.Bool false
  | Int (_, { width_signed = None; value }) ->
    Value.Integer value
  | Int (_, { width_signed = Some (width, true); value }) ->
    Value.Int { width; value }
  | Int (_, { width_signed = Some (width, false); value }) ->
    Value.Bit { width; value }
  | String (_, value) ->
    Value.String value
  | Name (_,name) ->
    EvalEnv.find_value name env
  | TopLevel (_,name) ->
    EvalEnv.find_value_toplevel name env
  | ArrayAccess ({ array = a; index = i }) ->
    eval_array env a i
  | BitStringAccess ({ bits = s; lo = i; hi = j }) ->
    (* TODO: BitStringAccess as l-value*)
    eval_bit_string_access env s i j
  | List { values } ->
    Value.List (values |> List.map ~f:(eval_expression env))
  | UnaryOp { op; arg = e } ->
    eval_unary op env e
  | BinaryOp { op; args = (l, r) } ->
    eval_binop op env l r
  | Cast { typ; expr } ->
    eval_cast env typ expr
  | TypeMember { typ; name } ->
    eval_typ_mem env typ name
  | ErrorMember t  -> Error (t)
  | ExpressionMember { expr; name } ->
    eval_expr_mem env expr name
  | Ternary ({ cond ; tru; fls }) ->
    eval_ternary env cond tru fls
  | FunctionCall { func; type_args; args } ->
    eval_funcall env func type_args args
  | NamelessInstantiation { typ; args } ->
    eval_nameless env typ args
  | Mask ({ expr = e; mask = m}) ->
    Set ( Mask (eval_expression env e, eval_expression env m) )
  | Range {lo; hi} ->
    Set ( Range (eval_expression env lo, eval_expression env hi) )

and eval_array env a i =
  (* header stack *)
  match (eval_expression env a) with
  | Value.List l ->
    Base.List.nth_exn l (Eval_int.to_int (eval_expression env i))
  | _ -> failwith "impossible"

(* 7.2.7 *)
and eval_expr_mem env expr name = failwith "unimplemented"

and eval_funcall env func type_args args = failwith "unimplemented"

and eval_nameless env typ args =
  let open Types in
  let positional_binding (param : Parameter.t) arg: (P4String.t * Value.t) =
    match (snd arg) with
    | Argument.Expression {value} ->
      print_endline (Info.to_string (fst value));
      let v = eval_expression env value in
      ((snd param).variable, v)
    | _ -> failwith "unimplemented"
  in
  match type_lookup env (snd typ) with
  | None -> failwith "couldn't find type..."
  | Some (info, Declaration.Control typ_decl) ->
    Objstate {
      decl = (info, Declaration.Control typ_decl);
      state = List.map2_exn typ_decl.constructor_params args ~f:positional_binding
    }
  | Some (info, Declaration.Parser typ_decl) ->
    Objstate {
      decl = (info, Declaration.Parser typ_decl);
      state = List.map2_exn typ_decl.constructor_params args ~f:positional_binding
    }
  | Some (info, Declaration.PackageType pack_decl) ->
    Objstate {
      decl = (info, Declaration.PackageType pack_decl);
      state = List.map2_exn pack_decl.params args ~f:positional_binding
    }
  | Some (_, Declaration.ExternFunction typ_decl) ->
    failwith "unimplemented"
  | Some _ -> failwith "unimplemented"

and eval_typ_mem env typ name =
  match snd typ with
  | Types.Type.HeaderStack { header = (_, TypeName s) ; size = size } ->
    if s = name then failwith "look up the context"
    else failwith "member not exist"
  | _ -> failwith "unimplemented"

and eval_argument env arg = failwith "unimplemented"
(*copy in copy out*)

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
    failwith "unimplemented"
  | BlockStatement({block}) ->
    eval_block env block
  | Exit -> env
  | EmptyStatement -> env
  | Return({expr}) -> env
  (*"TODO: difference between exit and return?"*)
  | Switch({expr; cases}) -> failwith "unimplemented"
  | DeclarationStatement({decl}) -> failwith "unimplemented "

and eval_block env block: EvalEnv.t =
  match snd block with
  | {annotations; statements} ->
    let rec loop env = function
      | [] -> env
      | h :: d -> begin
          match h with
          | _, Types.Statement.Exit -> env (*Fix: terminate all *)
          | _ -> loop (eval_statement env h) d
        end in
    loop env statements

and eval_assign env lhs rhs: EvalEnv.t =
  let open Types in
  match snd lhs with
  | Expression.Name (_,n) -> EvalEnv.insert_value env n (eval_expression env rhs)
  (* prefixedNonTypeName? *)
  | Expression.BitStringAccess({bits; lo; hi}) -> failwith "unimplemented"
  | Expression.ArrayAccess({array = ar; index}) ->
    let i = Eval_int.to_int (eval_expression env index) in
    let r = eval_expression env rhs in
    begin match snd ar, eval_expression env ar with
      | Expression.Name (_,n), List l ->
        let rec helper acc = (function
            | h::d -> if acc = i then r::d else h::(helper (acc + 1) d)
            | [] -> [])
        in
        EvalEnv.insert_value env n (Value.List(helper 0 l))
      | _ -> failwith "array expected to evaluate to Value.List?"
    end
  | Expression.ExpressionMember({ expr; name}) -> failwith "unimplemented"
  | _ -> failwith "can't assign to the LHS"

and eval_decl (env : EvalEnv.t) (d : Types.Declaration.t) : EvalEnv.t =
  let open Types.Declaration in
  match snd d with
  | Constant({annotations; typ; name = (_,name); value}) ->
    eval_expression env value |>
    EvalEnv.insert_value env name
  | Variable({annotations; typ; name; init}) ->
    eval_decl_var env annotations typ name init
  | Instantiation({annotations; typ; args; name}) ->
    eval_instantiation env typ args name
  | Parser({ name = (_,name); _ })
  | Control({ name = (_,name); _ })
  | PackageType({ name = (_,name); _ }) ->
    EvalEnv.insert_decls env name d
  | _ -> silent_fail env

(* to fix *)
and eval_decl_var env annotations typ name init =
  match init with
  | None -> env
  | Some e -> eval_expression env e |> EvalEnv.insert_value env (snd name)

and eval_instantiation (env:EvalEnv.t) typ args name =
  print_endline (snd name);
  let obj = eval_nameless env typ args in
  EvalEnv.insert_value env (snd name) obj

and eval_decl_list (env: EvalEnv.t) (decl_list : Types.Declaration.t list) : EvalEnv.t =
  List.fold_left decl_list ~init:env ~f:eval_decl

(*-------------------------------------------------------------------*)
(*The following functions are not used when evaluating hello_world.p4*)
and eval_cast env typ expr =
  let open Types in
  let build_bit w v =
    Value.Bit({width = w |> eval_expression env |> Eval_int.to_int;
               value = Bigint.of_int v}) in
  let changesize w v l =
    let new_w = l |> eval_expression env |> Eval_int.to_int in
    let value = if new_w >= w then v
      else (Bigint.shift_left v (w - new_w) |>
            Bigint.shift_right) (w - new_w) in
    (new_w, value) in
  begin match eval_expression env expr, snd typ with
    | Value.Bit({width = w; value = v}), Type.Bool ->
      if Bigint.(=) v Bigint.zero
      then Value.Bool(false)
      else if Bigint.(=) v Bigint.one
      then Value.Bool(true)
      else failwith "can't cast this bitstring to bool"
    | Value.Bool(b), Type.BitType(e) ->
      if b then build_bit e 1
      else build_bit e 0
    | Value.Int({width = w; value = v}), Type.BitType(_) ->
      let turn_pos w v =
        if Bigint.(<) v Bigint.zero
        then Bigint.(+) v (Eval_int.power2w (w+1))
        else v in
      Value.Bit({width = w; value = turn_pos w v})
    | Value.Bit({width = w; value = v}), Type.IntType(_) ->
      let neg_bit w v =
        if Bigint.(>=) v (Eval_int.power2w (w-1))
        then Bigint.(-) v (Eval_int.power2w w)
        else v in
      Value.Int({width = w; value = neg_bit w v})
    (* preserves all bits unchanged and reinterprets values whose most-significant bit is 1 as negative values *)
    | Value.Bit({width = w; value = v}), Type.BitType(l) ->
      let width, value = changesize w v l in
      Value.Bit({width; value})
    (* Should be shift_right_truncate*)
    (* truncates the value if W > X, and otherwise (i.e., if  W <= X) pads the value with zero bits; which side?*)
    | Value.Int({width = w; value = v}), Type.IntType(l) ->
      let width, value = changesize w v l in
      Value.Int({width; value})
    | _ -> failwith "unimplemented"
  end

and eval_ternary env c te fe =
  begin match (eval_expression env c) with
    | Value.Bool(true)  -> (eval_expression env te)
    | Value.Bool(false) -> (eval_expression env fe)
    | _ -> failwith "impossible to typecheck the ternary expression"
  end

(* b[m:l], m \geq l, m is index from left*)
and eval_bit_string_access env s m l =
  (* m, l are compile-time known values  *)
  let m = eval_expression env m in
  let l = eval_expression env l in
  match m, l, (eval_expression env s) with
  | Value.Bit({ width = wm; value = vm }), Value.Bit({ width = wl; value = vl }),
    Value.Bit({ width = w1; value = v1 }) ->
    let m' = Eval_int.to_int m in
    let l' = Eval_int.to_int l in
    Value.Bit({ width = m' - l' + 1;
                value = (Bigint.shift_left v1 (l'+1) |>
                         Bigint.shift_right) (w1-m'+l')}) (*should be shift right trunc*)
  | _ -> failwith "bit string access impossible"

and eval_unary op env e =
  let open Types.Op in
  begin match snd op, (eval_expression env e )  with
    | UMinus, Value.Bit({ width = w; value = v}) ->
      Value.Bit({ width = w; value = Bigint.(-) (Eval_int.power2w w) v })
    | UMinus, Value.Int({ width = w; value = v}) ->
      Value.Bit({ width = w; value = Bigint.neg v})
    | BitNot, Value.Bit({ width = w; value = v}) ->
      Value.Bit({ width = w; value = Bigint.neg v})
    | BitNot, Value.Int({ width = w; value = v}) ->
      Value.Int({ width = w; value = Bigint.neg v})
    | Not,  Value.Bool b ->  Value.Bool (not b)
    | _ -> failwith "unary options don't apply"
  end

and eval_binop op env l r =
  let open Types.Op in
  let l = eval_expression env l in
  let r = eval_expression env r in
  let eval = begin match snd op with
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
  end
  in eval env l r

(*assume the width for signed integer include the `sign` digits? *)
and eval_sat op env l r =
  let compute m n w =
    let a = Bigint.abs (op m n) in
    (* TODO: check < or <= *)
    if  Bigint.(<) a m || Bigint.(<) a n then Eval_int.power2w w else a in
  match l,r with
  | Value.Bit({ width = w1; value = v1 }), Value.Bit({width = w2; value = v2 }) ->
    Value.Bit({ width = w1; value = compute v1 v2 w1} )
  | Value.Int({ width = w1; value = v1 }), Value.Int({width = w2; value = v2 }) ->
    Value.Int({ width = w1; value = compute v1 v2 (w1-1)})
  | _ -> failwith "binary logical operation only works on bitstrings"


(* leftshift: Logical and arithmetic are the same
   rightshift: Logical and arithmetic are the same for positive but not negative
   assume that value in Value.Bit are positive Bigint
*)
and eval_shift op env l r =
  let open Value in
  match l,r with
  | Value.Bit({ width = w1; value = v1 }), Value.Bit({width = w2; value = v2 })
  | Value.Bit({ width = w1; value = v1 }), Value.Int({width = w2; value = v2 }) ->
    if v1 >= Bigint.zero then
      Bit({width = w1; value = op v1 (Bigint.to_int_exn v2)})
    else failwith "can't shift with a negative amount"
  | _ -> failwith "shift doesn't works on this type"
(* this would be impossible if type checked*)

and eval_eq op env l r =
  match l,r with
  | Value.Bit({ width = _; value = v1 }), Value.Bit({width = _; value = v2 })
  | Value.Int({ width = _; value = v1 }), Value.Int({width = _; value = v2 })
  | Value.Integer v1, Value.Integer v2 ->
    if op v1 v2 then Value.Bool true else Value.Bool false
  | _ -> failwith "equality for varbit binary comparison only works on bitstrings"

and eval_compare op env l r =
  match l,r with
  | Value.Bit({ width = w1; value = v1 }), Value.Bit({width = w2; value = v2 })
  | Value.Int({ width = w1; value = v1 }), Value.Int({width = w2; value = v2 }) ->
    if op v1 v2 then Value.Bool true else Value.Bool false
  | _ -> failwith " binary comparison only works on fixed length integer"

and eval_two op env l r =
  match l,r with
  | Value.Bit({ width = w1; value = v1 }), Value.Bit({width = w2; value = v2 }) ->
    Value.Bit({ width = w1; value = op v1 v2} )
  | Value.Int({ width = w1; value = v1 }), Value.Int({width = w2; value = v2 }) ->
    Value.Int({ width = w1; value = op v1 v2})
  | _ -> failwith "binary logical operation only works on bitstrings"

and eval_concat env l r =
  let concat (m:Bigint.t) (n:Bigint.t) shift_amount =
    Bigint.( + ) (Bigint.shift_left m shift_amount) n in
  match l,r with
  | Value.Bit({ width = w1; value = v1 }), Value.Bit({width = w2; value = v2 }) ->
    Value.Bit({ width = w1+w2; value = concat v1 v2 w2})
  | Value.Int({ width = w1; value = v1 }), Value.Int({width = w2; value = v2 }) ->
    Value.Int({ width = w1+w2; value = concat v1 v2 w2})
  | _ -> failwith " binary concatenation only works on fixed length integer"

and eval_and_or op env l r =
  let open Value in
  match l,r with
  | Bool(bl), Bool(br) -> Bool(op bl br)
  | _ -> failwith "and / or operation only works on Bools"

(*-------------------------------------------------------------------*)

(* Entry point *)
let eval = function Types.Program l ->
  let env = eval_decl_list EvalEnv.empty_eval_env l in
  Format.printf "Looking up main@\n";
  let top = EvalEnv.get_decl_toplevel env in
  Format.printf "TopEnv: [%a]@\n"
    (Pretty.format_list_sep (fun fmt (x,_) -> Format.fprintf fmt "%s" x) ", ")
    top;
  let main = EvalEnv.find_value "main" env in
  ignore (main);
  Format.printf "Done"
