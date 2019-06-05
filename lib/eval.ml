open Types

let rec eval_expression (env: Env.eval_env) (exp: Expression.t) =
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
  | List { values } ->
    Value.List (values |> List.map (eval_expression env))
  | BinaryOp { op; args = (l, r) } ->
    let open Op in
    let l = eval_expression env l in
    let r = eval_expression env r in
    let eval = begin match snd op with
      | Plus     -> eval_plus
      | PlusSat  -> eval_plus_sat
      | Minus    -> eval_minus
      | MinusSat -> eval_minus_sat
      | Mul      -> eval_mul
      | Div      -> eval_div
      | Mod      -> eval_mod
      | Shl      -> eval_shl
      | Shr      -> eval_shr
      | Le       -> eval_le
      | Ge       -> eval_ge
      | Lt       -> eval_lt
      | Gt       -> eval_gt
      | Eq       -> eval_eq
      | NotEq    -> eval_not_eq
      | BitAnd   -> eval_bit_and
      | BitXor   -> eval_bit_xor
      | BitOr    -> eval_bit_or
      | PlusPlus -> eval_plus_plus
      | And      -> eval_and
      | Or       -> eval_or
      end
    in eval env l r
  | _ -> failwith "Unimplemented"

and eval_plus _ _ _ =
  failwith "Unimplemented"

and eval_plus_sat _ _ _ =
  failwith "Unimplemented"

and eval_minus _ _ _ =
  failwith "Unimplemented"

and eval_minus_sat _ _ _ =
  failwith "Unimplemented"

and eval_mul _ _ _ =
  failwith "Unimplemented"

and eval_div _ _ _ =
  failwith "Unimplemented"

and eval_mod _ _ _ =
  failwith "Unimplemented"

and eval_shl _ _ _ =
  failwith "Unimplemented"

and eval_shr _ _ _ =
  failwith "Unimplemented"

and eval_le _ _ _ =
  failwith "Unimplemented"

and eval_ge _ _ _ =
  failwith "Unimplemented"

and eval_lt _ _ _ =
  failwith "Unimplemented"

and eval_gt _ _ _ =
  failwith "Unimplemented"

and eval_eq _ _ _ =
  failwith "Unimplemented"

and eval_not_eq _ _ _ =
  failwith "Unimplemented"

and eval_bit_and _ _ _ =
  failwith "Unimplemented"

and eval_bit_xor _ _ _ =
  failwith "Unimplemented"

and eval_bit_or _ _ _ =
  failwith "Unimplemented"

and eval_plus_plus _ _ _ =
  failwith "Unimplemented"

and eval_and _ _ _ =
  failwith "Unimplemented"

and eval_or _ _ _ =
  failwith "Unimplemented"
