open Core_kernel
open P4light
open Bitstring

(*----------------------------------------------------------------------------*)
(* Unary Operator Evaluation *)
(*----------------------------------------------------------------------------*)

let eval_not (v : coq_Value) : coq_Value =
  match v with
  | ValBool b -> ValBool (not b)
  | _ -> failwith "not operator can only be applied to bools"

let eval_bitnot (v : coq_Value) : coq_Value =
  match v with
  | ValBit (w, n) -> ValBit (w, bitwise_neg_of_bigint n (Bigint.of_int w))
  | _ -> failwith "bitwise complement on non-fixed width unsigned bitstring"

and eval_uminus (v : coq_Value) : coq_Value =
  match v with
  | ValBit (w, n) -> Bigint.(ValBit (w, (power_of_two (of_int w)) - n))
  | ValInt (w, n) -> Bigint.(ValInt (w, to_twos_complement (-n) (of_int w)))
  | ValInteger n -> ValInteger (Bigint.neg n)
  | _ -> failwith "unary minus on non-int type"

(*----------------------------------------------------------------------------*)
(* binary operator interpretation *)
(*----------------------------------------------------------------------------*)

let unsigned_op_sat (l : Bigint.t) (r : Bigint.t) (w : int)
(op : Bigint.t -> Bigint.t -> Bigint.t) : coq_Value =
  let x = power_of_two (Bigint.of_int w) in
  let n = op l r in
  let n' =
    if Bigint.(n > zero)
    then Bigint.min n Bigint.(x - one)
    else Bigint.max n Bigint.zero in
  ValBit (w, n')

let signed_op_sat (l : Bigint.t) (r : Bigint.t) (w : int)
(op : Bigint.t -> Bigint.t -> Bigint.t) : coq_Value =
  let x = power_of_two Bigint.(of_int w - one) in
  let n = op l r in
  let n' =
    if Bigint.(n > zero)
    then Bigint.min n Bigint.(x - one)
    else Bigint.max n Bigint.(-x) in
  ValInt (w, n')

let rec interp_bplus (l : coq_Value) (r : coq_Value) : coq_Value =
  match (l,r) with
  | ValBit (w, v1), ValBit (_, v2) ->
    let v = Bigint.(of_twos_complement (v1 + v2) (of_int w)) in
    ValBit(w, v) 
  | ValInt (w, v1), ValInt (_, v2) ->
    let v = Bigint.(to_twos_complement (v1 + v2) (of_int w)) in
    ValInt(w, v)
  | ValBit (w, v1), ValInteger n   -> interp_bplus l (bit_of_rawint n w)
  | ValInteger n,   ValBit (w, v1) -> interp_bplus (bit_of_rawint n w) r
  | ValInt (w, v1), ValInteger n   -> interp_bplus l (int_of_rawint n w)
  | ValInteger n,   ValInt (w, v1) -> interp_bplus (int_of_rawint n w) r
  | ValInteger n1,  ValInteger n2  -> ValInteger Bigint.(n1 + n2)
  | _ -> failwith "binary plus operation only defined on ints"

let rec interp_bplus_sat (l : coq_Value) (r : coq_Value) : coq_Value =
  match (l,r) with
  | ValBit(w, v1), ValBit(_, v2) -> unsigned_op_sat v1 v2 w Bigint.(+)
  | ValInt(w, v1), ValInt(_, v2) -> signed_op_sat v1 v2 w Bigint.(+)
  | ValBit(w, v1), ValInteger n   -> interp_bplus_sat l (bit_of_rawint n w)
  | ValInteger n,   ValBit(w, _)    -> interp_bplus_sat (bit_of_rawint n w) r
  | ValInt(w, _),    ValInteger n   -> interp_bplus_sat l (int_of_rawint n w)
  | ValInteger n,   ValInt(w, _)    -> interp_bplus_sat (int_of_rawint n w) r
  | _ -> failwith "binary sat plus operation only definted on fixed-width ints"

let rec interp_bminus (l : coq_Value) (r : coq_Value) : coq_Value =
  match (l,r) with
  | ValBit(w, v1), ValBit(_, v2) ->
    let v = Bigint.(of_twos_complement (v1 - v2) (of_int w)) in
    ValBit(w, v)
  | ValInt(w, v1), ValInt(_, v2) ->
    let v = Bigint.(to_twos_complement (v1 - v2) (of_int w)) in
    ValInt(w, v)
  | ValBit(w, v1), ValInteger n   -> interp_bminus l (bit_of_rawint n w)
  | ValInteger n,   ValBit(w, v1) -> interp_bminus (bit_of_rawint n w) r
  | ValInt(w, v1), ValInteger n   -> interp_bminus l (int_of_rawint n w)
  | ValInteger n,   ValInt(w, v1) -> interp_bminus (int_of_rawint n w) r
  | ValInteger n1,  ValInteger n2  -> ValInteger Bigint.(n1 - n2)
  | _ -> failwith "binary plus operation only defined on ints"

let rec interp_bminus_sat (l : coq_Value) (r : coq_Value) : coq_Value =
  match (l,r) with
  | ValBit(w, v1), ValBit(_, v2) -> unsigned_op_sat v1 v2 w Bigint.(-)
  | ValInt(w, v1), ValInt(_, v2) -> signed_op_sat v1 v2 w Bigint.(-)
  | ValBit(w, v1), ValInteger n   -> interp_bminus_sat l (bit_of_rawint n w)
  | ValInteger n, ValBit(w, _)      -> interp_bminus_sat (bit_of_rawint n w) r
  | ValInt(w, _), ValInteger n      -> interp_bminus_sat l (int_of_rawint n w)
  | ValInteger n, ValInt(w, _)      -> interp_bminus_sat (int_of_rawint n w) r
  | _ -> failwith "binary sat plus operation only definted on fixed-width ints"

let rec interp_bmult (l : coq_Value) (r : coq_Value) : coq_Value =
  match (l,r) with
  | ValBit(w, v1), ValBit(_, v2) ->
    ValBit(w, of_twos_complement Bigint.(v1 * v2) (Bigint.of_int w))
  | ValInt(w, v1), ValInt(_, v2) ->
    ValInt(w, to_twos_complement Bigint.(v1 * v2) (Bigint.of_int w))
  | ValBit(w, v1), ValInteger n   -> interp_bmult l (bit_of_rawint n w)
  | ValInteger n,   ValBit(w, v1) -> interp_bmult (bit_of_rawint n w) r
  | ValInt(w, v1), ValInteger n   -> interp_bmult l (int_of_rawint n w)
  | ValInteger n,   ValInt(w, v1) -> interp_bmult (int_of_rawint n w) r
  | ValInteger n1,  ValInteger n2  -> ValInteger Bigint.(n1 * n2)
  | _ -> failwith "binary mult operation only defined on ints"

let interp_bdiv (l : coq_Value) (r : coq_Value) : coq_Value =
  match (l,r) with
  | ValInteger n1, ValInteger n2     -> ValInteger Bigint.(n1 / n2)
  | ValBit (w, v1), ValBit (_, v2) -> ValBit (w, Bigint.(v1 / v2))
  | _ -> failwith "division only defined on positive values"

let interp_bmod (l : coq_Value) (r : coq_Value) : coq_Value =
  match (l,r) with
  | ValInteger n1, ValInteger n2     -> ValInteger Bigint.(n1 % n2)
  | ValBit (w, v1), ValBit (_, v2) -> ValBit (w, Bigint.(v1 % v2))
  | _ -> failwith "mod only defined on positive values"

let interp_bshl (l : coq_Value) (r : coq_Value) : coq_Value =
  match (l,r) with
  | ValBit(w, v1), ValBit(_, v2)
  | ValBit(w, v1), ValInteger v2 ->
    ValBit(w, of_twos_complement (shift_bitstring_left v1 v2) (Bigint.of_int w))
  | ValInt(w, v1), ValBit(_, v2)
  | ValInt(w, v1), ValInteger v2 ->
    ValInt(w, to_twos_complement (shift_bitstring_left v1 v2) (Bigint.of_int w))
  | ValInteger v1, ValInteger v2  -> ValInteger(shift_bitstring_left v1 v2)
  | ValBit (w, v1), ValInt(_, v2) ->
    ValBit(w, of_twos_complement (shift_bitstring_left v1 v2) (Bigint.of_int w))
  | ValInt (w, v1), ValInt(_, v2) ->
    ValInt(w, to_twos_complement (shift_bitstring_left v1 v2) (Bigint.of_int w))
  | _ -> failwith "shift left operator not defined for these types"

let interp_bshr (l : coq_Value) (r : coq_Value) : coq_Value =
  match (l,r) with
  | ValBit (w, v1), ValBit(_, v2)
  | ValBit(w, v1), ValInteger v2 ->
    ValBit(w, of_twos_complement (shift_bitstring_right v1 v2 false Bigint.zero) (Bigint.of_int w))
  | ValInt(w, v1), ValBit(_, v2)
  | ValInt (w, v1), ValInt(_, v2)
  | ValInt(w, v1), ValInteger v2 ->
    let w' = Bigint.of_int w in
    let v1 = of_twos_complement v1 w' in
    let exp = Bitstring.power_of_two Bigint.(w' - one) in
    let arith = Bigint.(v1 > exp) in
    ValInt(w, to_twos_complement (shift_bitstring_right v1 v2 arith exp) w')
  | ValInteger v1,  ValInteger v2 ->
    ValInteger(shift_bitstring_right v1 v2 false Bigint.zero)
  | ValBit (w, v1), ValInt(_, v2) ->
    ValBit(w, of_twos_complement (shift_bitstring_right v1 v2 false Bigint.zero) (Bigint.of_int w))
  | _ -> failwith "shift right operator not defined for these types"

let rec interp_ble (l : coq_Value) (r : coq_Value) : coq_Value =
  match (l,r) with
  | ValBit(_, v1), ValBit(_, v2)
  | ValInteger v1, ValInteger v2
  | ValInt(_, v1), ValInt(_, v2) -> ValBool Bigint.(v1 <= v2)
  | ValInteger v1, ValBit(w, v2)  -> interp_ble (bit_of_rawint v1 w) r
  | ValBit(w, v1), ValInteger v2  -> interp_ble l (bit_of_rawint v2 w)
  | ValInteger v1, ValInt(w, v2)  -> interp_ble (int_of_rawint v1 w) r
  | ValInt(w, v1), ValInteger v2  -> interp_ble l (int_of_rawint v2 w)
  | _ -> failwith "leq operator only defined on int types"

let rec interp_bge (l : coq_Value) (r : coq_Value) : coq_Value =
  match (l,r) with
  | ValBit(_, v1), ValBit(_, v2)
  | ValInteger v1,  ValInteger v2
  | ValInt(_, v1), ValInt(_, v2) -> ValBool Bigint.(v1 >= v2)
  | ValInteger v1,  ValBit(w, v2) -> interp_bge (bit_of_rawint v1 w) r
  | ValBit(w, v1), ValInteger v2  -> interp_bge l (bit_of_rawint v2 w)
  | ValInteger v1,  ValInt(w, v2) -> interp_bge (int_of_rawint v1 w) r
  | ValInt(w, v1), ValInteger v2  -> interp_bge l (int_of_rawint v2 w)
  | _ -> failwith "geq operator only defined on int types"

let rec interp_blt (l : coq_Value) (r : coq_Value) : coq_Value =
  match (l,r) with
  | ValBit(_, v1), ValBit(_, v2)
  | ValInteger v1, ValInteger v2
  | ValInt(_, v1), ValInt(_, v2) -> ValBool Bigint.(v1 < v2)
  | ValInteger v1, ValBit(w, v2)  -> interp_blt (bit_of_rawint v1 w) r
  | ValBit(w, v1), ValInteger v2  -> interp_blt l (bit_of_rawint v2 w)
  | ValInteger v1, ValInt(w, v2)  -> interp_blt (int_of_rawint v1 w) r
  | ValInt(w, v1), ValInteger v2  -> interp_blt l (int_of_rawint v2 w)
  | _ -> failwith "lt operator only defined on int types"

let rec interp_bgt (l : coq_Value) (r : coq_Value) : coq_Value =
  match (l,r) with
  | ValBit(_, v1), ValBit(_, v2)
  | ValInteger v1,  ValInteger v2
  | ValInt(_, v1), ValInt(_, v2) -> ValBool Bigint.(v1 > v2)
  | ValInteger v1,  ValBit(w, v2) -> interp_bgt (bit_of_rawint v1 w) r
  | ValBit(w, v1), ValInteger v2  -> interp_bgt l (bit_of_rawint v2 w)
  | ValInteger v1,  ValInt(w, v2) -> interp_bgt (int_of_rawint v1 w) r
  | ValInt(w, v1), ValInteger v2  -> interp_bgt l (int_of_rawint v2 w)
  | _ -> failwith "gt operator only defined on int types"

let rec interp_beq (l : coq_Value) (r : coq_Value) : bool =
  match (l,r) with
  | ValError s1, ValError s2
  | ValEnumField(_, s1),
    ValEnumField(_, s2) ->
    P4string.eq s1 s2
  | ValSenumField(_, _, v1),
    ValSenumField(_, _, v2)  ->
    interp_beq v1 v2
  | ValBool b1, ValBool b2 ->
    Poly.(b1 = b2)
  | ValBit(_, n1), ValBit(_, n2)
  | ValInteger n1, ValInteger n2
  | ValInt(_, n1), ValInt(_, n2) ->
    Bigint.(n1 = n2)
  | ValBit(w,n1), ValInteger n2 -> interp_beq l (bit_of_rawint n2 w)
  | ValInteger n1, ValBit(w,n2) -> interp_beq (bit_of_rawint n1 w) r
  | ValInt (w,n1), ValInteger n2 -> interp_beq l (int_of_rawint n2 w)
  | ValInteger n1, ValInt(w,n2) -> interp_beq (int_of_rawint n1 w) r
  | ValStruct l1,
    ValStruct l2 ->
    structs_equal l1 l2
  | ValHeader (l1, b1),
    ValHeader (l2, b2) ->
    headers_equal l1 l2 b1 b2
  | ValTuple l1,
    ValTuple l2 ->
    tuples_equal l1 l2
  | _ -> failwith "equality comparison undefined for given types"

and structs_equal (l1 : (P4string.t * coq_Value) list)
(l2 : (P4string.t * coq_Value) list) : bool =
  let f (a : (P4string.t * coq_Value) list) (b : P4string.t * coq_Value) =
    if List.Assoc.mem a ~equal:P4string.eq (fst b)
    then a
    else b :: a in
  let l1' = List.fold_left l1 ~init:[] ~f:f in
  let l2' = List.fold_left l2 ~init:[] ~f:f in
  let g (a,b) =
    let h = (fun (x,y) -> P4string.eq x a && interp_beq y b) in
    List.exists l2' ~f:h in
  List.for_all l1' ~f:g

and headers_equal (l1 : (P4string.t * coq_Value) list)
    (l2 : (P4string.t * coq_Value) list) (b1 : bool) (b2 : bool) : bool =
  let a = not b1 && not b2 in
  let b = b1 && b2 && structs_equal l1 l2 in
  a || b

and stacks_equal (l1 : coq_Value list) (l2 : coq_Value list) : bool =
  let f = (fun i a -> a |> interp_beq (List.nth_exn l2 i)) in
  let b = List.for_alli l1 ~f:f in
  b

and unions_equal l1 l2 : bool =
  structs_equal l1 l2

and tuples_equal (l1 : coq_Value list) (l2 : coq_Value list) : bool =
  let f acc v1 v2 =
    let b = interp_beq v1 v2 in
    acc && b in
  match List.fold2 ~init:true ~f l1 l2 with
  | Ok b -> b
  | Unequal_lengths -> false

let interp_bne (l : coq_Value) (r : coq_Value) : bool =
  not (interp_beq l r)

let rec interp_bitwise_and (l : coq_Value) (r : coq_Value) : coq_Value =
  match (l,r) with
  | ValBit(w, v1), ValBit(_, v2) -> ValBit(w,Bigint.bit_and v1 v2)
  | ValBit(w, v1), ValInteger n   -> interp_bitwise_and l (bit_of_rawint n w)
  | ValInteger n, ValBit(w, v2)   -> interp_bitwise_and (bit_of_rawint n w) r
  | _ -> failwith "bitwise and only defined on fixed width ints"

let rec interp_bitwise_xor (l : coq_Value) (r : coq_Value) : coq_Value =
  match (l,r) with
  | ValBit(w, v1), ValBit(_, v2) -> ValBit(w, Bigint.bit_xor v1 v2)
  | ValBit(w, v1), ValInteger n   -> interp_bitwise_xor l (bit_of_rawint n w)
  | ValInteger n,   ValBit(w, v2) -> interp_bitwise_xor (bit_of_rawint n w) r
  | _ -> failwith "bitwise xor only defined on fixed width ints"

let rec interp_bitwise_or (l : coq_Value) (r : coq_Value) : coq_Value =
  match (l,r) with
  | ValBit(w, v1), ValBit(_, v2) -> ValBit(w, Bigint.bit_or v1 v2)
  | ValBit(w, v1), ValInteger n   -> interp_bitwise_or l (bit_of_rawint n w)
  | ValInteger n, ValBit(w, v2)   -> interp_bitwise_or (bit_of_rawint n w) r
  | _ -> failwith "bitwise or only defined on fixed width ints"

let rec interp_concat (l : coq_Value) (r : coq_Value) : coq_Value =
  match (l,r) with
  | ValBit(w1, v1), ValBit(w2, v2) ->
     ValBit (w1+w2, Bigint.(shift_bitstring_left v1 (of_int w2) + v2))
  | ValBit(w, v),  ValInteger n -> interp_concat l (bit_of_rawint n w)
  | ValInteger n, ValBit(w, v)  -> interp_concat (bit_of_rawint n w) r
  | _ -> failwith "concat operator only defined on unsigned ints"

let interp_band (l : coq_Value) (r : coq_Value) : coq_Value =
  match (l,r) with
  | ValBool b1, ValBool b2 -> ValBool(b1 && b2)
  | _ -> failwith "and operator only defined on bools"

let interp_bor (l : coq_Value) (r : coq_Value) : coq_Value =
  match (l,r) with
  | ValBool b1, ValBool b2 -> ValBool(b1 || b2)
  | _ -> failwith "or operator only defined on bools"

let bitwise_op_of_signeds (op : Bigint.t -> Bigint.t -> Bigint.t)
(v1 : Bigint.t) (v2 : Bigint.t) (w : int) : coq_Value =
  let w' = Bigint.of_int w in
  let v1' = of_twos_complement v1 w' in
  let v2' = of_twos_complement v2 w' in
  let n = op v1' v2' in
  ValBit (w, to_twos_complement n w')

let interp_binary_op (op: coq_OpBin) (l: coq_Value) (r: coq_Value) =
  match op with
  | Plus     -> interp_bplus l r
  | PlusSat  -> interp_bplus_sat l r
  | Minus    -> interp_bminus l r
  | MinusSat -> interp_bminus_sat l r
  | Mul      -> interp_bmult l r
  | Div      -> interp_bdiv l r
  | Mod      -> interp_bmod l r
  | Shl      -> interp_bshl l r
  | Shr      -> interp_bshr l r
  | Le       -> interp_ble l r
  | Ge       -> interp_bge l r
  | Lt       -> interp_blt l r
  | Gt       -> interp_bgt l r
  | Eq       -> ValBool (interp_beq l r)
  | NotEq    -> ValBool (interp_bne l r)
  | BitAnd   -> interp_bitwise_and l r
  | BitXor   -> interp_bitwise_xor l r
  | BitOr    -> interp_bitwise_or l r
  | PlusPlus -> interp_concat l r
  | And      -> interp_band l r
  | Or       -> interp_bor l r


let interp_unary_op (op: coq_OpUni) (v: coq_Value) =
  match op with
  | Not    -> eval_not v
  | BitNot -> eval_bitnot v
  | UMinus -> eval_uminus v

(*----------------------------------------------------------------------------*)
(* Cast evaluation                                                            *)
(*----------------------------------------------------------------------------*)

let bool_of_val (v : coq_Value) : coq_Value =
  match v with
  | ValBit (w,n) when w = 1 -> ValBool Bigint.(n = one)
  | _ -> failwith "cast to bool undefined"

let rec bit_of_val (width : int) (v : coq_Value) : coq_Value =
  match v with
  | ValInt(_, n)
  | ValBit(_, n)
  | ValInteger n -> bit_of_rawint n width
  | ValBool b -> ValBit (width, if b then Bigint.one else Bigint.zero)
  | ValSenumField(_, _, v) -> bit_of_val width v
  | _ -> failwith "cast to bitstring undefined"

let rec int_of_val (width : int) (v : coq_Value) : coq_Value =
  match v with
  | ValBit(_, n)
  | ValInt(_, n)
  | ValInteger n -> int_of_rawint n width
  | ValSenumField(_, _, v) -> int_of_val width v
  | _ -> failwith "cast to bitstring undefined"

let fields_for_cast (fields: P4light.coq_FieldType list) (value: coq_Value) =
  match value with
  | ValTuple vals ->
     let fields_vals = List.zip_exn fields vals in
     List.map ~f:(fun ((f, _), v) -> f, v) fields_vals
  | ValRecord fields -> fields
  | _ -> failwith "cannot cast"

let rec interp_cast ~type_lookup:(type_lookup: P4name.t -> P4light.coq_P4Type)
      (new_type: coq_P4Type) (value: coq_Value) : coq_Value =
  match new_type with
  | TypBool -> bool_of_val value
  | TypBit width -> bit_of_val (Bigint.to_int_exn width) value
  | TypInt width -> int_of_val (Bigint.to_int_exn width) value
  | TypNewType (name, typ) -> interp_cast ~type_lookup typ value
  | TypTypeName n -> interp_cast ~type_lookup (type_lookup n) value
  | TypHeader fields -> ValHeader (fields_for_cast fields value, true)
  | TypStruct fields -> ValStruct (fields_for_cast fields value)
  | TypTuple types ->
    begin match value with
      | ValTuple v -> value
      | _ -> failwith "cannot cast"
    end
  | _ -> failwith "cast unimplemented"
