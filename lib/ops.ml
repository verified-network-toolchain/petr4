open Core_kernel
open Typed
open Prog
open Bitstring

(*----------------------------------------------------------------------------*)
(* Unary Operator Evaluation *)
(*----------------------------------------------------------------------------*)

let eval_not (v : coq_ValueBase) : coq_ValueBase =
  match v with
  | ValBaseBool b -> ValBaseBool (not b)
  | _ -> failwith "not operator can only be applied to bools"

let eval_bitnot (v : coq_ValueBase) : coq_ValueBase =
  match v with
  | ValBaseBit (w, n) -> ValBaseBit (w, bitwise_neg_of_bigint n (Bigint.of_int w))
  | _ -> failwith "bitwise complement on non-fixed width unsigned bitstring"

and eval_uminus (v : coq_ValueBase) : coq_ValueBase =
  match v with
  | ValBaseBit (w, n) -> Bigint.(ValBaseBit (w, (power_of_two (of_int w)) - n))
  | ValBaseInt (w, n) -> Bigint.(ValBaseInt (w, to_twos_complement (-n) (of_int w)))
  | ValBaseInteger n -> ValBaseInteger (Bigint.neg n)
  | _ -> failwith "unary minus on non-int type"

(*----------------------------------------------------------------------------*)
(* binary operator interpretation *)
(*----------------------------------------------------------------------------*)

let unsigned_op_sat (l : Bigint.t) (r : Bigint.t) (w : int)
(op : Bigint.t -> Bigint.t -> Bigint.t) : coq_ValueBase =
  let x = power_of_two (Bigint.of_int w) in
  let n = op l r in
  let n' =
    if Bigint.(n > zero)
    then Bigint.min n Bigint.(x - one)
    else Bigint.max n Bigint.zero in
  ValBaseBit (w, n')

let signed_op_sat (l : Bigint.t) (r : Bigint.t) (w : int)
(op : Bigint.t -> Bigint.t -> Bigint.t) : coq_ValueBase =
  let x = power_of_two Bigint.(of_int w - one) in
  let n = op l r in
  let n' =
    if Bigint.(n > zero)
    then Bigint.min n Bigint.(x - one)
    else Bigint.max n Bigint.(-x) in
  ValBaseInt (w, n')

let rec interp_bplus (l : coq_ValueBase) (r : coq_ValueBase) : coq_ValueBase =
  match (l,r) with
  | ValBaseBit (w, v1), ValBaseBit (_, v2) ->
    let v = Bigint.(of_twos_complement (v1 + v2) (of_int w)) in
    ValBaseBit(w, v) 
  | ValBaseInt (w, v1), ValBaseInt (_, v2) ->
    let v = Bigint.(to_twos_complement (v1 + v2) (of_int w)) in
    ValBaseInt(w, v)
  | ValBaseBit (w, v1), ValBaseInteger n   -> interp_bplus l (bit_of_rawint n w)
  | ValBaseInteger n,   ValBaseBit (w, v1) -> interp_bplus (bit_of_rawint n w) r
  | ValBaseInt (w, v1), ValBaseInteger n   -> interp_bplus l (int_of_rawint n w)
  | ValBaseInteger n,   ValBaseInt (w, v1) -> interp_bplus (int_of_rawint n w) r
  | ValBaseInteger n1,  ValBaseInteger n2  -> ValBaseInteger Bigint.(n1 + n2)
  | _ -> failwith "binary plus operation only defined on ints"

let rec interp_bplus_sat (l : coq_ValueBase) (r : coq_ValueBase) : coq_ValueBase =
  match (l,r) with
  | ValBaseBit(w, v1), ValBaseBit(_, v2) -> unsigned_op_sat v1 v2 w Bigint.(+)
  | ValBaseInt(w, v1), ValBaseInt(_, v2) -> signed_op_sat v1 v2 w Bigint.(+)
  | ValBaseBit(w, v1), ValBaseInteger n   -> interp_bplus_sat l (bit_of_rawint n w)
  | ValBaseInteger n,   ValBaseBit(w, _)    -> interp_bplus_sat (bit_of_rawint n w) r
  | ValBaseInt(w, _),    ValBaseInteger n   -> interp_bplus_sat l (int_of_rawint n w)
  | ValBaseInteger n,   ValBaseInt(w, _)    -> interp_bplus_sat (int_of_rawint n w) r
  | _ -> failwith "binary sat plus operation only definted on fixed-width ints"

let rec interp_bminus (l : coq_ValueBase) (r : coq_ValueBase) : coq_ValueBase =
  match (l,r) with
  | ValBaseBit(w, v1), ValBaseBit(_, v2) ->
    let v = Bigint.(of_twos_complement (v1 - v2) (of_int w)) in
    ValBaseBit(w, v)
  | ValBaseInt(w, v1), ValBaseInt(_, v2) ->
    let v = Bigint.(to_twos_complement (v1 - v2) (of_int w)) in
    ValBaseInt(w, v)
  | ValBaseBit(w, v1), ValBaseInteger n   -> interp_bminus l (bit_of_rawint n w)
  | ValBaseInteger n,   ValBaseBit(w, v1) -> interp_bminus (bit_of_rawint n w) r
  | ValBaseInt(w, v1), ValBaseInteger n   -> interp_bminus l (int_of_rawint n w)
  | ValBaseInteger n,   ValBaseInt(w, v1) -> interp_bminus (int_of_rawint n w) r
  | ValBaseInteger n1,  ValBaseInteger n2  -> ValBaseInteger Bigint.(n1 - n2)
  | _ -> failwith "binary plus operation only defined on ints"

let rec interp_bminus_sat (l : coq_ValueBase) (r : coq_ValueBase) : coq_ValueBase =
  match (l,r) with
  | ValBaseBit(w, v1), ValBaseBit(_, v2) -> unsigned_op_sat v1 v2 w Bigint.(-)
  | ValBaseInt(w, v1), ValBaseInt(_, v2) -> signed_op_sat v1 v2 w Bigint.(-)
  | ValBaseBit(w, v1), ValBaseInteger n   -> interp_bminus_sat l (bit_of_rawint n w)
  | ValBaseInteger n, ValBaseBit(w, _)      -> interp_bminus_sat (bit_of_rawint n w) r
  | ValBaseInt(w, _), ValBaseInteger n      -> interp_bminus_sat l (int_of_rawint n w)
  | ValBaseInteger n, ValBaseInt(w, _)      -> interp_bminus_sat (int_of_rawint n w) r
  | _ -> failwith "binary sat plus operation only definted on fixed-width ints"

let rec interp_bmult (l : coq_ValueBase) (r : coq_ValueBase) : coq_ValueBase =
  match (l,r) with
  | ValBaseBit(w, v1), ValBaseBit(_, v2) ->
    ValBaseBit(w, of_twos_complement Bigint.(v1 * v2) (Bigint.of_int w))
  | ValBaseInt(w, v1), ValBaseInt(_, v2) ->
    ValBaseInt(w, to_twos_complement Bigint.(v1 * v2) (Bigint.of_int w))
  | ValBaseBit(w, v1), ValBaseInteger n   -> interp_bmult l (bit_of_rawint n w)
  | ValBaseInteger n,   ValBaseBit(w, v1) -> interp_bmult (bit_of_rawint n w) r
  | ValBaseInt(w, v1), ValBaseInteger n   -> interp_bmult l (int_of_rawint n w)
  | ValBaseInteger n,   ValBaseInt(w, v1) -> interp_bmult (int_of_rawint n w) r
  | ValBaseInteger n1,  ValBaseInteger n2  -> ValBaseInteger Bigint.(n1 * n2)
  | _ -> failwith "binary mult operation only defined on ints"

let interp_bdiv (l : coq_ValueBase) (r : coq_ValueBase) : coq_ValueBase =
  match (l,r) with
  | ValBaseInteger n1, ValBaseInteger n2     -> ValBaseInteger Bigint.(n1 / n2)
  | ValBaseBit (w, v1), ValBaseBit (_, v2) -> ValBaseBit (w, Bigint.(v1 / v2))
  | _ -> failwith "division only defined on positive values"

let interp_bmod (l : coq_ValueBase) (r : coq_ValueBase) : coq_ValueBase =
  match (l,r) with
  | ValBaseInteger n1, ValBaseInteger n2     -> ValBaseInteger Bigint.(n1 % n2)
  | ValBaseBit (w, v1), ValBaseBit (_, v2) -> ValBaseBit (w, Bigint.(v1 % v2))
  | _ -> failwith "mod only defined on positive values"

let interp_bshl (l : coq_ValueBase) (r : coq_ValueBase) : coq_ValueBase =
  match (l,r) with
  | ValBaseBit(w, v1), ValBaseBit(_, v2)
  | ValBaseBit(w, v1), ValBaseInteger v2 ->
    ValBaseBit(w, of_twos_complement (shift_bitstring_left v1 v2) (Bigint.of_int w))
  | ValBaseInt(w, v1), ValBaseBit(_, v2)
  | ValBaseInt(w, v1), ValBaseInteger v2 ->
    ValBaseInt(w, to_twos_complement (shift_bitstring_left v1 v2) (Bigint.of_int w))
  | ValBaseInteger v1, ValBaseInteger v2  -> ValBaseInteger(shift_bitstring_left v1 v2)
  | ValBaseBit (w, v1), ValBaseInt(_, v2) ->
    ValBaseBit(w, of_twos_complement (shift_bitstring_left v1 v2) (Bigint.of_int w))
  | ValBaseInt (w, v1), ValBaseInt(_, v2) ->
    ValBaseInt(w, to_twos_complement (shift_bitstring_left v1 v2) (Bigint.of_int w))
  | _ -> failwith "shift left operator not defined for these types"

let interp_bshr (l : coq_ValueBase) (r : coq_ValueBase) : coq_ValueBase =
  match (l,r) with
  | ValBaseBit (w, v1), ValBaseBit(_, v2)
  | ValBaseBit(w, v1), ValBaseInteger v2 ->
    ValBaseBit(w, of_twos_complement (shift_bitstring_right v1 v2 false Bigint.zero) (Bigint.of_int w))
  | ValBaseInt(w, v1), ValBaseBit(_, v2)
  | ValBaseInt (w, v1), ValBaseInt(_, v2)
  | ValBaseInt(w, v1), ValBaseInteger v2 ->
    let w' = Bigint.of_int w in
    let v1 = of_twos_complement v1 w' in
    let exp = Bitstring.power_of_two Bigint.(w' - one) in
    let arith = Bigint.(v1 > exp) in
    ValBaseInt(w, to_twos_complement (shift_bitstring_right v1 v2 arith exp) w')
  | ValBaseInteger v1,  ValBaseInteger v2 ->
    ValBaseInteger(shift_bitstring_right v1 v2 false Bigint.zero)
  | ValBaseBit (w, v1), ValBaseInt(_, v2) ->
    ValBaseBit(w, of_twos_complement (shift_bitstring_right v1 v2 false Bigint.zero) (Bigint.of_int w))
  | _ -> failwith "shift right operator not defined for these types"

let rec interp_ble (l : coq_ValueBase) (r : coq_ValueBase) : coq_ValueBase =
  match (l,r) with
  | ValBaseBit(_, v1), ValBaseBit(_, v2)
  | ValBaseInteger v1, ValBaseInteger v2
  | ValBaseInt(_, v1), ValBaseInt(_, v2) -> ValBaseBool Bigint.(v1 <= v2)
  | ValBaseInteger v1, ValBaseBit(w, v2)  -> interp_ble (bit_of_rawint v1 w) r
  | ValBaseBit(w, v1), ValBaseInteger v2  -> interp_ble l (bit_of_rawint v2 w)
  | ValBaseInteger v1, ValBaseInt(w, v2)  -> interp_ble (int_of_rawint v1 w) r
  | ValBaseInt(w, v1), ValBaseInteger v2  -> interp_ble l (int_of_rawint v2 w)
  | _ -> failwith "leq operator only defined on int types"

let rec interp_bge (l : coq_ValueBase) (r : coq_ValueBase) : coq_ValueBase =
  match (l,r) with
  | ValBaseBit(_, v1), ValBaseBit(_, v2)
  | ValBaseInteger v1,  ValBaseInteger v2
  | ValBaseInt(_, v1), ValBaseInt(_, v2) -> ValBaseBool Bigint.(v1 >= v2)
  | ValBaseInteger v1,  ValBaseBit(w, v2) -> interp_bge (bit_of_rawint v1 w) r
  | ValBaseBit(w, v1), ValBaseInteger v2  -> interp_bge l (bit_of_rawint v2 w)
  | ValBaseInteger v1,  ValBaseInt(w, v2) -> interp_bge (int_of_rawint v1 w) r
  | ValBaseInt(w, v1), ValBaseInteger v2  -> interp_bge l (int_of_rawint v2 w)
  | _ -> failwith "geq operator only defined on int types"

let rec interp_blt (l : coq_ValueBase) (r : coq_ValueBase) : coq_ValueBase =
  match (l,r) with
  | ValBaseBit(_, v1), ValBaseBit(_, v2)
  | ValBaseInteger v1, ValBaseInteger v2
  | ValBaseInt(_, v1), ValBaseInt(_, v2) -> ValBaseBool Bigint.(v1 < v2)
  | ValBaseInteger v1, ValBaseBit(w, v2)  -> interp_blt (bit_of_rawint v1 w) r
  | ValBaseBit(w, v1), ValBaseInteger v2  -> interp_blt l (bit_of_rawint v2 w)
  | ValBaseInteger v1, ValBaseInt(w, v2)  -> interp_blt (int_of_rawint v1 w) r
  | ValBaseInt(w, v1), ValBaseInteger v2  -> interp_blt l (int_of_rawint v2 w)
  | _ -> failwith "lt operator only defined on int types"

let rec interp_bgt (l : coq_ValueBase) (r : coq_ValueBase) : coq_ValueBase =
  match (l,r) with
  | ValBaseBit(_, v1), ValBaseBit(_, v2)
  | ValBaseInteger v1,  ValBaseInteger v2
  | ValBaseInt(_, v1), ValBaseInt(_, v2) -> ValBaseBool Bigint.(v1 > v2)
  | ValBaseInteger v1,  ValBaseBit(w, v2) -> interp_bgt (bit_of_rawint v1 w) r
  | ValBaseBit(w, v1), ValBaseInteger v2  -> interp_bgt l (bit_of_rawint v2 w)
  | ValBaseInteger v1,  ValBaseInt(w, v2) -> interp_bgt (int_of_rawint v1 w) r
  | ValBaseInt(w, v1), ValBaseInteger v2  -> interp_bgt l (int_of_rawint v2 w)
  | _ -> failwith "gt operator only defined on int types"

let rec interp_beq (l : coq_ValueBase) (r : coq_ValueBase) : bool =
  match (l,r) with
  | ValBaseError s1, ValBaseError s2
  | ValBaseEnumField(_, s1),
    ValBaseEnumField(_, s2) ->
    P4string.eq s1 s2
  | ValBaseSenumField(_, _, v1),
    ValBaseSenumField(_, _, v2)  ->
    interp_beq v1 v2
  | ValBaseBool b1, ValBaseBool b2 ->
    Poly.(b1 = b2)
  | ValBaseBit(_, n1), ValBaseBit(_, n2)
  | ValBaseInteger n1, ValBaseInteger n2
  | ValBaseInt(_, n1), ValBaseInt(_, n2) ->
    Bigint.(n1 = n2)
  | ValBaseVarbit(_, w1, n1),
    ValBaseVarbit(_, w2, n2) ->
    Bigint.(n1 = n2) && (w1 = w2)
  | ValBaseBit(w,n1), ValBaseInteger n2 -> interp_beq l (bit_of_rawint n2 w)
  | ValBaseInteger n1, ValBaseBit(w,n2) -> interp_beq (bit_of_rawint n1 w) r
  | ValBaseInt (w,n1), ValBaseInteger n2 -> interp_beq l (int_of_rawint n2 w)
  | ValBaseInteger n1, ValBaseInt(w,n2) -> interp_beq (int_of_rawint n1 w) r
  | ValBaseStruct l1,
    ValBaseStruct l2 ->
    structs_equal l1 l2
  | ValBaseHeader (l1, b1),
    ValBaseHeader (l2, b2) ->
    headers_equal l1 l2 b1 b2
  | ValBaseStack (l1, _, _),
    ValBaseStack (l2, _, _) ->
    stacks_equal l1 l2
  | ValBaseUnion l1,
    ValBaseUnion l2 ->
    unions_equal l1 l2
  | ValBaseTuple l1,
    ValBaseTuple l2 ->
    tuples_equal l1 l2
  | ValBaseNull, ValBaseNull -> true
  | ValBaseNull, _
  | _, ValBaseNull -> false
  | _ -> failwith "equality comparison undefined for given types"

and structs_equal (l1 : (P4string.t * coq_ValueBase) list)
(l2 : (P4string.t * coq_ValueBase) list) : bool =
  let f (a : (P4string.t * coq_ValueBase) list) (b : P4string.t * coq_ValueBase) =
    if List.Assoc.mem a ~equal:P4string.eq (fst b)
    then a
    else b :: a in
  let l1' = List.fold_left l1 ~init:[] ~f:f in
  let l2' = List.fold_left l2 ~init:[] ~f:f in
  let g (a,b) =
    let h = (fun (x,y) -> P4string.eq x a && interp_beq y b) in
    List.exists l2' ~f:h in
  List.for_all l1' ~f:g

and headers_equal (l1 : (P4string.t * coq_ValueBase) list)
    (l2 : (P4string.t * coq_ValueBase) list) (b1 : bool) (b2 : bool) : bool =
  let a = not b1 && not b2 in
  let b = b1 && b2 && structs_equal l1 l2 in
  a || b

and stacks_equal (l1 : coq_ValueBase list) (l2 : coq_ValueBase list) : bool =
  let f = (fun i a -> a |> interp_beq (List.nth_exn l2 i)) in
  let b = List.for_alli l1 ~f:f in
  b

and unions_equal l1 l2 : bool =
  structs_equal l1 l2

and tuples_equal (l1 : coq_ValueBase list) (l2 : coq_ValueBase list) : bool =
  let f acc v1 v2 =
    let b = interp_beq v1 v2 in
    acc && b in
  match List.fold2 ~init:true ~f l1 l2 with
  | Ok b -> b
  | Unequal_lengths -> false

let interp_bne (l : coq_ValueBase) (r : coq_ValueBase) : bool =
  not (interp_beq l r)

let rec interp_bitwise_and (l : coq_ValueBase) (r : coq_ValueBase) : coq_ValueBase =
  match (l,r) with
  | ValBaseBit(w, v1), ValBaseBit(_, v2) -> ValBaseBit(w,Bigint.bit_and v1 v2)
  | ValBaseBit(w, v1), ValBaseInteger n   -> interp_bitwise_and l (bit_of_rawint n w)
  | ValBaseInteger n, ValBaseBit(w, v2)   -> interp_bitwise_and (bit_of_rawint n w) r
  | _ -> failwith "bitwise and only defined on fixed width ints"

let rec interp_bitwise_xor (l : coq_ValueBase) (r : coq_ValueBase) : coq_ValueBase =
  match (l,r) with
  | ValBaseBit(w, v1), ValBaseBit(_, v2) -> ValBaseBit(w, Bigint.bit_xor v1 v2)
  | ValBaseBit(w, v1), ValBaseInteger n   -> interp_bitwise_xor l (bit_of_rawint n w)
  | ValBaseInteger n,   ValBaseBit(w, v2) -> interp_bitwise_xor (bit_of_rawint n w) r
  | _ -> failwith "bitwise xor only defined on fixed width ints"

let rec interp_bitwise_or (l : coq_ValueBase) (r : coq_ValueBase) : coq_ValueBase =
  match (l,r) with
  | ValBaseBit(w, v1), ValBaseBit(_, v2) -> ValBaseBit(w, Bigint.bit_or v1 v2)
  | ValBaseBit(w, v1), ValBaseInteger n   -> interp_bitwise_or l (bit_of_rawint n w)
  | ValBaseInteger n, ValBaseBit(w, v2)   -> interp_bitwise_or (bit_of_rawint n w) r
  | _ -> failwith "bitwise or only defined on fixed width ints"

let rec interp_concat (l : coq_ValueBase) (r : coq_ValueBase) : coq_ValueBase =
  match (l,r) with
  | ValBaseBit(w1, v1), ValBaseBit(w2, v2) ->
     ValBaseBit (w1+w2, Bigint.(shift_bitstring_left v1 (of_int w2) + v2))
  | ValBaseBit(w, v),  ValBaseInteger n -> interp_concat l (bit_of_rawint n w)
  | ValBaseInteger n, ValBaseBit(w, v)  -> interp_concat (bit_of_rawint n w) r
  | _ -> failwith "concat operator only defined on unsigned ints"

let interp_band (l : coq_ValueBase) (r : coq_ValueBase) : coq_ValueBase =
  match (l,r) with
  | ValBaseBool b1, ValBaseBool b2 -> ValBaseBool(b1 && b2)
  | _ -> failwith "and operator only defined on bools"

let interp_bor (l : coq_ValueBase) (r : coq_ValueBase) : coq_ValueBase =
  match (l,r) with
  | ValBaseBool b1, ValBaseBool b2 -> ValBaseBool(b1 || b2)
  | _ -> failwith "or operator only defined on bools"

let bitwise_op_of_signeds (op : Bigint.t -> Bigint.t -> Bigint.t)
(v1 : Bigint.t) (v2 : Bigint.t) (w : int) : coq_ValueBase =
  let w' = Bigint.of_int w in
  let v1' = of_twos_complement v1 w' in
  let v2' = of_twos_complement v2 w' in
  let n = op v1' v2' in
  ValBaseBit (w, to_twos_complement n w')

let interp_binary_op (op: coq_OpBin) (l: coq_ValueBase) (r: coq_ValueBase) =
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
  | Eq       -> ValBaseBool (interp_beq l r)
  | NotEq    -> ValBaseBool (interp_bne l r)
  | BitAnd   -> interp_bitwise_and l r
  | BitXor   -> interp_bitwise_xor l r
  | BitOr    -> interp_bitwise_or l r
  | PlusPlus -> interp_concat l r
  | And      -> interp_band l r
  | Or       -> interp_bor l r


let interp_unary_op (op: coq_OpUni) (v: coq_ValueBase) =
  match op with
  | Not    -> eval_not v
  | BitNot -> eval_bitnot v
  | UMinus -> eval_uminus v

(*----------------------------------------------------------------------------*)
(* Cast evaluation                                                            *)
(*----------------------------------------------------------------------------*)

let bool_of_val (v : coq_ValueBase) : coq_ValueBase =
  match v with
  | ValBaseBit (w,n) when w = 1 -> ValBaseBool Bigint.(n = one)
  | _ -> failwith "cast to bool undefined"

let rec bit_of_val (width : int) (v : coq_ValueBase) : coq_ValueBase =
  match v with
  | ValBaseInt(_, n)
  | ValBaseBit(_, n)
  | ValBaseInteger n -> bit_of_rawint n width
  | ValBaseBool b -> ValBaseBit (width, if b then Bigint.one else Bigint.zero)
  | ValBaseSenumField(_, _, v) -> bit_of_val width v
  | _ -> failwith "cast to bitstring undefined"

let rec int_of_val (width : int) (v : coq_ValueBase) : coq_ValueBase =
  match v with
  | ValBaseBit(_, n)
  | ValBaseInt(_, n)
  | ValBaseInteger n -> int_of_rawint n width
  | ValBaseSenumField(_, _, v) -> int_of_val width v
  | _ -> failwith "cast to bitstring undefined"

let fields_for_cast (fields: Typed.coq_FieldType list) (value: coq_ValueBase) =
  match value with
  | ValBaseTuple vals ->
     let fields_vals = List.zip_exn fields vals in
     List.map ~f:(fun ((MkFieldType (f, _)), v) -> f, v) fields_vals
  | ValBaseRecord fields -> fields
  | _ -> failwith "cannot cast"

let rec interp_cast ~type_lookup:(type_lookup: P4name.t -> Typed.coq_P4Type)
      (new_type: coq_P4Type) (value: coq_ValueBase) : coq_ValueBase =
  match new_type with
  | TypBool -> bool_of_val value
  | TypBit width -> bit_of_val width value
  | TypInt width -> int_of_val width value
  | TypNewType (name, typ) -> interp_cast ~type_lookup typ value
  | TypTypeName n -> interp_cast ~type_lookup (type_lookup n) value
  | TypHeader fields -> ValBaseHeader (fields_for_cast fields value, true)
  | TypStruct fields -> ValBaseStruct (fields_for_cast fields value)
  | TypTuple types ->
    begin match value with
      | ValBaseTuple v -> value
      | _ -> failwith "cannot cast"
    end
  | TypSet t ->
     begin match value with
     | ValBaseSet v -> ValBaseSet v
     | ValBaseSenumField (_, _, ValBaseBit (w, v))
     | ValBaseSenumField (_, _, ValBaseInt (w, v))
     | ValBaseInt (w, v)
     | ValBaseBit (w, v) -> ValBaseSet (ValSetSingleton (w, v))
     |_ -> failwith "cannot cast"
     end
  | _ -> failwith "cast unimplemented"
