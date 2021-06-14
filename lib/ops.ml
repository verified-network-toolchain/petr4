open Core_kernel
module V = Prog.Value
module Op = Typed.Op
open Bitstring

(*----------------------------------------------------------------------------*)
(* Unary Operator Evaluation *)
(*----------------------------------------------------------------------------*)

let eval_not (v : V.value) : V.value =
  match v with
  | VBool b -> VBool (not b)
  | _ -> failwith "not operator can only be applied to bools"

let eval_bitnot (v : V.value) : V.value =
  match v with
  | VBit{w;v=n} -> VBit{w;v=bitwise_neg_of_bigint n w}
  | _ -> failwith "bitwise complement on non-fixed width unsigned bitstring"

and eval_uminus (v : V.value) : V.value =
  match v with
  | VBit{w;v=n}  -> Bigint.(VBit{w;v=(power_of_two w) - n})
  | VInt{w;v=n}  -> Bigint.(VInt{w;v=to_twos_complement (-n) w})
  | VInteger n -> VInteger (Bigint.neg n)
  | _ -> failwith "unary minus on non-int type"

(*----------------------------------------------------------------------------*)
(* binary operator interpuation *)
(*----------------------------------------------------------------------------*)

let unsigned_op_sat (l : Bigint.t) (r : Bigint.t) (w : Bigint.t)
(op : Bigint.t -> Bigint.t -> Bigint.t) : V.value =
  let x = power_of_two w in
  let n = op l r in
  let n' =
    if Bigint.(n > zero)
    then Bigint.min n Bigint.(x - one)
    else Bigint.max n Bigint.zero in
  VBit{w;v=n'}

let signed_op_sat (l : Bigint.t) (r : Bigint.t) (w : Bigint.t)
(op : Bigint.t -> Bigint.t -> Bigint.t) : V.value =
  let x = power_of_two Bigint.(w-one) in
  let n = op l r in
  let n' =
    if Bigint.(n > zero)
    then Bigint.min n Bigint.(x - one)
    else Bigint.max n Bigint.(-x) in
  VInt{w;v=n'}

let rec interp_bplus (l : V.value) (r : V.value) : V.value =
  match (l,r) with
  | VBit{w;v=v1}, VBit{v=v2;_} -> VBit{w;v=of_twos_complement Bigint.(v1 + v2) w}
  | VInt{w;v=v1}, VInt{v=v2;_} -> VInt{w;v=to_twos_complement Bigint.(v1 + v2) w}
  | VBit{w;v=v1}, VInteger n   -> interp_bplus l (bit_of_rawint n w)
  | VInteger n,   VBit{w;v=v1} -> interp_bplus (bit_of_rawint n w) r
  | VInt{w;v=v1}, VInteger n   -> interp_bplus l (int_of_rawint n w)
  | VInteger n,   VInt{w;v=v1} -> interp_bplus (int_of_rawint n w) r
  | VInteger n1,  VInteger n2  -> VInteger Bigint.(n1 + n2)
  | _ -> raise_s [%message "binary plus operation only defined on ints"
                     ~l:(l: V.value) (r: V.value)]

let rec interp_bplus_sat (l : V.value) (r : V.value) : V.value =
  match (l,r) with
  | VBit{w;v=v1}, VBit{v=v2;_} -> unsigned_op_sat v1 v2 w Bigint.(+)
  | VInt{w;v=v1}, VInt{v=v2;_} -> signed_op_sat v1 v2 w Bigint.(+)
  | VBit{w;v=v1}, VInteger n   -> interp_bplus_sat l (bit_of_rawint n w)
  | VInteger n,   VBit{w;_}    -> interp_bplus_sat (bit_of_rawint n w) r
  | VInt{w;_},    VInteger n   -> interp_bplus_sat l (int_of_rawint n w)
  | VInteger n,   VInt{w;_}    -> interp_bplus_sat (int_of_rawint n w) r
  | _ -> failwith "binary sat plus operation only definted on fixed-width ints"

let rec interp_bminus (l : V.value) (r : V.value) : V.value =
  match (l,r) with
  | VBit{w;v=v1}, VBit{v=v2;_} -> VBit{w;v=of_twos_complement Bigint.(v1 - v2) w}
  | VInt{w;v=v1}, VInt{v=v2;_} -> VInt{w;v=to_twos_complement Bigint.(v1 - v2) w}
  | VBit{w;v=v1}, VInteger n   -> interp_bminus l (bit_of_rawint n w)
  | VInteger n,   VBit{w;v=v1} -> interp_bminus (bit_of_rawint n w) r
  | VInt{w;v=v1}, VInteger n   -> interp_bminus l (int_of_rawint n w)
  | VInteger n,   VInt{w;v=v1} -> interp_bminus (int_of_rawint n w) r
  | VInteger n1,  VInteger n2  -> VInteger Bigint.(n1 - n2)
  | _ -> failwith "binary plus operation only defined on ints"

let rec interp_bminus_sat (l : V.value) (r : V.value) : V.value =
  match (l,r) with
  | VBit{w;v=v1}, VBit{v=v2;_} -> unsigned_op_sat v1 v2 w Bigint.(-)
  | VInt{w;v=v1}, VInt{v=v2;_} -> signed_op_sat v1 v2 w Bigint.(-)
  | VBit{w;v=v1}, VInteger n   -> interp_bminus_sat l (bit_of_rawint n w)
  | VInteger n, VBit{w;_}      -> interp_bminus_sat (bit_of_rawint n w) r
  | VInt{w;_}, VInteger n      -> interp_bminus_sat l (int_of_rawint n w)
  | VInteger n, VInt{w;_}      -> interp_bminus_sat (int_of_rawint n w) r
  | _ -> failwith "binary sat plus operation only definted on fixed-width ints"

let rec interp_bmult (l : V.value) (r : V.value) : V.value =
  match (l,r) with
  | VBit{w;v=v1}, VBit{v=v2;_} -> VBit{w;v=of_twos_complement Bigint.(v1 * v2) w}
  | VInt{w;v=v1}, VInt{v=v2;_} -> VInt{w;v=to_twos_complement Bigint.(v1 * v2) w}
  | VBit{w;v=v1}, VInteger n   -> interp_bmult l (bit_of_rawint n w)
  | VInteger n,   VBit{w;v=v1} -> interp_bmult (bit_of_rawint n w) r
  | VInt{w;v=v1}, VInteger n   -> interp_bmult l (int_of_rawint n w)
  | VInteger n,   VInt{w;v=v1} -> interp_bmult (int_of_rawint n w) r
  | VInteger n1,  VInteger n2  -> VInteger Bigint.(n1 * n2)
  | _ -> failwith "binary mult operation only defined on ints"

let interp_bdiv (l : V.value) (r : V.value) : V.value =
  match (l,r) with
  | VInteger n1, VInteger n2     -> VInteger Bigint.(n1 / n2)
  | VBit {w;v=v1}, VBit {v=v2;_} -> VBit {w;v=Bigint.(v1 / v2)}
  | _ -> failwith "division only defined on positive values"

let interp_bmod (l : V.value) (r : V.value) : V.value =
  match (l,r) with
  | VInteger n1, VInteger n2     -> VInteger Bigint.(n1 % n2)
  | VBit {w;v=v1}, VBit {v=v2;_} -> VBit {w;v=Bigint.(v1 % v2)}
  | _ -> failwith "mod only defined on positive values"

let interp_bshl (l : V.value) (r : V.value) : V.value =
  match (l,r) with
  | VBit{w;v=v1}, VBit{v=v2;_}
  | VBit{w;v=v1}, VInteger v2 -> VBit{w;v=of_twos_complement (shift_bitstring_left v1 v2) w}
  | VInt{w;v=v1}, VBit{v=v2;_}
  | VInt{w;v=v1}, VInteger v2 -> VInt{w;v=to_twos_complement (shift_bitstring_left v1 v2) w}
  | VInteger v1, VInteger v2  -> VInteger(shift_bitstring_left v1 v2)
  | VBit {w;v=v1}, VInt{v=v2;_} -> VBit{w;v=of_twos_complement (shift_bitstring_left v1 v2) w} (* TODO *)
  | VInt {w;v=v1}, VInt{v=v2;_} -> VInt{w;v=to_twos_complement (shift_bitstring_left v1 v2) w} (* TODO *)
  | _ -> failwith "shift left operator not defined for these types"

let interp_bshr (l : V.value) (r : V.value) : V.value =
  match (l,r) with
  | VBit{w;v=v1}, VBit{v=v2;_}
  | VBit{w;v=v1}, VInteger v2 ->
    VBit{w;v=of_twos_complement (shift_bitstring_right v1 v2 false Bigint.zero) w}
  | VInt{w;v=v1}, VBit{v=v2;_}
  | VInt {w;v=v1}, VInt{v=v2;_}
  | VInt{w;v=v1}, VInteger v2 ->
    let v1 = of_twos_complement v1 w in
    let exp = Bitstring.power_of_two Bigint.(w-one) in
    let arith = Bigint.(v1 > exp) in
    VInt{w;v=to_twos_complement (shift_bitstring_right v1 v2 arith exp) w}
  | VInteger v1,  VBit{v=v2; _}
  | VInteger v1,  VInt{v=v2; _}
  | VInteger v1,  VInteger v2 ->
    VInteger(shift_bitstring_right v1 v2 false Bigint.zero)
  | VBit {w;v=v1}, VInt{v=v2;_} ->
    VBit{w;v=of_twos_complement (shift_bitstring_right v1 v2 false Bigint.zero) w}
  | _ -> failwith "shift right operator not defined for these types"

let rec interp_ble (l : V.value) (r : V.value) : V.value =
  match (l,r) with
  | VBit{v=v1;_}, VBit{v=v2;_}
  | VInteger v1, VInteger v2
  | VInt{v=v1;_}, VInt{v=v2;_} -> VBool Bigint.(v1 <= v2)
  | VInteger v1, VBit{w;v=v2}  -> interp_ble (bit_of_rawint v1 w) r
  | VBit{w;v=v1}, VInteger v2  -> interp_ble l (bit_of_rawint v2 w)
  | VInteger v1, VInt{w;v=v2}  -> interp_ble (int_of_rawint v1 w) r
  | VInt{w;v=v1}, VInteger v2  -> interp_ble l (int_of_rawint v2 w)
  | _ -> failwith "leq operator only defined on int types"

let rec interp_bge (l : V.value) (r : V.value) : V.value =
  match (l,r) with
  | VBit{v=v1;_}, VBit{v=v2;_}
  | VInteger v1,  VInteger v2
  | VInt{v=v1;_}, VInt{v=v2;_} -> VBool Bigint.(v1 >= v2)
  | VInteger v1,  VBit{w;v=v2} -> interp_bge (bit_of_rawint v1 w) r
  | VBit{w;v=v1}, VInteger v2  -> interp_bge l (bit_of_rawint v2 w)
  | VInteger v1,  VInt{w;v=v2} -> interp_bge (int_of_rawint v1 w) r
  | VInt{w;v=v1}, VInteger v2  -> interp_bge l (int_of_rawint v2 w)
  | _ -> failwith "geq operator only defined on int types"

let rec interp_blt (l : V.value) (r : V.value) : V.value =
  match (l,r) with
  | VBit{v=v1;_}, VBit{v=v2;_}
  | VInteger v1, VInteger v2
  | VInt{v=v1;_}, VInt{v=v2;_} -> VBool Bigint.(v1 < v2)
  | VInteger v1, VBit{w;v=v2}  -> interp_blt (bit_of_rawint v1 w) r
  | VBit{w;v=v1}, VInteger v2  -> interp_blt l (bit_of_rawint v2 w)
  | VInteger v1, VInt{w;v=v2}  -> interp_blt (int_of_rawint v1 w) r
  | VInt{w;v=v1}, VInteger v2  -> interp_blt l (int_of_rawint v2 w)
  | _ -> failwith "lt operator only defined on int types"

let rec interp_bgt (l : V.value) (r : V.value) : V.value =
  match (l,r) with
  | VBit{v=v1;_}, VBit{v=v2;_}
  | VInteger v1,  VInteger v2
  | VInt{v=v1;_}, VInt{v=v2;_} -> VBool Bigint.(v1 > v2)
  | VInteger v1,  VBit{w;v=v2} -> interp_bgt (bit_of_rawint v1 w) r
  | VBit{w;v=v1}, VInteger v2  -> interp_bgt l (bit_of_rawint v2 w)
  | VInteger v1,  VInt{w;v=v2} -> interp_bgt (int_of_rawint v1 w) r
  | VInt{w;v=v1}, VInteger v2  -> interp_bgt l (int_of_rawint v2 w)
  | _ -> failwith "gt operator only defined on int types"

let rec interp_beq (l : V.value) (r : V.value) : V.value =
  match (l,r) with
  | VError s1, VError s2
  | VEnumField{enum_name=s1;_},
    VEnumField{enum_name=s2;_}                -> VBool Poly.(s1 = s2)
  | VSenumField{v=v1;_},
    VSenumField{v=v2;_}                       -> interp_beq v1 v2
  | VBool b1, VBool b2                        -> VBool Poly.(b1 = b2)
  | VBit{v=n1;_}, VBit{v=n2;_}
  | VInteger n1, VInteger n2
  | VInt{v=n1;_}, VInt{v=n2;_}                -> VBool Bigint.(n1 = n2)
  | VVarbit{w=w1;v=n1;_},
    VVarbit{w=w2;v=n2;_}                      -> VBool(Bigint.(n1 = n2 && w1 = w2))
  | VBit{w;v=n1}, VInteger n2                 -> interp_beq l (bit_of_rawint n2 w)
  | VInteger n1, VBit{w;v=n2}                 -> interp_beq (bit_of_rawint n1 w) r
  | VInt{w;v=n1}, VInteger n2                 -> interp_beq l (int_of_rawint n2 w)
  | VInteger n1, VInt{w;v=n2}                 -> interp_beq (int_of_rawint n1 w) r
  | VStruct{fields=l1;_},
    VStruct{fields=l2;_}                      -> structs_equal l1 l2
  | VHeader{fields=l1;is_valid=b1;_},
    VHeader{fields=l2;is_valid=b2;_}          -> headers_equal l1 l2 b1 b2
  | VStack{headers=l1;_},
    VStack{headers=l2;_}                      -> stacks_equal l1 l2
  | VUnion{fields=l1},
    VUnion{fields=l2}                         -> unions_equal l1 l2
  | VTuple l1, VTuple l2                      -> tuples_equal l1 l2
  | VNull, VNull -> VBool true
  | VNull, _
  | _, VNull -> VBool false
  | _ -> raise_s [%message "equality comparison undefined for given types"
                     ~l:(l:V.value) ~r:(r:V.value)]

and structs_equal (l1 : (string * V.value) list)
(l2 : (string * V.value) list) : V.value =
  let f (a : (string * V.value) list) (b : string * V.value) =
    if List.Assoc.mem a ~equal:String.equal (fst b)
    then a
    else b :: a in
  let l1' = List.fold_left l1 ~init:[] ~f:f in
  let l2' = List.fold_left l2 ~init:[] ~f:f in
  let g (a,b) =
    let h = (fun (x,y) -> String.equal x a && V.assert_bool (interp_beq y b)) in
    List.exists l2' ~f:h in
  let b = List.for_all l1' ~f:g in
  VBool b

and headers_equal (l1 : (string * V.value) list)
    (l2 : (string * V.value) list) (b1 : bool) (b2 : bool) : V.value =
  let a = (not b1 && not b2) in
  let b = (b1 && b2 && V.assert_bool (structs_equal l1 l2)) in
  VBool (a || b)

and stacks_equal (l1 : V.value list) (l2 : V.value list) : V.value =
  let f = (fun i a -> a |> interp_beq (List.nth_exn l2 i) |> V.assert_bool) in
  let b = List.for_alli l1 ~f:f in
  VBool b

and unions_equal (l1 : (string * V.value) list) (l2 : (string * V.value) list) : V.value =
  VBool (V.assert_bool (structs_equal l1 l2))

and tuples_equal (l1 : V.value list) (l2 : V.value list) : V.value =
  let f acc v1 v2 =
    let b = interp_beq v1 v2 in
    V.VBool (acc |> V.assert_bool && b |> V.assert_bool) in
  match List.fold2 ~init:(V.VBool true) ~f l1 l2 with
  | Ok b -> b
  | Unequal_lengths -> V.VBool false

let interp_bne (l : V.value) (r : V.value) : V.value =
  interp_beq l r |> V.assert_bool |> not |> VBool

let rec interp_bitwise_and (l : V.value) (r : V.value) : V.value =
  match (l,r) with
  | VBit{w;v=v1}, VBit{v=v2;_} -> VBit{w;v=Bigint.bit_and v1 v2}
  | VBit{w;v=v1}, VInteger n   -> interp_bitwise_and l (bit_of_rawint n w)
  | VInteger n, VBit{w;v=v2}   -> interp_bitwise_and (bit_of_rawint n w) r
  | _ -> failwith "bitwise and only defined on fixed width ints"

let rec interp_bitwise_xor (l : V.value) (r : V.value) : V.value =
  match (l,r) with
  | VBit{w;v=v1}, VBit{v=v2;_} -> VBit{w;v=Bigint.bit_xor v1 v2}
  | VBit{w;v=v1}, VInteger n   -> interp_bitwise_xor l (bit_of_rawint n w)
  | VInteger n,   VBit{w;v=v2} -> interp_bitwise_xor (bit_of_rawint n w) r
  | _ -> failwith "bitwise xor only defined on fixed width ints"

let rec interp_bitwise_or (l : V.value) (r : V.value) : V.value =
  match (l,r) with
  | VBit{w;v=v1}, VBit{v=v2;_} -> VBit{w;v=Bigint.bit_or v1 v2}
  | VBit{w;v=v1}, VInteger n   -> interp_bitwise_or l (bit_of_rawint n w)
  | VInteger n, VBit{w;v=v2}   -> interp_bitwise_or (bit_of_rawint n w) r
  | _ -> failwith "bitwise or only defined on fixed width ints"

let rec interp_concat (l : V.value) (r : V.value) : V.value =
  match (l,r) with
  | VBit{w=w1;v=v1}, VBit{w=w2;v=v2} ->
     VBit{w=Bigint.(w1+w2);v=Bigint.(shift_bitstring_left v1 w2 + v2)}
  | VBit{w;v},  VInteger n -> interp_concat l (bit_of_rawint n w)
  | VInteger n, VBit{w;v}  -> interp_concat (bit_of_rawint n w) r
  | _ -> failwith "concat operator only defined on unsigned ints"

let interp_band (l : V.value) (r : V.value) : V.value =
  match (l,r) with
  | VBool b1, VBool b2 -> VBool(b1 && b2)
  | _ -> failwith "and operator only defined on bools"

let interp_bor (l : V.value) (r : V.value) : V.value =
  match (l,r) with
  | VBool b1, VBool b2 -> VBool(b1 || b2)
  | _ -> failwith "or operator only defined on bools"

let bitwise_op_of_signeds (op : Bigint.t -> Bigint.t -> Bigint.t)
(v1 : Bigint.t) (v2 : Bigint.t) (w : Bigint.t) : V.value =
  let v1' = of_twos_complement v1 w in
  let v2' = of_twos_complement v2 w in
  let n = op v1' v2' in
  VBit{w;v=to_twos_complement n w}

let interp_binary_op (op: Op.bin) (l: V.value) (r: V.value) =
  match snd op with
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
  | Eq       -> interp_beq l r
  | NotEq    -> interp_bne l r
  | BitAnd   -> interp_bitwise_and l r
  | BitXor   -> interp_bitwise_xor l r
  | BitOr    -> interp_bitwise_or l r
  | PlusPlus -> interp_concat l r
  | And      -> interp_band l r
  | Or       -> interp_bor l r


let interp_unary_op (op: Op.uni) (v: V.value) =
  match snd op with
  | Not    -> eval_not v
  | BitNot -> eval_bitnot v
  | UMinus -> eval_uminus v

(*----------------------------------------------------------------------------*)
(* Cast evaluation                                                            *)
(*----------------------------------------------------------------------------*)

let bool_of_val (v : V.value) : V.value =
  match v with
  | VBit{w;v=n} when Bigint.(w = one) -> VBool Bigint.(n = one)
  | _ -> failwith "cast to bool undefined"

let rec bit_of_val (width : int) (v : V.value) : V.value =
  let w = Bigint.of_int width in
  match v with
  | VInt{v=n;_}
  | VBit{v=n;_}
  | VInteger n -> bit_of_rawint n w
  | VBool b -> VBit{v=if b then Bigint.one else Bigint.zero; w=w;}
  | VSenumField{v;_} -> bit_of_val width v
  | _ -> failwith "cast to bitstring undefined"

let rec int_of_val (width : int) (v : V.value) : V.value =
  let w = Bigint.of_int width in
  match v with
  | VBit{v=n;_}
  | VInt{v=n;_}
  | VInteger n -> int_of_rawint n w
  | VSenumField{v;_} -> int_of_val width v
  | _ -> failwith "cast to bitstring undefined"

let fields_for_cast (fields: Typed.RecordType.field list) (value: V.value) =
  match value with
  | VTuple vals ->
     let fields_vals = List.zip_exn fields vals in
     List.map ~f:(fun (f, v) -> f.name, v) fields_vals
  | VRecord fields -> fields
  | _ -> raise_s [%message "cannot cast" ~value:(value:V.value)]


let rec interp_cast ~type_lookup:(type_lookup: Types.name -> Typed.Type.t)
      (new_type: Typed.Type.t) (value: V.value) : V.value =
  match new_type with
  | Bool -> bool_of_val value
  | Bit{width} -> bit_of_val width value
  | Int{width} -> int_of_val width value
  | NewType nt -> interp_cast ~type_lookup nt.typ value
  | TypeName n -> interp_cast ~type_lookup (type_lookup n) value
  | Header {fields} -> VHeader {is_valid = true;
                                fields = fields_for_cast fields value}
  | Struct {fields} -> VStruct {fields = fields_for_cast fields value}
  | Tuple types -> begin match value with
                   | VTuple v -> VTuple v
                   | _ -> failwith "cannot cast"
                   end
  | Set t ->
     begin match value with
     | VSet v -> VSet v
     | VSenumField {v = VBit {w; v}; _}
     | VSenumField {v = VInt {w; v}; _}
     | VInt {w; v}
     | VBit {w; v} -> VSet (SSingleton {w; v})
     |_ -> raise_s [%message "cannot cast" ~value:(value:V.value) ~t:(t:Typed.Type.t)]
     end
  | _ -> raise_s [%message "cast unimplemented" ~value:(value:V.value) ~t:(new_type:Typed.Type.t)]
