open Core_kernel
module V = Prog.Value
module Op = Typed.Op
open Bitstring
open Target

(*----------------------------------------------------------------------------*)
(* Unary Operator Evaluation *)
(*----------------------------------------------------------------------------*)

let rec eval_not (st : 'a State.t) (v : V.value) : V.value =
  match v with
  | VBool b -> VBool (not b)
  | VLoc l  -> st |> State.find_heap l |> eval_not st
  | _ -> failwith "not operator can only be applied to bools"

let rec eval_bitnot (st : 'a State.t) (v : V.value) : V.value =
  match v with
  | VBit{w;v=n} -> VBit{w;v=bitwise_neg_of_bigint n w}
  | VLoc l  -> st |> State.find_heap l |> eval_bitnot st
  | _ -> failwith "bitwise complement on non-fixed width unsigned bitstring"

and eval_uminus (st : 'a State.t) (v : V.value) : V.value =
  match v with
  | VBit{w;v=n}  -> Bigint.(VBit{w;v=(power_of_two w) - n})
  | VInt{w;v=n}  -> Bigint.(VInt{w;v=to_twos_complement (-n) w})
  | VInteger n -> VInteger (Bigint.neg n)
  | VLoc l  -> st |> State.find_heap l |> eval_uminus st
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

let rec interp_bplus (st : 'a State.t) (l : V.value) (r : V.value) : V.value =
  match (l,r) with
  | VBit{w;v=v1}, VBit{v=v2;_} -> VBit{w;v=of_twos_complement Bigint.(v1 + v2) w}
  | VInt{w;v=v1}, VInt{v=v2;_} -> VInt{w;v=to_twos_complement Bigint.(v1 + v2) w}
  | VBit{w;v=v1}, VInteger n   -> interp_bplus st l (bit_of_rawint n w)
  | VInteger n,   VBit{w;v=v1} -> interp_bplus st (bit_of_rawint n w) r
  | VInt{w;v=v1}, VInteger n   -> interp_bplus st l (int_of_rawint n w)
  | VInteger n,   VInt{w;v=v1} -> interp_bplus st (int_of_rawint n w) r
  | VInteger n1,  VInteger n2  -> VInteger Bigint.(n1 + n2)
  | VLoc l1, VLoc l2           -> interp_bplus st (State.find_heap l1 st) (State.find_heap l2 st)
  | _ -> raise_s [%message "binary plus operation only defined on ints"
                     ~l:(l: V.value) (r: V.value)]

let rec interp_bplus_sat (st : 'a State.t) (l : V.value) (r : V.value) : V.value =
  match (l,r) with
  | VBit{w;v=v1}, VBit{v=v2;_} -> unsigned_op_sat v1 v2 w Bigint.(+)
  | VInt{w;v=v1}, VInt{v=v2;_} -> signed_op_sat v1 v2 w Bigint.(+)
  | VBit{w;v=v1}, VInteger n   -> interp_bplus_sat st l (bit_of_rawint n w)
  | VInteger n,   VBit{w;_}    -> interp_bplus_sat st (bit_of_rawint n w) r
  | VInt{w;_},    VInteger n   -> interp_bplus_sat st l (int_of_rawint n w)
  | VInteger n,   VInt{w;_}    -> interp_bplus_sat st (int_of_rawint n w) r
  | VLoc l1, VLoc l2           -> interp_bplus_sat st (State.find_heap l1 st) (State.find_heap l2 st)
  | _ -> failwith "binary sat plus operation only definted on fixed-width ints"

let rec interp_bminus (st : 'a State.t) (l : V.value) (r : V.value) : V.value =
  match (l,r) with
  | VBit{w;v=v1}, VBit{v=v2;_} -> VBit{w;v=of_twos_complement Bigint.(v1 - v2) w}
  | VInt{w;v=v1}, VInt{v=v2;_} -> VInt{w;v=to_twos_complement Bigint.(v1 - v2) w}
  | VBit{w;v=v1}, VInteger n   -> interp_bminus st l (bit_of_rawint n w)
  | VInteger n,   VBit{w;v=v1} -> interp_bminus st (bit_of_rawint n w) r
  | VInt{w;v=v1}, VInteger n   -> interp_bminus st l (int_of_rawint n w)
  | VInteger n,   VInt{w;v=v1} -> interp_bminus st (int_of_rawint n w) r
  | VInteger n1,  VInteger n2  -> VInteger Bigint.(n1 - n2)
  | VLoc l1, VLoc l2           -> interp_bminus st (State.find_heap l1 st) (State.find_heap l2 st)
  | _ -> failwith "binary plus operation only defined on ints"

let rec interp_bminus_sat (st : 'a State.t) (l : V.value) (r : V.value) : V.value =
  match (l,r) with
  | VBit{w;v=v1}, VBit{v=v2;_} -> unsigned_op_sat v1 v2 w Bigint.(-)
  | VInt{w;v=v1}, VInt{v=v2;_} -> signed_op_sat v1 v2 w Bigint.(-)
  | VBit{w;v=v1}, VInteger n   -> interp_bminus_sat st l (bit_of_rawint n w)
  | VInteger n, VBit{w;_}      -> interp_bminus_sat st (bit_of_rawint n w) r
  | VInt{w;_}, VInteger n      -> interp_bminus_sat st l (int_of_rawint n w)
  | VInteger n, VInt{w;_}      -> interp_bminus_sat st (int_of_rawint n w) r
  | VLoc l1, VLoc l2           -> interp_bminus_sat st (State.find_heap l1 st) (State.find_heap l2 st)
  | _ -> failwith "binary sat plus operation only definted on fixed-width ints"

let rec interp_bmult (st : 'a State.t) (l : V.value) (r : V.value) : V.value =
  match (l,r) with
  | VBit{w;v=v1}, VBit{v=v2;_} -> VBit{w;v=of_twos_complement Bigint.(v1 * v2) w}
  | VInt{w;v=v1}, VInt{v=v2;_} -> VInt{w;v=to_twos_complement Bigint.(v1 * v2) w}
  | VBit{w;v=v1}, VInteger n   -> interp_bmult st l (bit_of_rawint n w)
  | VInteger n,   VBit{w;v=v1} -> interp_bmult st (bit_of_rawint n w) r
  | VInt{w;v=v1}, VInteger n   -> interp_bmult st l (int_of_rawint n w)
  | VInteger n,   VInt{w;v=v1} -> interp_bmult st (int_of_rawint n w) r
  | VInteger n1,  VInteger n2  -> VInteger Bigint.(n1 * n2)
  | VLoc l1, VLoc l2           -> interp_bmult st (State.find_heap l1 st) (State.find_heap l2 st)
  | _ -> failwith "binary mult operation only defined on ints"

let rec interp_bdiv (st : 'a State.t) (l : V.value) (r : V.value) : V.value =
  match (l,r) with
  | VInteger n1, VInteger n2     -> VInteger Bigint.(n1 / n2)
  | VBit {w;v=v1}, VBit {v=v2;_} -> VBit {w;v=Bigint.(v1 / v2)}
  | VLoc l1, VLoc l2             -> interp_bdiv st (State.find_heap l1 st) (State.find_heap l2 st)
  | _ -> failwith "division only defined on positive values"

let rec interp_bmod (st : 'a State.t) (l : V.value) (r : V.value) : V.value =
  match (l,r) with
  | VInteger n1, VInteger n2     -> VInteger Bigint.(n1 % n2)
  | VBit {w;v=v1}, VBit {v=v2;_} -> VBit {w;v=Bigint.(v1 % v2)}
  | VLoc l1, VLoc l2             -> interp_bmod st (State.find_heap l1 st) (State.find_heap l2 st)
  | _ -> failwith "mod only defined on positive values"

let rec interp_bshl (st : 'a State.t) (l : V.value) (r : V.value) : V.value =
  match (l,r) with
  | VBit{w;v=v1}, VBit{v=v2;_}
  | VBit{w;v=v1}, VInteger v2 -> VBit{w;v=of_twos_complement (shift_bitstring_left v1 v2) w}
  | VInt{w;v=v1}, VBit{v=v2;_}
  | VInt{w;v=v1}, VInteger v2 -> VInt{w;v=to_twos_complement (shift_bitstring_left v1 v2) w}
  | VInteger v1, VInteger v2  -> VInteger(shift_bitstring_left v1 v2)
  | VBit {w;v=v1}, VInt{v=v2;_} -> VBit{w;v=of_twos_complement (shift_bitstring_left v1 v2) w} (* TODO *)
  | VInt {w;v=v1}, VInt{v=v2;_} -> VInt{w;v=to_twos_complement (shift_bitstring_left v2 v2) w} (* TODO *)
  | VLoc l1, VLoc l2            -> interp_bshl st (State.find_heap l1 st) (State.find_heap l2 st)
  | _ -> failwith "shift left operator not defined for these types"

let rec interp_bshr (st : 'a State.t) (l : V.value) (r : V.value) : V.value =
  match (l,r) with
  | VBit{w;v=v1}, VBit{v=v2;_}
  | VBit{w;v=v1}, VInteger v2 -> VBit{w;v=of_twos_complement (shift_bitstring_right v1 v2) w}
  | VInt{w;v=v1}, VBit{v=v2;_}
  | VInt{w;v=v1}, VInteger v2 -> VInt{w;v=to_twos_complement (shift_bitstring_right v1 v2) w}
  | VInteger v1,  VInteger v2 -> VInteger(shift_bitstring_right v1 v2)
  | VBit {w;v=v1}, VInt{v=v2;_} -> VBit{w;v=of_twos_complement (shift_bitstring_right v1 v2) w} (* TODO *)
  | VInt {w;v=v1}, VInt{v=v2;_} -> VInt{w;v=to_twos_complement (shift_bitstring_right v2 v2) w} (* TODO *)
  | VLoc l1, VLoc l2            -> interp_bshr st (State.find_heap l1 st) (State.find_heap l2 st)
  | _ -> failwith "shift right operator not defined for these types"

let rec interp_ble (st : 'a State.t) (l : V.value) (r : V.value) : V.value =
  match (l,r) with
  | VBit{v=v1;_}, VBit{v=v2;_}
  | VInteger v1, VInteger v2
  | VInt{v=v1;_}, VInt{v=v2;_} -> VBool Bigint.(v1 <= v2)
  | VInteger v1, VBit{w;v=v2}  -> interp_ble st (bit_of_rawint v1 w) r
  | VBit{w;v=v1}, VInteger v2  -> interp_ble st l (bit_of_rawint v2 w)
  | VInteger v1, VInt{w;v=v2}  -> interp_ble st (int_of_rawint v1 w) r
  | VInt{w;v=v1}, VInteger v2  -> interp_ble st l (int_of_rawint v2 w)
  | VLoc l1, VLoc l2           -> interp_ble st (State.find_heap l1 st) (State.find_heap l2 st)
  | _ -> failwith "leq operator only defined on int types"

let rec interp_bge (st : 'a State.t) (l : V.value) (r : V.value) : V.value =
  match (l,r) with
  | VBit{v=v1;_}, VBit{v=v2;_}
  | VInteger v1,  VInteger v2
  | VInt{v=v1;_}, VInt{v=v2;_} -> VBool Bigint.(v1 >= v2)
  | VInteger v1,  VBit{w;v=v2} -> interp_bge st (bit_of_rawint v1 w) r
  | VBit{w;v=v1}, VInteger v2  -> interp_bge st l (bit_of_rawint v2 w)
  | VInteger v1,  VInt{w;v=v2} -> interp_bge st (int_of_rawint v1 w) r
  | VInt{w;v=v1}, VInteger v2  -> interp_bge st l (int_of_rawint v2 w)
  | VLoc l1, VLoc l2           -> interp_bge st (State.find_heap l1 st) (State.find_heap l2 st)
  | _ -> failwith "geq operator only defined on int types"

let rec interp_blt (st : 'a State.t) (l : V.value) (r : V.value) : V.value =
  match (l,r) with
  | VBit{v=v1;_}, VBit{v=v2;_}
  | VInteger v1, VInteger v2
  | VInt{v=v1;_}, VInt{v=v2;_} -> VBool Bigint.(v1 < v2)
  | VInteger v1, VBit{w;v=v2}  -> interp_blt st (bit_of_rawint v1 w) r
  | VBit{w;v=v1}, VInteger v2  -> interp_blt st l (bit_of_rawint v2 w)
  | VInteger v1, VInt{w;v=v2}  -> interp_blt st (int_of_rawint v1 w) r
  | VInt{w;v=v1}, VInteger v2  -> interp_blt st l (int_of_rawint v2 w)
  | VLoc l1, VLoc l2           -> interp_blt st (State.find_heap l1 st) (State.find_heap l2 st)
  | _ -> failwith "lt operator only defined on int types"

let rec interp_bgt (st : 'a State.t) (l : V.value) (r : V.value) : V.value =
  match (l,r) with
  | VBit{v=v1;_}, VBit{v=v2;_}
  | VInteger v1,  VInteger v2
  | VInt{v=v1;_}, VInt{v=v2;_} -> VBool Bigint.(v1 > v2)
  | VInteger v1,  VBit{w;v=v2} -> interp_bgt st (bit_of_rawint v1 w) r
  | VBit{w;v=v1}, VInteger v2  -> interp_bgt st l (bit_of_rawint v2 w)
  | VInteger v1,  VInt{w;v=v2} -> interp_bgt st (int_of_rawint v1 w) r
  | VInt{w;v=v1}, VInteger v2  -> interp_bgt st l (int_of_rawint v2 w)
  | VLoc l1, VLoc l2           -> interp_bgt st (State.find_heap l1 st) (State.find_heap l2 st)
  | _ -> failwith "gt operator only defined on int types"

let rec interp_beq (st : 'a State.t) (l : V.value) (r : V.value) : V.value =
  match (l,r) with
  | VError s1, VError s2
  | VEnumField{enum_name=s1;_},
    VEnumField{enum_name=s2;_}                -> VBool Poly.(s1 = s2)
  | VSenumField{v=v1;_},
    VSenumField{v=v2;_}                       -> interp_beq st v1 v2
  | VBool b1, VBool b2                        -> VBool Poly.(b1 = b2)
  | VBit{v=n1;_}, VBit{v=n2;_}
  | VInteger n1, VInteger n2
  | VInt{v=n1;_}, VInt{v=n2;_}                -> VBool Bigint.(n1 = n2)
  | VVarbit{w=w1;v=n1;_},
    VVarbit{w=w2;v=n2;_}                      -> VBool(Bigint.(n1 = n2 && w1 = w2))
  | VBit{w;v=n1}, VInteger n2                 -> interp_beq st l (bit_of_rawint n2 w)
  | VInteger n1, VBit{w;v=n2}                 -> interp_beq st (bit_of_rawint n1 w) r
  | VInt{w;v=n1}, VInteger n2                 -> interp_beq st l (int_of_rawint n2 w)
  | VInteger n1, VInt{w;v=n2}                 -> interp_beq st (int_of_rawint n1 w) r
  | VStruct{fields=l1;_},
    VStruct{fields=l2;_}                      -> structs_equal st l1 l2
  | VHeader{fields=l1;is_valid=b1;_},
    VHeader{fields=l2;is_valid=b2;_}          -> headers_equal st l1 l2 b1 b2
  | VStack{headers=l1;_},
    VStack{headers=l2;_}                      -> stacks_equal st l1 l2
  | VUnion{fields=l1},
    VUnion{fields=l2}                         -> unions_equal st l1 l2
  | VTuple l1, VTuple l2                      -> tuples_equal st l1 l2
  | VNull, VNull -> VBool true
  | VLoc l1, VLoc l2                          -> interp_beq st (State.find_heap l1 st) (State.find_heap l2 st)
  | VNull, _
  | _, VNull -> VBool false
  | _ -> raise_s [%message "equality comparison undefined for given types"
                     ~l:(l:V.value) ~r:(r:V.value)]

and structs_equal (st : 'a State.t) (l1 : (string * V.loc) list)
(l2 : (string * V.loc) list) : V.value =
  let f (a : (string * V.loc) list) (b : string * V.loc) =
    if List.Assoc.mem a ~equal:String.equal (fst b)
    then a
    else b :: a in
  let l1' = List.fold_left l1 ~init:[] ~f:f in
  let l2' = List.fold_left l2 ~init:[] ~f:f in
  let g (a,b) =
    let b = State.find_heap b st in
    let h = (fun (x,y) ->
      let y = State.find_heap y st in
      String.equal x a && V.assert_bool (interp_beq st y b)) in
    List.exists l2' ~f:h in
  let b = List.for_all l1' ~f:g in
  VBool b

and headers_equal (st : 'a State.t) (l1 : (string * V.loc) list)
    (l2 : (string * V.loc) list) (b1 : bool) (b2 : bool) : V.value =
  let a = (not b1 && not b2) in
  let b = (b1 && b2 && V.assert_bool (structs_equal st l1 l2)) in
  VBool (a || b)

and stacks_equal (st : 'a State.t) (l1 : V.loc list) (l2 : V.loc list) : V.value =
  let l1 = List.map l1 ~f:(fun x -> State.find_heap x st) in
  let l2 = List.map l2 ~f:(fun x -> State.find_heap x st) in
  let f = (fun i a -> a |> interp_beq st (List.nth_exn l2 i) |> V.assert_bool) in
  let b = List.for_alli l1 ~f:f in
  VBool b

and unions_equal (st : 'a State.t) (l1 : (string * V.loc) list) (l2 : (string * V.loc) list) : V.value =
  VBool (V.assert_bool (structs_equal st l1 l2))

and tuples_equal (st : 'a State.t) (l1 : V.value list) (l2 : V.value list) : V.value =
  let f acc v1 v2 =
    let b = interp_beq st v1 v2 in
    V.VBool (acc |> V.assert_bool && b |> V.assert_bool) in
  match List.fold2 ~init:(V.VBool true) ~f l1 l2 with
  | Ok b -> b
  | Unequal_lengths -> V.VBool false

let interp_bne (st : 'a State.t) (l : V.value) (r : V.value) : V.value =
  interp_beq st l r |> V.assert_bool |> not |> VBool

let rec interp_bitwise_and (st : 'a State.t) (l : V.value) (r : V.value) : V.value =
  match (l,r) with
  | VBit{w;v=v1}, VBit{v=v2;_} -> VBit{w;v=Bigint.bit_and v1 v2}
  | VBit{w;v=v1}, VInteger n   -> interp_bitwise_and st l (bit_of_rawint n w)
  | VInteger n, VBit{w;v=v2}   -> interp_bitwise_and st (bit_of_rawint n w) r
  | VLoc l1, VLoc l2           -> interp_bitwise_and st (State.find_heap l1 st) (State.find_heap l2 st)
  | _ -> failwith "bitwise and only defined on fixed width ints"

let rec interp_bitwise_xor (st : 'a State.t) (l : V.value) (r : V.value) : V.value =
  match (l,r) with
  | VBit{w;v=v1}, VBit{v=v2;_} -> VBit{w;v=Bigint.bit_xor v1 v2}
  | VBit{w;v=v1}, VInteger n   -> interp_bitwise_xor st l (bit_of_rawint n w)
  | VInteger n,   VBit{w;v=v2} -> interp_bitwise_xor st (bit_of_rawint n w) r
  | VLoc l1, VLoc l2           -> interp_bitwise_xor st (State.find_heap l1 st) (State.find_heap l2 st)
  | _ -> failwith "bitwise xor only defined on fixed width ints"

let rec interp_bitwise_or (st : 'a State.t) (l : V.value) (r : V.value) : V.value =
  match (l,r) with
  | VBit{w;v=v1}, VBit{v=v2;_} -> VBit{w;v=Bigint.bit_or v1 v2}
  | VBit{w;v=v1}, VInteger n   -> interp_bitwise_or st l (bit_of_rawint n w)
  | VInteger n, VBit{w;v=v2}   -> interp_bitwise_or st (bit_of_rawint n w) r
  | VLoc l1, VLoc l2           -> interp_bitwise_or st (State.find_heap l1 st) (State.find_heap l2 st)
  | _ -> failwith "bitwise or only defined on fixed width ints"

let rec interp_concat (st : 'a State.t) (l : V.value) (r : V.value) : V.value =
  match (l,r) with
  | VBit{w=w1;v=v1}, VBit{w=w2;v=v2} ->
     VBit{w=Bigint.(w1+w2);v=Bigint.(shift_bitstring_left v1 w2 + v2)}
  | VBit{w;v},  VInteger n -> interp_concat st l (bit_of_rawint n w)
  | VInteger n, VBit{w;v}  -> interp_concat st (bit_of_rawint n w) r
  | VLoc l1, VLoc l2       -> interp_concat st (State.find_heap l1 st) (State.find_heap l2 st)
  | _ -> failwith "concat operator only defined on unsigned ints"

let rec interp_band (st : 'a State.t) (l : V.value) (r : V.value) : V.value =
  match (l,r) with
  | VBool b1, VBool b2 -> VBool(b1 && b2)
  | VLoc l1, VLoc l2   -> interp_band st (State.find_heap l1 st) (State.find_heap l2 st)
  | _ -> failwith "and operator only defined on bools"

let rec interp_bor (st : 'a State.t) (l : V.value) (r : V.value) : V.value =
  match (l,r) with
  | VBool b1, VBool b2 -> VBool(b1 || b2)
  | VLoc l1, VLoc l2   -> interp_bor st (State.find_heap l1 st) (State.find_heap l2 st)
  | _ -> failwith "or operator only defined on bools"

let bitwise_op_of_signeds (op : Bigint.t -> Bigint.t -> Bigint.t)
(v1 : Bigint.t) (v2 : Bigint.t) (w : Bigint.t) : V.value =
  let v1' = of_twos_complement v1 w in
  let v2' = of_twos_complement v2 w in
  let n = op v1' v2' in
  VBit{w;v=to_twos_complement n w}

let interp_binary_op (st : 'a State.t) (op: Op.bin) (l: V.value) (r: V.value) =
  match snd op with
  | Plus     -> interp_bplus st l r
  | PlusSat  -> interp_bplus_sat st l r
  | Minus    -> interp_bminus st l r
  | MinusSat -> interp_bminus_sat st l r
  | Mul      -> interp_bmult st l r
  | Div      -> interp_bdiv st l r
  | Mod      -> interp_bmod st l r
  | Shl      -> interp_bshl st l r
  | Shr      -> interp_bshr st l r
  | Le       -> interp_ble st l r
  | Ge       -> interp_bge st l r
  | Lt       -> interp_blt st l r
  | Gt       -> interp_bgt st l r
  | Eq       -> interp_beq st l r
  | NotEq    -> interp_bne st l r
  | BitAnd   -> interp_bitwise_and st l r
  | BitXor   -> interp_bitwise_xor st l r
  | BitOr    -> interp_bitwise_or st l r
  | PlusPlus -> interp_concat st l r
  | And      -> interp_band st l r
  | Or       -> interp_bor st l r


let interp_unary_op (st : 'a State.t) (op: Op.uni) (v: V.value) =
  match snd op with
  | Not    -> eval_not st v
  | BitNot -> eval_bitnot st v
  | UMinus -> eval_uminus st v

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

let rec interp_cast ~type_lookup:(type_lookup: Types.name -> Typed.Type.t)
      (new_type: Typed.Type.t) (value: V.value) : V.value =
  match new_type with
  | Bool -> bool_of_val value
  | Bit{width} -> bit_of_val width value
  | Int{width} -> int_of_val width value
  | NewType nt -> interp_cast ~type_lookup nt.typ value
  | TypeName n -> interp_cast ~type_lookup (type_lookup n) value
  | _ -> failwith "type cast unimplemented"
