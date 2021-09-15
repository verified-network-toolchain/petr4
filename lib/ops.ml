open Core_kernel
open Typed
open Prog

(*----------------------------------------------------------------------------*)
(* Unary Operator Evaluation *)
(*----------------------------------------------------------------------------*)

let eval_not (v : coq_ValueBase) : coq_ValueBase =
  match v with
  | ValBaseBool b -> ValBaseBool (not b)
  | _ -> failwith "not operator can only be applied to bools"

let eval_bitnot (v : coq_ValueBase) : coq_ValueBase =
  failwith "unimplemented"

and eval_uminus (v : coq_ValueBase) : coq_ValueBase =
  failwith "unimplemented"

(*----------------------------------------------------------------------------*)
(* binary operator interpretation *)
(*----------------------------------------------------------------------------*)

let unsigned_op_sat (l : Bigint.t) (r : Bigint.t) (w : int)
(op : Bigint.t -> Bigint.t -> Bigint.t) : coq_ValueBase =
  failwith "unimplemented"

let signed_op_sat (l : Bigint.t) (r : Bigint.t) (w : int)
(op : Bigint.t -> Bigint.t -> Bigint.t) : coq_ValueBase =
  failwith "unimplemented"

let interp_bplus (l : coq_ValueBase) (r : coq_ValueBase) : coq_ValueBase =
  failwith "unimplemented"

let interp_bplus_sat (l : coq_ValueBase) (r : coq_ValueBase) : coq_ValueBase =
  failwith "unimplemented"

let interp_bminus (l : coq_ValueBase) (r : coq_ValueBase) : coq_ValueBase =
  failwith "unimplemented"

let interp_bminus_sat (l : coq_ValueBase) (r : coq_ValueBase) : coq_ValueBase =
  failwith "unimplemented"

let interp_bmult (l : coq_ValueBase) (r : coq_ValueBase) : coq_ValueBase =
  failwith "unimplemented"

let interp_bdiv (l : coq_ValueBase) (r : coq_ValueBase) : coq_ValueBase =
  failwith "unimplemented"

let interp_bmod (l : coq_ValueBase) (r : coq_ValueBase) : coq_ValueBase =
  failwith "unimplemented"

let interp_bshl (l : coq_ValueBase) (r : coq_ValueBase) : coq_ValueBase =
  failwith "unimplemented"

let interp_bshr (l : coq_ValueBase) (r : coq_ValueBase) : coq_ValueBase =
  failwith "unimplemented"

let interp_ble (l : coq_ValueBase) (r : coq_ValueBase) : coq_ValueBase =
  failwith "unimplemented"

let interp_bge (l : coq_ValueBase) (r : coq_ValueBase) : coq_ValueBase =
  failwith "unimplemented"

let interp_blt (l : coq_ValueBase) (r : coq_ValueBase) : coq_ValueBase =
  failwith "unimplemented"

let interp_bgt (l : coq_ValueBase) (r : coq_ValueBase) : coq_ValueBase =
  failwith "unimplemented"

let rec interp_beq (l : coq_ValueBase) (r : coq_ValueBase) : bool =
  failwith "unimplemented"

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

let interp_bitwise_and (l : coq_ValueBase) (r : coq_ValueBase) : coq_ValueBase =
  failwith "unimplemented"

let interp_bitwise_xor (l : coq_ValueBase) (r : coq_ValueBase) : coq_ValueBase =
  failwith "unimplemented"

let interp_bitwise_or (l : coq_ValueBase) (r : coq_ValueBase) : coq_ValueBase =
  failwith "unimplemented"

let interp_concat (l : coq_ValueBase) (r : coq_ValueBase) : coq_ValueBase =
  failwith "unimplemented"

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
  failwith "unimplemented"

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
  failwith "unimplemented"

let bit_of_val (width : int) (v : coq_ValueBase) : coq_ValueBase =
  failwith "unimplemented"

let int_of_val (width : int) (v : coq_ValueBase) : coq_ValueBase =
  failwith "unimplemented"

let fields_for_cast (fields: Typed.coq_FieldType list) (value: coq_ValueBase) =
  match value with
  | ValBaseTuple vals ->
     let fields_vals = List.zip_exn fields vals in
     List.map ~f:(fun ((f, _), v) -> f, v) fields_vals
  | ValBaseRecord fields -> fields
  | _ -> failwith "cannot cast"

let interp_cast ~type_lookup:(type_lookup: P4name.t -> Typed.coq_P4Type)
      (new_type: coq_P4Type) (value: coq_ValueBase) : coq_ValueBase =
  failwith "unimplemented"
