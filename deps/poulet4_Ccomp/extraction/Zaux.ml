open BinInt
open BinNums
open BinPos
open Datatypes

type radix =
  coq_Z
  (* singleton inductive, whose constructor was Build_radix *)

(** val radix_val : radix -> coq_Z **)

let radix_val r =
  r

(** val radix2 : radix **)

let radix2 =
  Zpos (Coq_xO Coq_xH)

(** val coq_Zpos_div_eucl_aux1 : positive -> positive -> coq_Z * coq_Z **)

let rec coq_Zpos_div_eucl_aux1 a b = match b with
| Coq_xI _ -> Z.pos_div_eucl a (Zpos b)
| Coq_xO b' ->
  (match a with
   | Coq_xI a' ->
     let (q, r) = coq_Zpos_div_eucl_aux1 a' b' in
     (q, (Z.add (Z.mul (Zpos (Coq_xO Coq_xH)) r) (Zpos Coq_xH)))
   | Coq_xO a' ->
     let (q, r) = coq_Zpos_div_eucl_aux1 a' b' in
     (q, (Z.mul (Zpos (Coq_xO Coq_xH)) r))
   | Coq_xH -> (Z0, (Zpos a)))
| Coq_xH -> ((Zpos a), Z0)

(** val coq_Zpos_div_eucl_aux : positive -> positive -> coq_Z * coq_Z **)

let coq_Zpos_div_eucl_aux a b =
  match Pos.compare a b with
  | Eq -> ((Zpos Coq_xH), Z0)
  | Lt -> (Z0, (Zpos a))
  | Gt -> coq_Zpos_div_eucl_aux1 a b

(** val coq_Zfast_div_eucl : coq_Z -> coq_Z -> coq_Z * coq_Z **)

let coq_Zfast_div_eucl a b =
  match a with
  | Z0 -> (Z0, Z0)
  | Zpos a' ->
    (match b with
     | Z0 -> (Z0, (match Z.modulo (Zpos Coq_xH) Z0 with
                   | Z0 -> Z0
                   | _ -> a))
     | Zpos b' -> coq_Zpos_div_eucl_aux a' b'
     | Zneg b' ->
       let (q, r) = coq_Zpos_div_eucl_aux a' b' in
       (match r with
        | Z0 -> ((Z.opp q), Z0)
        | _ -> ((Z.opp (Z.add q (Zpos Coq_xH))), (Z.add b r))))
  | Zneg a' ->
    (match b with
     | Z0 -> (Z0, (match Z.modulo (Zpos Coq_xH) Z0 with
                   | Z0 -> Z0
                   | _ -> a))
     | Zpos b' ->
       let (q, r) = coq_Zpos_div_eucl_aux a' b' in
       (match r with
        | Z0 -> ((Z.opp q), Z0)
        | _ -> ((Z.opp (Z.add q (Zpos Coq_xH))), (Z.sub b r)))
     | Zneg b' -> let (q, r) = coq_Zpos_div_eucl_aux a' b' in (q, (Z.opp r)))

(** val iter_nat : ('a1 -> 'a1) -> nat -> 'a1 -> 'a1 **)

let rec iter_nat f n x =
  match n with
  | O -> x
  | S n' -> iter_nat f n' (f x)
