open BinInt
open BinNums
open BinPos
open Coqlib
open Datatypes

(** val coq_P_mod_two_p : positive -> nat -> coq_Z **)

let rec coq_P_mod_two_p p = function
| O -> Z0
| S m ->
  (match p with
   | Coq_xI q -> Z.succ_double (coq_P_mod_two_p q m)
   | Coq_xO q -> Z.double (coq_P_mod_two_p q m)
   | Coq_xH -> Zpos Coq_xH)

(** val coq_Zshiftin : bool -> coq_Z -> coq_Z **)

let coq_Zshiftin b x =
  if b then Z.succ_double x else Z.double x

(** val coq_Zzero_ext : coq_Z -> coq_Z -> coq_Z **)

let coq_Zzero_ext n x =
  Z.iter n (fun rec0 x0 -> coq_Zshiftin (Z.odd x0) (rec0 (Z.div2 x0)))
    (fun _ -> Z0) x

(** val coq_Zsign_ext : coq_Z -> coq_Z -> coq_Z **)

let coq_Zsign_ext n x =
  Z.iter (Z.pred n) (fun rec0 x0 ->
    coq_Zshiftin (Z.odd x0) (rec0 (Z.div2 x0))) (fun x0 ->
    if (&&) (Z.odd x0) ((fun x -> x) (zlt Z0 n)) then Zneg Coq_xH else Z0) x

(** val coq_Z_one_bits : nat -> coq_Z -> coq_Z -> coq_Z list **)

let rec coq_Z_one_bits n x i =
  match n with
  | O -> []
  | S m ->
    if Z.odd x
    then i :: (coq_Z_one_bits m (Z.div2 x) (Z.add i (Zpos Coq_xH)))
    else coq_Z_one_bits m (Z.div2 x) (Z.add i (Zpos Coq_xH))

(** val coq_P_is_power2 : positive -> bool **)

let rec coq_P_is_power2 = function
| Coq_xI _ -> false
| Coq_xO q -> coq_P_is_power2 q
| Coq_xH -> true

(** val coq_Z_is_power2 : coq_Z -> coq_Z option **)

let coq_Z_is_power2 x = match x with
| Zpos p -> if coq_P_is_power2 p then Some (Z.log2 x) else None
| _ -> None

(** val coq_Zsize : coq_Z -> coq_Z **)

let coq_Zsize = function
| Zpos p -> Zpos (Pos.size p)
| _ -> Z0
