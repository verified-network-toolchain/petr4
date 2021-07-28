open BinInt
open BinNums
open Binary
open Zbool

(** val join_bits : coq_Z -> coq_Z -> bool -> coq_Z -> coq_Z -> coq_Z **)

let join_bits mw ew s m e =
  Z.add
    (Z.shiftl (Z.add (if s then Z.pow (Zpos (Coq_xO Coq_xH)) ew else Z0) e)
      mw) m

(** val split_bits : coq_Z -> coq_Z -> coq_Z -> (bool * coq_Z) * coq_Z **)

let split_bits mw ew x =
  let mm = Z.pow (Zpos (Coq_xO Coq_xH)) mw in
  let em = Z.pow (Zpos (Coq_xO Coq_xH)) ew in
  (((Z.leb (Z.mul mm em) x), (Z.modulo x mm)), (Z.modulo (Z.div x mm) em))

(** val bits_of_binary_float : coq_Z -> coq_Z -> binary_float -> coq_Z **)

let bits_of_binary_float mw ew =
  let emax = Z.pow (Zpos (Coq_xO Coq_xH)) (Z.sub ew (Zpos Coq_xH)) in
  let prec = Z.add mw (Zpos Coq_xH) in
  let emin = Z.sub (Z.sub (Zpos (Coq_xI Coq_xH)) emax) prec in
  (fun x ->
  match x with
  | B754_zero sx -> join_bits mw ew sx Z0 Z0
  | B754_infinity sx ->
    join_bits mw ew sx Z0
      (Z.sub (Z.pow (Zpos (Coq_xO Coq_xH)) ew) (Zpos Coq_xH))
  | B754_nan (sx, plx) ->
    join_bits mw ew sx (Zpos plx)
      (Z.sub (Z.pow (Zpos (Coq_xO Coq_xH)) ew) (Zpos Coq_xH))
  | B754_finite (sx, mx, ex) ->
    let m = Z.sub (Zpos mx) (Z.pow (Zpos (Coq_xO Coq_xH)) mw) in
    if Z.leb Z0 m
    then join_bits mw ew sx m (Z.add (Z.sub ex emin) (Zpos Coq_xH))
    else join_bits mw ew sx (Zpos mx) Z0)

(** val binary_float_of_bits_aux : coq_Z -> coq_Z -> coq_Z -> full_float **)

let binary_float_of_bits_aux mw ew =
  let emax = Z.pow (Zpos (Coq_xO Coq_xH)) (Z.sub ew (Zpos Coq_xH)) in
  let prec = Z.add mw (Zpos Coq_xH) in
  let emin = Z.sub (Z.sub (Zpos (Coq_xI Coq_xH)) emax) prec in
  (fun x ->
  let (p, ex) = split_bits mw ew x in
  let (sx, mx) = p in
  if coq_Zeq_bool ex Z0
  then (match mx with
        | Z0 -> F754_zero sx
        | Zpos px -> F754_finite (sx, px, emin)
        | Zneg _ -> F754_nan (false, Coq_xH))
  else if coq_Zeq_bool ex
            (Z.sub (Z.pow (Zpos (Coq_xO Coq_xH)) ew) (Zpos Coq_xH))
       then (match mx with
             | Z0 -> F754_infinity sx
             | Zpos plx -> F754_nan (sx, plx)
             | Zneg _ -> F754_nan (false, Coq_xH))
       else (match Z.add mx (Z.pow (Zpos (Coq_xO Coq_xH)) mw) with
             | Zpos px ->
               F754_finite (sx, px, (Z.sub (Z.add ex emin) (Zpos Coq_xH)))
             | _ -> F754_nan (false, Coq_xH)))

(** val binary_float_of_bits : coq_Z -> coq_Z -> coq_Z -> binary_float **)

let binary_float_of_bits mw ew x =
  let emax = Z.pow (Zpos (Coq_xO Coq_xH)) (Z.sub ew (Zpos Coq_xH)) in
  let prec = Z.add mw (Zpos Coq_xH) in
  coq_FF2B prec emax (binary_float_of_bits_aux mw ew x)

type binary32 = binary_float

(** val b32_of_bits : coq_Z -> binary32 **)

let b32_of_bits =
  binary_float_of_bits (Zpos (Coq_xI (Coq_xI (Coq_xI (Coq_xO Coq_xH)))))
    (Zpos (Coq_xO (Coq_xO (Coq_xO Coq_xH))))

(** val bits_of_b32 : binary32 -> coq_Z **)

let bits_of_b32 =
  bits_of_binary_float (Zpos (Coq_xI (Coq_xI (Coq_xI (Coq_xO Coq_xH)))))
    (Zpos (Coq_xO (Coq_xO (Coq_xO Coq_xH))))

type binary64 = binary_float

(** val b64_of_bits : coq_Z -> binary64 **)

let b64_of_bits =
  binary_float_of_bits (Zpos (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI
    Coq_xH)))))) (Zpos (Coq_xI (Coq_xI (Coq_xO Coq_xH))))

(** val bits_of_b64 : binary64 -> coq_Z **)

let bits_of_b64 =
  bits_of_binary_float (Zpos (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI
    Coq_xH)))))) (Zpos (Coq_xI (Coq_xI (Coq_xO Coq_xH))))
