open BinInt
open BinNums
open BinPos
open Bool
open Bracket
open Datatypes
open Defs
open FLT
open Operations
open Round
open SpecFloat
open Zaux
open Zbool
open Zpower

type full_float =
| F754_zero of bool
| F754_infinity of bool
| F754_nan of bool * positive
| F754_finite of bool * positive * coq_Z

type binary_float =
| B754_zero of bool
| B754_infinity of bool
| B754_nan of bool * positive
| B754_finite of bool * positive * coq_Z

(** val coq_FF2B : coq_Z -> coq_Z -> full_float -> binary_float **)

let coq_FF2B _ _ = function
| F754_zero s -> B754_zero s
| F754_infinity s -> B754_infinity s
| F754_nan (b, pl) -> B754_nan (b, pl)
| F754_finite (s, m, e) -> B754_finite (s, m, e)

(** val coq_Bsign : coq_Z -> coq_Z -> binary_float -> bool **)

let coq_Bsign _ _ = function
| B754_zero s -> s
| B754_infinity s -> s
| B754_nan (s, _) -> s
| B754_finite (s, _, _) -> s

(** val get_nan_pl : coq_Z -> coq_Z -> binary_float -> positive **)

let get_nan_pl _ _ = function
| B754_nan (_, pl) -> pl
| _ -> Coq_xH

(** val build_nan : coq_Z -> coq_Z -> binary_float -> binary_float **)

let build_nan prec emax x =
  B754_nan ((coq_Bsign prec emax x), (get_nan_pl prec emax x))

(** val coq_Bopp :
    coq_Z -> coq_Z -> (binary_float -> binary_float) -> binary_float ->
    binary_float **)

let coq_Bopp prec emax opp_nan x = match x with
| B754_zero sx -> B754_zero (negb sx)
| B754_infinity sx -> B754_infinity (negb sx)
| B754_nan (_, _) -> build_nan prec emax (opp_nan x)
| B754_finite (sx, mx, ex) -> B754_finite ((negb sx), mx, ex)

(** val coq_Babs :
    coq_Z -> coq_Z -> (binary_float -> binary_float) -> binary_float ->
    binary_float **)

let coq_Babs prec emax abs_nan x = match x with
| B754_zero _ -> B754_zero false
| B754_infinity _ -> B754_infinity false
| B754_nan (_, _) -> build_nan prec emax (abs_nan x)
| B754_finite (_, mx, ex) -> B754_finite (false, mx, ex)

(** val coq_Bcompare :
    coq_Z -> coq_Z -> binary_float -> binary_float -> comparison option **)

let coq_Bcompare _ _ f1 f2 =
  match f1 with
  | B754_zero _ ->
    (match f2 with
     | B754_zero _ -> Some Eq
     | B754_infinity s -> Some (if s then Gt else Lt)
     | B754_nan (_, _) -> None
     | B754_finite (s, _, _) -> Some (if s then Gt else Lt))
  | B754_infinity s ->
    (match f2 with
     | B754_infinity s0 ->
       Some (if s then if s0 then Eq else Lt else if s0 then Gt else Eq)
     | B754_nan (_, _) -> None
     | _ -> Some (if s then Lt else Gt))
  | B754_nan (_, _) -> None
  | B754_finite (s1, m1, e1) ->
    (match f2 with
     | B754_zero _ -> Some (if s1 then Lt else Gt)
     | B754_infinity s -> Some (if s then Gt else Lt)
     | B754_nan (_, _) -> None
     | B754_finite (s2, m2, e2) ->
       Some
         (if s1
          then if s2
               then (match Z.compare e1 e2 with
                     | Eq -> coq_CompOpp (Pos.compare_cont Eq m1 m2)
                     | Lt -> Gt
                     | Gt -> Lt)
               else Lt
          else if s2
               then Gt
               else (match Z.compare e1 e2 with
                     | Eq -> Pos.compare_cont Eq m1 m2
                     | x -> x)))

type shr_record = { shr_m : coq_Z; shr_r : bool; shr_s : bool }

(** val shr_1 : shr_record -> shr_record **)

let shr_1 mrs =
  let { shr_m = m; shr_r = r; shr_s = s } = mrs in
  let s0 = (||) r s in
  (match m with
   | Z0 -> { shr_m = Z0; shr_r = false; shr_s = s0 }
   | Zpos p0 ->
     (match p0 with
      | Coq_xI p -> { shr_m = (Zpos p); shr_r = true; shr_s = s0 }
      | Coq_xO p -> { shr_m = (Zpos p); shr_r = false; shr_s = s0 }
      | Coq_xH -> { shr_m = Z0; shr_r = true; shr_s = s0 })
   | Zneg p0 ->
     (match p0 with
      | Coq_xI p -> { shr_m = (Zneg p); shr_r = true; shr_s = s0 }
      | Coq_xO p -> { shr_m = (Zneg p); shr_r = false; shr_s = s0 }
      | Coq_xH -> { shr_m = Z0; shr_r = true; shr_s = s0 }))

(** val loc_of_shr_record : shr_record -> location **)

let loc_of_shr_record mrs =
  let { shr_m = _; shr_r = shr_r0; shr_s = shr_s0 } = mrs in
  if shr_r0
  then if shr_s0 then Coq_loc_Inexact Gt else Coq_loc_Inexact Eq
  else if shr_s0 then Coq_loc_Inexact Lt else Coq_loc_Exact

(** val shr_record_of_loc : coq_Z -> location -> shr_record **)

let shr_record_of_loc m = function
| Coq_loc_Exact -> { shr_m = m; shr_r = false; shr_s = false }
| Coq_loc_Inexact c ->
  (match c with
   | Eq -> { shr_m = m; shr_r = true; shr_s = false }
   | Lt -> { shr_m = m; shr_r = false; shr_s = true }
   | Gt -> { shr_m = m; shr_r = true; shr_s = true })

(** val shr : shr_record -> coq_Z -> coq_Z -> shr_record * coq_Z **)

let shr mrs e n = match n with
| Zpos p -> ((iter_pos shr_1 p mrs), (Z.add e n))
| _ -> (mrs, e)

(** val shr_fexp :
    coq_Z -> coq_Z -> coq_Z -> coq_Z -> location -> shr_record * coq_Z **)

let shr_fexp prec emax =
  let emin = Z.sub (Z.sub (Zpos (Coq_xI Coq_xH)) emax) prec in
  let fexp = coq_FLT_exp emin prec in
  (fun m e l ->
  shr (shr_record_of_loc m l) e (Z.sub (fexp (Z.add (coq_Zdigits2 m) e)) e))

type mode =
| Coq_mode_NE
| Coq_mode_ZR
| Coq_mode_DN
| Coq_mode_UP
| Coq_mode_NA

(** val choice_mode : mode -> bool -> coq_Z -> location -> coq_Z **)

let choice_mode m sx mx lx =
  match m with
  | Coq_mode_NE -> cond_incr (round_N (negb (Z.even mx)) lx) mx
  | Coq_mode_ZR -> mx
  | Coq_mode_DN -> cond_incr (round_sign_DN sx lx) mx
  | Coq_mode_UP -> cond_incr (round_sign_UP sx lx) mx
  | Coq_mode_NA -> cond_incr (round_N true lx) mx

(** val overflow_to_inf : mode -> bool -> bool **)

let overflow_to_inf m s =
  match m with
  | Coq_mode_ZR -> false
  | Coq_mode_DN -> s
  | Coq_mode_UP -> negb s
  | _ -> true

(** val binary_overflow : coq_Z -> coq_Z -> mode -> bool -> full_float **)

let binary_overflow prec emax m s =
  if overflow_to_inf m s
  then F754_infinity s
  else F754_finite (s,
         (match Z.sub (Z.pow (Zpos (Coq_xO Coq_xH)) prec) (Zpos Coq_xH) with
          | Zpos p -> p
          | _ -> Coq_xH), (Z.sub emax prec))

(** val binary_round_aux :
    coq_Z -> coq_Z -> mode -> bool -> coq_Z -> coq_Z -> location -> full_float **)

let binary_round_aux prec emax mode0 sx mx ex lx =
  let (mrs', e') = shr_fexp prec emax mx ex lx in
  let (mrs'', e'') =
    shr_fexp prec emax
      (choice_mode mode0 sx mrs'.shr_m (loc_of_shr_record mrs')) e'
      Coq_loc_Exact
  in
  (match mrs''.shr_m with
   | Z0 -> F754_zero sx
   | Zpos m ->
     if Z.leb e'' (Z.sub emax prec)
     then F754_finite (sx, m, e'')
     else binary_overflow prec emax mode0 sx
   | Zneg _ -> F754_nan (false, Coq_xH))

(** val coq_Bmult :
    coq_Z -> coq_Z -> (binary_float -> binary_float -> binary_float) -> mode
    -> binary_float -> binary_float -> binary_float **)

let coq_Bmult prec emax mult_nan m x y =
  match x with
  | B754_zero sx ->
    (match y with
     | B754_zero sy -> B754_zero (xorb sx sy)
     | B754_finite (sy, _, _) -> B754_zero (xorb sx sy)
     | _ -> build_nan prec emax (mult_nan x y))
  | B754_infinity sx ->
    (match y with
     | B754_infinity sy -> B754_infinity (xorb sx sy)
     | B754_finite (sy, _, _) -> B754_infinity (xorb sx sy)
     | _ -> build_nan prec emax (mult_nan x y))
  | B754_nan (_, _) -> build_nan prec emax (mult_nan x y)
  | B754_finite (sx, mx, ex) ->
    (match y with
     | B754_zero sy -> B754_zero (xorb sx sy)
     | B754_infinity sy -> B754_infinity (xorb sx sy)
     | B754_nan (_, _) -> build_nan prec emax (mult_nan x y)
     | B754_finite (sy, my, ey) ->
       coq_FF2B prec emax
         (binary_round_aux prec emax m (xorb sx sy) (Zpos (Pos.mul mx my))
           (Z.add ex ey) Coq_loc_Exact))

(** val shl_align : positive -> coq_Z -> coq_Z -> positive * coq_Z **)

let shl_align mx ex ex' =
  match Z.sub ex' ex with
  | Zneg d -> ((shift_pos d mx), ex')
  | _ -> (mx, ex)

(** val shl_align_fexp :
    coq_Z -> coq_Z -> positive -> coq_Z -> positive * coq_Z **)

let shl_align_fexp prec emax =
  let emin = Z.sub (Z.sub (Zpos (Coq_xI Coq_xH)) emax) prec in
  let fexp = coq_FLT_exp emin prec in
  (fun mx ex -> shl_align mx ex (fexp (Z.add (Zpos (digits2_pos mx)) ex)))

(** val binary_round :
    coq_Z -> coq_Z -> mode -> bool -> positive -> coq_Z -> full_float **)

let binary_round prec emax m sx mx ex =
  let (mz, ez) = shl_align_fexp prec emax mx ex in
  binary_round_aux prec emax m sx (Zpos mz) ez Coq_loc_Exact

(** val binary_normalize :
    coq_Z -> coq_Z -> mode -> coq_Z -> coq_Z -> bool -> binary_float **)

let binary_normalize prec emax mode0 m e szero =
  match m with
  | Z0 -> B754_zero szero
  | Zpos m0 -> coq_FF2B prec emax (binary_round prec emax mode0 false m0 e)
  | Zneg m0 -> coq_FF2B prec emax (binary_round prec emax mode0 true m0 e)

(** val coq_Bplus :
    coq_Z -> coq_Z -> (binary_float -> binary_float -> binary_float) -> mode
    -> binary_float -> binary_float -> binary_float **)

let coq_Bplus prec emax plus_nan m x y =
  match x with
  | B754_zero sx ->
    (match y with
     | B754_zero sy ->
       if eqb sx sy
       then x
       else (match m with
             | Coq_mode_DN -> B754_zero true
             | _ -> B754_zero false)
     | B754_nan (_, _) -> build_nan prec emax (plus_nan x y)
     | _ -> y)
  | B754_infinity sx ->
    (match y with
     | B754_infinity sy ->
       if eqb sx sy then x else build_nan prec emax (plus_nan x y)
     | B754_nan (_, _) -> build_nan prec emax (plus_nan x y)
     | _ -> x)
  | B754_nan (_, _) -> build_nan prec emax (plus_nan x y)
  | B754_finite (sx, mx, ex) ->
    (match y with
     | B754_zero _ -> x
     | B754_infinity _ -> y
     | B754_nan (_, _) -> build_nan prec emax (plus_nan x y)
     | B754_finite (sy, my, ey) ->
       let ez = Z.min ex ey in
       binary_normalize prec emax m
         (Z.add (cond_Zopp sx (Zpos (fst (shl_align mx ex ez))))
           (cond_Zopp sy (Zpos (fst (shl_align my ey ez))))) ez
         (match m with
          | Coq_mode_DN -> true
          | _ -> false))

(** val coq_Bminus :
    coq_Z -> coq_Z -> (binary_float -> binary_float -> binary_float) -> mode
    -> binary_float -> binary_float -> binary_float **)

let coq_Bminus prec emax minus_nan m x y =
  match x with
  | B754_zero sx ->
    (match y with
     | B754_zero sy ->
       if eqb sx (negb sy)
       then x
       else (match m with
             | Coq_mode_DN -> B754_zero true
             | _ -> B754_zero false)
     | B754_infinity sy -> B754_infinity (negb sy)
     | B754_nan (_, _) -> build_nan prec emax (minus_nan x y)
     | B754_finite (sy, my, ey) -> B754_finite ((negb sy), my, ey))
  | B754_infinity sx ->
    (match y with
     | B754_infinity sy ->
       if eqb sx (negb sy) then x else build_nan prec emax (minus_nan x y)
     | B754_nan (_, _) -> build_nan prec emax (minus_nan x y)
     | _ -> x)
  | B754_nan (_, _) -> build_nan prec emax (minus_nan x y)
  | B754_finite (sx, mx, ex) ->
    (match y with
     | B754_zero _ -> x
     | B754_infinity sy -> B754_infinity (negb sy)
     | B754_nan (_, _) -> build_nan prec emax (minus_nan x y)
     | B754_finite (sy, my, ey) ->
       let ez = Z.min ex ey in
       binary_normalize prec emax m
         (Z.sub (cond_Zopp sx (Zpos (fst (shl_align mx ex ez))))
           (cond_Zopp sy (Zpos (fst (shl_align my ey ez))))) ez
         (match m with
          | Coq_mode_DN -> true
          | _ -> false))

(** val coq_Bfma_szero :
    coq_Z -> coq_Z -> mode -> binary_float -> binary_float -> binary_float ->
    bool **)

let coq_Bfma_szero prec emax m x y z =
  let s_xy = xorb (coq_Bsign prec emax x) (coq_Bsign prec emax y) in
  if eqb s_xy (coq_Bsign prec emax z)
  then s_xy
  else (match m with
        | Coq_mode_DN -> true
        | _ -> false)

(** val coq_Bfma :
    coq_Z -> coq_Z -> (binary_float -> binary_float -> binary_float ->
    binary_float) -> mode -> binary_float -> binary_float -> binary_float ->
    binary_float **)

let coq_Bfma prec emax fma_nan m x y z =
  match x with
  | B754_zero _ ->
    (match y with
     | B754_zero _ ->
       (match z with
        | B754_zero _ -> B754_zero (coq_Bfma_szero prec emax m x y z)
        | B754_nan (_, _) -> build_nan prec emax (fma_nan x y z)
        | _ -> z)
     | B754_finite (_, _, _) ->
       (match z with
        | B754_zero _ -> B754_zero (coq_Bfma_szero prec emax m x y z)
        | B754_nan (_, _) -> build_nan prec emax (fma_nan x y z)
        | _ -> z)
     | _ -> build_nan prec emax (fma_nan x y z))
  | B754_infinity sx ->
    (match y with
     | B754_infinity sy ->
       let s = xorb sx sy in
       (match z with
        | B754_infinity sz ->
          if eqb s sz then z else build_nan prec emax (fma_nan x y z)
        | B754_nan (_, _) -> build_nan prec emax (fma_nan x y z)
        | _ -> B754_infinity s)
     | B754_finite (sy, _, _) ->
       let s = xorb sx sy in
       (match z with
        | B754_infinity sz ->
          if eqb s sz then z else build_nan prec emax (fma_nan x y z)
        | B754_nan (_, _) -> build_nan prec emax (fma_nan x y z)
        | _ -> B754_infinity s)
     | _ -> build_nan prec emax (fma_nan x y z))
  | B754_nan (_, _) -> build_nan prec emax (fma_nan x y z)
  | B754_finite (sx, mx, ex) ->
    (match y with
     | B754_zero _ ->
       (match z with
        | B754_zero _ -> B754_zero (coq_Bfma_szero prec emax m x y z)
        | B754_nan (_, _) -> build_nan prec emax (fma_nan x y z)
        | _ -> z)
     | B754_infinity sy ->
       let s = xorb sx sy in
       (match z with
        | B754_infinity sz ->
          if eqb s sz then z else build_nan prec emax (fma_nan x y z)
        | B754_nan (_, _) -> build_nan prec emax (fma_nan x y z)
        | _ -> B754_infinity s)
     | B754_nan (_, _) -> build_nan prec emax (fma_nan x y z)
     | B754_finite (sy, my, ey) ->
       (match z with
        | B754_zero _ ->
          let x0 = { coq_Fnum = (cond_Zopp sx (Zpos mx)); coq_Fexp = ex } in
          let y0 = { coq_Fnum = (cond_Zopp sy (Zpos my)); coq_Fexp = ey } in
          let { coq_Fnum = mr; coq_Fexp = er } = coq_Fmult radix2 x0 y0 in
          binary_normalize prec emax m mr er
            (coq_Bfma_szero prec emax m x y z)
        | B754_infinity _ -> z
        | B754_nan (_, _) -> build_nan prec emax (fma_nan x y z)
        | B754_finite (sz, mz, ez) ->
          let x0 = { coq_Fnum = (cond_Zopp sx (Zpos mx)); coq_Fexp = ex } in
          let y0 = { coq_Fnum = (cond_Zopp sy (Zpos my)); coq_Fexp = ey } in
          let z0 = { coq_Fnum = (cond_Zopp sz (Zpos mz)); coq_Fexp = ez } in
          let { coq_Fnum = mr; coq_Fexp = er } =
            coq_Fplus radix2 (coq_Fmult radix2 x0 y0) z0
          in
          binary_normalize prec emax m mr er
            (coq_Bfma_szero prec emax m x y z)))

(** val coq_Fdiv_core_binary :
    coq_Z -> coq_Z -> coq_Z -> coq_Z -> coq_Z -> coq_Z ->
    (coq_Z * coq_Z) * location **)

let coq_Fdiv_core_binary prec emax =
  let emin = Z.sub (Z.sub (Zpos (Coq_xI Coq_xH)) emax) prec in
  let fexp = coq_FLT_exp emin prec in
  (fun m1 e1 m2 e2 ->
  let d1 = coq_Zdigits2 m1 in
  let d2 = coq_Zdigits2 m2 in
  let e' = Z.min (fexp (Z.sub (Z.add d1 e1) (Z.add d2 e2))) (Z.sub e1 e2) in
  let s = Z.sub (Z.sub e1 e2) e' in
  let m' = match s with
           | Z0 -> m1
           | Zpos _ -> Z.shiftl m1 s
           | Zneg _ -> Z0 in
  let (q, r) = coq_Zfast_div_eucl m' m2 in
  ((q, e'), (new_location m2 r Coq_loc_Exact)))

(** val coq_Bdiv :
    coq_Z -> coq_Z -> (binary_float -> binary_float -> binary_float) -> mode
    -> binary_float -> binary_float -> binary_float **)

let coq_Bdiv prec emax div_nan m x y =
  match x with
  | B754_zero sx ->
    (match y with
     | B754_infinity sy -> B754_zero (xorb sx sy)
     | B754_finite (sy, _, _) -> B754_zero (xorb sx sy)
     | _ -> build_nan prec emax (div_nan x y))
  | B754_infinity sx ->
    (match y with
     | B754_zero sy -> B754_infinity (xorb sx sy)
     | B754_finite (sy, _, _) -> B754_infinity (xorb sx sy)
     | _ -> build_nan prec emax (div_nan x y))
  | B754_nan (_, _) -> build_nan prec emax (div_nan x y)
  | B754_finite (sx, mx, ex) ->
    (match y with
     | B754_zero sy -> B754_infinity (xorb sx sy)
     | B754_infinity sy -> B754_zero (xorb sx sy)
     | B754_nan (_, _) -> build_nan prec emax (div_nan x y)
     | B754_finite (sy, my, ey) ->
       coq_FF2B prec emax
         (let (p, lz) =
            coq_Fdiv_core_binary prec emax (Zpos mx) ex (Zpos my) ey
          in
          let (mz, ez) = p in
          binary_round_aux prec emax m (xorb sx sy) mz ez lz))

(** val coq_Fsqrt_core_binary :
    coq_Z -> coq_Z -> coq_Z -> coq_Z -> (coq_Z * coq_Z) * location **)

let coq_Fsqrt_core_binary prec emax =
  let emin = Z.sub (Z.sub (Zpos (Coq_xI Coq_xH)) emax) prec in
  let fexp = coq_FLT_exp emin prec in
  (fun m e ->
  let d = coq_Zdigits2 m in
  let e' = Z.min (fexp (Z.div2 (Z.add (Z.add d e) (Zpos Coq_xH)))) (Z.div2 e)
  in
  let s = Z.sub e (Z.mul (Zpos (Coq_xO Coq_xH)) e') in
  let m' = match s with
           | Z0 -> m
           | Zpos _ -> Z.shiftl m s
           | Zneg _ -> Z0 in
  let (q, r) = Z.sqrtrem m' in
  let l =
    if coq_Zeq_bool r Z0
    then Coq_loc_Exact
    else Coq_loc_Inexact (if Z.leb r q then Lt else Gt)
  in
  ((q, e'), l))

(** val coq_Bsqrt :
    coq_Z -> coq_Z -> (binary_float -> binary_float) -> mode -> binary_float
    -> binary_float **)

let coq_Bsqrt prec emax sqrt_nan m x = match x with
| B754_zero _ -> x
| B754_infinity s -> if s then build_nan prec emax (sqrt_nan x) else x
| B754_nan (_, _) -> build_nan prec emax (sqrt_nan x)
| B754_finite (sx, mx, ex) ->
  if sx
  then build_nan prec emax (sqrt_nan x)
  else coq_FF2B prec emax
         (let (p, lz) = coq_Fsqrt_core_binary prec emax (Zpos mx) ex in
          let (mz, ez) = p in binary_round_aux prec emax m false mz ez lz)
