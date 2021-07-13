Require Coq.extraction.Extraction.
(* Require Import Coq.extraction.ExtrOcamlBasic. *)
(* Require Import ExtrOcamlString. *)
Require Import Coq.extraction.ExtrOcamlNatInt.
(* Require Import Coq.extraction.ExtrOcamlZInt. *)
Require Import Coq.Numbers.BinNums.
(* Standard lib *)

(* Datatypes *)

Extract Inductive positive => "Bigint.t"
  [ "(fun p -> Bigint.of_zarith_bigint (Big_int_Z.succ_big_int (Big_int_Z.mult_big_int (Big_int_Z.big_int_of_int 2) (Bigint.to_zarith_bigint p))))"
      "(fun p -> Bigint.of_zarith_bigint (Big_int_Z.mult_big_int (Big_int_Z.big_int_of_int 2) (Bigint.to_zarith_bigint p)))" "(Bigint.of_zarith_bigint Big_int_Z.unit_big_int)" ]
  "(fun f2p1 f2p f1 p -> if Big_int_Z.le_big_int (Bigint.to_zarith_bigint p) Big_int_Z.unit_big_int then f1 () else let (q,r) = Big_int_Z.quomod_big_int (Bigint.to_zarith_bigint p) (Big_int_Z.big_int_of_int 2) in if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p (Bigint.of_zarith_bigint q) else f2p1 (Bigint.of_zarith_bigint q))".

Extract Inductive Z => "Bigint.t" [ "(Bigint.of_zarith_bigint Big_int_Z.zero_big_int)" "" "(fun z -> Bigint.of_zarith_bigint (Big_int_Z.minus_big_int (Bigint.to_zarith_bigint z)))" ]
  "(fun fO fp fn z -> let nz = (Bigint.to_zarith_bigint z) in let s = Big_int_Z.sign_big_int nz in if s = 0 then fO () else if s > 0 then fp z else fn (Bigint.of_zarith_bigint (Big_int_Z.minus_big_int nz)))".

Extract Inductive N => "Bigint.t" [ "(Bigint.of_zarith_bigint Big_int_Z.zero_big_int)" "" ]
  "(fun fO fp n -> if Big_int_Z.sign_big_int (Bigint.to_zarith_bigint n) <= 0 then fO () else fp n)".
Require Poulet4.SimplExpr.
Require Poulet4.GenLoc.
Require Poulet4_Ccomp.CComp.

Extract Constant SyntaxUtil.dummy_ident => "(fun () -> failwith ""unrealized dummy_ident reached"")".
Extract Constant SimplExpr.to_digit => "(fun x -> Char.chr 20)".
Extract Constant SimplExpr.N_to_string_aux => "(fun x y z -> z)". (* Don't remove: this line informs Coq to not actually extract this function. *)
Extract Constant SimplExpr.N_to_string => "(fun x -> Big_int_Z.string_of_big_int (Bigint.to_zarith_bigint x))".
Extract Constant SimplExpr.add1 => "(fun x -> Bigint.of_zarith_bigint (Big_int_Z.succ_big_int (Bigint.to_zarith_bigint x)))".
Extract Inlined Constant SimplExpr.Nzero => "(Bigint.of_zarith_bigint Big_int_Z.zero_big_int)".
Extract Inlined Constant BinNat.N.eqb => "Bigint.(=)".
Extract Inlined Constant BinNat.N.add => "Bigint.(+)".
Extract Inlined Constant Nat.add => "(+)".
(* TODO: figure out what is the correct reference of PrintClight *)
Extract Constant CComp.print_Clight => "PrintClight.print_if".

Extraction Blacklist List String Int Z.
(* Set Extraction AccessOpaque. *)

Cd "extraction/lib/".
Separate Extraction Poulet4_Ccomp.CComp.
Cd "../../".
