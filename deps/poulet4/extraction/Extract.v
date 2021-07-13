Require Coq.extraction.Extraction.
Require Import Coq.extraction.ExtrOcamlBasic.
Require Import Coq.extraction.ExtrOcamlNativeString.
Require Import Coq.extraction.ExtrOcamlNatInt.

Require Import Coq.Numbers.BinNums.

Extract Inductive positive => "Bigint.t"
  [ "(fun p -> Bigint.of_zarith_bigint (Z.succ (Z.mul (Z.of_int 2) (Bigint.to_zarith_bigint p))))"
      "(fun p -> Bigint.of_zarith_bigint (Z.mul (Z.of_int 2) (Bigint.to_zarith_bigint p)))" "(Bigint.of_zarith_bigint Z.one)" ]
  "(fun f2p1 f2p f1 p -> if Z.leq (Bigint.to_zarith_bigint p) Z.one then f1 () else let (q,r) = Z.div_rem (Bigint.to_zarith_bigint p) (Z.of_int 2) in if Z.equal r Z.zero then f2p (Bigint.of_zarith_bigint q) else f2p1 (Bigint.of_zarith_bigint q))".

Extract Inductive Z => "Bigint.t" [ "(Bigint.of_zarith_bigint Z.zero)" "" "(fun z -> Bigint.of_zarith_bigint (Z.neg (Bigint.to_zarith_bigint z)))" ]
  "(fun fO fp fn z -> let nz = (Bigint.to_zarith_bigint z) in let s = Z.sign nz in if s = 0 then fO () else if s > 0 then fp z else fn (Bigint.of_zarith_bigint (Z.neg nz)))".

Extract Inductive N => "Bigint.t" [ "(Bigint.of_zarith_bigint Z.zero)" "" ]
  "(fun fO fp n -> if Z.sign (Bigint.to_zarith_bigint n) <= 0 then fO () else fp n)".

Require Poulet4.SimplExpr.
Require Poulet4.GenLoc.

Extract Constant SyntaxUtil.dummy_ident => "(fun () -> failwith ""unrealized dummy_ident reached"")".
Extract Constant SimplExpr.to_digit => "(fun x -> Char.chr 20)".
Extract Constant SimplExpr.N_to_string_aux => "(fun x y z -> z)". (* Don't remove: this line informs Coq to not actually extract this function. *)
Extract Constant SimplExpr.N_to_string => "(fun x -> Z.to_string (Bigint.to_zarith_bigint x))".
Extract Constant SimplExpr.add1 => "(fun x -> Bigint.of_zarith_bigint (Z.succ (Bigint.to_zarith_bigint x)))".
Extract Inlined Constant SimplExpr.Nzero => "(Bigint.of_zarith_bigint Z.zero)".
Extract Inlined Constant BinNat.N.eqb => "Bigint.(=)".
Extract Inlined Constant BinNat.N.add => "Bigint.(+)".
Extract Inlined Constant Nat.add => "(+)".

Require Poulet4.Syntax.
Require Poulet4.Typed.


Separate Extraction Poulet4.Syntax
         Poulet4.Typed Poulet4.SimplExpr
         Poulet4.GenLoc.
