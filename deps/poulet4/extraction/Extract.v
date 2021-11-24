Require Coq.extraction.Extraction.
Require Import Coq.extraction.ExtrOcamlBasic.
Require Import Coq.extraction.ExtrOcamlNativeString.
Require Import Coq.extraction.ExtrOcamlNatInt.

Require Import Coq.Numbers.BinNums.

Require Poulet4.SimplExpr.
Require Poulet4.GenLoc.
Require Poulet4.Syntax.
Require Poulet4.Typed.
Require Poulet4.ConstValue.
Require Poulet4.P4cub.GCL.
Require Poulet4.ToP4cub.
Require Poulet4.P4cub.ToGCL.


Extract Inductive positive => "Bigint.t"
  [ "(fun p -> Bigint.of_zarith_bigint (Z.succ (Z.mul (Z.of_int 2) (Bigint.to_zarith_bigint p))))"
      "(fun p -> Bigint.of_zarith_bigint (Z.mul (Z.of_nat 2) (Bigint.to_zarith_bigint p)))" "(Bigint.of_zarith_bigint (Z.of_nat 1))" ]
  "(fun f2p1 f2p f1 p -> if Z.leq (Bigint.to_zarith_bigint p) (Z.of_nat 1) then f1 () else let (q,r) = Z.div_rem (Bigint.to_zarith_bigint p) (Z.of_int 2) in if Z.equal r (Z.of_nat 0) then f2p (Bigint.of_zarith_bigint q) else f2p1 (Bigint.of_zarith_bigint q))".

Extract Inductive Z => "Bigint.t" [ "(Bigint.of_zarith_bigint (Z.of_nat 0))" "" "(fun z -> Bigint.of_zarith_bigint (Z.neg (Bigint.to_zarith_bigint z)))" ]
  "(fun fO fp fn z -> let nz = (Bigint.to_zarith_bigint z) in let s = Z.sign nz in if s = 0 then fO () else if s > 0 then fp z else fn (Bigint.of_zarith_bigint (Z.neg nz)))".

Extract Inductive N => "Bigint.t" [ "(Bigint.of_zarith_bigint (Z.of_nat 0))" "" ]
  "(fun fO fp n -> if Z.sign (Bigint.to_zarith_bigint n) <= 0 then fO () else fp n)".


Extract Constant SyntaxUtil.dummy_ident => "(fun () -> failwith ""unrealized dummy_ident reached"")".
Extract Constant SimplExpr.to_digit => "(fun x -> Char.chr 20)".
Extract Constant SimplExpr.N_to_string_aux => "(fun x y z -> z)". (* Don't remove: this line informs Coq to not actually extract this function. *)
Extract Constant SimplExpr.N_to_string => "(fun x -> Z.to_string (Bigint.to_zarith_bigint x))".
Extract Constant SimplExpr.add1 => "(fun x -> Bigint.of_zarith_bigint (Z.succ (Bigint.to_zarith_bigint x)))".
Extract Inlined Constant SimplExpr.Nzero => "(Bigint.of_zarith_bigint (Z.of_int 0))".
Extract Inlined Constant BinNat.N.eqb => "Bigint.(=)".
Extract Inlined Constant BinNat.N.add => "Bigint.(+)".
Extract Inlined Constant Nat.add => "(+)".


Separate Extraction Poulet4.Syntax
         Poulet4.Typed Poulet4.SimplExpr
         Poulet4.GenLoc
         Poulet4.ConstValue
         Poulet4.ToP4cub
         Poulet4.P4cub.GCL
         Poulet4.P4cub.ToGCL.
