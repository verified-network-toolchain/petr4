Require Coq.extraction.Extraction.
Require Import Coq.Numbers.BinNums.

Extract Inductive positive => "Bigint.t"
  [ "(fun p -> Bigint.of_zarith_bigint (Z.succ (Z.mul (Z.of_int 2) (Bigint.to_zarith_bigint p))))"
      "(fun p -> Bigint.of_zarith_bigint (Z.mul (Z.of_int 2) (Bigint.to_zarith_bigint p)))" "(Bigint.of_zarith_bigint Z.one)" ]
  "(fun f2p1 f2p f1 p -> if Z.leq (Bigint.to_zarith_bigint p) Z.one then f1 () else let (q,r) = Z.div_rem (Bigint.to_zarith_bigint p) (Z.of_int 2) in if Z.equal r Z.zero then f2p (Bigint.of_zarith_bigint q) else f2p1 (Bigint.of_zarith_bigint q))".

Extract Inductive Z => "Bigint.t" [ "(Bigint.of_zarith_bigint Z.zero)" "" "(fun z -> Bigint.of_zarith_bigint (Z.neg (Bigint.to_zarith_bigint z)))" ]
  "(fun fO fp fn z -> let nz = (Bigint.to_zarith_bigint z) in let s = Z.sign nz in if s = 0 then fO () else if s > 0 then fp z else fn (Bigint.of_zarith_bigint (Z.neg nz)))".

Extract Inductive N => "Bigint.t" [ "(Bigint.of_zarith_bigint Z.zero)" "" ]
  "(fun fO fp n -> if Z.sign (Bigint.to_zarith_bigint n) <= 0 then fO () else fp n)".
