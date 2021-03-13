Require Import Coq.extraction.ExtrOcamlBasic.
Require Import Coq.extraction.ExtrOcamlNativeString.
Require Import Coq.extraction.ExtrOcamlNatInt.
Require Import Petr4.ExtractOcamlBinNumsBigint.
Require Petr4.Syntax.
Require Petr4.Typed.
Require Petr4.Trans.
Require Extraction.

Extract Constant Trans.to_digit => "(fun x -> Char.chr 20)".
Extract Constant Trans.to_N_aux => "(fun x y z -> z)".
Extract Constant Trans.N_to_string => "(fun x -> Z.to_string (Bigint.to_zarith_bigint x))".
Extract Constant Trans.add1 => "(fun x -> Bigint.of_zarith_bigint (Z.succ (Bigint.to_zarith_bigint x)))".
Extract Inlined Constant Trans.Nzero => "(Bigint.of_zarith_bigint Z.zero)".

Cd "lib".
Separate Extraction Syntax Typed Trans.
Cd "..".
