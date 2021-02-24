Require Import Coq.extraction.ExtrOcamlBasic.
Require Import Coq.extraction.ExtrOcamlNativeString.
Require Import Coq.extraction.ExtrOcamlNatInt.
Require Import Petr4.ExtractOcamlBinNumsBigint.
Require Petr4.Syntax.
Require Petr4.Typed.
Require Extraction.

Cd "lib".
Separate Extraction Syntax Typed.
Cd "..".
