Require Import Coq.extraction.ExtrOcamlBasic.
Require Import Coq.extraction.ExtrOcamlNativeString.
Require Import Coq.extraction.ExtrOcamlNatInt.
Require Import Petr4.ExtractOcamlBinNumsBigint.
Require Syntax.
Require Extraction.

Cd "extraction/lib/".
Separate Extraction Syntax Typed.
Cd "../../".
