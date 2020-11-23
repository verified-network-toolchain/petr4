Require Import Coq.extraction.ExtrOcamlBasic.
Require Import Coq.extraction.ExtrOcamlString.
Require Import Coq.extraction.ExtrOcamlNatInt.
Require Syntax.
Require Extraction.

Extract Constant CamlString.caml_string => "string".
Extract Constant CamlString.caml_string_cmp =>
  "(fun x y -> let c = String.compare x y in
               if c < 0 then LT
               else if c = 0 then EQ
               else if c > 0 then GT)".
Extract Constant CamlString.caml_string_eqb => "(=)".
Extract Constant CamlString.caml_string_of_chars =>
  "(fun cs -> String.init (List.length cs) (fun n -> List.nth n cs)".

Cd "extraction/lib/".
Separate Extraction Syntax.
Cd "../../".
