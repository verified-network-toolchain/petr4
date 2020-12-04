Require Coq.extraction.Extraction.
Require Import Coq.ZArith.ZArith.

Extract Inductive positive => "Bigint.t"
  [ "(fun p->Bigint.(of_int 1 + (of_int 2) * p))"
      "(fun p->Bigint.(of_int 2*p))" "1" ]
  "(fun f2p1 f2p f1 p -> if Bigint.(p<=one) then f1 () else if Bigint.(p mod of_int 2 = 0) then f2p Bigint.(p/2) else f2p1 Bigint.(p/2))".

Extract Inductive Z => "Bigint.t" [ "Bigint.zero" "" "Bigint.(~-)" ]
  "(fun f0 fp fn z -> if z=Bigint.zero then f0 () else if Bigint.(z>zero) then fp z else fn Bigint.(-z))".

Extract Inductive N => "Bigint.t" [ "0" "" ]
  "(fun f0 fp n -> if n=0 then f0 () else fp n)".
