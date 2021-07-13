Require Coq.extraction.Extraction.
Require Import Coq.extraction.ExtrOcamlBasic.
Require Import Coq.extraction.ExtrOcamlNativeString.
Require Import Coq.extraction.ExtrOcamlNatInt.

Require Import Coq.Numbers.BinNums.
(* Standard lib *)
Require Import Coq.extraction.ExtrOcamlString.
Require Import ExtrOcamlBasic.

(* Datatypes *)
Extract Inlined Constant Datatypes.fst => "fst".
Extract Inlined Constant Datatypes.snd => "snd".

Extract Inductive positive => "Bigint.t"
  [ "(fun p->Bigint.(of_int 1 + (of_int 2) * p))"
      "(fun p->Bigint.(of_int 2*p))" "1" ]
  "(fun f2p1 f2p f1 p -> if Bigint.(p<=one) then f1 () else if Bigint.(p mod of_int 2 = 0) then f2p Bigint.(p/2) else f2p1 Bigint.(p/2))".

Extract Inductive Z => "Bigint.t" [ "Bigint.zero" "" "Bigint.(~-)" ]
  "(fun f0 fp fn z -> if z=Bigint.zero then f0 () else if Bigint.(z>zero) then fp z else fn Bigint.(-z))".

Extract Inductive N => "Bigint.t" [ "0" "" ]
  "(fun f0 fp n -> if n=0 then f0 () else fp n)".

Require Poulet4.SimplExpr.
Require Poulet4.GenLoc.
Require Poulet4_Ccomp.CComp.

Extract Constant SyntaxUtil.dummy_ident => "(fun () -> failwith ""unrealized dummy_ident reached"")".
Extract Constant SimplExpr.to_digit => "(fun x -> Char.chr 20)".
Extract Constant SimplExpr.N_to_string_aux => "(fun x y z -> z)". (* Don't remove: this line informs Coq to not actually extract this function. *)
Extract Constant SimplExpr.N_to_string => "(fun x -> Z.to_string (Bigint.to_zarith_bigint x))".
Extract Constant SimplExpr.add1 => "(fun x -> Bigint.of_zarith_bigint (Z.succ (Bigint.to_zarith_bigint x)))".
Extract Inlined Constant SimplExpr.Nzero => "(Bigint.of_zarith_bigint Z.zero)".
Extract Inlined Constant BinNat.N.eqb => "Bigint.(=)".
Extract Inlined Constant BinNat.N.add => "Bigint.(+)".
Extract Inlined Constant Nat.add => "(+)".
(* TODO: figure out what is the correct reference of PrintClight *)
Extract Constant CComp.print_Clight => "PrintClight.print_if".


Cd "extraction/lib/".
Separate Extraction Poulet4_Ccomp.CComp.
Cd "../../".
