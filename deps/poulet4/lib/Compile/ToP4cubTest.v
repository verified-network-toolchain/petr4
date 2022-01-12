From Poulet4 Require Import P4light.Syntax.P4defs
     P4light.Syntax.Syntax P4light.Examples.SimpleNat
     P4light.Examples.ECMP2 P4light.Examples.MultiProtocol
     Utils.Util.Result Compile.ToP4cub.

Import Result Syntax List ListNotations.

(* The Test Programs*)

(* Test Lemma For simple_nat.p4*)
(* Compute (translate_program Info NoInfo SimpleNat.prog). *)
Lemma simplenat_no_error: Result.is_ok (translate_program Info NoInfo SimpleNat.prog).
Proof.
  compute.
  trivial.
Qed.

(* Compute ECMP2.prog. *)

(* Test lemma for ecmp_2.v *)
(* Compute (translate_program Info NoInfo ECMP2.prog). *)
(* CAVEAT EMPTOR.  I swapped all the "selector" matchkinds in ECMP2.prog for "exact" *)
(* TODO When we add support for arbitrary matchkinds, regenerate ECMP2 so that it uses "selector".  *)
Lemma ecmp2_no_error: Result.is_ok (translate_program Info NoInfo ECMP2.prog).
Proof.
  compute.
  trivial.
Qed.


(* Compute (translate_program Info NoInfo MultiProtocol.prog). *)

Lemma multiprotocol_no_error :
  Result.is_ok (translate_program Info NoInfo MultiProtocol.prog).
Proof.
  compute.
  trivial.
Qed.
