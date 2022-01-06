Require Import Poulet4.P4defs.
Require Import Poulet4.Syntax.
Require Import Poulet4.P4cub.Util.Result.
Require Import Poulet4.ToP4cub.

Import Result Syntax List ListNotations.

(* The Test Programs*)

Require Import Poulet4.LightExamples.SimpleNat.
Require Import Poulet4.LightExamples.ECMP2.
Require Import Poulet4.LightExamples.Flowlet.
Require Import Poulet4.LightExamples.MultiProtocol.
Require Import Poulet4.LightExamples.LinearRoad.
Require Import Poulet4.LightExamples.HeavyHitter.
Require Import Poulet4.LightExamples.Netchain.
Require Import Poulet4.LightExamples.Hula.


(**                       NOTE
 * Don't comment out these test cases if they break.
 * These are regression tests, which maintain code quality
 * Commenting them out without fixing the problems is the same
 * as breaking the build.
 **)

(* Test Lemma For simple_nat.p4*)
(* Compute (preprocess Info NoInfo SimpleNat.prog). *)
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

(* CAVEAT EMPTOR -- had to manually add type-widths to bitvectors *)
Definition cub_flowlet := translate_program Info NoInfo Flowlet.prog.
(* Compute cub_flowlet. *)
Lemma flowlet_no_error: Result.is_ok cub_flowlet.
Proof. compute; trivial. Qed.

(* Compute (translate_program Info NoInfo MultiProtocol.prog). *)

Lemma multiprotocol_no_error :
  Result.is_ok (translate_program Info NoInfo MultiProtocol.prog).
Proof.
  compute.
  trivial.
Qed.

(* Linearroad *)
Definition p4cub_linearroad := ToP4cub.translate_program Info NoInfo LinearRoad.prog.
Lemma linearroad_no_error : Result.is_ok p4cub_linearroad.
Proof. compute; trivial. Qed.

(* Heavy Hitter 1 *)
Definition p4cub_heavy_hitter := ToP4cub.translate_program Info NoInfo HeavyHitter.prog.
(* Compute HeavyHitter.prog. *)
(* Compute p4cub_heavy_hitter. *)
Lemma heavy_hitter_no_error: Result.is_ok p4cub_heavy_hitter.
Proof. compute; trivial. Qed.

(* Netchain *)
Definition p4cub_netchain := ToP4cub.translate_program Info NoInfo Netchain.prog.
(* Compute (preprocess Info NoInfo Netchain.prog). *)
(* Compute (aeval (ToP4cub.inline_types_prog Info (Program [InlineTypeDecl.overlay_t NoInfo; *)
(*                                                  InlineTypeDecl.headers NoInfo]))). *)
(* Compute p4cub_netchain. *)
Lemma netchain_no_error: Result.is_ok p4cub_netchain.
Proof. compute; trivial. Qed.

(* HULA *)
Definition p4cub_hula := ToP4cub.translate_program Info NoInfo Hula.prog.
Lemma hula_no_error: Result.is_ok p4cub_hula.
Proof. compute; trivial. Qed.
