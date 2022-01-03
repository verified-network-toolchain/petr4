Require Import Poulet4.P4defs.
Require Import Poulet4.Syntax.
Require Import Poulet4.P4cub.Util.Result.
Require Import Poulet4.ToP4cubTest.
Require Import Poulet4.P4cub.Envn.
Require Import Poulet4.P4cub.BigStep.InstUtil.
Require Import Poulet4.P4cub.BigStep.BSPacket.
Require Import Poulet4.P4cub.TableInstr.
Require Import Poulet4.P4cub.V1model.
Require Poulet4.P4cub.GCL.
Require Poulet4.P4cub.ToGCL.
Require Poulet4.P4cub.Inline.
Import Result ResultNotations Syntax List ListNotations.


(* Import the Test programs *)
Require Import Poulet4.LightExamples.SimpleNat.
Require Import Poulet4.LightExamples.ECMP2.
Require Import Poulet4.LightExamples.MultiProtocol.
Require Import Poulet4.LightExamples.Flowlet.
Require Import Poulet4.LightExamples.LinearRoad.

Module GCL := GCL.GCL.
Module BV := ToGCL.BV.
Module E := GCL.E.
Module ST := Stmt.
Definition d := NoInfo.


(**                       NOTE
 * Don't comment out these test cases if they break.
 * These are regression tests, which maintain code quality
 * Commenting them out without fixing the problems is the same
 * as breaking the build.
 **)

Definition p4cub_simple_nat := ToP4cub.translate_program Info NoInfo SimpleNat.prog.
(* Compute p4cub_simple_nat. *)

Definition simple_nat_test_case :=
  let* sn := p4cub_simple_nat in
  let externs := V1model.externs in
  ToGCL.from_p4cub Info TableInstr.instr 1000 externs (V1model.package NoInfo) sn.

Definition simple_nat_inline_test : result (Inline.t Info) :=
  let* sn := p4cub_simple_nat in
  ToGCL.inline_from_p4cub Info 1000 externs (V1model.package NoInfo) sn.

(* Compute p4cub_simple_nat. *)
(* Compute simple_nat_inline_test. *)
(* Compute simple_nat_test_case. *)

Lemma simple_nat_test1 : is_ok simple_nat_test_case.
Proof. compute. trivial. Qed.

(* ECMP2 *)
Definition p4cub_ecmp2 := ToP4cub.translate_program Info NoInfo ECMP2.prog.

Definition ecmp2_test_case :=
  let* sn := p4cub_ecmp2 in
  let externs := V1model.externs in
  ToGCL.from_p4cub Info TableInstr.instr 1000 externs (V1model.package NoInfo) sn.

Compute p4cub_ecmp2.
Compute ecmp2_test_case.

Lemma ecmp2_test : is_ok ecmp2_test_case.
Proof. compute. trivial. Qed.

(* CAVEAT EMPTOR -- had to manually add type-widths to bitvectors *)
Definition p4cub_flowlet := ToP4cub.translate_program Info NoInfo Flowlet.prog.
Definition gcl_flowlet :=
  let* sn := p4cub_flowlet in
  let externs := V1model.externs in
  ToGCL.from_p4cub Info TableInstr.instr 1000 externs (V1model.package NoInfo) sn.

(* Compute cub_flowlet. *)
(* Compute gcl_flowlet. *)
Lemma flowlet_no_error: Result.is_ok gcl_flowlet.
Proof. compute; trivial. Qed.

(* 07-Multi-Protocol *)

Definition p4cub_multiprotocol := ToP4cub.translate_program Info NoInfo MultiProtocol.prog.

Definition multiprotocol_test_case :=
  let* sn := p4cub_multiprotocol in
  let externs := V1model.externs in
  ToGCL.from_p4cub Info TableInstr.instr 1000 externs (V1model.package NoInfo) sn.

(* Compute p4cub_multiprotocol. *)
(* Compute multiprotocol_test_case. *)

Lemma multiprotocol_test : is_ok multiprotocol_test_case.
Proof. compute. trivial. Qed.


(* LinearRoad *)

Definition p4cub_linearroad := ToP4cub.translate_program Info NoInfo LinearRoad.prog.

Definition inline_linearroad :=
  let* ctx := p4cub_linearroad in
  ToGCL.inline_from_p4cub Info 1000 externs (V1model.package NoInfo) ctx.


Definition linearroad_test_case :=
  let* sn := p4cub_linearroad in
  let externs := V1model.externs in
  ToGCL.from_p4cub Info TableInstr.instr 1000 externs (V1model.package NoInfo) sn.

(* Compute inline_linearroad. *)
(* Compute linearroad_test_case. *)

Lemma linearroad_test : is_ok linearroad_test_case.
Proof. compute; trivial. Qed.

(* heavy_hitter_1 *)

Definition heavy_hitter_test_case :=
  let* hh := ToP4cubTest.p4cub_heavy_hitter in
  ToGCL.from_p4cub Info TableInstr.instr 1000 V1model.externs (V1model.package NoInfo) hh.

Lemma heavy_hitter_test: is_ok heavy_hitter_test_case.
Proof. compute; trivial. Qed.


(* netchain *)

Definition netchain_test_case :=
  let* nc := ToP4cubTest.p4cub_netchain in
  ToGCL.from_p4cub Info TableInstr.instr 1000 V1model.externs (V1model.package NoInfo) nc.

Print TypHeader.

Lemma netchain_test: is_ok netchain_test_case.
Proof. compute; trivial. Qed.


(* hula *)
Definition hula_test_case :=
  let* hula := ToP4cubTest.p4cub_hula in
  ToGCL.from_p4cub Info TableInstr.instr 1000 V1model.externs (V1model.package NoInfo) hula.

Lemma hula_test: is_ok hula_test_case.
Proof. compute; trivial. Qed.
