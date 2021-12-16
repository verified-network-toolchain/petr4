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
Import Result ResultNotations Syntax List ListNotations.


(* Import the Test programs *)
Require Import Poulet4.LightExamples.SimpleNat.
Require Import Poulet4.LightExamples.ECMP2.
Require Import Poulet4.LightExamples.MultiProtocol.


Module GCL := GCL.GCL.
Module BV := ToGCL.BV.
Module E := GCL.E.
Module ST := Stmt.
Definition d := NoInfo.

Import SimpleNat.

(* Definition p4cub_simple_nat := ToP4cub.translate_program Info NoInfo SimpleNat.prog.
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

(* Compute p4cub_ecmp2. *)
(* Compute ecmp2_test_case. *)

Lemma ecmp2_test : is_ok ecmp2_test_case.
Proof. compute. trivial. Qed.


(* 07-Multi-Protocol *)

Definition p4cub_multiprotocol := ToP4cub.translate_program Info NoInfo MultiProtocol.prog.

Definition multiprotocol_test_case :=
  let* sn := p4cub_multiprotocol in
  let externs := V1model.externs in
  ToGCL.from_p4cub Info TableInstr.instr 1000 externs (V1model.package NoInfo) sn.

(* Compute p4cub_multiprotocol. *)
(* Compute multiprotocol_test_case. *)

Lemma multiprotocol_test : is_ok multiprotocol_test_case.
Proof. compute. trivial. Qed. *)
