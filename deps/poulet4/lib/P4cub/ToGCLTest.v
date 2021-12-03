Require Import Poulet4.P4defs.
Require Import Poulet4.Syntax.
Require Import Poulet4.SimpleNat.
Require Import Poulet4.P4cub.Util.Result.
Require Import Poulet4.ToP4cubTest.
Require Import Poulet4.P4cub.Envn.
Require Import Poulet4.P4cub.BigStep.InstUtil.
Require Import Poulet4.P4cub.BigStep.BSPacket.
Require Import Poulet4.P4cub.TableInstr.
Require Import Poulet4.P4cub.V1model.
Require Poulet4.P4cub.GCL.
Require Poulet4.P4cub.ToGCL.
Import Result ResultNotations SimpleNat Syntax List ListNotations.


Module GCL := GCL.GCL.
Module BV := ToGCL.BV.
Module E := GCL.E.
Module ST := Stmt.
Definition d := NoInfo.

Definition p4cub_simple_nat := ToP4cub.translate_program Info NoInfo ToP4cubTest.test.
(* Compute p4cub_simple_nat. *)


Definition simple_nat_test_case :=
  let* sn := p4cub_simple_nat in
  let externs := V1model.externs in
  ToGCL.p4cub_to_gcl Info TableInstr.instr 1000 externs V1model.package sn.

(* Compute simple_nat_test_case. *)

Lemma simple_nat_test1 : is_ok simple_nat_test_case.
Proof. compute. trivial. Qed.
