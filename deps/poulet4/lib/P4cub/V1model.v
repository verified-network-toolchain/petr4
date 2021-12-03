Require Import Poulet4.P4defs.
Require Import Poulet4.P4cub.Util.Result.
Require Import Poulet4.P4cub.Envn.
Require Poulet4.P4cub.GCL.
Require Poulet4.P4cub.ToGCL.
Import Result ResultNotations Syntax List ListNotations String.
Open Scope string_scope.

Module G := GCL.GCL.
Module F := GCL.Form.
Module BV := GCL.BitVec.
Module E := GCL.E.
Module ST := Stmt.
Definition d := NoInfo.

Definition externs : ToGCL.model Info :=
  [("_", [("mark_to_drop",  G.GAssign _ (E.TBit (BinNat.N.of_nat 1)) "standard_metadata.egress_spec" (BV.bit _ 1 1 d) d);
         ("clone3", G.GSkip _ NoInfo)
   ])
  ].

Definition cub_seq (statements : list (ST.s Info)) : ST.s Info  :=
  let seq := fun s1 s2 => ST.SSeq s1 s2 NoInfo in
  List.fold_right seq (ST.SSkip NoInfo) statements.

Definition t_arg (dir : (E.e Info) -> paramarg (E.e Info) (E.e Info)) typ var := (var, dir (E.EVar typ var NoInfo)).
Definition s_arg dir var stype :=
  t_arg dir (E.TVar stype) var.

Definition pipeline (htype mtype : E.t) (parser v_check ingress egress c_check deparser : string) : ST.s Info :=
  let ext_args := [] in
  let pargs := [
        s_arg PADirLess "packet_in"           "b";
        t_arg PAOut      htype                "parsedHdr";
        t_arg PAInOut    mtype                "meta";
        s_arg PAInOut    "standard_metdata_t" "standard_metadata"] in
  let vck_args := [
        t_arg PAInOut htype "hdr";
        t_arg PAInOut mtype "meta"] in
  let ing_args := [
        t_arg PAInOut htype "hdr";
        t_arg PAInOut mtype "meta";
        s_arg PAInOut "standard_metadata_t" "standard_metadata"] in
  let egr_args := [
        t_arg PAInOut htype "hdr";
        t_arg PAInOut mtype "meta";
        s_arg PAInOut "standard_metadata_t" "standard_metadata"] in
  let cck_args := [
        t_arg PAInOut htype "hdr";
        t_arg PAInOut mtype "meta"] in
  let dep_args := [
        s_arg PADirLess "packet_out" "b";
        t_arg PAIn htype "hdr"] in
  cub_seq [
        (* ST.PApply _ parser   ext_args pargs    NoInfo; *)
        (* ST.SApply   v_check  ext_args vck_args NoInfo; *)
        ST.SApply   ingress  ext_args ing_args NoInfo;
        ST.SApply   egress   ext_args egr_args NoInfo
        (* ST.SApply   c_check  ext_args cck_args NoInfo; *)
        (* ST.SApply   deparser ext_args dep_args NoInfo *)
    ].

Definition package (types : list E.t) (cargs : E.constructor_args Info) : result (ST.s Info) :=
  match List.map snd cargs with
  | [E.CAName p; E.CAName vc; E.CAName ing; E.CAName egr; E.CAName cc; E.CAName d] =>
    match types with
    | [htype; mtype] =>
      ok (pipeline htype mtype p vc ing egr cc d)
    | [] =>
      error "no type arguments provided:("
    | _ =>
      error "ill-formed type arguments to V1Switch instantiation."
    end
  | _ =>
    error "ill-formed constructor arguments to V1Switch instantiation."
  end.
