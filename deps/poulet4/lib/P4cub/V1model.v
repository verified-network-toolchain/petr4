
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

Definition externs : ToGCL.model :=
  [("_", [("mark_to_drop", G.GAssign (E.TBit (BinNat.N.of_nat 9)) "standard_metadata.egress_spec" (BV.bit (Some 9) 511));
         ("clone3", G.GSkip);
         ("assert", G.GAssert (F.LVar "check"));
         ("assume", G.GAssume (F.LVar "check"));
         ("hash", G.GSkip);
         ("truncate", G.GSkip);
         ("random", G.GSkip);
         ("crc_poly", G.GSkip);
         ("digest", G.GSkip)
   ]);
  ("packet_in", [("extract", G.GSkip)]);
  ("counter", [("count", G.GSkip)]);
  ("direct_counter", [("count", G.GSkip)]);
  ("register", [("read", G.GSkip); ("write", G.GSkip)]);
  ("meter", [("meter", G.GSkip); ("execute_meter", G.GSkip)]);
  ("direct_meter", [("direct_meter", G.GSkip); ("read", G.GSkip)])
  ].

Definition cub_seq {tags_t : Type} (i : tags_t) (statements : list (ST.s tags_t)) : ST.s tags_t  :=
  let seq := fun s1 s2 => ST.SSeq s1 s2 i in
  List.fold_right seq (ST.SSkip i) statements.

Definition det_fwd_asst {tags_t : Type} (i : tags_t) :=
  let assertion :=
      E.EBop E.TBool
             E.NotEq
             (E.EVar (E.TBit 9%N) "standard_metadata.egress_spec" i)
             (E.EBit 9%N 0%Z i) i
  in
  let paramargs := [("check", PAIn assertion)] in
  let arrowE := {| paramargs := paramargs ; rtrns := None |} in
  ST.SExternMethodCall "_" "assert" [] arrowE i.

Definition t_arg {tags_t : Type} (i : tags_t) (dir : (E.e tags_t) -> paramarg (E.e tags_t) (E.e tags_t)) typ var :=
  (var, dir (E.EVar typ var i)).
Definition s_arg {tags_t : Type} (i : tags_t) dir var stype :=
  t_arg i dir (E.TVar stype) var.

Definition pipeline {tags_t : Type} (i : tags_t) (htype mtype : E.t) (parser v_check ingress egress c_check deparser : string) : ST.s tags_t :=
  let ext_args := [] in
  let pargs := [
        s_arg i PADirLess "packet_in"           "b";
        t_arg i PAOut      htype                "parsedHdr";
        t_arg i PAInOut    mtype                "meta";
        s_arg i PAInOut    "standard_metadata_t" "standard_metadata"] in
  let vck_args := [
        t_arg i PAInOut htype "hdr";
        t_arg i PAInOut mtype "meta"] in
  let ing_args := [
        t_arg i PAInOut htype "hdr";
        t_arg i PAInOut mtype "meta";
        s_arg i PAInOut "standard_metadata_t" "standard_metadata"] in
  let egr_args := [
        t_arg i PAInOut htype "hdr";
        t_arg i PAInOut mtype "meta";
        s_arg i PAInOut "standard_metadata_t" "standard_metadata"] in
  let cck_args := [
        t_arg i PAInOut htype "hdr";
        t_arg i PAInOut mtype "meta"] in
  let dep_args := [
        s_arg i PADirLess "packet_out" "b";
      t_arg i PAIn htype "hdr"] in
  cub_seq i [
        ST.SApply parser  ext_args pargs    i
        (* ST.SApply v_check ext_args vck_args i; *)
        (* ST.SApply ingress ext_args ing_args i; *)
        (* ST.SApply egress  ext_args egr_args i; *)
        (* det_fwd_asst i *)
        (* ST.SApply   c_check  ext_args cck_args NoInfo; *)
        (* ST.SApply   deparser ext_args dep_args NoInfo *)
    ].

Definition package {tags_t : Type} (i : tags_t) (types : list E.t) (cargs : E.constructor_args tags_t) : result (ST.s tags_t) :=
  match List.map snd cargs with
  | [E.CAName p; E.CAName vc; E.CAName ing; E.CAName egr; E.CAName cc; E.CAName d] =>
    match types with
    | [htype; mtype] =>
      ok (pipeline i htype mtype p vc ing egr cc d)
    | [] =>
      error "no type arguments provided:("
    | _ =>
      error "ill-formed type arguments to V1Switch instantiation."
    end
  | _ =>
    error "ill-formed constructor arguments to V1Switch instantiation."
  end.

Definition gcl_from_p4cub {tags_t : Type} (d : tags_t) instr gas unroll p4cub : result ToGCL.target :=
  let arrowtype := ({|paramargs:=[("check", PAIn E.TBool)]; rtrns:=None|} : Expr.arrowT) in
  let assume_decl := TopDecl.TPExtern "_" [] [] [("assume", ([], arrowtype))] d in
  let p4cub_instrumented := ToP4cub.add_extern tags_t p4cub assume_decl in
  ToGCL.from_p4cub tags_t instr gas unroll externs (package d) p4cub.
