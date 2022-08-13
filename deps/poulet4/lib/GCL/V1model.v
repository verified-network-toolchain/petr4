Set Warnings "-custom-entry-overridden".
From Poulet4 Require Import P4light.Syntax.P4defs
     Monads.Result Utils.Envn GCL.GCL GCL.ToGCL.
Import Result ResultNotations Syntax List ListNotations String.
Open Scope string_scope.

Module G := GCL.GCL.
Module F := GCL.Form.
Module BV := GCL.BitVec.
Module E := GCL.E.
Module ST := Stmt.

Definition externs : ToGCL.model :=
  [("_", [("mark_to_drop",  G.GAssign (E.TBit (BinNat.N.of_nat 9)) "standard_metadata.egress_spec" (BV.bit (Some 9%nat) 511));
         ("clone3", G.GSkip);
         ("assert", G.GAssert (F.LVar "check"));
         ("assume", G.GAssume (F.LVar "check"));
         ("hash", G.GSkip);
         ("truncate", G.GSkip);
         ("random", G.GSkip);
         ("crc_poly", G.GSkip);
         ("digest", G.GSkip)
   ]);
  ("packet_in", [("extract", G.GAssign (E.TBit 1%N) "hdr.is_valid" (BV.bit (Some 1%nat) 1))]);
  ("counter", [("count", G.GSkip)]);
  ("direct_counter", [("count", G.GSkip)]);
  ("register", [("read", G.GSkip); ("write", G.GSkip)]);
  ("meter", [("meter", G.GSkip); ("execute_meter", G.GSkip)]);
  ("direct_meter", [("direct_meter", G.GSkip); ("read", G.GSkip)])
  ].

Definition cub_seq (statements : list ST.s): ST.s :=
  List.fold_right ST.Seq ST.Skip statements.

Definition det_fwd_asst   :=
  let assertion :=
      E.Bop E.TBool
             E.NotEq
             (E.Var (E.TBit 9%N) "standard_metadata.egress_spec" 0)
             (E.Bit 9%N 0%Z)
  in
  let paramargs := [(*check*) PAIn assertion] in
  ST.Call (ST.Method "_" "assert" [] None) paramargs.

Definition t_arg (dir : E.e -> paramarg E.e E.e) typ var :=
  (var, dir (E.Var typ var 0)).
Definition s_arg  dir var stype :=
  t_arg dir (E.TVar stype) var.

Definition pipeline   (htype mtype : E.t) (parser v_check ingress egress c_check deparser : string) : ST.s  :=
  let ext_args := ["packet_in"] in
  let pargs := [
        t_arg PAOut      htype                "parsedHdr";
        t_arg PAInOut    mtype                "meta";
        s_arg PAInOut    "standard_metadata_t" 0 (* TODO: "standard_metadata" should be inlined in p4cub *)] in
  let vck_args := [
        t_arg PAInOut htype "hdr";
        t_arg PAInOut mtype "meta"] in
  let ing_args := [
        t_arg PAInOut htype "hdr";
        t_arg PAInOut mtype "meta";
        s_arg PAInOut "standard_metadata_t" 0 (* TODO: "standard_metadata" should be inlined in p4cub *)] in
  let egr_args := [
        t_arg PAInOut htype "hdr";
        t_arg PAInOut mtype "meta";
        s_arg PAInOut "standard_metadata_t" 0 (* TODO: "standard_metadata" should be inlined in p4cub *)] in
  let cck_args := [
        t_arg PAInOut htype "hdr";
        t_arg PAInOut mtype "meta"] in
  let dep_ext_args := [ "packet_out" ; "b" ] in
  let dep_args := [ t_arg PAIn htype "hdr"] in
  cub_seq [
        ST.Apply parser  ext_args (map snd pargs) ;
          (* ST.Apply v_check ext_args vck_args i; *)
          ST.Conditional
            (E.Var E.TBool ("_state$accept$next") 0)
            (cub_seq [
                       ST.Apply ingress ext_args (map snd ing_args)
                       ; ST.Apply egress  ext_args (map snd egr_args)
                       ; det_fwd_asst
            ])
            ST.Skip
        (* ST.Apply   c_check  ext_args cck_args NoInfo; *)
        (* ST.Apply   deparser ext_args dep_args NoInfo *)
    ].

Definition package (types : list E.t) (cargs : TopDecl.constructor_args) : result ST.s :=
  match cargs with
  | [p; vc; ing; egr; cc; d] =>
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

Definition gcl_from_p4cub instr gas unroll p4cub : result ToGCL.target :=
  let arrowtype := ({|paramargs:=[("check", PAIn E.TBool)]; rtrns:=None|} : Expr.arrowT) in
  let assume_decl := TopDecl.Extern "_" 1 [] [] [("assume", (0%nat, [], arrowtype))] in
  let p4cub_instrumented := ToP4cub.add_extern  p4cub assume_decl in
  ToGCL.from_p4cub  instr gas unroll externs (package) p4cub.
