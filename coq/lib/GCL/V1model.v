Set Warnings "-custom-entry-overridden".
From Poulet4 Require Import P4light.Syntax.P4defs
     Monads.Result Utils.Envn GCL.GCL GCL.ToGCL.
Import Result ResultNotations Syntax List ListNotations String.
Open Scope string_scope.

Module G := GCL.GCL.
Module F := GCL.Form.
Module BV := GCL.BitVec.
Module E := GCL.E.
Module ST := Stm.

Definition externs : ToGCL.model :=
  [("_", [("mark_to_drop",  G.GAssign (Typ.Bit (BinNat.N.of_nat 9)) "standard_metadata.egress_spec" (BV.bit (Some 9%nat) 511));
         ("clone3", G.GSkip);
         ("assert", G.GAssert (F.LVar "check"));
         ("assume", G.GAssume (F.LVar "check"));
         ("hash", G.GSkip);
         ("truncate", G.GSkip);
         ("random", G.GSkip);
         ("crc_poly", G.GSkip);
         ("digest", G.GSkip);
         ("hopen", G.GAssume (F.LVar "check"));
         ("hclose", G.GAssert (F.LVar "check"))
   ]);
  ("packet_in", [("extract", G.GAssign (Typ.Bit 1%N) "hdr.is_valid" (BV.bit (Some 1%nat) 1));
                 ("lookahead", G.GSkip)]);
  ("counter", [("count", G.GSkip)]);
  ("direct_counter", [("count", G.GSkip)]);
  ("register", [("read", G.GSkip); ("write", G.GSkip)]);
  ("meter", [("meter", G.GSkip); ("execute_meter", G.GSkip)]);
  ("direct_meter", [("direct_meter", G.GSkip); ("read", G.GSkip)])
  ].

Definition cub_seq (statements : list ST.t): ST.t :=
  List.fold_right ST.Seq ST.Skip statements.

Definition det_fwd_asst   :=
  let assertion :=
      E.Bop Typ.Bool
             Bin.NotEq
             (E.Var (Typ.Bit 9%N) "standard_metadata.egress_spec" 0)
             (E.Bit 9%N 0%Z)
  in
  let args := InOut.mk_t [(*check*) assertion] [] in
  ST.App (Call.Method "_" "assert" [] None) args.

Definition standard_metadata_t : Typ.t :=
  Typ.Struct
    false
    [Typ.Bit 9 (*ingress_port*);
     Typ.Bit 9 (*egress_spec*);
     Typ.Bit 9 (*egress_port*);
     Typ.Bit 32 (*instance_type*);
     Typ.Bit 32 (*packet_length*);
     Typ.Bit 32 (*enq_timestamp*);
     Typ.Bit 19 (*enq_qdepth*);
     Typ.Bit 32 (*deq_timedelta*);
     Typ.Bit 19 (*deq_qdepth*);
     Typ.Bit 48 (*ingress_global_timestamp*);
     Typ.Bit 48 (*egress_global_timestamp*);
     Typ.Bit 16 (*mcast_grp*);
     Typ.Bit 16 (*egress_rid*);
     Typ.Bit 1 (*checksum_error*);
     Typ.Error (* parser error *);
     Typ.Bit 3 (*priority*)].

(* TODO: correct de bruijn index? *)
Definition t_arg typ var :=
  (var, E.Var typ var 0).

Definition pipeline  (htype mtype : Typ.t) (parser v_check ingress egress c_check deparser : string) : ST.t * ST.t  :=
  let ext_args := ["packet_in"] in
  let pargs :=
    InOut.mk_t
      [t_arg mtype               "meta";
       t_arg standard_metadata_t "standard_metadata"]
      [t_arg htype               "parsedHdr";
       t_arg mtype               "meta";
       t_arg standard_metadata_t "standard_metadata"] in
  let vck_args :=
    InOut.mk_t
      [t_arg htype "hdr";
       t_arg mtype "meta"]
      [t_arg htype "hdr";
       t_arg mtype "meta"] in
  let ing_args :=
    InOut.mk_t
      [t_arg htype "hdr";
       t_arg mtype "meta";
       t_arg standard_metadata_t "standard_metadata"]
      [t_arg htype "hdr";
       t_arg mtype "meta";
       t_arg standard_metadata_t "standard_metadata"] in
  let egr_args :=
    InOut.mk_t
      [t_arg htype "hdr";
       t_arg mtype "meta";
       t_arg standard_metadata_t "standard_metadata"]
      [t_arg htype "hdr";
       t_arg mtype "meta";
       t_arg standard_metadata_t "standard_metadata"] in
  let cck_args :=
    InOut.mk_t
      [t_arg htype "hdr";
       t_arg mtype "meta"]
      [t_arg htype "hdr";
       t_arg mtype "meta"] in
  let dep_ext_args := [ "packet_out" ; "b" ] in
  (*let dep_args := InOut.mk_t [ t_arg htype "hdr"] [] in*)
  (ST.App (Call.Inst parser ext_args) (InOut.map_uni snd pargs),
    (* ST.Apply v_check ext_args vck_args i; *)
    ST.Cond
        (E.Var Typ.Bool ("_state$accept$next") 0)
        (cub_seq [
                 ST.App (Call.Inst ingress ext_args) (InOut.map_uni snd ing_args)
                 ; ST.App (Call.Inst egress ext_args) (InOut.map_uni snd egr_args)
                 (* ; det_fwd_asst *)
        ])
        ST.Skip
        (* ST.Apply   c_check  ext_args cck_args NoInfo; *)
        (* ST.Apply   deparser ext_args dep_args NoInfo *)
  ).

Definition package (types : list Typ.t) (cargs : Top.constructor_args) : result string (ST.t * ST.t) :=
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

(* Definition gcl_from_p4cub instr hv gas unroll p4cub : result string ToGCL.target := *)
(*   let arrowtype := ({|paramargs:=[("check", PAIn E.TBool)]; rtrns:=None|} : Expr.arrowT) in *)
(*   let assume_decl := TopDecl.Extern "_" 1 [] [] [("assume", (0%nat, [], arrowtype))] in *)

Definition gcl_from_p4cub instr hv gas unroll p4cub : result string (ToGCL.target * ToGCL.target) :=
  let arrowtype := ({|Arr.inout:=InOut.mk_t [("check", Typ.Bool)] []; Arr.ret:=None|} : Typ.arrow) in
  let assume_decl := Top.Extern "_" 1 [] [] [("assume", (0%nat, [], arrowtype))] in
  let p4cub_instrumented := ToP4cub.add_extern  p4cub assume_decl in
  ToGCL.from_p4cub instr hv gas unroll externs package p4cub.
