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

Definition get_arg_expr (arg : Exp.arg) : E.t :=
  match arg with
  | PAIn e => e
  | PAOut e => e
  | PAInOut e => e
  end.

Definition externs extern method (args : Exp.args) (ret : option Exp.t)  : result string Inline.t :=
  let args_expr := map get_arg_expr args in
  if (extern =? "_")%string then
      if (method =? "mark_to_drop")%string then
          match args_expr with
          | [stdmeta] =>
            let t := Typ.Bit (BinNat.N.of_nat 9) in
            ok $ Inline.IAssign t (Exp.Member t 1 stdmeta) (Exp.Bit 9 511%Z)
          | _ =>
            error "too many arguments passed to mark_to_drop"
          end
      else if orb (method =? "assert") (method =? "assume")%string then
        ok $ Inline.IExternMethodCall extern method args None
      else
          match List.find (String.eqb method) ["hash"; "truncate"; "random"; "crc_poly"; "digest"] with
          | None =>
            error ("couldnt find extern " ++ extern ++ "." ++ method)
          | Some _ => ok Inline.ISkip
          end
  else if (extern =? "packet_in")%string then
         if (method =? "extract")%string then
           match args_expr with
           | nil => error "cannot extract 0 args "
           | [hdr] =>
             ok $ Inline.ISetValidity true hdr
           | [hdr; _] =>
             ok $ Inline.ISetValidity true hdr
           | _ =>
             error "cannot extract with more than 2 args"
           end
         else if (method =? "lookahead")%string then
            (* this relies on SimplExpr assigning packet_in.lookahead a fresh
            var for correctness *)
            ok Inline.ISkip
         else
            error ("couldnt find extern " ++ extern ++ "." ++ method)
  else ok Inline.ISkip.

Definition cub_seq (statements : list ST.t): ST.t :=
  List.fold_right ST.Seq ST.Skip statements.

Definition det_fwd_asst :=
  let assertion :=
      E.Bop Typ.Bool
             Bin.NotEq
             (E.Var (Typ.Bit 9%N) "standard_metadata.egress_spec" 0)
             (E.Bit 9%N 0%Z)
  in
  let paramargs := [(*check*) PAIn assertion] in
  ST.App (Call.Method "_" "assert" [] None) paramargs.

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
Definition t_arg (dir : E.t -> paramarg E.t E.t) typ var :=
  (var, dir (E.Var typ var 0)).

Definition pipeline  (htype mtype : Typ.t) (parser v_check ingress egress c_check deparser : string) : ST.t * ST.t  :=
  let ext_args := ["packet_in"] in
  let pargs := [
        t_arg PAOut      htype                "parsedHdr";
        t_arg PAInOut    mtype                "meta";
        t_arg PAInOut standard_metadata_t "standard_metadata"] in
  let vck_args := [
        t_arg PAInOut htype "hdr";
        t_arg PAInOut mtype "meta"] in
  let ing_args := [
        t_arg PAInOut htype "hdr";
        t_arg PAInOut mtype "meta";
        t_arg PAInOut standard_metadata_t "standard_metadata"] in
  let egr_args := [
        t_arg PAInOut htype "hdr";
        t_arg PAInOut mtype "meta";
        t_arg PAInOut standard_metadata_t "standard_metadata"] in
  let cck_args := [
        t_arg PAInOut htype "hdr";
        t_arg PAInOut mtype "meta"] in
  let dep_ext_args := [ "packet_out" ; "b" ] in
  let dep_args := [ t_arg PAIn htype "hdr"] in
  (ST.App (Call.Inst parser ext_args) (map snd pargs),
    (* ST.Apply v_check ext_args vck_args i; *)
    ST.Cond
        (E.Var Typ.Bool ("_state$accept$next") 0)
        (cub_seq [
                 ST.App (Call.Inst ingress ext_args) (map snd ing_args)
                 ; ST.App (Call.Inst egress ext_args) (map snd egr_args)
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
  let arrowtype := ({|paramargs:=[("check", PAIn Typ.Bool)]; rtrns:=None|} : Typ.arrowT) in
  let assume_decl := Top.Extern "_" 1 [] [] [("assume", (0%nat, [], arrowtype))] in
  let p4cub_instrumented := ToP4cub.add_extern  p4cub assume_decl in
  ToGCL.from_p4cub instr hv gas unroll externs (package) p4cub.
