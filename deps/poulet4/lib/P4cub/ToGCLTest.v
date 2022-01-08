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
Require Poulet4.P4cub.V1model.
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

Definition simple_nat_test_case :=
  let* sn := p4cub_simple_nat in
  let externs := V1model.externs in
  ToGCL.from_p4cub Info TableInstr.instr 1000 10 externs (V1model.package NoInfo) sn.

Definition inline_simple_nat : result (Inline.t Info) :=
  let* sn := p4cub_simple_nat in
  ToGCL.inline_from_p4cub Info 1000 10 externs (V1model.package NoInfo) sn.

Definition instrumented_simple_nat : result (Inline.t Info) :=
  let* isn := inline_simple_nat in
  Inline.assert_headers_valid_before_use _ isn.
Require Import Poulet4.P4cub.Syntax.InferMemberTypes.

Compute (let+ sn := p4cub_simple_nat in ToP4cub.infer_member_types Info sn).

Compute InferMemberTypes.inf_s
        (Stmt.SAssign
                        (Expr.EExprMember
                           (Expr.TStruct
                              [("do_forward", Expr.TBit 1); ("ipv4_sa", Expr.TBit 32);
                              ("ipv4_da", Expr.TBit 32); ("tcp_sp", Expr.TBit 16);
                              ("tcp_dp", Expr.TBit 16); ("nhop_ipv4", Expr.TBit 32);
                              ("if_ipv4_addr", Expr.TBit 32); ("if_mac_addr", Expr.TBit 48);
                              ("is_ext_if", Expr.TBit 1); ("tcpLength", Expr.TBit 16);
                              ("if_index", Expr.TBit 8); ("init_egress_spec", Expr.TBit 9)])
                           "if_index"
                           (Expr.EExprMember
                              (Expr.THeader
                                 [("meta",
                                  Expr.TStruct
                                    [("do_forward", Expr.TBit 1); ("ipv4_sa", Expr.TBit 32);
                                    ("ipv4_da", Expr.TBit 32); ("tcp_sp", Expr.TBit 16);
                                    ("tcp_dp", Expr.TBit 16); ("nhop_ipv4", Expr.TBit 32);
                                    ("if_ipv4_addr", Expr.TBit 32); ("if_mac_addr", Expr.TBit 48);
                                    ("is_ext_if", Expr.TBit 1); ("tcpLength", Expr.TBit 16);
                                    ("if_index", Expr.TBit 8); ("init_egress_spec", Expr.TBit 9)])])
                              "meta"
                              (Expr.EVar
                                 (Expr.THeader
                                    [("meta",
                                     Expr.TStruct
                                       [("do_forward", Expr.TBit 1); ("ipv4_sa", Expr.TBit 32);
                                       ("ipv4_da", Expr.TBit 32); ("tcp_sp", Expr.TBit 16);
                                       ("tcp_dp", Expr.TBit 16); ("nhop_ipv4", Expr.TBit 32);
                                       ("if_ipv4_addr", Expr.TBit 32);
                                       ("if_mac_addr", Expr.TBit 48); ("is_ext_if", Expr.TBit 1);
                                       ("tcpLength", Expr.TBit 16); ("if_index", Expr.TBit 8);
                                       ("init_egress_spec", Expr.TBit 9)])]) "meta" NoInfo) NoInfo)
                           NoInfo)
                        (Expr.ECast (Expr.TBit 8)
                           (Expr.EExprMember
                              (Expr.THeader
                                 [("ingress_port", Expr.TBit 9); ("egress_spec", Expr.TBit 9);
                                 ("egress_port", Expr.TBit 9); ("instance_type", Expr.TBit 32);
                                 ("packet_length", Expr.TBit 32); ("enq_timestamp", Expr.TBit 32);
                                 ("enq_qdepth", Expr.TBit 19); ("deq_timedelta", Expr.TBit 32);
                                 ("deq_qdepth", Expr.TBit 19);
                                 ("ingress_global_timestamp", Expr.TBit 48);
                                 ("egress_global_timestamp", Expr.TBit 48);
                                 ("mcast_grp", Expr.TBit 16); ("egress_rid", Expr.TBit 16);
                                 ("checksum_error", Expr.TBit 1); ("parser_error", Expr.TError);
                                 ("priority", Expr.TBit 3)]) "ingress_port"
                              (Expr.EVar
                                 (Expr.THeader
                                    [("ingress_port", Expr.TBit 9); ("egress_spec", Expr.TBit 9);
                                    ("egress_port", Expr.TBit 9); ("instance_type", Expr.TBit 32);
                                    ("packet_length", Expr.TBit 32);
                                    ("enq_timestamp", Expr.TBit 32); ("enq_qdepth", Expr.TBit 19);
                                    ("deq_timedelta", Expr.TBit 32); ("deq_qdepth", Expr.TBit 19);
                                    ("ingress_global_timestamp", Expr.TBit 48);
                                    ("egress_global_timestamp", Expr.TBit 48);
                                    ("mcast_grp", Expr.TBit 16); ("egress_rid", Expr.TBit 16);
                                    ("checksum_error", Expr.TBit 1); ("parser_error", Expr.TError);
                                    ("priority", Expr.TBit 3)]) "standard_metadata" NoInfo) NoInfo)
                           NoInfo) NoInfo).


Definition sn_start_state :=
               {|
                 Parser.stmt :=
                   Stmt.SSeq
                     (Stmt.SAssign
                        (Expr.EExprMember
                           (Expr.TStruct
                              [("do_forward", Expr.TBit 1); ("ipv4_sa", Expr.TBit 32);
                              ("ipv4_da", Expr.TBit 32); ("tcp_sp", Expr.TBit 16);
                              ("tcp_dp", Expr.TBit 16); ("nhop_ipv4", Expr.TBit 32);
                              ("if_ipv4_addr", Expr.TBit 32); ("if_mac_addr", Expr.TBit 48);
                              ("is_ext_if", Expr.TBit 1); ("tcpLength", Expr.TBit 16);
                              ("if_index", Expr.TBit 8); ("init_egress_spec", Expr.TBit 9)])
                           "if_index"
                           (Expr.EExprMember
                              (Expr.THeader
                                 [("meta",
                                  Expr.TStruct
                                    [("do_forward", Expr.TBit 1); ("ipv4_sa", Expr.TBit 32);
                                    ("ipv4_da", Expr.TBit 32); ("tcp_sp", Expr.TBit 16);
                                    ("tcp_dp", Expr.TBit 16); ("nhop_ipv4", Expr.TBit 32);
                                    ("if_ipv4_addr", Expr.TBit 32); ("if_mac_addr", Expr.TBit 48);
                                    ("is_ext_if", Expr.TBit 1); ("tcpLength", Expr.TBit 16);
                                    ("if_index", Expr.TBit 8); ("init_egress_spec", Expr.TBit 9)])])
                              "meta"
                              (Expr.EVar
                                 (Expr.THeader
                                    [("meta",
                                     Expr.TStruct
                                       [("do_forward", Expr.TBit 1); ("ipv4_sa", Expr.TBit 32);
                                       ("ipv4_da", Expr.TBit 32); ("tcp_sp", Expr.TBit 16);
                                       ("tcp_dp", Expr.TBit 16); ("nhop_ipv4", Expr.TBit 32);
                                       ("if_ipv4_addr", Expr.TBit 32);
                                       ("if_mac_addr", Expr.TBit 48); ("is_ext_if", Expr.TBit 1);
                                       ("tcpLength", Expr.TBit 16); ("if_index", Expr.TBit 8);
                                       ("init_egress_spec", Expr.TBit 9)])]) "meta" NoInfo) NoInfo)
                           NoInfo)
                        (Expr.ECast (Expr.TBit 8)
                           (Expr.EExprMember
                              (Expr.THeader
                                 [("ingress_port", Expr.TBit 9); ("egress_spec", Expr.TBit 9);
                                 ("egress_port", Expr.TBit 9); ("instance_type", Expr.TBit 32);
                                 ("packet_length", Expr.TBit 32); ("enq_timestamp", Expr.TBit 32);
                                 ("enq_qdepth", Expr.TBit 19); ("deq_timedelta", Expr.TBit 32);
                                 ("deq_qdepth", Expr.TBit 19);
                                 ("ingress_global_timestamp", Expr.TBit 48);
                                 ("egress_global_timestamp", Expr.TBit 48);
                                 ("mcast_grp", Expr.TBit 16); ("egress_rid", Expr.TBit 16);
                                 ("checksum_error", Expr.TBit 1); ("parser_error", Expr.TError);
                                 ("priority", Expr.TBit 3)]) "ingress_port"
                              (Expr.EVar
                                 (Expr.THeader
                                    [("ingress_port", Expr.TBit 9); ("egress_spec", Expr.TBit 9);
                                    ("egress_port", Expr.TBit 9); ("instance_type", Expr.TBit 32);
                                    ("packet_length", Expr.TBit 32);
                                    ("enq_timestamp", Expr.TBit 32); ("enq_qdepth", Expr.TBit 19);
                                    ("deq_timedelta", Expr.TBit 32); ("deq_qdepth", Expr.TBit 19);
                                    ("ingress_global_timestamp", Expr.TBit 48);
                                    ("egress_global_timestamp", Expr.TBit 48);
                                    ("mcast_grp", Expr.TBit 16); ("egress_rid", Expr.TBit 16);
                                    ("checksum_error", Expr.TBit 1); ("parser_error", Expr.TError);
                                    ("priority", Expr.TBit 3)]) "standard_metadata" NoInfo) NoInfo)
                           NoInfo) NoInfo) (Stmt.SSkip NoInfo) NoInfo;
                 Parser.trans :=
                   Parser.PSelect
                     (Expr.ETuple [Expr.ESlice (Expr.EVar (Expr.TBit 64) "t'0" NoInfo) 63 1 NoInfo]
                        NoInfo) (Parser.PGoto (Parser.STName "parse_ethernet") NoInfo)
                     [(Parser.PATTuple [Parser.PATBit 64 0],
                      Parser.PGoto (Parser.STName "parse_cpu_header") NoInfo)] NoInfo
               |}.
Print Inline.inline_state.
Check Inline.inline_parser.
Compute let* ctx := p4cub_simple_nat  in
        Inline.inline_parser Info 1000 10 NoInfo ctx "start" sn_start_state [].
Check Inline.translate_pat.
Compute (Inline.translate_pat Info NoInfo
        (Expr.ETuple [Expr.EVar (Expr.TBit 64) "t'0" NoInfo] NoInfo)
        (Parser.PATTuple [Parser.PATBit 64 0])).
(* = [t0] [= [t0] [63w0]]  *)


(* Compute (ToP4cub.preprocess Info NoInfo SimpleNat.prog). *)
Compute inline_simple_nat.
Compute (ToGCL.arrowE_to_arglist Info
{|
                                         paramargs :=
                                           [("hdr.dstAddr",
                                            PAOut
                                              (Inline.E.EExprMember (Inline.E.TBit 48) "dstAddr"
                                                 (Inline.E.EExprMember
                                                    (Inline.E.THeader [("dstAddr", Inline.E.TBit 48); ("srcAddr", Inline.E.TBit 48); ("etherType", Inline.E.TBit 16)]) "ethernet"
                                                    (Inline.E.EVar
                                                       (Inline.E.TStruct
                                                          [("cpu_header",
                                                           Inline.E.THeader
                                                             [("preamble", Inline.E.TBit 64); ("device", Inline.E.TBit 8); ("reason", Inline.E.TBit 8); ("if_index", Inline.E.TBit 8)]);
                                                          ("ethernet",
                                                          Inline.E.THeader [("dstAddr", Inline.E.TBit 48); ("srcAddr", Inline.E.TBit 48); ("etherType", Inline.E.TBit 16)]);
                                                          ("ipv4",
                                                          Inline.E.THeader
                                                            [("version", Inline.E.TBit 4); ("ihl", Inline.E.TBit 4); ("diffserv", Inline.E.TBit 8); ("totalLen", Inline.E.TBit 16);
                                                            ("identification", Inline.E.TBit 16); ("flags", Inline.E.TBit 3); ("fragOffset", Inline.E.TBit 13);
                                                            ("ttl", Inline.E.TBit 8); ("protocol", Inline.E.TBit 8); ("hdrChecksum", Inline.E.TBit 16); ("srcAddr", Inline.E.TBit 32);
                                                            ("dstAddr", Inline.E.TBit 32)]);
                                                          ("tcp",
                                                          Inline.E.THeader
                                                            [("srcPort", Inline.E.TBit 16); ("dstPort", Inline.E.TBit 16); ("seqNo", Inline.E.TBit 32); ("ackNo", Inline.E.TBit 32);
                                                            ("dataOffset", Inline.E.TBit 4); ("res", Inline.E.TBit 4); ("flags", Inline.E.TBit 8); ("window", Inline.E.TBit 16);
                                                            ("checksum", Inline.E.TBit 16); ("urgentPtr", Inline.E.TBit 16)])]) "hdr" NoInfo) NoInfo) NoInfo));
                                           ("hdr.srcAddr",
                                           PAOut
                                             (Inline.E.EExprMember (Inline.E.TBit 48) "srcAddr"
                                                (Inline.E.EExprMember
                                                   (Inline.E.THeader [("dstAddr", Inline.E.TBit 48); ("srcAddr", Inline.E.TBit 48); ("etherType", Inline.E.TBit 16)]) "ethernet"
                                                   (Inline.E.EVar
                                                      (Inline.E.TStruct
                                                         [("cpu_header",
                                                          Inline.E.THeader
                                                            [("preamble", Inline.E.TBit 64); ("device", Inline.E.TBit 8); ("reason", Inline.E.TBit 8); ("if_index", Inline.E.TBit 8)]);
                                                         ("ethernet",
                                                         Inline.E.THeader [("dstAddr", Inline.E.TBit 48); ("srcAddr", Inline.E.TBit 48); ("etherType", Inline.E.TBit 16)]);
                                                         ("ipv4",
                                                         Inline.E.THeader
                                                           [("version", Inline.E.TBit 4); ("ihl", Inline.E.TBit 4); ("diffserv", Inline.E.TBit 8); ("totalLen", Inline.E.TBit 16);
                                                           ("identification", Inline.E.TBit 16); ("flags", Inline.E.TBit 3); ("fragOffset", Inline.E.TBit 13);
                                                           ("ttl", Inline.E.TBit 8); ("protocol", Inline.E.TBit 8); ("hdrChecksum", Inline.E.TBit 16); ("srcAddr", Inline.E.TBit 32);
                                                           ("dstAddr", Inline.E.TBit 32)]);
                                                         ("tcp",
                                                         Inline.E.THeader
                                                           [("srcPort", Inline.E.TBit 16); ("dstPort", Inline.E.TBit 16); ("seqNo", Inline.E.TBit 32); ("ackNo", Inline.E.TBit 32);
                                                           ("dataOffset", Inline.E.TBit 4); ("res", Inline.E.TBit 4); ("flags", Inline.E.TBit 8); ("window", Inline.E.TBit 16);
                                                           ("checksum", Inline.E.TBit 16); ("urgentPtr", Inline.E.TBit 16)])]) "hdr" NoInfo) NoInfo) NoInfo));
                                           ("hdr.etherType",
                                           PAOut
                                             (Inline.E.EExprMember (Inline.E.TBit 16) "etherType"
                                                (Inline.E.EExprMember
                                                   (Inline.E.THeader [("dstAddr", Inline.E.TBit 48); ("srcAddr", Inline.E.TBit 48); ("etherType", Inline.E.TBit 16)]) "ethernet"
                                                   (Inline.E.EVar
                                                      (Inline.E.TStruct
                                                         [("cpu_header",
                                                          Inline.E.THeader
                                                            [("preamble", Inline.E.TBit 64); ("device", Inline.E.TBit 8); ("reason", Inline.E.TBit 8); ("if_index", Inline.E.TBit 8)]);
                                                         ("ethernet",
                                                         Inline.E.THeader [("dstAddr", Inline.E.TBit 48); ("srcAddr", Inline.E.TBit 48); ("etherType", Inline.E.TBit 16)]);
                                                         ("ipv4",
                                                         Inline.E.THeader
                                                           [("version", Inline.E.TBit 4); ("ihl", Inline.E.TBit 4); ("diffserv", Inline.E.TBit 8); ("totalLen", Inline.E.TBit 16);
                                                           ("identification", Inline.E.TBit 16); ("flags", Inline.E.TBit 3); ("fragOffset", Inline.E.TBit 13);
                                                           ("ttl", Inline.E.TBit 8); ("protocol", Inline.E.TBit 8); ("hdrChecksum", Inline.E.TBit 16); ("srcAddr", Inline.E.TBit 32);
                                                           ("dstAddr", Inline.E.TBit 32)]);
                                                         ("tcp",
                                                         Inline.E.THeader
                                                           [("srcPort", Inline.E.TBit 16); ("dstPort", Inline.E.TBit 16); ("seqNo", Inline.E.TBit 32); ("ackNo", Inline.E.TBit 32);
                                                           ("dataOffset", Inline.E.TBit 4); ("res", Inline.E.TBit 4); ("flags", Inline.E.TBit 8); ("window", Inline.E.TBit 16);
                                                           ("checksum", Inline.E.TBit 16); ("urgentPtr", Inline.E.TBit 16)])]) "hdr" NoInfo) NoInfo) NoInfo));
                                           ("hdr.is_valid",
                                           PAOut
                                             (Inline.E.EExprMember (Inline.E.TBit 1) "is_valid"
                                                (Inline.E.EExprMember
                                                   (Inline.E.THeader [("dstAddr", Inline.E.TBit 48); ("srcAddr", Inline.E.TBit 48); ("etherType", Inline.E.TBit 16)]) "ethernet"
                                                   (Inline.E.EVar
                                                      (Inline.E.TStruct
                                                         [("cpu_header",
                                                          Inline.E.THeader
                                                            [("preamble", Inline.E.TBit 64); ("device", Inline.E.TBit 8); ("reason", Inline.E.TBit 8); ("if_index", Inline.E.TBit 8)]);
                                                         ("ethernet",
                                                         Inline.E.THeader [("dstAddr", Inline.E.TBit 48); ("srcAddr", Inline.E.TBit 48); ("etherType", Inline.E.TBit 16)]);
                                                         ("ipv4",
                                                         Inline.E.THeader
                                                           [("version", Inline.E.TBit 4); ("ihl", Inline.E.TBit 4); ("diffserv", Inline.E.TBit 8); ("totalLen", Inline.E.TBit 16);
                                                           ("identification", Inline.E.TBit 16); ("flags", Inline.E.TBit 3); ("fragOffset", Inline.E.TBit 13);
                                                           ("ttl", Inline.E.TBit 8); ("protocol", Inline.E.TBit 8); ("hdrChecksum", Inline.E.TBit 16); ("srcAddr", Inline.E.TBit 32);
                                                           ("dstAddr", Inline.E.TBit 32)]);
                                                         ("tcp",
                                                         Inline.E.THeader
                                                           [("srcPort", Inline.E.TBit 16); ("dstPort", Inline.E.TBit 16); ("seqNo", Inline.E.TBit 32); ("ackNo", Inline.E.TBit 32);
                                                           ("dataOffset", Inline.E.TBit 4); ("res", Inline.E.TBit 4); ("flags", Inline.E.TBit 8); ("window", Inline.E.TBit 16);
                                                           ("checksum", Inline.E.TBit 16); ("urgentPtr", Inline.E.TBit 16)])]) "hdr" NoInfo) NoInfo) NoInfo))];
                                         rtrns := None
                                       |}).

Compute (ToGCL.subst_args
           (G.GAssign (E.TBit 1%N) "hdr.is_valid" (BV.bit (Some 1) 1))
         [("hdr.dstAddr", inr (ToGCL.BV.BVVar "hdr.ethernet.dstAddr" 48));
         ("hdr.srcAddr", inr (ToGCL.BV.BVVar "hdr.ethernet.srcAddr" 48));
         ("hdr.etherType", inr (ToGCL.BV.BVVar "hdr.ethernet.etherType" 16));
         ("hdr.is_valid", inr (ToGCL.BV.BVVar "hdr.ethernet.is_valid" 1))]).

Compute (ToGCL.subst_args
           (G.GAssign (E.TBit 1%N) "hdr.is_valid" (BV.bit (Some 1) 1))
         [("hdr.is_valid", inr (ToGCL.BV.BVVar "hdr.ethernet.is_valid" 1))]).

Compute ToGCL.lvalue_subst "hdr.is_valid" (BV.BVVar "hdr.ethernet.is_valid" 1) "hdr.is_valid".

Compute (GCL.subst_rvalue ToGCL.lvalue_subst BV.subst_bv GCL.Form.subst_bv
        "hdr.is_valid" (BV.BVVar "hdr.ethernet.is_valid" 1) (G.GAssign (E.TBit 1%N) "hdr.is_valid" (BV.bit (Some 1) 1))).

Compute (ToGCL.inline_to_gcl Info TableInstr.instr ToGCL.initial
                             (Poulet4.P4cub.V1model.externs)
(Inline.IExternMethodCall Info "packet_in" "extract"
                                       {|
                                         paramargs :=
                                           [("hdr.dstAddr",
                                            PAOut
                                              (Inline.E.EExprMember (Inline.E.TBit 48) "dstAddr"
                                                 (Inline.E.EExprMember
                                                    (Inline.E.THeader [("dstAddr", Inline.E.TBit 48); ("srcAddr", Inline.E.TBit 48); ("etherType", Inline.E.TBit 16)]) "ethernet"
                                                    (Inline.E.EVar
                                                       (Inline.E.TStruct
                                                          [("cpu_header",
                                                           Inline.E.THeader
                                                             [("preamble", Inline.E.TBit 64); ("device", Inline.E.TBit 8); ("reason", Inline.E.TBit 8); ("if_index", Inline.E.TBit 8)]);
                                                          ("ethernet",
                                                          Inline.E.THeader [("dstAddr", Inline.E.TBit 48); ("srcAddr", Inline.E.TBit 48); ("etherType", Inline.E.TBit 16)]);
                                                          ("ipv4",
                                                          Inline.E.THeader
                                                            [("version", Inline.E.TBit 4); ("ihl", Inline.E.TBit 4); ("diffserv", Inline.E.TBit 8); ("totalLen", Inline.E.TBit 16);
                                                            ("identification", Inline.E.TBit 16); ("flags", Inline.E.TBit 3); ("fragOffset", Inline.E.TBit 13);
                                                            ("ttl", Inline.E.TBit 8); ("protocol", Inline.E.TBit 8); ("hdrChecksum", Inline.E.TBit 16); ("srcAddr", Inline.E.TBit 32);
                                                            ("dstAddr", Inline.E.TBit 32)]);
                                                          ("tcp",
                                                          Inline.E.THeader
                                                            [("srcPort", Inline.E.TBit 16); ("dstPort", Inline.E.TBit 16); ("seqNo", Inline.E.TBit 32); ("ackNo", Inline.E.TBit 32);
                                                            ("dataOffset", Inline.E.TBit 4); ("res", Inline.E.TBit 4); ("flags", Inline.E.TBit 8); ("window", Inline.E.TBit 16);
                                                            ("checksum", Inline.E.TBit 16); ("urgentPtr", Inline.E.TBit 16)])]) "hdr" NoInfo) NoInfo) NoInfo));
                                           ("hdr.srcAddr",
                                           PAOut
                                             (Inline.E.EExprMember (Inline.E.TBit 48) "srcAddr"
                                                (Inline.E.EExprMember
                                                   (Inline.E.THeader [("dstAddr", Inline.E.TBit 48); ("srcAddr", Inline.E.TBit 48); ("etherType", Inline.E.TBit 16)]) "ethernet"
                                                   (Inline.E.EVar
                                                      (Inline.E.TStruct
                                                         [("cpu_header",
                                                          Inline.E.THeader
                                                            [("preamble", Inline.E.TBit 64); ("device", Inline.E.TBit 8); ("reason", Inline.E.TBit 8); ("if_index", Inline.E.TBit 8)]);
                                                         ("ethernet",
                                                         Inline.E.THeader [("dstAddr", Inline.E.TBit 48); ("srcAddr", Inline.E.TBit 48); ("etherType", Inline.E.TBit 16)]);
                                                         ("ipv4",
                                                         Inline.E.THeader
                                                           [("version", Inline.E.TBit 4); ("ihl", Inline.E.TBit 4); ("diffserv", Inline.E.TBit 8); ("totalLen", Inline.E.TBit 16);
                                                           ("identification", Inline.E.TBit 16); ("flags", Inline.E.TBit 3); ("fragOffset", Inline.E.TBit 13);
                                                           ("ttl", Inline.E.TBit 8); ("protocol", Inline.E.TBit 8); ("hdrChecksum", Inline.E.TBit 16); ("srcAddr", Inline.E.TBit 32);
                                                           ("dstAddr", Inline.E.TBit 32)]);
                                                         ("tcp",
                                                         Inline.E.THeader
                                                           [("srcPort", Inline.E.TBit 16); ("dstPort", Inline.E.TBit 16); ("seqNo", Inline.E.TBit 32); ("ackNo", Inline.E.TBit 32);
                                                           ("dataOffset", Inline.E.TBit 4); ("res", Inline.E.TBit 4); ("flags", Inline.E.TBit 8); ("window", Inline.E.TBit 16);
                                                           ("checksum", Inline.E.TBit 16); ("urgentPtr", Inline.E.TBit 16)])]) "hdr" NoInfo) NoInfo) NoInfo));
                                           ("hdr.etherType",
                                           PAOut
                                             (Inline.E.EExprMember (Inline.E.TBit 16) "etherType"
                                                (Inline.E.EExprMember
                                                   (Inline.E.THeader [("dstAddr", Inline.E.TBit 48); ("srcAddr", Inline.E.TBit 48); ("etherType", Inline.E.TBit 16)]) "ethernet"
                                                   (Inline.E.EVar
                                                      (Inline.E.TStruct
                                                         [("cpu_header",
                                                          Inline.E.THeader
                                                            [("preamble", Inline.E.TBit 64); ("device", Inline.E.TBit 8); ("reason", Inline.E.TBit 8); ("if_index", Inline.E.TBit 8)]);
                                                         ("ethernet",
                                                         Inline.E.THeader [("dstAddr", Inline.E.TBit 48); ("srcAddr", Inline.E.TBit 48); ("etherType", Inline.E.TBit 16)]);
                                                         ("ipv4",
                                                         Inline.E.THeader
                                                           [("version", Inline.E.TBit 4); ("ihl", Inline.E.TBit 4); ("diffserv", Inline.E.TBit 8); ("totalLen", Inline.E.TBit 16);
                                                           ("identification", Inline.E.TBit 16); ("flags", Inline.E.TBit 3); ("fragOffset", Inline.E.TBit 13);
                                                           ("ttl", Inline.E.TBit 8); ("protocol", Inline.E.TBit 8); ("hdrChecksum", Inline.E.TBit 16); ("srcAddr", Inline.E.TBit 32);
                                                           ("dstAddr", Inline.E.TBit 32)]);
                                                         ("tcp",
                                                         Inline.E.THeader
                                                           [("srcPort", Inline.E.TBit 16); ("dstPort", Inline.E.TBit 16); ("seqNo", Inline.E.TBit 32); ("ackNo", Inline.E.TBit 32);
                                                           ("dataOffset", Inline.E.TBit 4); ("res", Inline.E.TBit 4); ("flags", Inline.E.TBit 8); ("window", Inline.E.TBit 16);
                                                           ("checksum", Inline.E.TBit 16); ("urgentPtr", Inline.E.TBit 16)])]) "hdr" NoInfo) NoInfo) NoInfo));
                                           ("hdr.is_valid",
                                           PAOut
                                             (Inline.E.EExprMember (Inline.E.TBit 1) "is_valid"
                                                (Inline.E.EExprMember
                                                   (Inline.E.THeader [("dstAddr", Inline.E.TBit 48); ("srcAddr", Inline.E.TBit 48); ("etherType", Inline.E.TBit 16)]) "ethernet"
                                                   (Inline.E.EVar
                                                      (Inline.E.TStruct
                                                         [("cpu_header",
                                                          Inline.E.THeader
                                                            [("preamble", Inline.E.TBit 64); ("device", Inline.E.TBit 8); ("reason", Inline.E.TBit 8); ("if_index", Inline.E.TBit 8)]);
                                                         ("ethernet",
                                                         Inline.E.THeader [("dstAddr", Inline.E.TBit 48); ("srcAddr", Inline.E.TBit 48); ("etherType", Inline.E.TBit 16)]);
                                                         ("ipv4",
                                                         Inline.E.THeader
                                                           [("version", Inline.E.TBit 4); ("ihl", Inline.E.TBit 4); ("diffserv", Inline.E.TBit 8); ("totalLen", Inline.E.TBit 16);
                                                           ("identification", Inline.E.TBit 16); ("flags", Inline.E.TBit 3); ("fragOffset", Inline.E.TBit 13);
                                                           ("ttl", Inline.E.TBit 8); ("protocol", Inline.E.TBit 8); ("hdrChecksum", Inline.E.TBit 16); ("srcAddr", Inline.E.TBit 32);
                                                           ("dstAddr", Inline.E.TBit 32)]);
                                                         ("tcp",
                                                         Inline.E.THeader
                                                           [("srcPort", Inline.E.TBit 16); ("dstPort", Inline.E.TBit 16); ("seqNo", Inline.E.TBit 32); ("ackNo", Inline.E.TBit 32);
                                                           ("dataOffset", Inline.E.TBit 4); ("res", Inline.E.TBit 4); ("flags", Inline.E.TBit 8); ("window", Inline.E.TBit 16);
                                                           ("checksum", Inline.E.TBit 16); ("urgentPtr", Inline.E.TBit 16)])]) "hdr" NoInfo) NoInfo) NoInfo))];
                                         rtrns := None
                                       |} NoInfo)).
Compute instrumented_simple_nat.

Compute simple_nat_test_case.
Lemma simple_nat_test1 : is_ok simple_nat_test_case.
Proof. compute. trivial. Qed.

(* ECMP2 *)
Definition p4cub_ecmp2 := ToP4cub.translate_program Info NoInfo ECMP2.prog.

Definition ecmp2_test_case :=
  let* sn := p4cub_ecmp2 in
  let externs := V1model.externs in
  ToGCL.from_p4cub Info TableInstr.instr 1000 10 externs (V1model.package NoInfo) sn.

(* Compute p4cub_ecmp2. *)
(* Compute ecmp2_test_case. *)

Lemma ecmp2_test : is_ok ecmp2_test_case.
Proof. compute. trivial. Qed.

(* CAVEAT EMPTOR -- had to manually add type-widths to bitvectors *)
Definition p4cub_flowlet := ToP4cub.translate_program Info NoInfo Flowlet.prog.
Definition gcl_flowlet :=
  let* sn := p4cub_flowlet in
  let externs := V1model.externs in
  ToGCL.from_p4cub Info TableInstr.instr 1000 10 externs (V1model.package NoInfo) sn.

(* Compute cub_flowlet. *)
(* Compute gcl_flowlet. *)
Lemma flowlet_no_error: Result.is_ok gcl_flowlet.
Proof. compute; trivial. Qed.

(* 07-Multi-Protocol *)

Definition p4cub_multiprotocol := ToP4cub.translate_program Info NoInfo MultiProtocol.prog.

Definition multiprotocol_test_case :=
  let* sn := p4cub_multiprotocol in
  let externs := V1model.externs in
  ToGCL.from_p4cub Info TableInstr.instr 1000 10 externs (V1model.package NoInfo) sn.

Definition inline_multiprotocol : result (Inline.t Info) :=
  let* mp := p4cub_multiprotocol in
  ToGCL.inline_from_p4cub Info 1000 10 externs (V1model.package NoInfo) mp.

Definition instrumented_multiprotocol : result (Inline.t Info) :=
  let* imp := inline_multiprotocol in
  Inline.assert_headers_valid_before_use _ imp.

(* Compute p4cub_multiprotocol. *)
(* Compute instrumented_multiprotocol. *)
(* Compute multiprotocol_test_case. *)

Definition ethernet :=
  (Inline.E.EExprMember
                          (Inline.E.THeader
                             [("dstAddr", Inline.E.TBit 48);
                             ("srcAddr", Inline.E.TBit 48);
                             ("etherType", Inline.E.TBit 16)]) "ethernet"
                          (Inline.E.EVar
                             (Inline.E.TStruct
                                [("ethernet",
                                  Inline.E.THeader
                                    [("dstAddr", Inline.E.TBit 48);
                                    ("srcAddr", Inline.E.TBit 48);
                                    ("etherType", Inline.E.TBit 16)]);
                                ("icmp",
                                 Inline.E.THeader
                                   [("typeCode", Inline.E.TBit 16);
                                   ("hdrChecksum", Inline.E.TBit 16)]);
                                ("ipv4",
                                 Inline.E.THeader
                                   [("version", Inline.E.TBit 4);
                                   ("ihl", Inline.E.TBit 4);
                                   ("diffserv", Inline.E.TBit 8);
                                   ("totalLen", Inline.E.TBit 16);
                                   ("identification", Inline.E.TBit 16);
                                   ("flags", Inline.E.TBit 3);
                                   ("fragOffset", Inline.E.TBit 13);
                                   ("ttl", Inline.E.TBit 8);
                                   ("protocol", Inline.E.TBit 8);
                                   ("hdrChecksum", Inline.E.TBit 16);
                                   ("srcAddr", Inline.E.TBit 32);
                                   ("dstAddr", Inline.E.TBit 32)]);
                                ("ipv6",
                                 Inline.E.THeader
                                   [("version", Inline.E.TBit 4);
                                   ("trafficClass", Inline.E.TBit 8);
                                   ("flowLabel", Inline.E.TBit 20);
                                   ("payloadLen", Inline.E.TBit 16);
                                   ("nextHdr", Inline.E.TBit 8);
                                   ("hopLimit", Inline.E.TBit 8);
                                   ("srcAddr", Inline.E.TBit 128);
                                   ("dstAddr", Inline.E.TBit 128)]);
                                ("tcp",
                                 Inline.E.THeader
                                   [("srcPort", Inline.E.TBit 16);
                                   ("dstPort", Inline.E.TBit 16);
                                   ("seqNo", Inline.E.TBit 32);
                                   ("ackNo", Inline.E.TBit 32);
                                   ("dataOffset", Inline.E.TBit 4);
                                   ("res", Inline.E.TBit 4);
                                   ("flags", Inline.E.TBit 8);
                                   ("window", Inline.E.TBit 16);
                                   ("checksum", Inline.E.TBit 16);
                                   ("urgentPtr", Inline.E.TBit 16)]);
                                ("udp",
                                 Inline.E.THeader
                                   [("srcPort", Inline.E.TBit 16);
                                   ("dstPort", Inline.E.TBit 16);
                                   ("length_", Inline.E.TBit 16);
                                   ("checksum", Inline.E.TBit 16)]);
                                ("vlan_tag",
                                 Inline.E.THeader
                                   [("pcp", Inline.E.TBit 3);
                                   ("cfi", Inline.E.TBit 1);
                                   ("vid", Inline.E.TBit 12);
                                   ("etherType", Inline.E.TBit 16)])])
                             "hdr" NoInfo) NoInfo).


Compute (ToGCL.to_lvalue Info ethernet).
Definition ether__is_valid := Inline.E.EUop Inline.E.TBool Inline.E.IsValid ethernet NoInfo.

Compute (ToGCL.to_form Info ether__is_valid).

Definition assert_args : E.arrowE Info :=
  {| paramargs := [("check", PAIn ether__is_valid)] ; rtrns := None|}.

(* Definition arglist := ToGCL.arrowE_to_arglist Info assert_args. *)
(* Compute arglist. *)
(* Definition assert_impl : ToGCL.target := GCL.GCL.GAssert (GCL.Form.LVar "check"). *)
(* Compute (let+ a := arglist in ToGCL.subst_args assert_impl a). *)


Compute (ToGCL.inline_to_gcl Info TableInstr.instr ToGCL.initial
                             (Poulet4.P4cub.V1model.externs)
                             (Inline.IExternMethodCall Info "_" "assert" assert_args
                                        NoInfo)).

Lemma multiprotocol_test : is_ok multiprotocol_test_case.
Proof. compute. trivial. Qed.


(* LinearRoad *)

Definition p4cub_linearroad := ToP4cub.translate_program Info NoInfo LinearRoad.prog.

Definition inline_linearroad :=
  let* ctx := p4cub_linearroad in
  ToGCL.inline_from_p4cub Info 1000 10 externs (V1model.package NoInfo) ctx.


Definition linearroad_test_case :=
  let* sn := p4cub_linearroad in
  let externs := V1model.externs in
  ToGCL.from_p4cub Info TableInstr.instr 1000 10 externs (V1model.package NoInfo) sn.

(* Compute inline_linearroad. *)
(* Compute linearroad_test_case. *)

Lemma linearroad_test : is_ok linearroad_test_case.
Proof. compute; trivial. Qed.

(* heavy_hitter_1 *)

Definition heavy_hitter_test_case :=
  let* hh := ToP4cubTest.p4cub_heavy_hitter in
  ToGCL.from_p4cub Info TableInstr.instr 1000 10 V1model.externs (V1model.package NoInfo) hh.

Lemma heavy_hitter_test: is_ok heavy_hitter_test_case.
Proof. compute; trivial. Qed.


(* netchain *)

Definition netchain_test_case :=
  let* nc := ToP4cubTest.p4cub_netchain in
  ToGCL.from_p4cub Info TableInstr.instr 1000 10 V1model.externs (V1model.package NoInfo) nc.

Lemma netchain_test: is_ok netchain_test_case.
Proof. compute; trivial. Admitted.
(* EHC need to handle next *)

(* hula *)
Definition hula_test_case :=
  let* hula := ToP4cubTest.p4cub_hula in
  ToGCL.from_p4cub Info TableInstr.instr 1000 10 V1model.externs (V1model.package NoInfo) hula.
Lemma hula_test: is_ok hula_test_case.
Proof. compute; trivial. Admitted.
(* EHC need to handle next *)
