/*******************************************************************************
 * 
 ******************************************************************************/

#include <core.p4>

header ingress_intrinsic_metadata_t {
    bit<1> resubmit_flag;               // Flag distinguishing original packets
}

struct ingress_intrinsic_metadata_for_tm_t {
    bit<1> bypass_egress;               // Request flag for the warp mode
                                        // (egress bypass).
}

struct ingress_intrinsic_metadata_from_parser_t {
    bit<48> global_tstamp;              // Global timestamp (ns) taken upon
                                        // arrival at ingress.
}

struct ingress_intrinsic_metadata_for_deparser_t {
    bit<3> drop_ctl;                    // Disable packet replication:
}

header egress_intrinsic_metadata_t {
    bit<19> enq_qdepth;                 // Queue depth at the packet enqueue
                                        // time.
}

struct egress_intrinsic_metadata_from_parser_t {
    bit<48> global_tstamp;              // Global timestamp (ns) taken upon
                                        // arrival at egress.
}

struct egress_intrinsic_metadata_for_deparser_t {
    bit<3> drop_ctl;                    // Disable packet replication:
}

struct egress_intrinsic_metadata_for_output_port_t {
    bit<1> capture_tstamp_on_tx;        // Request for packet departure
}


parser IngressParserT<H, M>(
    packet_in pkt,
    out H hdr,
    out M ig_md,
    @optional out ingress_intrinsic_metadata_t ig_intr_md,
    @optional out ingress_intrinsic_metadata_for_tm_t ig_intr_md_for_tm,
    @optional out ingress_intrinsic_metadata_from_parser_t ig_intr_md_from_prsr);

parser EgressParserT<H, M>(
    packet_in pkt,
    out H hdr,
    out M eg_md,
    @optional out egress_intrinsic_metadata_t eg_intr_md,
    @optional out egress_intrinsic_metadata_from_parser_t eg_intr_md_from_prsr);

control IngressT<H, M>(
    inout H hdr,
    inout M ig_md,
    @optional in ingress_intrinsic_metadata_t ig_intr_md,
    @optional in ingress_intrinsic_metadata_from_parser_t ig_intr_md_from_prsr,
    @optional inout ingress_intrinsic_metadata_for_deparser_t ig_intr_md_for_dprsr,
    @optional inout ingress_intrinsic_metadata_for_tm_t ig_intr_md_for_tm);

control EgressT<H, M>(
    inout H hdr,
    inout M eg_md,
    @optional in egress_intrinsic_metadata_t eg_intr_md,
    @optional in egress_intrinsic_metadata_from_parser_t eg_intr_md_from_prsr,
    @optional inout egress_intrinsic_metadata_for_deparser_t eg_intr_md_for_dprsr,
    @optional inout egress_intrinsic_metadata_for_output_port_t eg_intr_md_for_oport);

control IngressDeparserT<H, M>(
    packet_out pkt,
    inout H hdr,
    in M metadata,
    @optional in ingress_intrinsic_metadata_for_deparser_t ig_intr_md_for_dprsr,
    @optional in ingress_intrinsic_metadata_t ig_intr_md);

control EgressDeparserT<H, M>(
    packet_out pkt,
    inout H hdr,
    in M metadata,
    @optional in egress_intrinsic_metadata_for_deparser_t eg_intr_md_for_dprsr,
    @optional in egress_intrinsic_metadata_t eg_intr_md,
    @optional in egress_intrinsic_metadata_from_parser_t eg_intr_md_from_prsr);

package Pipeline<IH, IM, EH, EM>(
    IngressParserT<IH, IM> ingress_parser,
    IngressT<IH, IM> ingress,
    IngressDeparserT<IH, IM> ingress_deparser,
    EgressParserT<EH, EM> egress_parser,
    EgressT<EH, EM> egress,
    EgressDeparserT<EH, EM> egress_deparser);

package Switch<IH0, IM0, EH0, EM0, IH1, IM1, EH1, EM1,
               IH2, IM2, EH2, EM2, IH3, IM3, EH3, EM3>(
    Pipeline<IH0, IM0, EH0, EM0> pipe0,
    @optional Pipeline<IH1, IM1, EH1, EM1> pipe1,
    @optional Pipeline<IH2, IM2, EH2, EM2> pipe2,
    @optional Pipeline<IH3, IM3, EH3, EM3> pipe3);



header data_h {
  bit<24> da;
  bit<8> db;
}

struct header_t {
    data_h hdr;
}

struct metadata_t {
    bit<16> ind_0;
    bit<16> ind_1;
}

parser SwitchIngressParser(
        packet_in pkt,
        out header_t hdr,
        out metadata_t ig_md,
        out ingress_intrinsic_metadata_t ig_intr_md) {

    state start {
        transition accept;
    }
}

control SwitchIngress(
        inout header_t hdr,
        inout metadata_t ig_md,
        in ingress_intrinsic_metadata_t ig_intr_md,
        in ingress_intrinsic_metadata_from_parser_t ig_intr_prsr_md,
        inout ingress_intrinsic_metadata_for_deparser_t ig_intr_dprsr_md,
        inout ingress_intrinsic_metadata_for_tm_t ig_intr_tm_md) {
    
    apply {
    }
}


control SwitchIngressDeparser(
        packet_out pkt,
        inout header_t hdr,
        in metadata_t ig_md,
        in ingress_intrinsic_metadata_for_deparser_t ig_intr_dprsr_md) {

    apply {
        pkt.emit(hdr);
    }
}

parser SwitchEgressParser(
        packet_in pkt,
        out header_t hdr,
        out metadata_t eg_md,
        out egress_intrinsic_metadata_t eg_intr_md) {
    state start {
        transition accept;
    }
}

control SwitchEgress(
        inout header_t hdr,
        inout metadata_t eg_md,
        in egress_intrinsic_metadata_t eg_intr_md,
        in egress_intrinsic_metadata_from_parser_t eg_intr_from_prsr,
        inout egress_intrinsic_metadata_for_deparser_t eg_intr_md_for_dprsr,
        inout egress_intrinsic_metadata_for_output_port_t eg_intr_md_for_oport) {

    apply {
        // empty
    }
}

control SwitchEgressDeparser(packet_out pkt,
                              inout header_t hdr,
                              in metadata_t eg_md,
                              in egress_intrinsic_metadata_for_deparser_t 
                                eg_intr_dprsr_md
                              ) {
    apply {
        pkt.emit(hdr);
    }
}


Pipeline(SwitchIngressParser(),
         SwitchIngress(),
         SwitchIngressDeparser(),
         SwitchEgressParser(),
         SwitchEgress(),
         SwitchEgressDeparser()) pipe;

Switch(pipe) main;
